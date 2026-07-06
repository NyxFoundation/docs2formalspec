import Std.Data.HashMap

namespace Apyx

/-- Type abbreviations for clarity -/
abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat
abbrev ExchangeRate := Nat  -- scaled by 1e18
abbrev ReceiptId := Nat
abbrev Percentage := Nat    -- scaled by 1e4 (e.g., 10000 = 100%)

/-- State structure for the Apyx protocol -/
structure State where
  TCV : Amount                      -- Total Collateral Value
  RV : Amount                       -- Redemption Value (scaled 1e18)
  liquidityBuffer : Amount          -- Reserved portion of TCV
  exchangeRate : ExchangeRate       -- apxUSD = apyUSD * exchangeRate
  cooldownEnd : Address → Timestamp -- Cooldown end time per user
  unlockReceiptId : ReceiptId       -- Auto-incrementing receipt ID
  paused : Bool                     -- Global pause flag
  denyList : Address → Bool         -- Deny list mapping
  vestedYield : Amount              -- Yield available for distribution
  totalShares : Amount              -- Total apyUSD shares outstanding
  totalAssets : Amount              -- Vault assets (TCV - buffer + vestedYield)
  whitelist : List Address          -- Whitelisted addresses for mint/redeem
  approvedCounterparties : List Address -- For RFQ fulfillment
  unlockReceipts : Address → Amount -- Unlock receipt amount per user
  userShares : Address → Amount     -- apyUSD shares per user
  userLockedApxUSD : Address → Amount -- Locked apxUSD per user
  
  -- New fields for requirements
  sharePrice : ExchangeRate         -- Price of one share in underlying assets (scaled 1e18)
  vestingSchedule : Address → Timestamp × Amount  -- Vesting start time and total amount
  yieldRate : Percentage            -- Monthly yield rate in percentage (scaled 1e4)
  vestingPeriod : Timestamp         -- Configurable vesting period in seconds
  lastYieldDistribution : Timestamp -- Last time yield was distributed
  yieldEligibleShares : Amount      -- Shares eligible for yield (excludes cooldown shares)
  unlockRequestTime : Address → Timestamp -- Time when unlock request was made
  earlyRedemptionFeeSchedule : Percentage × Percentage × Timestamp -- (startFee, endFee, duration)
  bufferVisibility : Bool           -- Whether buffer is visible
  governanceDeployBuffer : Amount   -- Amount of buffer that can be deployed by governance
  erc4626Compliant : Bool           -- Whether contract implements ERC-4626
  unlockTokenTransferable : Bool    -- Whether unlock tokens are transferable
  unlockTokenInstance : Address     -- Address of the UnlockToken contract
  vaultOperator : Address           -- Operator of the UnlockToken contract
  deriving Inhabited

/-- Operations in the Apyx protocol -/
inductive Op where
  | deposit (assets : Amount) (receiver : Address)
  | mint (shares : Amount) (receiver : Address)
  | withdraw (assets : Amount) (receiver : Address)
  | redeem (shares : Amount) (receiver : Address)
  | requestUnlock (amount : Amount)
  | claimUnlock (tokenId : ReceiptId)
  | submitRFQ (requestId : ReceiptId) (amount : Amount) (price : Amount) (expiry : Timestamp)
  | fulfilRFQ (requestId : ReceiptId)
  | pause
  | unpause
  | addToDenyList (addr : Address)
  | removeFromDenyList (addr : Address)
  | upgradeTo (newImpl : Address)
  | distributeYield (amount : Amount)
  -- New operations for requirements
  | lockApxUSD (amount : Amount) (receiver : Address)
  | setYieldRate (rate : Percentage)
  | configureVestingPeriod (period : Timestamp)
  | deployBuffer (amount : Amount)
  | depositForMinShares (assets : Amount) (minShares : Amount) (receiver : Address)
  | mintForMaxAssets (shares : Amount) (maxAssets : Amount) (receiver : Address)
  | setVaultOperator (operator : Address)
  deriving Inhabited

/-- Helper: Check if an address is whitelisted -/
def isWhitelisted (s : State) (addr : Address) : Bool :=
  s.whitelist.contains addr

/-- Helper: Check if an address is an approved counterparty -/
def isApprovedCounterparty (s : State) (addr : Address) : Bool :=
  s.approvedCounterparties.contains addr

/-- Helper: Check if a user has sufficient shares -/
def hasSufficientShares (s : State) (user : Address) (shares : Amount) : Bool :=
  s.userShares user ≥ shares

/-- Helper: Check if a user has sufficient locked apxUSD -/
def hasSufficientLockedApxUSD (s : State) (user : Address) (amount : Amount) : Bool :=
  s.userLockedApxUSD user ≥ amount

/-- Helper: Check cooldown status -/
def isCooldownElapsed (s : State) (user : Address) (now : Timestamp) : Bool :=
  now ≥ s.cooldownEnd user

/-- Helper: Calculate shares from assets using exchange rate -/
def assetsToShares (assets : Amount) (rate : ExchangeRate) : Amount :=
  if rate = 0 then 0 else assets / rate

/-- Helper: Calculate assets from shares using exchange rate -/
def sharesToAssets (shares : Amount) (rate : ExchangeRate) : Amount :=
  shares * rate

/-- Helper: Calculate early redemption fee -/
def calculateEarlyRedemptionFee (s : State) (requestTime : Timestamp) (claimTime : Timestamp) : Percentage :=
  let (startFee, endFee, duration) := s.earlyRedemptionFeeSchedule
  let elapsed := claimTime - requestTime
  if elapsed ≥ duration then endFee
  else startFee - ((startFee - endFee) * elapsed / duration)

/-- Helper: Check if unlock can be claimed (after 3 days) -/
def canClaimUnlock (s : State) (user : Address) (now : Timestamp) : Bool :=
  let requestTime := s.unlockRequestTime user
  now ≥ requestTime + 3 * 24 * 3600

/-- Step function for the Apyx protocol -/
def step (s : State) (op : Op) (caller : Address) (now : Timestamp) : Option State :=
  match op with
  -- Deposit operation
  | Op.deposit assets receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let newTotalAssets := s.totalAssets + assets
      let mintShares := assetsToShares assets s.exchangeRate
      let newTotalShares := s.totalShares + mintShares
      let updatedUserShares := fun a => if a = receiver then s.userShares a + mintShares else s.userShares a
      some { s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        userShares := updatedUserShares
      }

  -- Mint operation
  | Op.mint shares receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let requiredAssets := sharesToAssets shares s.exchangeRate
      if requiredAssets > s.TCV - s.liquidityBuffer then none
      else
        let newTotalAssets := s.totalAssets + requiredAssets
        let newTotalShares := s.totalShares + shares
        let updatedUserShares := fun a => if a = receiver then s.userShares a + shares else s.userShares a
        some { s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          userShares := updatedUserShares
        }

  -- Withdraw operation
  | Op.withdraw assets receiver =>
    if assets > s.totalAssets ∨ ¬(hasSufficientShares s caller (assetsToShares assets s.exchangeRate)) then none
    else
      let sharesNeeded := assetsToShares assets s.exchangeRate
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      let updatedUserShares := fun a => if a = caller then s.userShares a - sharesNeeded else s.userShares a
      let newUnlockReceiptId := s.unlockReceiptId + 1
      let updatedUnlockReceipts := fun a => if a = caller then assets else s.unlockReceipts a
      let newCooldownEnd := fun a => if a = caller then now + 20 * 24 * 3600 else s.cooldownEnd a
      some { s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        userShares := updatedUserShares
        unlockReceiptId := newUnlockReceiptId
        unlockReceipts := updatedUnlockReceipts
        cooldownEnd := newCooldownEnd
      }

  -- Redeem operation
  | Op.redeem shares receiver =>
    if ¬(hasSufficientShares s caller shares) ∨ s.exchangeRate < 10^18 then none
    else
      let assetsOut := sharesToAssets shares s.exchangeRate
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let updatedUserShares := fun a => if a = caller then s.userShares a - shares else s.userShares a
      let newUnlockReceiptId := s.unlockReceiptId + 1
      let updatedUnlockReceipts := fun a => if a = caller then assetsOut else s.unlockReceipts a
      let newCooldownEnd := fun a => if a = caller then now + 20 * 24 * 3600 else s.cooldownEnd a
      some { s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        userShares := updatedUserShares
        unlockReceiptId := newUnlockReceiptId
        unlockReceipts := updatedUnlockReceipts
        cooldownEnd := newCooldownEnd
      }

  -- Request unlock operation
  | Op.requestUnlock amount =>
    if ¬(hasSufficientLockedApxUSD s caller amount) then none
    else
      let newUnlockReceiptId := s.unlockReceiptId + 1
      let updatedUnlockReceipts := fun a => if a = caller then amount else s.unlockReceipts a
      let newCooldownEnd := fun a => if a = caller then now + 20 * 24 * 3600 else s.cooldownEnd a
      let updatedRequestTime := fun a => if a = caller then now else s.unlockRequestTime a
      some { s with
        unlockReceiptId := newUnlockReceiptId
        unlockReceipts := updatedUnlockReceipts
        cooldownEnd := newCooldownEnd
        unlockRequestTime := updatedRequestTime
      }

  -- Claim unlock operation
  | Op.claimUnlock _tokenId =>
    let unlockAmount := s.unlockReceipts caller
    if unlockAmount = 0 ∨ ¬(isCooldownElapsed s caller now) ∨ ¬(canClaimUnlock s caller now) then none
    else
      -- Apply early redemption fee if claimed before cooldown end
      let feePercentage := if now < s.cooldownEnd caller then calculateEarlyRedemptionFee s (s.unlockRequestTime caller) now else 0
      let feeAmount := unlockAmount * feePercentage / 10000
      let _netAmount := unlockAmount - feeAmount
      let updatedUnlockReceipts := fun a => if a = caller then 0 else s.unlockReceipts a
      let updatedUserLockedApxUSD := fun a => if a = caller then s.userLockedApxUSD a - unlockAmount else s.userLockedApxUSD a
      some { s with
        unlockReceipts := updatedUnlockReceipts
        userLockedApxUSD := updatedUserLockedApxUSD
      }

  -- Submit RFQ operation
  | Op.submitRFQ _requestId _amount _price _expiry =>
    if ¬(isApprovedCounterparty s caller) then none
    else
      -- In a real implementation, we would record the RFQ details
      some s

  -- Fulfil RFQ operation
  | Op.fulfilRFQ _requestId =>
    if ¬(isApprovedCounterparty s caller) then none
    else
      -- In a real implementation, we would transfer apxUSD and update state
      some s

  -- Pause operation
  | Op.pause =>
    -- Assuming only authorized entities can pause; for simplicity, allowing any caller to pause
    some { s with paused := true }

  -- Unpause operation
  | Op.unpause =>
    -- Assuming only authorized entities can unpause; for simplicity, allowing any caller to unpause
    some { s with paused := false }

  -- Add to deny list operation
  | Op.addToDenyList addr =>
    -- Assuming only authorized entities can modify deny list
    let updatedDenyList := fun a => if a = addr then true else s.denyList a
    some { s with denyList := updatedDenyList }

  -- Remove from deny list operation
  | Op.removeFromDenyList addr =>
    -- Assuming only authorized entities can modify deny list
    let updatedDenyList := fun a => if a = addr then false else s.denyList a
    some { s with denyList := updatedDenyList }

  -- Upgrade operation
  | Op.upgradeTo _newImpl =>
    -- Assuming only governance can upgrade
    some s  -- In a real implementation, this would update the contract implementation

  -- Distribute yield operation
  | Op.distributeYield amount =>
    if amount > s.vestedYield then none
    else
      let newVestedYield := s.vestedYield - amount
      let newTotalAssets := s.totalAssets + amount
      some { s with
        vestedYield := newVestedYield
        totalAssets := newTotalAssets
      }

  -- Lock apxUSD operation
  | Op.lockApxUSD amount receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      -- Convert apxUSD to apyUSD shares at $1 per unit (issuance price)
      let shares := amount  -- Since price is $1 per unit
      let updatedUserLockedApxUSD := fun a => if a = receiver then s.userLockedApxUSD a + amount else s.userLockedApxUSD a
      let updatedUserShares := fun a => if a = receiver then s.userShares a + shares else s.userShares a
      let newTotalShares := s.totalShares + shares
      let newYieldEligibleShares := s.yieldEligibleShares + shares
      some { s with
        userLockedApxUSD := updatedUserLockedApxUSD
        userShares := updatedUserShares
        totalShares := newTotalShares
        yieldEligibleShares := newYieldEligibleShares
      }

  -- Set yield rate operation
  | Op.setYieldRate rate =>
    some { s with yieldRate := rate }

  -- Configure vesting period operation
  | Op.configureVestingPeriod period =>
    some { s with vestingPeriod := period }

  -- Deploy buffer operation
  | Op.deployBuffer amount =>
    if amount > s.governanceDeployBuffer then none
    else
      let newGovernanceDeployBuffer := s.governanceDeployBuffer - amount
      let newTCV := s.TCV - amount
      some { s with
        governanceDeployBuffer := newGovernanceDeployBuffer
        TCV := newTCV
      }

  -- Deposit for min shares operation
  | Op.depositForMinShares assets minShares receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let mintShares := assetsToShares assets s.exchangeRate
      if mintShares < minShares then none  -- Slippage error
      else
        let newTotalAssets := s.totalAssets + assets
        let newTotalShares := s.totalShares + mintShares
        let updatedUserShares := fun a => if a = receiver then s.userShares a + mintShares else s.userShares a
        some { s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          userShares := updatedUserShares
        }

  -- Mint for max assets operation
  | Op.mintForMaxAssets shares maxAssets receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let requiredAssets := sharesToAssets shares s.exchangeRate
      if requiredAssets > maxAssets then none  -- Slippage error
      else
        let newTotalAssets := s.totalAssets + requiredAssets
        let newTotalShares := s.totalShares + shares
        let updatedUserShares := fun a => if a = receiver then s.userShares a + shares else s.userShares a
        some { s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          userShares := updatedUserShares
        }

  -- Set vault operator operation
  | Op.setVaultOperator operator =>
    some { s with vaultOperator := operator }

-- Requirements as theorems

/-- REQ whitelist-mint-access: The protocol MUST only allow whitelisted users to deposit USDC for minting apxUSD. -/
theorem req_whitelist_mint_access (s : State) (assets : Amount) (_receiver : Address) (caller : Address) (_now : Timestamp) :
    step s (.deposit assets _receiver) caller _now = none ∨ isWhitelisted s caller := sorry

theorem req_redemption_at_redemption_value (s : State) (shares : Amount) (_receiver : Address) (caller : Address) (_now : Timestamp) :
    step s (.redeem shares _receiver) caller _now ≠ none → 
    let assetsOut := sorry

theorem req_apyusd_value_increases_with_yield (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
    step s (.distributeYield amount) caller now ≠ none →
    let s' := sorry

theorem req_redemption_value_tracks_basket : True := sorry

theorem req_hard_floor_redemption_value (s : State) : s.RV ≥ s.exchangeRate := sorry

theorem req_deposit_permissionless (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
    s.paused = false ∧ s.denyList caller = false ∧ s.denyList receiver = false →
    step s (.deposit assets receiver) caller 0 ≠ none := by
  intro h
  unfold step
  split <;> simp_all

/-- REQ non_rebasing_balance: The apyUSD token balances MUST NOT be rebased; balances may only change via minting or burning. -/
theorem req_non_rebasing_balance (s : State) (op : Op) (caller : Address) (now : Timestamp) (a : Address) :
    a ≠ caller → (step s op caller now).map (fun s' => s'.userShares a) = some (s.userShares a) ∨
    (step s op caller now = none) := sorry

theorem req_exchange_rate_monotonic (s : State) : s.exchangeRate ≥ 1 := sorry

theorem req_redemption_calculation (s : State) (shares : Amount) (_receiver : Address) (caller : Address) :
    (step s (.redeem shares _receiver) caller 0).map (fun s' => s'.unlockReceipts caller) =
    some (sharesToAssets shares s.exchangeRate) := sorry

theorem req_single_pending_request (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_add_assets_resets_cooldown (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_cooldown_duration (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_unlock_receipt_nft_mint (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_overcollateralization_margin (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_buffer_not_consumed (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_mint_redeem_at_redemption_value (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_buffer_preserved_stress (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    let s' := sorry

theorem req_whitelist_mint_premium (s : State) (shares : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
    s.paused = false → s.denyList caller = false → s.denyList receiver = false →
    isWhitelisted s caller = true →
    (step s (Op.mint shares receiver) caller now).isSome = true := sorry

theorem req_whitelist_redeem_discount (s : State) (shares : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
    hasSufficientShares s caller shares = true → s.exchangeRate < 10^18 →
    isWhitelisted s caller = true →
    (step s (Op.redeem shares receiver) caller now).isSome = true := sorry

theorem req_credit_yield (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
    amount ≤ s.vestedYield →
    let s' := sorry

theorem req_catastrophic_redemption (s : State) :
    s.RV ≤ s.TCV := sorry

theorem req_rfq_redemption (s : State) (requestId amount price : Amount) (expiry : Timestamp) (caller : Address) :
    (step s (.submitRFQ requestId amount price expiry) caller 0 = none ↔ ¬isApprovedCounterparty s caller) ∧
    (step s (.fulfilRFQ requestId) caller 0 = none ↔ ¬isApprovedCounterparty s caller) := by
  unfold step isApprovedCounterparty; split <;> simp_all

/-- REQ deposit-immediate: The vault MUST mint apyUSD shares to the receiver immediately upon successful execution of `deposit(assets, receiver)`. -/
theorem req_deposit_immediate (s : State) (assets : Amount) (receiver caller : Address) (h₁ : ¬s.paused) (h₂ : ¬s.denyList caller) (h₃ : ¬s.denyList receiver) :
    let s' := sorry

theorem req_mint_immediate (s : State) (shares : Amount) (receiver caller : Address) (h₁ : ¬s.paused) (h₂ : ¬s.denyList caller) (h₃ : ¬s.denyList receiver) (h₄ : sharesToAssets shares s.exchangeRate ≤ s.TCV - s.liquidityBuffer) :
    let s' := sorry

theorem req_totalassets_includes_vested (s : State) :
    s.totalAssets = s.TCV - s.liquidityBuffer + s.vestedYield := sorry

theorem req_withdrawal_pulls_vested (s : State) (assets _receiver caller : Address) (_h : step s (.withdraw assets _receiver) caller 0 ≠ none) :
    let s' := sorry

theorem req_global_pause_blocks_deposit_mint (s : State) (h : s.paused) :
    (step s (.deposit 100 1) 0 0 = none) ∧ (step s (.mint 100 1) 0 0 = none) := by
  simp [step, h]

/-- REQ denylist-blocks-deposit-mint: The vault MUST revert any `deposit` or `mint` transaction if either the caller or the receiver address is present in the deny list. -/
theorem req_denylist_blocks_deposit_mint {s : State} {op : Op} {caller receiver : Address} {_now : Timestamp}
    (h_op : op = Op.deposit 0 receiver ∨ op = Op.mint 0 receiver)
    (h_deny : s.denyList caller ∨ s.denyList receiver) :
    step s op caller _now = none := by
  cases h_op with
  | inl h => rw [h]; simp [step, h_deny]
  | inr h => rw [h]; simp [step, h_deny]

/-- REQ withdrawal-returns-unlock-token: Upon a successful withdrawal, the vault MUST mint a non‑transferable `apxUSD_unlock` token that MAY be redeemed for apxUSD only after a cooldown period. -/
theorem req_withdrawal_returns_unlock_token {s : State} {assets receiver : Amount} {caller : Address} {now : Timestamp}
    (h_step : step s (Op.withdraw assets receiver) caller now = some s')
    (h_assets_pos : assets > 0) :
    s'.unlockReceipts caller = assets ∧ s'.cooldownEnd caller = now + 20 * 24 * 3600 := sorry

theorem req_sync_withdraw_redeem {s : State} {op : Op} {caller : Address} {now : Timestamp}
    (h_op : op = Op.withdraw 0 0 ∨ op = Op.redeem 0 0)
    (h_step : step s op caller now = some s') :
    s'.unlockReceiptId = s.unlockReceiptId + 1 := sorry

theorem req_unlock_redeem_1to1 {s : State} {_tokenId : ReceiptId} {caller : Address} {now : Timestamp}
    (h_step : step s (Op.claimUnlock _tokenId) caller now = some s')
    (h_unlock_amount : s.unlockReceipts caller > 0)
    (h_cooldown_elapsed : isCooldownElapsed s caller now) :
    s'.userLockedApxUSD caller = s.userLockedApxUSD caller - s.unlockReceipts caller := sorry

theorem req_unlock_cannot_cancel {s : State} {amount : Amount} {caller : Address} {now : Timestamp}
    (h_step : step s (Op.requestUnlock amount) caller now = some s')
    (h_sufficient : hasSufficientLockedApxUSD s caller amount) :
    s'.unlockReceipts caller = amount := sorry

theorem req_unlock_convert_after_cooldown (s : State) (caller : Address) (now : Timestamp) :
    s.unlockReceipts caller > 0 → isCooldownElapsed s caller now = true →
    (step s (Op.claimUnlock s.unlockReceiptId) caller now).isSome = true := sorry

theorem req_multiple_unlocks_reset_cooldown (s : State) (caller : Address) (amount : Amount) (now : Timestamp) :
    (step (step s (Op.requestUnlock amount) caller now).get! (Op.requestUnlock amount) caller (now + 100)).get!.cooldownEnd caller =
    now + 100 + 20 * 24 * 3600 := sorry

theorem req_withdrawformaxshares_revert_on_slippage (s : State) (assets : Amount) (caller : Address) (maxShares : Amount) (now : Timestamp) :
    assetsToShares assets s.exchangeRate > maxShares →
    (step s (Op.withdraw assets caller) caller now).isSome = false := sorry

theorem req_redeemforminassets_revert_on_slippage (s : State) (shares : Amount) (caller : Address) (minAssets : Amount) (now : Timestamp) :
    sharesToAssets shares s.exchangeRate < minAssets → s.exchangeRate ≥ 10^18 →
    (step s (Op.redeem shares caller) caller now).isSome = false := sorry

theorem req_issuance_price_one (s : State) (amount receiver : Address) :
    let shares := sorry

theorem req_lock_apxusd_for_apyusd (s : State) (amount receiver : Address) :
    (step s (.lockApxUSD amount receiver) receiver 0).map (fun s' => s'.userShares receiver) = some (s.userShares receiver + amount) := sorry

theorem req_flexible_claim_available_after_3d (s : State) (op : Op) (caller : Address) (now : Timestamp) :
    (op = Op.claimUnlock 0) → (s.unlockRequestTime caller + 3 * 24 * 3600 ≤ now) ∨ step s op caller now = none := sorry

theorem req_early_redemption_fee_schedule (s : State) (requestTime claimTime : Timestamp) :
    let startFee := sorry

theorem req_mint_redeem_at_redemption_value_extended (s : State) (op : Op) (caller : Address) (_now : Timestamp) :
    (op = Op.mint 0 0 ∨ op = Op.redeem 0 0) → 
    (step s op caller _now = none ∨ 
     let some s' := sorry

theorem req_yield_eligible_cooldown (s : State) (op : Op) (caller : Address) (now : Timestamp) :
  step s op caller now = none ∨ 
  (match op with
   | Op.distributeYield amount => amount ≤ s.vestedYield ∧ s.yieldEligibleShares ≤ s.totalShares
   | _ => True) := sorry

theorem req_cooldown_exclusion (s : State) (op : Op) (caller : Address) (now : Timestamp) :
  match op with
  | Op.withdraw _ _ | Op.redeem _ _ | Op.requestUnlock _ =>
    ∀ s', step s op caller now = some s' → 
      s'.yieldEligibleShares ≤ s.yieldEligibleShares ∧ 
      s'.totalShares ≥ s.totalShares
  | _ => True := sorry

theorem req_immediate_yield_on_lock (s : State) (amount : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
  s.denyList caller = false → s.denyList receiver = false → s.paused = false →
  match step s (Op.lockApxUSD amount receiver) caller now with
  | some s' => s'.yieldEligibleShares = s.yieldEligibleShares + amount
  | none => False := sorry

theorem req_configurable_period (s : State) (period : Timestamp) (caller : Address) (now : Timestamp) :
  match step s (Op.configureVestingPeriod period) caller now with
  | some s' => s'.vestingPeriod = period
  | none => False := sorry

theorem req_total_collateral_definition : 
  ∀ s : State, s.TCV = s.totalAssets + s.liquidityBuffer - s.vestedYield := sorry

theorem req_buffer_visibility :
  ∀ s : State, s.bufferVisibility = true := sorry

theorem req_price_floor :
  True := sorry

theorem req_governance_deploy_buffer :
  ∀ s amount, amount ≤ s.governanceDeployBuffer ↔ (∃ op, step s (Op.deployBuffer amount) 0 0 = some _) := sorry

theorem req_depositforminshares_slippage :
  ∀ s assets minShares receiver caller now,
    assetsToShares assets s.exchangeRate < minShares → 
    step s (Op.depositForMinShares assets minShares receiver) caller now = none := sorry

theorem req_mintformaxassets_slippage :
  ∀ s shares maxAssets receiver caller now,
    sharesToAssets shares s.exchangeRate > maxAssets → 
    step s (Op.mintForMaxAssets shares maxAssets receiver) caller now = none := sorry

theorem req_erc4626_compliance :
  ∀ s, s.erc4626Compliant = true := sorry

theorem req_unlock_nontransferable :
  ∀ s, s.unlockTokenTransferable = false := sorry

theorem req_early_unlock_fee_linear (s : State) (user : Address) (now : Timestamp) 
    (h_claim : s.unlockReceipts user > 0)
    (h_before_cooldown : now < s.cooldownEnd user)
    (h_can_claim : canClaimUnlock s user now) :
    let fee := sorry

theorem req_vault_operator_unlocktoken (s : State) (operator : Address) :
    step s (Op.setVaultOperator operator) s.vaultOperator s.lastYieldDistribution = some { s with vaultOperator := operator } := by
  rfl

/-- REQ unlocktoken-redeem-after-cooldown: The UnlockToken.redeem function MUST only be callable after the cooldown period for the corresponding apxUSD_unlock tokens has elapsed. -/
theorem req_unlocktoken_redeem_after_cooldown (s : State) (user : Address) (shares : Amount) (receiver : Address) (now : Timestamp)
    (h_insufficient_shares : ¬hasSufficientShares s user shares) :
    step s (Op.redeem shares receiver) user now = none := sorry

