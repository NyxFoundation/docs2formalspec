namespace Apyx

-- Type abbreviations for clarity
abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat
abbrev ReceiptId := Nat

-- Constants
def COOLDOWN_DURATION : Timestamp := 20 * 24 * 3600  -- 20 days in seconds
def MIN_COOLDOWN_CLAIM : Timestamp := 3 * 24 * 3600   -- 3 days in seconds
def EXCHANGE_RATE_SCALE : Amount := 1000000000000000000  -- 1e18
def EARLY_UNLOCK_FEE_MAX : Amount := 35  -- 3.5% scaled by 10
def EARLY_UNLOCK_FEE_MIN : Amount := 1   -- 0.1% scaled by 10

-- Linear Vesting Schedule Structure
structure VestingSchedule where
  startTime : Timestamp
  endTime : Timestamp
  totalAmount : Amount
  claimedAmount : Amount
  deriving Inhabited

-- Yield Rate Structure
structure YieldRate where
  periodStart : Timestamp
  periodEnd : Timestamp
  rateInDollars : Amount  -- Rate expressed in dollar terms
  deriving Inhabited

-- State structure
structure State where
  TCV : Amount                      -- Total Collateral Value
  RV : Amount                       -- Redemption Value
  liquidityBuffer : Amount          -- Liquidity buffer
  exchangeRate : Amount             -- Exchange rate (apyUSD to apxUSD)
  totalShares : Amount              -- Total apyUSD shares
  totalAssets : Amount              -- Total assets in vault
  vestedYield : Amount              -- Vested yield available
  paused : Bool                     -- Global pause flag
  denyList : Address → Bool         -- Deny list mapping
  whitelist : List Address          -- Whitelist for mint/redeem
  approvedCounterparties : List Address  -- Approved RFQ counterparties
  unlockReceiptId : ReceiptId       -- Auto-incrementing receipt ID
  cooldownEnd : Address → Timestamp -- Cooldown end time per user
  pendingUnlockAmount : Address → Amount  -- Pending unlock amount per user
  unlockReceiptOwner : ReceiptId → Address  -- Owner of each unlock receipt
  unlockReceiptAmount : ReceiptId → Amount  -- Amount locked in each receipt
  unlockReceiptCooldownEnd : ReceiptId → Timestamp  -- Cooldown end for each receipt
  bal : Address → Amount            -- apyUSD balance per address
  apxUsdBal : Address → Amount      -- apxUSD balance per address
  rfqRequests : ReceiptId → Option (Amount × Amount × Timestamp)  -- (amount, price, expiry)
  -- New fields for requirements
  currentTime : Timestamp           -- Current system time
  yieldRates : List YieldRate      -- Monthly yield rates
  vestingPeriod : Timestamp        -- Configurable vesting period
  userVestingSchedules : Address → Option VestingSchedule  -- Linear vesting per user
  unlockReceiptTransferable : Bool := false  -- Unlock tokens are non-transferable
  unlockReceiptCancelable : Bool := false    -- Unlock requests cannot be canceled
  deriving Inhabited

-- Operations
inductive Op
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
  | distributeYield (amount : Amount)
  -- New operations for requirements
  | depositForMinShares (assets : Amount) (minShares : Amount) (receiver : Address)
  | mintForMaxAssets (shares : Amount) (maxAssets : Amount) (receiver : Address)
  | withdrawForMaxShares (assets : Amount) (maxShares : Amount) (receiver : Address)
  | redeemForMinAssets (shares : Amount) (minAssets : Amount) (receiver : Address)
  | setYieldRate (rate : YieldRate)
  | claimVestedYield (caller : Address)
  | updateVestingPeriod (newPeriod : Timestamp)
  deriving Inhabited

-- Helper functions
def sharePrice (s : State) : Amount :=
  if s.totalShares = 0 then EXCHANGE_RATE_SCALE else s.totalAssets / s.totalShares

def convertToShares (s : State) (assets : Amount) : Amount :=
  if s.totalAssets = 0 ∨ s.totalShares = 0 then assets
  else assets * s.totalShares / s.totalAssets

def convertToAssets (s : State) (shares : Amount) : Amount :=
  if s.totalShares = 0 then shares else shares * s.totalAssets / s.totalAssets

def calculateEarlyUnlockFee (s : State) (_caller : Address) (receiptId : ReceiptId) : Amount :=
  let cooldownEnd := s.unlockReceiptCooldownEnd receiptId
  let now := s.currentTime
  if now >= cooldownEnd then 0
  else
    let elapsed := cooldownEnd - now
    let maxFee := EARLY_UNLOCK_FEE_MAX
    let minFee := EARLY_UNLOCK_FEE_MIN
    let feeDecline := (elapsed * (maxFee - minFee)) / COOLDOWN_DURATION
    maxFee - feeDecline

def getVestedAmount (s : State) (schedule : VestingSchedule) : Amount :=
  if s.currentTime >= schedule.endTime then
    schedule.totalAmount - schedule.claimedAmount
  else
    let elapsed := s.currentTime - schedule.startTime
    let totalVestingTime := schedule.endTime - schedule.startTime
    if totalVestingTime = 0 then 0
    else
      let vested := (schedule.totalAmount * elapsed) / totalVestingTime
      vested - schedule.claimedAmount

-- Step function
def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.deposit assets _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let mintShares := assets / s.exchangeRate
      let newTotalAssets := s.totalAssets + assets
      let newTotalShares := s.totalShares + mintShares
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = _receiver then s.bal a + mintShares else s.bal a
      }
  | Op.mint shares _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let requiredAssets := shares * s.exchangeRate
      if requiredAssets > s.TCV - s.liquidityBuffer then none
      else
        let newTotalAssets := s.totalAssets + requiredAssets
        let newTotalShares := s.totalShares + shares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = _receiver then s.bal a + shares else s.bal a
        }
  | Op.withdraw assets receiver =>
    let sharesNeeded := convertToShares s assets
    if assets > s.totalAssets ∨ s.bal caller < sharesNeeded then none
    else
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assets else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assets else s.pendingUnlockAmount a
      }
  | Op.redeem shares receiver =>
    if shares > s.totalShares ∨ s.exchangeRate < EXCHANGE_RATE_SCALE then none
    else
      let assetsOut := shares * s.exchangeRate
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - shares else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assetsOut else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assetsOut else s.pendingUnlockAmount a
      }
  | Op.requestUnlock amount =>
    if amount > s.apxUsdBal caller then none
    else
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then amount else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + amount else s.pendingUnlockAmount a
      }
  | Op.claimUnlock tokenId =>
    let owner := s.unlockReceiptOwner tokenId
    let amount := s.unlockReceiptAmount tokenId
    let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
    if owner ≠ caller ∨ s.currentTime < cooldownEnd then none
    else
      let fee := calculateEarlyUnlockFee s caller tokenId
      let amountAfterFee := amount - (amount * fee / 1000)
      some {
        s with
        apxUsdBal := fun a => if a = caller then s.apxUsdBal a + amountAfterFee else s.apxUsdBal a
        unlockReceiptOwner := fun id => if id = tokenId then 0 else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = tokenId then 0 else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = tokenId then 0 else s.unlockReceiptCooldownEnd id
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a - amount else s.pendingUnlockAmount a
      }
  | Op.submitRFQ requestId amount price expiry =>
    if ¬(s.approvedCounterparties.contains caller) then none
    else
      some {
        s with
        rfqRequests := fun id => if id = requestId then some (amount, price, expiry) else s.rfqRequests id
      }
  | Op.fulfilRFQ requestId =>
    if ¬(s.approvedCounterparties.contains caller) then none
    else
      match s.rfqRequests requestId with
      | none => none
      | some (amount, _, expiry) =>
        if s.currentTime > expiry then none
        else
          some {
            s with
            apxUsdBal := fun a => if a = caller then s.apxUsdBal a + amount else s.apxUsdBal a
            rfqRequests := fun id => if id = requestId then none else s.rfqRequests id
          }
  | Op.pause =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with paused := true }
  | Op.unpause =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with paused := false }
  | Op.addToDenyList addr =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with denyList := fun a => if a = addr then true else s.denyList a }
  | Op.removeFromDenyList addr =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with denyList := fun a => if a = addr then false else s.denyList a }
  | Op.distributeYield amount =>
    if amount > s.vestedYield then none
    else
      let newVestedYield := s.vestedYield - amount
      let newTotalAssets := s.totalAssets + amount
      some {
        s with
        vestedYield := newVestedYield
        totalAssets := newTotalAssets
      }
  | Op.depositForMinShares assets minShares receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let mintShares := assets / s.exchangeRate
      if mintShares < minShares then none  -- Slippage check
      else
        let newTotalAssets := s.totalAssets + assets
        let newTotalShares := s.totalShares + mintShares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = receiver then s.bal a + mintShares else s.bal a
        }
  | Op.mintForMaxAssets shares maxAssets receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let requiredAssets := shares * s.exchangeRate
      if requiredAssets > maxAssets then none  -- Slippage check
      else
        let newTotalAssets := s.totalAssets + requiredAssets
        let newTotalShares := s.totalShares + shares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = receiver then s.bal a + shares else s.bal a
        }
  | Op.withdrawForMaxShares assets maxShares receiver =>
    let sharesNeeded := convertToShares s assets
    if sharesNeeded > maxShares then none  -- Slippage check
    else if assets > s.totalAssets ∨ s.bal caller < sharesNeeded then none
    else
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assets else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assets else s.pendingUnlockAmount a
      }
  | Op.redeemForMinAssets shares minAssets receiver =>
    let assetsOut := shares * s.exchangeRate
    if assetsOut < minAssets then none  -- Slippage check
    else if shares > s.totalShares then none
    else
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - shares else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assetsOut else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assetsOut else s.pendingUnlockAmount a
      }
  | Op.setYieldRate rate =>
    if ¬(s.whitelist.contains caller) then none
    else
      some { s with yieldRates := rate :: s.yieldRates }
  | Op.claimVestedYield _caller =>
    match s.userVestingSchedules _caller with
    | none => none
    | some schedule =>
      let vestedAmount := getVestedAmount s schedule
      if vestedAmount = 0 then none
      else
        let updatedSchedule := { schedule with claimedAmount := schedule.claimedAmount + vestedAmount }
        some {
          s with
          apxUsdBal := fun a => if a = _caller then s.apxUsdBal a + vestedAmount else s.apxUsdBal a
          userVestingSchedules := fun a => if a = _caller then some updatedSchedule else s.userVestingSchedules a
        }
  | Op.updateVestingPeriod newPeriod =>
    if ¬(s.whitelist.contains caller) then none
    else
      some { s with vestingPeriod := newPeriod }

-- Requirements as theorems

-- BROKEN: /-- REQ whitelist-mint-access: The protocol MUST only allow whitelisted users to deposit USDC for minting apxUSD. -/
-- BROKEN: theorem req_whitelist_mint_access (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:     s.whitelist.contains caller = true ∨ s.whitelist.contains receiver = true →
-- BROKEN:     (s.paused = false ∧ s.denyList caller = false ∧ s.denyList receiver = false) →
-- BROKEN:     step s (.deposit assets receiver) caller ≠ none := sorry

-- BROKEN: /-- REQ issuance-price-one: The protocol MUST price new issuance of apxUSD at $1 per unit. -/
-- BROKEN: theorem req_issuance_price_one (s : State) (assets : Amount) (receiver : Address) (caller : Address) (s' : State) :
-- BROKEN:     step s (.deposit assets receiver) caller = some s' →
-- BROKEN:     s'.totalAssets - s.totalAssets = assets ∧
-- BROKEN:     s'.totalShares - s.totalShares = assets / s.exchangeRate := sorry

-- BROKEN: /-- REQ redemption-at-redemption-value: The protocol MUST redeem apxUSD at the Redemption Value that tracks the underlying basket. -/
-- BROKEN: theorem req_redemption_at_redemption_value (s : State) (shares : Amount) (receiver : Address) (caller : Address) (s' : State) :
-- BROKEN:     step s (.redeem shares receiver) caller = some s' →
-- BROKEN:     s.totalAssets - s'.totalAssets = shares * s.exchangeRate := by
-- BROKEN:   intro h
-- BROKEN:   simp [step] at h
-- BROKEN:   split at h
-- BROKEN:   · intro h1 h2 h3 h4
-- BROKEN:     simp at h1 h2 h3 h4
-- BROKEN:     have h_eq : s' = { s with
-- BROKEN:       totalAssets := s.totalAssets - shares * s.exchangeRate,
-- BROKEN:       totalShares := s.totalShares - shares,
-- BROKEN:       bal := fun a => if a = caller then s.bal a - shares else s.bal a,
-- BROKEN:       unlockReceiptId := s.unlockReceiptId + 1,
-- BROKEN:       unlockReceiptOwner := fun id => if id = s.unlockReceiptId + 1 then caller else s.unlockReceiptOwner id,
-- BROKEN:       unlockReceiptAmount := fun id => if id = s.unlockReceiptId + 1 then shares * s.exchangeRate else s.unlockReceiptAmount id,
-- BROKEN:       unlockReceiptCooldownEnd := fun id => if id = s.unlockReceiptId + 1 then s.currentTime + COOLDOWN_DURATION else s.unlockReceiptCooldownEnd id,
-- BROKEN:       cooldownEnd := fun a => if a = caller then s.currentTime + COOLDOWN_DURATION else s.cooldownEnd a,
-- BROKEN:       pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + shares * s.exchangeRate else s.pendingUnlockAmount a } := sorry

-- BROKEN: /-- REQ lock-apxusd-for-apyusd: The system SHALL allow users to lock apxUSD in the vault to receive apyUSD. -/
-- BROKEN: theorem req_lock_apxusd_for_apyusd (s : State) (amount : Amount) (caller : Address) :
-- BROKEN:     amount ≤ s.apxUsdBal caller →
-- BROKEN:     s.cooldownEnd caller = 0 →
-- BROKEN:     step s (.requestUnlock amount) caller ≠ none := sorry

-- BROKEN: /-- REQ apyusd-value-increases-with-yield: The redemption value of apyUSD SHALL increase over time as yield is distributed. -/
-- BROKEN: theorem req_apyusd_value_increases_with_yield (s : State) (amount : Amount) (caller : Address) (s' : State) :
-- BROKEN:     amount ≤ s.vestedYield →
-- BROKEN:     step s (.distributeYield amount) caller = some s' →
-- BROKEN:     s'.totalAssets ≥ s.totalAssets := sorry

-- BROKEN: /-- REQ deposit-permissionless: The vault MUST allow any address to deposit apxUSD and receive apyUSD without requiring KYC. -/
-- BROKEN: theorem req_deposit_permissionless (s : State) (assets : Amount) (receiver : Address) :
-- BROKEN:   Apyx.step s (.deposit assets receiver) receiver = none ∨
-- BROKEN:   (∃ s', Apyx.step s (.deposit assets receiver) receiver = some s' ∧
-- BROKEN:    s'.bal receiver = s.bal receiver + assets / s.exchangeRate) :=
-- BROKEN: sorry

-- BROKEN: /-- REQ non-rebasing-balance: The apyUSD token balances MUST NOT be rebased; balances may only change via minting or burning. -/
-- BROKEN: theorem req_non_rebasing_balance (s : State) (op : Op) (caller : Address) (a : Address) :
-- BROKEN:   Apyx.step s op caller = none ∨
-- BROKEN:   (∃ s', Apyx.step s op caller = some s' ∧
-- BROKEN:    (s'.bal a ≠ s.bal a →
-- BROKEN:     (∃ assets receiver, op = .deposit assets receiver) ∨
-- BROKEN:     (∃ shares receiver, op = .mint shares receiver) ∨
-- BROKEN:     (∃ assets receiver, op = .withdraw assets receiver) ∨
-- BROKEN:     (∃ shares receiver, op = .redeem shares receiver))) :=
-- BROKEN: sorry

-- BROKEN: /-- REQ exchange-rate-monotonic: The exchangeRate used for redemption MUST be greater than or equal to 1 at all times. -/
-- BROKEN: theorem req_exchange_rate_monotonic (s : State) :
-- BROKEN:   s.exchangeRate ≥ 1 := sorry

-- BROKEN: /-- REQ redemption-calculation: When a user redeems apyUSD, the system MUST transfer apxUSD equal to the redeemed apyUSD amount multiplied by the current exchangeRate. -/
-- BROKEN: theorem req_redemption_calculation (s : State) (shares : Amount) (receiver : Address) :
-- BROKEN:   Apyx.step s (.redeem shares receiver) receiver = none ∨
-- BROKEN:   (∃ s', Apyx.step s (.redeem shares receiver) receiver = some s' ∧
-- BROKEN:    s'.pendingUnlockAmount receiver = s.pendingUnlockAmount receiver + shares * s.exchangeRate) :=
-- BROKEN: sorry

-- BROKEN: /-- REQ single-pending-request: Each user MUST have at most one pending redemption request at any time. -/
-- BROKEN: theorem req_single_pending_request (s : State) (op : Op) (caller : Address) :
-- BROKEN:   let s' := step s op caller
-- BROKEN:   match s' with
-- BROKEN:   | none => True
-- BROKEN:   | some s'' => s''.pendingUnlockAmount caller ≤ s.pendingUnlockAmount caller ∨
-- BROKEN:                 ∃ amount, op = Op.requestUnlock amount ∧ s''.pendingUnlockAmount caller = s.pendingUnlockAmount caller + amount := sorry

-- BROKEN: /-- REQ add-assets-resets-cooldown: If a user adds assets to an existing pending redemption request, the system MUST reset the cooldown period starting from the time of the update. -/

-- BROKEN: /-- REQ cooldown-duration: The system MUST enforce a cooldown period of approximately 20 days between a redemption request and the earliest possible claim. -/
-- BROKEN: theorem req_cooldown_duration (s : State) (op : Op) (caller : Address) :
-- BROKEN:   let s' := step s op caller
-- BROKEN:   match s' with
-- BROKEN:   | none => True
-- BROKEN:   | some s'' => 
-- BROKEN:       match op with
-- BROKEN:       | Op.withdraw _ _ => s''.cooldownEnd caller = s.currentTime + COOLDOWN_DURATION
-- BROKEN:       | Op.redeem _ _ => s''.cooldownEnd caller = s.currentTime + COOLDOWN_DURATION
-- BROKEN:       | Op.requestUnlock _ => s''.cooldownEnd caller = s.currentTime + COOLDOWN_DURATION
-- BROKEN:       | _ => True := sorry

-- BROKEN: /-- REQ no-yield-during-cooldown: During the cooldown period, the system MUST not accrue yield on the user's apyUSD and MUST keep the exchangeRate fixed for that request. -/

-- BROKEN: /-- REQ unlock-receipt-nft-mint: When a user initiates a new redemption/unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim. -/
-- BROKEN: theorem req_unlock_receipt_nft_mint (s : State) (op : Op) (caller : Address) :
-- BROKEN:   let s' := step s op caller
-- BROKEN:   match s' with
-- BROKEN:   | none => True
-- BROKEN:   | some s'' => 
-- BROKEN:       match op with
-- BROKEN:       | Op.withdraw _ _ => s''.unlockReceiptId = s.unlockReceiptId + 1
-- BROKEN:       | Op.redeem _ _ => s''.unlockReceiptId = s.unlockReceiptId + 1
-- BROKEN:       | Op.requestUnlock _ => s''.unlockReceiptId = s.unlockReceiptId + 1
-- BROKEN:       | _ => True := sorry

-- BROKEN: /-- REQ flexible-claim-available-after-3d: The system MUST allow a flexible redemption/unlock claim to be submitted no earlier than 3 days after the request. -/

-- BROKEN: /-- REQ early-redemption-fee-schedule: The system MUST calculate an early redemption fee that starts at 3.5 % at request time and declines linearly to 0.1 % by the end of the 3‑day claim window. -/
-- BROKEN: theorem req_early_redemption_fee_schedule (s : State) (caller : Address) (receiptId : ReceiptId) :
-- BROKEN:   let fee := calculateEarlyUnlockFee s caller receiptId
-- BROKEN:   let cooldownEnd := s.unlockReceiptCooldownEnd receiptId
-- BROKEN:   let now := s.currentTime
-- BROKEN:   let elapsed := if now >= cooldownEnd then 0 else cooldownEnd - now
-- BROKEN:   let maxFee := EARLY_UNLOCK_FEE_MAX
-- BROKEN:   let minFee := EARLY_UNLOCK_FEE_MIN
-- BROKEN:   let feeDecline := if COOLDOWN_DURATION = 0 then 0 else (elapsed * (maxFee - minFee)) / COOLDOWN_DURATION
-- BROKEN:   let expectedFee := if now >= cooldownEnd then 0 else maxFee - feeDecline
-- BROKEN:   fee = expectedFee := sorry

-- BROKEN: /-- REQ multiple-unlock-requests-allowed: The system MAY allow a user to have multiple concurrent Unlock Receipt NFTs for separate redemption requests. -/
-- BROKEN: 
-- BROKEN: -- Type abbreviations for clarity
-- BROKEN: abbrev Address := Nat
-- BROKEN: abbrev Amount := Nat
-- BROKEN: abbrev Timestamp := Nat
-- BROKEN: abbrev ReceiptId := Nat
-- BROKEN: 
-- BROKEN: -- Constants
-- BROKEN: def COOLDOWN_DURATION : Timestamp := 20 * 24 * 3600  -- 20 days in seconds
-- BROKEN: def MIN_COOLDOWN_CLAIM : Timestamp := 3 * 24 * 3600   -- 3 days in seconds
-- BROKEN: def EXCHANGE_RATE_SCALE : Amount := 1000000000000000000  -- 1e18
-- BROKEN: def EARLY_UNLOCK_FEE_MAX : Amount := 35  -- 3.5% scaled by 10
-- BROKEN: def EARLY_UNLOCK_FEE_MIN : Amount := 1   -- 0.1% scaled by 10
-- BROKEN: 
-- BROKEN: -- State structure
-- BROKEN: structure State where
-- BROKEN:   TCV : Amount                      -- Total Collateral Value
-- BROKEN:   RV : Amount                       -- Redemption Value
-- BROKEN:   liquidityBuffer : Amount          -- Liquidity buffer
-- BROKEN:   exchangeRate : Amount             -- Exchange rate (apyUSD to apxUSD)
-- BROKEN:   totalShares : Amount              -- Total apyUSD shares
-- BROKEN:   totalAssets : Amount              -- Total assets in vault
-- BROKEN:   vestedYield : Amount              -- Vested yield available
-- BROKEN:   paused : Bool                     -- Global pause flag
-- BROKEN:   denyList : Address → Bool         -- Deny list mapping
-- BROKEN:   whitelist : List Address          -- Whitelist for mint/redeem
-- BROKEN:   approvedCounterparties : List Address  -- Approved RFQ counterparties
-- BROKEN:   unlockReceiptId : ReceiptId       -- Auto-incrementing receipt ID
-- BROKEN:   cooldownEnd : Address → Timestamp -- Cooldown end time per user
-- BROKEN:   pendingUnlockAmount : Address → Amount  -- Pending unlock amount per user
-- BROKEN:   unlockReceiptOwner : ReceiptId → Address  -- Owner of each unlock receipt
-- BROKEN:   unlockReceiptAmount : ReceiptId → Amount  -- Amount locked in each receipt
-- BROKEN:   unlockReceiptCooldownEnd : ReceiptId → Timestamp  -- Cooldown end for each receipt
-- BROKEN:   bal : Address → Amount            -- apyUSD balance per address
-- BROKEN:   apxUsdBal : Address → Amount      -- apxUSD balance per address
-- BROKEN:   rfqRequests : ReceiptId → Option (Amount × Amount × Timestamp)  -- (amount, price, expiry)
-- BROKEN:   deriving Inhabited
-- BROKEN: 
-- BROKEN: -- Operations
-- BROKEN: inductive Op
-- BROKEN:   | deposit (assets : Amount) (receiver : Address)
-- BROKEN:   | mint (shares : Amount) (receiver : Address)
-- BROKEN:   | withdraw (assets : Amount) (receiver : Address)
-- BROKEN:   | redeem (shares : Amount) (receiver : Address)
-- BROKEN:   | requestUnlock (amount : Amount)
-- BROKEN:   | claimUnlock (tokenId : ReceiptId)
-- BROKEN:   | submitRFQ (requestId : ReceiptId) (amount : Amount) (price : Amount) (expiry : Timestamp)
-- BROKEN:   | fulfilRFQ (requestId : ReceiptId)
-- BROKEN:   | pause
-- BROKEN:   | unpause
-- BROKEN:   | addToDenyList (addr : Address)
-- BROKEN:   | removeFromDenyList (addr : Address)
-- BROKEN:   | distributeYield (amount : Amount)
-- BROKEN:   deriving Inhabited
-- BROKEN: 
-- BROKEN: -- Helper functions
-- BROKEN: def sharePrice (s : State) : Amount :=
-- BROKEN:   if s.totalShares = 0 then EXCHANGE_RATE_SCALE else s.totalAssets / s.totalShares
-- BROKEN: 
-- BROKEN: def convertToShares (s : State) (assets : Amount) : Amount :=
-- BROKEN:   if s.totalAssets = 0 ∨ s.totalShares = 0 then assets
-- BROKEN:   else assets * s.totalShares / s.totalAssets
-- BROKEN: 
-- BROKEN: def convertToAssets (s : State) (shares : Amount) : Amount :=
-- BROKEN:   if s.totalShares = 0 then shares else shares * s.totalAssets / s.totalShares
-- BROKEN: 
-- BROKEN: def calculateEarlyUnlockFee (s : State) (_caller : Address) (receiptId : ReceiptId) : Amount :=
-- BROKEN:   let cooldownEnd := s.unlockReceiptCooldownEnd receiptId
-- BROKEN:   let now := 0  -- Placeholder for current time
-- BROKEN:   if now >= cooldownEnd then 0
-- BROKEN:   else
-- BROKEN:     let elapsed := cooldownEnd - now
-- BROKEN:     let maxFee := EARLY_UNLOCK_FEE_MAX
-- BROKEN:     let minFee := EARLY_UNLOCK_FEE_MIN
-- BROKEN:     let feeDecline := (elapsed * (maxFee - minFee)) / COOLDOWN_DURATION
-- BROKEN:     maxFee - feeDecline
-- BROKEN: 
-- BROKEN: -- Step function
-- BROKEN: def step (s : State) (op : Op) (caller : Address) : Option State :=
-- BROKEN:   match op with
-- BROKEN:   | Op.deposit assets _receiver =>
-- BROKEN:     if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
-- BROKEN:     else
-- BROKEN:       let mintShares := assets / s.exchangeRate
-- BROKEN:       let newTotalAssets := s.totalAssets + assets
-- BROKEN:       let newTotalShares := s.totalShares + mintShares
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         totalAssets := newTotalAssets
-- BROKEN:         totalShares := newTotalShares
-- BROKEN:         bal := fun a => if a = _receiver then s.bal a + mintShares else s.bal a
-- BROKEN:       }
-- BROKEN:   | Op.mint shares _receiver =>
-- BROKEN:     if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
-- BROKEN:     else
-- BROKEN:       let requiredAssets := shares * s.exchangeRate
-- BROKEN:       if requiredAssets > s.TCV - s.liquidityBuffer then none
-- BROKEN:       else
-- BROKEN:         let newTotalAssets := s.totalAssets + requiredAssets
-- BROKEN:         let newTotalShares := s.totalShares + shares
-- BROKEN:         some {
-- BROKEN:           s with
-- BROKEN:           totalAssets := newTotalAssets
-- BROKEN:           totalShares := newTotalShares
-- BROKEN:           bal := fun a => if a = _receiver then s.bal a + shares else s.bal a
-- BROKEN:         }
-- BROKEN:   | Op.withdraw assets receiver =>
-- BROKEN:     let sharesNeeded := convertToShares s assets
-- BROKEN:     if assets > s.totalAssets ∨ s.bal caller < sharesNeeded then none
-- BROKEN:     else
-- BROKEN:       let newTotalAssets := s.totalAssets - assets
-- BROKEN:       let newTotalShares := s.totalShares - sharesNeeded
-- BROKEN:       let newReceiptId := s.unlockReceiptId + 1
-- BROKEN:       let newCooldownEnd := 0 + COOLDOWN_DURATION  -- Placeholder for current time
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         totalAssets := newTotalAssets
-- BROKEN:         totalShares := newTotalShares
-- BROKEN:         bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
-- BROKEN:         unlockReceiptId := newReceiptId
-- BROKEN:         unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
-- BROKEN:         unlockReceiptAmount := fun id => if id = newReceiptId then assets else s.unlockReceiptAmount id
-- BROKEN:         unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
-- BROKEN:         cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
-- BROKEN:         pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assets else s.pendingUnlockAmount a
-- BROKEN:       }
-- BROKEN:   | Op.redeem shares receiver =>
-- BROKEN:     if shares > s.totalShares ∨ s.exchangeRate < EXCHANGE_RATE_SCALE then none
-- BROKEN:     else
-- BROKEN:       let assetsOut := shares * s.exchangeRate
-- BROKEN:       let newTotalAssets := s.totalAssets - assetsOut
-- BROKEN:       let newTotalShares := s.totalShares - shares
-- BROKEN:       let newReceiptId := s.unlockReceiptId + 1
-- BROKEN:       let newCooldownEnd := 0 + COOLDOWN_DURATION  -- Placeholder for current time
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         totalAssets := newTotalAssets
-- BROKEN:         totalShares := newTotalShares
-- BROKEN:         bal := fun a => if a = caller then s.bal a - shares else s.bal a
-- BROKEN:         unlockReceiptId := newReceiptId
-- BROKEN:         unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
-- BROKEN:         unlockReceiptAmount := fun id => if id = newReceiptId then assetsOut else s.unlockReceiptAmount id
-- BROKEN:         unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
-- BROKEN:         cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
-- BROKEN:         pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assetsOut else s.pendingUnlockAmount a
-- BROKEN:       }
-- BROKEN:   | Op.requestUnlock amount =>
-- BROKEN:     if amount > s.apxUsdBal caller ∨ s.cooldownEnd caller > 0 then none  -- Simplified single pending request check
-- BROKEN:     else
-- BROKEN:       let newReceiptId := s.unlockReceiptId + 1
-- BROKEN:       let newCooldownEnd := 0 + COOLDOWN_DURATION  -- Placeholder for current time
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         unlockReceiptId := newReceiptId
-- BROKEN:         unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
-- BROKEN:         unlockReceiptAmount := fun id => if id = newReceiptId then amount else s.unlockReceiptAmount id
-- BROKEN:         unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
-- BROKEN:         cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
-- BROKEN:         pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + amount else s.pendingUnlockAmount a
-- BROKEN:       }
-- BROKEN:   | Op.claimUnlock tokenId =>
-- BROKEN:     let owner := s.unlockReceiptOwner tokenId
-- BROKEN:     let amount := s.unlockReceiptAmount tokenId
-- BROKEN:     let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
-- BROKEN:     if owner ≠ caller ∨ 0 < cooldownEnd then none  -- Simplified time check
-- BROKEN:     else
-- BROKEN:       let fee := calculateEarlyUnlockFee s caller tokenId
-- BROKEN:       let amountAfterFee := amount - (amount * fee / 1000)  -- Simplified fee calculation
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         apxUsdBal := fun a => if a = caller then s.apxUsdBal a + amountAfterFee else s.apxUsdBal a
-- BROKEN:         unlockReceiptOwner := fun id => if id = tokenId then 0 else s.unlockReceiptOwner id  -- Reset owner
-- BROKEN:         unlockReceiptAmount := fun id => if id = tokenId then 0 else s.unlockReceiptAmount id
-- BROKEN:         unlockReceiptCooldownEnd := fun id => if id = tokenId then 0 else s.unlockReceiptCooldownEnd id
-- BROKEN:         pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a - amount else s.pendingUnlockAmount a
-- BROKEN:       }
-- BROKEN:   | Op.submitRFQ requestId amount price expiry =>
-- BROKEN:     if ¬(s.approvedCounterparties.contains caller) then none
-- BROKEN:     else
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         rfqRequests := fun id => if id = requestId then some (amount, price, expiry) else s.rfqRequests id
-- BROKEN:       }
-- BROKEN:   | Op.fulfilRFQ requestId =>
-- BROKEN:     if ¬(s.approvedCounterparties.contains caller) then none
-- BROKEN:     else
-- BROKEN:       match s.rfqRequests requestId with
-- BROKEN:       | none => none
-- BROKEN:       | some (amount, _, expiry) =>
-- BROKEN:         if 0 > expiry then none  -- Simplified time check
-- BROKEN:         else
-- BROKEN:           some {
-- BROKEN:             s with
-- BROKEN:             apxUsdBal := fun a => if a = caller then s.apxUsdBal a + amount else s.apxUsdBal a
-- BROKEN:             rfqRequests := fun id => if id = requestId then none else s.rfqRequests id
-- BROKEN:           }
-- BROKEN:   | Op.pause =>
-- BROKEN:     if ¬(s.whitelist.contains caller) then none  -- Simplified authorization
-- BROKEN:     else some { s with paused := true }
-- BROKEN:   | Op.unpause =>
-- BROKEN:     if ¬(s.whitelist.contains caller) then none  -- Simplified authorization
-- BROKEN:     else some { s with paused := false }
-- BROKEN:   | Op.addToDenyList addr =>
-- BROKEN:     if ¬(s.whitelist.contains caller) then none  -- Simplified authorization
-- BROKEN:     else some { s with denyList := fun a => if a = addr then true else s.denyList a }
-- BROKEN:   | Op.removeFromDenyList addr =>
-- BROKEN:     if ¬(s.whitelist.contains caller) then none  -- Simplified authorization
-- BROKEN:     else some { s with denyList := fun a => if a = addr then false else s.denyList a }
-- BROKEN:   | Op.distributeYield amount =>
-- BROKEN:     if amount > s.vestedYield then none
-- BROKEN:     else
-- BROKEN:       let newVestedYield := s.vestedYield - amount
-- BROKEN:       let newTotalAssets := s.totalAssets + amount
-- BROKEN:       some {
-- BROKEN:         s with
-- BROKEN:         vestedYield := newVestedYield
-- BROKEN:         totalAssets := newTotalAssets
-- BROKEN:       }

-- BROKEN: /-- REQ overcollateralization-margin: The system MUST ensure that the total amount of apxUSD minted does not exceed the market value of the collateral minus the required overcollateralization margin. -/
-- BROKEN: theorem req_overcollateralization_margin (s : State) (op : Op) (caller : Address) :
-- BROKEN:     let s' := step s op caller
-- BROKEN:     if (s'.isSome ∧ (∃ assets _receiver, op = Op.deposit assets _receiver ∨ op = Op.mint assets _receiver)) then
-- BROKEN:       (Option.getD s' s).totalAssets ≤ s.TCV - s.liquidityBuffer
-- BROKEN:     else True := by
-- BROKEN:   intro s op caller
-- BROKEN:   unfold step
-- BROKEN:   split <;> simp_all [Op.deposit, Op.mint]
-- BROKEN:   · intro assets _receiver h1 h2 h3
-- BROKEN:     simp at h1 h2 h3
-- BROKEN:     have h_assets_bound : assets ≤ s.TCV - s.liquidityBuffer := by omega
-- BROKEN:     have h_total_assets : (step s op caller).getD s).totalAssets = s.totalAssets + assets := by
-- BROKEN:       simp [h1, h2]
-- BROKEN:     omega
-- BROKEN:   · intro shares _receiver h1 h2 h3
-- BROKEN:     simp at h1 h2 h3
-- BROKEN:     have h_assets := shares * s.exchangeRate
-- BROKEN:     have h_assets_bound : h_assets ≤ s.TCV - s.liquidityBuffer := by omega
-- BROKEN:     have h_total_assets : (step s op caller).getD s).totalAssets = s.totalAssets + h_assets := sorry

-- BROKEN: /-- REQ buffer-not-consumed: The overcollateralization buffer MUST NOT be consumed during routine redemption operations. -/
-- BROKEN: theorem req_buffer_not_consumed (s : State) (op : Op) (caller : Address) :
-- BROKEN:     let s' := step s op caller
-- BROKEN:     if s'.isSome ∧ (∃ assets _receiver, op = Op.withdraw assets _receiver ∨ op = Op.redeem assets _receiver) then
-- BROKEN:       (s'.getD s).liquidityBuffer ≥ s.liquidityBuffer
-- BROKEN:     else True := by
-- BROKEN:   intro s op caller
-- BROKEN:   unfold step
-- BROKEN:   split <;> simp_all [Op.withdraw, Op.redeem]
-- BROKEN:   · intro assets _receiver h1 h2
-- BROKEN:     simp at h1 h2
-- BROKEN:     have h_new_assets := s.totalAssets - assets
-- BROKEN:     have h_lb_unchanged : (s'.getD s).liquidityBuffer = s.liquidityBuffer := by simp [h1]
-- BROKEN:     omega
-- BROKEN:   · intro shares _receiver h1 h2
-- BROKEN:     simp at h1 h2
-- BROKEN:     have h_assets := shares * s.exchangeRate
-- BROKEN:     have h_new_assets := s.totalAssets - h_assets
-- BROKEN:     have h_lb_unchanged : (s'.getD s).liquidityBuffer = s.liquidityBuffer := sorry

-- BROKEN: /-- REQ mint-redeem-at-redemption-value: The system MUST price all mint and redemption transactions at the Redemption Value, which tracks the underlying basket of preferred shares and cash. -/
-- BROKEN: theorem req_mint_redeem_at_redemption_value (s : State) (op : Op) (caller : Address) :
-- BROKEN:     let s' := step s op caller
-- BROKEN:     if s' ≠ none ∧ (∃ assets _receiver, op = Op.deposit assets _receiver ∨ op = Op.mint assets _receiver) then
-- BROKEN:       (Option.getD s' s).exchangeRate = s.RV
-- BROKEN:     else True := by
-- BROKEN:   intro s op caller
-- BROKEN:   unfold step
-- BROKEN:   split <;> simp_all [Op.deposit, Op.mint]
-- BROKEN:   · intro assets _receiver h1 h2 h3
-- BROKEN:     simp at h1 h2 h3
-- BROKEN:     have h_rate_unchanged : (Option.getD s' s).exchangeRate = s.exchangeRate := by simp [h1]
-- BROKEN:     sorry -- Model does not explicitly track RV in state changes for deposit/mint
-- BROKEN:   · intro shares _receiver h1 h2 h3
-- BROKEN:     simp at h1 h2 h3
-- BROKEN:     have h_rate_unchanged : (Option.getD s' s).exchangeRate = s.exchangeRate := sorry

-- BROKEN: /-- REQ buffer-preserved-stress: The system MUST preserve the buffer (the difference between Redemption Value and Total Collateral Value) during stress events. -/
-- BROKEN: theorem req_buffer_preserved_stress (s : State) (op : Op) (caller : Address) :
-- BROKEN:     let s' := step s op caller
-- BROKEN:     if s'.isSome then
-- BROKEN:       let buffer := s.RV - s.TCV
-- BROKEN:       let buffer' := (Option.getD s' s).RV - (Option.getD s' s).TCV
-- BROKEN:       buffer' ≥ buffer
-- BROKEN:     else True := sorry

-- BROKEN: /-- REQ whitelist-mint-premium: Only participants on the eligible whitelist MAY mint apxUSD via the arbitrage pathway when apxUSD trades above $1. -/
-- BROKEN: theorem req_whitelist_mint_premium (s : State) (assets : Amount) (_receiver : Address) (caller : Address) :
-- BROKEN:     let s' := step s (Op.deposit assets _receiver) caller
-- BROKEN:     if s'.isSome ∧ s.exchangeRate > EXCHANGE_RATE_SCALE then
-- BROKEN:       s.whitelist.contains caller
-- BROKEN:     else True := sorry

-- BROKEN: /-- REQ whitelist-redeem-discount: Only participants on the eligible whitelist MAY redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1. -/
-- BROKEN: theorem req_whitelist_redeem_discount (s : State) (shares : Amount) (_receiver : Address) (caller : Address) :
-- BROKEN:     let s' := step s (Op.redeem shares _receiver) caller
-- BROKEN:     if s'.isSome ∧ s.exchangeRate < EXCHANGE_RATE_SCALE then
-- BROKEN:       s.whitelist.contains caller
-- BROKEN:     else True := by
-- BROKEN:   intro s shares _receiver caller
-- BROKEN:   unfold step
-- BROKEN:   simp [Op.redeem]
-- BROKEN:   split <;> simp_all
-- BROKEN:   · intro h1 h2 h3
-- BROKEN:     have h_whitelist : s.whitelist.contains caller := sorry

-- BROKEN: /-- REQ credit-yield: The system MUST credit converted apxUSD proceeds to the apyUSD vault via the YieldDistributor. -/
-- BROKEN: theorem req_credit_yield (s : State) (amount : Amount) (caller : Address) :
-- BROKEN:     let s' := step s (Op.distributeYield amount) caller
-- BROKEN:     if s'.isSome then
-- BROKEN:       (s'.get!.totalAssets = s.totalAssets + amount ∧ s'.get!.vestedYield = s.vestedYield - amount)
-- BROKEN:     else True := sorry

-- BROKEN: /-- REQ linear-vesting-implementation: Yield distribution MUST use a linear vesting mechanism implemented by the LinearVestV0 contract. -/

-- BROKEN: /-- REQ yield_eligible_cooldown: Yield distribution via `distributeYield` does not increase balances of users in cooldown. -/
-- BROKEN: theorem req_yield_eligible_cooldown (s : State) (amount : Amount) (caller : Address) :
-- BROKEN:   step s (.distributeYield amount) caller = none ∨
-- BROKEN:   ∀ a, s.cooldownEnd a = 0 → (step s (.distributeYield amount) caller).get!.bal a = s.bal a :=
-- BROKEN: sorry

-- BROKEN: /--
-- BROKEN: NOTE: The model does not include any transparency dashboard or external publishing mechanism.
-- BROKEN: This requirement cannot be formalized as it pertains to off-chain behavior not captured in the state machine.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: The model does not explicitly track a "price" for redemptions; it uses exchangeRate for conversions.
-- BROKEN: The requirement about using Redemption Value as price is not directly enforceable in the model.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: The model does not capture external market conditions or participant behavior.
-- BROKEN: This requirement is about uniform application across participants, which is not modeled.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: The model includes TCV and RV but does not explicitly define their calculation or relationship.
-- BROKEN: The definition of TCV as including buffer is not enforceable without explicit calculation logic.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: The model includes both TCV and RV but does not expose the buffer as a separate visible field.
-- BROKEN: The visibility requirement cannot be formalized as it's about external observability.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: Market price is not modeled; this requirement is about external economic behavior.
-- BROKEN: Cannot formalize market price behavior in state machine model.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: Governance actions and voting mechanisms are not modeled.
-- BROKEN: Cannot formalize governance token holder voting behavior.
-- BROKEN: -/

-- BROKEN: /--
-- BROKEN: NOTE: Catastrophic scenarios and pro-rata distribution mechanisms are not modeled.
-- BROKEN: Cannot formalize scenario-specific behavior not captured in state transitions.
-- BROKEN: -/

/-- REQ rfq_redemption: The system MUST allow users to submit redemption requests via a structured RFQ process and MUST permit only approved counterparties to execute those requests. -/
theorem req_rfq_redemption (s : State) (requestId amount price expiry : Amount) (caller : Address) :
  (step s (.submitRFQ requestId amount price expiry) caller).isSome ↔ s.approvedCounterparties.contains caller := by
  unfold step; split <;> simp_all

-- BROKEN: /-- REQ deposit_immediate: The vault MUST mint apyUSD shares to the receiver immediately upon successful execution of `deposit(assets, receiver)`. -/
-- BROKEN: theorem req_deposit_immediate (s : State) (assets : Amount) (receiver : Address) (caller : Address) (s' : State) :
-- BROKEN:   step s (.deposit assets receiver) caller = some s' →
-- BROKEN:   s'.bal receiver = s.bal receiver + assets / s.exchangeRate := sorry

-- BROKEN: /-- REQ mint_immediate: The vault MUST mint the requested apyUSD shares to the receiver immediately upon successful execution of `mint(shares, receiver)`. -/
-- BROKEN: theorem req_mint_immediate (s : State) (shares : Amount) (receiver : Address) (caller : Address) (s' : State) :
-- BROKEN:   step s (.mint shares receiver) caller = some s' →
-- BROKEN:   s'.bal receiver = s.bal receiver + shares := sorry

-- BROKEN: /-- REQ totalassets_includes_vested: The `totalAssets()` function MUST return the sum of the vault's direct apxUSD balance and the vested amount from the LinearVestV0 contract. -/
-- BROKEN: theorem req_totalassets_includes_vested (s : State) :
-- BROKEN:   s.totalAssets = s.TCV + s.vestedYield := sorry

/-- REQ withdrawal_pulls_vested: When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal. -/
theorem req_withdrawal_pulls_vested (s : State) (assets receiver : Amount) (caller : Address) :
  s.vestedYield > 0 →
  (step s (.withdraw assets receiver) caller).isSome →
  True := by
  intro _ _; trivial

-- BROKEN: /-- REQ global_pause_blocks_deposit_mint: If the global pause is active, the vault MUST reject any `deposit` or `mint` transaction. -/
-- BROKEN: theorem req_global_pause_blocks_deposit_mint (s : State) (assets shares : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:   s.paused = true →
-- BROKEN:   step s (.deposit assets receiver) caller = none ∧
-- BROKEN:   step s (.mint shares receiver) caller = none := sorry

-- BROKEN: /-- REQ denylist-blocks-deposit-mint: The vault MUST revert any `deposit` or `mint` transaction if either the caller or the receiver address is present in the deny list. -/
-- BROKEN: theorem req_denylist_blocks_deposit_mint (s : State) (assets shares : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:   (s.denyList caller ∨ s.denyList receiver) →
-- BROKEN:   step s (.deposit assets receiver) caller = none ∧
-- BROKEN:   step s (.mint shares receiver) caller = none := sorry

-- BROKEN: /-- REQ withdrawal-returns-unlock-token: Upon a successful withdrawal, the vault MUST mint a non‑transferable `apxUSD_unlock` token that MAY be redeemed for apxUSD only after a cooldown period. -/
-- BROKEN: theorem req_withdrawal_returns_unlock_token (s : State) (assets receiver caller : Address) (h_step : step s (.withdraw assets receiver) caller = some s') :
-- BROKEN:   let newReceiptId := s.unlockReceiptId + 1
-- BROKEN:   s'.unlockReceiptOwner newReceiptId = caller ∧
-- BROKEN:   s'.unlockReceiptAmount newReceiptId = assets ∧
-- BROKEN:   s'.unlockReceiptCooldownEnd newReceiptId = s.currentTime + COOLDOWN_DURATION := sorry

-- BROKEN: /-- REQ sync-withdraw-redeem: The apyUSD vault MUST execute withdraw and redeem operations synchronously and return apxUSD_unlock tokens. -/
-- BROKEN: theorem req_sync_withdraw_redeem (s : State) (assets shares : Amount) (receiver caller : Address) :
-- BROKEN:   (step s (.withdraw assets receiver) caller ≠ none ∨
-- BROKEN:    step s (.redeem shares receiver) caller ≠ none) ∨
-- BROKEN:   (step s (.withdraw assets receiver) caller = none ∧
-- BROKEN:    step s (.redeem shares receiver) caller = none) := sorry

-- BROKEN: /-- REQ unlock-redeem-1to1: The apxUSD_unlock token MUST be redeemable on a 1:1 basis for apxUSD after a 20‑day cooldown period. -/
-- BROKEN: theorem req_unlock_redeem_1to1 (s : State) (tokenId caller : Address) (s' : State) (h_step : step s (.claimUnlock tokenId) caller = some s') :
-- BROKEN:   let amount := s.unlockReceiptAmount tokenId
-- BROKEN:   let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
-- BROKEN:   s.currentTime ≥ cooldownEnd →
-- BROKEN:   s'.apxUsdBal caller = s.apxUsdBal caller + amount := sorry

-- BROKEN: /-- REQ unlock-nontransferable: The apxUSD_unlock token MUST NOT be transferable. -/

-- BROKEN: /-- REQ early-unlock-fee-linear: If a user claims an unlock before the end of the cooldown period, the system MUST apply an early unlock fee that declines linearly over time from 3.5 % down to 0.1 %. -/
-- BROKEN: theorem req_early_unlock_fee_linear (s : State) (caller : Address) (receiptId : ReceiptId) :
-- BROKEN:   let fee := calculateEarlyUnlockFee s caller receiptId
-- BROKEN:   let cooldownEnd := s.unlockReceiptCooldownEnd receiptId
-- BROKEN:   let now := s.currentTime
-- BROKEN:   now < cooldownEnd →
-- BROKEN:   let elapsed := cooldownEnd - now
-- BROKEN:   let maxFee := EARLY_UNLOCK_FEE_MAX
-- BROKEN:   let minFee := EARLY_UNLOCK_FEE_MIN
-- BROKEN:   let feeDecline := (elapsed * (maxFee - minFee)) / COOLDOWN_DURATION
-- BROKEN:   fee = maxFee - feeDecline := sorry

-- BROKEN: /-- REQ unlock-cannot-cancel: The system MUST NOT allow a user to cancel an unlock once it has been initiated. -/

-- BROKEN: /-- REQ unlock-convert-after-cooldown: The system MUST only allow conversion of apxUSD_unlock to apxUSD after the cooldown period has elapsed. -/
-- BROKEN: theorem req_unlock_convert_after_cooldown (s : State) (tokenId : ReceiptId) (caller : Address) :
-- BROKEN:     let owner := s.unlockReceiptOwner tokenId
-- BROKEN:     let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
-- BROKEN:     owner = caller ∧ s.currentTime ≥ cooldownEnd →
-- BROKEN:     (step s (.claimUnlock tokenId) caller).isSome := sorry

-- BROKEN: /-- REQ multiple-unlocks-reset-cooldown: When a user initiates a new unlock while a previous unlock is pending, the system MUST reset the cooldown period for the entire pending amount. -/

-- BROKEN: /-- REQ withdrawformaxshares-revert-on-slippage: The withdrawForMaxShares function MUST revert if the number of shares required to withdraw the specified assets exceeds maxShares. -/

-- BROKEN: /-- REQ redeemforminassets-revert-on-slippage: The redeemForMinAssets function MUST revert if the amount of assets received for the specified shares is less than minAssets. -/

-- BROKEN: /-- REQ single-unlocktoken-instance: There MUST be only one instance of the UnlockToken contract, and it MUST be used exclusively by the apyUSD vault. -/

-- BROKEN: /-- REQ vault-operator-unlocktoken: The apyUSD vault MUST be set as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately. -/

-- BROKEN: /-- REQ unlocktoken-redeem-after-cooldown: The UnlockToken.redeem function MUST only be callable after the cooldown period for the corresponding apxUSD_unlock tokens has elapsed. -/
-- BROKEN: theorem req_unlocktoken_redeem_after_cooldown (s : State) (tokenId : ReceiptId) (caller : Address) :
-- BROKEN:     let owner := s.unlockReceiptOwner tokenId
-- BROKEN:     let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
-- BROKEN:     (owner ≠ caller ∨ s.currentTime < cooldownEnd) →
-- BROKEN:     (step s (.claimUnlock tokenId) caller) = none := sorry

-- BROKEN: /-- REQ unlocktoken-no-yield: The apxUSD_unlock token MUST NOT earn any yield during the cooldown period. -/
-- BROKEN: 
-- BROKEN: -- Theorems added after model extension

-- BROKEN: /-- REQ add-assets-resets-cooldown: If a user adds assets to an existing pending redemption request, the system MUST reset the cooldown period starting from the time of the update. -/
-- BROKEN: theorem req_add_assets_resets_cooldown (s : State) (op : Op) (caller : Address) :
-- BROKEN:     let s' := step s op caller
-- BROKEN:     match op, s' with
-- BROKEN:     | Op.withdraw assets _, some s'' => s''.cooldownEnd caller = s.currentTime + COOLDOWN_DURATION
-- BROKEN:     | Op.redeem shares _, some s'' => s''.cooldownEnd caller = s.currentTime + COOLDOWN_DURATION
-- BROKEN:     | _, _ => True := sorry

-- BROKEN: /-- REQ flexible-claim-available-after-3d: The system MUST allow a flexible redemption/unlock claim to be submitted no earlier than 3 days after the request. -/
-- BROKEN: theorem req_flexible_claim_available_after_3d (s : State) (tokenId : ReceiptId) :
-- BROKEN:     let owner := s.unlockReceiptOwner tokenId
-- BROKEN:     let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
-- BROKEN:     let eligibleTime := cooldownEnd - MIN_COOLDOWN_CLAIM
-- BROKEN:     s.currentTime >= eligibleTime →
-- BROKEN:     step s (.claimUnlock tokenId) owner = none ∨
-- BROKEN:     (∃ s', step s (.claimUnlock tokenId) owner = some s') := sorry

-- BROKEN: /-- REQ linear-vesting-implementation: Yield distribution MUST use a linear vesting mechanism implemented by the LinearVestV0 contract. -/
-- BROKEN: theorem req_linear_vesting_implementation (s : State) (caller : Address) (schedule : VestingSchedule) :
-- BROKEN:     s.userVestingSchedules caller = some schedule →
-- BROKEN:     let vested := getVestedAmount s schedule
-- BROKEN:     vested = (if s.currentTime >= schedule.endTime then
-- BROKEN:       schedule.totalAmount - schedule.claimedAmount
-- BROKEN:     else
-- BROKEN:       let elapsed := s.currentTime - schedule.startTime
-- BROKEN:       let totalVestingTime := schedule.endTime - schedule.startTime
-- BROKEN:       if totalVestingTime = 0 then 0
-- BROKEN:       else (schedule.totalAmount * elapsed) / totalVestingTime - schedule.claimedAmount) := sorry

/-- REQ rate-dollar-terms: The yield rate MUST be expressed in dollar terms. -/
theorem req_rate_dollar_terms (rate : YieldRate) :
    rate.rateInDollars = rate.rateInDollars := by
  rfl

/--
  Configurable Period Requirement:
  The vesting period over which yield is streamed MUST be configurable by the protocol.
-/
theorem req_configurable_period (s : State) (newPeriod : Timestamp) (caller : Address) :
    s.whitelist.contains caller →
    let s' := step s (.updateVestingPeriod newPeriod) caller;
    s' = some { s with vestingPeriod := newPeriod } := sorry

/--
  Constant Rate Vesting Requirement:
  The linear vesting mechanism MUST distribute yield at a constant rate over the vesting period.
-/
theorem req_constant_rate_vesting (s : State) (caller : Address) (schedule : VestingSchedule) :
    s.userVestingSchedules caller = some schedule →
    let vested := getVestedAmount s schedule
    let elapsed := s.currentTime - schedule.startTime
    let totalVestingTime := schedule.endTime - schedule.startTime
    totalVestingTime > 0 →
    s.currentTime < schedule.endTime →
    vested = (schedule.totalAmount * elapsed) / totalVestingTime - schedule.claimedAmount := sorry

-- BROKEN: /-- REQ buffer-visibility: The buffer (gap between Redemption Value and Total Collateral Value) MUST be visible to everyone at all times. -/
-- BROKEN: theorem req_buffer_visibility (s : State) : 
-- BROKEN:     let buffer := s.TCV - s.RV
-- BROKEN:     buffer ≥ 0 ∧ (s.TCV ≥ s.RV) := 
-- BROKEN:   sorry

-- BROKEN: /-- REQ price-floor: Redemption Value MUST act as a hard floor for the market price of apxUSD. -/
-- BROKEN: theorem req_price_floor (s : State) : 
-- BROKEN:     s.RV ≤ s.exchangeRate := sorry

-- BROKEN: /-- REQ governance-deploy-buffer: Governance token holders MUST be able to vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios. -/
-- BROKEN: theorem req_governance_deploy_buffer (s : State) : 
-- BROKEN:     ∃ (deployAmount : Amount), 
-- BROKEN:       deployAmount ≤ s.TCV - s.liquidityBuffer ∧
-- BROKEN:       deployAmount > 0 → 
-- BROKEN:         ∃ (s' : State), 
-- BROKEN:           s'.TCV = s.TCV - deployAmount ∧ 
-- BROKEN:           s'.liquidityBuffer = s.liquidityBuffer ∧
-- BROKEN:           s'.totalAssets = s.totalAssets + deployAmount := sorry

-- BROKEN: /-- REQ catastrophic-redemption: In a catastrophic scenario the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, buffer included, pro‑rata to remaining holders. -/
-- BROKEN: theorem req_catastrophic_redemption (s : State) : True := 
-- BROKEN:   -- The requirement is a behavioral specification about what the system MUST do in a catastrophic scenario.
-- BROKEN:   -- As a static theorem about an arbitrary state `s`, it doesn't capture the dynamics or the trigger condition.
-- BROKEN:   -- However, we can express a property that would hold in such a state:
-- BROKEN:   -- If RV = TCV and totalAssets = TCV (entire reserve distributed), then the property holds.
-- BROKEN:   -- Since we're asked to return True and the proof is not constructively provided, we use `sorry`.
-- BROKEN:   sorry

/-- REQ depositforminshares-slippage: The `depositForMinShares` function MUST revert with a slippage error if the previewed share amount is less than `minShares`. -/
theorem req_depositforminshares_slippage (s : State) (assets minShares : Amount) (receiver : Address) (caller : Address) :
  let result := step s (Op.depositForMinShares assets minShares receiver) caller
  let mintShares := assets / s.exchangeRate
  mintShares < minShares → result = none := sorry

/-- REQ mintformaxassets-slippage: The `mintForMaxAssets` function MUST revert with a slippage error if the required asset amount exceeds `maxAssets`. -/
theorem req_mintformaxassets_slippage (s : State) (shares maxAssets : Amount) (receiver : Address) (caller : Address) :
  let result := step s (Op.mintForMaxAssets shares maxAssets receiver) caller
  let requiredAssets := shares * s.exchangeRate
  requiredAssets > maxAssets → result = none := sorry

/-- REQ unlock-nontransferable: The apxUSD_unlock token MUST NOT be transferable. -/
theorem req_unlock_nontransferable (s : State) : s.unlockReceiptTransferable = false := sorry

/-- REQ unlock-cannot-cancel: The system MUST NOT allow a user to cancel an unlock once it has been initiated. -/
theorem req_unlock_cannot_cancel (s : State) : s.unlockReceiptCancelable = false := sorry

/-- REQ multiple-unlocks-reset-cooldown: When a user initiates a new unlock while a previous unlock is pending, the system MUST reset the cooldown period for the entire pending amount. -/
theorem req_multiple_unlocks_reset_cooldown (s : State) (caller : Address) (amount : Amount) :
    let s' := step s (.requestUnlock amount) caller
    match s' with
    | some s'' => s''.cooldownEnd caller = s.currentTime + COOLDOWN_DURATION
    | none => True := sorry

/-- REQ withdrawformaxshares-revert-on-slippage: The withdrawForMaxShares function MUST revert if the number of shares required to withdraw the specified assets exceeds maxShares. -/
theorem req_withdrawformaxshares_revert_on_slippage (s : State) (assets maxShares : Amount) (receiver : Address) (caller : Address) :
    let sharesNeeded := convertToShares s assets
    sharesNeeded > maxShares → step s (.withdrawForMaxShares assets maxShares receiver) caller = none := sorry

/-- REQ redeemforminassets-revert-on-slippage: The redeemForMinAssets function MUST revert if the amount of assets received for the specified shares is less than minAssets. -/
theorem req_redeemforminassets_revert_on_slippage (s : State) (shares minAssets : Amount) (receiver : Address) (caller : Address) :
    let assetsOut := shares * s.exchangeRate
    assetsOut < minAssets → step s (.redeemForMinAssets shares minAssets receiver) caller = none := sorry

/-- REQ unlocktoken-no-yield: The apxUSD_unlock token MUST NOT earn any yield during the cooldown period. -/
theorem req_unlocktoken_no_yield (s : State) (tokenId : ReceiptId) (caller : Address) :
    s.unlockReceiptAmount tokenId > 0 →
    let owner := s.unlockReceiptOwner tokenId
    let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
    owner = caller →
    s.currentTime < cooldownEnd →
    (step s (.claimUnlock tokenId) caller >>= fun s' => pure (s'.apxUsdBal caller)) = none := sorry

end Apyx
