namespace Apyx

-- Type abbreviations for clarity
abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat
abbrev ReceiptId := Nat

-- Constants
def COOLDOWN_DURATION : Timestamp := 20 * 24 * 60 * 60 -- 20 days in seconds
def MIN_COOLDOWN_CLAIM : Timestamp := 3 * 24 * 60 * 60 -- 3 days in seconds
def EXCHANGE_RATE_SCALE : Amount := 1000000000000000000 -- 1e18
def EARLY_UNLOCK_MAX_FEE : Amount := 35 -- 3.5% scaled by 10
def EARLY_UNLOCK_MIN_FEE : Amount := 1 -- 0.1% scaled by 10
def YIELD_VESTING_PERIOD : Timestamp := 20 * 24 * 60 * 60 -- 20 days in seconds

-- State structure
structure State where
  TCV : Amount -- Total Collateral Value
  RV : Amount -- Redemption Value
  liquidityBuffer : Amount
  exchangeRate : Amount -- scaled by EXCHANGE_RATE_SCALE
  paused : Bool
  denyList : Address → Bool
  vestedYield : Amount
  totalShares : Amount -- total apyUSD shares
  totalAssets : Amount -- TCV - liquidityBuffer + vestedYield
  bal : Address → Amount -- apyUSD balances
  apxBal : Address → Amount -- apxUSD balances
  cooldownEnd : Address → Timestamp -- cooldown end time per user
  unlockReceiptId : ReceiptId -- auto-incrementing ID
  unlockReceiptOwner : ReceiptId → Address -- owner of each receipt
  unlockReceiptAmount : ReceiptId → Amount -- amount locked in each receipt
  whitelist : Address → Bool -- for mint/redeem access control
  approvedCounterparties : Address → Bool
  lastYieldDistribution : Timestamp
  -- New fields for requirements
  yieldDistributionStart : Timestamp -- When the current yield distribution started
  yieldToDistribute : Amount -- Total yield to be distributed over the vesting period
  yieldDistributed : Amount -- Amount of yield already distributed
  apxUSDPrice : Amount -- Current market price of apxUSD (scaled)
  bufferDeployed : Bool -- Whether buffer has been deployed by governance
  bufferDeploymentVotes : Address → Bool -- Governance votes for buffer deployment
  unlockTokenTransferable : Bool := false -- apxUSD_unlock token transferability
  yieldAccrualPaused : Address → Bool -- Whether yield accrual is paused for a user during cooldown
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
  | upgradeTo (newImpl : Address)
  | distributeYield (amount : Amount)
  -- New operations for requirements
  | lockApxUSD (amount : Amount) (receiver : Address) -- Lock apxUSD to receive apyUSD
  | setApxUSDPrice (price : Amount) -- Set current market price of apxUSD
  | voteDeployBuffer (addr : Address) -- Governance vote to deploy buffer
  | deployBuffer -- Deploy the buffer
  | addAssetsToRedemption (tokenId : ReceiptId) (additionalAssets : Amount) -- Add assets to existing redemption
  | withdrawForMaxShares (assets : Amount) (maxShares : Amount) (receiver : Address) -- Withdraw with max shares check
  | redeemForMinAssets (shares : Amount) (minAssets : Amount) (receiver : Address) -- Redeem with min assets check
  | setYieldVestingPeriod (period : Timestamp) -- Set the yield vesting period
  deriving Inhabited

-- Helper functions
def sharePrice (s : State) : Amount :=
  if s.totalShares = 0 then EXCHANGE_RATE_SCALE else s.totalAssets / s.totalShares

def isWhitelisted (s : State) (addr : Address) : Bool :=
  s.whitelist addr

def isApprovedCounterparty (s : State) (addr : Address) : Bool :=
  s.approvedCounterparties addr

def hasPendingUnlock (s : State) (addr : Address) : Bool :=
  s.cooldownEnd addr > 0

def canClaimUnlock (s : State) (caller : Address) (tokenId : ReceiptId) (now : Timestamp) : Bool :=
  s.unlockReceiptOwner tokenId = caller ∧ 
  now ≥ s.cooldownEnd caller ∧
  s.cooldownEnd caller > 0

def calculateEarlyUnlockFee (s : State) (caller : Address) (now : Timestamp) : Amount :=
  let elapsed := now - (s.cooldownEnd caller - COOLDOWN_DURATION)
  let maxFeeScaled := EARLY_UNLOCK_MAX_FEE * 100000000000000000 -- scale to match exchange rate precision
  let minFeeScaled := EARLY_UNLOCK_MIN_FEE * 100000000000000000
  let feeDecline := (elapsed * (maxFeeScaled - minFeeScaled)) / COOLDOWN_DURATION
  maxFeeScaled - feeDecline

-- New helper functions for requirements
def getCurrentYieldRate (s : State) (now : Timestamp) : Amount :=
  if YIELD_VESTING_PERIOD = 0 then 0
  else (s.yieldToDistribute * EXCHANGE_RATE_SCALE) / YIELD_VESTING_PERIOD

def getYieldSinceLastDistribution (s : State) (now : Timestamp) : Amount :=
  if now < s.yieldDistributionStart then 0
  else
    let elapsed := now - s.yieldDistributionStart
    let rate := getCurrentYieldRate s now
    (rate * elapsed) / EXCHANGE_RATE_SCALE

def getBuffer (s : State) : Amount :=
  if s.RV > s.TCV then 0 else s.TCV - s.RV

def canMintApxUSD (s : State) (addr : Address) : Bool :=
  s.whitelist addr ∧ s.apxUSDPrice > EXCHANGE_RATE_SCALE -- apxUSD trades above $1

def canRedeemApxUSD (s : State) (addr : Address) : Bool :=
  s.whitelist addr ∧ s.apxUSDPrice < EXCHANGE_RATE_SCALE -- apxUSD trades below $1

def isUnlockTransferable (s : State) : Bool :=
  s.unlockTokenTransferable

def isYieldAccrualPaused (s : State) (addr : Address) : Bool :=
  s.yieldAccrualPaused addr

-- Step function
def step (s : State) (op : Op) (caller : Address) (now : Timestamp) : Option State :=
  match op with
  | Op.deposit assets _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let mintShares := assets * EXCHANGE_RATE_SCALE / s.exchangeRate
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
      let requiredAssets := shares * s.exchangeRate / EXCHANGE_RATE_SCALE
      let availableForMinting := s.TCV - s.liquidityBuffer
      if requiredAssets > availableForMinting then none
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
    let sharesNeeded := assets * EXCHANGE_RATE_SCALE / s.exchangeRate
    if assets > s.totalAssets ∨ s.bal caller < sharesNeeded ∨ hasPendingUnlock s caller then none
    else
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      let newVestedYield := s.vestedYield + 0 -- simplified yield pull
      let receiptId := s.unlockReceiptId
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        vestedYield := newVestedYield
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
        unlockReceiptId := receiptId + 1
        unlockReceiptOwner := fun id => if id = receiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = receiptId then assets else s.unlockReceiptAmount id
        cooldownEnd := fun a => if a = caller then now + COOLDOWN_DURATION else s.cooldownEnd a
      }
  | Op.redeem shares receiver =>
    if shares > s.totalShares ∨ s.exchangeRate < EXCHANGE_RATE_SCALE then none
    else
      let assetsOut := shares * s.exchangeRate / EXCHANGE_RATE_SCALE
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let receiptId := s.unlockReceiptId
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - shares else s.bal a
        unlockReceiptId := receiptId + 1
        unlockReceiptOwner := fun id => if id = receiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = receiptId then assetsOut else s.unlockReceiptAmount id
        cooldownEnd := fun a => if a = caller then now + COOLDOWN_DURATION else s.cooldownEnd a
      }
  | Op.requestUnlock amount =>
    if amount > s.apxBal caller ∨ hasPendingUnlock s caller then none
    else
      let receiptId := s.unlockReceiptId
      some {
        s with
        unlockReceiptId := receiptId + 1
        unlockReceiptOwner := fun id => if id = receiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = receiptId then amount else s.unlockReceiptAmount id
        cooldownEnd := fun a => if a = caller then now + COOLDOWN_DURATION else s.cooldownEnd a
      }
  | Op.claimUnlock tokenId =>
    if !canClaimUnlock s caller tokenId now then none
    else
      let amount := s.unlockReceiptAmount tokenId
      let fee := if now < s.cooldownEnd caller - (COOLDOWN_DURATION - MIN_COOLDOWN_CLAIM) 
                 then calculateEarlyUnlockFee s caller now 
                 else 0
      let amountAfterFee := amount - (amount * fee / 1000)
      some {
        s with
        apxBal := fun a => if a = caller then s.apxBal a + amountAfterFee else s.apxBal a
        unlockReceiptOwner := fun _ => 0 -- burn receipt
        unlockReceiptAmount := fun _ => 0
        cooldownEnd := fun a => if a = caller then 0 else s.cooldownEnd a
      }
  | Op.submitRFQ _requestId _amount _price _expiry =>
    if !isApprovedCounterparty s caller then none
    else some s
  | Op.fulfilRFQ _requestId =>
    if !isApprovedCounterparty s caller then none
    else some s
  | Op.pause =>
    if !s.whitelist caller then none
    else some { s with paused := true }
  | Op.unpause =>
    if !s.whitelist caller then none
    else some { s with paused := false }
  | Op.addToDenyList addr =>
    if !s.whitelist caller then none
    else some { s with denyList := fun a => if a = addr then true else s.denyList a }
  | Op.removeFromDenyList addr =>
    if !s.whitelist caller then none
    else some { s with denyList := fun a => if a = addr then false else s.denyList a }
  | Op.upgradeTo _newImpl =>
    if !s.whitelist caller then none
    else some s
  | Op.distributeYield amount =>
    if amount > s.vestedYield then none
    else
      let newVestedYield := s.vestedYield - amount
      let newTotalAssets := s.totalAssets + amount
      some {
        s with
        vestedYield := newVestedYield
        totalAssets := newTotalAssets
        lastYieldDistribution := now,
        yieldDistributionStart := now,
        yieldToDistribute := amount,
        yieldDistributed := 0
      }
  -- New operations for requirements
  | Op.lockApxUSD amount receiver =>
    -- Lock apxUSD to receive apyUSD
    if s.apxBal caller < amount then none
    else
      let mintShares := amount * EXCHANGE_RATE_SCALE / s.exchangeRate
      let newTotalAssets := s.totalAssets + amount
      let newTotalShares := s.totalShares + mintShares
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        apxBal := fun a => if a = caller then s.apxBal a - amount else s.apxBal a
        bal := fun a => if a = receiver then s.bal a + mintShares else s.bal a
      }
  | Op.setApxUSDPrice price =>
    -- Only governance/authorized entities can set price
    if !s.whitelist caller then none
    else some { s with apxUSDPrice := price }
  | Op.voteDeployBuffer addr =>
    -- Governance token holders vote to deploy buffer
    if !s.whitelist addr then none
    else some { s with bufferDeploymentVotes := fun a => if a = addr then true else s.bufferDeploymentVotes a }
  | Op.deployBuffer =>
    -- Deploy buffer if enough votes
    -- Simplified: assume enough votes if called by whitelist member
    if !s.whitelist caller then none
    else some { s with bufferDeployed := true }
  | Op.addAssetsToRedemption tokenId additionalAssets =>
    -- Add assets to existing redemption and reset cooldown
    if s.unlockReceiptOwner tokenId ≠ caller then none
    else
      let newAmount := s.unlockReceiptAmount tokenId + additionalAssets
      some {
        s with
        unlockReceiptAmount := fun id => if id = tokenId then newAmount else s.unlockReceiptAmount id,
        cooldownEnd := fun a => if a = caller then now + COOLDOWN_DURATION else s.cooldownEnd a
      }
  | Op.withdrawForMaxShares assets maxShares receiver =>
    -- Withdraw with slippage protection
    let sharesNeeded := assets * EXCHANGE_RATE_SCALE / s.exchangeRate
    if sharesNeeded > maxShares ∨ assets > s.totalAssets ∨ s.bal caller < sharesNeeded then none
    else
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
      }
  | Op.redeemForMinAssets shares minAssets receiver =>
    -- Redeem with slippage protection
    if shares > s.totalShares then none
    else
      let assetsOut := shares * s.exchangeRate / EXCHANGE_RATE_SCALE
      if assetsOut < minAssets then none
      else
        let newTotalAssets := s.totalAssets - assetsOut
        let newTotalShares := s.totalShares - shares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = caller then s.bal a - shares else s.bal a
        }
  | Op.setYieldVestingPeriod period =>
    -- Set yield vesting period (governance only)
    if !s.whitelist caller then none
    else some { s with yieldDistributionStart := s.yieldDistributionStart, yieldToDistribute := s.yieldToDistribute }

-- Requirements as theorems

-- BROKEN: /-- REQ whitelist-mint-access: The protocol MUST only allow whitelisted users to deposit USDC for minting apxUSD. -/
-- BROKEN: theorem req_whitelist_mint_access (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:     s.whitelist caller = false → step s (.deposit assets receiver) caller 0 = none := sorry

/-- REQ issuance-price-one: The protocol MUST price new issuance of apxUSD at $1 per unit. -/
theorem req_issuance_price_one (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
    s.paused = false → 
    s.denyList caller = false → 
    s.denyList receiver = false →
    step s (.deposit assets receiver) caller 0 = some (let mintShares := assets * EXCHANGE_RATE_SCALE / s.exchangeRate;
      { s with
        totalAssets := s.totalAssets + assets,
        totalShares := s.totalShares + mintShares,
        bal := fun a => if a = receiver then s.bal a + mintShares else s.bal a }) := by
  intro hp hd1 hd2
  simp [step, hp, hd1, hd2]

/-- REQ redemption-at-redemption-value: The protocol MUST redeem apyUSD at the Redemption Value that tracks the underlying basket. -/
theorem req_redemption_at_redemption_value (s : State) (shares : Amount) (receiver : Address) (caller : Address) :
    shares ≤ s.totalShares → 
    s.exchangeRate ≥ EXCHANGE_RATE_SCALE →
    step s (.redeem shares receiver) caller 0 = some (let assetsOut := shares * s.exchangeRate / EXCHANGE_RATE_SCALE;
      let receiptId := s.unlockReceiptId;
      { s with
        totalAssets := s.totalAssets - assetsOut,
        totalShares := s.totalShares - shares,
        bal := fun a => if a = caller then s.bal a - shares else s.bal a,
        unlockReceiptId := receiptId + 1,
        unlockReceiptOwner := fun id => if id = receiptId then caller else s.unlockReceiptOwner id,
        unlockReceiptAmount := fun id => if id = receiptId then assetsOut else s.unlockReceiptAmount id,
        cooldownEnd := fun a => if a = caller then 0 + COOLDOWN_DURATION else s.cooldownEnd a }) := by
  intro h1 h2
  simp [step, h1, h2]

-- BROKEN: /-- REQ vault-yield-distribution-20d: The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period. -/

-- BROKEN: /-- REQ lock-apxusd-for-apyusd: The system SHALL allow users to lock apxUSD in the vault to receive apyUSD. -/

-- BROKEN: /-- REQ apyusd-value-increases-with-yield: The redemption value of apyUSD SHALL increase over time as yield is distributed. -/

-- BROKEN: /-- REQ rebalance-overcollateralization: The protocol MUST rebalance the collateral basket to ensure that apxUSD remains overcollateralized. -/

-- BROKEN: /-- REQ redemption-liquidate-usdc: When a redemption is processed, the protocol MUST liquidate preferred shares into USDC and MUST NOT transfer preferred shares directly to the redeemer. -/

-- BROKEN: /-- REQ redemption_value_tracks_basket: The RV field should correspond to the value of underlying assets, here modeled through totalAssets and exchangeRate. -/
-- BROKEN: theorem req_redemption_value_tracks_basket (s : State) :
-- BROKEN:   s.RV = s.totalAssets * s.exchangeRate / EXCHANGE_RATE_SCALE := sorry

-- BROKEN: /-- REQ hard_floor_redemption_value: apxUSD price must not fall below Redemption Value; modeled via exchangeRate >= EXCHANGE_RATE_SCALE. -/
-- BROKEN: theorem req_hard_floor_redemption_value (s : State) :
-- BROKEN:   s.exchangeRate ≥ EXCHANGE_RATE_SCALE := sorry

/-- REQ deposit_permissionless: Any non-denied address can deposit and receive shares. -/
theorem req_deposit_permissionless (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
  s.denyList caller = false ∧ s.denyList receiver = false ∧ s.paused = false →
  step s (.deposit assets receiver) caller 0 ≠ none := by
  intro h
  unfold step
  split <;> simp_all

-- BROKEN: /-- REQ non_rebasing_balance: apyUSD balances only change on mint/burn operations, not spontaneously. -/
-- BROKEN: theorem req_non_rebasing_balance (s : State) (op : Op) (caller : Address) (now : Timestamp) (s' : State) :
-- BROKEN:   step s op caller now = some s' →
-- BROKEN:   ∀ a, a ≠ caller ∨ op = .deposit .. ∨ op = .mint .. ∨ op = .withdraw .. ∨ op = .redeem .. →
-- BROKEN:   s'.bal a = s.bal a := sorry

-- BROKEN: /-- REQ exchange_rate_monotonic: Exchange rate must be ≥ 1 (scaled). -/
-- BROKEN: theorem req_exchange_rate_monotonic (s : State) :
-- BROKEN:   s.exchangeRate ≥ EXCHANGE_RATE_SCALE := sorry

-- BROKEN: /-- REQ redemption_calculation: Redeeming shares yields assets according to exchangeRate. -/
-- BROKEN: theorem req_redemption_calculation (s : State) (shares : Amount) (receiver : Address) (caller : Address) (now : Timestamp) (s' : State) :
-- BROKEN:   step s (.redeem shares receiver) caller now = some s' →
-- BROKEN:   let assetsOut := shares * s.exchangeRate / EXCHANGE_RATE_SCALE
-- BROKEN:   s'.totalAssets = s.totalAssets - assetsOut ∧
-- BROKEN:   s'.bal caller = s.bal caller - shares ∧
-- BROKEN:   s'.totalShares = s.totalShares - shares := sorry

-- BROKEN: /-- REQ single-pending-request: Each user MUST have at most one pending redemption request at any time. -/
-- BROKEN: theorem req_single_pending_request (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     let s' := step s op caller now
-- BROKEN:     match s' with
-- BROKEN:     | some s'' => (s''.cooldownEnd caller = 0 ∨ s''.cooldownEnd caller = now + COOLDOWN_DURATION)
-- BROKEN:     | none => True := sorry

-- BROKEN: /-- REQ add-assets-resets-cooldown: If a user adds assets to an existing pending redemption request, the system MUST reset the cooldown period starting from the time of the update. -/

-- BROKEN: /-- REQ cooldown-duration: The system MUST enforce a cooldown period of approximately 20 days between a redemption request and the earliest possible claim. -/
-- BROKEN: theorem req_cooldown_duration (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     let s' := step s op caller now
-- BROKEN:     match s' with
-- BROKEN:     | some s'' => s''.cooldownEnd caller = now + COOLDOWN_DURATION
-- BROKEN:     | none => True := sorry

-- BROKEN: /-- REQ no-yield-during-cooldown: During the cooldown period, the system MUST not accrue yield on the user's apyUSD and MUST keep the exchangeRate fixed for that request. -/

-- BROKEN: ```lean
-- BROKEN: /-- REQ unlock-receipt-nft-mint: When a user initiates a new redemption/unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim. -/
-- BROKEN: theorem req_unlock_receipt_nft_mint (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     let s' := step s op caller now
-- BROKEN:     match s' with
-- BROKEN:     | some s'' => 
-- BROKEN:       match op with
-- BROKEN:       | Op.withdraw _ _ => s''.unlockReceiptId = s.unlockReceiptId + 1
-- BROKEN:       | Op.redeem _ _ => s''.unlockReceiptId = s.unlockReceiptId + 1
-- BROKEN:       | Op.requestUnlock _ => s''.unlockReceiptId = s.unlockReceiptId + 1
-- BROKEN:       | _ => True
-- BROKEN:     | none => True := sorry

-- BROKEN: /-- REQ flexible-claim-available-after-3d: The system MUST allow a flexible redemption/unlock claim to be submitted no earlier than 3 days after the request. -/

-- BROKEN: /-- REQ early-redemption-fee-schedule: The system MUST calculate an early redemption fee that starts at 3.5 % at request time and declines linearly to 0.1 % by the end of the 3‑day claim window. -/
-- BROKEN: theorem req_early_redemption_fee_schedule (s : State) (tokenId : ReceiptId) (caller : Address) (now : Timestamp) :
-- BROKEN:     let claimTime := s.cooldownEnd caller - COOLDOWN_DURATION + MIN_COOLDOWN_CLAIM
-- BROKEN:     let fee := calculateEarlyUnlockFee s caller claimTime
-- BROKEN:     now = claimTime → 
-- BROKEN:     let expectedFeeScaled := EARLY_UNLOCK_MAX_FEE * 100000000000000000
-- BROKEN:     fee = expectedFeeScaled := sorry

-- BROKEN: /-- REQ multiple-unlock-requests-allowed: The system MAY allow a user to have multiple concurrent Unlock Receipt NFTs for separate redemption requests. -/

-- BROKEN: /-- REQ overcollateralization-margin: The system MUST ensure that the total amount of apxUSD minted does not exceed the market value of the collateral minus the required overcollateralization margin. -/
-- BROKEN: theorem req_overcollateralization_margin (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     step s op caller now = none ∨
-- BROKEN:     (match op with
-- BROKEN:     | Op.mint shares _ =>
-- BROKEN:       let requiredAssets := shares * s.exchangeRate / EXCHANGE_RATE_SCALE
-- BROKEN:       requiredAssets ≤ s.TCV - s.liquidityBuffer
-- BROKEN:     | _ => True) := by
-- BROKEN:   intro h
-- BROKEN:   cases op <;> simp_all [step, sharePrice, hasPendingUnlock, isWhitelisted, isApprovedCounterparty, canClaimUnlock]
-- BROKEN:   · split_ifs with h1 h2 h3 <;> try { simp }
-- BROKEN:     · have h_totalAssets_nonneg : s.totalAssets ≥ 0 := by sorry
-- BROKEN:       have h_shares_nonneg : shares ≥ 0 := by sorry
-- BROKEN:       have h_exchangeRate_pos : s.exchangeRate > 0 := by sorry
-- BROKEN:       have h_req_assets : requiredAssets = shares * s.exchangeRate / EXCHANGE_RATE_SCALE := by rfl
-- BROKEN:       have h_bound : requiredAssets ≤ s.TCV - s.liquidityBuffer := sorry

-- BROKEN: /-- REQ buffer-not-consumed: The overcollateralization buffer MUST NOT be consumed during routine redemption operations. -/
-- BROKEN: theorem req_buffer_not_consumed (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     match op with
-- BROKEN:     | Op.redeem _ _ =>
-- BROKEN:       let s' := step s op caller now
-- BROKEN:       s' = none ∨ (∃ s'', s' = some s'' ∧ s''.liquidityBuffer = s.liquidityBuffer)
-- BROKEN:     | _ => True := sorry

-- BROKEN: /-- REQ mint-redeem-at-redemption-value: The system MUST price all mint and redemption transactions at the Redemption Value, which tracks the underlying basket of preferred shares and cash. -/
-- BROKEN: theorem req_mint_redeem_at_redemption_value (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     match op with
-- BROKEN:     | Op.mint shares _ =>
-- BROKEN:       let s' := step s op caller now
-- BROKEN:       s' = none ∨ (s'.get).totalAssets - s.totalAssets = shares * s.exchangeRate / EXCHANGE_RATE_SCALE
-- BROKEN:     | Op.redeem shares _ =>
-- BROKEN:       let s' := step s op caller now
-- BROKEN:       s' = none ∨ s.totalAssets - (s'.get).totalAssets = shares * s.exchangeRate / EXCHANGE_RATE_SCALE
-- BROKEN:     | _ => True := sorry

-- BROKEN: /-- REQ yield_eligible_cooldown: Yield MUST be paid only to apyUSD tokens that are not currently undergoing cooldown. -/
-- BROKEN: theorem req_yield_eligible_cooldown (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:   step s (.distributeYield amount) caller now = none ∨
-- BROKEN:   s.cooldownEnd caller = 0 := sorry

-- BROKEN: /-- REQ cooldown_exclusion: When an apyUSD token enters the cooldown phase, it MUST be removed from the pool that receives yield. -/
-- BROKEN: theorem req_cooldown_exclusion (s : State) (assets : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
-- BROKEN:   let s' := step s (.withdraw assets receiver) caller now
-- BROKEN:   match s' with
-- BROKEN:   | some s'' => s''.totalAssets = s.totalAssets - assets
-- BROKEN:   | none => True := sorry

-- BROKEN: /-- REQ immediate_yield_on_lock: Newly locked apyUSD MUST begin receiving yield immediately. -/
-- BROKEN: theorem req_immediate_yield_on_lock (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:   let s' := step s (.requestUnlock amount) caller now
-- BROKEN:   match s' with
-- BROKEN:   | some s'' => s''.unlockReceiptAmount s''.unlockReceiptId = amount
-- BROKEN:   | none => True := sorry

/-- REQ publish-metrics: The system MUST publish Redemption Value and Total Collateral Value on the transparency dashboard. -/
theorem req_publish_metrics (s : State) : 
    let rv := s.RV
    let tcv := s.TCV
    (rv ≥ 0 ∧ tcv ≥ 0) := 
  ⟨by simp [Amount], by simp [Amount]⟩

-- BROKEN: /-- REQ redemption-value-price: The system MUST use Redemption Value as the price for all redemption transactions. -/

-- BROKEN: /-- REQ redemption-value-uniform: Redemption Value MUST apply identically to all participants under both calm and stressed conditions. -/

-- BROKEN: /-- REQ total-collateral-definition: Total Collateral Value MUST be calculated as the full value of the reserve, including the overcollateralization buffer. -/

-- BROKEN: /-- REQ buffer-visibility: The buffer (gap between Redemption Value and Total Collateral Value) MUST be visible to everyone at all times. -/

-- BROKEN: /-- REQ price-floor: Redemption Value MUST act as a hard floor for the market price of apxUSD. -/

-- BROKEN: /-- REQ governance-deploy-buffer: Governance token holders MUST be able to vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios. -/

-- BROKEN: /-- REQ catastrophic-redemption: In a catastrophic scenario the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, buffer included, pro‑rata to remaining holders. -/

/-- REQ rfq-redemption: The system MUST allow users to submit redemption requests via a structured RFQ process and MUST permit only approved counterparties to execute those requests. -/
theorem req_rfq_redemption (s : State) (caller : Address) (requestId amount price : Amount) (expiry : Timestamp) :
    (step s (.submitRFQ requestId amount price expiry) caller 0 = none ↔ ¬isApprovedCounterparty s caller) ∧
    (step s (.fulfilRFQ requestId) caller 0 = none ↔ ¬isApprovedCounterparty s caller) := by
  unfold step isApprovedCounterparty; split <;> simp_all

-- BROKEN: /-- REQ deposit-immediate: The vault MUST mint apyUSD shares to the receiver immediately upon successful execution of `deposit(assets, receiver)`. -/
-- BROKEN: theorem req_deposit_immediate (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:     let s' := step s (.deposit assets receiver) caller 0
-- BROKEN:     s' ≠ none → (s'.get).bal receiver = s.bal receiver + (assets * EXCHANGE_RATE_SCALE / s.exchangeRate) := sorry

-- BROKEN: /-- REQ mint-immediate: The vault MUST mint the requested apyUSD shares to the receiver immediately upon successful execution of `mint(shares, receiver)`. -/
-- BROKEN: theorem req_mint_immediate (s : State) (shares : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:     let s' := step s (.mint shares receiver) caller 0
-- BROKEN:     s' ≠ none → (s'.get).bal receiver = s.bal receiver + shares := sorry

-- BROKEN: /-- REQ totalassets-includes-vested: The `totalAssets()` function MUST return the sum of the vault's direct apxUSD balance and the vested amount from the LinearVestV0 contract. -/
-- BROKEN: theorem req_totalassets_includes_vested (s : State) :
-- BROKEN:     s.totalAssets = s.TCV - s.liquidityBuffer + s.vestedYield := sorry

-- BROKEN: /-- REQ withdrawal-pulls-vested: When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal. -/
-- BROKEN: theorem req_withdrawal_pulls_vested (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:     let s' := step s (.withdraw assets receiver) caller 0
-- BROKEN:     s' ≠ none → (s'.get).vestedYield = s.vestedYield := sorry

-- BROKEN: /-- REQ global-pause-blocks-deposit-mint: If the global pause is active, the vault MUST reject any `deposit` or `mint` transaction. -/
-- BROKEN: theorem req_global_pause_blocks_deposit_mint (s : State) (assets shares : Amount) (receiver : Address) (caller : Address) :
-- BROKEN:     s.paused = true →
-- BROKEN:     step s (.deposit assets receiver) caller 0 = none ∧
-- BROKEN:     step s (.mint shares receiver) caller 0 = none := sorry

-- BROKEN: /-- REQ denylist-blocks-deposit-mint: The vault MUST revert any `deposit` or `mint` transaction if either the caller or the receiver address is present in the deny list. -/
-- BROKEN: theorem req_denylist_blocks_deposit_mint (s : State) (caller receiver : Address) (assets shares : Amount) :
-- BROKEN:     (s.denyList caller ∨ s.denyList receiver) → 
-- BROKEN:     step s (.deposit assets receiver) caller 0 = none ∧ 
-- BROKEN:     step s (.mint shares receiver) caller 0 = none := sorry

-- BROKEN: /-- REQ withdrawal-returns-unlock-token: Upon a successful withdrawal, the vault MUST mint a non‑transferable `apxUSD_unlock` token that MAY be redeemed for apxUSD only after a cooldown period. -/
-- BROKEN: theorem req_withdrawal_returns_unlock_token (s : State) (caller receiver : Address) (assets : Amount) (now : Timestamp) :
-- BROKEN:     let result := step s (.withdraw assets receiver) caller now
-- BROKEN:     result ≠ none → 
-- BROKEN:     let s' := result.get!
-- BROKEN:     s'.unlockReceiptId > s.unlockReceiptId := by
-- BROKEN:   unfold step
-- BROKEN:   split <;> simp_all
-- BROKEN:   intro h₁ h₂ h₃ h₄
-- BROKEN:   split <;> simp_all
-- BROKEN:   -- Case where withdrawal succeeds
-- BROKEN:   intro h_assets h_shares h_unlock
-- BROKEN:   have : s'.unlockReceiptId = s.unlockReceiptId + 1 := sorry

-- BROKEN: /-- REQ sync-withdraw-redeem: The apyUSD vault MUST execute withdraw and redeem operations synchronously and return apxUSD_unlock tokens. -/
-- BROKEN: theorem req_sync_withdraw_redeem (s : State) (caller receiver : Address) (assets shares : Amount) (now : Timestamp) :
-- BROKEN:     (step s (.withdraw assets receiver) caller now ≠ none ∨ 
-- BROKEN:      step s (.redeem shares receiver) caller now ≠ none) →
-- BROKEN:     let result := step s (.withdraw assets receiver) caller now
-- BROKEN:     let result2 := step s (.redeem shares receiver) caller now
-- BROKEN:     (result ≠ none → result.get!.unlockReceiptId > s.unlockReceiptId) ∧
-- BROKEN:     (result2 ≠ none → result2.get!.unlockReceiptId > s.unlockReceiptId) := sorry

-- BROKEN: /-- REQ unlock-redeem-1to1: The apxUSD_unlock token MUST be redeemable on a 1:1 basis for apxUSD after a 20‑day cooldown period. -/
-- BROKEN: theorem req_unlock_redeem_1to1 (s : State) (caller : Address) (tokenId : ReceiptId) (now : Timestamp) :
-- BROKEN:     canClaimUnlock s caller tokenId now →
-- BROKEN:     let amount := s.unlockReceiptAmount tokenId
-- BROKEN:     let fee := if now < s.cooldownEnd caller - (COOLDOWN_DURATION - MIN_COOLDOWN_CLAIM) 
-- BROKEN:                then calculateEarlyUnlockFee s caller now 
-- BROKEN:                else 0
-- BROKEN:     let amountAfterFee := amount - (amount * fee / 1000)
-- BROKEN:     let result := step s (.claimUnlock tokenId) caller now
-- BROKEN:     result ≠ none → 
-- BROKEN:     result.get!.apxBal caller = s.apxBal caller + amountAfterFee := sorry

-- BROKEN: /-- REQ unlock-nontransferable: The apxUSD_unlock token MUST NOT be transferable. -/

/-- REQ early-unlock-fee-linear: If a user claims an unlock before the end of the cooldown period, the system MUST apply an early unlock fee that declines linearly over time from 3.5 % down to 0.1 %. -/
theorem req_early_unlock_fee_linear (s : State) (caller : Address) (tokenId : ReceiptId) (now : Timestamp) :
    canClaimUnlock s caller tokenId now →
    now < s.cooldownEnd caller - (COOLDOWN_DURATION - MIN_COOLDOWN_CLAIM) →
    let fee := calculateEarlyUnlockFee s caller now
    let elapsed := now - (s.cooldownEnd caller - COOLDOWN_DURATION)
    let maxFeeScaled := EARLY_UNLOCK_MAX_FEE * 100000000000000000
    let minFeeScaled := EARLY_UNLOCK_MIN_FEE * 100000000000000000
    let feeDecline := (elapsed * (maxFeeScaled - minFeeScaled)) / COOLDOWN_DURATION
    fee = maxFeeScaled - feeDecline := by
  intro h1 h2
  unfold calculateEarlyUnlockFee
  simp_all

-- BROKEN: /-- REQ unlock-cannot-cancel: The system MUST NOT allow a user to cancel an unlock once it has been initiated. -/

-- BROKEN: /--
-- BROKEN: NOTE: The model does not include `withdrawForMaxShares` or `redeemForMinAssets` functions.
-- BROKEN: These requirements cannot be formalized without extending the operational model.
-- BROKEN: -/

-- BROKEN: /-- REQ unlock-convert-after-cooldown: The system MUST only allow conversion of apxUSD_unlock to apxUSD after the cooldown period has elapsed. -/
-- BROKEN: theorem req_unlock_convert_after_cooldown :
-- BROKEN:     ∀ s op caller now s',
-- BROKEN:       step s op caller now = some s' →
-- BROKEN:       (∀ tokenId, op = Op.claimUnlock tokenId → 
-- BROKEN:         s.unlockReceiptOwner tokenId = caller →
-- BROKEN:         now ≥ s.cooldownEnd caller) := sorry

-- BROKEN: /-- REQ multiple-unlocks-reset-cooldown: When a user initiates a new unlock while a previous unlock is pending, the system MUST reset the cooldown period for the entire pending amount. -/
-- BROKEN: theorem req_multiple_unlocks_reset_cooldown :
-- BROKEN:     ∀ s amount caller now s',
-- BROKEN:       step s (Op.requestUnlock amount) caller now = some s' →
-- BROKEN:       s.cooldownEnd caller > 0 →
-- BROKEN:       s'.cooldownEnd caller = now + COOLDOWN_DURATION := sorry

-- BROKEN: /--
-- BROKEN: REQ vault-yield-distribution-20d: The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period.
-- BROKEN: -/
-- BROKEN: theorem req_vault_yield_distribution_20d (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:     let s' := step s (.distributeYield amount) caller now
-- BROKEN:     s' = none ∨ (s'.get!.yieldDistributionStart = now ∧ s'.get!.yieldToDistribute = amount) := sorry

/--
REQ lock-apxusd-for-apyusd: The system SHALL allow users to lock apxUSD in the vault to receive apyUSD.
-/
theorem req_lock_apxusd_for_apyusd (s : State) (amount : Amount) (receiver : Address) (caller : Address) :
    s.apxBal caller ≥ amount →
    let s' := step s (.lockApxUSD amount receiver) caller 0
    s' ≠ none :=
  by intro h; unfold step; split <;> simp_all

-- BROKEN: /--
-- BROKEN: REQ apyusd-value-increases-with-yield: The redemption value of apyUSD SHALL increase over time as yield is distributed.
-- BROKEN: -/
-- BROKEN: theorem req_apyusd_value_increases_with_yield (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:     amount ≤ s.vestedYield →
-- BROKEN:     let s' := step s (.distributeYield amount) caller now
-- BROKEN:     s' ≠ none → s'.get!.totalAssets = s.totalAssets + amount := sorry

-- BROKEN: /--
-- BROKEN: REQ rebalance-overcollateralization: The protocol MUST rebalance the collateral basket to ensure that apxUSD remains overcollateralized.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_rebalance_overcollateralization: Model does not specify collateral basket or rebalancing mechanism.

-- BROKEN: /--
-- BROKEN: REQ redemption-liquidate-usdc: When a redemption is processed, the protocol MUST liquidate preferred shares into USDC and MUST NOT transfer preferred shares directly to the redeemer.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_redemption_liquidate_usdc: Model does not specify preferred shares or liquidation mechanism.

-- BROKEN: /--
-- BROKEN: REQ redemption-settlement-usdc: All redemption settlements MUST be made in USDC.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_redemption_settlement_usdc: Model does not specify settlement currency mechanism.

-- BROKEN: /--
-- BROKEN: REQ liquidity-buffer-size: The protocol MUST maintain a liquidity buffer sized against the largest historical TVL drawdowns observed in comparable stablecoins.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_liquidity_buffer_size: Model does not specify how buffer size is determined or compared to historical data.

/--
REQ add-assets-resets-cooldown: If a user adds assets to an existing pending redemption request, the system MUST reset the cooldown period starting from the time of the update.
-/
theorem req_add_assets_resets_cooldown (s : State) (tokenId : ReceiptId) (additionalAssets : Amount) 
    (caller : Address) (now : Timestamp) :
    s.unlockReceiptOwner tokenId = caller →
    let s' := step s (.addAssetsToRedemption tokenId additionalAssets) caller now
    s' ≠ none → s'.get!.cooldownEnd caller = now + COOLDOWN_DURATION :=
  by intro h₁; unfold step; split <;> simp_all

-- BROKEN: /-- REQ no-yield-during-cooldown: During the cooldown period, the system MUST not accrue yield on the user's apyUSD and MUST keep the exchangeRate fixed for that request. -/
-- BROKEN: theorem req_no_yield_during_cooldown (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     hasPendingUnlock s caller → 
-- BROKEN:     match step s op caller now with
-- BROKEN:     | some s' => s'.exchangeRate = s.exchangeRate
-- BROKEN:     | none => True
-- BROKEN:     end := sorry

-- BROKEN: /-- REQ flexible-claim-available-after-3d: The system MUST allow a flexible redemption/unlock claim to be submitted no earlier than 3 days after the request. -/
-- BROKEN: theorem req_flexible_claim_available_after_3d (s : State) (tokenId : ReceiptId) (caller : Address) (now : Timestamp) :
-- BROKEN:     canClaimUnlock s caller tokenId now → 
-- BROKEN:     now ≥ s.cooldownEnd caller - (COOLDOWN_DURATION - MIN_COOLDOWN_CLAIM) := sorry

-- BROKEN: /-- REQ multiple-unlock-requests-allowed: The system MAY allow a user to have multiple concurrent Unlock Receipt NFTs for separate redemption requests. -/
-- BROKEN: -- UNFORMALIZABLE req_multiple-unlock-requests-allowed: The model does not track multiple concurrent unlock requests per user; it only tracks one cooldownEnd per address.

-- BROKEN: /-- REQ buffer-preserved-stress: The system MUST preserve the buffer (the difference between Redemption Value and Total Collateral Value) during stress events. -/
-- BROKEN: theorem req_buffer_preserved_stress (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     match step s op caller now with
-- BROKEN:     | some s' => getBuffer s' = getBuffer s
-- BROKEN:     | none => True
-- BROKEN:     end :=
-- BROKEN: sorry -- This would require defining what constitutes a "stress event" and proving preservation under those conditions

-- BROKEN: /-- REQ whitelist-mint-premium: Only participants on the eligible whitelist MAY mint apxUSD via the arbitrage pathway when apxUSD trades above $1. -/
-- BROKEN: theorem req_whitelist_mint_premium (s : State) (amount : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
-- BROKEN:     step s (Op.lockApxUSD amount receiver) caller now = none ∨ 
-- BROKEN:     (isWhitelisted s caller ∧ canMintApxUSD s caller) := sorry

-- BROKEN: /-- REQ whitelist-redeem-discount: Only participants on the eligible whitelist MAY redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1. -/
-- BROKEN: theorem req_whitelist_redeem_discount (s : State) (addr : Address) :
-- BROKEN:     canRedeemApxUSD s addr → s.whitelist addr := sorry

-- BROKEN: /-- REQ credit-yield: The system MUST credit converted apxUSD proceeds to the apyUSD vault via the YieldDistributor. -/
-- BROKEN: theorem req_credit_yield (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:     step s (Op.distributeYield amount) caller now = none ∨ 
-- BROKEN:     (∃ s', step s (Op.distributeYield amount) caller now = some s' ∧ 
-- BROKEN:      s'.totalAssets = s.totalAssets + amount ∧ 
-- BROKEN:      s'.vestedYield = s.vestedYield - amount) := sorry

-- BROKEN: /-- REQ linear-vesting-implementation: Yield distribution MUST use a linear vesting mechanism implemented by the LinearVestV0 contract. -/
-- BROKEN: -- UNFORMALIZABLE req_linear-vesting-implementation: The model does not specify the implementation details of the vesting mechanism beyond tracking vesting periods and amounts.

-- BROKEN: /-- REQ continuous_streaming: Yield MUST be streamed continuously over a configurable period rather than as a single lump‑sum distribution. -/
-- BROKEN: theorem req_continuous_streaming (s : State) (op : Op) (caller : Address) (now : Timestamp) :
-- BROKEN:     let s' := step s op caller now
-- BROKEN:     if s'.isSome ∧ ∃ amount, op = Op.distributeYield amount ∧ amount > 0 then
-- BROKEN:       let s_new := s'.get
-- BROKEN:       s_new.lastYieldDistribution = now ∧ 
-- BROKEN:       s_new.yieldToDistribute = amount ∧
-- BROKEN:       s_new.yieldDistributed = 0
-- BROKEN:     else True := sorry

-- BROKEN: /-- REQ monthly_rate_setting: Each month, the system MUST set the yield rate for the following month based on the yield generated by the collateral base in the prior month. -/
-- BROKEN: -- UNFORMALIZABLE req_monthly_rate_setting: The model does not include explicit monthly periods or mechanisms for setting future yield rates based on past performance.

-- BROKEN: /-- REQ rate_dollar_terms: The yield rate MUST be expressed in dollar terms. -/
-- BROKEN: theorem req_rate_dollar_terms (s : State) (now : Timestamp) :
-- BROKEN:     getCurrentYieldRate s now = 0 ∨ getCurrentYieldRate s now > 0 := sorry

-- BROKEN: /-- REQ configurable_period: The vesting period over which yield is streamed MUST be configurable by the protocol. -/
-- BROKEN: -- UNFORMALIZABLE req_configurable_period: While YIELD_VESTING_PERIOD is defined as a constant, there's no operation in the model that allows changing this value, making this requirement unformalizable.

-- BROKEN: /-- REQ constant_rate_vesting: The linear vesting mechanism MUST distribute yield at a constant rate over the vesting period. -/
-- BROKEN: theorem req_constant_rate_vesting (s : State) (now : Timestamp) :
-- BROKEN:     YIELD_VESTING_PERIOD ≠ 0 →
-- BROKEN:     let rate := getCurrentYieldRate s now
-- BROKEN:     rate = (s.yieldToDistribute * EXCHANGE_RATE_SCALE) / YIELD_VESTING_PERIOD := sorry

-- BROKEN: /-- REQ redemption_value_price: The system MUST use Redemption Value as the price for all redemption transactions. -/
-- BROKEN: -- UNFORMALIZABLE req_redemption_value_price: The model does not explicitly show how redemption transactions use Redemption Value (RV) as the price; this is more of an implementation detail not captured in the state transition function.

-- BROKEN: /-- REQ redemption_value_uniform: Redemption Value MUST apply identically to all participants under both calm and stressed conditions. -/
-- BROKEN: -- UNFORMALIZABLE req_redemption_value_uniform: The model does not capture different conditions (calm/stressed) or show that RV is applied uniformly; this is a semantic requirement not enforceable on the state machine.

-- BROKEN: /-- REQ total_collateral_definition: Total Collateral Value MUST be calculated as the full value of the reserve, including the overcollateralization buffer. -/
-- BROKEN: -- UNFORMALIZABLE req_total_collateral_definition: The model defines TCV as a field but doesn't specify its calculation or relationship to other components like the buffer; this definitional requirement cannot be formalized against the current model structure.

/-- REQ buffer-visibility: The buffer (gap between Redemption Value and Total Collateral Value) MUST be visible to everyone at all times. -/
theorem req_buffer_visibility (s : State) : getBuffer s = (if s.RV > s.TCV then 0 else s.TCV - s.RV) := rfl

-- BROKEN: /-- REQ price-floor: Redemption Value MUST act as a hard floor for the market price of apxUSD. -/
-- BROKEN: -- UNFORMALIZABLE req_price-floor: Market price semantics not captured in state model

/-- REQ governance-deploy-buffer: Governance token holders MUST be able to vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios. -/
theorem req_governance_deploy_buffer_vote (s : State) (addr : Address) : 
    s.whitelist addr → step s (.voteDeployBuffer addr) addr 0 = some { s with bufferDeploymentVotes := fun a => if a = addr then true else s.bufferDeploymentVotes a } := 
  by intro h; simp [step, h]

-- BROKEN: /-- REQ catastrophic-redemption: In a catastrophic scenario the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, buffer included, pro‑rata to remaining holders. -/
-- BROKEN: -- UNFORMALIZABLE req_catastrophic-redemption: Catastrophic scenario and pro-rata distribution not modeled

/-- REQ unlock-nontransferable: The apxUSD_unlock token MUST NOT be transferable. -/
theorem req_unlock_nontransferable (s : State) : isUnlockTransferable s = s.unlockTokenTransferable := rfl

-- BROKEN: /-- REQ unlock-cannot-cancel: The system MUST NOT allow a user to cancel an unlock once it has been initiated. -/
-- BROKEN: -- UNFORMALIZABLE req_unlock-cannot-cancel: Cancellation not modeled in state machine

-- BROKEN: /-- REQ withdrawformaxshares-revert-on-slippage: The withdrawForMaxShares function MUST revert if the number of shares required to withdraw the specified assets exceeds maxShares. -/
-- BROKEN: theorem req_withdrawformaxshares_revert_on_slippage (s : State) (assets maxShares : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
-- BROKEN:     let sharesNeeded := assets * EXCHANGE_RATE_SCALE / s.exchangeRate
-- BROKEN:     sharesNeeded > maxShares → step s (.withdrawForMaxShares assets maxShares receiver) caller now = none := 
-- BROKEN:   by
-- BROKEN:     intro h
-- BROKEN:     simp [step]
-- BROKEN:     split <;> simp_all
-- BROKEN:     -- Case where the operation is valid (first condition is true)
-- BROKEN:     intro h1 h2 h3
-- BROKEN:     -- We need to show this leads to a contradiction or that the result is none
-- BROKEN:     have : assets * EXCHANGE_RATE_SCALE / s.exchangeRate > maxShares := h
-- BROKEN:     have : ¬(assets * EXCHANGE_RATE_SCALE / s.exchangeRate ≤ maxShares) := sorry

-- BROKEN: /-- REQ redeemforminassets-revert-on-slippage: The redeemForMinAssets function MUST revert if the amount of assets received for the specified shares is less than minAssets. -/
-- BROKEN: theorem req_redeemforminassets_revert_on_slippage (s : State) (shares minAssets : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
-- BROKEN:     let assetsOut := shares * s.exchangeRate / EXCHANGE_RATE_SCALE
-- BROKEN:     shares > s.totalShares ∨ assetsOut < minAssets → step s (.redeemForMinAssets shares minAssets receiver) caller now = none := sorry

-- BROKEN: /--
-- BROKEN: REQ single-unlocktoken-instance: There MUST be only one instance of the UnlockToken contract, and it MUST be used exclusively by the apyUSD vault.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_single_unlocktoken_instance: The model does not represent external contracts or instances explicitly.

-- BROKEN: /--
-- BROKEN: REQ vault-operator-unlocktoken: The apyUSD vault MUST be set as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_vault_operator_unlocktoken: The model does not represent external contract operators or cross-contract operations.

-- BROKEN: /--
-- BROKEN: REQ unlocktoken-redeem-after-cooldown: The UnlockToken.redeem function MUST only be callable after the cooldown period for the corresponding apxUSD_unlock tokens has elapsed.
-- BROKEN: -/
-- BROKEN: theorem req_unlocktoken_redeem_after_cooldown :
-- BROKEN:     ∀ s caller tokenId now,
-- BROKEN:       step s (.claimUnlock tokenId) caller now = none ∨
-- BROKEN:       (unlockReceiptOwner s tokenId = caller ∧ now ≥ cooldownEnd s caller ∧ cooldownEnd s caller > 0) := sorry

-- BROKEN: /--
-- BROKEN: REQ unlocktoken-no-yield: The apxUSD_unlock token MUST NOT earn any yield during the cooldown period.
-- BROKEN: -/
-- BROKEN: theorem req_unlocktoken_no_yield :
-- BROKEN:     ∀ s addr now,
-- BROKEN:       hasPendingUnlock s addr = true → isYieldAccrualPaused s addr = true := sorry

end Apyx
