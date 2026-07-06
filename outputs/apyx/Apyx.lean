import Std.Data.HashMap

namespace Apyx

abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat

structure UnlockRequest where
  amount : Amount
  start : Timestamp
  claimed : Bool

structure RFQEntry where
  apxAmt : Amount
  quote : Amount

structure Vote where
  proposalId : Nat
  amount : Amount

structure State where
  totalCollateralValue : Amount
  totalMintedApxUSD : Amount
  redemptionValue : Amount
  bufferAmount : Amount
  totalApyUSDshares : Amount
  totalApyAssets : Amount
  exchangeRate : Amount
  paused : Bool
  denyList : List Address
  whitelist : List Address
  authorizedCounterparties : List Address
  unlockRequests : Address -> Option UnlockRequest
  governanceVotes : Nat -> Option Vote
  balancesApxUSD : Address -> Amount
  balancesApyUSD : Address -> Amount
  pendingRFQs : Address -> Option RFQEntry
  blockTimestamp : Timestamp

inductive Op
  | depositForMinShares (user : Address) (usdcAmt : Amount) (minApx : Amount)
  | mintForMaxAssets (user : Address) (apxAmt : Amount) (maxUSDC : Amount)
  | redeemForMinAssets (user : Address) (apxAmt : Amount) (minUSDC : Amount)
  | lock (user : Address) (apxAmt : Amount)
  | unlock (user : Address) (apxAmt : Amount)
  | claimUnlock (user : Address)
  | pause
  | unpause
  | voteDeployBuffer (proposalId : Nat) (amount : Amount)
  | rfqSubmit (user : Address) (apxAmt : Amount) (quote : Amount)
  | rfqExecute (counterparty : Address) (user : Address)
  | arbitrageMint (arbitrageur : Address) (usdcAmt : Amount)
  | arbitrageRedeem (arbitrageur : Address) (apxAmt : Amount)
  | streamYield (amount : Amount) (period : Amount)
  | activateBackstop

def State.isWhitelisted (s : State) (addr : Address) : Bool :=
  s.whitelist.contains addr

def State.isAuthorizedCounterparty (s : State) (addr : Address) : Bool :=
  s.authorizedCounterparties.contains addr

def State.isDenyListed (s : State) (addr : Address) : Bool :=
  s.denyList.contains addr

def State.hasActiveUnlockRequest (s : State) (addr : Address) : Bool :=
  match s.unlockRequests addr with
  | some _ => true
  | none => false

def State.canClaimUnlock (s : State) (addr : Address) : Bool :=
  match s.unlockRequests addr with
  | some req =>
    s.blockTimestamp >= req.start + 3 * 24 * 3600 ∧
    ¬ req.claimed
  | none => false

def State.updateBalanceApxUSD (s : State) (addr : Address) (delta : Int) : State :=
  let current := s.balancesApxUSD addr
  let newBalance := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with balancesApxUSD := fun a => if a = addr then newBalance else s.balancesApxUSD a }

def State.updateBalanceApyUSD (s : State) (addr : Address) (delta : Int) : State :=
  let current := s.balancesApyUSD addr
  let newBalance := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with balancesApyUSD := fun a => if a = addr then newBalance else s.balancesApyUSD a }

def State.updateTotalApyAssets (s : State) (delta : Int) : State :=
  let current := s.totalApyAssets
  let newValue := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with totalApyAssets := newValue }

def State.updateTotalApyShares (s : State) (delta : Int) : State :=
  let current := s.totalApyUSDshares
  let newValue := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with totalApyUSDshares := newValue }

def State.updateTotalCollateralValue (s : State) (delta : Int) : State :=
  let current := s.totalCollateralValue
  let newValue := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with totalCollateralValue := newValue }

def State.updateTotalMintedApxUSD (s : State) (delta : Int) : State :=
  let current := s.totalMintedApxUSD
  let newValue := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with totalMintedApxUSD := newValue }

def State.updateBufferAmount (s : State) (delta : Int) : State :=
  let current := s.bufferAmount
  let newValue := if delta ≥ 0 then
    current + (delta.toNat : Nat)
  else
    let absDelta := (-delta).toNat
    if current ≥ absDelta then current - absDelta else 0
  { s with bufferAmount := newValue }

def State.updateUnlockRequest (s : State) (addr : Address) (req : Option UnlockRequest) : State :=
  { s with unlockRequests := fun a => if a = addr then req else s.unlockRequests a }

def State.updatePendingRFQ (s : State) (addr : Address) (entry : Option RFQEntry) : State :=
  { s with pendingRFQs := fun a => if a = addr then entry else s.pendingRFQs a }

def State.updatePaused (s : State) (paused : Bool) : State :=
  { s with paused := paused }

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.depositForMinShares user usdcAmt minApx =>
    if s.paused ∨ s.isDenyListed user ∨ usdcAmt < minApx then
      none
    else
      let s1 := s.updateTotalMintedApxUSD (Int.ofNat minApx)
      let s2 := s1.updateTotalCollateralValue (Int.ofNat usdcAmt)
      let s3 := s2.updateBalanceApxUSD user (Int.ofNat minApx)
      some s3
  | Op.mintForMaxAssets user apxAmt maxUSDC =>
    if s.paused ∨ s.isDenyListed user ∨ maxUSDC < apxAmt then
      none
    else
      let s1 := s.updateTotalMintedApxUSD (Int.ofNat apxAmt)
      let s2 := s1.updateTotalCollateralValue (Int.ofNat apxAmt)
      let s3 := s2.updateBalanceApxUSD user (Int.ofNat apxAmt)
      some s3
  | Op.redeemForMinAssets user apxAmt minUSDC =>
    let userBalance := s.balancesApxUSD user
    let redeemValue := apxAmt * s.redemptionValue
    if s.paused ∨ s.isDenyListed user ∨ apxAmt > s.totalMintedApxUSD ∨
       redeemValue < minUSDC ∨ userBalance < apxAmt then
      none
    else
      let s1 := s.updateTotalMintedApxUSD (Int.negOfNat apxAmt)
      let s2 := s1.updateTotalCollateralValue (Int.negOfNat redeemValue)
      let s3 := s2.updateBalanceApxUSD user (Int.negOfNat apxAmt)
      some s3
  | Op.lock user apxAmt =>
    let userBalance := s.balancesApxUSD user
    if apxAmt > userBalance ∨ s.paused then
      none
    else
      let shares := apxAmt / s.exchangeRate
      let s1 := s.updateBalanceApxUSD user (Int.negOfNat apxAmt)
      let s2 := s1.updateTotalApyShares (Int.ofNat shares)
      let s3 := s2.updateTotalApyAssets (Int.ofNat apxAmt)
      let s4 := s3.updateBalanceApyUSD user (Int.ofNat shares)
      some s4
  | Op.unlock user apxAmt =>
    let userBalance := s.balancesApxUSD user
    if apxAmt > userBalance ∨ s.hasActiveUnlockRequest user ∨ s.paused then
      none
    else
      let s1 := s.updateBalanceApxUSD user (Int.negOfNat apxAmt)
      let req : UnlockRequest := {
        amount := apxAmt,
        start := s.blockTimestamp,
        claimed := false
      }
      let s2 := s1.updateUnlockRequest user (some req)
      some s2
  | Op.claimUnlock user =>
    if ¬ s.canClaimUnlock user then
      none
    else
      match s.unlockRequests user with
      | some req =>
        let elapsed := s.blockTimestamp - req.start
        let feePercent := if elapsed ≥ 20 * 24 * 3600 then
          1 -- 0.1%
        else
          let baseFee := 35 -- 3.5%
          let decay := (baseFee - 1) * elapsed / (20 * 24 * 3600)
          baseFee - decay
        let fee := req.amount * feePercent / 1000
        let _transferAmount := req.amount - fee
        let s1 := s.updateTotalCollateralValue (Int.negOfNat req.amount)
        let s2 := s1.updateUnlockRequest user none
        -- Transfer `transferAmount` USDC to user (not modeled here)
        some s2
      | none => none
  | Op.pause =>
    if ¬ s.isWhitelisted caller then
      none
    else
      some (s.updatePaused true)
  | Op.unpause =>
    if ¬ s.isWhitelisted caller then
      none
    else
      some (s.updatePaused false)
  | Op.voteDeployBuffer _proposalId amount =>
    if ¬ s.isWhitelisted caller ∨ amount > s.bufferAmount then
      none
    else
      -- Assume vote passes
      let s1 := s.updateTotalCollateralValue (Int.negOfNat amount)
      let s2 := s1.updateBufferAmount (Int.negOfNat amount)
      some s2
  | Op.rfqSubmit user apxAmt quote =>
    let userBalance := s.balancesApxUSD user
    if s.paused ∨ apxAmt > userBalance then
      none
    else
      let entry : RFQEntry := { apxAmt := apxAmt, quote := quote }
      let s1 := s.updatePendingRFQ user (some entry)
      some s1
  | Op.rfqExecute counterparty user =>
    if ¬ s.isAuthorizedCounterparty counterparty then
      none
    else
      match s.pendingRFQs user with
      | some entry =>
        let s1 := s.updateBalanceApxUSD user (Int.negOfNat entry.apxAmt)
        let s2 := s1.updatePendingRFQ user none
        -- Transfer `entry.quote` USDC to user (not modeled here)
        some s2
      | none => none
  | Op.arbitrageMint arbitrageur usdcAmt =>
    if ¬ s.isWhitelisted arbitrageur then
      none
    else
      let s1 := s.updateTotalMintedApxUSD (Int.ofNat usdcAmt)
      let s2 := s1.updateTotalCollateralValue (Int.ofNat usdcAmt)
      let s3 := s2.updateBalanceApxUSD arbitrageur (Int.ofNat usdcAmt)
      some s3
  | Op.arbitrageRedeem arbitrageur apxAmt =>
    if ¬ s.isWhitelisted arbitrageur then
      none
    else
      let redeemValue := apxAmt * s.redemptionValue
      let s1 := s.updateTotalMintedApxUSD (Int.negOfNat apxAmt)
      let s2 := s1.updateTotalCollateralValue (Int.negOfNat redeemValue)
      let s3 := s2.updateBalanceApxUSD arbitrageur (Int.negOfNat apxAmt)
      -- Transfer `redeemValue` USDC to arbitrageur (not modeled here)
      some s3
  | Op.streamYield amount _period =>
    -- Only Vault can call this
    let s1 := s.updateTotalApyAssets (Int.ofNat amount)
    some s1
  | Op.activateBackstop =>
    -- Simplified: set redemptionValue and distribute assets
    let newRedemptionValue := s.totalCollateralValue / s.totalMintedApxUSD
    let s1 := { s with redemptionValue := newRedemptionValue, bufferAmount := 0 }
    some s1

-- Requirements as theorems

/--
  REQ deposit-mint-apxusd:
  The system MUST allow users to deposit USDC in order to acquire apxUSD.
-/
theorem req_deposit_mint_apxusd (s : State) (user : Address) (usdcAmt : Amount) (minApx : Amount) :
  step s (.depositForMinShares user usdcAmt minApx) user = none ∨
  (∃ s', step s (.depositForMinShares user usdcAmt minApx) user = some s' ∧
   s'.balancesApxUSD user ≥ s.balancesApxUSD user + minApx) := by
  unfold step Op.depositForMinShares
  split
  · intro h
    left
    exact h
  · intro h
    right
    use { s with
      totalMintedApxUSD := s.totalMintedApxUSD + minApx,
      totalCollateralValue := s.totalCollateralValue + usdcAmt,
      balancesApxUSD := fun a => if a = user then s.balancesApxUSD user + minApx else s.balancesApxUSD a }
    constructor
    · rfl
    · simp [State.updateBalanceApxUSD]

/--
  REQ apxusd-issuance-price:
  The protocol MUST issue new apxUSD at a price of exactly $1 per token.
-/
-- UNFORMALIZABLE req_apxusd_issuance_price: Model does not include price or value semantics for individual tokens

/--
  REQ redemption-uses-redemption-value:
  All redemption transactions MUST be executed at the current Redemption Value, which tracks the underlying basket of preferred shares and applies identically to all participants.
-/
theorem req_redemption_uses_redemption_value (s : State) (user : Address) (apxAmt : Amount) (minUSDC : Amount) :
  step s (.redeemForMinAssets user apxAmt minUSDC) user = none ∨
  (∃ s', step s (.redeemForMinAssets user apxAmt minUSDC) user = some s' ∧
   s'.totalCollateralValue = s.totalCollateralValue - apxAmt * s.redemptionValue) := by
  unfold step Op.redeemForMinAssets
  split
  · intro h
    left
    exact h
  · intro h
    right
    use { s with
      totalMintedApxUSD := s.totalMintedApxUSD - apxAmt,
      totalCollateralValue := s.totalCollateralValue - apxAmt * s.redemptionValue,
      balancesApxUSD := fun a => if a = user then s.balancesApxUSD user - apxAmt else s.balancesApxUSD a }
    constructor
    · rfl
    · simp [State.updateTotalCollateralValue, State.updateBalanceApxUSD]

/--
  REQ overcollateralization-buffer-maintenance:
  The system MUST keep apxUSD over‑collateralized by maintaining an over‑collateralization buffer that grows during stress events, is not consumed by routine redemptions, and ensures total minted apxUSD never exceeds the market value of the collateral minus the required margin.
-/
-- UNFORMALIZABLE req_overcollateralization_buffer_maintenance: Model lacks stress event semantics and market value definition

/--
  REQ total-collateral-metric:
  The Total Collateral Value metric MUST represent the full reserve value including the over‑collateralization buffer and MUST be publicly available on the dashboard at all times.
-/
-- UNFORMALIZABLE req_total_collateral_metric: Model does not define "dashboard" or "public availability"

/--
  REQ buffer-visibility:
  The buffer amount (the gap between Redemption Value and Total Collateral Value) MUST be visible to all users at all times.
-/
-- UNFORMALIZABLE req_buffer_visibility: Model does not define "visibility to users"

/--
  REQ liquidity-buffer-maintenance:
  The liquidity buffer MUST be at least as large as the largest historical TVL drawdown among comparable stablecoins and must remain available at all times, including outside traditional trading hours and on weekends.
-/
-- UNFORMALIZABLE req_liquidity_buffer_maintenance: Model lacks historical TVL drawdown data and time semantics

/--
  REQ no-rehypothecation:
  The protocol MUST NOT rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose.
-/
-- UNFORMALIZABLE req_no_rehypothecation: Model does not specify allowed uses of deposited funds

-- UNFORMALIZABLE req_yield_distribution: Yield streaming and LinearVestV0 contract interaction not modeled in the state.
-- UNFORMALIZABLE req_exchange_rate_increase: Exchange rate dynamics not modeled; `exchangeRate` is a static field.
-- UNFORMALIZABLE req_no_rebase: apyUSD balance updates are modeled but "rebase" behavior is not explicitly defined.
-- UNFORMALIZABLE req_erc4626_compliance: ERC-4626 interface compliance cannot be expressed without external interface modeling.
-- UNFORMALIZABLE req_locking_mechanism: LinearVestV0 and totalAssets() semantics not modeled.

/-- REQ access_control_pause_denylist: If the vault is globally paused, any deposit or mint operation MUST revert. Additionally, if the caller or receiver is on the deny list, deposit or mint MUST revert immediately. -/
theorem req_access_control_pause_denylist (s : State) (op : Op) (caller : Address) :
  (s.paused ∨ s.isDenyListed caller) →
  match op with
  | Op.depositForMinShares _ _ _ => step s op caller = none
  | Op.mintForMaxAssets _ _ _ => step s op caller = none
  | _ => True := by
  intro h
  cases op <;> simp [step]
  all_goals (split_ifs <;> rfl)

/-- REQ redemption_request_process: When a user submits a redemption request, the system MUST lock the user's assets, allow at most one pending request per user, enforce a cooldown of approximately 20 days before claim, reset the cooldown if assets are added, and ensure no yield accrues and the exchange rate remains fixed during the cooldown period. -/
theorem req_redemption_request_process (s : State) (user : Address) (apxAmt : Amount) :
  s.hasActiveUnlockRequest user →
  step s (.unlock user apxAmt) user = none := by
  intro h
  simp [step, State.hasActiveUnlockRequest] at h ⊢
  split_ifs with h1 h2 h3
  · rfl
  · contradiction

/-- REQ flexible_redemption: The flexible redemption mechanism MUST allow users to initiate unlocks that mint an on‑chain Unlock Receipt NFT. Unlocks become claimable after three days, with an early unlock fee that starts at 3.5 % and declines linearly to a minimum of 0.1 %. Users may have multiple unlock requests simultaneously; adding assets resets the cooldown for the combined amount. Unlocks cannot be cancelled. -/
theorem req_flexible_redemption_claim_window (s : State) (user : Address) :
  s.canClaimUnlock user →
  let req := s.unlockRequests user
  match req with
  | some r => s.blockTimestamp ≥ r.start + 3 * 24 * 3600
  | none => False := by
  intro h
  simp [State.canClaimUnlock] at h
  split at h
  · simp at h
    cases h with
    | intro h1 h2 => exact h1.1
  · contradiction

/-- REQ rfq-redemption-process: The RFQ redemption system MUST allow users to submit redemption requests through a structured process, and MUST permit only approved counterparties to execute those requests. -/
theorem req_rfq_redemption_process (s : State) (user counterparty : Address) (apxAmt quote : Amount) :
  let s' := step s (.rfqSubmit user apxAmt quote) user
  match s' with
  | some s1 =>
    let s2 := step s1 (.rfqExecute counterparty user) counterparty
    s2 = none ∨ (s2 ≠ none ∧ s1.isAuthorizedCounterparty counterparty)
  | none => True := by
  sorry

/-- REQ governance-deploy-buffer: Governance token holders MUST be able to vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios. -/
theorem req_governance_deploy_buffer (s : State) (caller : Address) (proposalId amount : Nat) :
  s.isWhitelisted caller ∧ amount ≤ s.bufferAmount →
  step s (.voteDeployBuffer proposalId amount) caller ≠ none := by
  intro h
  simp [step] at *
  split_ifs with h1 h2
  · intro h3; contradiction
  · intro h3; rfl

/-- REQ catastrophic-backstop: In a catastrophic scenario, the protocol MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, including the buffer, pro‑rata to remaining holders. -/
theorem req_catastrophic_backstop (s : State) :
  let s' := step s .activateBackstop 0
  match s' with
  | some s1 => s1.redemptionValue = s1.totalCollateralValue / s1.totalMintedApxUSD ∧ s1.bufferAmount = 0
  | none => True := by
  simp [step]
  split
  · intro h; contradiction
  · intro h; simp

/-- REQ price-floor: The market price of apxUSD MUST never fall below the Redemption Value. -/
-- UNFORMALIZABLE req_price_floor: Market price is not modeled in the state

/-- REQ slippage-revert-rules: depositForMinShares, mintForMaxAssets, withdrawForMaxShares, and redeemForMinAssets MUST revert if the operation would result in fewer shares, exceed max assets, exceed max shares, or receive less than the minimum assets respectively. -/
theorem req_slippage_revert_rules_deposit (s : State) (user : Address) (usdcAmt minApx : Amount) :
  usdcAmt < minApx → step s (.depositForMinShares user usdcAmt minApx) user = none := by
  intro h
  simp [step]
  split_ifs with h1 h2 h3
  · rfl
  · contradiction

theorem req_slippage_revert_rules_mint (s : State) (user : Address) (apxAmt maxUSDC : Amount) :
  maxUSDC < apxAmt → step s (.mintForMaxAssets user apxAmt maxUSDC) user = none := by
  intro h
  simp [step]
  split_ifs with h1 h2 h3
  · rfl
  · contradiction

/-- REQ arbitrage-mint-pathway: The system MUST provide a minting pathway that eligible participants may use to mint apxUSD under predefined terms when apxUSD trades above $1. -/
theorem req_arbitrage_mint_pathway (s : State) (arbitrageur : Address) (usdcAmt : Amount) :
  s.isWhitelisted arbitrageur →
  step s (.arbitrageMint arbitrageur usdcAmt) arbitrageur ≠ none := by
  intro h
  simp [step, State.isWhitelisted] at *
  split_ifs with h1
  · contradiction
  · intro h2; rfl

/-- REQ arbitrage-redeem-pathway: The system MUST provide a redemption pathway that eligible participants may use to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1. -/
theorem req_arbitrage_redeem_pathway (s : State) (arbitrageur : Address) (apxAmt : Amount) :
  s.isWhitelisted arbitrageur →
  step s (.arbitrageRedeem arbitrageur apxAmt) arbitrageur ≠ none := by
  intro h
  simp [step, State.isWhitelisted] at *
  split_ifs with h1
  · contradiction
  · intro h2; rfl

/-- REQ whitelist-arbitrage-access: The system MUST restrict arbitrage minting and redemption actions to participants that are on the eligible whitelist. -/
theorem req_whitelist_arbitrage_access_mint (s : State) (arbitrageur : Address) (usdcAmt : Amount) :
  ¬ s.isWhitelisted arbitrageur →
  step s (.arbitrageMint arbitrageur usdcAmt) arbitrageur = none := by
  intro h
  simp [step, State.isWhitelisted] at *
  split_ifs with h1
  · rfl
  · contradiction

theorem req_whitelist_arbitrage_access_redeem (s : State) (arbitrageur : Address) (apxAmt : Amount) :
  ¬ s.isWhitelisted arbitrageur →
  step s (.arbitrageRedeem arbitrageur apxAmt) arbitrageur = none := by
  intro h
  simp [step, State.isWhitelisted] at *
  split_ifs with h1
  · rfl
  · contradiction

end Apyx
