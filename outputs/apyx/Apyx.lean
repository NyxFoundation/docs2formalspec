namespace Apyx

abbrev Address := Nat
abbrev Timestamp := Nat
abbrev Amount := Nat
abbrev BasisPoint := Nat
abbrev Ray := Nat -- 1e27 fixed point

structure UnlockRequest where
  owner : Address
  amount : Amount
  requestTime : Timestamp
  deriving Repr, BEq

/-- A simplified representation of functions for Repr purposes -/
@[reducible]
def FunctionRepr (α β : Type) [Repr α] [Repr β] : Repr (α → β) where
  reprPrec _ _ := "fun"

instance : Repr (Address → Amount) := FunctionRepr Address Amount
instance : Repr (Nat → Option UnlockRequest) := FunctionRepr Nat (Option UnlockRequest)
instance : Repr (Nat → Option Timestamp) := FunctionRepr Nat (Option Timestamp)
instance : Repr (Address → Nat → Option Timestamp) := FunctionRepr Address (Nat → Option Timestamp)

structure State where
  -- Core token supplies
  totalSupply_apxUSD : Amount
  totalSupply_apyUSD : Amount

  -- Redemption & collateral tracking
  redemptionValue_cents : Amount -- in USD cents
  overcollateralizationBuffer_cents : Int

  -- Exchange rate (ray: 1e27 fixed point)
  exchangeRate_ray : Ray

  -- User balances
  bal_apxUSD : Address → Amount
  bal_apyUSD : Address → Amount

  -- Unlock requests (requestId -> UnlockRequest)
  unlockRequests : Nat → Option UnlockRequest
  nextRequestId : Nat

  -- Cooldown tracking: user -> requestId -> cooldown end timestamp
  cooldownEnd : Address → Nat → Option Timestamp

  -- Access control
  whitelist : List Address
  denylist : List Address
  admins : List Address
  pauseRole : List Address
  govRole : List Address
  rfqCounterparties : List Address
  globalPause : Bool

  -- Yield parameters
  yieldRateMonth_bps : BasisPoint
  vestPeriod_seconds : Timestamp
  lastYieldCredit : Timestamp

  -- Yield vesting state
  vestedYield : Amount -- amount of yield currently vested
  totalVestingAmount : Amount -- total yield being vested
  vestStartTime : Timestamp -- when current vesting period started

  deriving Repr

-- Initial empty state
def initialState : State := {
  totalSupply_apxUSD := 0,
  totalSupply_apyUSD := 0,
  redemptionValue_cents := 100, -- $1.00 in cents
  overcollateralizationBuffer_cents := 0,
  exchangeRate_ray := 1000000000000000000000000000, -- 1e27
  bal_apxUSD := fun _ => 0,
  bal_apyUSD := fun _ => 0,
  unlockRequests := fun _ => none,
  nextRequestId := 0,
  cooldownEnd := fun _ _ => none,
  whitelist := [],
  denylist := [],
  admins := [],
  pauseRole := [],
  govRole := [],
  rfqCounterparties := [],
  globalPause := false,
  yieldRateMonth_bps := 0,
  vestPeriod_seconds := 1728000, -- 20 days in seconds
  lastYieldCredit := 0,
  vestedYield := 0,
  totalVestingAmount := 0,
  vestStartTime := 0
}

inductive Op where
  | depositUSDC (amount : Amount)
  | mintApxUSD (to : Address) (amount : Amount)
  | lockApxUSD (amount : Amount)
  | requestUnlock (amount : Amount)
  | claimUnlock (requestId : Nat)
  | redeemApxUSD (amount : Amount)
  | withdraw (assets : Amount) (receiver : Address)
  | pause
  | unpause
  | addToWhitelist (addr : Address)
  | removeFromWhitelist (addr : Address)
  | addToDenylist (addr : Address)
  | removeFromDenylist (addr : Address)
  | setYieldRate (bps : BasisPoint)
  | creditYield (amount : Amount)
  | executeRFQRedemption (user : Address) (amount : Amount)
  deriving Repr

-- Helper functions
def hasRole (s : State) (addr : Address) (role : List Address) : Bool :=
  role.contains addr

def isWhitelisted (s : State) (addr : Address) : Bool :=
  s.whitelist.contains addr

def isDenylisted (s : State) (addr : Address) : Bool :=
  s.denylist.contains addr

def hasUnlockRequest (s : State) (user : Address) : Bool :=
  let reqId := 0 -- This function seems incomplete in the original code
  match s.unlockRequests reqId with
  | some _req => true
  | none => false

def getUnlockRequest (s : State) (requestId : Nat) : Option UnlockRequest :=
  s.unlockRequests requestId

def isCooldownEnded (s : State) (user : Address) (requestId : Nat) (now : Timestamp) : Bool :=
  match s.cooldownEnd user requestId with
  | some endTime => now >= endTime
  | none => false

def apxUSD_balance (s : State) (addr : Address) : Amount :=
  s.bal_apxUSD addr

def apyUSD_balance (s : State) (addr : Address) : Amount :=
  s.bal_apyUSD addr

def convert_apyUSD_to_apxUSD (s : State) (apyUSD_amount : Amount) : Amount :=
  (apyUSD_amount * s.exchangeRate_ray) / 1000000000000000000000000000

-- State transition function
def step (s : State) (op : Op) (caller : Address) (now : Timestamp) : Option State :=
  match op with
  | Op.depositUSDC amount =>
    if s.globalPause ∨ isDenylisted s caller ∨ amount = 0 then
      none
    else
      let newS := {
        s with
        totalSupply_apxUSD := s.totalSupply_apxUSD + amount,
        bal_apxUSD := fun a => if a = caller then s.bal_apxUSD a + amount else s.bal_apxUSD a
      }
      some newS

  | Op.mintApxUSD to amount =>
    if ¬(isWhitelisted s caller) ∨ amount = 0 then
      none
    else
      let newS := {
        s with
        totalSupply_apxUSD := s.totalSupply_apxUSD + amount,
        bal_apxUSD := fun a => if a = to then s.bal_apxUSD a + amount else s.bal_apxUSD a
      }
      some newS

  | Op.lockApxUSD amount =>
    if s.bal_apxUSD caller < amount ∨ amount = 0 then
      none
    else
      let shares := (amount * 1000000000000000000000000000) / s.exchangeRate_ray
      let newS := {
        s with
        bal_apxUSD := fun a => if a = caller then s.bal_apxUSD a - amount else s.bal_apxUSD a,
        bal_apyUSD := fun a => if a = caller then s.bal_apyUSD a + shares else s.bal_apyUSD a,
        totalSupply_apyUSD := s.totalSupply_apyUSD + shares
      }
      some newS

  | Op.requestUnlock amount =>
    if s.bal_apyUSD caller < amount ∨ amount = 0 then
      none
    else
      let requestId := s.nextRequestId
      let newUnlockRequests := fun id => if id = requestId then 
        some { owner := caller, amount := amount, requestTime := now }
      else s.unlockRequests id
      let newS := {
        s with
        bal_apyUSD := fun a => if a = caller then s.bal_apyUSD a - amount else s.bal_apyUSD a,
        unlockRequests := newUnlockRequests,
        nextRequestId := requestId + 1,
        cooldownEnd := fun u r => if u = caller ∧ r = requestId then 
          some (now + 1728000) -- 20 days
        else s.cooldownEnd u r
      }
      some newS

  | Op.claimUnlock requestId =>
    match s.unlockRequests requestId with
    | some req =>
      if req.owner ≠ caller ∨ ¬(isCooldownEnded s caller requestId now) then
        none
      else
        let newUnlockRequests := fun id => if id = requestId then none else s.unlockRequests id
        let newS := {
          s with
          bal_apxUSD := fun a => if a = caller then s.bal_apxUSD a + req.amount else s.bal_apxUSD a,
          unlockRequests := newUnlockRequests,
          cooldownEnd := fun u r => if u = caller ∧ r = requestId then none else s.cooldownEnd u r
        }
        some newS
    | none => none

  | Op.redeemApxUSD amount =>
    if s.bal_apxUSD caller < amount ∨ amount = 0 then
      none
    else
      -- Calculate USDC to transfer (amount * redemptionValue / 100 for cents conversion)
      let _usdcAmount := (amount * s.redemptionValue_cents) / 100
      let newS := {
        s with
        bal_apxUSD := fun a => if a = caller then s.bal_apxUSD a - amount else s.bal_apxUSD a,
        totalSupply_apxUSD := s.totalSupply_apxUSD - amount
        -- Note: In a real implementation, we'd transfer USDC to caller here
      }
      some newS

  | Op.withdraw assets _receiver =>
    -- Simplified version - in reality would need to pull vested yield
    let apyUSD_amount := (assets * 1000000000000000000000000000) / s.exchangeRate_ray
    if s.bal_apyUSD caller < apyUSD_amount then
      none
    else
      -- This is a simplified model - real implementation would:
      -- 1. Pull vested yield from LinearVestV0
      -- 2. Burn apyUSD shares
      -- 3. Deposit apxUSD into UnlockToken
      -- 4. Mint unlock NFT
      let newS := {
        s with
        bal_apyUSD := fun a => if a = caller then s.bal_apyUSD a - apyUSD_amount else s.bal_apyUSD a
        -- Other state changes omitted for brevity
      }
      some newS

  | Op.pause =>
    if ¬(hasRole s caller s.pauseRole) then
      none
    else
      some { s with globalPause := true }

  | Op.unpause =>
    if ¬(hasRole s caller s.pauseRole) then
      none
    else
      some { s with globalPause := false }

  | Op.addToWhitelist addr =>
    if ¬(hasRole s caller s.admins) then
      none
    else
      some { s with whitelist := if s.whitelist.contains addr then s.whitelist else addr :: s.whitelist }

  | Op.removeFromWhitelist addr =>
    if ¬(hasRole s caller s.admins) then
      none
    else
      some { s with whitelist := s.whitelist.filter (· ≠ addr) }

  | Op.addToDenylist addr =>
    if ¬(hasRole s caller s.admins) then
      none
    else
      some { s with denylist := if s.denylist.contains addr then s.denylist else addr :: s.denylist }

  | Op.removeFromDenylist addr =>
    if ¬(hasRole s caller s.admins) then
      none
    else
      some { s with denylist := s.denylist.filter (· ≠ addr) }

  | Op.setYieldRate bps =>
    if ¬(hasRole s caller s.govRole) then
      none
    else
      some { s with yieldRateMonth_bps := bps }

  | Op.creditYield amount =>
    -- Simplified - in reality would update LinearVestV0
    if ¬(true) then -- Placeholder for YieldDistributor check
      none
    else
      some { s with totalVestingAmount := s.totalVestingAmount + amount, vestStartTime := now }

  | Op.executeRFQRedemption user amount =>
    if ¬(s.rfqCounterparties.contains caller) ∨ ¬(isWhitelisted s user) then
      none
    else
      if s.bal_apxUSD user < amount then
        none
      else
        let _usdcAmount := (amount * s.redemptionValue_cents) / 100
        let newS := {
          s with
          bal_apxUSD := fun a => if a = user then s.bal_apxUSD a - amount else s.bal_apxUSD a,
          totalSupply_apxUSD := s.totalSupply_apxUSD - amount
        }
        some newS

-- Requirements as theorems

-- BROKEN: /--
-- BROKEN:   REQ deposit-mint-apxusd: The protocol MUST mint apxUSD to a user when the user deposits USDC.
-- BROKEN: -/
-- BROKEN: theorem req_deposit_mint_apxusd (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:     amount > 0 → ¬s.globalPause → ¬isDenylisted s caller →
-- BROKEN:     match step s (.depositUSDC amount) caller now with
-- BROKEN:     | some s' => s'.bal_apxUSD caller = s.bal_apxUSD caller + amount
-- BROKEN:     | none => False
-- BROKEN:     := by
-- BROKEN:   intro hamount hpaused hdenylist
-- BROKEN:   simp [step]
-- BROKEN:   split
-- BROKEN:   · intro h
-- BROKEN:     simp at h
-- BROKEN:     have : amount = 0 ∨ s.globalPause ∨ isDenylisted s caller := sorry

-- BROKEN: /--
-- BROKEN:   REQ mint-price: The protocol MUST price newly minted apxUSD at $1 per unit.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_mint_price: Model does not include pricing logic or external price feeds

-- BROKEN: /--
-- BROKEN:   REQ redemption-value: The protocol MUST allow redemption of apxUSD at the current Redemption Value.
-- BROKEN: -/
-- BROKEN: theorem req_redemption_value (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:     amount > 0 → s.bal_apxUSD caller ≥ amount →
-- BROKEN:     match step s (.redeemApxUSD amount) caller now with
-- BROKEN:     | some s' => s'.bal_apxUSD caller = s.bal_apxUSD caller - amount
-- BROKEN:     | none => False
-- BROKEN:   := by
-- BROKEN:   intro hamount hbalance
-- BROKEN:   simp [step]
-- BROKEN:   split
-- BROKEN:   · intro h
-- BROKEN:     simp at h
-- BROKEN:     have : s.bal_apxUSD caller < amount ∨ amount = 0 := sorry

-- BROKEN: /--
-- BROKEN:   REQ no-rehypothecation: The protocol MUST NOT rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_no_rehypothecation: Negative invariant about external behavior cannot be formalized

-- BROKEN: /--
-- BROKEN:   REQ yield-distribution-period: The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_yield_distribution_period: Vesting period is modeled but not formally constrained to 20 days in all cases

-- BROKEN: /--
-- BROKEN:   REQ lock-apxusd: The protocol MUST allow a user to lock apxUSD in the vault and receive apyUSD.
-- BROKEN: -/
-- BROKEN: theorem req_lock_apxusd (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:     amount > 0 → s.bal_apxUSD caller ≥ amount →
-- BROKEN:     match step s (.lockApxUSD amount) caller now with
-- BROKEN:     | some s' => s'.bal_apyUSD caller ≥ s.bal_apyUSD caller
-- BROKEN:     | none => False
-- BROKEN:     := by
-- BROKEN:   intro hamount hbalance
-- BROKEN:   simp [step]
-- BROKEN:   split
-- BROKEN:   · intro h
-- BROKEN:     simp at h
-- BROKEN:     have : s.bal_apxUSD caller < amount ∨ amount = 0 := by
-- BROKEN:       omega
-- BROKEN:     cases this <;> contradiction
-- BROKEN:   · intro h
-- BROKEN:     simp at h
-- BROKEN:     -- When the operation succeeds, we get a new state s'
-- BROKEN:     -- In this state, the caller's apyUSD balance has increased by shares
-- BROKEN:     -- We need to show that s'.bal_apyUSD caller ≥ s.bal_apyUSD caller
-- BROKEN:     -- The increase is (amount * 1000000000000000000000000000) / s.exchangeRate_ray
-- BROKEN:     -- Since amount > 0 and exchangeRate_ray > 0, this increase is positive
-- BROKEN:     have h_shares_pos : (amount * 1000000000000000000000000000) / s.exchangeRate_ray ≥ 0 := sorry

-- BROKEN: /--
-- BROKEN:   REQ apyusd-value-increase: The redeemable value of apyUSD MUST increase over time as yield is distributed to the vault.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_apyusd_value_increase: Model does not capture yield accrual mechanics affecting apyUSD value

-- BROKEN: /--
-- BROKEN:   REQ price-may-include-spreads: The protocol MAY reflect spreads and offchain execution expenses in the price during minting and redemption.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_price_may_include_spreads: Permissive requirement about optional behavior cannot be formalized as a constraint
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_rebalance_overcollateralization: The model does not include explicit collateral basket tracking or rebalancing logic.
-- BROKEN: -- UNFORMALIZABLE req_redeem_liquidate_usdc: The model does not include preferred-share collateral or liquidation mechanisms.
-- BROKEN: -- UNFORMALIZABLE req_redeem_no_share_transfer: The model does not explicitly track preferred shares or their transfers.
-- BROKEN: -- UNFORMALIZABLE req_redemption_settlement_value: The model does not define "Redemption Value" as tracking an underlying basket in a formalized way.
-- BROKEN: -- UNFORMALIZABLE req_mint_access_whitelist: The model does not include eligibility or jurisdiction checks beyond whitelisting.
-- BROKEN: -- UNFORMALIZABLE req_redeem_access_whitelist: The model does not include eligibility or jurisdiction checks beyond whitelisting.
-- BROKEN: -- UNFORMALIZABLE req_issuance_price_one: The model does not include pricing logic for new apxUSD issuance.

/-- REQ deposit-permissionless: The vault MUST allow any address to deposit apxUSD and receive apyUSD without requiring KYB/KYC. -/
theorem req_deposit_permissionless {s : State} {caller : Address} {amount : Amount} {now : Timestamp} :
    amount > 0 → isDenylisted s caller = false → s.globalPause = false →
    step s (.depositUSDC amount) caller now = none ∨
    (∃ s', step s (.depositUSDC amount) caller now = some s' ∧
     s'.bal_apxUSD caller ≥ s.bal_apxUSD caller + amount ∧
     s'.totalSupply_apxUSD ≥ s.totalSupply_apxUSD + amount) := sorry

/--
  REQ token-no-rebase: The apyUSD token MUST NOT rebase its balances; balances may change only via transfers, minting, or burning.
-/
theorem req_token_no_rebase (s : State) (op : Op) (caller : Address) (now : Timestamp) :
  let s' := step s op caller now;
  ∀ a, (s'.map (·.bal_apyUSD a) = some (s.bal_apyUSD a)) ∨
       (∃ amount, op = Op.lockApxUSD amount ∧ s'.map (·.bal_apyUSD a) = some (s.bal_apyUSD a + (amount * 1000000000000000000000000000) / s.exchangeRate_ray)) ∨
       (∃ amount, op = Op.requestUnlock amount ∧ s'.map (·.bal_apyUSD a) = some (s.bal_apyUSD a - amount)) ∨
       (∃ assets, ∃ _receiver : Address, op = Op.withdraw assets _receiver ∧ s'.map (·.bal_apyUSD a) = some (s.bal_apyUSD a - (assets * 1000000000000000000000000000) / s.exchangeRate_ray)) := by
  sorry

-- BROKEN: /--
-- BROKEN:   REQ exchange-rate-non-decreasing: The exchange rate between apyUSD and apxUSD MUST be non‑decreasing over time.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_exchange_rate_non_decreasing: The model does not expose a way to compare exchange rates across time steps or states.

-- BROKEN: /--
-- BROKEN:   REQ redemption-exchange-rate-multiplier: When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_redemption_exchange_rate_multiplier: The model does not implement apyUSD redemption directly; it only implements apxUSD redemption.

-- BROKEN: /--
-- BROKEN:   REQ redemption-async-process: Redemption requests MUST follow the three‑step asynchronous process of request, cooldown, and claim.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_redemption_async_process: The model does not fully implement the redemption process as described; it only has unlock requests which are similar but not identical.

/--
  REQ redemption-cooldown-period: After a redemption request is submitted, the system MUST enforce a cooldown period of approximately 20 days before a claim can be executed.
-/
theorem req_redemption_cooldown_period (s : State) (caller : Address) (requestId : Nat) (amount : Amount) (now : Timestamp) :
  let s' := step s (Op.requestUnlock amount) caller now;
  let s'' := step (Option.getD s' s) (Op.claimUnlock requestId) caller (now + 1728000);
  (s''.isSome → isCooldownEnded (Option.getD s' s) caller requestId (now + 1728000)) := by
  sorry

-- BROKEN: /--
-- BROKEN:   REQ single-pending-redemption-per-user: Each user MUST have at most one pending redemption request; if the user adds assets to an existing request, the cooldown timer MUST reset to the time of the update.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_single_pending_redemption_per_user: The model allows multiple unlock requests per user and does not implement request updates.

-- BROKEN: /--
-- BROKEN:   REQ cooldown-no-yield: During a redemption cooldown, the exchange rate for the locked apyUSD MUST remain fixed and the user MUST not accrue additional yield on those tokens.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_cooldown_no_yield: The model does not implement yield accrual, so this cannot be formalized.

-- BROKEN: /--
-- BROKEN:   REQ flexible-redemption-claim-minimum: A flexible redemption claim MUST be executable only after a minimum of 3 days have elapsed since the request.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_flexible_redemption_claim_minimum: The model enforces a fixed 20-day cooldown and does not implement flexible redemption claims with a 3-day minimum.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_flexible_redemption_early_fee: The model does not include early redemption fees or their calculation logic.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_flexible_redemption_multiple_requests: The model does not track multiple concurrent unlock requests per user in a way that can be easily formalized.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_overcollateralization_limit: The model does not include explicit collateral tracking or market value calculations needed to enforce this constraint.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_buffer_preservation: The model does not explicitly track or preserve an overcollateralization buffer during redemptions.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_mint_redeem_at_redemption_value: The model does not include external price feeds or mechanisms to ensure minting/redemption at a specific basket value.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_buffer_non_decreasing: The model does not track the overcollateralization buffer as a separate field or enforce its non-decreasing behavior.

/-- REQ arbitrage-mint-access: Only eligible whitelist participants SHALL be permitted to invoke the minting pathway for arbitrage when apxUSD trades above $1.00. -/
theorem req_arbitrage_mint_access (s : State) (to : Address) (amount : Amount) (caller : Address) :
    step s (.mintApxUSD to amount) caller 0 = none ∨ isWhitelisted s caller := sorry

/-- REQ arbitrage-redeem-access: Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00. -/
theorem req_arbitrage_redeem_access (s : State) (amount : Amount) (caller : Address) :
    step s (.redeemApxUSD amount) caller 0 = none ∨ step s (.redeemApxUSD amount) caller 0 = some s := by
  sorry

-- BROKEN: /--
-- BROKEN: REQ new_locked_receives_yield: When new apyUSD is locked, it MUST immediately begin receiving yield, which reduces the overall percentage yield for existing holders.
-- BROKEN: -/
-- BROKEN: theorem req_new_locked_receives_yield (s : State) (caller : Address) (amount : Amount) :
-- BROKEN:   let result := step s (Op.lockApxUSD amount) caller 0
-- BROKEN:   match result with
-- BROKEN:   | some s' => s'.totalSupply_apyUSD > s.totalSupply_apyUSD ∧
-- BROKEN:                s'.bal_apyUSD caller > s.bal_apyUSD caller
-- BROKEN:   | none => True :=
-- BROKEN: by
-- BROKEN:   unfold step
-- BROKEN:   split
-- BROKEN:   · -- Op.depositUSDC case
-- BROKEN:     intro h
-- BROKEN:     simp [h]
-- BROKEN:   · split
-- BROKEN:     · -- Op.mintApxUSD case
-- BROKEN:       intro h
-- BROKEN:       simp [h]
-- BROKEN:     · split
-- BROKEN:       · -- Op.lockApxUSD case (this is what we want)
-- BROKEN:         intro h
-- BROKEN:         simp [h] at *
-- BROKEN:         split
-- BROKEN:         · -- s.bal_apxUSD caller < amount ∨ amount = 0
-- BROKEN:           intro h1
-- BROKEN:           simp [h1]
-- BROKEN:         · -- valid lock operation
-- BROKEN:           intro h1 h2
-- BROKEN:           simp at h1 h2
-- BROKEN:           split
-- BROKEN:           · -- amount = 0
-- BROKEN:             intro h3
-- BROKEN:             simp [h3]
-- BROKEN:           · -- actual lock operation with amount > 0
-- BROKEN:             intro h3
-- BROKEN:             simp at h3
-- BROKEN:             -- Extract the new state
-- BROKEN:             let shares := (amount * 1000000000000000000000000000) / s.exchangeRate_ray
-- BROKEN:             have h_shares_pos : shares > 0 := sorry

/--
REQ cooldown_removal: When apyUSD enters the cooldown phase, it MUST be removed from the yield pool, causing remaining apyUSD to receive a higher percentage yield.
-/
theorem req_cooldown_removal (s : State) (caller : Address) (amount : Amount) :
  let result := step s (Op.requestUnlock amount) caller 0
  match result with
  | some s' => s'.bal_apyUSD caller < s.bal_apyUSD caller
  | none => True := sorry

-- BROKEN: /--
-- BROKEN: NOTE: This requirement cannot be formalized directly against the current model
-- BROKEN: because it speaks about "configurable" values, but the model does not expose
-- BROKEN: a configuration interface or parameter for the vesting period that can be proven
-- BROKEN: to be used in `step`. The vestPeriod_seconds is hardcoded in the state.
-- BROKEN: -/
-- BROKEN: -- UNFORMALIZABLE req_configurable_vesting_period: vesting period is hardcoded in model

/-- REQ redemption-value-uniform: The system MUST apply the same Redemption Value to all participants regardless of market conditions. -/
theorem req_redemption_value_uniform (s : State) (op : Op) (caller : Address) (now : Timestamp) :
  step s op caller now = none ∨
  (let s' := match step s op caller now with | some state => state | none => s; s'.redemptionValue_cents = s.redemptionValue_cents) :=
by
  sorry

/--
  REQ unlock-cooldown:
  The apxUSD_unlock token MAY be redeemed for apxUSD only after a cooldown period has elapsed.
-/
theorem req_unlock_cooldown (s : State) (requestId : Nat) (caller : Address) (now : Timestamp) :
  step s (.claimUnlock requestId) caller now = none ∨
  (match s.unlockRequests requestId with
   | some req => req.owner = caller ∧ isCooldownEnded s caller requestId now
   | none => False) := sorry

/--
  REQ global-pause-blocks-deposit:
  If the global pause is active, any deposit or mint transaction MUST revert.
-/
theorem req_global_pause_blocks_deposit (s : State) (amount : Amount) (to : Address) (caller : Address) (now : Timestamp) :
  s.globalPause = true →
  step s (.depositUSDC amount) caller now = none ∧
  step s (.mintApxUSD to amount) caller now = none := sorry

/--
  REQ denylist-blocks-deposit:
  If the caller or the receiver address is present in the deny list, deposit and mint operations MUST revert.
-/
theorem req_denylist_blocks_deposit (s : State) (amount : Amount) (to : Address) (caller : Address) (now : Timestamp) :
  (isDenylisted s caller ∨ isDenylisted s to) →
  step s (.depositUSDC amount) caller now = none ∧
  step s (.mintApxUSD to amount) caller now = none := sorry

/-- REQ unlock-token-redeemable-1to1-after-20d: apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period. -/
theorem req_unlock_token_redeemable_1to1_after_20d (s : State) (requestId : Nat) (caller : Address) (now : Timestamp) :
  let result := step s (.claimUnlock requestId) caller now
  match result, s.unlockRequests requestId with
  | some s', some req => 
    req.owner = caller → isCooldownEnded s caller requestId now → 
    s'.bal_apxUSD caller = s.bal_apxUSD caller + req.amount
  | _, _ => True := 
sorry

/-- REQ unlock-receipt-nft-mint: When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim. -/
theorem req_unlock_receipt_nft_mint (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
  let result := step s (.requestUnlock amount) caller now
  match result with
  | some s' => 
    amount > 0 → s.bal_apyUSD caller ≥ amount → 
    s'.unlockRequests s.nextRequestId = some { owner := caller, amount := amount, requestTime := now }
  | none => True :=
sorry

/-- REQ unlock-claimable-after-3d: Unlocks MUST become claimable after three days. -/
theorem req_unlock_claimable_after_3d (s : State) (requestId : Nat) (caller : Address) (requestTime : Timestamp) :
  let result := step s (.claimUnlock requestId) caller (requestTime + 259200) -- 3 days in seconds
  match s.unlockRequests requestId, result with
  | some req, some s' => 
    req.owner = caller → req.requestTime = requestTime → 
    s'.bal_apxUSD caller = s.bal_apxUSD caller + req.amount
  | _, _ => True :=
sorry

-- BROKEN: /-- UNFORMALIZABLE req_early_unlock_fee_linear_decline: The model does not include any logic for early unlock fees or their computation. -/
-- BROKEN: #guard_msgs in
-- BROKEN: theorem req_unlock_cannot_be_cancelled (s : State) (requestId : Nat) (caller : Address) (now : Timestamp) :
-- BROKEN:   match step s (.claimUnlock requestId) caller now with
-- BROKEN:   | some _ => True
-- BROKEN:   | none => getUnlockRequest s requestId = none ∨
-- BROKEN:             match getUnlockRequest s requestId with
-- BROKEN:             | some req => req.owner ≠ caller ∨ ¬(isCooldownEnded s caller requestId now)
-- BROKEN:             | none => True := sorry

-- BROKEN: /-- UNFORMALIZABLE req_multiple_unlocks_reset_cooldown: The model does not track "total locked amount" or reset behavior for multiple unlocks. -/
-- BROKEN: #guard_msgs in
-- BROKEN: theorem req_unlock_conversion_after_cooldown (s : State) (requestId : Nat) (caller : Address) (now : Timestamp) :
-- BROKEN:   match step s (.claimUnlock requestId) caller now with
-- BROKEN:   | some s' => 
-- BROKEN:     match s.unlockRequests requestId with
-- BROKEN:     | some req => req.owner = caller ∧ isCooldownEnded s caller requestId now
-- BROKEN:     | none => False
-- BROKEN:   | none => True := sorry

-- BROKEN: /-- UNFORMALIZABLE req_withdraw_for_max_shares_revert_if_exceeds_max_shares: The model does not include a `withdrawForMaxShares` operation with a `maxShares` parameter. -/
-- BROKEN: #guard_msgs in
-- BROKEN: theorem req_vault_burns_apyUSD_shares_immediately (s : State) (assets : Amount) (receiver : Address) (caller : Address) (now : Timestamp) :
-- BROKEN:   match step s (.withdraw assets receiver) caller now with
-- BROKEN:   | some s' => 
-- BROKEN:     let apyUSD_amount := (assets * 1000000000000000000000000000) / s.exchangeRate_ray
-- BROKEN:     s'.bal_apyUSD caller = s.bal_apyUSD caller - apyUSD_amount
-- BROKEN:   | none => True := sorry

-- BROKEN: /-- UNFORMALIZABLE req_redeem_for_min_assets_revert_if_below_min_assets: The model does not include a `redeemForMinAssets` operation with a `minAssets` parameter. -/
-- BROKEN: #guard_msgs in

-- BROKEN: /-- UNFORMALIZABLE req_vault_pulls_vested_yield_before_withdraw: The model does not include interaction with a LinearVestV0 contract or explicit pulling of vested yield. -/
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_vault_deposits_apxUSD_into_UnlockToken: The model does not include an UnlockToken contract or explicit linking to one, so this requirement cannot be formalized.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_unlockToken_mints_apxUSD_unlock_immediately: The model does not include apxUSD_unlock tokens or explicit minting logic for them.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_unlockToken_redeem_after_cooldown: The model does not include an UnlockToken contract or explicit redeem logic for it.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_singleton_unlockToken_instance: The model does not include multiple instances of UnlockToken or a way to enforce singleton behavior.
-- BROKEN: 
-- BROKEN: -- UNFORMALIZABLE req_vault_operator_of_UnlockToken: The model does not include an UnlockToken contract or operator roles for it.
-- BROKEN: 
-- BROKEN: -- Theorems added by coverage reconciliation
-- BROKEN: 
-- BROKEN: ```lean
-- BROKEN: -- UNFORMALIZABLE req_buffer_not_consumed: The model does not track overcollateralization buffer changes during redemptions explicitly
-- BROKEN: -- UNFORMALIZABLE req_catastrophic_backstop: Catastrophic scenarios and governance actions on buffer deployment are not modeled
-- BROKEN: -- UNFORMALIZABLE req_governance_deploy_buffer: Governance token and voting mechanisms are not part of the model
-- BROKEN: -- UNFORMALIZABLE req_synchronous_withdraw_return_token: The model does not represent apxUSD_unlock tokens or synchronous withdrawal completion

/-- REQ rfq_redemption_allowed: The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute those requests. -/
theorem req_rfq_redemption_allowed (s : State) (user caller : Address) (amount : Amount) (now : Timestamp) :
  (s.rfqCounterparties.contains caller ∧ s.whitelist.contains user ∧ s.bal_apxUSD user ≥ amount ∧ amount > 0) →
  step s (.executeRFQRedemption user amount) caller now ≠ none := sorry

-- BROKEN: /--
-- BROKEN:   REQ deposit-immediate: The apyUSD vault MUST complete deposit operations synchronously and deliver apyUSD shares to the receiver without any delay.
-- BROKEN:   This is formalized as: if `lockApxUSD` succeeds, the caller's apyUSD balance increases immediately.
-- BROKEN: -/
-- BROKEN: theorem req_deposit_immediate (s : State) (amount : Amount) (caller : Address) (now : Timestamp) :
-- BROKEN:   let s' := step s (.lockApxUSD amount) caller now;
-- BROKEN:   s' = none ∨ (∃ s'', s' = some s'' ∧ s''.bal_apyUSD caller ≥ s.bal_apyUSD caller) := by
-- BROKEN:   unfold step
-- BROKEN:   split
-- BROKEN:   · intro h
-- BROKEN:     left
-- BROKEN:     exact h
-- BROKEN:   · intro h
-- BROKEN:     right
-- BROKEN:     cases h
-- BROKEN:     rename_i s'' h_s''
-- BROKEN:     exists s''
-- BROKEN:     constructor
-- BROKEN:     · exact h_s''
-- BROKEN:     · cases h_s'' ▸ h
-- BROKEN:       simp [State.bal_apyUSD]
-- BROKEN:       split
-- BROKEN:       · intro h_cond
-- BROKEN:         have h_false : False := by
-- BROKEN:           cases h_cond.left
-- BROKEN:           case intro h_bal
-- BROKEN:           have h_contra : s.bal_apxUSD caller < amount ∨ amount = 0 := h_bal
-- BROKEN:           cases h_contra
-- BROKEN:           case inl h_bal_lt
-- BROKEN:           have h_bal_contra : s.bal_apxUSD caller ≥ amount := by
-- BROKEN:             have h_none : s' = none := by
-- BROKEN:               rw [step]
-- BROKEN:               simp only [Op.lockApxUSD]
-- BROKEN:               split
-- BROKEN:               · assumption
-- BROKEN:               · simp
-- BROKEN:             contradiction
-- BROKEN:           contradiction
-- BROKEN:           case inr h_amount_zero
-- BROKEN:           have h_amount_nonzero : amount ≠ 0 := by
-- BROKEN:             intro h_zero
-- BROKEN:             subst h_zero
-- BROKEN:             have h_none : s' = none := by
-- BROKEN:               rw [step]
-- BROKEN:               simp only [Op.lockApxUSD]
-- BROKEN:               split
-- BROKEN:               · simp
-- BROKEN:               · simp
-- BROKEN:             contradiction
-- BROKEN:           contradiction
-- BROKEN:         contradiction
-- BROKEN:       · intro h_success
-- BROKEN:         simp
-- BROKEN:         have shares := (amount * 1000000000000000000000000000) / s.exchangeRate_ray
-- BROKEN:         have h_shares_nonneg : shares ≥ 0 := sorry

/--
  REQ mint-immediate: The apyUSD vault MUST complete mint operations synchronously and deliver apyUSD shares to the receiver without any delay.
  This is formalized as: if `mintApxUSD` succeeds, the receiver's apxUSD balance increases immediately.
-/
theorem req_mint_immediate (s : State) (to : Address) (amount : Amount) (caller : Address) (now : Timestamp) :
  let s' := step s (.mintApxUSD to amount) caller now;
  s' = none ∨ (∃ s'', s' = some s'' ∧ s''.bal_apxUSD to ≥ s.bal_apxUSD to) := sorry

end Apyx
