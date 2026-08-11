import D2fsSpecs.Accounting

/-!
# V2-INV: phase structure and the total operation classification

Proof Map v2 (life#59) V2-B demands that no conservation theorem carry its
operation exclusions as *implicit* assumptions: every operation must either
preserve the composite invariant or fall under an explicitly named,
separately proved exception contract. `handleStressEvent` and
`catastrophicBackstop` cannot satisfy a conservation invariant by design —
losing collateral and paying out the whole reserve are their specified
effects — so they get *phase-scoped* rules rather than membership in the
preserving class.

Layers:

* **Phases, derived from the existing state** — `NormalPhase` /
  `StressPhase` read `emergencyFlag`, the model's single phase bit (only
  `handleStressEvent` sets it, nothing clears it). `stressPhase_absorbing`
  proves the phase order Normal → Stress is one-way; `req_catastrophic_backstop`
  already proves the backstop fires only inside `StressPhase`.

* **Exception contracts** — `StressContract` (collateral falls by exactly the
  stress amount, the flag rises, the obligation ledger and reserve are framed,
  and pending-aware solvency degrades by *at most the stress amount*),
  `BackstopContract` (fires only in stress, zeroes the reserve, credits the
  pro-rata payouts, reprices, frames the obligation ledger),
  `ReserveOutflowContract` (admin-only, guarded by the reserve balance, exact
  reserve/receiver deltas, obligation ledger framed).

* **`opCoverage` + `stepContract`** — the totality theorems: every `Op`
  is either `OutstandingScopedOp` (the preserving class of
  `protocolInvFull_step`) or one of the five named exceptions, and one theorem
  delivers the applicable rule for *every* operation with no silent gaps.

Status (proof-map §11): all contracts are model-local; `stepContract` is
the total per-step classification; phase absorption is model-local. The
vault exits appear here through their V2-ACC conservation equations — under
`apxUSDObligations` they are conservation, not exclusion.
-/

namespace Apyx

/-! ## Proof Map v3: operation families

The v2 `opCoverage` theorem classifies preserving operations versus named
exceptions.  v3 adds the orthogonal security boundary: each public operation
belongs to exactly one family.  The classification is used by the existing
step-contract proofs and gives later attacker/composition proofs a closed
operation domain to quantify over. -/

inductive OperationFamily
  | user
  | vault
  | redemption
  | admin
  | oracle
  | governance
  | external
  | time

def operationFamily : Op → OperationFamily
  | Op.depositUSDC _ => .user
  | Op.mintApxUSD _ _ => .user
  | Op.lockApxUSD _ => .vault
  | Op.requestUnlock _ => .redemption
  | Op.claimUnlock _ => .redemption
  | Op.redeemApxUSD _ => .redemption
  | Op.withdraw _ _ => .vault
  | Op.redeem _ _ => .vault
  | Op.flexibleRequestUnlock _ => .redemption
  | Op.flexibleClaimUnlock _ => .redemption
  | Op.pause => .admin
  | Op.unpause => .admin
  | Op.addToWhitelist _ => .admin
  | Op.removeFromWhitelist _ => .admin
  | Op.addToDenylist _ => .admin
  | Op.removeFromDenylist _ => .admin
  | Op.setYieldRate _ => .admin
  | Op.creditYield _ => .admin
  | Op.voteBufferDeployment => .governance
  | Op.submitRFQRequest _ => .redemption
  | Op.executeRFQRedemption _ _ => .external
  | Op.updateRedemptionValue _ => .admin
  | Op.handleStressEvent _ => .admin
  | Op.catastrophicBackstop => .admin
  | Op.setVestPeriod _ => .admin
  | Op.setApxUSDMarketPrice _ => .oracle
  | Op.withdrawReserve _ _ => .admin
  | Op.poolRedeem _ _ _ => .external
  | Op.tick _ => .time

theorem operationFamily_total (op : Op) :
    ∃ family, operationFamily op = family := by
  cases op <;> exact ⟨_, rfl⟩

theorem operationFamily_stepContract_scope (op : Op) :
    operationFamily op = .admin →
      (∃ amount, op = Op.handleStressEvent amount) ∨
      op = Op.catastrophicBackstop ∨
      (∃ amount receiver, op = Op.withdrawReserve amount receiver) ∨
      (∃ value, op = Op.updateRedemptionValue value) ∨
      OutstandingScopedOp op := by
  intro h
  cases op <;> simp_all [operationFamily, OutstandingScopedOp]

/-! ## Proof Map v3: exhaustive accounting boundary

`opCoverage` proves which operations preserve the composite invariant, but that is not the same as
enumerating where value/accounting can change.  This second classifier is intentionally broader: it
names every operation's accounting boundary, including inflows, fee loss, reserve outflow, repricing,
and external settlement.  The class is a scope index; the exact delta theorems remain the evidence. -/

inductive AccountingEffect
  | preserving
  | obligationInflow
  | feeOutflow
  | reserveOutflow
  | collateralLoss
  | backstopSettlement
  | externalSettlement
  | repricing
  | administrative

def accountingEffect : Op → AccountingEffect
  | Op.depositUSDC _ => .obligationInflow
  | Op.mintApxUSD _ _ => .obligationInflow
  | Op.lockApxUSD _ => .preserving
  | Op.requestUnlock _ => .preserving
  | Op.claimUnlock _ => .preserving
  | Op.redeemApxUSD _ => .externalSettlement
  | Op.withdraw _ _ => .preserving
  | Op.redeem _ _ => .preserving
  | Op.flexibleRequestUnlock _ => .preserving
  | Op.flexibleClaimUnlock _ => .feeOutflow
  | Op.pause => .administrative
  | Op.unpause => .administrative
  | Op.addToWhitelist _ => .administrative
  | Op.removeFromWhitelist _ => .administrative
  | Op.addToDenylist _ => .administrative
  | Op.removeFromDenylist _ => .administrative
  | Op.setYieldRate _ => .administrative
  | Op.creditYield _ => .obligationInflow
  | Op.voteBufferDeployment => .administrative
  | Op.submitRFQRequest _ => .preserving
  | Op.executeRFQRedemption _ _ => .externalSettlement
  | Op.updateRedemptionValue _ => .repricing
  | Op.handleStressEvent _ => .collateralLoss
  | Op.catastrophicBackstop => .backstopSettlement
  | Op.setVestPeriod _ => .administrative
  | Op.setApxUSDMarketPrice _ => .repricing
  | Op.withdrawReserve _ _ => .reserveOutflow
  | Op.poolRedeem _ _ _ => .externalSettlement
  | Op.tick _ => .preserving

theorem accountingEffect_total (op : Op) :
    ∃ effect, accountingEffect op = effect := by
  cases op <;> exact ⟨_, rfl⟩

theorem accountingEffect_preserving_scope (op : Op) :
    accountingEffect op = .preserving →
      (obligationTraceOp op ∨
        (∃ a, op = Op.submitRFQRequest a)) := by
  intro h
  cases op <;> simp [accountingEffect, obligationTraceOp] at h ⊢

/-! ## Proof Map v3: operation-contract coverage

`OperationFamily` and `AccountingEffect` answer *where an operation belongs*;
they do not, by themselves, prove its transition contract.  The following
catalog makes the five contract dimensions explicit for every constructor of
the public `Op` type.  A `partial` or `notModeled` entry is intentionally not a
proof result: it is a typed to-do boundary that prevents a future report from
silently treating a family classification as a pre/postcondition proof.
-/

inductive ContractStatus
  | proved
  | incomplete
  | handoff
  | notModeled

structure OperationContractCoverage where
  family : OperationFamily
  accounting : AccountingEffect
  precondition : ContractStatus
  postcondition : ContractStatus
  revert : ContractStatus
  frame : ContractStatus
  relational : ContractStatus
  evidence : List String
  nextCheck : String

private def modelContract (family : OperationFamily) (accounting : AccountingEffect)
    (evidence : List String) (nextCheck : String) : OperationContractCoverage :=
  { family := family
    accounting := accounting
    precondition := .incomplete
    postcondition := .incomplete
    revert := .notModeled
    frame := .incomplete
    relational := .notModeled
    evidence := evidence
    nextCheck := nextCheck }

private def implementationContract (family : OperationFamily) (accounting : AccountingEffect)
    (evidence : List String) (nextCheck : String) : OperationContractCoverage :=
  { family := family
    accounting := accounting
    precondition := .incomplete
    postcondition := .incomplete
    revert := .notModeled
    frame := .incomplete
    relational := .handoff
    evidence := evidence
    nextCheck := nextCheck }

def operationContract : Op → OperationContractCoverage
  | Op.depositUSDC _ => modelContract .user .obligationInflow
      ["depositUSDC_step_effect", "apxUSDLedgerConsistent_step"]
      "prove named guard reasons and USDC boundary"
  | Op.mintApxUSD _ _ => modelContract .user .obligationInflow
      ["mintApxUSD_step_effect", "apxUSDLedgerConsistent_step"]
      "prove oracle-price and recipient guard contract"
  | Op.lockApxUSD _ => modelContract .vault .preserving
      ["apxUSDObligations_lockApxUSD", "apyUSDLedgerConsistent_lock_step"]
      "prove live-rate rounding postcondition"
  | Op.requestUnlock _ => modelContract .redemption .preserving
      ["requestUnlockStep_effect", "apxUSDObligations_requestUnlock"]
      "return typed standard-request revert reasons"
  | Op.claimUnlock _ => modelContract .redemption .preserving
      ["claimUnlockStep_effect", "apxUSDObligations_claimUnlock"]
      "prove owner/operator and cooldown failure reasons"
  | Op.redeemApxUSD _ => modelContract .redemption .externalSettlement
      ["redeemApxUSD_step_effect", "req_buffer_non_decreasing"]
      "connect reserve sufficiency and external USDC settlement"
  | Op.withdraw _ _ => implementationContract .vault .preserving
      ["withdrawStep_effect", "holder_value_withdraw"]
      "refine vault custody and UnlockToken receipt semantics"
  | Op.redeem _ _ => implementationContract .vault .preserving
      ["redeemStep_effect", "holder_value_redeem"]
      "refine vault custody and UnlockReceipt semantics"
  | Op.flexibleRequestUnlock _ => modelContract .redemption .preserving
      ["flexibleRequestUnlockStep_effect", "apxUSDObligations_flexibleRequestUnlock"]
      "prove concurrent-position and fee-recipient frames"
  | Op.flexibleClaimUnlock _ => modelContract .redemption .feeOutflow
      ["flexibleClaimStep_effect", "flexibleClaim_holderValueAt_fee"]
      "prove fee recipient conservation"
  | Op.pause => modelContract .admin .administrative ["pause_guard"]
      "add role-specific revert and frame theorem"
  | Op.unpause => modelContract .admin .administrative ["unpause_guard"]
      "add role-specific revert and frame theorem"
  | Op.addToWhitelist _ => modelContract .admin .administrative ["whitelist_frame"]
      "connect AccessManager role graph"
  | Op.removeFromWhitelist _ => modelContract .admin .administrative ["whitelist_frame"]
      "connect AccessManager role graph"
  | Op.addToDenylist _ => modelContract .admin .administrative ["denylist_frame"]
      "connect token hook behavior"
  | Op.removeFromDenylist _ => modelContract .admin .administrative ["denylist_frame"]
      "connect token hook behavior"
  | Op.setYieldRate _ => modelContract .admin .administrative ["yield_rate_guard"]
      "prove cadence and collateral-base relational contract"
  | Op.creditYield _ => modelContract .admin .obligationInflow
      ["apxUSDObligations_creditYield", "REQ-credit-preserves-accrued-vest"]
      "connect YieldDistributor authority and custody"
  | Op.voteBufferDeployment => modelContract .governance .administrative ["governance_guard"]
      "model vote aggregation and timelock"
  | Op.submitRFQRequest _ => modelContract .redemption .preserving ["rfq_request_frame"]
      "connect RFQ request registry and counterparty settlement"
  | Op.executeRFQRedemption _ _ => implementationContract .external .externalSettlement
      ["external settlement boundary"]
      "model approved-counterparty and USDC transfer semantics"
  | Op.updateRedemptionValue _ => modelContract .admin .repricing ["redemption_value_frame"]
      "prove price-authority and user-value relational effects"
  | Op.handleStressEvent _ => modelContract .admin .collateralLoss ["handleStressEvent_contract"]
      "connect exogenous loss to reserve/collateral evidence"
  | Op.catastrophicBackstop => modelContract .admin .backstopSettlement
      ["catastrophicBackstop_contract", "catastrophicBackstop_accounting"]
      "prove deployed payout and rounding-residual boundary"
  | Op.setVestPeriod _ => modelContract .admin .administrative
      ["apxUSDObligations_pullVestedYield"]
      "prove admin authority and vesting-clock frame"
  | Op.setApxUSDMarketPrice _ => modelContract .oracle .repricing ["oracle price field frame"]
      "model freshness, source, and multi-price consistency"
  | Op.withdrawReserve _ _ => implementationContract .admin .reserveOutflow
      ["withdrawReserve_contract", "reserve_outflow_only_via_redemption"]
      "connect AccessManager delay and Safe threshold"
  | Op.poolRedeem _ _ _ => implementationContract .external .externalSettlement
      ["pool redemption boundary"]
      "model redeemer role, minOut, and token custody"
  | Op.tick _ => modelContract .time .preserving
      ["apxUSDObligations_tick", "now_moves_only_by_tick"]
      "add liveness/fairness contract if progress is claimed"

theorem operationContract_family (op : Op) :
    (operationContract op).family = operationFamily op := by
  cases op <;> rfl

theorem operationContract_accounting (op : Op) :
    (operationContract op).accounting = accountingEffect op := by
  cases op <;> rfl

theorem operationContract_dimensions_explicit (op : Op) :
    ∃ c : OperationContractCoverage,
      operationContract op = c :=
  ⟨operationContract op, rfl⟩

/-! ## Phases

`NormalPhase` is defined in `Init.lean` (it is a conjunct of `Init`); this
module adds its stress-side counterpart and the phase-order facts. -/

/-- Stress operation: the emergency flag is up. Entered by a successful
`handleStressEvent`; the backstop's guard requires this phase. -/
def StressPhase (s : State) : Prop := s.emergencyFlag = true

/-- **The stress phase is absorbing**: no operation clears the emergency flag.
Once the protocol has entered stress, every successful step stays there. -/
theorem stressPhase_absorbing (s : State) (op : Op) (caller : Address) (s' : State)
    (hstep : step s op caller = some s') (h : StressPhase s) : StressPhase s' := by
  unfold StressPhase at h ⊢
  cases hop : op with
  | handleStressEvent a =>
      subst hop
      simp only [step] at hstep
      split at hstep
      · cases Option.some.inj hstep; rfl
      · exact absurd hstep (by simp)
  | _ =>
      subst hop
      rw [emergencyFlag_frame s _ caller s' hstep (by simp)]
      exact h

/-! ## Exception contracts -/

/-- The stress-phase entry contract: admin-only, the collateral falls by
exactly the exogenous loss, the flag rises, the obligation ledger and the
reserve are framed — and pending-aware solvency degrades by **at most the
stress amount**, the v2 "buffer decrease bounded by the stress amount" rule. -/
def StressContract (s s' : State) (amount : Nat) : Prop :=
  s'.totalCollateralValue = s.totalCollateralValue - amount ∧
  StressPhase s' ∧
  apxUSDObligations s' = apxUSDObligations s ∧
  s'.usdcReserve = s.usdcReserve ∧
  outstandingApxUSD s' = outstandingApxUSD s ∧
  (SolventOutstanding s →
    outstandingApxUSD s' ≤ s'.totalCollateralValue + s'.usdcReserve + amount)

/-- The wind-down contract: fires only inside `StressPhase`, reprices to the
collateral-per-token rate, credits every address its pro-rata payout, zeroes
the reserve and the buffer, and frames the apxUSD obligation ledger. The
payout/residual conservation equation is `catastrophicBackstop_accounting`. -/
def BackstopContract (s s' : State) : Prop :=
  StressPhase s ∧
  s'.redemptionValue = (s.totalCollateralValue * ray) / s.totalSupply_apxUSD ∧
  (∀ a, s'.usdcBal a = s.usdcBal a + backstopPayout s a) ∧
  s'.usdcReserve = 0 ∧
  s'.overcollateralizationBuffer = 0 ∧
  apxUSDObligations s' = apxUSDObligations s

/-- The bare admin reserve outflow: guarded by the reserve balance, with exact
reserve and receiver deltas; the apxUSD obligation ledger is framed. -/
def ReserveOutflowContract (s s' : State) (amount : Nat) (receiver : Address) : Prop :=
  amount ≤ s.usdcReserve ∧
  s'.usdcReserve = s.usdcReserve - amount ∧
  s'.usdcBal receiver = s.usdcBal receiver + amount ∧
  apxUSDObligations s' = apxUSDObligations s

theorem handleStressEvent_contract (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hstep : step s (Op.handleStressEvent amount) caller = some s') :
    StressContract s s' amount := by
  simp only [step] at hstep
  split at hstep
  · cases Option.some.inj hstep
    refine ⟨rfl, rfl, ?_, rfl, ?_, ?_⟩
    · unfold apxUSDObligations apxUSDFlow
      rw [outstandingApxUSD_of_projections_eq (s :=
        { s with totalCollateralValue := s.totalCollateralValue - amount,
                 emergencyFlag := true }) (t := s) rfl rfl rfl rfl]
    · exact outstandingApxUSD_of_projections_eq rfl rfl rfl rfl
    · intro hsol
      have h1 : outstandingApxUSD
          { s with totalCollateralValue := s.totalCollateralValue - amount,
                   emergencyFlag := true } = outstandingApxUSD s :=
        outstandingApxUSD_of_projections_eq rfl rfl rfl rfl
      unfold SolventOutstanding at hsol
      rw [h1]
      dsimp only
      omega
  · exact absurd hstep (by simp)

theorem catastrophicBackstop_contract (s : State) (caller : Address) (s' : State)
    (hstep : step s Op.catastrophicBackstop caller = some s') :
    BackstopContract s s' := by
  have hguard : caller = s.admin ∧ s.emergencyFlag = true := by
    simp only [step] at hstep
    split at hstep
    · assumption
    · exact absurd hstep (by simp)
  obtain ⟨hcaller, hflag⟩ := hguard
  subst hcaller
  obtain ⟨-, hprice, hbal, hres, hbuf⟩ := req_catastrophic_backstop s s' hstep
  refine ⟨hflag, hprice, fun a => hbal a, hres, hbuf, ?_⟩
  simp only [step, hflag] at hstep
  split at hstep
  · cases Option.some.inj hstep
    unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
      standardUnlockTotal flexibleUnlockTotal
    dsimp only
  · exact absurd hstep (by simp)

theorem withdrawReserve_contract (s : State) (amount : Nat)
    (receiver caller : Address) (s' : State)
    (hstep : step s (Op.withdrawReserve amount receiver) caller = some s') :
    ReserveOutflowContract s s' amount receiver := by
  simp only [step] at hstep
  split at hstep
  · split at hstep
    · exact absurd hstep (by simp)
    · rename_i hguard
      cases Option.some.inj hstep
      refine ⟨by omega, rfl, by simp, ?_⟩
      unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
        standardUnlockTotal flexibleUnlockTotal
      dsimp only
  · exact absurd hstep (by simp)

/-! ## Totality: every operation is classified, nothing is silently excluded -/

/-- **Operation coverage**: every `Op` is either in the preserving scope of
`protocolInvFull_step` or is one of the five named exceptions. This is the v2
"no implicit exclusion" declaration, checkable by case analysis. -/
theorem opCoverage (op : Op) :
    OutstandingScopedOp op ∨
    (∃ assets receiver, op = Op.withdraw assets receiver) ∨
    (∃ shares receiver, op = Op.redeem shares receiver) ∨
    (∃ amount, op = Op.handleStressEvent amount) ∨
    op = Op.catastrophicBackstop ∨
    (∃ amount receiver, op = Op.withdrawReserve amount receiver) := by
  cases op <;>
    first
      | (left
         refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ => ?_, ?_, fun _ _ => ?_⟩ <;>
           (simp; done))
      | (right; left; exact ⟨_, _, rfl⟩)
      | (right; right; left; exact ⟨_, _, rfl⟩)
      | (right; right; right; left; exact ⟨_, rfl⟩)
      | (right; right; right; right; left; rfl)
      | (right; right; right; right; right; exact ⟨_, _, rfl⟩)

/-- **The total step contract**: one theorem delivering, for *every* operation
with no exclusions, the rule that governs it — invariant preservation for the
scoped class, conservation for the vault exits, and the named phase/outflow
contracts for the three remaining exceptions. -/
theorem stepContract (s : State) (op : Op) (caller : Address) (s' : State)
    (hstep : step s op caller = some s') :
    (OutstandingScopedOp op → PriceBoundedOp op → ProtocolInvFull s → ProtocolInvFull s') ∧
    (∀ assets receiver, op = Op.withdraw assets receiver → RegistryWellIndexed s →
      apxUSDObligations s' = apxUSDObligations s) ∧
    (∀ shares receiver, op = Op.redeem shares receiver → RegistryWellIndexed s →
      apxUSDObligations s' = apxUSDObligations s) ∧
    (∀ amount, op = Op.handleStressEvent amount → StressContract s s' amount) ∧
    (op = Op.catastrophicBackstop → BackstopContract s s') ∧
    (∀ amount receiver, op = Op.withdrawReserve amount receiver →
      ReserveOutflowContract s s' amount receiver) := by
  refine ⟨fun hscope hprice hinv => protocolInvFull_step s op caller s' hinv hstep hscope hprice,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro assets receiver rfl hreg
    exact apxUSDObligations_withdraw s assets receiver caller s' hreg hstep
  · rintro shares receiver rfl hreg
    exact apxUSDObligations_redeem s shares receiver caller s' hreg hstep
  · rintro amount rfl
    exact handleStressEvent_contract s amount caller s' hstep
  · rintro rfl
    exact catastrophicBackstop_contract s caller s' hstep
  · rintro amount receiver rfl
    exact withdrawReserve_contract s amount receiver caller s' hstep

/-! ## v3 connection: coverage entry to an actual proof obligation

`operationContract` remains a status index because revert-reason fidelity and
implementation refinement are not yet modeled.  The model-local portion is
nevertheless a real proposition, not only a string in the catalog: it is the
existing total `stepContract` packaged as the proof obligation attached to an
operation entry.  This is the seam future per-operation pre/post/frame and
relational proofs can refine without changing the public operation taxonomy.
-/

def OperationContractProof (s : State) (op : Op) (caller : Address) (s' : State) : Prop :=
  step s op caller = some s' →
    (OutstandingScopedOp op → PriceBoundedOp op → ProtocolInvFull s → ProtocolInvFull s') ∧
    (∀ assets receiver, op = Op.withdraw assets receiver → RegistryWellIndexed s →
      apxUSDObligations s' = apxUSDObligations s) ∧
    (∀ shares receiver, op = Op.redeem shares receiver → RegistryWellIndexed s →
      apxUSDObligations s' = apxUSDObligations s) ∧
    (∀ amount, op = Op.handleStressEvent amount → StressContract s s' amount) ∧
    (op = Op.catastrophicBackstop → BackstopContract s s') ∧
    (∀ amount receiver, op = Op.withdrawReserve amount receiver →
      ReserveOutflowContract s s' amount receiver)

theorem operationContract_proof (s : State) (op : Op) (caller : Address) (s' : State) :
    OperationContractProof s op caller s' := by
  intro hstep
  exact stepContract s op caller s' hstep

end Apyx
