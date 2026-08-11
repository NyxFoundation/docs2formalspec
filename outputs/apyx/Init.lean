import D2fsSpecs.Invariant

/-!
# Funded initial states and the `Init`-anchored reachability relation

Proof Map v2 (life#59) V2-A asks for a global safety series that does **not**
anchor reachability at the empty `default` state: from `default` no in-scope
operation seeds a positive USDC balance, so a funded settlement trace would
not be exhibitable from that base. This module provides the layer:

* `Init` — the predicate a *legitimate initial state* must satisfy. It is not a
  single state: any state whose registries are well-indexed, whose pending-aware
  solvency holds, whose finite ledgers agree with their supplies, whose receipt
  ledger matches the registries, and whose emergency flag is down, qualifies.
  `default` satisfies it, and so does the funded witness `fundedInit` below.
* `ProtocolInvFull` — the v2 composite: `ProtocolInvOutstanding` plus the receipt
  ledger identity plus the phase discipline.
* `init_inv` / `protocolInvFull_step` / `protocolInvFull_reachable` — the v2 main
  series: initialization, per-step preservation with operation-side conditions
  only, and reachability from **any** `Init` state.
* `fundedInit_settlement_trace` — the funded witness runs a full
  request → cooldown → claim settlement cycle, which the `default`-anchored
  relation could never exhibit as a nonzero trace.

Scope: the reachability relation carries the operation-side conditions
`OutstandingScopedOp` + `PriceBoundedOp` of `protocolInvOutstanding_step`. Removing
the vault-exit exclusion is V2-ACC/V2-INV work — it requires the custody
accounting this measure does not yet contain; the stress/backstop exclusions
move to phase-scoped invariants in V2-INV. The USDC holder ledger
(`UsdcLedgerConsistent`) stays outside `Init` because it takes its finite
support and total supply as **external parameters** — the current `State` has
no USDC total-supply field. Proof Map v2 records this as decision V2-A option 2:
`Init` stays a `State` predicate, and the USDC boundary remains a documented
external-accounting layer rather than a silently-absorbed conjunct.

Status (proof-map §11): `init_inv` and `protocolInvFull_step` are model-local;
`protocolInvFull_reachable` is reachable-scoped over `ReachInit`;
`fundedInit_settlement_trace` is a witness.
-/

namespace Apyx

/-- Phase discipline for legitimate initial states: the emergency flag is down.
The only writer of `emergencyFlag` is `Op.handleStressEvent` (the backstop
*reads* it as a guard but never writes it), so under `OutstandingScopedOp` this
is a frame fact, proved as `emergencyFlag_frame`/`normalPhase_step` below. V2-INV replaces
this single bit with an explicit Normal/Stress/Backstop phase. -/
def NormalPhase (s : State) : Prop := s.emergencyFlag = false

/-- A legitimate initial state for the v2 safety series. Not anchored at any
concrete state — `default` qualifies (`init_default`), and so does the funded
`fundedInit` (`init_fundedInit`). -/
def Init (s : State) : Prop :=
  RegistryWellIndexed s ∧ SolventOutstanding s ∧ WellFormed s ∧
    ApxUSDLedgerConsistent s ∧ ApyUSDLedgerConsistent s ∧
    UnlockTokenLedgerConsistent s ∧ NormalPhase s

/-- The v2 composite invariant: the pending-aware composite plus the receipt
ledger identity plus the phase discipline. -/
def ProtocolInvFull (s : State) : Prop :=
  ProtocolInvOutstanding s ∧ UnlockTokenLedgerConsistent s ∧ NormalPhase s

/-- v2 main series, initialization: a legitimate initial state satisfies the
composite invariant. This is a projection — `Init` was chosen to be exactly the
data the induction needs. -/
theorem init_inv (s : State) (h : Init s) : ProtocolInvFull s :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The empty state is a legitimate initial state, so the v1 anchoring is a
special case of the v2 relation. -/
theorem init_default : Init (default : State) :=
  ⟨registryWellIndexed_default, solventOutstanding_default,
   protocolInv_default.2.2.1, apxUSDLedgerConsistent_default,
   apyUSDLedgerConsistent_default, unlockTokenLedgerConsistent_default, rfl⟩

@[simp] private theorem pullVestedYield_emergencyFlag (s : State) :
    (pullVestedYield s).emergencyFlag = s.emergencyFlag := by
  unfold pullVestedYield
  dsimp only
  split <;> rfl

/-- **Only `handleStressEvent` writes the emergency flag.** Exhaustive over the
closed `Op`; the backstop reads the flag as a guard but leaves it unchanged. -/
theorem emergencyFlag_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_not_stress : ∀ a, op ≠ Op.handleStressEvent a) :
    s'.emergencyFlag = s.emergencyFlag := by
  cases op
  case handleStressEvent a => exact absurd rfl (h_not_stress a)
  all_goals
    simp only [step] at h_step
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; rfl)
        | (cases Option.some.inj h_step
           simp [emitEvent, updateExchangeRate, createStandardUnlock,
             createFlexibleUnlock, retireStandardUnlock, retireFlexibleUnlock,
             updateStandardUnlock, burnUnlockNFT, burnApyUSD, mintApyUSD,
             burnApxUSD, mintApxUSD])
        | exact absurd h_step (by simp)

/-- The phase discipline is a frame fact under the outstanding scope. -/
theorem normalPhase_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (hscope : OutstandingScopedOp op)
    (h : NormalPhase s) : NormalPhase s' := by
  unfold NormalPhase at h ⊢
  rw [emergencyFlag_frame s op caller s' h_step hscope.2.2.1]
  exact h

/-- v2 main series, preservation: one successful in-scope step preserves the
composite, with operation-side hypotheses only. -/
theorem protocolInvFull_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h : ProtocolInvFull s) (hstep : step s op caller = some s')
    (hscope : OutstandingScopedOp op) (hprice : PriceBoundedOp op) :
    ProtocolInvFull s' :=
  ⟨protocolInvOutstanding_step s op caller s' h.1 hstep hscope hprice,
   unlockTokenLedgerConsistent_step s s' op caller h.1.1 h.2.1 hstep,
   normalPhase_step s op caller s' hstep hscope h.2.2⟩

/-- Reachability from **any** legitimate initial state. A `default`-anchored
relation is the special case `ReachInit.initial init_default`; the step
constructor carries the operation-side conditions of
`protocolInvOutstanding_step`. -/
inductive ReachInit : State → Prop
  | initial {s : State} : Init s → ReachInit s
  | next {s s' : State} {op : Op} {caller : Address} :
      ReachInit s →
      (es : List Event) →
      stepResult s op caller = .accepted s' es →
      OutstandingScopedOp op →
      PriceBoundedOp op →
      ReachInit s'

/-- Successful-`step` form of the step constructor, for callers that do not
carry the event projection. -/
theorem ReachInit.next' {s s' : State} {op : Op} {caller : Address}
    (h : ReachInit s) (hstep : step s op caller = some s')
    (hscope : OutstandingScopedOp op) (hprice : PriceBoundedOp op) :
    ReachInit s' :=
  ReachInit.next h (eventDelta s s')
    ((stepResult_accepted_iff s op caller s' (eventDelta s s')).mpr ⟨hstep, rfl⟩)
    hscope hprice

/-- v2 main series, reachability: every state reachable from a legitimate
initial state satisfies the composite invariant. -/
theorem protocolInvFull_reachable (s : State) (h : ReachInit s) :
    ProtocolInvFull s := by
  induction h with
  | initial hinit => exact init_inv _ hinit
  | next _ es hacc hscope hprice ih =>
      exact protocolInvFull_step _ _ _ _ ih
        ((stepResult_accepted_iff _ _ _ _ _).mp hacc).1 hscope hprice

/-! The v3 state-view form of the main reachability theorem.  This is not a
new projection-only fact: it consumes the same `ProtocolInvFull` induction
and then routes its pending-aware component through
`protocolInvOutstanding_to_view`. -/

theorem protocolInvFull_reachable_view (s : State) (h : ReachInit s) :
    ProtocolViewInvariant (protocolState s) (outstandingApxUSD s) :=
  protocolInvOutstanding_to_view s (protocolInvFull_reachable s h).1

/-! ## The funded witness

A concrete nonzero legitimate initial state: one holder (address 1) with 1000
apxUSD, collateral 1200, reserve 300, price at par, no pending positions. The
settlement-cycle theorem below is exactly the trace the `default`-anchored
relation could not exhibit. -/

/-- A funded legitimate initial state. -/
def fundedInit : State :=
  { (default : State) with
      totalSupply_apxUSD := 1000
      apxUSDBal := fun a => if a = 1 then 1000 else 0
      totalCollateralValue := 1200
      usdcReserve := 300
      redemptionValue := ray }

theorem init_fundedInit : Init fundedInit := by
  refine ⟨⟨⟨fun i _ => rfl, fun i _ => rfl⟩, fun a i h => by simp [fundedInit, default] at h,
      fun i => Or.inl rfl⟩, ?_, ⟨?_, Nat.le_refl ray⟩, ?_, ?_, ?_, rfl⟩
  · -- SolventOutstanding: 1000 + 0 ≤ 1200 + 300
    unfold SolventOutstanding outstandingApxUSD pendingApxUSD
      standardUnlockTotal flexibleUnlockTotal
    simp [fundedInit, default]
  · -- balances bounded by supply
    intro a
    by_cases h : a = 1 <;> simp [fundedInit, h]
  · -- finite apxUSD ledger: single holder [1]
    exact ⟨[1], by simp, fun a ha => by
      by_cases h : a = 1
      · simp [h]
      · exfalso; exact ha (by simp [fundedInit, h]),
      by simp [sumOver, fundedInit]⟩
  · -- finite apyUSD ledger: empty
    exact ⟨[], by simp, fun a ha => by exact absurd rfl ha, by simp [sumOver, fundedInit, default]⟩
  · -- receipt ledger: vacuous, no ids allocated
    intro id hid
    simp [fundedInit, default] at hid

/-- **The funded settlement cycle.** From `fundedInit`, a request for 400
apxUSD succeeds, the cooldown elapses by `tick`, and the claim does not revert
— the full request → cooldown → claim cycle runs from a nonzero legitimate
initial state. A `default`-anchored relation cannot exhibit this trace: from
the empty `default` no in-scope operation seeds the balances this cycle
consumes. -/
theorem fundedInit_settlement_trace :
    ∃ s₁ s₂,
      step fundedInit (Op.requestUnlock 400) 1 = some s₁ ∧
      step s₁ (Op.tick cooldownPeriod) 1 = some s₂ ∧
      step s₂ (Op.claimUnlock fundedInit.nextUnlockId) 1 ≠ none :=
  redemption_cycle_closes_after_cooldown fundedInit 400 1 rfl
    (by simp [fundedInit]) rfl rfl

/-- The settlement cycle stays inside the v2 relation: both executed steps are
in scope, so the mid-cycle states are `ReachInit`-reachable and carry
`ProtocolInvFull`. -/
theorem fundedInit_settlement_reachInit :
    ∃ s₁ s₂,
      step fundedInit (Op.requestUnlock 400) 1 = some s₁ ∧
      step s₁ (Op.tick cooldownPeriod) 1 = some s₂ ∧
      ReachInit s₂ ∧ ProtocolInvFull s₂ := by
  obtain ⟨s₁, s₂, h1, h2, -⟩ := fundedInit_settlement_trace
  have r0 : ReachInit fundedInit := ReachInit.initial init_fundedInit
  have r1 : ReachInit s₁ := r0.next' h1 (by simp [OutstandingScopedOp]) (by simp [PriceBoundedOp])
  have r2 : ReachInit s₂ := r1.next' h2 (by simp [OutstandingScopedOp]) (by simp [PriceBoundedOp])
  exact ⟨s₁, s₂, h1, h2, r2, protocolInvFull_reachable s₂ r2⟩

end Apyx
