import D2fsSpecs.Registry
import D2fsSpecs.Safety
import D2fsSpecs.Ledger
import D2fsSpecs.HolderValue
import D2fsSpecs.Transition

/-!
# Conditional composite invariant layer

`docs/11-apyx-proof-map.md` §6 asks for a composite `Inv` with an initialization
theorem, a per-step preservation theorem, and a reachability predicate built from
the *same* transition restrictions the preservation theorem uses. This module
supplies exactly that shape for the facts the development actually carries:

~~~text
ProtocolInv s := RegistryWellIndexed s ∧ Solvent s ∧ WellFormed s ∧
  ApxUSDLedgerConsistent s ∧ ApyUSDLedgerConsistent s
~~~

**This is a conditional, global-design layer — not an unconditional deployed
safety theorem.** The composition is honest about three standing limits of the
current aggregate model, none of which this module repairs:

* **Pending unlock liabilities are not in `Solvent`.** `Solvent` compares
  `totalSupply_apxUSD` against collateral plus reserve; apxUSD burned into a
  standard or flexible unlock position leaves the supply while the future
  re-mint obligation is tracked nowhere on the left-hand side. That is exactly
  why `solvency_step` must exclude `claimUnlock` and `flexibleClaimUnlock`, and
  why those exclusions reappear verbatim in `SolvencyScopedOp` below.
* **The aggregate facts do not imply the finite ledger identities.** The token
  ledgers are bare `Address → Nat` functions, so
  `ApxUSDLedgerConsistent` and `ApyUSDLedgerConsistent` are carried as separate
  conjuncts and preserved by their writer programs; neither is derived from
  `WellFormed`/`Solvent`. Their witnesses record this model expressiveness gap.
* **`WellFormed s'` is an explicit transition assumption in the base layer —
  and discharged in the ops-only layer below.** `protocolInv_step` takes the
  post-state's well-formedness as a hypothesis rather than proving it, and
  `ProtocolReach.next` carries the same hypothesis so that
  `protocolInv_reachable` closes the §6 loop *for this restricted relation*
  without a gap between the preservation theorem and the reachability
  predicate. Since `Ledger.lean` now proves the finite apxUSD identity is
  preserved by every `Op` and implies the per-address balance bound
  (`apxUSDLedgerConsistent_balance_le`), the only part of `WellFormed` that
  genuinely needs a side condition is the price bound `redemptionValue ≤ ray`,
  whose sole in-scope writer is `updateRedemptionValue` (the model, like the
  deployment, caps nothing). The `PriceBoundedOp` layer below therefore trades
  the *state-side* hypothesis `WellFormed s'` for the *operation-side*
  condition "any `updateRedemptionValue` in the trace publishes at most par",
  yielding `ProtocolReachOps`/`protocolInv_reachableOps` with no post-state
  assumption at all. The base layer is kept because a par-exceeding price
  update is a real admin capability (deployment guard is only `newRate != 0`);
  the ops-only layer describes the at-most-par operating regime.

The five operation exclusions are precisely those `solvency_step` already
requires — `claimUnlock`, `flexibleClaimUnlock`, `handleStressEvent`,
`catastrophicBackstop`, `withdrawReserve` — with the reasons documented at that
theorem. Nothing here re-argues or widens them.

The base state is the model's empty `default`, with the same caveat as
`RegistryReach` in `Registry.lean`: using it is a modeling choice, not a claim
that a deployed genesis or post-migration state matches it.

Status (proof-map §11): `protocolInv_default` and `protocolInv_step` are
model-local; `protocolInv_reachable` is reachable-scoped over the restricted
`ProtocolReach` relation. All three are conditional in the sense above.
-/

namespace Apyx

/-- The composite design invariant currently provable in one package: registry
well-indexedness, aggregate solvency, per-address well-formedness, and the
finite apxUSD and apyUSD ledger identities. Conditional —
see the module docstring for what each conjunct does and does not claim. -/
def ProtocolInv (s : State) : Prop :=
  RegistryWellIndexed s ∧ Solvent s ∧ WellFormed s ∧
    ApxUSDLedgerConsistent s ∧ ApyUSDLedgerConsistent s

/-- The receipt-aware extension of `ProtocolInv`.

This is kept as a separate predicate rather than silently changing `ProtocolInv`:
the latter is already used for the solvency-scoped design relation, while this
extension adds the model-local identity tying pending registry amounts to the
receipt owner and face amount. The receipt identity has its own exhaustive
operation coverage; it does not add a fee-wallet or USDC ledger that the current
`State` cannot represent. -/
def ProtocolInvWithReceiptLedger (s : State) : Prop :=
  ProtocolInv s ∧ UnlockTokenLedgerConsistent s

/-- Exactly the five operation exclusions `solvency_step` requires, packaged as
one predicate on the operation. `claimUnlock`/`flexibleClaimUnlock` re-mint
against unlock obligations `Solvent` does not track as liabilities;
`handleStressEvent` is an exogenous collateral loss; `catastrophicBackstop` is
the documented wind-down that pays out the whole reserve; `withdrawReserve` is
the admin's bare reserve outflow with nothing on the other side of the ledger.
See `solvency_step` in `Safety.lean` for the full discussion. -/
def SolvencyScopedOp (op : Op) : Prop :=
  (∀ id, op ≠ Op.claimUnlock id) ∧
  (∀ id, op ≠ Op.flexibleClaimUnlock id) ∧
  (∀ a, op ≠ Op.handleStressEvent a) ∧
  op ≠ Op.catastrophicBackstop ∧
  (∀ amt r, op ≠ Op.withdrawReserve amt r)

/-- Initialization: the empty `default` state satisfies the composite invariant.
Everything is zero, so solvency, well-formedness, and both ledger identities are
trivial; the registry part is `registryWellIndexed_default`. -/
theorem protocolInv_default : ProtocolInv (default : State) := by
  refine ⟨registryWellIndexed_default, Nat.zero_le _, ?_,
    apxUSDLedgerConsistent_default, apyUSDLedgerConsistent_default⟩
  exact ⟨(fun _ => Nat.zero_le _), Nat.zero_le _⟩

theorem protocolInvWithReceiptLedger_default :
    ProtocolInvWithReceiptLedger (default : State) := by
  exact ⟨protocolInv_default, unlockTokenLedgerConsistent_default⟩

/-- Conditional preservation: a successful step preserves `ProtocolInv`, given
(1) the five solvency exclusions on the operation and (2) `WellFormed` at the
**post**-state, supplied as an explicit hypothesis. The registry conjunct is
unconditional (`registryWellIndexed_step`); the solvency conjunct is
`solvency_step` under its documented exclusions; the well-formedness conjunct
cannot be derived from the aggregate ledger and is therefore assumed, not
proved; the two finite ledger conjuncts are supplied by
`apxUSDLedgerConsistent_step` and `apyUSDLedgerConsistent_step`. -/
theorem protocolInv_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h : ProtocolInv s) (hstep : step s op caller = some s')
    (hscope : SolvencyScopedOp op) (hwf' : WellFormed s') :
    ProtocolInv s' :=
  ⟨registryWellIndexed_step s op caller s' h.1 hstep,
   solvency_step s op caller s' hstep h.2.1 h.2.2.1
     hscope.1 hscope.2.1 hscope.2.2.1 hscope.2.2.2.1 hscope.2.2.2.2,
   hwf',
   apxUSDLedgerConsistent_step s s' op caller h.2.2.2.1 hstep,
   apyUSDLedgerConsistent_step s s' op caller h.2.2.2.2 hstep⟩

/-- Conditional preservation of the receipt-aware composite. The solvency and
`WellFormed` premises are exactly those of `protocolInv_step`; receipt
consistency additionally consumes the registry premise and its exhaustive
operation coverage. -/
theorem protocolInvWithReceiptLedger_step
    (s : State) (op : Op) (caller : Address) (s' : State)
    (h : ProtocolInvWithReceiptLedger s)
    (hstep : step s op caller = some s')
    (hscope : SolvencyScopedOp op) (hwf' : WellFormed s') :
    ProtocolInvWithReceiptLedger s' := by
  refine ⟨protocolInv_step s op caller s' h.1 hstep hscope hwf', ?_⟩
  exact unlockTokenLedgerConsistent_step s s' op caller h.1.1 h.2 hstep

/-- The same composite preservation theorem stated over the explicit
`StepResult` boundary. The event payload is carried through but does not enter
the current invariant; the accepted-result equivalence supplies the underlying
successful `step` equation. -/
theorem protocolInv_stepResult_accepted
    (s : State) (op : Op) (caller : Address) (s' : State) (es : List Event)
    (h : ProtocolInv s)
    (hacc : stepResult s op caller = .accepted s' es)
    (hscope : SolvencyScopedOp op) (hwf' : WellFormed s') :
    ProtocolInv s' :=
  protocolInv_step s op caller s' h
    ((stepResult_accepted_iff s op caller s' es).mp hacc).1 hscope hwf'

theorem protocolInvWithReceiptLedger_stepResult_accepted
    (s : State) (op : Op) (caller : Address) (s' : State) (es : List Event)
    (h : ProtocolInvWithReceiptLedger s)
    (hacc : stepResult s op caller = .accepted s' es)
    (hscope : SolvencyScopedOp op) (hwf' : WellFormed s') :
    ProtocolInvWithReceiptLedger s' :=
  protocolInvWithReceiptLedger_step s op caller s' h
    ((stepResult_accepted_iff s op caller s' es).mp hacc).1 hscope hwf'

/-- Restricted reachability: states obtainable from `default` by successful
transitions that (a) avoid the five solvency-excluded operations and (b) land in
a `WellFormed` state. The extra hypotheses are carried **in the relation** so
that `protocolInv_reachable` has no gap between what the preservation theorem
needs and what the reachability predicate provides (proof-map §6's warning).
This makes the relation strictly narrower than `RegistryReach`: it is a
design-scenario relation ("the protocol operated inside its solvency regime,
with a well-formed ledger throughout"), not a description of everything the
model — let alone a deployment — can do. -/
inductive ProtocolReach : State → Prop
  | initial : ProtocolReach (default : State)
  | next {s s' : State} {op : Op} {caller : Address} :
      ProtocolReach s →
      (es : List Event) →
      stepResult s op caller = .accepted s' es →
      SolvencyScopedOp op →
      WellFormed s' →
      ProtocolReach s'

/-- Every `ProtocolReach` state satisfies the composite invariant. Induction on
the trace: `protocolInv_default` at the base, `protocolInv_step` at each step,
consuming the exclusion and well-formedness hypotheses the `next` constructor
carries. Conditional exactly as `ProtocolReach` is restricted — this is a
global-design theorem about the solvency-scoped, well-formed regime, not an
unconditional safety guarantee about the deployed system. -/
theorem protocolInv_reachable (s : State) (h : ProtocolReach s) : ProtocolInv s := by
  induction h with
  | initial => exact protocolInv_default
  | next _ _ hacc hscope hwf' ih =>
      exact protocolInv_stepResult_accepted _ _ _ _ _ ih hacc hscope hwf'

theorem protocolInvWithReceiptLedger_reachable
    (s : State) (h : ProtocolReach s) : ProtocolInvWithReceiptLedger s := by
  induction h with
  | initial => exact protocolInvWithReceiptLedger_default
  | next _ _ hacc hscope hwf' ih =>
      exact protocolInvWithReceiptLedger_stepResult_accepted _ _ _ _ _ ih hacc hscope hwf'

/-! ## The ops-only layer: discharging the `WellFormed s'` assumption

The base relation above carries `WellFormed s'` as a hypothesis at every step.
That hypothesis splits into two conjuncts with different fates:

* the balance bound `∀ a, apxUSDBal a ≤ totalSupply_apxUSD` follows from the
  finite ledger identity `ProtocolInv` already carries and preserves
  (`apxUSDLedgerConsistent_balance_le` in `Ledger.lean`), so it never needed to
  be assumed once the ledger conjunct joined the composite;
* the price bound `redemptionValue ≤ ray` is written only by
  `updateRedemptionValue` (in scope; `catastrophicBackstop`, the other writer,
  is already excluded by `SolvencyScopedOp`), and the model — deliberately
  mirroring the deployed `newRate != 0`-only guard — lets the admin publish any
  nonzero value. No state-side fact can prevent that; the honest replacement is
  the *operation-side* condition `PriceBoundedOp`: every price update in the
  trace publishes at most par.

`ProtocolReachOps` therefore restricts operations only — the same five
solvency exclusions plus `PriceBoundedOp` — and carries **no post-state
hypothesis**. `protocolReachOps_inv_and_reach` shows every such state satisfies
the composite invariant *and* lies in the base `ProtocolReach` relation, so
this layer is a strengthening, not a fork: it proves the well-formedness the
base relation assumes, within the at-most-par regime.

Status (proof-map §11): all theorems in this section are reachable-scoped over
`ProtocolReachOps`; the side conditions are operation restrictions, not state
assumptions. -/

/-- Operation-side price discipline: if the operation is a price update, the
published value is at most par. Every non-update operation satisfies this
vacuously. This is a *regime* restriction (the admin stays at or below par),
not a model guard — the transition itself accepts any nonzero value, exactly
as the deployment does. -/
def PriceBoundedOp (op : Op) : Prop :=
  ∀ v, op = Op.updateRedemptionValue v → v ≤ ray

/-- The price bound is preserved by any successful in-scope step: a price
update is bounded by `PriceBoundedOp`, and every other operation (except the
already-excluded `catastrophicBackstop`) leaves `redemptionValue` unchanged
(`redemptionValue_frame`). -/
theorem redemptionValue_le_ray_step
    (s : State) (op : Op) (caller : Address) (s' : State)
    (hstep : step s op caller = some s') (hpre : s.redemptionValue ≤ ray)
    (hprice : PriceBoundedOp op) (hnb : op ≠ Op.catastrophicBackstop) :
    s'.redemptionValue ≤ ray := by
  by_cases hupd : ∃ v, op = Op.updateRedemptionValue v
  · obtain ⟨v, rfl⟩ := hupd
    obtain ⟨-, -, hs'⟩ := step_updateRedemptionValue_exact s v caller s' hstep
    rw [hs']
    exact hprice v rfl
  · have hframe := redemptionValue_frame s op caller s' hstep
      (fun v hv => hupd ⟨v, hv⟩) hnb
    rw [hframe]
    exact hpre

/-- Post-state well-formedness is *derivable* — not assumed — for any
successful step out of a `ProtocolInv` state, given the solvency scope and the
price discipline. The balance half comes from the preserved finite ledger
identity; the price half from `redemptionValue_le_ray_step`. -/
theorem wellFormed_step_of_inv
    (s : State) (op : Op) (caller : Address) (s' : State)
    (h : ProtocolInv s) (hstep : step s op caller = some s')
    (hscope : SolvencyScopedOp op) (hprice : PriceBoundedOp op) :
    WellFormed s' := by
  have hled' : ApxUSDLedgerConsistent s' :=
    apxUSDLedgerConsistent_step s s' op caller h.2.2.2.1 hstep
  refine ⟨apxUSDLedgerConsistent_balance_le s' hled', ?_⟩
  exact redemptionValue_le_ray_step s op caller s' hstep h.2.2.1.2 hprice
    hscope.2.2.2.1

/-- Preservation with operation-side hypotheses only: no `WellFormed s'`
assumption. -/
theorem protocolInv_step_ops
    (s : State) (op : Op) (caller : Address) (s' : State)
    (h : ProtocolInv s) (hstep : step s op caller = some s')
    (hscope : SolvencyScopedOp op) (hprice : PriceBoundedOp op) :
    ProtocolInv s' :=
  protocolInv_step s op caller s' h hstep hscope
    (wellFormed_step_of_inv s op caller s' h hstep hscope hprice)

/-- `protocolInv_step_ops` at the accepted-`StepResult` boundary. -/
theorem protocolInv_stepResult_accepted_ops
    (s : State) (op : Op) (caller : Address) (s' : State) (es : List Event)
    (h : ProtocolInv s)
    (hacc : stepResult s op caller = .accepted s' es)
    (hscope : SolvencyScopedOp op) (hprice : PriceBoundedOp op) :
    ProtocolInv s' :=
  protocolInv_step_ops s op caller s' h
    ((stepResult_accepted_iff s op caller s' es).mp hacc).1 hscope hprice

/-- Reachability restricted by operations alone: the five solvency exclusions
plus the at-most-par price discipline. Unlike `ProtocolReach`, no constructor
demands anything of the *post-state* — whether a state belongs to the relation
is decided entirely by the trace of accepted operations that produced it. -/
inductive ProtocolReachOps : State → Prop
  | initial : ProtocolReachOps (default : State)
  | next {s s' : State} {op : Op} {caller : Address} :
      ProtocolReachOps s →
      (es : List Event) →
      stepResult s op caller = .accepted s' es →
      SolvencyScopedOp op →
      PriceBoundedOp op →
      ProtocolReachOps s'

/-- The ops-only relation both satisfies the composite invariant and embeds
into the base `ProtocolReach` relation: the invariant supplies, at every step,
exactly the `WellFormed` fact the base constructor demands. One simultaneous
induction proves both, because each step's embedding needs that step's
invariant. -/
theorem protocolReachOps_inv_and_reach (s : State) (h : ProtocolReachOps s) :
    ProtocolInv s ∧ ProtocolReach s := by
  induction h with
  | initial => exact ⟨protocolInv_default, ProtocolReach.initial⟩
  | next _ es hacc hscope hprice ih =>
      have hinv' := protocolInv_stepResult_accepted_ops _ _ _ _ _ ih.1 hacc
        hscope hprice
      exact ⟨hinv', ProtocolReach.next ih.2 es hacc hscope hinv'.2.2.1⟩

/-- Every ops-only reachable state satisfies the composite invariant — with
no well-formedness assumption anywhere in the statement. -/
theorem protocolInv_reachableOps (s : State) (h : ProtocolReachOps s) :
    ProtocolInv s :=
  (protocolReachOps_inv_and_reach s h).1

/-- The ops-only relation is contained in the base relation: the derived
invariant discharges the `WellFormed` obligation the base constructor carries. -/
theorem protocolReachOps_subset (s : State) (h : ProtocolReachOps s) :
    ProtocolReach s :=
  (protocolReachOps_inv_and_reach s h).2

/-- The receipt-aware composite over the ops-only relation, via the embedding. -/
theorem protocolInvWithReceiptLedger_reachableOps (s : State)
    (h : ProtocolReachOps s) : ProtocolInvWithReceiptLedger s :=
  protocolInvWithReceiptLedger_reachable s (protocolReachOps_subset s h)

end Apyx
