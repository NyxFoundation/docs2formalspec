import D2fsSpecs.Registry
import D2fsSpecs.Safety
import D2fsSpecs.Ledger

/-!
# Conditional composite invariant layer

`docs/11-apyx-proof-map.md` §6 asks for a composite `Inv` with an initialization
theorem, a per-step preservation theorem, and a reachability predicate built from
the *same* transition restrictions the preservation theorem uses. This module
supplies exactly that shape for the facts the development actually carries:

~~~text
ProtocolInv s := RegistryWellIndexed s ∧ Solvent s ∧ WellFormed s ∧
  ApxUSDLedgerConsistent s
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
* **The aggregate facts do not imply the finite ledger identity.** The ledger is
  a bare `Address → Nat`, so `ApxUSDLedgerConsistent` is carried as a separate
  conjunct and preserved by the writer program in `Ledger.lean`; it is not
  derived from `WellFormed`/`Solvent`. The witness in that module records this
  model expressiveness gap.
* **`WellFormed s'` is still an explicit transition assumption.**
  `protocolInv_step` takes the post-state's well-formedness as a hypothesis
  rather than proving it, and `ProtocolReach.next` carries the same hypothesis
  so that `protocolInv_reachable` closes the §6 loop *for this restricted
  relation* without a gap between the preservation theorem and the reachability
  predicate. The ledger conjunct no longer needs this assumption because its
  successful-step theorem is universal for the current `Op` datatype.

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
finite ledger identity. Conditional —
see the module docstring for what each conjunct does and does not claim. -/
def ProtocolInv (s : State) : Prop :=
  RegistryWellIndexed s ∧ Solvent s ∧ WellFormed s ∧ ApxUSDLedgerConsistent s

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
Everything is zero, so solvency and well-formedness are trivial; the registry
part is `registryWellIndexed_default`. -/
theorem protocolInv_default : ProtocolInv (default : State) := by
  refine ⟨registryWellIndexed_default, Nat.zero_le _, ?_,
    apxUSDLedgerConsistent_default⟩
  exact ⟨(fun _ => Nat.zero_le _), Nat.zero_le _⟩

/-- Conditional preservation: a successful step preserves `ProtocolInv`, given
(1) the five solvency exclusions on the operation and (2) `WellFormed` at the
**post**-state, supplied as an explicit hypothesis. The registry conjunct is
unconditional (`registryWellIndexed_step`); the solvency conjunct is
`solvency_step` under its documented exclusions; the well-formedness conjunct
cannot be derived from the aggregate ledger and is therefore assumed, not
proved; the finite ledger conjunct is supplied by
`apxUSDLedgerConsistent_step`. -/
theorem protocolInv_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h : ProtocolInv s) (hstep : step s op caller = some s')
    (hscope : SolvencyScopedOp op) (hwf' : WellFormed s') :
    ProtocolInv s' :=
  ⟨registryWellIndexed_step s op caller s' h.1 hstep,
   solvency_step s op caller s' hstep h.2.1 h.2.2.1
     hscope.1 hscope.2.1 hscope.2.2.1 hscope.2.2.2.1 hscope.2.2.2.2,
   hwf',
   apxUSDLedgerConsistent_step s s' op caller h.2.2.2 hstep⟩

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
      step s op caller = some s' →
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
  | next _ hstep hscope hwf' ih => exact protocolInv_step _ _ _ _ ih hstep hscope hwf'

end Apyx
