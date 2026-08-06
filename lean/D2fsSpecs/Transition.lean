import D2fsSpecs.Apyx
import D2fsSpecs.Registry

/-!
# Explicit transition result (honest wrapper over `step`)

`docs/11-apyx-proof-map.md` §4 asks for a transition result that represents both
success and failure explicitly:

~~~text
inductive StepResult
  | reverted (reason : RevertReason)
  | accepted (state : State) (events : List Event)
~~~

**That exact shape cannot be represented faithfully without a model change.** The
current model's transition function is `step : State → Op → Address → Option State`:

* A rejected call returns `none`. The model does not record *why* it was rejected —
  the guard that failed is not reified anywhere — so there is no `RevertReason` to
  put in the `reverted` constructor. Inventing one here (e.g. re-running the guards
  in a parallel decision procedure) would create a second, unverified copy of the
  transition semantics whose agreement with `step` would itself need proof, and any
  divergence would silently misattribute revert causes.
* An accepted call returns only the successor state. Events are embedded in the
  state (`State.eventLog`), and not every accepting branch of `step` appends to it,
  so a per-step `List Event` delta is not derivable as a *specified* artifact of the
  transition — it would be reverse-engineered from state diffs, not modeled.

This module therefore defines only the **sound subset** of the proof-map shape: a
`StepResult` that distinguishes `reverted` from `accepted`, defined *on top of* the
existing `step` (no protocol semantics are touched), together with the equivalence
lemmas that make the wrapper transparent and the theorem that a reverted result
carries no successor state.

**Honest-boundary caveats, stated once and meant literally.**

* `StepResult.reverted` carries **no reason**. Exact revert reasons require a model
  change: `step` would have to return the failed guard (e.g.
  `Except RevertReason State`), and each `none` branch would need to be re-derived
  from the specification. Until then, no theorem in this development can distinguish
  "rejected because paused" from "rejected because of insufficient balance".
* `StepResult.accepted` carries **no event list**. Per-step event deltas require a
  model change in which `step` returns the emitted events as an output rather than
  folding some of them into `State.eventLog`.
* Consequently this wrapper is **not implementation fidelity**: it cannot express
  the proof-map transition contract's clause "reverted result … has an allowed
  reason", nor functional-correctness claims about emitted events. Those remain
  visible assurance gaps (proof-map §14), to be closed by a future model change,
  not by this file.
* The proof-map clause "a reverted result preserves state" is representable here
  only as *absence*: in this model a rejected call produces no post-state at all
  (`step … = none`), so there is no intermediate state whose equality with the
  pre-state could even be stated. A partial-state-then-revert behavior of an
  implementation is out of scope, exactly as already noted for `RegistryReach` in
  `Registry.lean`.

Status (proof-map §11): every theorem below is **model-local** — definitional
unfolding of the wrapper, plus two bridges into `Registry.lean`'s reachable-scope
results.
-/

namespace Apyx

/-- Explicit transition outcome. The sound subset of the proof-map §4 shape:
`reverted` carries no reason and `accepted` carries no event list, because the
underlying `step` models neither (see the module docstring). -/
inductive StepResult
  | reverted
  | accepted (s' : State)

/-- The successor state a result carries: `none` for a revert. By construction a
`reverted` result *cannot* carry a state — this projection makes that structural
fact quotable as an equation. -/
def StepResult.state? : StepResult → Option State
  | .reverted => none
  | .accepted s' => some s'

/-- The public transition, presented with an explicit outcome. Defined by pattern
matching on the existing `step`; it introduces no new semantics, and the lemmas
below make the round trip exact. -/
def stepResult (s : State) (op : Op) (caller : Address) : StepResult :=
  match step s op caller with
  | none => .reverted
  | some s' => .accepted s'

/-- Equivalence, `none` direction: the wrapper reverts exactly when `step` rejects. -/
theorem stepResult_reverted_iff (s : State) (op : Op) (caller : Address) :
    stepResult s op caller = .reverted ↔ step s op caller = none := by
  unfold stepResult
  cases h : step s op caller <;> simp

/-- Equivalence, `some` direction: the wrapper accepts with successor `s'` exactly
when `step` succeeds with `s'`. -/
theorem stepResult_accepted_iff (s : State) (op : Op) (caller : Address) (s' : State) :
    stepResult s op caller = .accepted s' ↔ step s op caller = some s' := by
  unfold stepResult
  cases h : step s op caller <;> simp

/-- Round trip: projecting the successor state out of the wrapper recovers `step`
exactly. This is the sense in which `stepResult` adds no semantics. -/
theorem stepResult_state? (s : State) (op : Op) (caller : Address) :
    (stepResult s op caller).state? = step s op caller := by
  unfold stepResult
  cases h : step s op caller <;> rfl

/-- Totality of the case split: every call either reverts or accepts with some
successor state. -/
theorem stepResult_total (s : State) (op : Op) (caller : Address) :
    stepResult s op caller = .reverted ∨ ∃ s', stepResult s op caller = .accepted s' := by
  unfold stepResult
  cases h : step s op caller <;> simp

/-- **A reverted result carries no successor state**, projection form: the
`state?` of a reverted call is `none`. -/
theorem stepResult_reverted_no_state (s : State) (op : Op) (caller : Address)
    (h : stepResult s op caller = .reverted) :
    (stepResult s op caller).state? = none := by
  simp [h, StepResult.state?]

/-- **A reverted result carries no successor state**, constructor form: a call
that reverted did not accept, for any candidate successor. -/
theorem stepResult_not_accepted_of_reverted (s : State) (op : Op) (caller : Address)
    (h : stepResult s op caller = .reverted) (s' : State) :
    stepResult s op caller ≠ .accepted s' := by
  rw [h]
  exact fun hcontra => StepResult.noConfusion hcontra

/-- Bridge into `Registry.lean`: an *accepted* transition preserves the registry
invariants. Pure repackaging of `registryWellIndexed_step` through the wrapper —
registry-scoped, exactly as caveated there. -/
theorem registryWellIndexed_stepResult_accepted (s : State) (op : Op) (caller : Address)
    (s' : State) (h : RegistryWellIndexed s)
    (hacc : stepResult s op caller = .accepted s') :
    RegistryWellIndexed s' :=
  registryWellIndexed_step s op caller s' h
    ((stepResult_accepted_iff s op caller s').mp hacc)

/-- Bridge into `Registry.lean`'s reachability: registry-scoped reachability
advances along *accepted* results and only along them — the wrapper makes the
proof-map's "Reach is built from successful transitions" reading literal. -/
theorem registryReach_stepResult_accepted {s s' : State} {op : Op} {caller : Address}
    (h : RegistryReach s) (hacc : stepResult s op caller = .accepted s') :
    RegistryReach s' :=
  RegistryReach.next h ((stepResult_accepted_iff s op caller s').mp hacc)

end Apyx
