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

This module defines that exact shape as a **transparent wrapper** over the
existing `step : State → Op → Address → Option State`. No protocol semantics are
touched, duplicated, or re-derived; the wrapper is definitionally a re-packaging
of `step`'s result, and the round-trip lemmas below make that exact. Because the
underlying model exposes less than the proof-map shape asks for, the two extra
payloads are populated *honestly* rather than faithfully:

* **Revert reasons.** A rejected call returns `none`; the model does not record
  *which* guard failed. Reifying reasons here (e.g. by re-running the guards in a
  parallel decision procedure) would create a second, unverified copy of the
  transition semantics whose agreement with `step` would itself need proof, and
  any divergence would silently misattribute revert causes. `RevertReason`
  therefore has the single constructor `modelUnknown`, and every reverted result
  carries it (`RevertReason.eq_modelUnknown`). **No theorem in this development
  can distinguish** "rejected because paused" from "rejected because of
  insufficient balance" until `step` itself returns the failed guard (e.g.
  `Except RevertReason State`).
* **Events.** `step` folds emitted events into the cumulative `State.eventLog`
  (newest first, via `emitEvent`) instead of returning them as an output. The
  wrapper's `accepted` payload is `eventDelta pre post`: the prefix of the
  successor's log that extends beyond the pre-state's log *by length*. This is a
  **syntactic diff of the cumulative log, not a modeled artifact of the
  transition** — it is exactly the emitted events whenever the accepting branch
  only prepends to the log (which every current branch does), but that adequacy
  is *not proved here* and **no event-fidelity claim is made**. The theorems
  below establish only (a) the state round-trip, (b) that the payload is
  literally `eventDelta`, and (c) model-free list facts about `eventDelta`
  (`eventDelta_self`, `eventDelta_emit`, `eventDelta_append_drop`).

**Honest-boundary caveats, stated once and meant literally.**

* This wrapper is **not implementation fidelity**: it cannot express the
  proof-map transition contract's clause "reverted result … has an allowed
  reason", nor functional-correctness claims about emitted events. Those remain
  visible assurance gaps (proof-map §14), to be closed by a future model change
  (`step` returning `Except RevertReason (State × List Event)`), not by this
  file.
* The proof-map clause "a reverted result preserves state" is representable here
  only as *absence*: in this model a rejected call produces no post-state at all
  (`step … = none`), so there is no intermediate state whose equality with the
  pre-state could even be stated (`stepResult_reverted_no_state`). A
  partial-state-then-revert behavior of an implementation is out of scope,
  exactly as already noted for `RegistryReach` in `Registry.lean`.

Status (proof-map §11): every theorem below is **model-local** — definitional
unfolding of the wrapper plus elementary list arithmetic, and two bridges into
`Registry.lean`'s reachable-scope results.
-/

namespace Apyx

/-- An emitted event, matching the entries of `State.eventLog`: an event name
together with its (already ABI-flattened) numeric arguments. -/
abbrev Event : Type := String × List Nat

/-- Why a call reverted. **Honest about the current model**: `step` returns only
`Option State`, so the failed guard is not observable and the only representable
reason is `modelUnknown`. Distinguishable reasons require a model change (see the
module docstring). -/
inductive RevertReason
  /-- The model rejected the call (`step … = none`) but does not expose which
  guard failed. -/
  | modelUnknown

/-- The current model admits no other reason: this quotes, as a theorem, the fact
that the wrapper never claims to know *why* a call reverted. -/
theorem RevertReason.eq_modelUnknown : ∀ r : RevertReason, r = .modelUnknown
  | .modelUnknown => rfl

/-- Explicit transition outcome, in the proof-map §4 shape. The payloads are
honest rather than faithful: `reason` is always `modelUnknown`, and `events` is
the cumulative-log prefix diff `eventDelta` (see the module docstring). -/
inductive StepResult
  | reverted (reason : RevertReason)
  | accepted (state : State) (events : List Event)

/-- The successor state a result carries: `none` for a revert. By construction a
`reverted` result *cannot* carry a state — this projection makes that structural
fact quotable as an equation. -/
def StepResult.state? : StepResult → Option State
  | .reverted _ => none
  | .accepted s' _ => some s'

/-- The events a result carries: `[]` for a revert, the `accepted` payload
otherwise. -/
def StepResult.events : StepResult → List Event
  | .reverted _ => []
  | .accepted _ es => es

/-- The event delta between a pre-state and its successor, read off the
cumulative `State.eventLog`: the newest-first prefix of the successor's log that
extends beyond the pre-state's log **by length**. This is a syntactic diff, not a
modeled output of `step` — it coincides with the emitted events whenever the
accepting branch only prepends to the log, but no such fidelity is claimed or
proved here (see the module docstring). -/
def eventDelta (pre post : State) : List Event :=
  post.eventLog.take (post.eventLog.length - pre.eventLog.length)

/-- A step that leaves the log alone has an empty delta (model-free list fact). -/
theorem eventDelta_of_eventLog_eq (pre post : State)
    (h : post.eventLog = pre.eventLog) : eventDelta pre post = [] := by
  unfold eventDelta
  rw [h, Nat.sub_self]
  rfl

/-- Degenerate case of `eventDelta_of_eventLog_eq`: the delta from a state to
itself is empty. -/
theorem eventDelta_self (s : State) : eventDelta s s = [] :=
  eventDelta_of_eventLog_eq s s rfl

/-- A step that emits exactly one event — i.e. whose successor log is one
`emitEvent`-style cons on the pre-state log — has exactly that singleton delta
(model-free list fact). -/
theorem eventDelta_emit (pre post : State) (name : String) (args : List Nat)
    (h : post.eventLog = (name, args) :: pre.eventLog) :
    eventDelta pre post = [(name, args)] := by
  unfold eventDelta
  have hlen : pre.eventLog.length + 1 - pre.eventLog.length = 1 := by omega
  rw [h, List.length_cons, hlen]
  rfl

/-- The delta is a prefix of the successor's cumulative log: appending the
untaken suffix recovers the whole log (model-free list fact). -/
theorem eventDelta_append_drop (pre post : State) :
    eventDelta pre post
        ++ post.eventLog.drop (post.eventLog.length - pre.eventLog.length)
      = post.eventLog :=
  List.take_append_drop _ _

/-- The public transition, presented with an explicit outcome. Defined by pattern
matching on the existing `step`; it introduces no new semantics — rejections are
tagged with the honest `modelUnknown` reason and acceptances carry the
`eventDelta` prefix diff — and the lemmas below make the state round trip exact. -/
def stepResult (s : State) (op : Op) (caller : Address) : StepResult :=
  match step s op caller with
  | none => .reverted .modelUnknown
  | some s' => .accepted s' (eventDelta s s')

/-- Equivalence, `none` direction: the wrapper reverts (with any reason — there
is only one) exactly when `step` rejects. -/
theorem stepResult_reverted_iff (s : State) (op : Op) (caller : Address)
    (r : RevertReason) :
    stepResult s op caller = .reverted r ↔ step s op caller = none := by
  cases r
  unfold stepResult
  cases h : step s op caller <;> simp

/-- Equivalence, `some` direction: the wrapper accepts with successor `s'` and
events `es` exactly when `step` succeeds with `s'` and `es` is the cumulative-log
prefix diff. Note the second conjunct is *definitional bookkeeping*, not event
fidelity — see `eventDelta`. -/
theorem stepResult_accepted_iff (s : State) (op : Op) (caller : Address)
    (s' : State) (es : List Event) :
    stepResult s op caller = .accepted s' es ↔
      step s op caller = some s' ∧ es = eventDelta s s' := by
  unfold stepResult
  cases h : step s op caller with
  | none => simp
  | some a =>
    constructor
    · intro hacc
      injection hacc with h1 h2
      subst h1
      exact ⟨rfl, h2.symm⟩
    · intro hboth
      cases hboth with
      | intro hs he =>
        injection hs with h1
        subst h1
        subst he
        rfl

/-- State-projection form of `stepResult_accepted_iff`: the wrapper accepts with
successor `s'` (for *some* event payload) exactly when `step` succeeds with `s'`. -/
theorem stepResult_accepted_state_iff (s : State) (op : Op) (caller : Address)
    (s' : State) :
    (∃ es, stepResult s op caller = .accepted s' es) ↔
      step s op caller = some s' := by
  constructor
  · intro hex
    cases hex with
    | intro es hacc =>
      exact ((stepResult_accepted_iff s op caller s' es).mp hacc).1
  · intro hstep
    exact ⟨eventDelta s s',
      (stepResult_accepted_iff s op caller s' (eventDelta s s')).mpr ⟨hstep, rfl⟩⟩

/-- Round trip: projecting the successor state out of the wrapper recovers `step`
exactly. This is the sense in which `stepResult` adds no semantics. -/
theorem stepResult_state? (s : State) (op : Op) (caller : Address) :
    (stepResult s op caller).state? = step s op caller := by
  unfold stepResult
  cases h : step s op caller <;> rfl

/-- Totality of the case split: every call either reverts (necessarily with the
model-unknown reason) or accepts with some successor state and event payload. -/
theorem stepResult_total (s : State) (op : Op) (caller : Address) :
    stepResult s op caller = .reverted .modelUnknown ∨
      ∃ s' es, stepResult s op caller = .accepted s' es := by
  unfold stepResult
  cases h : step s op caller with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, eventDelta s a, rfl⟩

/-- **A reverted result carries no successor state**, projection form: the
`state?` of a reverted call is `none`. -/
theorem stepResult_reverted_no_state (s : State) (op : Op) (caller : Address)
    (r : RevertReason) (h : stepResult s op caller = .reverted r) :
    (stepResult s op caller).state? = none := by
  rw [h]
  rfl

/-- A reverted result carries no events, projection form: the `events` of a
reverted call are `[]`. -/
theorem stepResult_reverted_no_events (s : State) (op : Op) (caller : Address)
    (r : RevertReason) (h : stepResult s op caller = .reverted r) :
    (stepResult s op caller).events = [] := by
  rw [h]
  rfl

/-- **A reverted result carries no successor state**, constructor form: a call
that reverted did not accept, for any candidate successor and event payload. -/
theorem stepResult_not_accepted_of_reverted (s : State) (op : Op) (caller : Address)
    (r : RevertReason) (h : stepResult s op caller = .reverted r)
    (s' : State) (es : List Event) :
    stepResult s op caller ≠ .accepted s' es := by
  rw [h]
  exact fun hcontra => StepResult.noConfusion hcontra

/-- The event payload of an accepted result is *literally* the cumulative-log
prefix diff — bookkeeping, not event fidelity (see `eventDelta`). -/
theorem stepResult_accepted_events (s : State) (op : Op) (caller : Address)
    (s' : State) (es : List Event)
    (h : stepResult s op caller = .accepted s' es) :
    es = eventDelta s s' :=
  ((stepResult_accepted_iff s op caller s' es).mp h).2

/-- Bridge into `Registry.lean`: an *accepted* transition preserves the registry
invariants. Pure repackaging of `registryWellIndexed_step` through the wrapper —
registry-scoped, exactly as caveated there. -/
theorem registryWellIndexed_stepResult_accepted (s : State) (op : Op) (caller : Address)
    (s' : State) (es : List Event) (h : RegistryWellIndexed s)
    (hacc : stepResult s op caller = .accepted s' es) :
    RegistryWellIndexed s' :=
  registryWellIndexed_step s op caller s' h
    ((stepResult_accepted_iff s op caller s' es).mp hacc).1

/-- Bridge into `Registry.lean`'s reachability: registry-scoped reachability
advances along *accepted* results and only along them — the wrapper makes the
proof-map's "Reach is built from successful transitions" reading literal. -/
theorem registryReach_stepResult_accepted {s s' : State} {op : Op} {caller : Address}
    {es : List Event} (h : RegistryReach s)
    (hacc : stepResult s op caller = .accepted s' es) :
    RegistryReach s' :=
  RegistryReach.next h ((stepResult_accepted_iff s op caller s' es).mp hacc).1

end Apyx
