/-!
# Blast-radius theorem skeleton — TEMPLATE, NOT COMPILED

Fill in every `‹...›` placeholder from the Step-0 profile in this directory's README, using
`outputs/apyx/BlastRadius.lean` as the worked reference. Place the instantiated file in the
app's output directory (`outputs/‹app›/BlastRadius.lean`), symlinked from `lean/D2fsSpecs/`, and
add `import D2fsSpecs.BlastRadius` to `lean/D2fsSpecs.lean`.

This file is a reference skeleton: it intentionally does NOT compile as-is and is not part of the
lake build. Delete the placeholders and the "TEMPLATE" markers once instantiated.
-/

import D2fsSpecs.‹AppModule›   -- the app's model (State, Op, step)

namespace ‹AppNamespace›

/-! ## Infrastructure (copy near-verbatim across apps) -/

/-- Execute a `(op, caller)` trace in order; a reverting op leaves the state unchanged. -/
def execTrace (s : State) : List (Op × Address) → State
  | []          => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-- One predicate per privileged role: the `Op` cases `step` gates on `caller = ‹role›`. -/
def ‹Role›Op (op : Op) : Prop := ‹op = Op.foo ∨ ∃ x, op = Op.bar x ∨ ...›

/-! ## Base-model theorems (properties of the ACTUAL protocol) -/

/-- T1–T3 exact-effect frame: a successful ‹role›-gated op equals the pre-state with only its
    named non-value fields overridden. Proof: `intro/cases` on the op, `simp [step, ...]`. -/
theorem ‹role›_frame (s : State) (op : Op) (c : Address) (s' : State)
    (hrole : ‹Role›Op op) (hstep : step s op c = some s') :
    ‹s'.valueField₁ = s.valueField₁ ∧ ... ∧ s'.valueFieldₙ = s.valueFieldₙ› := by
  ‹rcases hrole ...; each case: simp [step] at hstep ⊢›

/-- T1–T3 trace form: an all-‹role› attack trace moves only the role's own non-value fields.
    Proof: induction on the trace, applying `‹role›_frame` at each accepted step. -/
theorem ‹role›_trace_blast_radius (s : State) (σ : List (Op × Address))
    (hall : ∀ p ∈ σ, ‹Role›Op p.1) :
    ‹(execTrace s σ).valueField = s.valueField ∧ ...› := by
  ‹induction σ ...›

/-- T4 non-custodial (per value field): a single-step decrease of `a`'s field implies `a`
    participated. Document every carve-out (e.g. a non-caller victim of an RFQ-style op). -/
theorem no_role_debits_‹field› (s : State) (op : Op) (c : Address) (s' : State)
    (hstep : step s op c = some s') (a : Address) (hlt : s'.‹field› a < s.‹field› a) :
    a = c ‹∨ <documented carve-out>› := by
  ‹cases op <;> simp [step] at hstep ⊢ <;> omega/…›

/-- T4 headline: even under total key compromise, a passive user (never signs, never a
    debit-site's non-caller target) loses none of their value. -/
theorem user_assets_immune_to_total_key_compromise (s : State) (σ : List (Op × Address)) (a : Address)
    (h_never_signs : ∀ p ∈ σ, p.2 ≠ a) ‹(carve-out hyps)› :
    ‹∀ field, s.field a ≤ (execTrace s σ).field a› := by
  ‹induction σ, apply the no_role_debits_* lemmas + omega›

/-- Active no-extraction: no `step` case credits a value field without backing (equal payment or
    settlement of the recipient's own pre-existing position). The in-scope-safety complement of T4. -/
theorem ‹token›_credit_is_backed (s : State) (op : Op) (c : Address) (s' : State)
    (hstep : step s op c = some s') (a : Address) (hgt : s.‹field› a < s'.‹field› a) :
    ‹(paid-mint case) ∨ (own-position-settlement case)› := by
  ‹cases op <;> ...›

/-- T6 no-cap finding (only if the model has an uncapped price/param an op can set): the payout
    formula plus a witness showing it exceeds any bound — a FINDING that motivates the wrappers. -/
theorem ‹payout›_has_no_cap : ∀ N : Nat, ∃ s s' amount c,
    step s (‹payoutOp› amount) c = some s' ∧ ‹N ≤ s'.‹field› c› := by
  ‹intro N; exact ⟨witness with ‹param› := N * ..., ...⟩›

/-- base_model_has_no_‹defense›: prove the ABSENCE of a defense as a negative finding, e.g. a
    privileged op takes effect in the same step (no escape window). -/
theorem base_model_has_no_‹defense› : ∃ s s', step s ‹privOp› s.admin = some s' ∧
    ‹s'.param ≠ s.param ∧ s'.now = s.now› := ‹⟨witness, ...⟩›

/-! ## Design theorems (what a MISSING defense would guarantee — recommendations, not current facts) -/

/-- T7 rate-limit wrapper. Layers an epoch-outflow meter over the base `step`; do NOT modify State. -/
structure RLState where
  base : State
  epoch : Nat
  spentThisEpoch : Nat
  cap : Nat

inductive RLOp | baseOp (op : Op) (c : Address) | advanceEpoch

def step2 (rs : RLState) : RLOp → Option RLState := ‹run step; charge reserve outflow via the
  reserve-outflow characterization lemma; revert if spentThisEpoch + d > cap; advanceEpoch resets›

/-- T7: cumulative reserve outflow is at most linear in elapsed epochs — "damage ≤ linear in time". -/
theorem rate_limit_linear_bound (rs : RLState) (τ : List RLOp) ‹(hspent : rs.spentThisEpoch ≤ rs.cap)› :
    ‹rs.base.reserve - (execTrace2 rs τ).base.reserve ≤ rs.cap * (countEpochs τ + 1)› := by
  ‹induction with the invariant spentThisEpoch ≤ cap›

/-- T8 timelock wrapper. Pending-op queue with effective times; base model has none (proved above). -/
structure TLState where
  base : State
  now : Nat
  pending : List (Op × Address × Nat)   -- op + caller + effective time
  delay : Nat

/-- T8: a queued privileged op cannot take effect until `delay` ticks after it was queued —
    a guaranteed user exit window. -/
theorem timelock_escape_guarantee ‹(...)› : ‹any successful execute of an entry queued at t0
    requires now ≥ t0 + delay› := by ‹induction maintaining eff = enqueueTime + delay›

end ‹AppNamespace›
