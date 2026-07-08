import D2fsSpecs.Apyx

/-! # Spec-level defect demonstrations (`docs/07-spec-defects.md`)

Machine-checked confirmations that the RFC 2119 requirement set is internally inconsistent.
Unlike the requirement-conformance theorems in `Apyx.lean` (which prove `model ⊨ requirement`,
treating the specification as ground truth and so never able to find the spec *wrong*), the
theorem here proves the *requirement set itself* is inconsistent — the "fourth activity" of
§`docs/07`, run against the spec rather than assuming it.

**Important attribution (root cause is EXTRACTION, not the protocol).** The inconsistency below
is between two entries in the LLM-*extracted* `requirements.json`, and tracing it back to the
source documentation (`corpus.md`) shows the **source is consistent**: the docs scope buffer
preservation to *routine redemptions* and *stress events*, and treat the catastrophic backstop
(a terminal hack/wind-down event) as a separate mechanism that deliberately distributes the
buffer. The contradiction arises only because the extractor **over-generalized**
`buffer-non-decreasing` into an *unconditional* "MUST NOT decrease", dropping the "through
stress events" scope that is present in its own `source_quote`. So this is a **requirement-
extraction defect** (a defect in the tool's own output), not a flaw in Apyx's protocol or
documentation. It is kept because it is a genuine, machine-checked demonstration of the
spec-defect-search method — and a cautionary example of why every candidate must be traced to
the source before being reported (see `docs/07` §3).

This module is additive and leaves `Apyx.lean`/`BlastRadius.lean`/`Safety.lean` untouched. -/

namespace Apyx

/-- Witness state for the buffer/backstop contradiction: a positive overcollateralization
buffer, with `totalSupply_apxUSD = ray` so that the redemption total equals the redemption
value. Everything else is at defaults; the buffer is `totalCollateralValue - redemptionTotal
= 1 - 0 = 1`. -/
private def bufWitness : State :=
  { (default : State) with
      totalSupply_apxUSD := ray, totalCollateralValue := 1, redemptionValue := 0 }

/-- The post-state of the mandated `catastrophicBackstop` step on `bufWitness`: exactly the
model's effect (`redemptionValue := totalCollateralValue`, `emergencyFlag := true`). -/
private def bufWitness' : State :=
  { bufWitness with redemptionValue := bufWitness.totalCollateralValue, emergencyFlag := true }

/-- **Requirement-extraction defect (docs/07 candidate 1): the *extracted* requirements
`buffer-non-decreasing` and `catastrophic-backstop` are jointly unsatisfiable.**

As written in `requirements.json`, `buffer-non-decreasing` states *unconditionally* that the
overcollateralization buffer "MUST NOT decrease" (it "MAY increase … over time"), while
`catastrophic-backstop` mandates that, on a catastrophic event, the system "distribute the
entire reserve, including the buffer, pro-rata" — i.e. drive the buffer to zero. This theorem
proves the two are jointly unsatisfiable: a state with a strictly positive buffer on which the
mandated `catastrophicBackstop` step (its own postcondition `redemptionValue =
totalCollateralValue` holds on the result) *strictly decreases* the buffer.

**Root cause — extraction, not protocol (verified against the source).** The source
documentation (`corpus.md`) is *consistent*: it says the buffer "is **not** consumed during
**routine redemptions**" and "is preserved through **stress events**", and separately that "in
a **catastrophic scenario** — a devastating hack, wind-down, … — the entire reserve, buffer
included, is distributed." The catastrophic case is an explicit, separate terminal mechanism.
The `buffer-non-decreasing` requirement's own `source_quote` is the *stress-events* sentence —
but the extractor generalized it into an unconditional "MUST NOT decrease", dropping the scope.
So the contradiction is a defect in the tool's **extraction** (this repo's `requirements.json`),
not in Apyx's protocol or docs; the correctly-scoped `buffer-preservation` (routine) and
`buffer-growth-stress` (stress) entries already capture the source faithfully and are redundant
with this over-generalized one. Corroboration: `Apyx.req_buffer_non_decreasing` is itself scoped
to routine-redemption ops precisely because the unconditional reading is false. -/
theorem extracted_reqs_inconsistent_buffer_vs_catastrophic :
    ∃ (s s' : State),
      -- a reachable-shaped state with a strictly positive buffer
      0 < overcollateralizationBuffer s ∧
      -- the catastrophic-backstop step fires (admin-authorized, as its requirement demands)
      step s Op.catastrophicBackstop s.admin = some s' ∧
      -- catastrophic-backstop's own postcondition holds on the result
      s'.redemptionValue = s'.totalCollateralValue ∧
      -- yet the buffer STRICTLY decreased — a direct violation of `buffer-non-decreasing`
      overcollateralizationBuffer s' < overcollateralizationBuffer s := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  refine ⟨bufWitness, bufWitness', ?_, ?_, ?_, ?_⟩
  · -- buffer bufWitness = 1 - 0 = 1 > 0
    simp [overcollateralizationBuffer, bufWitness]
  · -- the step: caller = admin, so it succeeds with the mandated redemptionValue := TCV
    simp [step, bufWitness']
  · -- redemptionValue and totalCollateralValue coincide on the result
    rfl
  · -- buffer after = 0 (redemptionTotal = ray·1/ray = 1 = TCV), buffer before = 1
    have h1 : overcollateralizationBuffer bufWitness = 1 := by
      simp [overcollateralizationBuffer, bufWitness]
    have h2 : overcollateralizationBuffer bufWitness' = 0 := by
      have hrt : bufWitness'.totalSupply_apxUSD * bufWitness'.redemptionValue / ray = 1 := by
        show ray * 1 / ray = 1
        rw [Nat.mul_one, Nat.div_self hray]
      simp only [overcollateralizationBuffer]
      rw [hrt]
      simp [bufWitness', bufWitness]
    omega

end Apyx
