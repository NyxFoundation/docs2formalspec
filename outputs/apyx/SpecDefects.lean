import D2fsSpecs.Apyx

/-! # Spec-level defect demonstrations (`docs/07-spec-defects.md`)

Machine-checked confirmations of **specification-level defects** — internal contradictions
between the RFC 2119 requirements themselves, as opposed to model-fidelity gaps or
implementation bugs. Unlike the requirement-conformance theorems in `Apyx.lean` (which prove
`model ⊨ requirement`, and so treat the specification as ground truth and can never find the
spec *wrong*), the theorems here prove the *requirement set itself* is inconsistent: they are
the "fourth activity" of §`docs/07`, run against the spec rather than assuming it.

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

/-- **Confirmed spec defect (docs/07 candidate 1): `buffer-non-decreasing` contradicts
`catastrophic-backstop`.**

`buffer-non-decreasing` states, *unconditionally*, that the overcollateralization buffer
"MUST NOT decrease" (it "MAY increase … over time"). `catastrophic-backstop` mandates that,
on a catastrophic event, the system "set Redemption Value equal to Total Collateral Value and
… distribute the entire reserve, including the buffer, pro-rata to remaining holders" — i.e.
drive the buffer to zero. The two obligations are jointly unsatisfiable in any catastrophic
scenario reached from a positive-buffer state.

The witness makes this concrete: a state with a strictly positive buffer on which the
mandated `catastrophicBackstop` step — whose own postcondition `redemptionValue =
totalCollateralValue` holds on the result — *strictly decreases* the buffer, violating
`buffer-non-decreasing`. No system can satisfy both requirements as written; one of them must
carry an explicit catastrophic-case exception that the specification does not state.

Corroboration inside the model itself: `Apyx.req_buffer_non_decreasing` had to be scoped to
the routine-redemption operations (`redeemApxUSD` / `requestUnlock` / `flexibleRequestUnlock`
/ `executeRFQRedemption`) — it is *false* for `catastrophicBackstop`, exactly the exclusion
this theorem forces, and one the natural-language requirement never authorizes. -/
theorem spec_defect_buffer_nondecrease_vs_catastrophic :
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
