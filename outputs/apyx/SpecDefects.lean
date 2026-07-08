import D2fsSpecs.Apyx

/-! # Spec-consistency search (`docs/07-spec-defects.md`)

Results of the "fourth activity" of §`docs/07`: turning the lens on the RFC 2119 requirement
set itself and asking whether it is internally consistent, rather than proving `model ⊨
requirement` (which treats the spec as ground truth and can never find it *wrong*). Each
candidate from `docs/07` §3 is triaged against the **source documentation** (`corpus.md`,
implementation): a candidate confirmed as a genuine *source* defect stays here as a defect
witness; a candidate traced to an *extraction* artifact (D6 — the LLM dropping a scope/exception
present in the source) is **fixed at the source** (`requirements.json`/`SPEC.md`) and its theorem
kept as the conformance property it actually demonstrates.

**Candidate 1 — resolved as an extraction defect, source now fixed.** The apparent
`buffer-non-decreasing` vs `catastrophic-backstop` contradiction was traced to `corpus.md`,
which is consistent: it scopes buffer preservation to *routine redemptions* and *stress events*
and treats the catastrophic backstop (a terminal hack/wind-down) as a separate mechanism that
distributes the buffer. The extractor had over-generalized `buffer-non-decreasing` into an
unconditional "MUST NOT decrease". `requirements.json`/`SPEC.md` have been corrected to restore
the routine/stress scope with the explicit catastrophic exception, and the model's
`req_buffer_non_decreasing` (already scoped to routine ops) now matches. The theorem below is
retained as the machine-checked statement of that catastrophic *exception*: the mandated
backstop step distributes the entire buffer (drives it to zero), which is exactly what
`catastrophic-backstop` requires and what the corrected `buffer-non-decreasing` now excludes.

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
model's per-unit effect (`redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD`,
`emergencyFlag := true`). On `bufWitness` (TCV = 1, supply = ray) this evaluates to `1`. -/
private def bufWitness' : State :=
  { bufWitness with
      redemptionValue := bufWitness.totalCollateralValue * ray / bufWitness.totalSupply_apxUSD,
      emergencyFlag := true }

/-- **`req_catastrophic_backstop_distributes_buffer`** (docs/07 candidate 1, resolved): the
machine-checked *catastrophic exception* to buffer preservation. On a catastrophic backstop the
mandated step distributes the entire overcollateralization buffer — driving it to zero — which
is what `catastrophic-backstop` requires and what the corrected `buffer-non-decreasing`
(scoped to routine redemptions and stress events) explicitly excludes.

The witness exhibits a state with a strictly positive buffer on which the admin-authorized
`catastrophicBackstop` step, whose own postcondition `redemptionValue = totalCollateralValue`
holds on the result, *strictly decreases* the buffer. This originally surfaced as an apparent
requirement contradiction; tracing it to `corpus.md` showed the source is consistent and the
fault was an over-generalized extraction of `buffer-non-decreasing` (now corrected in
`requirements.json`/`SPEC.md`). The theorem is retained as the positive statement of the
exception, and it partially closes the "second clause of catastrophic-backstop not modeled"
gap noted in `README` §6.2 — the buffer-distribution effect (buffer → 0) is now proved, though
the per-holder pro-rata split remains outside the aggregate ledger's expressible scope. -/
theorem req_catastrophic_backstop_distributes_buffer :
    ∃ (s s' : State),
      -- a reachable-shaped state with a strictly positive buffer
      0 < overcollateralizationBuffer s ∧
      -- the catastrophic-backstop step fires (admin-authorized, as its requirement demands)
      step s Op.catastrophicBackstop s.admin = some s' ∧
      -- catastrophic-backstop's own (corrected, per-unit) postcondition holds on the result
      s'.redemptionValue = s.totalCollateralValue * ray / s.totalSupply_apxUSD ∧
      -- yet the buffer STRICTLY decreased — the catastrophic exception to `buffer-non-decreasing`
      overcollateralizationBuffer s' < overcollateralizationBuffer s := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  have hval : bufWitness.totalCollateralValue * ray / bufWitness.totalSupply_apxUSD = 1 := by
    show (1 : Nat) * ray / ray = 1; rw [Nat.one_mul, Nat.div_self hray]
  refine ⟨bufWitness, bufWitness', ?_, ?_, ?_, ?_⟩
  · -- buffer bufWitness = 1 - 0 = 1 > 0
    simp [overcollateralizationBuffer, bufWitness]
  · -- the step: caller = admin, so it succeeds with the per-unit redemptionValue
    simp [step, bufWitness']
  · -- the per-unit redemption value on the result
    rfl
  · -- buffer after = 0 (redemptionTotal = ray·(1)/ray = 1 = TCV), buffer before = 1
    have h1 : overcollateralizationBuffer bufWitness = 1 := by
      simp [overcollateralizationBuffer, bufWitness]
    have h2 : overcollateralizationBuffer bufWitness' = 0 := by
      have hrt : bufWitness'.totalSupply_apxUSD * bufWitness'.redemptionValue / ray = 1 := by
        show ray * (bufWitness.totalCollateralValue * ray / bufWitness.totalSupply_apxUSD) / ray = 1
        rw [hval, Nat.mul_one, Nat.div_self hray]
      simp only [overcollateralizationBuffer]
      rw [hrt]
      simp [bufWitness', bufWitness]
    omega

/-- Witness for the missing redemption-price **floor** (docs/08 pattern G, gap-witness).
The redeem guards' fields are set explicitly (all to plausible values) so evaluation is closed. -/
private def floorWitness : State :=
  { (default : State) with
      globalPause := false, whitelist := fun _ => true, apxUSDBal := fun _ => 1,
      redemptionValue := 0, apxUSDMarketPrice := 0, usdcReserve := 0,
      totalCollateralValue := 0, totalSupply_apxUSD := 1 }

/-- **`redemption_has_no_floor`** (docs/08 §B.3 / templates/invariants `G`): the redemption path
has **no lower floor** on the redemption price. In a state whose `redemptionValue` is 0 (reachable
via `catastrophicBackstop` from a zero-collateral state), a whitelisted holder can still
successfully `redeemApxUSD` — the guards do not forbid it — yet the USDC paid for `amount` apxUSD is
`amount · redemptionValue / ray = 0`: the redeemer burns their apxUSD for **zero**. This is the
lower-bound companion to `BlastRadius.redeem_payout_has_no_cap` (no *upper* bound) and generalizes
`admin_rfq_coalition_drains` (same via the RFQ path) to the ordinary redeem entry point. Fix: a
redemption-price floor / clamp (README §5). -/
theorem redemption_has_no_floor :
    ∃ (s : State) (caller amount : Nat),
      0 < amount ∧ s.redemptionValue = 0 ∧ s.whitelist caller = true ∧
      amount ≤ s.apxUSDBal caller ∧
      (∃ s', step s (Op.redeemApxUSD amount) caller = some s') ∧
      amount * s.redemptionValue / ray = 0 := by
  have hray : (0 : Nat) < ray := Nat.pow_pos (by decide)
  refine ⟨floorWitness, 0, 1, Nat.one_pos, rfl, rfl, by simp [floorWitness], ?_, by simp [floorWitness]⟩
  rcases h : step floorWitness (Op.redeemApxUSD 1) 0 with _ | s'
  · exact absurd h (by simp [step, floorWitness, overcollateralizationBuffer, Nat.not_le.mpr hray])
  · exact ⟨s', rfl⟩

end Apyx
