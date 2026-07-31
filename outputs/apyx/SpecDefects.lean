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
value. The governance `emergencyFlag` is pre-set, since the document-faithful backstop only
fires once the flag is already up (raised by the stress pathway `handleStressEvent`; see the
guard on `step … Op.catastrophicBackstop`). Everything else is at defaults; the buffer is
`totalCollateralValue - redemptionTotal = 1 - 0 = 1`. -/
private def bufWitness : State :=
  { (default : State) with
      emergencyFlag := true,
      totalSupply_apxUSD := ray, totalCollateralValue := 1, redemptionValue := 0 }

/-- The post-state of the mandated `catastrophicBackstop` step on `bufWitness`: exactly the
model's effect — the per-unit `redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD`
(on `bufWitness`, TCV = 1, supply = ray, this evaluates to `1`), the pro-rata reserve credit, and
the recorded `overcollateralizationBuffer` field driven to `0`. -/
private def bufWitness' : State :=
  { bufWitness with
      redemptionValue := bufWitness.totalCollateralValue * ray / bufWitness.totalSupply_apxUSD,
      usdcBal := fun a =>
        bufWitness.usdcBal a + (bufWitness.usdcReserve * bufWitness.apxUSDBal a) / bufWitness.totalSupply_apxUSD,
      usdcReserve := 0,
      overcollateralizationBuffer := 0 }

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
  · -- the step: caller = admin and the emergency flag is up, so it succeeds with the
    -- per-unit redemptionValue and the buffer-distributing reserve payout
    simp [step, bufWitness']
    show bufWitness.emergencyFlag = true
    rfl
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

**The collateral is deliberately non-zero.** An earlier version of this witness set
`totalCollateralValue = 0`, which made the finding much weaker than it read: in a state with no
collateral at all, paying zero for a burn is arithmetically *correct*, not a floor violation. Here
the basket holds 1000 against a supply of 100, so the redeemer is burning a token that is backed
1000/100 = 10× over and receiving nothing for it. That is the case a floor would catch.

The redeem guards' fields are set explicitly so evaluation is closed, and note which ones the
path needs: `apxUSDMarketPrice < ray` (the arbitrage redeem is only open **below peg**) and the
buffer-non-decreasing check, which passes because a zero price makes the derived buffer
insensitive to the burn. -/
private def floorWitness : State :=
  { (default : State) with
      -- set explicitly: `default` is not a reliable source for fields a
      -- witness depends on (`Regression.lean` §R11)
      denylist := fun _ => false,
      globalPause := false, whitelist := fun _ => true,
      apxUSDBal := fun a => if a = 0 then 100 else 0,
      redemptionValue := 0, apxUSDMarketPrice := 0, usdcReserve := 0,
      totalCollateralValue := 1000, totalSupply_apxUSD := 100 }

/-- **`redemption_has_no_floor`** (docs/08 §B.3 / templates/invariants `G`): the redemption path
has **no lower floor** on the redemption price. In a state whose `redemptionValue` is 0 (reachable
via `catastrophicBackstop` from a zero-collateral state), a whitelisted holder can still
successfully `redeemApxUSD` — the guards do not forbid it, the arbitrage path being open below
peg — yet the USDC paid for `amount` apxUSD is `amount · redemptionValue / ray = 0`: the redeemer
burns their apxUSD for **zero**, and the witness now pins that this happens while the collateral
basket still covers the supply ten times over. This is the
lower-bound companion to `BlastRadius.redeem_payout_has_no_cap` (no *upper* bound) and generalizes
`admin_rfq_coalition_drains` (same via the RFQ path) to the ordinary redeem entry point. Fix: a
redemption-price floor / clamp (README §5). -/
theorem redemption_has_no_floor :
    ∃ (s : State) (caller amount : Nat),
      0 < amount ∧ s.redemptionValue = 0 ∧ s.whitelist caller = true ∧
      amount ≤ s.apxUSDBal caller ∧
      -- the burn happens against a **backed** supply: the basket covers it ten times over
      0 < s.totalCollateralValue ∧ s.totalSupply_apxUSD ≤ s.totalCollateralValue ∧
      (∃ s', step s (Op.redeemApxUSD amount) caller = some s') ∧
      amount * s.redemptionValue / ray = 0 := by
  have hray : (0 : Nat) < ray := Nat.pow_pos (by decide)
  refine ⟨floorWitness, 0, 100, by decide, rfl, rfl, by simp [floorWitness], by decide, by decide,
    ?_, by simp [floorWitness]⟩
  rcases h : step floorWitness (Op.redeemApxUSD 100) 0 with _ | s'
  · exact absurd h (by simp [step, floorWitness, overcollateralizationBuffer, burnApxUSD,
      Nat.not_le.mpr hray])
  · exact ⟨s', rfl⟩

end Apyx
