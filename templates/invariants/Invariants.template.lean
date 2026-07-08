/-!
# Design-safety invariant skeleton — TEMPLATE, NOT COMPILED

Fill in every `‹...›` placeholder from the Step-0 profile in this directory's README, using
`outputs/apyx/Safety.lean` (and `outputs/apyx/SpecDefects.lean` for the gap-witness) as the
worked reference. Place the instantiated file in the app's output directory
(`outputs/‹app›/Safety.lean`), symlinked from `lean/D2fsSpecs/`, and add the import to
`lean/D2fsSpecs.lean`.

This file is a reference skeleton: it intentionally does NOT compile as-is and is not part of
the lake build. Delete the placeholders and "TEMPLATE" markers once instantiated.

Each invariant is proved in two stages: (a) single-step, **exhaustive over the closed `Op`**,
and (b) trace-level by induction. The exhaustive `cases op` is the point: a balance-mutating
op that "forgets" to re-establish the invariant cannot compile — this is what structurally
closes the Euler-class "missing check on one path" flaw.
-/

import D2fsSpecs.‹AppModule›   -- the app's model (State, Op, step)

namespace ‹AppNamespace›

/-! ## Infrastructure (copy near-verbatim across apps) -/

/-- Revert-skip trace executor (shared with the blast-radius template). -/
def execTrace (s : State) : List (Op × Address) → State
  | []          => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-- Value of address `a`'s holdings priced at a fixed reference rate `R`. -/
def valueAt (R : Nat) (s : State) (a : Address) : Nat :=
  ‹s.valueField₁ a + convertAtRate (s.shareField a) R + s.valueFieldₙ a›

/-- Solvency predicate: outstanding claims never exceed backing. -/
def Solvent (s : State) : Prop := ‹claims s ≤ backing s›

/-- The ledger side-conditions the single-step solvency lemma needs and the aggregate model
    cannot re-derive; re-supplied at every trace prefix (be honest — do not manufacture it). -/
def WellFormed (s : State) : Prop := ‹(∀ a, s.balance a ≤ s.total) ∧ s.price ≤ par›

/-! ## I1 — Conservation / no-free-value (docs/08 pattern D) -/

/-- `a` holds nothing extractable. -/
def Penniless (a : Address) (s : State) : Prop := ‹s.valueField₁ a = 0 ∧ ...›

/-- Single step: a value-preserving op keeps `a` penniless unless it is a *paid* gift to `a`. -/
theorem penniless_step (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (a : Address) (h0 : Penniless a s)
    ‹(h_no_gift : op is not a paid credit directed at a)› : Penniless a s' := by
  ‹cases op <;> [each credit op: show every increase to `a` is backed by a burn/payment;
                 all others: simp, balances of a unchanged]›

/-- Trace: no operation sequence credits a penniless, un-gifted address (backbone: I1). -/
theorem no_free_value_trace (s : State) (σ : List (Op × Address)) (a : Address)
    (h0 : Penniless a s) ‹(h_no_gift : ∀ p ∈ σ, ¬ paid-gift to a)› :
    Penniless a (execTrace s σ) := by
  ‹induction σ generalizing s; apply penniless_step at the accepted head›

/-! ## I2 — Solvency (docs/08 pattern E — the #1 design flaw) -/

/-- Single step, **exhaustive over `Op`**: every non-excluded op preserves solvency. The
    `cases op` forces each balance-mutating op to re-establish it — a path that skips the
    check does not compile (this is the structural guarantee). -/
theorem solvency_step (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hs : Solvent s) (hwf : WellFormed s)
    ‹(h_excl : op ∉ {ops that legitimately consume the margin})› : Solvent s' := by
  ‹cases op <;> simp [step, ...] <;> omega  -- every branch must discharge›

/-- Trace: solvency preserved across any trace, WellFormed re-supplied per prefix. -/
theorem solvency_preserved (s : State) (σ : List (Op × Address)) (hs : Solvent s)
    (hwf : ∀ n, WellFormed (execTrace s (σ.take n)))
    ‹(h_excl : ∀ p ∈ σ, p.1 ∉ excluded)› : Solvent (execTrace s σ) := by
  ‹induction σ generalizing s; apply solvency_step at the accepted head›

/-! ## I3 — No-dilution / share-value monotone (docs/08 pattern B, Vault) -/

/-- A single accounted deposit by someone else never lowers a holder's redeemable value. -/
theorem no_dilution (s : State) (op : Op) (c a : Address) (s' : State)
    (h : step s op c = some s') ‹(h_bystander : a ≠ c)› :
    ‹redeemableValue s' a ≥ redeemableValue s a› := by
  ‹cases op; the share-minting op preserves per-share value; others leave a's shares fixed›
-- Live-rate trace closure is a distinct, hard arithmetic problem; scope it honestly (see
-- Apyx `caller_net_nonpositive_trace` for the fixed-rate trace fragment + the open note).

/-! ## I4 — Rounding favors the protocol (docs/08 pattern C) -/

/-- Round-trips never credit the user; withdrawals round up. Pure `Nat` division lemmas. -/
theorem rounding_favors_protocol (s : State) :
    (∀ a, ‹convertToAssets s (convertToShares s a) ≤ a›) ∧
    (∀ sh, ‹convertToShares s (convertToAssets s sh) ≤ sh›) ∧
    ‹(∀ a, previewDeposit s a ≤ previewWithdraw s a)› := by
  ‹unfold conversions; Nat.div_mul_le_self / Nat.div_le_div_right›

/-! ## I5 — Donation-immunity (docs/08 pattern B, the root) -/

/-- Pooled assets rise only through an accounted op paired with a share mint; there is no raw
    transfer primitive, so the ERC4626 inflation attack is structurally impossible. If the app
    *does* expose a raw-transfer sink into pooled accounting, this becomes a FINDING. -/
theorem donation_free (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') :
    ‹s'.pooledAssets ≤ s.pooledAssets  -- unless op = the accounted share-mint, then matched 1:1› := by
  ‹cases op; the only increaser is the share-mint op, paired with a supply increase›

theorem no_inflation_attack ‹...› := ‹derive from donation_free + rounding›

/-! ## G — Parameter-bound gap-witness (docs/08 pattern G): prove the ABSENCE of a floor/cap -/

/-- For each economically-sensitive param with no enforced bound, exhibit a reachable state
    where the missing bound causes a bad outcome — a machine-checked *vulnerability*, reported
    with the recommended fix. (Apyx: `redeem_payout_has_no_cap` — no upper bound on the payout;
    `admin_rfq_coalition_drains` — floor 0 ⇒ a victim's tokens burn for 0.) -/
theorem ‹param›_has_no_bound :
    ∃ (s s' : State) ‹...›, ‹reachable/witnessed step› ∧ ‹BadState s'› := by
  ‹refine ⟨witness, ...⟩; the mandated op drives the param past any safe bound›

end ‹AppNamespace›
