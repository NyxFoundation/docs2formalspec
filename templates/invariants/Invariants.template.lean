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

/-! # Tier 1.5 — async / queue / signed value (I10–I15)

**Skip this whole section unless Step 0b in the README says so.** These need model extensions
E1–E4; adding them to a genuinely synchronous app buys nothing and costs proof effort.
Worked reference: `templates/invariants/examples/AsyncQueueVault.lean` (fictional protocol,
compiled). I13/I14 below are schema only — no reference exists yet.
-/

/-! ## E1/E4 — model extensions -/

inductive Op
  | ‹protocol ops›
  -- E1: one settlement round elapses. `delivered` is what the settlement layer actually
  -- acknowledged — make it an ARGUMENT, do not hard-wire `delivered = inflight`, or the model
  -- assumes away exactly the failure it should expose.
  | tick (delivered : Nat)

structure Request where          -- E2: the two-phase op's filed intent
  id      : Nat
  owner   : Address
  amount  : Nat
  filedAt : Nat                  -- the round it was filed in
  quote   : Nat                  -- price snapshot AT FILING — the crux of I10

-- E4: `State` gains `pending : List Request`, `capacity : Nat`, `inflight`/`settled`.

/-! ## I10 — settlement-timing neutrality (docs/08 pattern J) -/

/-- Pay the protocol-favourable side of {filing price, settlement price}. -/
def settlePayout (r : Request) (px : Nat) : Nat :=
  min ‹entitle r.quote r.amount› ‹entitle px r.amount›

theorem settle_credits_protocol_favourable_side (s : State) (r : Request) ‹...›
    (h : step s (Op.settle r.id) ‹settler› = some s') :
    ‹s'.paid r.owner = s.paid r.owner + settlePayout r s.price› := by
  ‹cases the guards; the credit is exactly settlePayout›

theorem settler_timing_cannot_gain (r : Request) (px : Nat) :
    settlePayout r px ≤ ‹entitle r.quote r.amount› := Nat.min_le_left _ _

/-- Contrast witness — why the `min` is required, not merely nice: a filing-quote-only rule
    overpays whenever the price fell, handing a free option to whoever times settlement. -/
theorem naive_filing_price_overpays_witness :
    ∃ (r : Request) (px : Nat), ‹entitle px r.amount› < ‹entitle r.quote r.amount› := ‹WITNESS›

/-! ## I11 — queue liveness / capacity griefing (docs/08 pattern K) — gap-witness by default -/

/-- (a) occupancy: a full queue rejects EVERY honest enqueue; (b) zero cost: the attacker's
    cancel-then-refile cycle restores his holdings with the queue just as full. (b) is what
    turns a capacity bound into a denial of service — report it with the fix (per-user cap,
    non-refundable reservation, or fee). -/
theorem queue_capacity_griefing_witness :
    -- control clause first: without it, (2) would follow just as well from an empty balance and
    -- the witness would not be about capacity at all
    ‹step free (Op.enqueue n) honest ≠ none› ∧
    (∀ m, step ‹occupied› (Op.enqueue m) ‹honest› = none) ∧
    ‹(execTrace occupied [cancel; re-enqueue]).holdings attacker = occupied.holdings attacker› :=
  ‹WITNESS — or replace with the positive form below if the design guarantees progress›

/-- The other mechanism: an unsettleable head freezes everything behind it. Strongest when it
    exhibits a queued request the reserve COULD cover that still cannot settle. -/
theorem queue_head_of_line_blocking_witness :
    ‹(∀ c, step blocked (Op.settle headId) c = none)› ∧
    ‹(∀ c, step blocked (Op.settle nextId) c = none)› ∧
    ‹(∃ r ∈ blocked.pending, payout r ≤ blocked.reserve)› := ‹WITNESS›

/-- …paired with a monotonicity lemma, so the block is permanent rather than merely current. -/
theorem ‹backing›_non_increasing_trace (s : State) (σ : List (Op × Address)) :
    ‹(execTrace s σ).reserve ≤ s.reserve› := ‹induction σ; exhaustive single-step lemma at head›

theorem queue_no_starvation ‹(s) (σ) (r) (hpend : Pending (execTrace s σ) r)› :
    ‹∃ τ, HonestOnly τ ∧ Claimed (execTrace (execTrace s σ) τ) r› := ‹PROOF›

/-! ## I12 — in-flight conservation -/

theorem inflight_conservation (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') ‹(hacc : ¬ IsAccounted op)› :
    s'.settled + s'.inflight = s.settled + s.inflight := by
  ‹cases op <;> exhaustive — note this holds for a PARTIAL tick too›

/-- The "in-flight is zero next round" convention, with its hypothesis kept visible. -/
theorem tick_settles_exactly (s : State) ‹...› (h : step s (Op.tick s.inflight) c = some s') :
    s'.settled = s.settled + s.inflight ∧ s'.inflight = 0 := ‹PROOF›

/-- …and proof that the hypothesis is load-bearing. -/
theorem partial_tick_leaves_residue ‹(hd : d < s.inflight)› ‹...› : 0 < s'.inflight := ‹PROOF›

/-! ## I15 — signed net value, and the `Nat` vacuity trap -/

def netValueNat (s : State) : Nat := ‹assets - liabilities›        -- truncating: LIES
def netValueInt (s : State) : Int := ‹(assets : Int) - liabilities› -- the real reading

/-- True by typing; carries no protocol information. Keep it in the output next to the witness
    so a reviewer sees why the unsigned ledger was rejected. -/
theorem nat_solvency_is_vacuous (s : State) : 0 ≤ netValueNat s := Nat.zero_le _

theorem insolvency_witness : ∃ s, ‹Reachable s› ∧ netValueInt s < 0 ∧ netValueNat s = 0 :=
  ‹WITNESS — or prove `net_value_nonneg` over traces if the design really precludes it›

/-! # Tier 1-C — per-account solvency (I16–I21)

**Skip unless Step 0c says so.** Applies when users hold individual collateral/debt positions, the
protocol advertises an ordering, or a parameter is called immutable. Worked reference:
`templates/invariants/examples/CollateralizedDebt.lean` (fictional protocol, compiled).
I20 is schema only.
-/

def Healthy (s : State) (p : ‹Position›) : Prop := ‹owed s p * s.minRatio ≤ p.coll * s.price›
def AllHealthy (s : State) : Prop := ∀ p ∈ s.‹positions›, Healthy s p

/-- Ops that may legitimately make a position liquidatable — the honest exclusion list. Naming them
    is what keeps I16 from being either false or a lie. -/
def IsRiskSource : Op → Prop
  | Op.‹accrue› _   => True
  | Op.‹setPrice› _ => True
  | _               => False

/-- **I16.** State it BOOK-WIDE. A per-op guard lemma proves the op you looked at is safe; the
    Euler defect is always in the op you did not look at. -/
theorem all_healthy_preserved (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hsafe : ¬ IsRiskSource op) (hs : AllHealthy s) :
    AllHealthy s' := by
  ‹cases op; for each: pull membership back through the list update, then either reuse the op's own
   guard (borrow / withdraw / open) or a monotonicity lemma (repay / addCollateral / redeem)›
-- Budget for five mechanical helpers first: membership through update / drop / insert, and
-- `healthy_add_coll` / `healthy_sub_debt`. Plus `price_ratio_stable`: the pricing inputs the health
-- check reads must be shown untouched, or "healthy before" and "healthy after" are different claims.

/-- Whichever op REMOVES backing (redemption buying collateral out, partial withdrawal against a
    reduced obligation) is the one case of I16 that is not bookkeeping. State it separately. It is
    safe only if the user's obligation is computed with CEILING rounding (I4) and the protocol
    over-collateralizes — make both explicit, do not let them hide inside `step`. -/
theorem ‹redeem›_preserves_health (s : State) (p : ‹Position›) (amount : Nat)
    (hoc : ‹one ≤ s.minRatio›) (hp : Healthy s p) :
    ‹Healthy s { p with coll := p.coll - amount, debt := p.debt - obligation s amount }› := ‹PROOF›

/-- **I17.** A healthy position cannot be liquidated, and the seizure is bounded by the collateral
    actually present. An unbounded seizure is a finding, not a theorem (pattern G on the penalty). -/
theorem liquidate_requires_unhealthy ‹...› : ¬ Healthy s p := ‹PROOF›
theorem liquidation_seizure_bounded (s : State) (p : ‹Position›) : ‹seizure s p ≤ p.coll› := ‹PROOF›

/-- **I18.** An advertised order is a safety property: no skipping ahead, no being skipped. -/
theorem ‹redeem›_hits_head_only ‹...› : ‹s'.positions = f p :: rest› := ‹PROOF›
theorem ‹insert›_sorted (p : ‹Position›) : ∀ l, Sorted l → Sorted (‹insert› p l) := ‹PROOF›

/-- **I19.** The accrual index never falls, and accrual moves health one way only — which is why
    it is in `IsRiskSource` rather than being a counterexample to I16. -/
theorem index_monotone ‹...› : s.‹index› ≤ s'.‹index› := ‹cases op, exhaustive›
theorem accrual_never_lowers_debt ‹...› : ‹∃ p ∈ s.positions, p.debt ≤ q.debt› := ‹PROOF›

/-- **I21 — the dual of the pattern-G gap-witness, and the cheapest theorem in this file.**
    Wherever a deployment calls a parameter immutable, prove there is no mutation path. One
    `cases op`; a setter added in a later version breaks the build instead of the invariant. -/
theorem ‹param›_immutable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.‹param› = s.‹param› := by
  cases op <;> ‹EXHAUSTIVE — every branch is `rfl` after inverting the step›

/-! ## I20 — SCHEMA ONLY (socialized-loss pool)

Absorbing a loss into a shared pool must not create value: after absorption the depositors'
aggregate claim equals the pool before minus the amount absorbed, and no depositor's share rises.
Needs the counterparty side of the ledger in the model; no worked reference exists.
-/

/-! ## I13 / I14 — SCHEMA ONLY (no worked reference yet; do not report as covered)

I13: add an explicit in-transit bucket, prove `Σ(venues) + inTransit` preserved by internal moves,
     plus `in_transit_lands` (or witness permanently stuck funds).
I14: `|intent − realized| ≤ ‹minActionSize› * ‹unexecuted count›`, or — following pattern G —
     `∀ B, ∃ σ, B < |drift (execTrace s σ)|` when no bound is enforced.
-/

end ‹AppNamespace›
