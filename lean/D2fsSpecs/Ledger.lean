import D2fsSpecs.Safety

/-!
# Explicit finite-support ledger identity for apxUSD — and the witness that the
# current aggregate predicates do not imply it

`docs/11-apyx-proof-map.md` §5.1 asks for a ledger-consistency layer: state what
balances and total supply *mean*, i.e. `Σ_a apxUSDBal a = totalSupply_apxUSD`.
The standing gap, documented in `Safety.lean`'s S2 docstring and in
`Invariant.lean`, is that `State.apxUSDBal` is a bare `Address → Nat` with no
finite-support structure, so no such summation identity is stated anywhere —
which is exactly why `WellFormed` (the per-address bound) has to be *assumed*
along traces instead of derived.

This module makes the missing identity explicit:

* `ApxUSDLedgerConsistent s` — there is a finite set of holders covering the
  support of `apxUSDBal`, whose balances sum to `totalSupply_apxUSD`. The
  project deliberately has no Mathlib dependency, so `Finset Address` is not
  available; the predicate uses its exact underlying data instead — a
  duplicate-free `List Address` (`List.Pairwise (· ≠ ·)`) together with a
  summation over it. Up to the usual quotient, `∃ holders : Finset Address, …`
  and this statement are the same.
* `apxUSDLedgerConsistent_default` — the empty `default` state satisfies it
  (empty holder set, both sides `0`).
* `ledgerGapWitness` — a **model-gap / regression witness** (proof-map §11
  status: *witness*): a concrete state satisfying both `WellFormed` and
  `Solvent` in which two distinct holders' apxUSD balances together exceed
  `totalSupply_apxUSD`. Hence `wellFormed_solvent_not_imply_ledgerConsistent`:
  the aggregate predicates the development currently carries do **not** imply
  the finite ledger identity. This is a statement about the *model's*
  expressiveness — the abstract `State` admits states no ERC-20 ledger can
  reach — not a claim that the deployed protocol can mint unbacked balances.

## Why there is no `apxUSDLedgerConsistent_step` here

A step-preservation theorem for `ApxUSDLedgerConsistent` is the natural next
proof obligation, and it is deliberately **absent** rather than faked. To prove
that a successful `step` preserves the identity one needs, for every
balance-writing operation (`mintApxUSD`, `burnApxUSD`, `transferApxUSD`,
`requestUnlockStep`, the claim re-mints, `executeRFQRedemption`,
`poolRedeem`, …), a support/update lemma of the shape "the post-state's support
is contained in the pre-state's support plus the touched addresses, and the sum
over any covering holder set changes by exactly the supply delta". Nothing of
that shape exists in the development today, and it cannot be conjured from the
aggregate facts (`WellFormed`/`Solvent`) — the witness below is precisely the
counterexample. The two honest ways to obtain preservation are:

1. **change `State`** to carry an explicit holder domain (e.g. an association
   list / finite map for `apxUSDBal`), so finite support holds by construction
   and each writer updates the sum in lockstep with the supply; or
2. **keep the bare function** and prove, per balance-writing operation, the
   support-inclusion and sum-delta lemmas described above, then compose them
   into a preservation theorem with the same operation scoping discipline as
   `solvency_step`.

Either is a substantial, separately-scoped change to protocol-semantics files
this module must not touch. Until one is done, `ApxUSDLedgerConsistent` is an
*initialization-only* invariant plus a named gap, matching how `Invariant.lean`
keeps `WellFormed s'` an explicit hypothesis instead of pretending to derive it.

Status (proof-map §11): `apxUSDLedgerConsistent_default` is model-local;
`ledgerGapWitness_*` and `wellFormed_solvent_not_imply_ledgerConsistent` are
witness/regression facts, not universal theorems.
-/

namespace Apyx

/-- Sum of `f` over a list of addresses. Local, dependency-free stand-in for
`∑ a in holders, f a` (the project carries no Mathlib, hence no `Finset` or big
operators). -/
def sumOver (f : Address → Nat) : List Address → Nat
  | [] => 0
  | a :: rest => f a + sumOver f rest

@[simp] theorem sumOver_nil (f : Address → Nat) : sumOver f [] = 0 := rfl

@[simp] theorem sumOver_cons (f : Address → Nat) (a : Address) (l : List Address) :
    sumOver f (a :: l) = f a + sumOver f l := rfl

/-- One member's value is at most the sum over the list. -/
theorem sumOver_mem_le (f : Address → Nat) :
    ∀ {l : List Address} {a : Address}, a ∈ l → f a ≤ sumOver f l := by
  intro l
  induction l with
  | nil => intro a ha; cases ha
  | cons x xs ih =>
    intro a ha
    rw [sumOver_cons]
    cases List.mem_cons.mp ha with
    | inl hax => subst hax; exact Nat.le_add_right _ _
    | inr hax =>
      have := ih hax
      omega

/-- Two *distinct* members' values together are at most the sum over the list.
Distinctness alone suffices — no duplicate-freeness hypothesis is needed —
because the two occurrences are necessarily at different positions. -/
theorem sumOver_two_mem_le (f : Address → Nat) :
    ∀ {l : List Address} {a b : Address}, a ≠ b → a ∈ l → b ∈ l →
      f a + f b ≤ sumOver f l := by
  intro l
  induction l with
  | nil => intro a b _ ha _; cases ha
  | cons x xs ih =>
    intro a b hab ha hb
    rw [sumOver_cons]
    cases List.mem_cons.mp ha with
    | inl hax =>
      have hbx : b ∈ xs := by
        cases List.mem_cons.mp hb with
        | inl h => exact absurd (hax.trans h.symm) hab
        | inr h => exact h
      subst hax
      have := sumOver_mem_le f hbx
      omega
    | inr hax =>
      cases List.mem_cons.mp hb with
      | inl hbx =>
        subst hbx
        have := sumOver_mem_le f hax
        omega
      | inr hbx =>
        have := ih hab hax hbx
        omega

/-- **The finite-support ledger identity for apxUSD** (proof-map §5.1): there is
a finite, duplicate-free set of holders that covers the support of `apxUSDBal`
(every address with a non-zero balance is listed) and whose balances sum to
exactly `totalSupply_apxUSD`.

`List.Pairwise (· ≠ ·)` is `Nodup` spelled out; a duplicate-free list is the
underlying data of a `Finset Address`, so this is the Mathlib-free rendering of
`∃ holders : Finset Address, (∀ a, s.apxUSDBal a ≠ 0 → a ∈ holders) ∧
(∑ a in holders, s.apxUSDBal a = s.totalSupply_apxUSD)`.

On a real ERC-20 this holds by construction. In this model it is an extra
predicate the aggregate state does not maintain — see the module docstring for
why no step-preservation theorem accompanies it yet. -/
def ApxUSDLedgerConsistent (s : State) : Prop :=
  ∃ holders : List Address,
    holders.Pairwise (· ≠ ·) ∧
    (∀ a, s.apxUSDBal a ≠ 0 → a ∈ holders) ∧
    sumOver s.apxUSDBal holders = s.totalSupply_apxUSD

/-- Initialization: the empty `default` state satisfies the ledger identity with
the empty holder set — every balance is `0`, and both sides of the sum identity
are `0`. -/
theorem apxUSDLedgerConsistent_default : ApxUSDLedgerConsistent (default : State) := by
  refine ⟨[], List.Pairwise.nil, ?_, rfl⟩
  intro a hne
  exact absurd rfl hne

/-! ## Model-gap / regression witness

**Not a protocol exploit claim.** `ledgerGapWitness` is a state of the *abstract
model* that no ERC-20-conforming deployment can reach: two holders own one unit
each while the recorded total supply is one. Its role is the proof-map §15
"keep the counterexample as a witness" discipline: it pins down, as a
regression fact, that `WellFormed ∧ Solvent` — the strongest aggregate ledger
facts the development currently composes in `ProtocolInv` — are too weak to
entail the finite ledger identity, so any future claim that they do must first
refute this state. -/

/-- Two distinct holders (addresses `0` and `1`) hold one apxUSD unit each while
`totalSupply_apxUSD = 1`; the reserve is padded so `Solvent` holds. Every other
field is the empty `default`. -/
def ledgerGapWitness : State :=
  { (default : State) with
      totalSupply_apxUSD := 1
      apxUSDBal := fun a => if a = 0 then 1 else if a = 1 then 1 else 0
      usdcReserve := 2 }

/-- The witness satisfies `WellFormed`: each individual balance (`1`, `1`, or
`0`) is at most the total supply `1`, and the redemption price `0` is under
par. The per-address bound is exactly what makes `WellFormed` blind to the
*joint* overclaim. -/
theorem ledgerGapWitness_wellFormed : WellFormed ledgerGapWitness := by
  constructor
  · intro a
    show (if a = 0 then 1 else if a = 1 then 1 else 0) ≤ 1
    split
    · exact Nat.le_refl 1
    · split
      · exact Nat.le_refl 1
      · exact Nat.zero_le 1
  · exact Nat.zero_le ray

/-- The witness satisfies `Solvent`: supply `1` against collateral `0` plus
reserve `2`. `Solvent` only compares the *recorded* total supply with backing,
so it too is blind to balances summing past the supply. -/
theorem ledgerGapWitness_solvent : Solvent ledgerGapWitness := by
  show ledgerGapWitness.totalSupply_apxUSD
      ≤ ledgerGapWitness.totalCollateralValue + ledgerGapWitness.usdcReserve
  decide

/-- The two distinct holders jointly claim more than the recorded supply:
`bal 0 + bal 1 = 2 > 1 = totalSupply_apxUSD`. -/
theorem ledgerGapWitness_two_holders_exceed_supply :
    ledgerGapWitness.totalSupply_apxUSD
      < ledgerGapWitness.apxUSDBal 0 + ledgerGapWitness.apxUSDBal 1 := by
  decide

/-- The witness violates the finite-support ledger identity: any holder set
covering the support must contain both address `0` and address `1`, so its sum
is at least `2`, but the identity would force it to equal the supply `1`. -/
theorem ledgerGapWitness_not_ledgerConsistent :
    ¬ ApxUSDLedgerConsistent ledgerGapWitness := by
  intro h
  obtain ⟨holders, _hnd, hcov, hsum⟩ := h
  have h0 : (0 : Address) ∈ holders := hcov 0 (by decide)
  have h1 : (1 : Address) ∈ holders := hcov 1 (by decide)
  have hle := sumOver_two_mem_le ledgerGapWitness.apxUSDBal
    (by decide : (0 : Address) ≠ 1) h0 h1
  rw [hsum] at hle
  have e0 : ledgerGapWitness.apxUSDBal 0 = 1 := rfl
  have e1 : ledgerGapWitness.apxUSDBal 1 = 1 := rfl
  have et : ledgerGapWitness.totalSupply_apxUSD = 1 := rfl
  omega

/-- **The named gap, as a theorem** (status: witness/regression): the aggregate
predicates the development composes today — `WellFormed` and `Solvent` — do not
imply the finite-support ledger identity. Consequently `ApxUSDLedgerConsistent`
is genuinely new information over `ProtocolInv`'s conjuncts, and its trace
preservation cannot be obtained from them; it needs either a `State` that
carries a holder domain or per-operation support/update lemmas (see the module
docstring). -/
theorem wellFormed_solvent_not_imply_ledgerConsistent :
    ¬ (∀ s : State, WellFormed s → Solvent s → ApxUSDLedgerConsistent s) :=
  fun h => ledgerGapWitness_not_ledgerConsistent
    (h ledgerGapWitness ledgerGapWitness_wellFormed ledgerGapWitness_solvent)

end Apyx
