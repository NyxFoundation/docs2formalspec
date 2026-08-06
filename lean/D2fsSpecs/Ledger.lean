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
over any covering holder set changes by exactly the supply delta". Such lemmas
exist for only a subset of writers so far, and they cannot be conjured from the
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
this module must not touch. The **first slice of option 2 now exists** (see
"First balance-writer slice" below): `apxUSDLedgerConsistent_mint` and
`apxUSDLedgerConsistent_burn` prove exactly the support-inclusion / sum-delta
facts for the two *primitive* single-address writers, applied in isolation;
`apxUSDLedgerConsistent_transfer` covers the distinct-address primitive
two-address writer and records the self-transfer model defect. The **second
slice** composes those primitives with the public transition
function for the five simplest `step` branches:
`apxUSDLedgerConsistent_basic_step` (see "Scoped public-step slice" below)
covers `depositUSDC`, `mintApxUSD`, `lockApxUSD`, `requestUnlock` and
`flexibleRequestUnlock`, including the plumbing that discharges each burning
branch's underflow guard into the burn-side bound. Separate scoped theorems
also cover `claimUnlock`, `flexibleClaimUnlock`, `redeemApxUSD`,
`executeRFQRedemption`, and `poolRedeem`. Everything else —
the frame proofs for the non-writing branches — remains open, so
`ApxUSDLedgerConsistent` is still an *initialization-plus-fragment*
invariant with a named gap, matching how `Invariant.lean` keeps
`WellFormed s'` an explicit hypothesis instead of pretending to derive it.

Status (proof-map §11): `apxUSDLedgerConsistent_default` is model-local;
`apxUSDLedgerConsistent_mint` / `apxUSDLedgerConsistent_burn` /
`apxUSDLedgerConsistent_transfer` are model-local per-operation lemmas (not
trace facts); `apxUSDLedgerConsistent_basic_step` and
`apxUSDLedgerConsistent_claimUnlock_step` /
`apxUSDLedgerConsistent_flexibleClaimUnlock_step` /
`apxUSDLedgerConsistent_redeemApxUSD_step` /
`apxUSDLedgerConsistent_executeRFQRedemption_step` /
`apxUSDLedgerConsistent_poolRedeem_step` are model-local *scoped* step facts
(not a trace invariant and not full `Op` coverage); `ledgerGapWitness_*` and
`wellFormed_solvent_not_imply_ledgerConsistent` are witness/regression facts,
not universal theorems.
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

/-! ## First balance-writer slice: `mintApxUSD` / `burnApxUSD` preservation

These are the first two entries of the per-operation programme described in the
module docstring (option 2): for the raw single-address balance writers
`mintApxUSD` and `burnApxUSD` we prove that the sum over a covering holder set
moves in lockstep with the recorded supply, and compose that into preservation
of `ApxUSDLedgerConsistent`. The holder-list representation stays existential:
a mint to an address *outside* the current holder set conses that address onto
the list (the fresh cover), while a burn always retains the pre-state list —
the cover clause only demands that non-zero balances be listed, so a holder
burned to zero may harmlessly remain listed.

**Scope — read this before citing these theorems.** This slice covers exactly
the two primitive writers, applied in isolation:

* `apxUSDLedgerConsistent_mint` — any mint from a consistent pre-state;
* `apxUSDLedgerConsistent_burn` — a burn whose amount is at most the sender's
  pre-state balance. The bound is not decoration: `burnApxUSD` uses truncated
  `Nat` subtraction, so an over-burn destroys more supply than balance and the
  identity genuinely breaks. Every burning `step` branch carries an underflow
  guard of exactly this shape, but that guard is **not** imported here — the
  hypothesis must be discharged by the caller.

Still uncovered, which is why no *universal* `step`-preservation theorem is
stated: only the balance-non-writing projection frames and final composition
remain. The primitive `transferApxUSD`
is now covered by
`apxUSDLedgerConsistent_transfer`, with an explicit distinct-address
hypothesis because the current writer mishandles self-transfer. The five
simplest `step` branches — the deposit-path mints and the three
guard-protected single-burn paths, `requestUnlockStep` included — are now
composed per branch in `apxUSDLedgerConsistent_basic_step` below (the
`solvency_step` scoping discipline); extending its explicit disjunction
branch-by-branch is the remaining work.

The `sumOver_*` helpers below are dependency-free `List` lemmas (the project
carries no Mathlib): congruence on members, and the two single-address
update/sum-delta facts for duplicate-free (`Pairwise (· ≠ ·)`) lists. -/

/-- `sumOver` only reads `f` at members of the list: pointwise agreement on the
list gives equal sums. -/
theorem sumOver_congr {f g : Address → Nat} :
    ∀ {l : List Address}, (∀ a ∈ l, f a = g a) → sumOver f l = sumOver g l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [sumOver_cons]
    rw [h x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))]

/-- Bumping a single **listed** address by `amount` adds exactly `amount` to
the sum, provided the list is duplicate-free — `Pairwise (· ≠ ·)` is what makes
the bumped address count once. This is the mint-side sum-delta lemma. -/
theorem sumOver_update_add_mem (f : Address → Nat) (t : Address) (amount : Nat) :
    ∀ {l : List Address}, l.Pairwise (· ≠ ·) → t ∈ l →
      sumOver (fun a => if a = t then f a + amount else f a) l
        = sumOver f l + amount := by
  intro l
  induction l with
  | nil => intro _ ht; cases ht
  | cons x xs ih =>
    intro hpw ht
    cases hpw with
    | cons hx hxs =>
      simp only [sumOver_cons]
      cases List.mem_cons.mp ht with
      | inl hxt =>
        subst hxt
        have htail : sumOver (fun a => if a = t then f a + amount else f a) xs
            = sumOver f xs :=
          sumOver_congr (fun b hb => if_neg (Ne.symm (hx b hb)))
        rw [if_pos rfl, htail]
        omega
      | inr hmem =>
        rw [if_neg (hx t hmem), ih hxs hmem]
        omega

/-- Deducting `amount ≤ f t` at a single **listed** address removes exactly
`amount` from the sum (stated addition-side to stay in well-behaved `Nat`
arithmetic), provided the list is duplicate-free. This is the burn-side
sum-delta lemma; the bound is what keeps truncated subtraction honest. -/
theorem sumOver_update_sub_mem (f : Address → Nat) (t : Address) (amount : Nat)
    (hle : amount ≤ f t) :
    ∀ {l : List Address}, l.Pairwise (· ≠ ·) → t ∈ l →
      sumOver (fun a => if a = t then f a - amount else f a) l + amount
        = sumOver f l := by
  intro l
  induction l with
  | nil => intro _ ht; cases ht
  | cons x xs ih =>
    intro hpw ht
    cases hpw with
    | cons hx hxs =>
      simp only [sumOver_cons]
      cases List.mem_cons.mp ht with
      | inl hxt =>
        subst hxt
        have htail : sumOver (fun a => if a = t then f a - amount else f a) xs
            = sumOver f xs :=
          sumOver_congr (fun b hb => if_neg (Ne.symm (hx b hb)))
        rw [if_pos rfl, htail]
        omega
      | inr hmem =>
        rw [if_neg (hx t hmem)]
        have := ih hxs hmem
        omega

/-- **Mint preserves the ledger identity.** `mintApxUSD` adds `amount` to one
address's balance and to the supply, so any covering holder set keeps covering
and its sum tracks the supply: if the recipient is already listed the same list
works (`sumOver_update_add_mem`); if not, the recipient's pre-balance is forced
to `0` by the cover clause, and consing the recipient onto the list restores
both the cover and the sum. First half of the first balance-writer slice. -/
theorem apxUSDLedgerConsistent_mint (s : State) (to : Address) (amount : Nat)
    (h : ApxUSDLedgerConsistent s) :
    ApxUSDLedgerConsistent (mintApxUSD s to amount) := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  by_cases hmem : to ∈ holders
  · refine ⟨holders, hnd, ?_, ?_⟩
    · intro a ha
      by_cases hat : a = to
      · subst hat; exact hmem
      · exact hcov a (by simpa [mintApxUSD, hat] using ha)
    · show sumOver (fun a => if a = to then s.apxUSDBal a + amount else s.apxUSDBal a)
          holders = s.totalSupply_apxUSD + amount
      rw [sumOver_update_add_mem s.apxUSDBal to amount hnd hmem, hsum]
  · -- minting to a fresh address: its pre-balance is 0 (it is off the cover),
    -- and the new holder list is the recipient consed onto the old one
    have hzero : s.apxUSDBal to = 0 := by
      by_cases hz : s.apxUSDBal to = 0
      · exact hz
      · exact False.elim (hmem (hcov to hz))
    refine ⟨to :: holders, ?_, ?_, ?_⟩
    · refine List.Pairwise.cons ?_ hnd
      intro b hb heq
      subst heq
      exact hmem hb
    · intro a ha
      by_cases hat : a = to
      · exact List.mem_cons.mpr (Or.inl hat)
      · exact List.mem_cons.mpr (Or.inr (hcov a (by simpa [mintApxUSD, hat] using ha)))
    · show sumOver (fun a => if a = to then s.apxUSDBal a + amount else s.apxUSDBal a)
          (to :: holders) = s.totalSupply_apxUSD + amount
      have htail : sumOver (fun a => if a = to then s.apxUSDBal a + amount else s.apxUSDBal a)
          holders = sumOver s.apxUSDBal holders :=
        sumOver_congr (fun b hb => by
          by_cases hbt : b = to
          · subst b
            exact False.elim (hmem hb)
          · simp [hbt])
      simp only [sumOver_cons]
      simp [htail, hzero, hsum]
      omega

/-- **Guarded burn preserves the ledger identity.** `burnApxUSD` deducts
`amount` from one address's balance and from the supply; with the underflow
bound `amount ≤ s.apxUSDBal fromAddr` both deductions are exact, so the
pre-state holder list is *retained*: the cover survives (a balance can only
shrink, and only at `fromAddr`, which stays listed) and the sum tracks the
supply via `sumOver_update_sub_mem`. When `fromAddr` is off the cover its
balance is `0`, forcing `amount = 0` and a no-op burn. Without the bound the
identity genuinely fails — truncated subtraction would zero the balance while
the supply drops by the full `amount`. Every burning `step` branch carries a
guard of exactly this shape; wiring those guards to this hypothesis is a
future slice. Second half of the first balance-writer slice. -/
theorem apxUSDLedgerConsistent_burn (s : State) (fromAddr : Address) (amount : Nat)
    (hle : amount ≤ s.apxUSDBal fromAddr)
    (h : ApxUSDLedgerConsistent s) :
    ApxUSDLedgerConsistent (burnApxUSD s fromAddr amount) := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  refine ⟨holders, hnd, ?_, ?_⟩
  · intro a ha
    by_cases hat : a = fromAddr
    · subst a
      refine hcov fromAddr (fun hz => ha ?_)
      simp [burnApxUSD, hz]
    · exact hcov a (by simpa [burnApxUSD, hat] using ha)
  · by_cases hmem : fromAddr ∈ holders
    · show sumOver (fun a => if a = fromAddr then s.apxUSDBal a - amount else s.apxUSDBal a)
          holders = s.totalSupply_apxUSD - amount
      have hkey := sumOver_update_sub_mem s.apxUSDBal fromAddr amount hle hnd hmem
      omega
    · -- burner off the cover ⇒ zero balance ⇒ the guard forces a no-op burn
      have hzero : s.apxUSDBal fromAddr = 0 := by
        by_cases hz : s.apxUSDBal fromAddr = 0
        · exact hz
        · exact False.elim (hmem (hcov fromAddr hz))
      have hamt : amount = 0 := by omega
      subst hamt
      show sumOver (fun a => if a = fromAddr then s.apxUSDBal a - 0 else s.apxUSDBal a)
          holders = s.totalSupply_apxUSD - 0
      have hcong : sumOver (fun a => if a = fromAddr then s.apxUSDBal a - 0 else s.apxUSDBal a)
          holders = sumOver s.apxUSDBal holders :=
        sumOver_congr (fun b _ => by simp)
      rw [hcong]
      omega

/-! ## Primitive transfer slice

`transferApxUSD` is a state writer used by the protocol model's transfer
surface, but it is not currently one of the constructors of `Op`. It therefore
gets its own theorem rather than being smuggled into the public-step theorem.
The transfer preserves supply and moves one balance from `fromAddr` to
`toAddr`; the proof below covers both an existing receiver and a fresh one.
The balance bound is required because the writer uses truncated `Nat`
subtraction. The distinct-address hypothesis is intentional: the current
primitive checks `a = fromAddr` before `a = toAddr`, so a self-transfer is
modelled as a burn rather than an ERC-20 no-op. That is a model defect to fix
before claiming self-transfer semantics. -/

private theorem sumOver_update_transfer_mem (f : Address → Nat)
    (fromAddr toAddr : Address) (amount : Nat)
    (hle : amount ≤ f fromAddr) (hne : fromAddr ≠ toAddr) :
    ∀ {l : List Address}, l.Pairwise (· ≠ ·) → fromAddr ∈ l → toAddr ∈ l →
      sumOver (fun a => if a = fromAddr then f a - amount
        else if a = toAddr then f a + amount else f a) l = sumOver f l := by
  intro l hnd hfrom hto
  let fsub : Address → Nat := fun a => if a = fromAddr then f a - amount else f a
  have hsub := sumOver_update_sub_mem f fromAddr amount hle hnd hfrom
  have hadd := sumOver_update_add_mem fsub toAddr amount hnd hto
  have hpoint : ∀ a ∈ l,
      (if a = fromAddr then f a - amount
        else if a = toAddr then f a + amount else f a) =
      (if a = toAddr then fsub a + amount else fsub a) := by
    intro a ha
    by_cases haf : a = fromAddr
    · subst a
      simp [fsub, hne]
    · by_cases hat : a = toAddr
      · subst a
        simp [fsub, Ne.symm hne]
      · simp [fsub, haf, hat]
  have hsum := sumOver_congr hpoint
  rw [hsum]
  exact hadd.trans hsub

/-- Regression fact for the transfer model: because the `fromAddr` test comes
first, a self-transfer subtracts the amount instead of being a no-op. -/
theorem transferApxUSD_self_balance (s : State) (a : Address) (amount : Nat) :
    (transferApxUSD s a a amount).apxUSDBal a = s.apxUSDBal a - amount := by
  simp [transferApxUSD]

/-- **Primitive transfer preserves the finite ledger identity.** The pre-state
must satisfy `amount ≤ s.apxUSDBal fromAddr`, because `transferApxUSD` uses
truncated subtraction, and the addresses must be distinct. The latter exposes
a model defect: the current primitive's ordered condition makes self-transfer
burn the amount instead of leaving balances unchanged. The theorem is
deliberately about the primitive writer: the current `Op` type has no public
transfer constructor. -/
theorem apxUSDLedgerConsistent_transfer (s : State) (fromAddr toAddr : Address)
    (amount : Nat) (hne : fromAddr ≠ toAddr)
    (hle : amount ≤ s.apxUSDBal fromAddr)
    (h : ApxUSDLedgerConsistent s) :
    ApxUSDLedgerConsistent (transferApxUSD s fromAddr toAddr amount) := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  by_cases hzero : amount = 0
  · subst amount
    refine ⟨holders, hnd, ?_, ?_⟩
    · intro a ha
      exact hcov a (by simpa [transferApxUSD] using ha)
    · simpa [transferApxUSD] using hsum
  by_cases hto : toAddr ∈ holders
  · by_cases hself : fromAddr = toAddr
    · exact False.elim (hne hself)
    · have hfrom : fromAddr ∈ holders := by
        by_cases hm : fromAddr ∈ holders
        · exact hm
        · have hz : s.apxUSDBal fromAddr = 0 := by
            by_cases hz : s.apxUSDBal fromAddr = 0
            · exact hz
            · exact False.elim (hm (hcov fromAddr hz))
          omega
      refine ⟨holders, hnd, ?_, ?_⟩
      · intro a ha
        by_cases haf : a = fromAddr
        · subst a
          refine hcov fromAddr (fun hz => ha ?_)
          simp [transferApxUSD, hz]
        · by_cases hat : a = toAddr
          · subst a
            exact hto
          · exact hcov a (by simpa [transferApxUSD, haf, hat] using ha)
      · show sumOver (fun a => if a = fromAddr then s.apxUSDBal a - amount
            else if a = toAddr then s.apxUSDBal a + amount else s.apxUSDBal a) holders =
          s.totalSupply_apxUSD
        exact (sumOver_update_transfer_mem s.apxUSDBal fromAddr toAddr amount hle
          hne hnd hfrom hto).trans hsum
  · have htoZero : s.apxUSDBal toAddr = 0 := by
      by_cases hz : s.apxUSDBal toAddr = 0
      · exact hz
      · exact False.elim (hto (hcov toAddr hz))
    have hfrom : fromAddr ∈ holders := by
      by_cases hm : fromAddr ∈ holders
      · exact hm
      · have hz : s.apxUSDBal fromAddr = 0 := by
          by_cases hz : s.apxUSDBal fromAddr = 0
          · exact hz
          · exact False.elim (hm (hcov fromAddr hz))
        omega
    refine ⟨toAddr :: holders, ?_, ?_, ?_⟩
    · refine List.Pairwise.cons ?_ hnd
      intro b hb heq
      subst b
      exact hto hb
    · intro a ha
      by_cases hat : a = toAddr
      · exact List.mem_cons.mpr (Or.inl hat)
      · by_cases haf : a = fromAddr
        · subst a
          exact List.mem_cons.mpr (Or.inr (hfrom))
        · exact List.mem_cons.mpr (Or.inr (hcov a
            (by simpa [transferApxUSD, haf, hat] using ha)))
    · show sumOver (fun a => if a = fromAddr then s.apxUSDBal a - amount
          else if a = toAddr then s.apxUSDBal a + amount else s.apxUSDBal a)
          (toAddr :: holders) = s.totalSupply_apxUSD
      have htail : sumOver (fun a => if a = fromAddr then s.apxUSDBal a - amount
          else if a = toAddr then s.apxUSDBal a + amount else s.apxUSDBal a) holders =
          sumOver (fun a => if a = fromAddr then s.apxUSDBal a - amount else s.apxUSDBal a)
            holders := by
        apply sumOver_congr
        intro b hb
        have hbt : b ≠ toAddr := by
          intro hbeq
          apply hto
          simpa [hbeq] using hb
        by_cases hbf : b = fromAddr
        · simp [hbf]
        · simp [hbf, hbt]
      have hsub := sumOver_update_sub_mem s.apxUSDBal fromAddr amount hle hnd hfrom
      simp only [sumOver_cons]
      rw [htail]
      simp [Ne.symm hne, htoZero]
      omega

/-! ## Scoped public-step slice: `apxUSDLedgerConsistent_basic_step`

Second slice of the per-operation programme: the primitive mint/burn lemmas
above, composed with the public transition function for the **five** `step`
branches whose apxUSD-ledger effect is a single primitive `mintApxUSD` or a
single guard-protected `burnApxUSD` —

* `Op.depositUSDC` — mints `amount` to the caller (plus USDC bookkeeping);
* `Op.mintApxUSD` — mints `amount` to `to` (arbitrage path);
* `Op.lockApxUSD` — burns `amount` from the caller, then vault/apyUSD writes;
* `Op.requestUnlock` — burns via `requestUnlockStep`, then registry writes;
* `Op.flexibleRequestUnlock` — burns, then `createFlexibleUnlock`.

Each burning branch carries the guard `¬ (s.apxUSDBal caller < amount)`, which
is exactly the bound `apxUSDLedgerConsistent_burn` needs; the inversion lemmas
below surface it, so it is discharged locally from the successful `step` —
nothing is assumed beyond `ApxUSDLedgerConsistent s` and `step … = some s'`.

**Scoped, not universal — read this before citing the theorem.** The theorem
takes an explicit disjunction naming its five operations rather than claiming
all of `Op`. The balance-writing branches have separate theorems below; the
non-writing branches (`withdraw`,
`redeem`, `tick`, pause/list/admin ops), which need per-branch frame lemmas
instead. Extending the disjunction branch-by-branch — the `solvency_step`
scoping discipline — is the remaining work named in the module docstring.

The `step_*_ledgerProj` inversion lemmas are local re-derivations trimmed to
the two projections `ApxUSDLedgerConsistent` reads: the full inversion lemmas
in `Apyx.lean` are `private`, the same situation `Safety.lean` resolves the
same way. -/

/-- Frame theorem: `ApxUSDLedgerConsistent` reads exactly two state
projections — `apxUSDBal` and `totalSupply_apxUSD` — so any state agreeing
with a consistent one on both is itself consistent. This is what lets each
`step` branch's wrapper writes (`emitEvent`, `updateExchangeRate`, registry
and NFT writes, apyUSD and USDC moves) be discarded. -/
theorem apxUSDLedgerConsistent_of_projections_eq {s t : State}
    (hbal : s.apxUSDBal = t.apxUSDBal)
    (hsup : s.totalSupply_apxUSD = t.totalSupply_apxUSD)
    (h : ApxUSDLedgerConsistent t) : ApxUSDLedgerConsistent s := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  refine ⟨holders, hnd, ?_, ?_⟩
  · intro a ha
    refine hcov a ?_
    rw [← hbal]
    exact ha
  · rw [hbal, hsup]
    exact hsum

/-- `Op.depositUSDC` inversion, ledger projections only: the post-state agrees
with `mintApxUSD s caller amount` on `apxUSDBal` and `totalSupply_apxUSD` (the
USDC bookkeeping and the event log touch neither). -/
private theorem step_depositUSDC_ledgerProj (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h : step s (Op.depositUSDC amount) caller = some s') :
    s'.apxUSDBal = (mintApxUSD s caller amount).apxUSDBal ∧
    s'.totalSupply_apxUSD = (mintApxUSD s caller amount).totalSupply_apxUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · cases Option.some.inj h
          exact ⟨by simp [emitEvent, mintApxUSD], by simp [emitEvent, mintApxUSD]⟩

/-- `Op.mintApxUSD` inversion, ledger projections only: the post-state agrees
with `mintApxUSD s to amount` on the two ledger projections. -/
private theorem step_mintApxUSD_ledgerProj (s : State) (to : Address) (amount : Nat)
    (caller : Address) (s' : State)
    (h : step s (Op.mintApxUSD to amount) caller = some s') :
    s'.apxUSDBal = (mintApxUSD s to amount).apxUSDBal ∧
    s'.totalSupply_apxUSD = (mintApxUSD s to amount).totalSupply_apxUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · cases Option.some.inj h
            exact ⟨by simp [emitEvent, mintApxUSD], by simp [emitEvent, mintApxUSD]⟩

/-- `Op.lockApxUSD` inversion, ledger projections only: the branch guard gives
the burn bound, and the post-state agrees with `burnApxUSD s caller amount` on
the two ledger projections (the vault, apyUSD, rate and event writes touch
neither). -/
private theorem step_lockApxUSD_ledgerProj (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h : step s (Op.lockApxUSD amount) caller = some s') :
    amount ≤ s.apxUSDBal caller ∧
    s'.apxUSDBal = (burnApxUSD s caller amount).apxUSDBal ∧
    s'.totalSupply_apxUSD = (burnApxUSD s caller amount).totalSupply_apxUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · cases Option.some.inj h
        exact ⟨by omega, by simp [emitEvent, updateExchangeRate, mintApyUSD],
          by simp [emitEvent, updateExchangeRate, mintApyUSD]⟩

/-- `Op.requestUnlock` inversion, ledger projections only: the branch guard
gives the burn bound, and `requestUnlockStep`'s own frame lemmas reduce the
post-state's ledger projections to those of `burnApxUSD s caller amount`. -/
private theorem step_requestUnlock_ledgerProj (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h : step s (Op.requestUnlock amount) caller = some s') :
    amount ≤ s.apxUSDBal caller ∧
    s'.apxUSDBal = (burnApxUSD s caller amount).apxUSDBal ∧
    s'.totalSupply_apxUSD = (burnApxUSD s caller amount).totalSupply_apxUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · cases Option.some.inj h
        exact ⟨by omega, by simp, by simp [burnApxUSD]⟩

/-- `Op.flexibleRequestUnlock` inversion, ledger projections only: the branch
guard gives the burn bound, and `createFlexibleUnlock` touches neither ledger
projection. -/
private theorem step_flexibleRequestUnlock_ledgerProj (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (h : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    amount ≤ s.apxUSDBal caller ∧
    s'.apxUSDBal = (burnApxUSD s caller amount).apxUSDBal ∧
    s'.totalSupply_apxUSD = (burnApxUSD s caller amount).totalSupply_apxUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · cases Option.some.inj h
        exact ⟨by omega, by simp [createFlexibleUnlock], by simp [createFlexibleUnlock]⟩

/-- **Scoped public-step preservation of the ledger identity** (second slice).
A successful `step` of one of the five simple apxUSD balance paths —
`depositUSDC`, `mintApxUSD`, `lockApxUSD`, `requestUnlock`,
`flexibleRequestUnlock`, named by the explicit disjunction `hop` — preserves
`ApxUSDLedgerConsistent`. The two mint paths reduce to
`apxUSDLedgerConsistent_mint`; the three burn paths discharge
`apxUSDLedgerConsistent_burn`'s underflow bound from their own branch guard,
surfaced by the inversion lemmas above. **Not** a claim about all of `Op` —
see the section docstring for the branches that remain open. -/
theorem apxUSDLedgerConsistent_basic_step (s s' : State) (op : Op) (caller : Address)
    (h : ApxUSDLedgerConsistent s)
    (hstep : step s op caller = some s')
    (hop : (∃ amount, op = Op.depositUSDC amount) ∨
           (∃ to amount, op = Op.mintApxUSD to amount) ∨
           (∃ amount, op = Op.lockApxUSD amount) ∨
           (∃ amount, op = Op.requestUnlock amount) ∨
           (∃ amount, op = Op.flexibleRequestUnlock amount)) :
    ApxUSDLedgerConsistent s' := by
  rcases hop with ⟨amount, rfl⟩ | ⟨to, amount, rfl⟩ | ⟨amount, rfl⟩ | ⟨amount, rfl⟩
    | ⟨amount, rfl⟩
  · obtain ⟨hbal, hsup⟩ := step_depositUSDC_ledgerProj s amount caller s' hstep
    exact apxUSDLedgerConsistent_of_projections_eq hbal hsup
      (apxUSDLedgerConsistent_mint s caller amount h)
  · obtain ⟨hbal, hsup⟩ := step_mintApxUSD_ledgerProj s to amount caller s' hstep
    exact apxUSDLedgerConsistent_of_projections_eq hbal hsup
      (apxUSDLedgerConsistent_mint s to amount h)
  · obtain ⟨hle, hbal, hsup⟩ := step_lockApxUSD_ledgerProj s amount caller s' hstep
    exact apxUSDLedgerConsistent_of_projections_eq hbal hsup
      (apxUSDLedgerConsistent_burn s caller amount hle h)
  · obtain ⟨hle, hbal, hsup⟩ := step_requestUnlock_ledgerProj s amount caller s' hstep
    exact apxUSDLedgerConsistent_of_projections_eq hbal hsup
      (apxUSDLedgerConsistent_burn s caller amount hle h)
  · obtain ⟨hle, hbal, hsup⟩ := step_flexibleRequestUnlock_ledgerProj s amount caller s' hstep
    exact apxUSDLedgerConsistent_of_projections_eq hbal hsup
      (apxUSDLedgerConsistent_burn s caller amount hle h)

/-! ## Scoped claim-remint slice

`claimUnlock` retires the receipt and registry entry, then mints the released
amount back to the recorded owner. The registry retirement is a frame for the
two ledger projections, so this branch composes directly with the primitive
mint theorem. The inversion lemma is repeated locally because the corresponding
helper in `Registry.lean` is private. -/

private theorem step_claimUnlock_ledgerProj (s : State) (id : Nat) (caller : Address)
    (s' : State) (h : step s (Op.claimUnlock id) caller = some s') :
    ∃ owner amount cooldownEnd,
      s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      cooldownEnd ≤ s.now ∧
      s' = mintApxUSD (retireStandardUnlock s id owner) owner amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · exact ⟨owner, amount, cooldownEnd, heq, by simp_all, by assumption,
              by omega, (Option.some.inj h).symm⟩
        · exact absurd h (by simp)

/-- A successful standard unlock claim preserves the finite ledger identity:
retiring the registry is a ledger frame, and the released amount is minted
through the already-proved primitive mint writer. This is a branch theorem, not
yet a universal `step` theorem. -/
theorem apxUSDLedgerConsistent_claimUnlock_step (s : State) (id : Nat) (caller : Address)
    (s' : State) (h : ApxUSDLedgerConsistent s)
    (hstep : step s (Op.claimUnlock id) caller = some s') :
    ApxUSDLedgerConsistent s' := by
  obtain ⟨owner, amount, cooldownEnd, -, -, -, -, hpost⟩ :=
    step_claimUnlock_ledgerProj s id caller s' hstep
  rw [hpost]
  have hret : ApxUSDLedgerConsistent (retireStandardUnlock s id owner) :=
    apxUSDLedgerConsistent_of_projections_eq (by rfl) (by rfl) h
  exact apxUSDLedgerConsistent_mint _ owner amount hret

/-- Local inversion for the flexible claim branch. The mint amount is the
post-fee amount computed by `flexibleUnlockFee`, exactly as in `step`. -/
private theorem step_flexibleClaimUnlock_ledgerProj (s : State) (id : Nat)
    (caller : Address) (s' : State)
    (h : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      requestTime + minFlexibleClaim ≤ s.now ∧
      s' = mintApxUSD (retireFlexibleUnlock s id) owner
        (amount - amount * flexibleUnlockFee requestTime s.now / 10000) := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount requestTime cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · exact ⟨owner, amount, requestTime, cooldownEnd, heq, by simp_all, by assumption,
              by omega, (Option.some.inj h).symm⟩
        · exact absurd h (by simp)

/-- A successful flexible unlock claim preserves the finite ledger identity.
The fee-adjusted amount is minted after the flexible registry entry is retired;
both operations are handled by already-proved frame and mint lemmas. -/
theorem apxUSDLedgerConsistent_flexibleClaimUnlock_step
    (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : ApxUSDLedgerConsistent s)
    (hstep : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ApxUSDLedgerConsistent s' := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, -, -, -, -, hpost⟩ :=
    step_flexibleClaimUnlock_ledgerProj s id caller s' hstep
  rw [hpost]
  have hret : ApxUSDLedgerConsistent (retireFlexibleUnlock s id) :=
    apxUSDLedgerConsistent_of_projections_eq (by rfl) (by rfl) h
  exact apxUSDLedgerConsistent_mint _ owner
    (amount - amount * flexibleUnlockFee requestTime s.now / 10000) hret

/-! ## Scoped redemption-burn slice

`redeemApxUSD` has several guards (pause, deny-list, whitelist, market price,
reserve and the post-burn buffer), but its apxUSD ledger effect is still just a
guarded `burnApxUSD`. The local inversion below keeps those operational guards
visible while exposing only the balance bound and the post-state shape needed
by the ledger theorem. -/

private theorem step_redeemApxUSD_ledgerProj (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (h : step s (Op.redeemApxUSD amount) caller = some s') :
    amount ≤ s.apxUSDBal caller ∧
    s' = emitEvent { burnApxUSD s caller amount with
        usdcReserve := (burnApxUSD s caller amount).usdcReserve -
          (amount * s.redemptionValue) / ray
        usdcBal := fun a => if a = caller then
          (burnApxUSD s caller amount).usdcBal a +
            (amount * s.redemptionValue) / ray
          else (burnApxUSD s caller amount).usdcBal a }
      "Redeem" [caller, amount, (amount * s.redemptionValue) / ray] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · exact ⟨by omega, (Option.some.inj h).symm⟩

/-- A successful `redeemApxUSD` preserves the finite ledger identity. Its
reserve payout and event emission are ledger frames; the burn bound comes from
the branch guard and discharges the primitive burn theorem. -/
theorem apxUSDLedgerConsistent_redeemApxUSD_step
    (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : ApxUSDLedgerConsistent s)
    (hstep : step s (Op.redeemApxUSD amount) caller = some s') :
    ApxUSDLedgerConsistent s' := by
  obtain ⟨hle, hpost⟩ := step_redeemApxUSD_ledgerProj s amount caller s' hstep
  rw [hpost]
  exact apxUSDLedgerConsistent_of_projections_eq (by simp [emitEvent]) (by simp [emitEvent])
    (apxUSDLedgerConsistent_burn s caller amount hle h)

/-! ## Scoped RFQ-redemption burn slice -/

private theorem step_executeRFQRedemption_ledgerProj
    (s : State) (user : Address) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.executeRFQRedemption user amount) caller = some s') :
    amount ≤ s.apxUSDBal user ∧
    s' = { burnApxUSD s user amount with
        rfqRequests := fun a => if a = user then
          (burnApxUSD s user amount).rfqRequests a - amount
          else (burnApxUSD s user amount).rfqRequests a
        usdcReserve := (burnApxUSD s user amount).usdcReserve -
          (amount * s.redemptionValue) / ray
        usdcBal := fun a => if a = user then
          (burnApxUSD s user amount).usdcBal a +
            (amount * s.redemptionValue) / ray
          else (burnApxUSD s user amount).usdcBal a } := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · exact ⟨by omega, (Option.some.inj h).symm⟩

/-- A successful RFQ redemption preserves the finite ledger identity. The RFQ
request, reserve and USDC settlement writes do not affect the two apxUSD ledger
projections; the user-side burn is guarded by the request and balance checks. -/
theorem apxUSDLedgerConsistent_executeRFQRedemption_step
    (s : State) (user : Address) (amount : Nat) (caller : Address) (s' : State)
    (h : ApxUSDLedgerConsistent s)
    (hstep : step s (Op.executeRFQRedemption user amount) caller = some s') :
    ApxUSDLedgerConsistent s' := by
  obtain ⟨hle, hpost⟩ :=
    step_executeRFQRedemption_ledgerProj s user amount caller s' hstep
  rw [hpost]
  exact apxUSDLedgerConsistent_of_projections_eq (by rfl) (by rfl)
    (apxUSDLedgerConsistent_burn s user amount hle h)

/-! ## Scoped pool-redemption burn slice -/

private theorem step_poolRedeem_ledgerProj
    (s : State) (amount : Nat) (receiver : Address) (minOut : Nat)
    (caller : Address) (s' : State)
    (h : step s (Op.poolRedeem amount receiver minOut) caller = some s') :
    amount ≤ s.apxUSDBal caller ∧
    s' = { burnApxUSD s caller amount with
      usdcReserve := s.usdcReserve - (amount * s.redemptionValue) / ray
      usdcBal := fun a => if a = receiver then
        s.usdcBal a + (amount * s.redemptionValue) / ray
        else s.usdcBal a } := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · split at h
                · exact absurd h (by simp)
                · exact ⟨by omega, (Option.some.inj h).symm⟩

/-- A successful privileged pool redemption preserves the finite ledger
identity. The receiver's USDC credit and reserve debit are outside the apxUSD
ledger projection; the caller-side burn is guarded by the final branch check. -/
theorem apxUSDLedgerConsistent_poolRedeem_step
    (s : State) (amount : Nat) (receiver : Address) (minOut : Nat)
    (caller : Address) (s' : State) (h : ApxUSDLedgerConsistent s)
    (hstep : step s (Op.poolRedeem amount receiver minOut) caller = some s') :
    ApxUSDLedgerConsistent s' := by
  obtain ⟨hle, hpost⟩ :=
    step_poolRedeem_ledgerProj s amount receiver minOut caller s' hstep
  rw [hpost]
  exact apxUSDLedgerConsistent_of_projections_eq (by rfl) (by rfl)
    (apxUSDLedgerConsistent_burn s caller amount hle h)

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
