/-!
# `CollateralizedDebt` — worked reference for the collateralized-debt invariants

A deliberately tiny **collateralized debt protocol**: users open positions backed by collateral,
borrow against them, interest accrues on the debt, unhealthy positions are liquidated, and a
redemption mechanism buys collateral out of positions in a fixed priority order. That is the shape
shared by CDP stablecoins, borrow/lend markets and any design where per-account solvency — not just
pooled solvency — is the safety property.

The protocol is **fictional**: no real deployment is modelled. It is evidence for the Tier-1-C
invariant family of [`../README.md`](../README.md) (design memo: `docs/06-safety-properties.md`
§8, pattern taxonomy: `docs/08-defi-vuln-patterns.md` §A.7) — a compiled, `sorry`-free reference,
and a regression test for the template.

| Invariant | Theorem(s) here |
|---|---|
| **I16** per-position health on every path | `all_healthy_preserved` (book-wide, exhaustive over `Op`), `redeem_preserves_health` |
| — its supporting lemmas | `healthy_add_coll`, `healthy_sub_debt`, `price_ratio_stable`, `mem_updatePos`, `mem_dropPos`, `mem_insertPos` |
| **I17** liquidation is risk-reducing | `liquidate_requires_unhealthy`, `liquidation_seizure_bounded` |
| **I17c** liquidation has to be worth doing | `liquidation_unprofitable_witness` (**gap-witness**) |
| **I22** bad debt is accounted, never dropped | `liquidation_accounts_shortfall`, `bad_debt_only_from_liquidation`, `unprofitable_liquidation_books_bad_debt` |
| **the oracle boundary of this whole tier** | `oracle_move_enables_full_seizure` (**gap-witness**), `price_move_is_unbounded` |
| **I18** priority-order integrity | `sorted_preserved` (book-wide, exhaustive over `Op`), `redeem_hits_head_only`, `insertPos_sorted` |
| — its supporting lemmas | `sorted_head_le`, `sorted_tail`, `sorted_cons_of_bound`, `sorted_dropPos`, `sorted_updatePos`, `sorted_updateConst`, `sorted_map`, `mem_updateConst`, `lookupPos_mem` |
| **I19** accrual monotone | `index_monotone`, `accrual_never_lowers_debt` |
| **I4** rounding favours the protocol (load-bearing here) | `le_ceilDiv_one_mul` |
| **I21** immutable risk parameter (the dual of the pattern-G gap-witness) | `min_ratio_immutable`, `penalty_immutable` |
| anti-vacuity | `all_healthy_preserved_is_applicable`, `liquidation_is_reachable`, `redemption_is_reachable`, `healthy_position_cannot_be_liquidated` |

**I16 is the point of the whole file.** The Euler-class flaw is an invariant that holds on every
path *but one*; `all_healthy_preserved` establishes that **no** position in the book is left
unhealthy, by `cases op` over the closed `Op`, so a debt-increasing operation that forgot its check
could not compile. Two ops are excluded by name — `accrue` and `setPrice` — and that exclusion is
the design, not a gap: those are exactly the operations that are *supposed* to be able to make a
position liquidatable, and `accrual_never_lowers_debt` proves the direction they move it in.

**Redemption is where I16 stops being bookkeeping.** Redeeming takes collateral *out* of a position,
so unlike repayment it is not obviously health-preserving — and in a design that rounded the debt
reduction *down* it would not be. `redeem_preserves_health` isolates the two things that make it
safe: the debt reduction rounds **up** (I4 — a design choice, baked into `redemptionDebt`) and the
protocol over-collateralizes (`one ≤ minRatio` — a hypothesis the instantiation must discharge).
Round the debt down instead, or drop over-collateralization, and a redeemer can walk a healthy
position into liquidation one redemption at a time.

**An ordering lemma is not an ordering invariant.** `insertPos_sorted` says the *insert helper* is
order-preserving — which is a fact about a list function, not about the protocol: nothing in it stops
a different op from scrambling the book. `sorted_preserved` carries `Sorted` across `step`
exhaustively, so an op that reordered the queue, or inserted at the wrong end, would fail to compile.
The same distinction as I16's book-wide statement, and it costs the same kind of work: a head-bound
lemma and one preservation lemma per list operation the model uses.

**What a safety-only invariant set still misses.** Every theorem above can hold while the protocol
loses money, because safety says which operations are *forbidden* and says nothing about which ones
anybody will *perform*. A liquidator who recovers less than the debt is out of pocket, so the
position is left alone and its shortfall grows with each accrual — `liquidation_unprofitable_witness`
exhibits exactly that state, reachable and permitted. And the shortfall has to land somewhere:
dropping the position from the book without booking it (which is what the first version of this file
did) is a silent write-off that no other invariant here would have caught. I22 makes the accounting
explicit and proves no other op can create bad debt.

**I21 is worth lifting even on its own.** Pattern G in `docs/08` says: where an economically
sensitive parameter has no enforced bound, witness the reachable bad state. The dual is available
whenever a protocol claims a parameter is fixed — prove there is *no* mutation path at all,
exhaustively over `Op`. That converts a deployment comment into a theorem, and it is cheap.

## What this model deliberately does not have

There is **no counterparty ledger**: the debt token itself is not modelled, so a liquidator's
repayment and a redeemer's payment are not represented — only the effect on the position book and
the collateral leaving it. Everything proved here is a statement about the book. No
value-conservation claim is made or derivable, which is why I20 (socialized-loss pool conservation)
stays schema-only: stating it against this model would be a claim about a half-drawn system.
-/

namespace CollateralizedDebt

abbrev Address := Nat

/-- Fixed-point scale: `one` = 100%. -/
def one : Nat := 10000

/-- Ceiling division — the protocol-favourable direction (I4) wherever a user's obligation is
    computed from a quantity they chose. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The rounding fact the redemption proof rests on: a ceiling-divided obligation is never smaller
    than the value it was derived from. Rounding the other way is exactly the leak `docs/08`
    pattern C describes. -/
theorem le_ceilDiv_one_mul (a : Nat) : a ≤ ceilDiv a one * one := by
  unfold ceilDiv one
  have h1 := Nat.div_add_mod (a + 10000 - 1) 10000
  have h2 := Nat.mod_lt (a + 10000 - 1) (by omega : 0 < 10000)
  omega

/-- A borrowing position. `debt` is the current amount owed — `accrue` grows it directly. `rate` is
    the position's borrow rate and also its **priority key**: redemption consumes positions in
    ascending `rate` order, so the book is kept sorted. -/
structure Position where
  id    : Nat
  owner : Address
  coll  : Nat
  debt  : Nat
  rate  : Nat
deriving DecidableEq, Inhabited

structure State where
  price     : Nat
  /-- The minimum collateral ratio. Claimed immutable at deployment — `min_ratio_immutable`
      turns that claim into a theorem. -/
  minRatio  : Nat
  /-- Cumulative interest index; only ever rises. Recorded so I19 has something to be monotone in. -/
  index     : Nat
  /-- Extra collateral a liquidator may seize on top of the debt value, scaled by `one`. -/
  penalty   : Nat
  /-- Sorted ascending by `rate`; redemption consumes from the head. -/
  positions : List Position
  nextId    : Nat
  /-- Collateral paid out of the book, per address (to liquidators and redeemers). -/
  collOut   : Address → Nat
  /-- Debt a liquidation could not recover from the position's collateral. Without this field the
      shortfall would simply vanish when the position is dropped — see `I22` below. -/
  badDebt   : Nat
deriving Inhabited

inductive Op
  | setPrice (p : Nat)
  /-- Interest accrues: the index rises by `k` and every position's debt grows with it. -/
  | accrue (k : Nat)
  | openPosition (coll debt rate : Nat)
  | addCollateral (id amount : Nat)
  | borrow (id amount : Nat)
  | repay (id amount : Nat)
  | withdrawCollateral (id amount : Nat)
  | liquidate (id : Nat)
  /-- Buy `amount` of collateral out of the head position, at the front of the priority order,
      against a ceiling-rounded reduction of its debt. -/
  | redeem (amount : Nat)
deriving DecidableEq

/-- `p` is adequately collateralized: `debt · minRatio ≤ coll · price`, written multiplicatively so
    no division enters the invariant. -/
def Healthy (s : State) (p : Position) : Prop :=
  p.debt * s.minRatio ≤ p.coll * s.price

/-- Every position in the book is healthy. -/
def AllHealthy (s : State) : Prop := ∀ p ∈ s.positions, Healthy s p

/-- The protocol over-collateralizes. Required by `redeem_preserves_health`, and true of every CDP
    design by construction — but state it, do not assume it. -/
def OverCollateralized (s : State) : Prop := one ≤ s.minRatio

/-- The book is sorted ascending by `rate`: the redemption priority order. -/
def Sorted : List Position → Prop
  | []           => True
  | [_]          => True
  | p :: q :: rs => p.rate ≤ q.rate ∧ Sorted (q :: rs)

def lookupPos : List Position → Nat → Option Position
  | [],      _  => none
  | p :: ps, i  => if p.id = i then some p else lookupPos ps i

def updatePos (f : Position → Position) : List Position → Nat → List Position
  | [],      _ => []
  | p :: ps, i => if p.id = i then f p :: ps else p :: updatePos f ps i

def dropPos : List Position → Nat → List Position
  | [],      _ => []
  | p :: ps, i => if p.id = i then ps else p :: dropPos ps i

/-- Insert keeping `Sorted` (ascending by `rate`). -/
def insertPos (p : Position) : List Position → List Position
  | []      => [p]
  | q :: qs => if p.rate ≤ q.rate then p :: q :: qs else q :: insertPos p qs

/-- Collateral a liquidator receives for clearing `p`: the debt value plus the penalty, capped by
    what the position actually holds. -/
def seizure (s : State) (p : Position) : Nat :=
  min p.coll (p.debt * (one + s.penalty) / one * one / s.price)

/-- The seized collateral valued in debt units — what the liquidator actually recovers. -/
def seizureValue (s : State) (p : Position) : Nat := seizure s p * s.price / one

/-- Debt cleared by buying `amount` of collateral at the current price. Rounded **up**: the
    redeemer never gets collateral cheaper than the book's own valuation. -/
def redemptionDebt (s : State) (amount : Nat) : Nat := ceilDiv (amount * s.price) one

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.setPrice p =>
    if p = 0 then none else some { s with price := p }
  | Op.accrue k =>
    some { s with
      index     := s.index + k
      positions := s.positions.map (fun p => { p with debt := p.debt + p.debt * k / one }) }
  | Op.openPosition coll debt rate =>
    let p : Position := { id := s.nextId, owner := caller, coll := coll, debt := debt, rate := rate }
    -- the health check the whole family is about
    if ¬ (debt * s.minRatio ≤ coll * s.price) then none
    else some { s with positions := insertPos p s.positions, nextId := s.nextId + 1 }
  | Op.addCollateral id amount =>
    match lookupPos s.positions id with
    | none   => none
    | some _ => some { s with positions := updatePos (fun p => { p with coll := p.coll + amount })
                                                     s.positions id }
  | Op.borrow id amount =>
    match lookupPos s.positions id with
    | none   => none
    | some p =>
      if p.owner ≠ caller then none
      else
        let p' : Position := { p with debt := p.debt + amount }
        if ¬ (p'.debt * s.minRatio ≤ p'.coll * s.price) then none
        else some { s with positions := updatePos (fun _ => p') s.positions id }
  | Op.repay id amount =>
    match lookupPos s.positions id with
    | none   => none
    | some _ => some { s with positions := updatePos (fun q => { q with debt := q.debt - amount })
                                                     s.positions id }
  | Op.withdrawCollateral id amount =>
    match lookupPos s.positions id with
    | none   => none
    | some p =>
      if p.owner ≠ caller then none
      else if p.coll < amount then none
      else
        let p' : Position := { p with coll := p.coll - amount }
        if ¬ (p'.debt * s.minRatio ≤ p'.coll * s.price) then none
        else some { s with positions := updatePos (fun _ => p') s.positions id }
  | Op.liquidate id =>
    match lookupPos s.positions id with
    | none   => none
    | some p =>
      -- only an unhealthy position may be liquidated
      if p.debt * s.minRatio ≤ p.coll * s.price then none
      else some { s with
        positions := dropPos s.positions id
        collOut   := fun a => if a = caller then s.collOut a + seizure s p else s.collOut a
        -- the position leaves the book; whatever its collateral could not cover has to land
        -- somewhere, or the protocol has quietly written off debt it still owes against
        badDebt   := s.badDebt + (p.debt - seizureValue s p) }
  | Op.redeem amount =>
    match s.positions with
    | []      => none
    | p :: ps =>
      -- priority order: only the head is redeemable
      if p.coll < amount then none
      else if p.debt < redemptionDebt s amount then none
      else some { s with
        positions := { p with coll := p.coll - amount
                            , debt := p.debt - redemptionDebt s amount } :: ps
        collOut   := fun a => if a = caller then s.collOut a + amount else s.collOut a }

def execTrace (s : State) : List (Op × Address) → State
  | []           => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-! ## I21 — immutable risk parameter (the dual of the pattern-G gap-witness)

Where pattern G says "no bound is enforced, so witness the bad state", the dual applies whenever a
protocol *claims* a parameter is fixed: prove there is no mutation path at all. Exhaustive over the
closed `Op`, so a future op that quietly gained a setter would break this proof rather than ship. -/

/-- **I21.** No operation, by any caller, changes the minimum collateral ratio. -/
theorem min_ratio_immutable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.minRatio = s.minRatio := by
  cases op <;> simp only [step] at h <;> repeat' split at h
  all_goals (try simp at h)
  all_goals first
    | rfl
    | (subst h; rfl)
    | (injection h with e; subst e; rfl)

/-- The liquidation penalty is likewise fixed; the same one-line recipe extends to every parameter
    a deployment calls immutable. -/
theorem penalty_immutable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.penalty = s.penalty := by
  cases op <;> simp only [step] at h <;> repeat' split at h
  all_goals (try simp at h)
  all_goals first
    | rfl
    | (subst h; rfl)
    | (injection h with e; subst e; rfl)

/-! ## I19 — accrual monotonicity -/

/-- **I19.** The interest index never decreases. -/
theorem index_monotone (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s.index ≤ s'.index := by
  cases op <;> simp only [step] at h <;> repeat' split at h
  all_goals (try simp at h)
  all_goals (try subst h)
  all_goals first
    | exact Nat.le_refl _
    | exact Nat.le_add_right _ _
    | omega

/-- Accrual moves health in one direction only: every position's debt grows, so accrual can create
    liquidatable positions but never cure them. This is why `accrue` is excluded from
    `all_healthy_preserved` — the exclusion is the design, not a gap.

    **The correspondence is pinned.** An earlier form of this concluded
    `∃ p ∈ s.positions, p.debt ≤ q.debt` — an existential over the *whole* book, which a single
    zero-debt position discharges for every `q`, saying nothing about the position `q` came
    from. That is the same defect the `Sorted` review caught one section down: a statement that
    holds for a reason other than the one claimed. The book is rebuilt by `List.map`, so name
    the map and quantify over the pre-image. -/
theorem accrual_never_lowers_debt (s : State) (k : Nat) (c : Address) (s' : State)
    (h : step s (Op.accrue k) c = some s') :
    s'.positions = s.positions.map (fun p => { p with debt := p.debt + p.debt * k / one }) ∧
    ∀ p ∈ s.positions, p.debt ≤ ({ p with debt := p.debt + p.debt * k / one } : Position).debt := by
  simp only [step] at h
  injection h with e
  subst e
  exact ⟨rfl, fun _ _ => Nat.le_add_right _ _⟩

/-- Call-site form of the above: the position an accrued entry came from carries no more debt
    than the entry does. -/
theorem accrual_never_lowers_debt_pointwise (s : State) (k : Nat) (c : Address) (s' : State)
    (h : step s (Op.accrue k) c = some s') (q : Position) (hq : q ∈ s'.positions) :
    ∃ p ∈ s.positions, q = { p with debt := p.debt + p.debt * k / one } ∧ p.debt ≤ q.debt := by
  obtain ⟨hmap, -⟩ := accrual_never_lowers_debt s k c s' h
  rw [hmap, List.mem_map] at hq
  obtain ⟨p, hp, hpq⟩ := hq
  exact ⟨p, hp, hpq.symm, hpq ▸ Nat.le_add_right _ _⟩

/-! ## I16 — per-position health on every path -/

/-- More collateral never hurts. -/
theorem healthy_add_coll (s : State) (p : Position) (d : Nat) (h : Healthy s p) :
    Healthy s { p with coll := p.coll + d } := by
  simp only [Healthy] at h ⊢
  exact Nat.le_trans h (Nat.mul_le_mul_right s.price (Nat.le_add_right _ _))

/-- Less debt never hurts. -/
theorem healthy_sub_debt (s : State) (p : Position) (d : Nat) (h : Healthy s p) :
    Healthy s { p with debt := p.debt - d } := by
  simp only [Healthy] at h ⊢
  exact Nat.le_trans (Nat.mul_le_mul_right s.minRatio (Nat.sub_le _ _)) h

/-- **The redemption case, stated on its own because it is the interesting one.** Buying collateral
    out of a position removes backing, so health is *not* automatic — it holds exactly because the
    debt reduction rounds up (I4) and the protocol over-collateralizes. Round the debt down instead,
    or drop `OverCollateralized`, and a redeemer can walk a healthy position into liquidation. -/
theorem redeem_preserves_health (s : State) (p : Position) (amount : Nat)
    (hoc : OverCollateralized s) (hp : Healthy s p) :
    Healthy s { p with coll := p.coll - amount, debt := p.debt - redemptionDebt s amount } := by
  simp only [Healthy] at hp ⊢
  have hround : amount * s.price ≤ redemptionDebt s amount * one :=
    le_ceilDiv_one_mul (amount * s.price)
  have hba : amount * s.price ≤ redemptionDebt s amount * s.minRatio :=
    Nat.le_trans hround (Nat.mul_le_mul_left _ hoc)
  rw [Nat.sub_mul, Nat.sub_mul]
  exact Nat.le_trans (Nat.sub_le_sub_left hba _) (Nat.sub_le_sub_right hp _)

theorem mem_dropPos {q : Position} : ∀ (l : List Position) (i : Nat), q ∈ dropPos l i → q ∈ l
  | [],      _, hm => by simp [dropPos] at hm
  | p :: ps, i, hm => by
    simp only [dropPos] at hm
    split at hm
    · exact List.mem_cons_of_mem _ hm
    · rcases List.mem_cons.mp hm with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dropPos ps i h)

theorem mem_updatePos {q : Position} {f : Position → Position} :
    ∀ (l : List Position) (i : Nat), q ∈ updatePos f l i → q ∈ l ∨ ∃ r ∈ l, q = f r
  | [],      _, hm => by simp [updatePos] at hm
  | p :: ps, i, hm => by
    simp only [updatePos] at hm
    split at hm
    · rcases List.mem_cons.mp hm with h | h
      · exact Or.inr ⟨p, List.mem_cons_self, h⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp hm with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · rcases mem_updatePos ps i h with h' | ⟨r, hr, he⟩
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, he⟩

theorem mem_insertPos {q p : Position} :
    ∀ l : List Position, q ∈ insertPos p l → q = p ∨ q ∈ l
  | [],      hm => by simpa [insertPos] using hm
  | r :: rs, hm => by
    simp only [insertPos] at hm
    split at hm
    · rcases List.mem_cons.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases List.mem_cons.mp hm with h | h
      · exact Or.inr (h ▸ List.mem_cons_self)
      · rcases mem_insertPos rs h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem _ h')

/-- Ops that may legitimately make a position liquidatable — the honest exclusion list. -/
def IsRiskSource : Op → Prop
  | Op.accrue _   => True
  | Op.setPrice _ => True
  | _             => False

/-- The pricing inputs a health check reads are untouched by every non-risk-source op, so a
    position healthy before such an op is healthy after it under the *same* reading. -/
theorem price_ratio_stable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hsafe : ¬ IsRiskSource op) :
    s'.price = s.price ∧ s'.minRatio = s.minRatio := by
  cases op
  case setPrice p => exact absurd trivial hsafe
  case accrue k => exact absurd trivial hsafe
  all_goals (
    simp only [step] at h
    repeat' split at h
    all_goals (try simp at h)
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (subst h; exact ⟨rfl, rfl⟩)
      | (obtain ⟨-, e⟩ := h; subst e; exact ⟨rfl, rfl⟩)
      | (injection h with e; subst e; exact ⟨rfl, rfl⟩))

/-- **I16.** Every operation other than the two named risk sources preserves the health of
    **every** position in the book. Exhaustive over the closed `Op`: this is the theorem an
    Euler-class "one path forgot the check" defect cannot survive.

    `OverCollateralized` is required, and only by the redemption case — see
    `redeem_preserves_health` for why. It is a hypothesis, not a fact about the model, and an
    instantiation must discharge it. -/
theorem all_healthy_preserved (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hsafe : ¬ IsRiskSource op) (hoc : OverCollateralized s)
    (hs : AllHealthy s) : AllHealthy s' := by
  have hpr := price_ratio_stable s op c s' h hsafe
  have hH : ∀ p, Healthy s p → Healthy s' p := by
    intro p hp
    simp only [Healthy] at hp ⊢
    rw [hpr.1, hpr.2]
    exact hp
  intro q hq
  cases op with
  | setPrice p => exact absurd trivial hsafe
  | accrue k => exact absurd trivial hsafe
  | openPosition coll debt rate =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hg
      injection h with e; subst e
      rcases mem_insertPos _ hq with he | hm
      · subst he
        refine hH _ ?_
        simp only [Healthy]
        exact Decidable.not_not.mp hg
      · exact hH _ (hs _ hm)
  | addCollateral id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with e; subst e
      rcases mem_updatePos _ _ hq with hm | ⟨r, hr, he⟩
      · exact hH _ (hs _ hm)
      · subst he; exact hH _ (healthy_add_coll _ _ _ (hs _ hr))
  | borrow id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i hg
          injection h with e; subst e
          rcases mem_updatePos _ _ hq with hm | ⟨r, hr, he⟩
          · exact hH _ (hs _ hm)
          · subst he
            refine hH _ ?_
            simp only [Healthy]
            exact Decidable.not_not.mp hg
  | repay id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with e; subst e
      rcases mem_updatePos _ _ hq with hm | ⟨r, hr, he⟩
      · exact hH _ (hs _ hm)
      · subst he; exact hH _ (healthy_sub_debt _ _ _ (hs _ hr))
  | withdrawCollateral id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i hg
            injection h with e; subst e
            rcases mem_updatePos _ _ hq with hm | ⟨r, hr, he⟩
            · exact hH _ (hs _ hm)
            · subst he
              refine hH _ ?_
              simp only [Healthy]
              exact Decidable.not_not.mp hg
  | liquidate id =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · injection h with e; subst e
        exact hH _ (hs _ (mem_dropPos _ _ hq))
  | redeem amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i p ps hq' _ hdd
          injection h with e; subst e
          rcases List.mem_cons.mp hq with he | hm
          · subst he
            exact hH _ (redeem_preserves_health s p amount hoc
              (hs _ (hq' ▸ List.mem_cons_self)))
          · exact hH _ (hs _ (hq' ▸ List.mem_cons_of_mem _ hm))

/-! ## I17 — liquidation is risk-reducing -/

/-- **I17 (a).** A healthy position cannot be liquidated: the caller must show it is underwater. -/
theorem liquidate_requires_unhealthy (s : State) (id : Nat) (c : Address) (s' : State)
    (p : Position) (hl : lookupPos s.positions id = some p)
    (h : step s (Op.liquidate id) c = some s') : ¬ Healthy s p := by
  simp only [step, hl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hg
    simpa [Healthy] using hg

/-- **I17 (b).** Liquidation cannot enrich the liquidator without bound: the seizure never exceeds
    the collateral actually in the position. An unbounded seizure would be a finding, not a
    theorem — this is the shape pattern G asks for on the penalty parameter. -/
theorem liquidation_seizure_bounded (s : State) (p : Position) : seizure s p ≤ p.coll :=
  Nat.min_le_left _ _

/-! ## I22 — bad debt is accounted, never dropped

The failure that actually ends CDP protocols is not a liquidation that should have been forbidden;
it is a liquidation that was permitted, went ahead, and left a shortfall nobody wrote down. A model
that removes the position and stops looks correct on every other invariant while losing money. -/

/-- **I22 (a).** Liquidating a position books exactly the debt its collateral could not cover.
    Nothing is silently written off. -/
theorem liquidation_accounts_shortfall (s : State) (id : Nat) (c : Address) (s' : State)
    (p : Position) (hl : lookupPos s.positions id = some p)
    (h : step s (Op.liquidate id) c = some s') :
    s'.badDebt = s.badDebt + (p.debt - seizureValue s p) := by
  simp only [step, hl] at h
  split at h
  · exact absurd h (by simp)
  · injection h with e; subst e; simp only

/-- **I22 (b).** No other operation can create bad debt — exhaustive over the closed `Op`, so a
    future op that quietly absorbed a shortfall would break this proof rather than ship. -/
theorem bad_debt_only_from_liquidation (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hnl : ∀ id, op ≠ Op.liquidate id) : s'.badDebt = s.badDebt := by
  cases op with
  | liquidate id => exact absurd rfl (hnl id)
  | _ =>
    simp only [step] at h
    repeat' split at h
    all_goals (try simp at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (injection h with e; subst e; rfl)

/-! ## I18 — priority-order integrity -/

/-- **I18 (a).** Redemption consumes the head of the priority order and nothing else: the tail is
    untouched, so no participant can be jumped over and none can jump the queue. -/
theorem redeem_hits_head_only (s : State) (amount : Nat) (c : Address) (s' : State)
    (p : Position) (ps : List Position) (hq : s.positions = p :: ps)
    (h : step s (Op.redeem amount) c = some s') :
    s'.positions = { p with coll := p.coll - amount
                          , debt := p.debt - redemptionDebt s amount } :: ps := by
  simp only [step, hq] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · injection h with e; subst e; simp only

/-- **I18 (b).** `insertPos` keeps the book ordered, so a newly opened position lands at its
    correct place in the priority order rather than at whichever end its author preferred. -/
theorem insertPos_sorted (p : Position) : ∀ l : List Position, Sorted l → Sorted (insertPos p l)
  | [],      _ => by simp [insertPos, Sorted]
  | [q],     _ => by
    simp only [insertPos]
    split
    · rename_i hle; exact ⟨hle, trivial⟩
    · rename_i hgt
      exact ⟨Nat.le_of_not_le hgt, trivial⟩
  | q :: r :: rs, hs => by
    simp only [insertPos]
    split
    · rename_i hle; exact ⟨hle, hs⟩
    · rename_i hgt
      have hqr : q.rate ≤ r.rate := hs.1
      have htail : Sorted (insertPos p (r :: rs)) := insertPos_sorted p (r :: rs) hs.2
      split
      · rename_i hpr
        exact ⟨Nat.le_of_not_le hgt, hpr, hs.2⟩
      · rename_i hpr
        refine ⟨hqr, ?_⟩
        simpa [insertPos, hpr] using htail

/-! ### I18 (c) — the ordering is a system invariant, not a fact about `insertPos`

`insertPos_sorted` says the insert *helper* is order-preserving. That is not the property an audit
needs: nothing in it prevents a *different* op from scrambling the book. The invariant has to be
carried across `step`, exhaustively, exactly as I16 is. -/

theorem sorted_tail {p : Position} : ∀ {l : List Position}, Sorted (p :: l) → Sorted l
  | [],     _ => trivial
  | _ :: _, h => h.2

/-- The head of a sorted book bounds every element behind it — the fact that makes "dropping an
    element keeps it sorted" work without a transitivity fight at each call site. -/
theorem sorted_head_le : ∀ {p : Position} {l : List Position}, Sorted (p :: l) →
    ∀ q ∈ l, p.rate ≤ q.rate
  | _, [],      _, _, hq => absurd hq (by simp)
  | _, r :: rs, h, q, hq => by
    rcases List.mem_cons.mp hq with he | hm
    · exact he ▸ h.1
    · exact Nat.le_trans h.1 (sorted_head_le h.2 q hm)

theorem sorted_cons_of_bound {p : Position} {l : List Position}
    (hb : ∀ q ∈ l, p.rate ≤ q.rate) (hl : Sorted l) : Sorted (p :: l) := by
  cases l with
  | nil => trivial
  | cons q qs => exact ⟨hb q List.mem_cons_self, hl⟩

theorem sorted_dropPos : ∀ (l : List Position) (i : Nat), Sorted l → Sorted (dropPos l i)
  | [],      _, _ => trivial
  | p :: ps, i, h => by
    simp only [dropPos]
    split
    · exact sorted_tail h
    · exact sorted_cons_of_bound
        (fun q hq => sorted_head_le h q (mem_dropPos ps i hq))
        (sorted_dropPos ps i (sorted_tail h))

theorem sorted_updatePos {f : Position → Position} (hf : ∀ p, (f p).rate = p.rate) :
    ∀ (l : List Position) (i : Nat), Sorted l → Sorted (updatePos f l i)
  | [],      _, _ => trivial
  | p :: ps, i, h => by -- `hf` first here; call sites use `updatePos_sorted` below
    simp only [updatePos]
    split
    · exact sorted_cons_of_bound
        (fun q hq => by rw [hf]; exact sorted_head_le h q hq) (sorted_tail h)
    · exact sorted_cons_of_bound
        (fun q hq => by
          rcases mem_updatePos ps i hq with hm | ⟨r, hr, he⟩
          · exact sorted_head_le h q hm
          · rw [he, hf]; exact sorted_head_le h r hr)
        (sorted_updatePos hf ps i (sorted_tail h))

theorem sorted_map {f : Position → Position} (hf : ∀ p, (f p).rate = p.rate) :
    ∀ l : List Position, Sorted l → Sorted (l.map f)
  | [],      _ => trivial
  | p :: ps, h => by
    simp only [List.map_cons]
    refine sorted_cons_of_bound (fun q hq => ?_) (sorted_map hf ps (sorted_tail h))
    simp only [List.mem_map] at hq
    obtain ⟨r, hr, he⟩ := hq
    rw [hf, ← he, hf]
    exact sorted_head_le h r hr

theorem lookupPos_mem : ∀ (l : List Position) (i : Nat) (r : Position),
    lookupPos l i = some r → r ∈ l
  | [],      _, _, hl => by simp [lookupPos] at hl
  | p :: ps, i, r, hl => by
    simp only [lookupPos] at hl
    split at hl
    · exact (Option.some.inj hl) ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupPos_mem ps i r hl)

/-- Constant replacement rewrites exactly the element `lookupPos` returns, so an element of the
    updated list is either untouched or the replacement itself — and in the latter case a match
    exists. -/
theorem mem_updateConst {q p' : Position} :
    ∀ (l : List Position) (i : Nat), q ∈ updatePos (fun _ => p') l i →
      q ∈ l ∨ (q = p' ∧ ∃ r, lookupPos l i = some r)
  | [],      _, hm => by simp [updatePos] at hm
  | p :: ps, i, hm => by
    simp only [updatePos] at hm
    split at hm
    · rename_i hid
      rcases List.mem_cons.mp hm with he | h
      · exact Or.inr ⟨he, p, by simp only [lookupPos, if_pos hid]⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rename_i hid
      rcases List.mem_cons.mp hm with he | h
      · exact Or.inl (he ▸ List.mem_cons_self)
      · rcases mem_updateConst ps i h with h' | ⟨he, r, hr⟩
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr ⟨he, r, by simp only [lookupPos, if_neg hid]; exact hr⟩

/-- Constant replacement (`fun _ => p'`) does not preserve rate pointwise, so the rate-preserving
    lemma above does not apply — and it does not need to. `updatePos` rewrites only the first `id`
    match, which is exactly the element `lookupPos` returns, so the side condition has to talk about
    that one element only. -/
theorem sorted_updateConst {p' : Position} :
    ∀ (l : List Position) (i : Nat), Sorted l →
      (∀ r, lookupPos l i = some r → r.rate = p'.rate) → Sorted (updatePos (fun _ => p') l i)
  | [],      _, _, _  => trivial
  | p :: ps, i, h, hr => by
    simp only [updatePos]
    split
    · rename_i hid
      refine sorted_cons_of_bound (fun q hq => ?_) (sorted_tail h)
      rw [← hr p (by simp only [lookupPos, if_pos hid])]
      exact sorted_head_le h q hq
    · rename_i hid
      have hr' : ∀ r, lookupPos ps i = some r → r.rate = p'.rate := by
        intro r hrr
        exact hr r (by simp only [lookupPos, if_neg hid]; exact hrr)
      refine sorted_cons_of_bound (fun q hq => ?_) (sorted_updateConst ps i (sorted_tail h) hr')
      rcases mem_updateConst ps i hq with hm | ⟨he, r, hrr⟩
      · exact sorted_head_le h q hm
      · rw [he, ← hr' r hrr]
        exact sorted_head_le h r (lookupPos_mem ps i r hrr)

/-- Call-site friendly forms: with the side condition last, the expected type fixes `f` before it
    has to be elaborated. -/
theorem updatePos_sorted (l : List Position) (i : Nat) (h : Sorted l)
    {f : Position → Position} (hf : ∀ p, (f p).rate = p.rate) : Sorted (updatePos f l i) :=
  sorted_updatePos hf l i h

theorem map_sorted (l : List Position) (h : Sorted l)
    {f : Position → Position} (hf : ∀ p, (f p).rate = p.rate) : Sorted (l.map f) :=
  sorted_map hf l h

/-- **I18 (c).** Every operation keeps the book in priority order. Exhaustive over the closed `Op`:
    an op that reordered the queue — or inserted at the wrong end — could not compile. Together with
    `redeem_hits_head_only` this is what makes "the advertised order is enforced" a claim about the
    protocol rather than about a list helper. -/
theorem sorted_preserved (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hs : Sorted s.positions) : Sorted s'.positions := by
  cases op with
  | setPrice p =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with e; subst e; exact hs
  | accrue k =>
    simp only [step] at h
    injection h with e; subst e
    exact map_sorted _ hs (fun _ => rfl)
  | openPosition coll debt rate =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with e; subst e; exact insertPos_sorted _ _ hs
  | addCollateral id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with e; subst e; exact updatePos_sorted _ _ hs (fun _ => rfl)
  | borrow id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i p hlk _ _
          injection h with e; subst e
          refine sorted_updateConst _ _ hs (fun r hrr => ?_)
          rw [hlk] at hrr
          exact (Option.some.inj hrr) ▸ rfl
  | repay id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with e; subst e; exact updatePos_sorted _ _ hs (fun _ => rfl)
  | withdrawCollateral id amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i p hlk _ _ _
            injection h with e; subst e
            refine sorted_updateConst _ _ hs (fun r hrr => ?_)
            rw [hlk] at hrr
            exact (Option.some.inj hrr) ▸ rfl
  | liquidate id =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · injection h with e; subst e; exact sorted_dropPos _ _ hs
  | redeem amount =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i p ps hq' _ _
          have hsp : Sorted (p :: ps) := by rw [hq'] at hs; exact hs
          injection h with e; subst e
          simp only
          exact sorted_cons_of_bound (fun q hq => sorted_head_le hsp q hq) (sorted_tail hsp)

/-! ## Anti-vacuity guards -/

/-- A book with one position that the price move has put underwater. -/
def stressed : State where
  price     := one
  minRatio  := 15000
  index     := one
  penalty   := 1000
  positions := [{ id := 0, owner := 1, coll := 100, debt := 90, rate := 500 }]
  nextId    := 1
  collOut   := fun _ => 0
  badDebt   := 0

/-- The same book at a ratio that leaves the position healthy — something to redeem against. -/
def solvent : State := { stressed with minRatio := 10000 }

/-- **Anti-vacuity (liquidation).** Without this, `liquidate_requires_unhealthy` and
    `liquidation_seizure_bounded` could both hold of an operation that never succeeds. Address `7`
    — not the owner — clears the position and is credited the seizure. -/
theorem liquidation_is_reachable :
    (execTrace stressed [(Op.liquidate 0, 7)]).positions = [] ∧
    0 < (execTrace stressed [(Op.liquidate 0, 7)]).collOut 7 := by
  refine ⟨?_, ?_⟩ <;>
    simp [execTrace, step, stressed, lookupPos, dropPos, seizure, one]

/-- Control: the same liquidation is *rejected* while the position is healthy, so the theorem above
    is about the position's state and not about `liquidate` being unconditionally open. -/
theorem healthy_position_cannot_be_liquidated :
    step { stressed with minRatio := 10000 } (Op.liquidate 0) 7 = none := by
  simp [step, stressed, lookupPos, one]

/-! ## I17 (c) — liquidation has to be worth doing

`liquidate_requires_unhealthy` says an unhealthy position *may* be cleared. It does not say anyone
*will* clear it: a liquidator who recovers less than the debt is out of pocket, so in a real market
the position is simply left alone and the shortfall grows with every accrual. Permission without
incentive is how bad debt accumulates, and it is invisible to every safety-only invariant. -/

/-- A position whose collateral has fallen well below its debt. -/
def deeplyUnderwater : State :=
  { stressed with positions := [{ id := 0, owner := 1, coll := 50, debt := 90, rate := 500 }] }

/-- **I17 (c) — gap-witness.** A reachable state where liquidation is permitted (the position is
    unhealthy) but recovers strictly less than the debt, so no rational liquidator performs it and
    the position persists. Report it with the fix: a liquidation reserve, a backstop bidder, or a
    penalty floor that keeps the seizure worth more than the debt across the intended price range. -/
theorem liquidation_unprofitable_witness :
    ∃ p, lookupPos deeplyUnderwater.positions 0 = some p ∧
      ¬ Healthy deeplyUnderwater p ∧
      seizureValue deeplyUnderwater p < p.debt := by
  refine ⟨{ id := 0, owner := 1, coll := 50, debt := 90, rate := 500 }, ?_, ?_, ?_⟩ <;>
    simp [deeplyUnderwater, stressed, lookupPos, Healthy, seizureValue, seizure, one]

/-- …and the shortfall it would leave is booked rather than lost: clearing it anyway raises
    `badDebt` by exactly the uncovered amount. -/
theorem unprofitable_liquidation_books_bad_debt :
    (execTrace deeplyUnderwater [(Op.liquidate 0, 7)]).badDebt = 40 := by
  simp [execTrace, step, deeplyUnderwater, stressed, lookupPos, dropPos, seizureValue, seizure, one]

/-! ### The price input is outside every invariant above

`setPrice` is unauthenticated and unbounded here — the maximally adversarial oracle, and the right
default, because an invariant that only holds for honest prices should say so. What follows is the
boundary of this whole tier, stated as a witness rather than a caveat: I16 through I22 all continue
to hold while a healthy position is taken apart, because each of them is a statement about the
transition system *given* its inputs, and the price is an input.

This is pattern A in `docs/08` — the largest loss category — and Tier 1-C does not address it. The
tool for it is Tier 3: an oracle damage bound, not an oracle correctness proof. -/

/-- **Oracle gap-witness.** One price move turns a healthy position into a fully seizable one. The
    liquidator takes **all** of the collateral (the seizure formula caps at the position's balance,
    and the manipulated price pushes it past that cap), the owner is left with nothing, and the
    protocol still books bad debt because the seized collateral is valued at the manipulated price.

    Every Tier 1-C theorem holds throughout: the liquidation was permitted because the position
    genuinely was unhealthy *at the price the contract was told*. Report this as the scope boundary
    of any audit citing I16–I22 — the guarantees are conditional on the price input, and bounding
    that is a separate exercise. -/
theorem oracle_move_enables_full_seizure :
    let victim : Position := { id := 0, owner := 1, coll := 100, debt := 90, rate := 500 }
    -- healthy at the honest price
    Healthy solvent victim ∧
    -- and after a single price move, liquidation takes the entire collateral
    (execTrace solvent [(Op.setPrice 5000, 9), (Op.liquidate 0, 7)]).collOut 7 = 100 ∧
    (execTrace solvent [(Op.setPrice 5000, 9), (Op.liquidate 0, 7)]).positions = [] ∧
    -- while the protocol books bad debt on top, because the seizure is valued at the moved price
    (execTrace solvent [(Op.setPrice 5000, 9), (Op.liquidate 0, 7)]).badDebt = 40 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [solvent, stressed, execTrace, step, Healthy, lookupPos, dropPos, seizure, seizureValue,
          one]

/-- There is also no bound on how far one update may move the price — pattern G applied to the
    oracle. A design that wants one states a maximum per-update deviation; this one does not, and
    the absence is what makes the witness above a single step rather than a long grind. -/
theorem price_move_is_unbounded (p : Nat) (hp : p ≠ 0) (c : Address) :
    (step solvent (Op.setPrice p) c).isSome := by
  simp [step, hp]

/-- **Anti-vacuity for I16 itself.** `all_healthy_preserved` carries three hypotheses; if no state
    satisfied all of them alongside a successful step, the theorem would be about an empty premise
    set and would prove nothing. It is applicable: `solvent` is over-collateralized, its whole book
    is healthy, `redeem` is not a risk source, and the step succeeds — which is precisely the
    configuration the theorem talks about. A guard like this belongs next to every invariant whose
    hypotheses are not obviously satisfiable. -/
theorem all_healthy_preserved_is_applicable :
    ¬ IsRiskSource (Op.redeem 10) ∧ OverCollateralized solvent ∧ AllHealthy solvent ∧
      (step solvent (Op.redeem 10) 7).isSome := by
  refine ⟨by simp [IsRiskSource], by simp [OverCollateralized, solvent, stressed, one], ?_, ?_⟩
  · intro p hp
    simp only [solvent, stressed] at hp
    rcases List.mem_cons.mp hp with he | hm
    · subst he; simp [Healthy, solvent, stressed, one]
    · simp at hm
  · simp [step, solvent, stressed, redemptionDebt, ceilDiv, one]

/-- **Anti-vacuity (redemption).** `redeem_preserves_health` and `redeem_hits_head_only` are both
    conditioned on a redemption succeeding. It does — and collateral genuinely leaves the position
    for the redeemer, so the operation is an exchange rather than a free write-off of debt. -/
theorem redemption_is_reachable :
    (execTrace solvent [(Op.redeem 10, 7)]).collOut 7 = 10 ∧
    (execTrace solvent [(Op.redeem 10, 7)]).positions
      = [{ id := 0, owner := 1, coll := 90, debt := 80, rate := 500 }] := by
  refine ⟨?_, ?_⟩ <;>
    simp [execTrace, step, solvent, stressed, redemptionDebt, ceilDiv, one]

end CollateralizedDebt
