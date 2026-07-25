/-!
# `CollateralizedDebt` — worked reference for the collateralized-debt invariants

A deliberately tiny **collateralized debt protocol**: users open positions backed by collateral,
borrow against them, interest accrues, unhealthy positions are liquidated, and a redemption
mechanism repays debt against collateral in a fixed priority order. That is the shape shared by
CDP stablecoins, borrow/lend markets and any design where per-account solvency — not just pooled
solvency — is the safety property.

The protocol is **fictional**: no real deployment is modelled. It is evidence for the Tier-1-C
invariant family of [`../README.md`](../README.md) (design memo: `docs/06-safety-properties.md`
§8, pattern taxonomy: `docs/08-defi-vuln-patterns.md` §A.7) — a compiled, `sorry`-free reference,
and a regression test for the template.

| Invariant | Theorem(s) here |
|---|---|
| **I16** per-position health on every path | `all_healthy_preserved` (book-wide, exhaustive over `Op`), `borrow_requires_health`, `withdraw_requires_health`, supported by `healthy_add_coll`, `healthy_sub_debt`, `price_index_stable`, `mem_updatePos`, `mem_dropPos`, `mem_insertPos` |
| **I17** liquidation is risk-reducing | `liquidate_requires_unhealthy`, `liquidation_seizure_bounded` |
| **I18** priority-order integrity | `redeem_hits_head_only`, `insertPos_sorted` |
| **I19** accrual monotone | `index_monotone`, `accrual_never_improves_health` |
| **I21** immutable risk parameter (the dual of the pattern-G gap-witness) | `min_ratio_immutable`, `penalty_immutable` |
| anti-vacuity | `liquidation_is_reachable`, `healthy_position_cannot_be_liquidated` |

**I16 is the point of the whole file.** The Euler-class flaw is an invariant that holds on every
path *but one*; here `all_healthy_preserved` is a `cases op` over the closed `Op` establishing that
**no** position in the book is left unhealthy, so a borrow-like operation that forgot its health
check could not compile. Two ops are excluded by name
— `accrue` and `setPrice` — and that exclusion is not a weakness but the model being honest:
those are exactly the operations that are *supposed* to be able to make a position liquidatable,
and `accrual_never_improves_health` proves the direction they move it in.

**I21 is worth lifting even on its own.** Pattern G in `docs/08` says: where an economically
sensitive parameter has no enforced bound, witness the reachable bad state. The dual is available
whenever a protocol claims a parameter is fixed — prove there is *no* mutation path at all,
exhaustively over `Op`. That converts a deployment comment into a theorem, and it is cheap.
-/

namespace CollateralizedDebt

abbrev Address := Nat

/-- Fixed-point scale: `one` = 100%. -/
def one : Nat := 10000

/-- A borrowing position. `rate` is the position's borrow rate and also its **priority key**:
    redemption consumes positions in ascending `rate` order, so `positions` is kept sorted. -/
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
  /-- Interest index, scaled by `one`; only ever rises. -/
  index     : Nat
  /-- Extra collateral a liquidator may seize, on top of the debt value, scaled by `one`. -/
  penalty   : Nat
  /-- Sorted ascending by `rate`; redemption consumes from the head. -/
  positions : List Position
  nextId    : Nat
  seized    : Address → Nat
deriving Inhabited

inductive Op
  | setPrice (p : Nat)
  /-- Interest accrues: the index rises by `k`. -/
  | accrue (k : Nat)
  | openPosition (coll debt rate : Nat)
  | addCollateral (id amount : Nat)
  | borrow (id amount : Nat)
  | repay (id amount : Nat)
  | withdrawCollateral (id amount : Nat)
  | liquidate (id : Nat)
  /-- Repay the head position's debt against its collateral, at the front of the priority order. -/
  | redeem (amount : Nat)
deriving DecidableEq

/-- Debt marked to the current index. -/
def owed (s : State) (p : Position) : Nat := p.debt * s.index / one

/-- `p` is adequately collateralized: `owed · minRatio ≤ coll · price`, written
    multiplicatively so no division enters the invariant. -/
def Healthy (s : State) (p : Position) : Prop :=
  owed s p * s.minRatio ≤ p.coll * s.price

/-- Every position in the book is healthy. -/
def AllHealthy (s : State) : Prop := ∀ p ∈ s.positions, Healthy s p

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

/-- Collateral a liquidator receives for clearing `p`: the debt value plus the penalty,
    capped by what the position actually holds. -/
def seizure (s : State) (p : Position) : Nat :=
  min p.coll (owed s p * (one + s.penalty) / one * one / s.price)

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.setPrice p =>
    if p = 0 then none else some { s with price := p }
  | Op.accrue k =>
    some { s with index := s.index + k }
  | Op.openPosition coll debt rate =>
    let p : Position := { id := s.nextId, owner := caller, coll := coll, debt := debt, rate := rate }
    -- the health check the whole family is about
    if ¬ (debt * s.index / one * s.minRatio ≤ coll * s.price) then none
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
        if ¬ (owed s p' * s.minRatio ≤ p'.coll * s.price) then none
        else some { s with positions := updatePos (fun _ => p') s.positions id }
  | Op.repay id amount =>
    match lookupPos s.positions id with
    | none   => none
    | some p => some { s with positions := updatePos (fun q => { q with debt := q.debt - amount })
                                                     s.positions id }
  | Op.withdrawCollateral id amount =>
    match lookupPos s.positions id with
    | none   => none
    | some p =>
      if p.owner ≠ caller then none
      else if p.coll < amount then none
      else
        let p' : Position := { p with coll := p.coll - amount }
        if ¬ (owed s p' * s.minRatio ≤ p'.coll * s.price) then none
        else some { s with positions := updatePos (fun _ => p') s.positions id }
  | Op.liquidate id =>
    match lookupPos s.positions id with
    | none   => none
    | some p =>
      -- only an unhealthy position may be liquidated
      if owed s p * s.minRatio ≤ p.coll * s.price then none
      else some { s with
        positions := dropPos s.positions id
        seized    := fun a => if a = caller then s.seized a + seizure s p else s.seized a }
  | Op.redeem amount =>
    match s.positions with
    | []      => none
    | p :: ps =>
      -- priority order: only the head is redeemable
      if p.debt < amount then none
      else some { s with positions := { p with debt := p.debt - amount } :: ps }

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

/-- Accrual moves health in one direction only: a position's marked debt never falls, so accrual
    can create liquidatable positions but never cure them. This is why `accrue` is excluded from
    `health_preserved_by_user_ops` — the exclusion is the design, not a gap. -/
theorem accrual_never_improves_health (s : State) (k : Nat) (c : Address) (s' : State)
    (h : step s (Op.accrue k) c = some s') (p : Position) :
    owed s p ≤ owed s' p := by
  simp only [step] at h
  injection h with h
  subst h
  simp only [owed]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left p.debt (by omega))

/-! ## I16 — per-position health on every path

The Euler-class flaw is an invariant that holds on every path but one. Here the health check is
re-established by *each* debt-increasing or collateral-decreasing operation, and `cases op` forces
every branch to discharge. -/

/-- **I16 (a).** `borrow` cannot leave the position underwater — the guard is not optional. -/
theorem borrow_requires_health (s : State) (id amount : Nat) (c : Address) (s' : State) (p : Position)
    (hl : lookupPos s.positions id = some p) (h : step s (Op.borrow id amount) c = some s') :
    Healthy s { p with debt := p.debt + amount } := by
  simp only [step, hl] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i hg
      simp only [Healthy]
      exact Decidable.not_not.mp hg

/-- **I16 (b).** `withdrawCollateral` likewise. -/
theorem withdraw_requires_health (s : State) (id amount : Nat) (c : Address) (s' : State)
    (p : Position) (hl : lookupPos s.positions id = some p)
    (h : step s (Op.withdrawCollateral id amount) c = some s') :
    Healthy s { p with coll := p.coll - amount } := by
  simp only [step, hl] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hg
        simp only [Healthy]
        exact Decidable.not_not.mp hg

/-! ### I16 (c) — the book-wide statement

The per-op guards above say each *touched* position is left healthy. The property that actually
closes the Euler-class hole is the book-wide one: **no user operation leaves any position in the
book unhealthy**, proved by `cases op` so a future debt-increasing op that skips its check cannot
compile. `accrue` and `setPrice` are excluded by name — they are precisely the operations that are
*supposed* to be able to make positions liquidatable. -/

/-- More collateral never hurts. -/
theorem healthy_add_coll (s : State) (p : Position) (d : Nat) (h : Healthy s p) :
    Healthy s { p with coll := p.coll + d } := by
  simp only [Healthy, owed] at h ⊢
  exact Nat.le_trans h (Nat.mul_le_mul_right s.price (Nat.le_add_right _ _))

/-- Less debt never hurts. -/
theorem healthy_sub_debt (s : State) (p : Position) (d : Nat) (h : Healthy s p) :
    Healthy s { p with debt := p.debt - d } := by
  simp only [Healthy, owed] at h ⊢
  exact Nat.le_trans
    (Nat.mul_le_mul_right s.minRatio
      (Nat.div_le_div_right (Nat.mul_le_mul_right s.index (Nat.sub_le _ _)))) h

theorem mem_dropPos {q : Position} : ∀ (l : List Position) (i : Nat), q ∈ dropPos l i → q ∈ l
  | [],      _, hm => by simpa [dropPos] using hm
  | p :: ps, i, hm => by
    simp only [dropPos] at hm
    split at hm
    · exact List.mem_cons_of_mem _ hm
    · rcases List.mem_cons.mp hm with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dropPos ps i h)

theorem mem_updatePos {q : Position} {f : Position → Position} :
    ∀ (l : List Position) (i : Nat), q ∈ updatePos f l i → q ∈ l ∨ ∃ r ∈ l, q = f r
  | [],      _, hm => by simpa [updatePos] using hm
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
theorem price_index_stable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hsafe : ¬ IsRiskSource op) :
    s'.price = s.price ∧ s'.index = s.index := by
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

/-- **I16 (c).** Every operation other than the two named risk sources preserves the health of
    **every** position in the book. Exhaustive over the closed `Op`: this is the theorem an
    Euler-class "one path forgot the check" defect cannot survive. -/
theorem all_healthy_preserved (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hsafe : ¬ IsRiskSource op) (hs : AllHealthy s) :
    AllHealthy s' := by
  have hpi := price_index_stable s op c s' h hsafe
  have hmr := min_ratio_immutable s op c s' h
  have hH : ∀ p, Healthy s p → Healthy s' p := by
    intro p hp
    simp only [Healthy, owed] at hp ⊢
    rw [hpi.1, hpi.2, hmr]
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
        simp only [Healthy, owed]
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
        · rename_i p hlk _ hg
          injection h with e; subst e
          rcases mem_updatePos _ _ hq with hm | ⟨r, hr, he⟩
          · exact hH _ (hs _ hm)
          · subst he
            refine hH _ ?_
            simp only [Healthy, owed]
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
              simp only [Healthy, owed]
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
      · rename_i p ps hq' _
        injection h with e; subst e
        rcases List.mem_cons.mp hq with he | hm
        · subst he
          exact hH _ (healthy_sub_debt _ _ _ (hs _ (hq' ▸ List.mem_cons_self)))
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

/-! ## I18 — priority-order integrity

When a protocol advertises an order — liquidate the worst first, redeem the cheapest first, FIFO —
the order is a safety property: nobody may skip ahead, and nobody may be skipped. -/

/-- **I18 (a).** Redemption consumes the head of the priority order and nothing else: the tail is
    untouched, so no participant can be jumped over and none can jump the queue. -/
theorem redeem_hits_head_only (s : State) (amount : Nat) (c : Address) (s' : State)
    (p : Position) (ps : List Position) (hq : s.positions = p :: ps)
    (h : step s (Op.redeem amount) c = some s') :
    s'.positions = { p with debt := p.debt - amount } :: ps := by
  simp only [step, hq] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; simp only

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

/-! ## Anti-vacuity guard -/

/-- A book with one position that the price move has put underwater. -/
def stressed : State where
  price     := one
  minRatio  := 15000
  index     := one
  penalty   := 1000
  positions := [{ id := 0, owner := 1, coll := 100, debt := 90, rate := 500 }]
  nextId    := 1
  seized    := fun _ => 0

/-- **Anti-vacuity.** `liquidate` is reachable: without this, `liquidate_requires_unhealthy` and
    `liquidation_seizure_bounded` could both hold of an operation that never succeeds. Address `7`
    — not the owner — clears the position and is credited the seizure. -/
theorem liquidation_is_reachable :
    (execTrace stressed [(Op.liquidate 0, 7)]).positions = [] ∧
    0 < (execTrace stressed [(Op.liquidate 0, 7)]).seized 7 := by
  refine ⟨?_, ?_⟩ <;>
    simp [execTrace, step, stressed, lookupPos, dropPos, seizure, owed, one]

/-- Control: the same liquidation is *rejected* while the position is healthy, so the theorem above
    is about the position's state and not about `liquidate` being unconditionally open. -/
theorem healthy_position_cannot_be_liquidated :
    step { stressed with minRatio := 10000 } (Op.liquidate 0) 7 = none := by
  simp [step, stressed, lookupPos, owed, one]

end CollateralizedDebt
