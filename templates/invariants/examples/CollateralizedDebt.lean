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
| **I18** priority-order integrity | `redeem_hits_head_only`, `insertPos_sorted` |
| **I19** accrual monotone | `index_monotone`, `accrual_never_lowers_debt` |
| **I4** rounding favours the protocol (load-bearing here) | `le_ceilDiv_one_mul` |
| **I21** immutable risk parameter (the dual of the pattern-G gap-witness) | `min_ratio_immutable`, `penalty_immutable` |
| anti-vacuity | `liquidation_is_reachable`, `redemption_is_reachable`, `healthy_position_cannot_be_liquidated` |

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
        collOut   := fun a => if a = caller then s.collOut a + seizure s p else s.collOut a }
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
    `all_healthy_preserved` — the exclusion is the design, not a gap. -/
theorem accrual_never_lowers_debt (s : State) (k : Nat) (c : Address) (s' : State)
    (h : step s (Op.accrue k) c = some s') (q : Position) (hq : q ∈ s'.positions) :
    ∃ p ∈ s.positions, p.debt ≤ q.debt := by
  simp only [step] at h
  injection h with e
  subst e
  simp only [List.mem_map] at hq
  obtain ⟨p, hp, hpq⟩ := hq
  refine ⟨p, hp, ?_⟩
  subst hpq
  exact Nat.le_add_right _ _

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

/-- The same book at a ratio that leaves the position healthy — something to redeem against. -/
def solvent : State := { stressed with minRatio := 10000 }

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
