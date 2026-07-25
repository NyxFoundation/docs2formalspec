/-!
# `AsyncQueueVault` — worked reference for the async / queue / signed-value invariants

A deliberately tiny **async redemption vault**: users file a redemption request against a share
balance, the request matures over settlement rounds, and a settler executes it later at a price
that may have moved. That is the shape ERC-7540 standardizes, and the shape LST unstaking queues,
delayed-redemption stablecoins and queued-withdrawal vaults all converge on — the DeFi archetypes
`docs/08-defi-vuln-patterns.md` §A.6 collects.

The protocol itself is **fictional**: no real deployment is modelled here. What it is evidence for
is the Tier-1.5 invariant family of [`../README.md`](../README.md) (design memo:
`docs/06-safety-properties.md` §7) — a compiled, `sorry`-free reference the way
`outputs/apyx/Safety.lean` serves the Tier-1 family, and a regression test for the template.

What it demonstrates, in order:

| Invariant | Theorem(s) here |
|---|---|
| **I12** in-flight conservation | `inflight_conservation`, `tick_settles_exactly`, `partial_tick_leaves_residue` |
| **I10** settlement-timing neutrality | `settle_credits_protocol_favourable_side`, `settler_timing_cannot_gain`, `naive_filing_price_overpays_witness` |
| **I11b** queue capacity griefing | `queue_capacity_griefing_witness` |
| **I15** signed net value | `nat_solvency_is_vacuous`, `insolvency_witness` |

The three model extensions of `docs/06` §7.1 that this file exercises:

* **E1 clock** — `Op.tick` advances a settlement round. Without it none of I10–I12 is stateable.
* **E2 two-phase op + settlement hypothesis** — `Op.enqueue` files a `Request` carrying a price
  snapshot; `Op.settle` executes it later. Crucially `Op.tick` takes a `delivered` argument
  rather than hard-wiring full delivery: conservation then holds *unconditionally*, and only the
  "in-flight drops to zero" half needs the honesty hypothesis (`tick_settles_exactly`), with
  `partial_tick_leaves_residue` showing that hypothesis is load-bearing rather than cosmetic.
* **E4 explicit queue** — `State.pending` is a real FIFO list with a capacity, so starvation and
  occupancy are expressible.

Not exercised here (needs E2's venue split / more model): I13 cross-venue conservation, I14
intent-vs-realized drift. Those stay schema-only until a worked reference exists — see the
status note in `docs/06` §7.
-/

namespace AsyncQueueVault

abbrev Address := Nat

/-- Fixed-point scale for prices: `ray` = 1.00. -/
def ray : Nat := 1000000

/-- A filed redemption request. `quote` is the price snapshot taken at filing time — the
    whole point of the two-phase design is that this may differ from the price at settlement. -/
structure Request where
  id      : Nat
  owner   : Address
  shares  : Nat
  filedAt : Nat
  quote   : Nat
deriving DecidableEq, Inhabited

structure State where
  /-- E1: the settlement-round counter. -/
  round    : Nat
  price    : Nat
  shares   : Address → Nat
  /-- Cumulative amount credited to each address by settlement. -/
  paid     : Address → Nat
  /-- E4: the FIFO queue, head = oldest. -/
  pending  : List Request
  nextId   : Nat
  capacity : Nat
  /-- Rounds a request must age before it may be settled. -/
  delay    : Nat
  /-- Sent to the settlement layer but not yet acknowledged. -/
  inflight : Nat
  /-- Acknowledged by the settlement layer. -/
  settled  : Nat
  reserve  : Nat
deriving Inhabited

inductive Op
  /-- E1. `delivered` is how much of `inflight` the settlement layer actually acknowledged this
      round — modelled as an argument, *not* assumed to equal `inflight`. -/
  | tick (delivered : Nat)
  | setPrice (p : Nat)
  | enqueue (amount : Nat)
  | cancel (id : Nat)
  | settle (id : Nat)
deriving DecidableEq

/-- Value of `shares` at price `px`, rounded down (protocol-favourable, I4). -/
def entitle (px shares : Nat) : Nat := shares * px / ray

/-- **The I10 rule**: settlement pays the *lower* of the filing-time entitlement and the
    settlement-time entitlement, so choosing when to settle can never raise the payout. -/
def settlePayout (r : Request) (px : Nat) : Nat :=
  min (entitle r.quote r.shares) (entitle px r.shares)

def lookupReq : List Request → Nat → Option Request
  | [],      _  => none
  | r :: rs, id => if r.id = id then some r else lookupReq rs id

def removeReq : List Request → Nat → List Request
  | [],      _  => []
  | r :: rs, id => if r.id = id then rs else r :: removeReq rs id

/-- Total obligation recorded by the queue, valued at each request's filing quote. -/
def obligationOf : List Request → Nat
  | []      => 0
  | r :: rs => entitle r.quote r.shares + obligationOf rs

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.tick delivered =>
    if s.inflight < delivered then none
    else some { s with
      round    := s.round + 1
      settled  := s.settled + delivered
      inflight := s.inflight - delivered }
  | Op.setPrice p =>
    if p = 0 then none
    else some { s with price := p }
  | Op.enqueue amount =>
    -- capacity is checked first: a full queue rejects every enqueue, whatever the amount
    if s.capacity ≤ s.pending.length then none
    else if amount = 0 then none
    else if s.shares caller < amount then none
    else some { s with
      shares  := fun a => if a = caller then s.shares a - amount else s.shares a
      pending := s.pending ++ [{ id := s.nextId, owner := caller, shares := amount,
                                 filedAt := s.round, quote := s.price }]
      nextId  := s.nextId + 1 }
  | Op.cancel id =>
    match lookupReq s.pending id with
    | none   => none
    | some r =>
      if r.owner ≠ caller then none
      else some { s with
        shares  := fun a => if a = caller then s.shares a + r.shares else s.shares a
        pending := removeReq s.pending id }
  | Op.settle id =>
    match s.pending with
    | []        => none
    | r :: rest =>
      if r.id ≠ id then none                            -- FIFO: only the head may settle
      else if s.round < r.filedAt + s.delay then none   -- maturity window
      else if s.reserve < settlePayout r s.price then none
      else some { s with
        paid     := fun a => if a = r.owner then s.paid a + settlePayout r s.price else s.paid a
        reserve  := s.reserve - settlePayout r s.price
        inflight := s.inflight + settlePayout r s.price
        pending  := rest }

/-- Revert-skip trace executor (same shape as the Tier-1 template and `outputs/apyx`). -/
def execTrace (s : State) : List (Op × Address) → State
  | []           => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-! ## I12 — in-flight conservation

The accounting identity the "pending value" pattern rests on: nothing is created or destroyed
by moving between the in-flight and settled buckets. `Op.settle` is the one *accounted* op that
legitimately raises the total (it books a new obligation), exactly as the Tier-1 template treats
accounted-mint ops. -/

/-- The only op allowed to raise `settled + inflight`. -/
def IsAccounted : Op → Prop
  | Op.settle _ => True
  | _           => False

/-- **I12 (a).** Every non-accounted op — including a *partial* `tick` — preserves
    `settled + inflight`. Exhaustive over the closed `Op`: an op that leaked value between the
    two buckets could not compile. -/
theorem inflight_conservation (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hacc : ¬ IsAccounted op) :
    s'.settled + s'.inflight = s.settled + s.inflight := by
  cases op with
  | tick d =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hle
      injection h with h
      subst h
      simp only
      omega
  | setPrice p =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; simp only
  | enqueue n =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · injection h with h; subst h; simp only
  | cancel id =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · injection h with h; subst h; simp only
  | settle id => exact absurd trivial hacc

/-- **I12 (b).** Under the settlement hypothesis — the layer acknowledged *everything* that was
    in flight — a round boundary moves the whole in-flight bucket into settled and leaves nothing
    behind. This is the theorem the common "next block, treat in-flight as zero" convention needs;
    stating it with an explicit `delivered = inflight` premise keeps the assumption visible instead
    of burying it in the step function. -/
theorem tick_settles_exactly (s : State) (c : Address) (s' : State)
    (h : step s (Op.tick s.inflight) c = some s') :
    s'.settled = s.settled + s.inflight ∧ s'.inflight = 0 := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h
    subst h
    exact ⟨rfl, by simp⟩

/-- **I12 (c).** The hypothesis in `tick_settles_exactly` is load-bearing, not cosmetic: if the
    settlement layer acknowledges less than was sent, the residue survives the round boundary.
    A model that hard-wires "in-flight becomes 0 on the next round" silently assumes this away. -/
theorem partial_tick_leaves_residue (s : State) (c : Address) (s' : State) (d : Nat)
    (hd : d < s.inflight) (h : step s (Op.tick d) c = some s') :
    0 < s'.inflight := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h
    subst h
    simp only
    omega

/-! ## I10 — settlement-timing neutrality

The settler chooses *when* a matured request executes, and the price moves in between. That is a
free option unless the payout rule is one-sided. -/

/-- **I10 (step level).** Settling the head request credits its owner exactly
    `settlePayout r s.price` — the protocol-favourable side of the two prices. -/
theorem settle_credits_protocol_favourable_side
    (s : State) (r : Request) (rest : List Request) (id : Nat) (c : Address) (s' : State)
    (hq : s.pending = r :: rest) (h : step s (Op.settle id) c = some s') :
    s'.paid r.owner = s.paid r.owner + settlePayout r s.price := by
  simp only [step, hq] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · injection h with h
        subst h
        simp

/-- **I10 (a).** Waiting cannot raise the payout above the entitlement fixed at filing time. -/
theorem settler_timing_cannot_gain (r : Request) (px : Nat) :
    settlePayout r px ≤ entitle r.quote r.shares :=
  Nat.min_le_left _ _

/-- **I10 (b).** Nor above the entitlement at the price actually prevailing on settlement. -/
theorem settlement_never_overpays_current_value (r : Request) (px : Nat) :
    settlePayout r px ≤ entitle px r.shares :=
  Nat.min_le_right _ _

/-- **I10 (contrast).** Why the `min` is load-bearing: a design that honours the filing quote
    alone pays strictly more than the position is worth whenever the price has fallen — a free
    option handed to whoever controls settlement timing. Witnessed, not argued. -/
theorem naive_filing_price_overpays_witness :
    ∃ (r : Request) (px : Nat), entitle px r.shares < entitle r.quote r.shares := by
  refine ⟨{ id := 0, owner := 0, shares := 1000, filedAt := 0, quote := ray }, ray / 2, ?_⟩
  decide

/-! ## I11b — queue capacity griefing (gap-witness)

The Tier-1 template's pattern-G recipe applied to a *capacity* parameter rather than an economic
one: where safety cannot be proved, prove the reachability of the bad state instead. -/

/-- Witness ground state: capacity 1, attacker `0` and honest user `1` each holding one share. -/
def griefState : State where
  round    := 0
  price    := ray
  shares   := fun a => if a = 0 then 1 else if a = 1 then 1 else 0
  paid     := fun _ => 0
  pending  := []
  nextId   := 0
  capacity := 1
  delay    := 2
  inflight := 0
  settled  := 0
  reserve  := 100

/-- The state after the attacker has taken the single queue slot. -/
def occupied : State := execTrace griefState [(Op.enqueue 1, 0)]

/-- **I11b.** Zero-cost capacity griefing is reachable:

1. with the queue at capacity, **every** enqueue by the honest user is rejected, whatever the
   amount — the design offers no per-user reservation; and
2. the attacker recycles his slot indefinitely at **no cost**: cancel-then-refile returns him to
   exactly the holdings he had, with the queue just as full.

Neither clause is a proof failure — together they are the machine-checked finding that the
capacity parameter needs a per-user bound, a fee, or a non-refundable reservation. -/
theorem queue_capacity_griefing_witness :
    -- (0) control: before the slot is taken, this very user's enqueue succeeds. Without this
    -- clause (1) would also hold of a user who simply had no shares, and the witness would not
    -- be about capacity at all.
    step griefState (Op.enqueue 1) 1 ≠ none ∧
    -- (1) occupancy: once the slot is taken, EVERY enqueue by that user is rejected
    (∀ m : Nat, step occupied (Op.enqueue m) 1 = none) ∧
    -- (2) zero cost: cancel-then-refile restores the attacker's holdings, queue just as full
    (execTrace occupied [(Op.cancel 0, 0), (Op.enqueue 1, 0)]).shares 0 = occupied.shares 0 ∧
    (execTrace occupied [(Op.cancel 0, 0), (Op.enqueue 1, 0)]).pending.length
      = occupied.pending.length := by
  refine ⟨?_, fun m => ?_, ?_, ?_⟩ <;>
    simp [occupied, execTrace, step, griefState, lookupReq, removeReq]

/-! ### Head-of-line blocking

The other half of pattern K, and a different mechanism from capacity: FIFO means an unsettleable
head freezes everything behind it, however affordable those requests are on their own. -/

/-- Reserve is spent by settlement and replenished by nothing: no op in this model raises it. -/
theorem reserve_non_increasing (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.reserve ≤ s.reserve := by
  cases op with
  | tick d =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; simp
  | setPrice p =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; simp
  | enqueue n =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · injection h with h; subst h; simp
  | cancel id =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · injection h with h; subst h; simp
  | settle id =>
    simp only [step] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · injection h with h; subst h; simp only; omega

/-- …hence no trace can make an unaffordable head affordable: the block below is permanent, not
    merely current. -/
theorem reserve_non_increasing_trace (s : State) (σ : List (Op × Address)) :
    (execTrace s σ).reserve ≤ s.reserve := by
  induction σ generalizing s with
  | nil => simp [execTrace]
  | cons hd tl ih =>
    obtain ⟨op, c⟩ := hd
    simp only [execTrace]
    split
    · rename_i s' hstep
      exact Nat.le_trans (ih s') (reserve_non_increasing s op c s' hstep)
    · exact ih s

/-- Ground state for head-of-line blocking: two slots, a thin reserve, a whale (`1`) and a
    small honest user (`2`). -/
def hobState : State :=
  { griefState with
      capacity := 2
      reserve  := 10
      shares   := fun a => if a = 1 then 1000 else if a = 2 then 5 else 0 }

/-- Whale files first, small user second, then the maturity window passes. -/
def blocked : State := execTrace hobState
  [(Op.enqueue 1000, 1), (Op.enqueue 5, 2), (Op.tick 0, 0), (Op.tick 0, 0)]

/-- **I11 (starvation witness).** FIFO plus an unaffordable head starves everyone behind it:
    both queued requests are mature, the head cannot settle because the reserve cannot cover it,
    and the request behind it cannot settle either — *even though the reserve covers that one
    comfortably*. With `reserve_non_increasing_trace` the situation cannot resolve itself, so the
    small user is starved for good. The fix is a design choice — allow out-of-order settlement,
    partial fills, or per-request reserve earmarking — and naming it is the point of the witness. -/
theorem queue_head_of_line_blocking_witness :
    blocked.pending.length = 2 ∧
    (∀ c : Address, step blocked (Op.settle 0) c = none) ∧
    (∀ c : Address, step blocked (Op.settle 1) c = none) ∧
    (∃ r ∈ blocked.pending, settlePayout r blocked.price ≤ blocked.reserve) := by
  refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;>
    simp [blocked, hobState, griefState, execTrace, step, settlePayout, entitle, ray]

/-! ### Anti-vacuity guards -/

/-- A completed run: file at round 0, let two rounds elapse, settle the matured head. -/
def settledRun : State := execTrace griefState
  [(Op.enqueue 1, 0), (Op.tick 0, 0), (Op.tick 0, 0), (Op.settle 0, 9)]

/-- **Anti-vacuity guard.** The I10/I12 theorems above are conditioned on a settlement actually
    succeeding; if `Op.settle` were unreachable they would be statements about an empty set of
    executions. It is reachable, and settlement is permissionless here (address `9` settles a
    request it does not own). Instantiations should carry an equivalent check for every guarded
    op they reason about. -/
theorem settle_is_reachable :
    settledRun.paid 0 = 1 ∧ settledRun.inflight = 1 ∧ settledRun.pending = [] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [settledRun, execTrace, step, griefState, settlePayout, entitle, ray]

/-- Ground state for the price-move run: one user with enough shares and a deep reserve. -/
def priceDropState : State :=
  { griefState with shares := fun a => if a = 1 then 1000 else 0, reserve := 100000 }

/-- File at par, price halves, then settle. -/
def priceDropRun : State := execTrace priceDropState
  [(Op.enqueue 1000, 1), (Op.setPrice (ray / 2), 9), (Op.tick 0, 0), (Op.tick 0, 0),
   (Op.settle 0, 9)]

/-- **I10 (end-to-end).** The rule is not just an inequality about `min` — here is a trace where
    the price actually moves between filing and settlement. Filed at par for `1000`, settled after
    the price halved: the owner is credited `500`, the settlement-time value, while a rule
    honouring the filing quote alone would have paid `1000` out of the pool. That gap is the free
    option `settlePayout` closes. -/
theorem settlement_takes_lower_price_after_drop :
    priceDropRun.paid 1 = 500 ∧ entitle ray 1000 = 1000 := by
  refine ⟨?_, ?_⟩ <;>
    simp [priceDropRun, priceDropState, griefState, execTrace, step, settlePayout, entitle, ray]

/-! ## I15 — signed net value, and the `Nat` vacuity trap -/

/-- The vault's net value read off a `Nat` ledger: truncated subtraction. -/
def vaultNetNat (s : State) : Nat := s.reserve - obligationOf s.pending

/-- The same quantity read off a signed ledger. -/
def vaultNetInt (s : State) : Int := (s.reserve : Int) - (obligationOf s.pending : Int)

/-- **The trap.** On a `Nat` ledger "the vault is never underwater" is true *by typing*. Proving
    it carries no information about the protocol — it is the type-level form of the vacuity the
    round-trip judge flags in `review.json`. Any model whose net position can go negative must
    move to `Int` before the solvency claim means anything. -/
theorem nat_solvency_is_vacuous (s : State) : 0 ≤ vaultNetNat s := Nat.zero_le _

/-- Ground state for the insolvency witness: a thin reserve and a user able to file a large
    request against it. -/
def thinReserveState : State :=
  { griefState with reserve := 1, shares := fun a => if a = 1 then 1000 else 0 }

/-- **I15.** A reachable state whose signed net value is negative — while the `Nat` reading of
    the very same state reports a comfortable `0`. This is the concrete payload of
    `nat_solvency_is_vacuous`: the unsigned ledger does not merely lose precision, it reports
    insolvency as solvency. -/
theorem insolvency_witness :
    ∃ (s₀ : State) (σ : List (Op × Address)),
      vaultNetInt (execTrace s₀ σ) < 0 ∧ vaultNetNat (execTrace s₀ σ) = 0 := by
  refine ⟨thinReserveState, [(Op.enqueue 1000, 1)], ?_, ?_⟩ <;>
    simp [execTrace, step, thinReserveState, griefState, vaultNetInt, vaultNetNat,
          obligationOf, entitle, ray]

end AsyncQueueVault
