/-!
# `MinterV0`'s rate limit

`Apyx.lean` abstracts mint authorization away — `Op.depositUSDC` and `Op.mintApxUSD` mint at $1
with role and list checks and no volume bound. On-chain, minting goes through `MinterV0`
(`0x2c36e1aD…a76e`), which carries a **sliding-window rate limit**: `requestMint` reverts when the
order exceeds `rateLimitAmount - rateLimitMinted()`, where `rateLimitMinted()` sums the records in
`mintHistory` that fall inside `rateLimitPeriod`.

Live values at ≈ block 25,641,600: `rateLimitAmount = 5e25` (**50,000,000 apxUSD**),
`rateLimitPeriod = 86400` (1 day), `MAX_RATE_LIMIT_PERIOD = 1209600` (14 days), currently
`rateLimitMinted() = 0`. A `setRateLimit(1e24, 86400)` — a **50× tightening** — is scheduled in the
manager's queue (`model.md` §6).

Scope: this module models the guard, the two ways it can be surprised, and — as of the clock
pass — what the guard actually buys **over a trace**. That last part used to be delegated to
`BlastRadius.lean`'s `rate_limit_linear_bound`, on the grounds that it "establishes that shape
generically". It does not: that wrapper meters an **epoch** allowance (`cap * (elapsed / window + 1)`,
released in steps), whereas `MinterV0` runs a true **sliding window** in which each record expires
on its own schedule. The two coincide only at the boundaries, so the real contract's cumulative
behaviour needed proving here rather than borrowing.
-/

namespace MinterRateLimit

abbrev Address := Nat

def day : Nat := 86400
/-- The deployed configuration. -/
def liveAmount : Nat := 50000000 * 10 ^ 18
def livePeriod : Nat := day
/-- The tightening currently sitting in the AccessManager queue. -/
def queuedAmount : Nat := 1000000 * 10 ^ 18

/-- One entry of `mintHistory`: when it was recorded, and how much. -/
structure Record where
  time   : Nat
  amount : Nat
deriving DecidableEq, Inhabited

structure State where
  now             : Nat
  paused          : Bool
  rateLimitAmount : Nat
  rateLimitPeriod : Nat
  history         : List Record
deriving Inhabited

inductive Op
  | tick (dt : Nat)
  | requestMint (amount : Nat)
  /-- `restricted`; role 24 on-chain, i.e. a 3-day scheduled operation. -/
  | setRateLimit (amount : Nat) (period : Nat)
  | pause
  | unpause
deriving DecidableEq

/-- `rateLimitMinted()`: the records still inside the window. A record is inside when it was made
    no earlier than `now - period`, written without truncated subtraction. -/
def mintedInWindow : List Record → Nat → Nat → Nat
  | [],      _,   _      => 0
  | r :: rs, now, period =>
    (if now ≤ r.time + period then r.amount else 0) + mintedInWindow rs now period

def minted (s : State) : Nat := mintedInWindow s.history s.now s.rateLimitPeriod

/-- `rateLimitAvailable()`. -/
def available (s : State) : Nat := s.rateLimitAmount - minted s

/-- **`caller` is deliberately ignored.** On chain every operation below is role-gated
(`restricted`), but this miniature admits any caller, so each theorem is quantified over an
adversary who may call *anything*. That makes the invariants below **stronger** than their
on-chain counterparts, not weaker — they survive even a total collapse of the role system. The
parameter is kept so the signature matches the other machines' `step`, and so `execTrace` can
carry caller-tagged traces. -/
def step (s : State) (op : Op) (_caller : Address) : Option State :=
  match op with
  | Op.tick dt => some { s with now := s.now + dt }
  | Op.requestMint amount =>
    if s.paused then none
    else if amount = 0 then none
    else if available s < amount then none
    else some { s with history := { time := s.now, amount := amount } :: s.history }
  | Op.setRateLimit amount period =>
    if amount = 0 then none
    else if period = 0 then none
    else some { s with rateLimitAmount := amount, rateLimitPeriod := period }
  | Op.pause   => some { s with paused := true }
  | Op.unpause => some { s with paused := false }

/-- Execute a list of `(op, caller)` pairs in order; failed operations revert and the trace
continues, matching the other machines' `execTrace`. -/
def execTrace (s : State) : List (Op × Address) → State
  | [] => s
  | (op, c) :: σ =>
    match step s op c with
    | some s' => execTrace s' σ
    | none    => execTrace s σ

/-! ## The clock is a monopoly here too

Same discipline as `Apyx.lean`: a rate limit measured against a clock is worthless if any
operation can advance that clock, since the window could then be rolled for free. Stated
single-step and over traces, exhaustively over the closed `Op`.
-/

/-- **No operation but `tick` moves the clock.** -/
theorem now_moves_only_by_tick (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (h_not_tick : ∀ dt, op ≠ Op.tick dt) :
    s'.now = s.now := by
  cases op
  case tick dt => exact absurd rfl (h_not_tick dt)
  all_goals
    simp only [step] at h
    (repeat' split at h) <;> first | (cases Option.some.inj h; rfl) | exact absurd h (by simp)

/-- **A trace containing no `tick` cannot roll the window.** This is what makes the limit a limit:
elapsed time has to be bought, and no amount of minting, pausing or reconfiguring buys it. -/
theorem trace_now_fixed_without_tick (s : State) (σ : List (Op × Address))
    (h_no_tick : ∀ p ∈ σ, ∀ dt, p.1 ≠ Op.tick dt) :
    (execTrace s σ).now = s.now := by
  induction σ generalizing s with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have h_tail : ∀ q ∈ σ, ∀ dt, q.1 ≠ Op.tick dt :=
      fun q hq => h_no_tick q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail
    | some s1 =>
      rw [ih s1 h_tail]
      exact now_moves_only_by_tick s op c s1 hstep (h_no_tick (op, c) List.mem_cons_self)

/-! ## The guard -/

/-- A mint that would exceed the remaining allowance is rejected. This is the whole of the
    contract's protection, and it is evaluated against the window at the moment of the call. -/
theorem mint_over_available_is_rejected (s : State) (c : Address) (amount : Nat)
    (h : available s < amount) : step s (Op.requestMint amount) c = none := by
  simp only [step]
  repeat' split
  all_goals first | rfl | simp_all

/-- A successful mint records exactly what was minted, at the current time. -/
theorem mint_records_the_order (s : State) (c : Address) (amount : Nat) (s' : State)
    (h : step s (Op.requestMint amount) c = some s') :
    s'.history = { time := s.now, amount := amount } :: s.history ∧ available s ≥ amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hav
        cases Option.some.inj h
        exact ⟨rfl, Nat.not_lt.mp hav⟩

/-! ## What the guard buys over a trace

`mint_over_available_is_rejected` is one call. The property the contract exists for is the
invariant it maintains: **at every point of every trace, the volume inside the window is within
the ceiling**. Nothing above establishes that — a single rejected call says nothing about what a
long run accumulates.

The one operation that can break it is `setRateLimit`, and that is not an oversight but the
content of `tightening_does_not_unwind_the_window` below: lowering the ceiling leaves history
untouched, so the invariant is stated over traces that do not reconfigure the limiter.
-/

/-- Ticking can only shrink the window's contents: a record leaves when `now` passes
`time + period`, and never comes back. -/
theorem mintedInWindow_antitone_in_now (h : List Record) (period : Nat) :
    ∀ n₁ n₂, n₁ ≤ n₂ → mintedInWindow h n₂ period ≤ mintedInWindow h n₁ period := by
  intro n₁ n₂ hle
  induction h with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
    simp only [mintedInWindow]
    have hterm : (if n₂ ≤ r.time + period then r.amount else 0)
        ≤ (if n₁ ≤ r.time + period then r.amount else 0) := by
      split
      · rw [if_pos (by omega)]; exact Nat.le_refl _
      · exact Nat.zero_le _

    exact Nat.add_le_add hterm ih

/-- A fresh record is always inside the window it was made in, so a successful mint adds exactly
its amount to the metered volume. -/
theorem minted_after_mint (s : State) (c : Address) (amount : Nat) (s' : State)
    (h : step s (Op.requestMint amount) c = some s') :
    minted s' = amount + minted s := by
  obtain ⟨hhist, -⟩ := mint_records_the_order s c amount s' h
  have hnow : s'.now = s.now := now_moves_only_by_tick s _ c s' h (by simp)
  have hper : s'.rateLimitPeriod = s.rateLimitPeriod := by
    simp only [step] at h
    (repeat' split at h) <;> first | (cases Option.some.inj h; rfl) | exact absurd h (by simp)
  unfold minted
  rw [hhist, hnow, hper]
  simp only [mintedInWindow]
  rw [if_pos (by omega)]

/-- Operations other than `setRateLimit` never raise the metered volume above the ceiling, given
that it was within the ceiling to begin with. The three cases are the three things that can
happen: the clock moves and the window shrinks; a mint lands and the guard has already checked it
fits; or nothing relevant changes. -/
theorem minted_le_cap_step (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (h_inv : minted s ≤ s.rateLimitAmount)
    (h_no_cfg : ∀ a p, op ≠ Op.setRateLimit a p) :
    minted s' ≤ s'.rateLimitAmount := by
  cases op
  case setRateLimit a p => exact absurd rfl (h_no_cfg a p)
  case tick dt =>
    have hs' : s' = { s with now := s.now + dt } := by
      simp only [step] at h; exact (Option.some.inj h).symm
    subst hs'
    exact Nat.le_trans (mintedInWindow_antitone_in_now s.history s.rateLimitPeriod
      s.now (s.now + dt) (by omega)) h_inv
  case requestMint amount =>
    obtain ⟨-, hav⟩ := mint_records_the_order s c amount s' h
    have hcap : s'.rateLimitAmount = s.rateLimitAmount := by
      simp only [step] at h
      (repeat' split at h) <;> first | (cases Option.some.inj h; rfl) | exact absurd h (by simp)
    have hfits : amount + minted s ≤ s.rateLimitAmount := by
      unfold available at hav; omega
    rw [minted_after_mint s c amount s' h, hcap]
    exact hfits
  case pause =>
    have hs' : s' = { s with paused := true } := by
      simp only [step] at h; exact (Option.some.inj h).symm
    subst hs'; exact h_inv
  case unpause =>
    have hs' : s' = { s with paused := false } := by
      simp only [step] at h; exact (Option.some.inj h).symm
    subst hs'; exact h_inv

/-! ## Two ways the limit is weaker than it reads -/

/-- **Tightening the limit does not unwind what has already been minted.** `rateLimitMinted()` is
    computed from history, and `setRateLimit` touches only the ceiling, so immediately after a
    reduction the window can hold more than the new limit allows — `available` is then 0 and stays
    0 until the window rolls, rather than the excess being clawed back.

    Not a defect; worth stating because the 50× tightening now queued
    (`5e25 → 1e24`) lands in exactly this shape, and because it is the mirror image of
    `CommitToken.raising_the_delay_unclaims_pending_requests`: a parameter change reaching
    backwards into commitments already made. -/
theorem tightening_does_not_unwind_the_window :
    ∃ (s s' : State), minted s ≤ s.rateLimitAmount ∧
      step s (Op.setRateLimit queuedAmount livePeriod) 0 = some s' ∧
      s'.rateLimitAmount < minted s' ∧ available s' = 0 := by
  refine ⟨{ (default : State) with
              now := 0
              rateLimitAmount := liveAmount
              rateLimitPeriod := livePeriod
              history := [{ time := 0, amount := liveAmount }] },
          { (default : State) with
              now := 0
              rateLimitAmount := queuedAmount
              rateLimitPeriod := livePeriod
              history := [{ time := 0, amount := liveAmount }] }, ?_, ?_, ?_, ?_⟩
  · simp [minted, mintedInWindow]
  · simp [step, queuedAmount, liveAmount, livePeriod, day]
  · simp [minted, mintedInWindow, queuedAmount, liveAmount]
  · simp [available, minted, mintedInWindow, queuedAmount, liveAmount]

/-- **Waiting is the only thing that frees capacity, and it frees it all at once.** A record leaves
    the window the moment `now` passes `at + period`; there is no smoothing. So a full window
    followed by one `tick` past the boundary restores the entire allowance in a single block. -/
theorem window_frees_in_one_step :
    ∃ (s s' : State), available s = 0 ∧
      step s (Op.tick (livePeriod + 1)) 0 = some s' ∧ available s' = s'.rateLimitAmount := by
  refine ⟨{ (default : State) with
              now := 0
              rateLimitAmount := liveAmount
              rateLimitPeriod := livePeriod
              history := [{ time := 0, amount := liveAmount }] },
          { (default : State) with
              now := livePeriod + 1
              rateLimitAmount := liveAmount
              rateLimitPeriod := livePeriod
              history := [{ time := 0, amount := liveAmount }] }, ?_, ?_, ?_⟩
  · simp [available, minted, mintedInWindow]
  · simp [step]
  · simp [available, minted, mintedInWindow, liveAmount, livePeriod, day]

end MinterRateLimit
