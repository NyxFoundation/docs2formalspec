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

Scope: this module models the guard and the two ways it can be surprised. The trace-level
"damage is linear in elapsed time" statement is not re-proved here; `BlastRadius.lean`'s
`rate_limit_linear_bound` already establishes that shape generically over a wrapper, and what was
missing was the tie to a real contract's guard.
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

def step (s : State) (op : Op) (caller : Address) : Option State :=
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
