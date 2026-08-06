/-!
# The deployed redemption-price pipeline

`Apyx.lean` carries a single `redemptionValue` field written by privileged operations. On-chain
the price is produced by two contracts, and neither of them has the setter the model assumes:

* **`ApyxCollateralRatioOracle`** (`0x823210Eb…D305`) — the writable end. `pushRound(int256)` is
  assigned to role 22, a **4-hour scheduled operation**; `pushRound(int256,uint80)`,
  `setUpstreamOracle` and `clearOverride` are still role 0 (admin, undelayed).
* **`ApyxRedemptionOracle`** (`0x2037a5eb…23b4`, implementation `0xbcc4a174…d682`) — a read-only
  Chainlink-shaped aggregator, description *"Apyx Capped Collateralization Ratio"*, `decimals() = 8`.
  It has **no setter of any kind**. It reads the collateral oracle and applies `cap()`.

Live values at ≈ block 25,641,600: `cap() = 100000000` (**1.00** at 8 decimals) and a published
answer of `90365900` (0.903659).

This module models that pipeline. It settles two of the report's findings in opposite directions —
see `published_never_exceeds_par` and `published_has_no_floor` below — and it is where the
`h_rv : redemptionValue ≤ ray` hypothesis that `Safety.lean` re-supplies along every trace turns
out to be a property of the deployment rather than an assumption.
-/

namespace RedemptionOracle

abbrev Address := Nat

/-- 1.00 at the aggregator's 8 decimals — the value `cap()` actually holds. -/
def par : Nat := 100000000

/-- The published answer at the time of reading, 0.903659. -/
def liveAnswer : Nat := 90365900

structure State where
  now              : Nat
  paused           : Bool
  /-- `ApyxRedemptionOracle.cap()`. Fixed at `initialize`; the contract exposes no setter, so the
      only way to move it is a UUPS implementation swap (role 24, a 3-day scheduled operation). -/
  cap              : Nat
  /-- The latest round pushed onto `ApyxCollateralRatioOracle`. -/
  collateralAnswer : Nat
deriving Inhabited

inductive Op
  | tick (dt : Nat)
  /-- `ApyxCollateralRatioOracle.pushRound(int256)` — role 22, 4-hour scheduled. -/
  | pushRound (answer : Nat)
  | pause
  | unpause
deriving DecidableEq

/-- What `ApyxRedemptionOracle.latestRoundData` publishes: the collateral ratio, capped. -/
def published (s : State) : Nat := min s.collateralAnswer s.cap

/-- **`caller` is deliberately ignored.** On chain every operation below is role-gated
(`restricted`), but this miniature admits any caller, so each theorem is quantified over an
adversary who may call *anything*. That makes the invariants below **stronger** than their
on-chain counterparts, not weaker — they survive even a total collapse of the role system. The
parameter is kept so the signature matches the other machines' `step`, and so `execTrace` can
carry caller-tagged traces. -/
def step (s : State) (op : Op) (_caller : Address) : Option State :=
  match op with
  | Op.tick dt         => some { s with now := s.now + dt }
  | Op.pushRound a     => if s.paused then none else some { s with collateralAnswer := a }
  | Op.pause           => some { s with paused := true }
  | Op.unpause         => some { s with paused := false }

def execTrace (s : State) : List (Op × Address) → State
  | []           => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-! ## The clock is a monopoly

The pipeline has a clock because `pushRound` records a round at a time. Nothing here is a maturity
claim, so this is a hygiene result rather than a load-bearing one — but stating it is what keeps
the machine honest if a future round-staleness property is added, and it matches the discipline
`Apyx.lean`, `CommitToken.lean` and `MinterRateLimit.lean` now carry.
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

/-- And the trace form. -/
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

/-! ## The cap holds, and nothing in the pipeline can move it -/

/-- The published price never exceeds the cap. True by the shape of `latestRoundData`, which is
    the point: the bound is structural, not a guard someone has to remember to write. -/
theorem published_le_cap (s : State) : published s ≤ s.cap := Nat.min_le_right _ _

/-- **I21 against a real deployment.** No operation in the pipeline changes `cap`. Exhaustive over
    the closed `Op`, so if a future version grew a setter this proof would break rather than the
    invariant. On-chain the same statement holds for a different reason — the contract has no
    function that writes it — and moving it at all requires replacing the implementation, a 3-day
    scheduled operation under role 24. -/
theorem cap_immutable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.cap = s.cap := by
  cases op <;> simp only [step] at h <;> repeat' split at h
  all_goals first
    | (cases Option.some.inj h; rfl)
    | exact absurd h (by simp)

/-- Lifted to traces: no sequence of pipeline operations, by any caller, raises the cap. -/
theorem cap_immutable_trace (s : State) (σ : List (Op × Address)) :
    (execTrace s σ).cap = s.cap := by
  induction σ generalizing s with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    simp only [execTrace]
    cases hstep : step s op c with
    | none    => exact ih s
    | some s1 => rw [ih s1, cap_immutable s op c s1 hstep]

/-- **The upper bound the report said did not exist.** With the deployed `cap = par`, the published
    price is at most 1.00 along every trace, whatever is pushed.

    `BlastRadius.redeem_payout_has_no_cap` remains a true statement about the *design* — nothing in
    the specification forces a bound — but the deployment supplies one outside the modelled state,
    and this is it. It is also the discharge of `Safety.lean`'s `h_rv : redemptionValue ≤ ray`,
    which the trace-level proofs there re-supply as a hypothesis at every step. -/
theorem published_never_exceeds_par (s : State) (σ : List (Op × Address)) (h_cap : s.cap = par) :
    published (execTrace s σ) ≤ par := by
  have := published_le_cap (execTrace s σ)
  rw [cap_immutable_trace s σ, h_cap] at this
  exact this

/-! ## …and the other half: there is no floor -/

/-- **`redemption_has_no_floor` survives contact with the deployment.** One push of `0` publishes
    `0`; there is no lower clamp anywhere in the pipeline, and no minimum move size. So of the two
    parameter-bound findings in `SpecDefects.lean`, the cap one is answered by the deployment and
    the floor one is not. -/
theorem published_has_no_floor (s : State) (c : Address) (h_up : s.paused = false) :
    ∃ s', step s (Op.pushRound 0) c = some s' ∧ published s' = 0 := by
  refine ⟨{ s with collateralAnswer := 0 }, by simp [step, h_up], ?_⟩
  simp [published]

end RedemptionOracle
