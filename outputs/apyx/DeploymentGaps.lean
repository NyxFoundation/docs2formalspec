import D2fsSpecs.Apyx

/-!
# Three more mechanisms the model does not have, from the deployed Solidity

Companion to `DeploymentFees.lean`. Same method: verified sources from sourcify, live reads
against mainnet, formalize what the documentation corpus never mentioned. Sources here are
`src/ApxUSD.sol` (impl `0xdd71fd677fde2ed2579a3c45204f41a11016ccb4`) and `src/LinearVestV0.sol`
(`0x0d62b4cc02b4b51ed19ddf41d7a7979cf394c99f`, not behind a proxy).

**§A. `LinearVestV0.setBeneficiary` redirects the whole vesting pool — behind a 3-day schedule.**
`pullVestedYield()` is `onlyBeneficiary` and pays `vestedAmount()` **to the beneficiary**, so
whoever the beneficiary is can take the accrued pool, and the vault is never consulted. Two calls
therefore move it. **The mitigating fact, read from the AccessManager:**
`setBeneficiary(address)` on `0x0d62b4cc…c99f` resolves to **role 24**, which this report has
elsewhere recorded as a 3-day scheduled operation (`CommitToken.lean`, `MinterRateLimit.lean`), so
the retarget is pre-announced on chain rather than instant. That is a real defence and it is why
this is a governance-visibility item, not an instant-drain item. What remains is the *design*:
the payee is a mutable pointer rather than a fixed vault address, and a live read put
`vestedAmount()` at 122,187.95 apxUSD. The model has no `setBeneficiary` operation at all, so
`BlastRadius.lean`'s "admin alone cannot touch balances" is silent about this channel rather than
covering it.

**§B. `ApxUSD` has a supply cap; the model does not — and the admin can lift it.**
`mint` reverts unless `totalSupply() + amount <= supplyCap` (live: cap `750,000,000e18` against a
`327,073,514.82…e18` supply). That is a real bound on a lone compromised `MINT_STRAT`. It is not
a bound on a coalition: `setSupplyCap` accepts any value `>= totalSupply()`, so admin-plus-minter
reaches an arbitrary supply — the same shape as `admin_rfq_coalition_drains`, on a different
channel.

**§C. The vest clock: the model re-anchors on every pull, the deployment does not.**
`LinearVestV0` keeps *two* timestamps — `lastDepositTimestamp`, which fixes
`vestingPeriodEnd = lastDeposit + vestingPeriod`, and `lastTransferTimestamp`, the accrual
anchor. `pullVestedYield` moves only the latter, so **pulling does not move the finish line**.
The model collapses both into `vestStart` and `pullVestedYield` sets `vestStart := now`, which
restarts the schedule. The deployment pulls on *every* `withdraw`/`redeem`, so the model's yield
is deferred again each time — stated over a trace by `model_pullEvery_defers_without_bound`
against `periodEnd_invariant_under_pullEvery`, which needed giving this module a clock of its own
(`docs/06` §7.3 E1, the same move `Op.tick` made for the main model).
-/

namespace Apyx

/-! ## §A. The vesting beneficiary is a single-key drain

A miniature of `LinearVestV0` in the style of the wrapper machines in `BlastRadius.lean`: only
the fields the drain depends on. It carries the deployment's `onlyBeneficiary` guard, which is the
one the attack turns on. It deliberately does **not** carry `setBeneficiary`'s `restricted`
modifier — there is no caller argument, no role and no scheduling anywhere in this section,
because the premise is that the role-24 key is already compromised and the 3-day window has
elapsed. So "admin" below names the threat model, not anything Lean checks, and the theorems say
nothing about how long the retarget takes to become executable. Whether these definitions match
the Solidity is likewise a reading, not a theorem.
-/

/-- `LinearVestV0`'s state, restricted to what `pullVestedYield` reads and writes. -/
structure VestState where
  /-- `vestingAmount` — the currently-streaming pool. -/
  vestingAmount : Nat
  /-- `fullyVestedAmount` — already streamed, not yet pulled. -/
  fullyVested : Nat
  /-- `lastDepositTimestamp`; `vestingPeriodEnd = lastDeposit + period`. -/
  lastDeposit : Nat
  /-- `lastTransferTimestamp` — the accrual anchor, moved by pulls. -/
  lastTransfer : Nat
  /-- `vestingPeriod`. -/
  period : Nat
  /-- `beneficiary` — both the only permitted caller of `pullVestedYield` and its payee. -/
  beneficiary : Address
  /-- Who has received pulled yield. -/
  bal : Address → Nat
  /-- Block timestamp. -/
  now : Nat

/-- `vestingPeriodEnd()`. -/
def VestState.periodEnd (v : VestState) : Nat := v.lastDeposit + v.period

/-- `newlyVestedAmount()`, transcribed: zero pool or an anchor past the end yields nothing;
otherwise `mulDiv(vestingAmount, min(now, end) - lastTransfer, period, Floor)`. -/
def VestState.newlyVested (v : VestState) : Nat :=
  if v.vestingAmount = 0 then 0
  else if v.periodEnd ≤ v.lastTransfer then 0
  else v.vestingAmount * (min v.now v.periodEnd - v.lastTransfer) / v.period

/-- `vestedAmount()` = `fullyVestedAmount + newlyVestedAmount()`. -/
def VestState.vested (v : VestState) : Nat := v.fullyVested + v.newlyVested

/-- `pullVestedYield()` — **`onlyBeneficiary`**, and it pays the beneficiary. Returns `none` for
any other caller, mirroring the revert. -/
def pullVest (v : VestState) (caller : Address) : Option VestState :=
  if caller ≠ v.beneficiary then none
  else
    let amt := v.vested
    some { v with
      fullyVested := 0
      lastTransfer := v.now
      bal := fun a => if a = v.beneficiary then v.bal a + amt else v.bal a }

/-- `setBeneficiary(newBeneficiary)` — `restricted`, i.e. an admin-role call. Reverts only on
the zero address; no timelock, no acknowledgement from the outgoing beneficiary. -/
def setBeneficiary (v : VestState) (newB : Address) : Option VestState :=
  if newB = 0 then none else some { v with beneficiary := newB }

/-- **A witness in which two calls move the entire pending yield to an attacker address.**

The beneficiary is repointed at an address the attacker controls, and that address pulls. The
attacker ends holding exactly the yield that was owed to the vault, and nothing is credited to
the vault. The contrast conjunct is the point — from the same state, the attacker pulling
*without* the beneficiary change is refused outright (`onlyBeneficiary`), so the retarget is
doing all the work.

This is an `∃` over one state, not a universal claim, and the pool here is **streaming**
(`vestingAmount = 200` at the midpoint of a 10-tick period) rather than pre-banked, so the 100
taken is what `vestedAmount()` computes from the clock rather than a figure already sitting in
the `fullyVested` accumulator.

`BlastRadius.lean`'s `admin_cannot_touch_balances` and the `admin alone` row of
`single_key_bounds` say a compromised admin extracts zero. Both are true **of the model**, which
has no `setBeneficiary` operation.

*Outside Lean*: the sourcify-verified `LinearVestV0` has `pullVestedYield` gated `onlyBeneficiary`
and paying `beneficiary`, and `setBeneficiary` as a `restricted` call — which the AccessManager
assigns to **role 24**, the 3-day scheduled role, so the retarget is announced three days ahead
rather than executed on the spot. A live read put `vestedAmount()` at roughly 122k apxUSD. None
of that is established by the theorem below, which is arithmetic over a hand-written state. -/
theorem admin_alone_redirects_vested_yield :
    ∃ (v v1 v2 : VestState) (vault attacker : Address),
      v.beneficiary = vault ∧
      attacker ≠ vault ∧
      0 < v.vested ∧
      v.bal attacker = 0 ∧
      -- without the admin call the attacker cannot pull at all
      pullVest v attacker = none ∧
      -- with it, two steps move the whole pool
      setBeneficiary v attacker = some v1 ∧
      pullVest v1 attacker = some v2 ∧
      v2.bal attacker = v.vested ∧
      v2.bal vault = v.bal vault := by
  refine ⟨{ vestingAmount := 200, fullyVested := 0, lastDeposit := 0, lastTransfer := 0
            period := 10, beneficiary := 1, bal := fun _ => 0, now := 5 },
          _, _, 1, 2, rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pre-banked variant, for contrast: the pool has finished streaming and the 100 sits in
`fullyVested`. The retarget takes it just the same, so neither accumulator is safer than the
other. (Toy numbers — not to be confused with the mainnet `vestedAmount()` figure quoted above.) -/
theorem admin_redirect_takes_the_banked_accumulator :
    ∃ (v v1 v2 : VestState) (attacker : Address),
      v.vested = 100 ∧ v.vestingAmount = 0 ∧
      setBeneficiary v attacker = some v1 ∧
      pullVest v1 attacker = some v2 ∧
      v2.bal attacker = 100 := by
  refine ⟨{ vestingAmount := 0, fullyVested := 100, lastDeposit := 0, lastTransfer := 0
            period := 1, beneficiary := 1, bal := fun _ => 0, now := 0 },
          _, _, 2, by decide, rfl, rfl, rfl, rfl⟩

/-! ## §B. The supply cap, and the coalition that lifts it -/

/-- `ApxUSD.mint`'s guard: `totalSupply() + amount <= supplyCap`. -/
def mintUnderCap (cap supply amount : Nat) : Option Nat :=
  if supply + amount ≤ cap then some (supply + amount) else none

/-- `setSupplyCap`'s only guard: the new cap may not fall below the current supply. It may rise
without limit — and note the old cap is **not** read, which is the whole point: nothing in the
setter is relative to the bound currently in force. -/
def setCap (_cap supply newCap : Nat) : Option Nat :=
  if newCap < supply then none else some newCap

/-- **A lone compromised minter is bounded by the cap**, at every step. Lifted to whole runs in
`mint_run_bounded` just below; this statement is the single-step implication only. -/
theorem lone_minter_bounded (cap supply amount supply' : Nat)
    (h : mintUnderCap cap supply amount = some supply') :
    supply' ≤ cap := by
  unfold mintUnderCap at h
  split at h
  · rename_i hle
    have heq := Option.some.inj h
    omega
  · exact absurd h (by simp)

/-- The bound is inherited by any run of mints against a fixed cap — **starting from a supply
already under it**. The hypothesis is load-bearing: failed mints are no-ops, so a run begun above
the cap simply stays above it. -/
theorem mint_run_bounded (cap : Nat) : ∀ (amts : List Nat) (supply : Nat),
    supply ≤ cap →
    (amts.foldl (fun s a => (mintUnderCap cap s a).getD s) supply) ≤ cap := by
  intro amts
  induction amts with
  | nil => intro s hs; exact hs
  | cons a rest ih =>
    intro s hs
    apply ih
    cases hm : mintUnderCap cap s a with
    | none => simpa [hm] using hs
    | some s' => simpa [hm] using lone_minter_bounded cap s a s' hm

/-- **The cap is not a bound on a coalition.** For any target **at or above the current supply**
— the hypothesis, and the only restriction — one call raises the cap to it and one mints straight
to it.

Roles, keys and timelocks are not modelled here: `setCap` and `mintUnderCap` take no caller, so
"two keys, no timelock in between" is read off the Solidity's modifiers rather than proved. What
*is* proved is the arithmetic asymmetry — `lone_minter_bounded` holds the minter to the cap, and
this holds nobody to anything. Same shape as `admin_rfq_coalition_drains`. The model expresses
neither half, having no cap and no `setSupplyCap`. -/
theorem admin_minter_coalition_escapes_cap (cap supply target : Nat) (h : supply ≤ target) :
    ∃ cap' supply', setCap cap supply target = some cap' ∧
      mintUnderCap cap' supply (target - supply) = some supply' ∧
      supply' = target := by
  refine ⟨target, target, ?_, ?_, rfl⟩
  · unfold setCap; rw [if_neg (by omega)]
  · unfold mintUnderCap; rw [if_pos (by omega)]; congr 1; omega

/-- **The coalition result is not vacuous at the live configuration.** Instantiated at the values
read from mainnet — cap `750,000,000e18`, supply `327,073,514.822856436999740169e18` — the pair
reaches a supply of one billion, well past the cap the lone minter is held to. -/
theorem live_cap_escaped_at_one_billion :
    ∃ cap' supply',
      setCap 750000000000000000000000000 327073514822856436999740169
          1000000000000000000000000000 = some cap' ∧
      mintUnderCap cap' 327073514822856436999740169
          (1000000000000000000000000000 - 327073514822856436999740169) = some supply' ∧
      supply' = 1000000000000000000000000000 :=
  admin_minter_coalition_escapes_cap 750000000000000000000000000 327073514822856436999740169
    1000000000000000000000000000 (by decide)

/-! ## §C. The vest clock — pulling should not move the finish line

`pullVestedYield` writes `lastTransferTimestamp = block.timestamp` and leaves
`lastDepositTimestamp` alone, so `vestingPeriodEnd` is fixed by the last *deposit* and a pull
cannot postpone it. The model's `pullVestedYield` sets `vestStart := s.now`, and `vestStart` is
the model's only clock — it plays both roles at once.
-/

/-- The pull, restricted to the clock fields, as transcribed from `pullVestedYield`: the accrual
anchor moves, the end does not — because `periodEnd` reads `lastDeposit`, which this does not
write. -/
def VestState.afterPull (v : VestState) : VestState :=
  { v with fullyVested := 0, lastTransfer := v.now }

/-- **In this transcription, `periodEnd` reads no field that `afterPull` writes**, so pulling
cannot move the finish line. True by `rfl`: the content is entirely in `afterPull` matching
`pullVestedYield`, which is the reading Lean cannot check. Stated anyway because it is the exact
point of contrast with the model, where the same fact is *false*
(`model_pull_defers_completion`). -/
theorem periodEnd_invariant_under_pull (v : VestState) :
    v.afterPull.periodEnd = v.periodEnd := rfl

/-! ### A clock, so the repetition can be stated

`docs/06` §7.3 E1's point, applied to this module: without a `tick` the "pulls keep deferring it"
claim is not a property that can be expressed here, only a remark. `VestState.tick` advances the
transcription's clock the way `Op.tick` advances the model's, and `pullEvery` interleaves a pull
with each advance — which is the deployment's actual traffic, since `_withdraw` pulls on every
`withdraw`/`redeem`.
-/

/-- The clock, matching `Op.tick`'s role in the main model. -/
def VestState.tick (v : VestState) (dt : Nat) : VestState := { v with now := v.now + dt }

/-- `n` rounds of "advance `dt`, then pull". -/
def pullEvery (v : VestState) (dt : Nat) : Nat → VestState
  | 0 => v
  | n + 1 => ((pullEvery v dt n).tick dt).afterPull

/-- **The finish line survives arbitrarily many pulls.** The trace-level form of
`periodEnd_invariant_under_pull`: whatever the traffic, the transcribed deployment's `periodEnd`
stays where the last *deposit* put it. -/
theorem periodEnd_invariant_under_pullEvery (v : VestState) (dt : Nat) :
    ∀ n, (pullEvery v dt n).periodEnd = v.periodEnd := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- And the clock really does advance under that traffic, so the invariant above is not holding
because nothing moved. -/
theorem pullEvery_advances_the_clock (v : VestState) (dt : Nat) :
    ∀ n, (pullEvery v dt n).now = v.now + n * dt := by
  intro n
  induction n with
  | zero => simp [pullEvery]
  | succ k ih =>
    show (pullEvery v dt k).now + dt = v.now + (k + 1) * dt
    rw [ih, Nat.succ_mul]
    omega

/-! ### The same traffic against the model's clock

The model keeps no separate accrual anchor, so each pull rewrites `vestStart` to `now`. Under the
same traffic its completion time therefore moves out once per round, without bound — the
repetition the single-step `model_pull_defers_completion` could only gesture at.
-/

private theorem pv_now_here (s : State) : (pullVestedYield s).now = s.now := by
  unfold pullVestedYield; dsimp only; split <;> rfl

private theorem pv_vestPeriod_here (s : State) :
    (pullVestedYield s).vestPeriod = s.vestPeriod := by
  unfold pullVestedYield; dsimp only; split <;> rfl

/-- `n` rounds of "advance `dt`, then pull", on the model's own `State`. -/
def modelPullEvery (s : State) (dt : Nat) : Nat → State
  | 0 => s
  | n + 1 => pullVestedYield { modelPullEvery s dt n with
      now := (modelPullEvery s dt n).now + dt }

theorem modelPullEvery_now (s : State) (dt : Nat) :
    ∀ n, (modelPullEvery s dt n).now = s.now + n * dt := by
  intro n
  induction n with
  | zero => simp [modelPullEvery]
  | succ k ih =>
    show (pullVestedYield { modelPullEvery s dt k with
        now := (modelPullEvery s dt k).now + dt }).now = s.now + (k + 1) * dt
    rw [pv_now_here]
    show (modelPullEvery s dt k).now + dt = s.now + (k + 1) * dt
    rw [ih, Nat.succ_mul]
    omega

theorem modelPullEvery_vestPeriod (s : State) (dt : Nat) :
    ∀ n, (modelPullEvery s dt n).vestPeriod = s.vestPeriod := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show (pullVestedYield { modelPullEvery s dt k with
        now := (modelPullEvery s dt k).now + dt }).vestPeriod = s.vestPeriod
    rw [pv_vestPeriod_here]
    exact ih

/-- **The model's completion time moves out once per pull, without bound.**

After `n + 1` rounds the model's schedule ends at `s.now + (n+1) * dt + vestPeriod`, which grows
linearly in the number of pulls. The transcribed deployment's `periodEnd` does not move at all
(`periodEnd_invariant_under_pullEvery`), so the gap between them is unbounded.

The hypothesis is the same one `model_pull_defers_completion` carries, at the round in question:
that round's pull must actually move yield, since `pullVestedYield` is the identity otherwise. -/
theorem model_pullEvery_defers_without_bound (s : State) (dt n : Nat)
    (h_moves : 0 < (modelPullEvery s dt n).fullyVestedAmount
      + newlyVestedAmount { modelPullEvery s dt n with
          now := (modelPullEvery s dt n).now + dt } ((modelPullEvery s dt n).now + dt)) :
    (modelPullEvery s dt (n + 1)).vestStart + (modelPullEvery s dt (n + 1)).vestPeriod
      = s.now + (n + 1) * dt + s.vestPeriod := by
  have hvs : (modelPullEvery s dt (n + 1)).vestStart = (modelPullEvery s dt n).now + dt := by
    show (pullVestedYield { modelPullEvery s dt n with
        now := (modelPullEvery s dt n).now + dt }).vestStart = _
    unfold pullVestedYield
    dsimp only
    rw [if_neg (by
      show ¬ ((modelPullEvery s dt n).fullyVestedAmount
        + newlyVestedAmount { modelPullEvery s dt n with
            now := (modelPullEvery s dt n).now + dt } ((modelPullEvery s dt n).now + dt) = 0)
      omega)]
  rw [hvs, modelPullEvery_vestPeriod s dt (n + 1), modelPullEvery_now s dt n, Nat.succ_mul]
  omega

/-- **The model's finish line moves with every pull that actually moves yield**, taken after the
clock has started. Both hypotheses are material: `pullVestedYield` is the identity when nothing
has vested, and the jump is zero when `vestStart = now`. Under them, the model's completion time
— `vestStart + vestPeriod` — moves forward by exactly the elapsed time, while the transcribed
deployment's stays put (`periodEnd_invariant_under_pull`).

The repeated case is `model_pullEvery_defers_without_bound` above: under `n` rounds of
"advance, then pull" — the deployment's own traffic, since it pulls on every `withdraw`/`redeem` —
the model's completion time is `s.now + n * dt + vestPeriod`, growing linearly, while the
transcription's `periodEnd` does not move at all
(`periodEnd_invariant_under_pullEvery`). *Still not proved here:* that this makes the model
under-report `totalAssets` and the share price. There is no `totalAssets` comparison and no
share-price comparison in this file. -/
theorem model_pull_defers_completion (s : State)
    (h_start : s.vestStart < s.now)
    (h_nonzero : 0 < s.fullyVestedAmount + newlyVestedAmount s s.now) :
    (pullVestedYield s).vestStart + s.vestPeriod
      = (s.vestStart + s.vestPeriod) + (s.now - s.vestStart) ∧
    s.vestStart + s.vestPeriod < (pullVestedYield s).vestStart + s.vestPeriod := by
  have hv : (pullVestedYield s).vestStart = s.now := by
    unfold pullVestedYield
    dsimp only
    rw [if_neg (by omega)]
  constructor
  · rw [hv]; omega
  · rw [hv]; omega

/-- A closed arithmetic witness for the size of the deferral: a 200-unit pool over a 10-tick
period, pulled at the midpoint. Every conjunct below is about the **model** (`State`,
`newlyVestedAmount`, `pullVestedYield`); the deployment's side is not computed here, though by
`periodEnd_invariant_under_pull` its finish line would still be tick 10. The model, having
restarted its clock, has streamed only half of the remaining 100 by then, and does not finish
until tick 15. -/
theorem vest_stretch_witness :
    ∃ (s : State),
      s.vestTotal = 200 ∧ s.vestPeriod = 10 ∧ s.vestStart = 0 ∧ s.now = 5 ∧
      -- `model_pull_defers_completion`'s two hypotheses hold here, so it is not vacuous
      s.vestStart < s.now ∧ 0 < s.fullyVestedAmount + newlyVestedAmount s s.now ∧
      newlyVestedAmount s s.now = 100 ∧
      -- after the pull the model's clock restarts at 5 with 100 left …
      (pullVestedYield s).vestStart = 5 ∧ (pullVestedYield s).vestTotal = 100 ∧
      -- … so at the deployment's finish line (tick 10) only half of it has streamed
      newlyVestedAmount (pullVestedYield s) 10 = 50 ∧
      -- and the model does not finish until tick 15
      newlyVestedAmount (pullVestedYield s) 15 = 100 := by
  refine ⟨{ (default : State) with vestTotal := 200, vestPeriod := 10, vestStart := 0, now := 5 },
    rfl, rfl, rfl, rfl, by decide, by decide, by decide, ?_, ?_, by decide, by decide⟩ <;> rfl

end Apyx
