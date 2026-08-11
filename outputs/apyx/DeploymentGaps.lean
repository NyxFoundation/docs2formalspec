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

/-! ## Proof Map v3: deployment authority map

The core `State` models role addresses as caller guards.  That is not the same as proving who can
submit those calls on mainnet.  The records below consolidate the deployment-derived authority facts
already used by the companion modules.  `role 0` is recorded as the direct admin path; roles 22, 24,
and 41 are kept separate because their delays differ.  Safe membership/threshold, authority-change
and proxy-storage facts remain explicit unknowns rather than being filled with guesses. -/

structure AuthorityDeploymentRecord where
  target : String
  operation : String
  role : Nat
  executionDelay : Nat
  authorityEvidence : String
  modelOperation : String

def authorityDeploymentMap : List AuthorityDeploymentRecord :=
  [ { target := "ApyxCollateralRatioOracle"
      operation := "pushRound(int256)"
      role := 22
      executionDelay := 4 * 60 * 60
      authorityEvidence := "AccessManager role assignment; deployment-derived"
      modelOperation := "Op.setApxUSDMarketPrice" }
  , { target := "LinearVestV0"
      operation := "setBeneficiary(address)"
      role := 24
      executionDelay := 3 * day
      authorityEvidence := "AccessManager role assignment; deployment-derived"
      modelOperation := "not represented" }
  , { target := "CommitToken / UnlockingDelay"
      operation := "setUnlockingDelay(uint256)"
      role := 24
      executionDelay := 3 * day
      authorityEvidence := "AccessManager role assignment; deployment-derived"
      modelOperation := "not represented in Apyx.State" }
  , { target := "LiquidationBatcher"
      operation := "withdrawTokens(address,uint256)"
      role := 41
      executionDelay := 0
      authorityEvidence := "single EOA grant; deployment-derived"
      modelOperation := "Op.withdrawReserve" }
  , { target := "ApyUSD / UnlockReceipt"
      operation := "setFeeCurve / fee configuration"
      role := 0
      executionDelay := 0
      authorityEvidence := "restricted admin path; deployment-derived"
      modelOperation := "not represented" }
  , { target := "UUPS implementations"
      operation := "upgradeToAndCall"
      role := 24
      executionDelay := 3 * day
      authorityEvidence := "proxy authority reading; implementation refinement required"
      modelOperation := "not represented" } ]

theorem authorityDeploymentMap_has_explicit_delay_classes :
    (authorityDeploymentMap.map AuthorityDeploymentRecord.executionDelay).length = 6 := by
  rfl

def authorityDeploymentUnknowns : List String :=
  [ "Safe/multisig membership and threshold"
  , "setAuthority target and delay on every authority"
  , "UUPS implementation slot and initializer state"
  , "beneficiary/fee recipient relationship to user claim custody"
  , "complete role graph for every deployed async vault" ]

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

end Apyx
