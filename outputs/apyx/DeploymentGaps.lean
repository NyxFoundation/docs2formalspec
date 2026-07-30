import D2fsSpecs.Apyx

/-!
# Three more mechanisms the model does not have, from the deployed Solidity

Companion to `DeploymentFees.lean`. Same method: verified sources from sourcify, live reads
against mainnet, formalize what the documentation corpus never mentioned. Sources here are
`src/ApxUSD.sol` (impl `0xdd71fd677fde2ed2579a3c45204f41a11016ccb4`) and `src/LinearVestV0.sol`
(`0x0d62b4cc02b4b51ed19ddf41d7a7979cf394c99f`, not behind a proxy).

**§A. `LinearVestV0.setBeneficiary` — a single admin key drains the whole vesting pool.**
`pullVestedYield()` is `onlyBeneficiary` and pays `vestedAmount()` **to the beneficiary**. The
beneficiary is admin-settable with no timelock and no consent from the vault. So one compromised
admin key redirects every accrued-but-unpulled unit of yield to an address of its choosing. Live
read: `vestedAmount() = 122,187.95…` apxUSD sitting pullable right now. The model has no
`setBeneficiary` operation at all, so `BlastRadius.lean`'s "admin alone cannot touch balances"
result is silent about this channel rather than covering it.

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
restarts the schedule. Since the deployment pulls on *every* `withdraw`/`redeem`, the model's
yield is perpetually deferred relative to the chain's.
-/

namespace Apyx

/-! ## §A. The vesting beneficiary is a single-key drain

A faithful miniature of `LinearVestV0`, in the style of the wrapper machines in
`BlastRadius.lean`: only the fields the drain depends on, with the deployment's own guards.
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

/-- **A single admin key redirects the entire vesting pool.**

Two calls: the admin points the beneficiary at an address it controls, and that address pulls.
The attacker ends holding exactly the yield that was owed to the vault, and the vault's balance
never moves. The contrast conjunct is the point — from the same state, the attacker pulling
*without* the beneficiary change is refused outright (`onlyBeneficiary`), so the admin call is
doing all the work.

`BlastRadius.lean`'s `admin_cannot_touch_balances` and the `admin alone` row of
`single_key_bounds` say a compromised admin extracts zero. Both are true **of the model**, which
has no `setBeneficiary` operation. On the deployed system this path exists, needs one key, and
at the live `vestedAmount()` has roughly 122k apxUSD standing in it. -/
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
  refine ⟨{ vestingAmount := 0, fullyVested := 100, lastDeposit := 0, lastTransfer := 0
            period := 1, beneficiary := 1, bal := fun _ => 0, now := 0 },
          _, _, 1, 2, rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same drain with the yield **still streaming** rather than already realized, so the
amount taken is the live `vestedAmount()` reading rather than a pre-banked figure: half of a
200-unit pool at the midpoint of its period. -/
theorem admin_redirect_takes_the_live_reading :
    ∃ (v v1 v2 : VestState) (attacker : Address),
      v.vested = 100 ∧
      setBeneficiary v attacker = some v1 ∧
      pullVest v1 attacker = some v2 ∧
      v2.bal attacker = 100 := by
  refine ⟨{ vestingAmount := 200, fullyVested := 0, lastDeposit := 0, lastTransfer := 0
            period := 10, beneficiary := 1, bal := fun _ => 0, now := 5 },
          _, _, 2, by decide, rfl, rfl, rfl⟩

/-! ## §B. The supply cap, and the coalition that lifts it -/

/-- `ApxUSD.mint`'s guard: `totalSupply() + amount <= supplyCap`. -/
def mintUnderCap (cap supply amount : Nat) : Option Nat :=
  if supply + amount ≤ cap then some (supply + amount) else none

/-- `setSupplyCap`'s only guard: the new cap may not fall below the current supply. It may rise
without limit. -/
def setCap (cap supply newCap : Nat) : Option Nat :=
  if newCap < supply then none else some newCap

/-- **A lone compromised minter is bounded by the cap**, at every step and hence over any run:
no sequence of successful mints puts the supply above it. -/
theorem lone_minter_bounded (cap supply amount supply' : Nat)
    (h : mintUnderCap cap supply amount = some supply') :
    supply' ≤ cap := by
  unfold mintUnderCap at h
  split at h
  · rename_i hle
    have heq := Option.some.inj h
    omega
  · exact absurd h (by simp)

/-- The bound is inherited by any run of mints against a fixed cap. -/
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

/-- **The cap is not a bound on a coalition.** For any target supply, an admin raises the cap to
it and the minter mints straight to it — two keys, two calls, no timelock in between.

Same shape as `admin_rfq_coalition_drains`: each key alone is bounded (`lone_minter_bounded` for
the minter; the admin cannot mint at all), and the pair is unbounded. The model expresses
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

/-- The deployment's pull, restricted to the clock fields: the accrual anchor moves, the end
does not. -/
def VestState.afterPull (v : VestState) : VestState :=
  { v with fullyVested := 0, lastTransfer := v.now }

/-- **The deployment's finish line is invariant under pulling.** -/
theorem periodEnd_invariant_under_pull (v : VestState) :
    v.afterPull.periodEnd = v.periodEnd := rfl

/-- And under any number of pulls. -/
theorem periodEnd_invariant_under_pulls (v : VestState) :
    ∀ n, (Nat.rec v (fun _ w => w.afterPull) n : VestState).periodEnd = v.periodEnd := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- **The model's finish line moves with every pull.** `pullVestedYield` re-anchors `vestStart`
at `now`, so the model's completion time — `vestStart + vestPeriod` — jumps forward by exactly
the time elapsed since the schedule began. The deployment's stays put
(`periodEnd_invariant_under_pull`).

Because the deployment pulls on *every* `withdraw`/`redeem`, this is not a corner case: in a
vault with steady unlock traffic the model's yield never finishes streaming, while the chain's
finishes on the original schedule. The model therefore under-reports `totalAssets`, and so the
share price, relative to the deployed system — the conservative direction, but a systematic one,
and it means the model's vesting theorems describe a slower schedule than the real one. -/
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
period, pulled at the midpoint. The deployment has the remaining 100 fully streamed by tick 10.
The model, having restarted its clock, has streamed only half of what remains by then — the
schedule now runs to tick 15. -/
theorem vest_stretch_witness :
    ∃ (s : State),
      s.vestTotal = 200 ∧ s.vestPeriod = 10 ∧ s.vestStart = 0 ∧ s.now = 5 ∧
      newlyVestedAmount s s.now = 100 ∧
      -- after the pull the model's clock restarts at 5 with 100 left …
      (pullVestedYield s).vestStart = 5 ∧ (pullVestedYield s).vestTotal = 100 ∧
      -- … so at the deployment's finish line (tick 10) only half of it has streamed
      newlyVestedAmount (pullVestedYield s) 10 = 50 ∧
      -- and the model does not finish until tick 15
      newlyVestedAmount (pullVestedYield s) 15 = 100 := by
  refine ⟨{ (default : State) with vestTotal := 200, vestPeriod := 10, vestStart := 0, now := 5 },
    rfl, rfl, rfl, rfl, by decide, ?_, ?_, by decide, by decide⟩ <;> rfl

end Apyx
