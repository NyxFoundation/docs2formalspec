import D2fsSpecs.HolderValue
import D2fsSpecs.Invariant

/-!
# Regression tests for the ERC-4626 pricing fix

These began as the five counterexamples from `code_review_lean.md` §1.0, re-pointed at the
**fixed** model; the file now runs R1–R13 as later fixes landed. Before the fix each of the
original five proved the model *violated* a README §4.2 headline claim; each assertion below pins
the corrected behaviour instead.

Read "pins" carefully: most assertions discriminate — they would fail if the fix were reverted —
but a few are markers rather than discriminators, and those say so where they sit (§R4's
denominator note is the clearest example).

The fix, grounded in the verified deployment (`../deployment_ground_truth.md`):

* `computeExchangeRate` is the **live** price `((totalAssets + 1) * ray) / (totalSupply_apyUSD + 1)`,
  matching `ApyUSD`'s stateless `totalAssets()`-based reads and OpenZeppelin 5.5.0's virtual
  share / virtual asset (`_decimalsOffset() = 0`, so `10**0 = 1`).
* Every conversion and every `step` branch prices off it. The `exchangeRate` **field** is now a
  published record only — it is never a pricing input.

Assertions are `by decide` / `rfl` or term-mode applications of the theorems they exercise; no
`native_decide` anywhere.

Run with:
```
cd lean && lake build D2fsSpecs
lake env lean ../outputs/apyx/review_witnesses/Regression.lean
```
-/

namespace Apyx

/-! ## R1/R2 — the stale-rate dilution is gone

Formerly `W1_stale_rate_dilution.lean` / `W2_honest_lifecycle_dilution.lean`: a fully honest
trace (no compromised key) in which `computeExchangeRate` *fell* and holder `1` was diluted 25%.
-/

/-- Rate-consistent start: no shares outstanding, so the live price is par. -/
def w0 : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := ray
      yieldDistributor := 5
      vestPeriod := 100 * day
      apxUSDBal := fun a => if a = 1 then 100 else if a = 2 then 100 else 0
      totalSupply_apxUSD := 200 }

/-- Holder `1` locks 100; the yield distributor credits 100; the stream fully vests. -/
def w3 : State :=
  execTrace w0 [(Op.lockApxUSD 100, 1), (Op.creditYield 100, 5), (Op.tick (100 * day), 0)]

/-- Then holder `2` locks 100 — the step that used to dilute holder `1`. -/
def w4 : State := execTrace w3 [(Op.lockApxUSD 100, 2)]

-- The vault really is worth 2x per share at `w3`: 200 assets against 100 shares.
example : totalAssets w3 = 200 ∧ w3.totalSupply_apyUSD = 100 ∧ w3.apyUSDBal 1 = 100 := by decide

/-- **The fix.** Holder `2` is now priced at the live rate and receives the *fair* 50 shares for
    100 apxUSD. Before the fix they received 100 — pricing off a stale-low cached rate — which is
    what diluted holder `1`. -/
example : w4.apyUSDBal 2 = 50 ∧ w4.totalSupply_apyUSD = 150 := by decide

/-- **The headline that used to fail.** The live per-share price is non-decreasing across the
    deposit. `W2` proved `computeExchangeRate w4 < computeExchangeRate w3`. -/
example : computeExchangeRate w3 ≤ computeExchangeRate w4 := by decide

/-- Holder `1`'s redeemable value is untouched by holder `2`'s deposit (199 → 199). Before the
    fix it fell 200 → 150. -/
example : redeemAssets (w3.apyUSDBal 1) (computeExchangeRate w3)
        = redeemAssets (w4.apyUSDBal 1) (computeExchangeRate w4) := by decide

/-- And the depositor does not gain at anyone's expense: 100 apxUSD in, 99 of redeemable value
    out — the floor rounding goes to the protocol, per `rounding_favors_protocol`. -/
example : redeemAssets (w4.apyUSDBal 2) (computeExchangeRate w4) = 99 := by decide

/-- `no_dilution` now applies here with no *state* side conditions — the `hbacked` and
    `0 < totalSupply_apyUSD` hypotheses it used to need are gone. The structural `h ≠ caller`
    remains, and is what the trailing `by decide` discharges. -/
example : ∀ s' , step w3 (Op.lockApxUSD 100) 2 = some s' →
    s'.apyUSDBal 1 = w3.apyUSDBal 1 ∧
    convertToAssets w3 (w3.apyUSDBal 1) ≤ convertToAssets s' (s'.apyUSDBal 1) :=
  fun s' h => no_dilution w3 100 2 1 s' h (by decide)

/-! ## R3 — the inflation attack is mitigated, and the residue is faithful

Formerly `W3_inflation_attack.lean`. This one is **not** fully closed, and that is deliberate:
the deployment's `_decimalsOffset()` is `0`, so the only structural defence is OpenZeppelin's
single virtual share. Modelling more protection than the chain has would be the wrong fix.
-/

/-- Attacker `3` holds the one outstanding share; the vault holds 200 assets. -/
def t0 : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := 200 * ray
      vaultApxUSDBal := 200
      totalSupply_apyUSD := 1
      apyUSDBal := fun a => if a = 3 then 1 else 0
      apxUSDBal := fun a => if a = 2 then 150 else 0
      totalSupply_apxUSD := 150 }

def t1 : State := execTrace t0 [(Op.lockApxUSD 150, 2)]

/-- **The fix.** The victim now receives a share instead of zero: the virtual share halves the
    quoted price, so 150 apxUSD clears one whole share. `W3` proved `t1.apyUSDBal 2 = 0`. -/
example : t1.apyUSDBal 2 = 1 := by decide

/-- **The residue, stated honestly.** The victim still takes a haircut (150 in, 117 of redeemable
    value out) and the attacker still gains (100 → 117). Sub-share dust rounds to the pool, which
    is exactly what `previewDeposit(1 wei) = 0` does on-chain. The user-side defence is
    `depositForMinShares`; the protocol-side defence would be a non-zero `_decimalsOffset`. -/
example : redeemAssets (t1.apyUSDBal 2) (computeExchangeRate t1) = 117
        ∧ redeemAssets (t0.apyUSDBal 3) (computeExchangeRate t0) = 100
        ∧ redeemAssets (t1.apyUSDBal 3) (computeExchangeRate t1) = 117 := by decide

/-! ## R4 — the `x / 0 = 0` vault drain is closed on the live rate

Formerly `W4_zero_rate_drain.lean`: with `exchangeRate = 0` (the `default`), `withdrawShares`
returned 0, the `apyUSDBal` guard read `0 < 0`, and an address holding **no shares** drained the
vault into its own unlock position, burning nothing.
-/

def u0 : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := 0
      vaultApxUSDBal := 100
      totalSupply_apyUSD := 100
      apyUSDBal := fun a => if a = 1 then 100 else 0 }

/-- The stored field is still 0 — but nothing prices off it any more, and the live rate is par. -/
example : u0.exchangeRate = 0 ∧ withdrawShares 100 (computeExchangeRate (pullVestedYield u0)) = 100 := by
  decide

/-- **The fix.** The withdrawal reverts. The operative cause is the live rate being par, so
    `withdrawShares 100 = 100 > 0` and the share-balance guard bites on address `9`, who holds
    none — before the fix the rate floored to 0, the cost was 0, and the guard read `0 < 0`. -/
example : step u0 (Op.withdraw 100 9) 9 = none := by decide

/-- `Nat.succ_pos` on the live rate's denominator expression. Retained as a marker of what the
    `+1` buys, but note it is a tautology about any `Nat` and mentions `computeExchangeRate`
    nowhere — it would pass with or without the fix, and R4b below is where the real content
    is. -/
example (s : State) : 0 < s.totalSupply_apyUSD + 1 := Nat.succ_pos _

/-! ### R4b — the rate itself can still floor to zero, and that needed its own guard

Found while re-reviewing the R4 fix. `computeExchangeRate` is
`((totalAssets + 1) * ray) / (totalSupply_apyUSD + 1)`, which floors to **0** whenever
`(totalAssets + 1) * ray < totalSupply_apyUSD + 1` — roughly `totalSupply_apyUSD > totalAssets * 1e27`.
A non-zero denominator therefore did *not* close the `x / 0` class: `withdrawShares assets 0` is
still `0`, so the share-balance guard read `0 < 0` and the drain from R4 came back in that corner.

On-chain the property is structural rather than incidental: `previewWithdraw` is
`ceil(assets * (totalSupply + 1) / (totalAssets + 1))`, whose denominator is at least 1, so for
`assets ≥ 1` it is at least 1 — a positive withdrawal always costs positive shares. `step` now
enforces exactly that.
-/

/-- `totalAssets = 1` but ~`2 * ray` shares outstanding, so the live rate floors to 0 — with a
    **funded** vault, which is what made the old corner exploitable. -/
def k0 : State :=
  { (default : State) with
      globalPause := false
      vaultApxUSDBal := 1
      totalSupply_apyUSD := 2 * ray + 5
      apyUSDBal := fun a => if a = 1 then 2 * ray + 5 else 0 }

example : totalAssets k0 = 1 ∧ computeExchangeRate k0 = 0 := by decide

/-- And `withdrawShares` really does return 0 there, which is what bypassed the share guard. -/
example : withdrawShares 1 (computeExchangeRate (pullVestedYield k0)) = 0 := by decide

/-- **The fix.** Address `9` holds no shares; the withdrawal reverts instead of draining. Before
    the guard this returned `some`, moved the vault's asset out, burned nothing, and left `9`
    holding a claimable unlock position. -/
example : step k0 (Op.withdraw 1 9) 9 = none := by decide

/-- Nothing moved. -/
example : (execTrace k0 [(Op.withdraw 1 9, 9)]).vaultApxUSDBal = 1
        ∧ (execTrace k0 [(Op.withdraw 1 9, 9)]).unlockRequests 0 = none := by decide

/-! ### R4c — `lockApxUSD` and `redeem` needed the same guard as `withdraw`

The re-review of R4b found that only `withdraw` had been guarded. In the same zero-rate corner,
`lockApxUSD` turned a deposit into a pure donation (assets into the vault, 0 shares out) and
`redeem` burned shares for 0 assets. Both are now guarded, and the guard is narrow: it fires only
when the *rate itself* is 0, so faithful sub-share dust rounding still succeeds.
-/

def z0 : State :=
  { (default : State) with
      globalPause := false
      vaultApxUSDBal := 9
      totalSupply_apyUSD := 10 ^ 28
      apyUSDBal := fun a => if a = 1 then 10 ^ 28 else 0
      apxUSDBal := fun a => if a = 2 then 1000 else 0
      totalSupply_apxUSD := 1000 }

example : totalAssets z0 = 9 ∧ computeExchangeRate z0 = 0 := by decide

/-- All three degenerate paths revert. -/
example : step z0 (Op.lockApxUSD 1000) 2 = none := by decide
example : step z0 (Op.redeem (10 ^ 28) 1) 1 = none := by decide
example : step z0 (Op.withdraw 9 9) 9 = none := by decide

/-- **The guards are narrow.** A healthy genesis-shaped state still deposits 1:1. -/
def h0 : State :=
  { (default : State) with
      globalPause := false
      apxUSDBal := fun a => if a = 2 then 1000 else 0
      totalSupply_apxUSD := 1000 }

example : computeExchangeRate h0 = ray ∧
    (execTrace h0 [(Op.lockApxUSD 1000, 2)]).apyUSDBal 2 = 1000 := by decide

/-- And **sub-share dust still rounds to zero shares and still succeeds** — that behaviour is
    faithful (`previewDeposit(1 wei) = 0` read on-chain), so the guard must not catch it. -/
example : lockShares 1 (computeExchangeRate t0) = 0 ∧ step t0 (Op.lockApxUSD 1) 2 ≠ none := by
  decide

/-! ## R5 — the first depositor is no longer robbed

Formerly `W5_first_depositor_steal.lean`: from a `default`-derived state (`exchangeRate = 0`) the
first depositor received 0 shares for 100 apxUSD, and the next caller redeemed the whole vault.
-/

def s0 : State :=
  { (default : State) with
      globalPause := false
      apxUSDBal := fun a => if a = 2 then 100 else if a = 3 then 1 else 0
      totalSupply_apxUSD := 101 }

def s1 : State := execTrace s0 [(Op.lockApxUSD 100, 2)]

/-- **The fix.** The first depositor gets 100 shares for 100 apxUSD, 1:1 at par. `W5` proved
    `s1.apyUSDBal 2 = 0` and `s1.totalSupply_apyUSD = 0` with the vault holding their 100. -/
example : s1.apyUSDBal 2 = 100 ∧ s1.totalSupply_apyUSD = 100 ∧ s1.vaultApxUSDBal = 100 := by
  decide

/-- Zero supply prices at par rather than at zero, which is what made the old hole reachable. -/
example : computeExchangeRate (default : State) = ray := by decide

/-! ## R6 — settling a standard unlock no longer strands the next request

`code_review_lean.md` §2.2: `claimUnlock` burned the receipt but left `unlockRequests id` and
`unlockRequestId owner` set. A later `requestUnlock` therefore topped up the already-settled
entry, and since the claim guard needs `unlockTokenOwner id = some owner` — which the burn had
set to `none` — the topped-up amount became **permanently unclaimable**.

`retireStandardUnlock` now clears all three, matching `CommitToken.redeem`, which deletes the
request in the same call that burns.
-/

/-- Holder `1` has a matured position for 50 and 100 apxUSD in hand. -/
def c0 : State :=
  { (default : State) with
      globalPause := false
      now := cooldownPeriod
      apxUSDBal := fun a => if a = 1 then 100 else 0
      totalSupply_apxUSD := 150
      nextUnlockId := 1
      unlockRequestId := fun a => if a = 1 then some 0 else none
      unlockRequests := fun i => if i = 0 then some (1, 50, 0) else none
      unlockTokenOwner := fun i => if i = 0 then some 1 else none
      unlockTokenAmount := fun i => if i = 0 then 50 else 0 }

def c1 : State := execTrace c0 [(Op.claimUnlock 0, 1)]

/-- **The fix.** Settling pays out *and* retires the entry and the pointer. -/
example : c1.apxUSDBal 1 = 150 ∧ c1.unlockRequests 0 = none ∧ c1.unlockRequestId 1 = none := by
  decide

/-- A later request opens a **fresh** position rather than topping up the dead one. -/
def c2 : State := execTrace c1 [(Op.requestUnlock 100, 1)]

example : c2.unlockRequestId 1 = some 1
        ∧ c2.unlockRequests 1 = some (1, 100, cooldownPeriod + cooldownPeriod)
        ∧ c2.unlockTokenOwner 1 = some 1
        ∧ c2.unlockRequests 0 = none := by decide

/-- **And it is claimable.** Before the fix this 100 apxUSD was stranded for good. -/
example : (execTrace c2 [(Op.tick cooldownPeriod, 0), (Op.claimUnlock 1, 1)]).apxUSDBal 1 = 150 := by
  decide

/-! ## R7 — `creditYield` no longer credits the USDC reserve

`code_review_lean.md` §2.1: the op added `amount` to **both** `usdcReserve` and the vest pool,
so one dollar of yield inflated the collateral side of `Solvent` /
`req_overcollateralization_limit` for free. On-chain `IVesting.depositYield(amount)` moves apxUSD
into the vesting contract and touches nothing else; the USDC redemption reserve is
`RedemptionPoolV0`, a different contract.
-/

def y0 : State :=
  { (default : State) with yieldDistributor := 5, usdcReserve := 777, vestPeriod := 100 * day }

/-- **The fix.** The reserve is untouched; only the vest pool grows. -/
example : (execTrace y0 [(Op.creditYield 100, 5)]).usdcReserve = 777
        ∧ (execTrace y0 [(Op.creditYield 100, 5)]).vestTotal = 100 := by decide

/-- Lifted to the role: a compromised `yieldDistributor` cannot move the reserve *at all* over
    any trace. This used to be stated as `s.usdcReserve ≤ …` — non-decreasing — because the op
    did credit it. -/
example (s : State) (σ : List (Op × Address)) (h : ∀ p ∈ σ, DistributorOp p.1) :
    (execTrace s σ).usdcReserve = s.usdcReserve :=
  (yield_distributor_trace_blast_radius s σ h).2.1

/-! ## R8 — the rate limiter is metered by the base clock, not by a free counter

`code_review_lean.md` §1.2: `rate_limit_linear_bound`'s wrapper carried its own
`RLOp.advanceEpoch` action — free, permissionless, unrelated to `base.now` — so the theorem
counted markers the attacker had placed in their own trace. `[drain, advanceEpoch, drain,
advanceEpoch, …]` drained the whole reserve without a single unit of time passing.

The wrapper now has no clock of its own. Allowance is derived from `base.now`, and `base.now`
moves only through `Op.tick`, so `docs/06` §7.3's E1 is what the bound rests on.
-/

def b0 : State :=
  { (default : State) with
      globalPause := false, admin := 7, usdcReserve := 1000, now := 0 }

/-- Window 100 clock units, allowance 10 per window, meter empty. -/
def rl0 : RLState := ⟨b0, 0, 100, 10, 0⟩

example : allowance rl0 = 10 := by decide

/-- **The old attack, now defused.** Twenty withdrawals with the clock standing still get one
    window's allowance out in total — not twenty. -/
example : (execTrace2 rl0 (List.replicate 20 (Op.withdrawReserve 10 7, 7))).base.usdcReserve = 990
        ∧ (execTrace2 rl0 (List.replicate 20 (Op.withdrawReserve 10 7, 7))).base.now = 0 := by
  decide

/-- **And allowance really is bought with time.** The same twenty withdrawals, with a full
    window ticked between each, get 200 out — exactly linear in elapsed time. -/
example :
    (execTrace2 rl0
      ((List.replicate 20 [(Op.withdrawReserve 10 7, 7), (Op.tick 100, 7)]).flatten)).base.usdcReserve
      = 800 := by decide

/-- The headline bound, instantiated at the no-time trace. -/
example : b0.usdcReserve
      - (execTrace2 rl0 (List.replicate 20 (Op.withdrawReserve 10 7, 7))).base.usdcReserve
    ≤ rl0.cap
      * (((execTrace2 rl0 (List.replicate 20 (Op.withdrawReserve 10 7, 7))).base.now - rl0.t0)
          / rl0.window + 1) :=
  rate_limit_linear_bound rl0 _ (by decide)

/-! ## R9 — the timelock window is real elapsed time, and the escape is usable

`code_review_lean.md` §1.2 recorded two defects in this wrapper. It carried its own clock
field advanced by a free `TLOp.tick`, unrelated to `base.now`, so the guarantee counted
wrapper tokens rather than time. And `queue` accepted *any* operation while `execute` was the
only route to the base state, so a user wanting to exit had to queue their own redemption and
wait the same `delay` — the window its name promised did not exist.

Now the clock **is** `base.now`, moved only through the base `step`, and `direct` runs
non-privileged operations immediately while refusing every `AdminOp`.
-/

def tb : State :=
  { (default : State) with
      globalPause := false, emergencyFlag := true, admin := 7,
      totalSupply_apxUSD := ray, totalCollateralValue := 1, redemptionValue := 0,
      whitelist := fun _ => true, apxUSDBal := fun a => if a = 1 then 100 else 0,
      now := 1000 }

/-- Timelock of 500 clock units, empty queue. -/
def tl0 : TLState := ⟨tb, [], 500⟩

/-- **`catastrophicBackstop` cannot bypass the queue.** (The general fact — `direct` refuses
    every `AdminOp` — is `step2tl`'s `isAdminOp` guard; only this instance is exhibited here.) -/
example : step2tl tl0 (TLOp.direct Op.catastrophicBackstop 7) = none := by decide

/-- Queueing announces without applying: the base state is bitwise untouched. -/
def q : TLState := execTraceTL tl0 [TLOp.queue Op.catastrophicBackstop 7]

example : q.base.redemptionValue = 0 ∧ q.base.now = 1000 ∧ q.pending.length = 1 := by decide

/-- **The window is measured on the base clock.** One unit short and the change does not land. -/
example : (execTraceTL q [TLOp.direct (Op.tick 499) 0, TLOp.execute 0]).base.redemptionValue = 0
        ∧ (execTraceTL q [TLOp.direct (Op.tick 499) 0, TLOp.execute 0]).pending.length = 1 := by
  decide

/-- At the full delay it lands — so the guarantee is not achieved by making `execute`
    unsatisfiable. -/
example : (execTraceTL q [TLOp.direct (Op.tick 500) 0, TLOp.execute 0]).base.redemptionValue = 1
        ∧ (execTraceTL q [TLOp.direct (Op.tick 500) 0, TLOp.execute 0]).pending.length = 0 := by
  decide

/-- **And the escape route is usable mid-window.** A holder *initiates* an exit through `direct`
    — unqueued, no `AdminOp` involved — while the queued change is still pending and the old
    parameters are still in force. This is what the wrapper previously could not do, because
    `direct` did not exist.

    Read the postcondition narrowly. `requestUnlock` opens a position; it does **not** return
    funds, and the position matures only after `cooldownPeriod` (20 days = 1728000 clock units)
    against a `delay` of 500 here — some 3456 windows after the queued `catastrophicBackstop`
    would land. So `apxUSDBal 1 = 0` below records the burn, not a completed exit, and it is what
    a confiscation would also look like. What the wrapper buys is an unqueued *entry point*
    during the window, not settlement within it. -/
example :
    (execTraceTL q [TLOp.direct (Op.tick 100) 0, TLOp.direct (Op.requestUnlock 100) 1]).base.apxUSDBal 1
        = 0
      ∧ (execTraceTL q [TLOp.direct (Op.tick 100) 0,
          TLOp.direct (Op.requestUnlock 100) 1]).base.redemptionValue = 0
      ∧ (execTraceTL q [TLOp.direct (Op.tick 100) 0,
          TLOp.direct (Op.requestUnlock 100) 1]).pending.length = 1 := by decide

/-! ## R10 — the per-holder measure now covers the payout channels

`code_review_lean.md` flagged twice that `Safety.valueAt` omits pending unlock positions — the
place `requestUnlock`/`withdraw`/`redeem` put the payout — so the caller laws read as "the holder
loses value" when the truth is "the holder is not extracting value".
[`../HolderValue.lean`](../HolderValue.lean) closes the measure and proves the three channels
generally. This section pins the arithmetic on a concrete holder.
-/

def pv0 : State :=
  { (default : State) with
      globalPause := false
      apxUSDBal := fun a => if a = 1 then 100 else 0
      totalSupply_apxUSD := 100
      -- historically load-bearing: the derived `default` used to point every address at a
      -- phantom request id (see R11, now fixed at the root); kept as documentation
      unlockRequestId := fun _ => none }

def pv1 : State := execTrace pv0 [(Op.requestUnlock 100, 1)]

/-- The old measure records a total loss; the complete one records none. Same step. -/
example : callerValue pv0 1 = 100 ∧ callerValue pv1 1 = 0 := by decide
example : holderValue pv0 1 = 100 ∧ holderValue pv1 1 = 100 := by decide
example : netDelta pv0 pv1 1 = 0 := by decide

/-- And the gap between the two measures is exactly the position sum, in every state. -/
example (s : State) (a : Address) :
    callerValue s a + stdPositions s a + flexPositions s a = holderValue s a :=
  callerValue_add_positions s a

/-- The general form, applied here: filing is value-neutral for the filer with no side
    conditions beyond the branch and the balance. -/
example : netDelta pv0 pv1 1 = 0 :=
  requestUnlock_netDelta_zero pv0 100 1 pv1 rfl (by decide) (by decide) (by decide)

/-! ## R11 — `default : State` is the empty state now (the trap is removed, not just pinned)

Found while applying `requestUnlock_netDelta_zero` to a `default`-derived witness: the hypothesis
`unlockRequestId caller = none` came out **false**.

`unlockRequestId : Address → Option Nat`, and `Address` is `Nat`, so the type is
`Nat → Option Nat` — which `some` itself inhabits. Lean's `Inhabited` derivation picked it, so in
the derived `default : State` **every address already pointed at a request id equal to its own
address** — and `unlockTokenOwner : Nat → Option Address` has the same type, so every unlock id
also had a phantom NFT owner equal to itself, a second instance of the trap this section's own
first draft missed.

Nothing proved was wrong because of it: `requestUnlockStep` follows the pointer to
`unlockRequests`, which *was* all-`none` by default, so it falls through to the create branch and
behaves as an empty registry. But any *hypothesis* of the form "this holder has no pending
request" was false on a `default`-derived state, and a witness that assumed otherwise would be
silently vacuous rather than failing loudly.

**Fixed at the root**: `Apyx.lean` now writes the `Inhabited State` instance out field by field
— `default` is the honest empty state, and the examples below pin the two previously-trapped
fields specifically. -/

example : (default : State).unlockRequestId 7 = none := by decide
example : (default : State).unlockTokenOwner 7 = none := by decide
example : (default : State).unlockRequests 7 = none := by decide

/-- `pv0`'s explicit `unlockRequestId := fun _ => none` (kept above as documentation of the
era when it was load-bearing) is redundant now, and the hypothesis holds on `default` too. -/
example : pv0.unlockRequestId 1 = none := by decide

/-! ## R12 — the rate limiter charges destroyed claims, not just reserve outflow

The residual `code_review_lean.md` §1.2 recorded after the clock fix: the meter charged
`usdcReserve` outflow only, so a settlement at a crashed `redemptionValue` burned a holder's claim
for **nothing**, moved no reserve, and passed an arbitrarily tight limiter uncharged.

`stepCost` now charges the larger of reserve outflow and claims destroyed at par.
-/

def cb : State :=
  { (default : State) with
      globalPause := false, admin := 7, whitelist := fun _ => true,
      rfqCounterparties := [2],
      apxUSDBal := fun a => if a = 1 then 100 else 0, totalSupply_apxUSD := 100,
      rfqRequests := fun a => if a = 1 then 100 else 0,
      usdcReserve := 100, redemptionValue := ray, now := 0 }

/-- Crash the price, then settle the victim's whole request for 0 USDC. -/
def drain : List (Op × Address) :=
  [(Op.updateRedemptionValue 1, 7), (Op.executeRFQRedemption 1 100, 2)]

/-- **The fix.** With an allowance large enough to admit it, the drain is charged its full 100 —
    even though the reserve never moved. Under the old metering this cost 0. -/
example : (execTrace2 ⟨cb, 0, 100, 100, 0⟩ drain).spent = 100
        ∧ (execTrace2 ⟨cb, 0, 100, 100, 0⟩ drain).base.usdcReserve = 100
        ∧ (execTrace2 ⟨cb, 0, 100, 100, 0⟩ drain).base.totalSupply_apxUSD = 0 := by decide

/-- So a tight limiter now stops it, and the holder keeps their claim. -/
example : (execTrace2 ⟨cb, 0, 100, 10, 0⟩ drain).spent = 0
        ∧ (execTrace2 ⟨cb, 0, 100, 10, 0⟩ drain).base.apxUSDBal 1 = 100 := by decide

/-- Honest traffic is priced exactly as before: a full-price settlement of the same request moves
    100 out of the reserve and is charged 100. -/
example : (execTrace2 ⟨cb, 0, 100, 100, 0⟩ [(Op.executeRFQRedemption 1 100, 2)]).spent = 100
        ∧ (execTrace2 ⟨cb, 0, 100, 100, 0⟩
            [(Op.executeRFQRedemption 1 100, 2)]).base.usdcReserve = 0 := by decide

/-- Each half lower-bounds the per-step charge, so no single step can be metered below either
    quantity. Both are single-step results: there is no trace-level bound on claims destroyed,
    only on reserve outflow (`rate_limit_linear_bound`). -/
example (s s' : State) : s.usdcReserve - s'.usdcReserve ≤ stepCost s s' :=
  reserve_out_le_stepCost s s'
example (s s' : State) : s.totalSupply_apxUSD - s'.totalSupply_apxUSD ≤ stepCost s s' :=
  claims_out_le_stepCost s s'

/-! ## R13 — the redemption paths are deny-list gated, as the deployment gates them

`code_review_lean.md` §2.6: `redeemApxUSD`, `requestUnlock`, `flexibleRequestUnlock` and
`poolRedeem` carried no deny-list check, so the model was **more permissive than the chain**.
On-chain `ApyUSD` overrides `_update` against both `ERC20PausableUpgradeable` and
`ERC20DenyListUpgradable`, so every mint, burn and transfer is gated structurally rather than by
remembering to check in each entry point.

All four are gated now, and so are both claim paths — the examples below check each direction,
including that a clean owner on a live token still settles. (An earlier draft of this header said
"three of the four … the claim paths are still open", which its own examples twenty lines down
already refuted.)
-/

def dl : State :=
  { (default : State) with
      globalPause := false
      whitelist := fun _ => true
      denylist := fun a => a = 1
      apxUSDBal := fun a => if a = 1 then 100 else if a = 2 then 100 else 0
      totalSupply_apxUSD := 200
      usdcReserve := 100
      redemptionValue := ray
      apxUSDMarketPrice := ray - 1 }

/-- **A deny-listed holder cannot burn.** All three gated paths revert for address 1. -/
example : step dl (Op.redeemApxUSD 100) 1 = none := by decide
example : step dl (Op.requestUnlock 100) 1 = none := by decide
example : step dl (Op.flexibleRequestUnlock 100) 1 = none := by decide

/-- `poolRedeem` gates **both** parties: it burns the caller's apxUSD and credits `receiver`. -/
example : step { dl with rfqCounterparties := [2] } (Op.poolRedeem 100 1 0) 2 = none := by decide

/-- The claim paths pass the hook too. A matured position whose owner is deny-listed cannot
    settle, and neither can one while the token is paused — the mint to the owner is a token
    move, so `ApyUSD._update` gates it on-chain. -/
def dlc : State :=
  { dl with
      now := cooldownPeriod
      nextUnlockId := 1
      unlockRequestId := fun a => if a = 1 then some 0 else none
      unlockRequests := fun i => if i = 0 then some (1, 50, 0) else none
      unlockTokenOwner := fun i => if i = 0 then some 1 else none
      unlockTokenAmount := fun i => if i = 0 then 50 else 0 }

example : step dlc (Op.claimUnlock 0) 1 = none := by decide
example : step { dlc with globalPause := true, denylist := fun _ => false }
    (Op.claimUnlock 0) 1 = none := by decide

/-- And a matured position with a clean owner on a live token still settles. -/
example : step { dlc with denylist := fun _ => false } (Op.claimUnlock 0) 1 ≠ none := by decide

/-- `flexibleClaimUnlock` takes the same treatment, and **also retires its registry entry** —
    it used to burn the receipt alone, leaving `flexibleUnlockRequests id` set for ever. -/
def dlf : State :=
  { dl with
      now := minFlexibleClaim
      nextUnlockId := 1
      flexibleUnlockRequests := fun i =>
        if i = 0 then some (1, 50, 0, cooldownPeriod) else none
      unlockTokenOwner := fun i => if i = 0 then some 1 else none
      unlockTokenAmount := fun i => if i = 0 then 50 else 0 }

example : step dlf (Op.flexibleClaimUnlock 0) 1 = none := by decide
example : step { dlf with globalPause := true, denylist := fun _ => false }
    (Op.flexibleClaimUnlock 0) 1 = none := by decide

/-- With a clean owner it settles, and the entry is gone rather than left stale. -/
example : (execTrace { dlf with denylist := fun _ => false }
      [(Op.flexibleClaimUnlock 0, 1)]).flexibleUnlockRequests 0 = none := by decide

/-- And an ordinary holder is unaffected — the gate is the deny-list, not a blanket block. -/
example : step dl (Op.requestUnlock 100) 2 ≠ none := by decide
example : step dl (Op.flexibleRequestUnlock 100) 2 ≠ none := by decide

/-! ## R14 — `solvency_preserved` is not vacuous

S2 is the one trace theorem still resting on an **assumed** invariant: it requires `WellFormed` to
hold at every prefix of the trace (`∀ n, WellFormed (execTrace s (σ.take n))`), because the
aggregate ledger carries no `Σ balances = supply` fact to derive it from (§6.2). An assumed
hypothesis is worth nothing if nothing satisfies it, so this section exhibits a state and a
non-trivial trace that do.

The trace is honest traffic: the clock advances, then a whitelisted holder deposits USDC and is
minted apxUSD 1:1. Both the balance bound and the price bound survive it, and the conclusion
`Solvent` is reached rather than assumed.
-/

/-- One holder owning the whole supply, fully backed, priced at par. -/
def sv0 : State :=
  { (default : State) with
      globalPause := false
      whitelist := fun _ => true
      apxUSDBal := fun a => if a = 1 then 100 else 0
      totalSupply_apxUSD := 100
      usdcBal := fun a => if a = 1 then 50 else 0
      usdcReserve := 0
      totalCollateralValue := 100
      redemptionValue := ray }

def svTrace : List (Op × Address) := [(Op.tick 100, 0), (Op.depositUSDC 50, 1)]

/-- The three distinct prefix states, named. -/
def sv1 : State := execTrace sv0 [(Op.tick 100, 0)]
def sv2 : State := execTrace sv0 svTrace

/-- Balances are either zero or the whole supply in each state, which is what the balance half of
`WellFormed` needs. -/
private theorem svWF (t : State) (x : Nat)
    (hb : t.apxUSDBal = fun a => if a = 1 then x else 0)
    (hx : x ≤ t.totalSupply_apxUSD)
    (hp : t.redemptionValue ≤ ray) : WellFormed t := by
  refine ⟨fun a => ?_, hp⟩
  rw [hb]
  by_cases h : a = 1 <;> simp [h] <;> try omega

private theorem sv0_bal : sv0.apxUSDBal = fun a => if a = 1 then 100 else 0 := rfl
private theorem sv1_bal : sv1.apxUSDBal = fun a => if a = 1 then 100 else 0 := rfl
private theorem sv2_bal : sv2.apxUSDBal = fun a => if a = 1 then 150 else 0 := by
  funext a
  by_cases h : a = 1 <;> simp [sv2, sv0, svTrace, execTrace, step, mintApxUSD, emitEvent, h]

example : Solvent sv0 := by unfold Solvent sv0; decide

/-- The deposit really happens: supply and reserve both rise by 50. -/
example : sv2.totalSupply_apxUSD = 150 ∧ sv2.usdcReserve = 50 := by decide

/-- **The assumed invariant is satisfiable along the whole trace.** Every prefix — and there are
only three distinct ones — is well-formed. -/
theorem svTrace_wellFormed : ∀ n, WellFormed (execTrace sv0 (svTrace.take n)) := by
  have w0 : WellFormed sv0 := svWF sv0 100 sv0_bal (by decide) (by unfold sv0; decide)
  have w1 : WellFormed sv1 := svWF sv1 100 sv1_bal (by decide) (by decide)
  have w2 : WellFormed sv2 := svWF sv2 150 sv2_bal (by decide) (by decide)
  intro n
  match n with
  | 0 => exact w0
  | 1 => exact w1
  | (k + 2) =>
    have htake : svTrace.take (k + 2) = svTrace := by
      apply List.take_of_length_le; simp [svTrace]
    rw [htake]; exact w2

/-- **So S2 applies, and its conclusion is reached rather than assumed.** The trace contains none
of the five excluded operations, so `solvency_preserved` discharges to `Solvent` at the end. -/
theorem svTrace_stays_solvent : Solvent (execTrace sv0 svTrace) := by
  refine solvency_preserved sv0 svTrace (by unfold Solvent sv0; decide) svTrace_wellFormed ?_
  intro p hp
  have hcases : p = (Op.tick 100, 0) ∨ p = (Op.depositUSDC 50, 1) := by
    simpa [svTrace] using hp
  rcases hcases with rfl | rfl <;>
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩

/-! ## R15 — the internal apxUSD flow trace is executable

The aggregate trace theorem is intentionally narrower than a protocol-wide
conservation claim. This witness exercises its typed trace boundary with a
successful clock step, which must leave custody and pending obligations
unchanged. -/

theorem apxUSDFlow_tick_trace_witness :
    ApxUSDFlowTrace (default : State) [(Op.tick 1, 0)]
      (execTrace (default : State) [(Op.tick 1, 0)]) 0 := by
  have h : ApxUSDFlowTrace (default : State) [(Op.tick 1, 0)]
      ({(default : State) with now := (default : State).now + 1}) 0 := by
    refine ApxUSDFlowTrace.cons (s := (default : State))
      (s₁ := {(default : State) with now := (default : State).now + 1})
      (s₂ := {(default : State) with now := (default : State).now + 1})
      (p := (Op.tick 1, 0)) (ps := []) (fees := 0) ?_ ?_
    · exact ApxUSDFlowStep.tick _ 1 0
    · exact ApxUSDFlowTrace.nil _
  simpa [execTrace, step, apxUSDFlowStepFee] using h

example :
    apxUSDFlow (execTrace (default : State) [(Op.tick 1, 0)]) =
      apxUSDFlow (default : State) := by
  have h := apxUSDFlow_trace apxUSDFlow_tick_trace_witness
  simpa using h.2

theorem apxUSDFlow_standard_request_trace_witness :
    ApxUSDFlowTrace (default : State) [(Op.requestUnlock 0, 0)]
      (execTrace (default : State) [(Op.requestUnlock 0, 0)]) 0 := by
  have h : ApxUSDFlowTrace (default : State) [(Op.requestUnlock 0, 0)]
      (requestUnlockStep (default : State) 0 0) 0 := by
    refine ApxUSDFlowTrace.cons (s := (default : State))
      (s₁ := requestUnlockStep (default : State) 0 0)
      (s₂ := requestUnlockStep (default : State) 0 0)
      (p := (Op.requestUnlock 0, 0)) (ps := []) (fees := 0) ?_ ?_
    · exact ApxUSDFlowStep.standardRequest _ 0 0 _
        registryWellIndexed_default (by decide) (by simp [step, requestUnlockStep])
    · exact ApxUSDFlowTrace.nil _
  simpa [execTrace, step] using h

/-! ## R16 — the parameterized USDC ledger is executable

The USDC relation is intentionally parameterized because the current model
does not contain a total-supply field. This witness supplies a finite holder
support and checks the debit-to-reserve arithmetic boundary. -/

def usdcLedger0 : State :=
  { (default : State) with
      usdcBal := fun a => if a = 1 then 100 else 0 }

def usdcLedgerDebit : State :=
  { usdcLedger0 with
      usdcBal := fun a => if a = 1 then 50 else 0
      usdcReserve := 50 }

example : UsdcLedgerConsistent usdcLedger0 [1] 100 := by
  simp [UsdcLedgerConsistent, usdcLedger0, default, sumOver]

example : UsdcLedgerConsistent usdcLedgerDebit [1] 100 := by
  refine usdcLedgerConsistent_debit_to_reserve usdcLedger0 usdcLedgerDebit [1] 100
    (by simp [UsdcLedgerConsistent, usdcLedger0, default, sumOver]) 1 50 (by simp) (by simp [usdcLedger0]) ?_ rfl
  funext a
  by_cases h : a = 1 <;> simp [usdcLedger0, usdcLedgerDebit, h]

/-! ## R17 — receipt custody consistency crosses the public unlock boundary

The lifecycle lemmas are useful only if the public dispatcher can use them. This
witness checks the standard claim path on a concrete live position: the receipt,
registry amount, and retired slot agree before the step, and the relation still
holds after the public claim succeeds. -/

private theorem c0_unlockTokenLedgerConsistent :
    UnlockTokenLedgerConsistent c0 := by
  intro id hid
  have hid' : id < 1 := by simpa [c0] using hid
  have hid0 : id = 0 := by omega
  subst id
  simp [c0, default]

example : UnlockTokenLedgerConsistent c1 := by
  apply unlockTokenLedgerConsistent_claimUnlock c0 0 1 c1 c0_unlockTokenLedgerConsistent
  simp [c1, execTrace, step, c0, retireStandardUnlock, burnUnlockNFT, mintApxUSD]

/-! ## R18 — receipt consistency has exhaustive operation coverage

The receipt relation is now composed with every constructor of Op through an
explicit coverage witness. Operations that allocate or retire positions use
their dedicated theorem; all other operations are required to prove a registry
and receipt frame. The stronger composite is kept separate from ProtocolInv so
the existing solvency-scoped invariant does not silently change meaning. -/

example : ProtocolInvWithReceiptLedger (default : State) :=
  protocolInvWithReceiptLedger_default

example : UnlockTokenLedgerCoveredOp (Op.withdraw 1 1) :=
  unlockTokenLedgerCoveredOp_all (Op.withdraw 1 1)

example : UnlockTokenLedgerCoveredOp (Op.setYieldRate 25) :=
  unlockTokenLedgerCoveredOp_all (Op.setYieldRate 25)

example : UnlockTokenLedgerConsistent
    (execTrace (default : State) [(Op.tick 1, 0), (Op.requestUnlock 0, 0)]) := by
  exact unlockTokenLedgerConsistent_trace (default : State)
    [(Op.tick 1, 0), (Op.requestUnlock 0, 0)] RegistryReach.initial
    unlockTokenLedgerConsistent_default

/-! ## R19 — the USDC ledger is an explicit external effect boundary

The generic effect theorem composes debit, payout, and frame cases without
claiming that the current State contains the missing finite support or total
supply. The witness supplies a holder membership proof and a concrete debit
effect; tying a public Op to this effect remains a separate model/SPECA task. -/

example : UsdcLedgerConsistent usdcLedgerDebit [1] 100 := by
  apply usdcLedgerConsistent_effect usdcLedger0 usdcLedgerDebit [1] 100
    (by simp [UsdcLedgerConsistent, usdcLedger0, default, sumOver])
  left
  refine ⟨1, 50, by simp, by simp [usdcLedger0], ?_, rfl⟩
  funext a
  by_cases h : a = 1 <;> simp [usdcLedger0, usdcLedgerDebit, h]

/-! ## R20 — a public USDC deposit can enter the external effect boundary

Unlike R19, this witness goes through the public dispatcher. The caller is
included in the externally supplied finite support, while the operation's
USDC debit and reserve credit are extracted by depositUSDCStep_effect. -/

def usdcDepositStart : State :=
  { usdcLedger0 with whitelist := fun a => a = 1 }

def usdcDepositPost : State :=
  execTrace usdcDepositStart [(Op.depositUSDC 50, 1)]

example : UsdcLedgerConsistent usdcDepositPost [1] 100 := by
  apply usdcLedgerConsistent_effect usdcDepositStart usdcDepositPost [1] 100
    (by simp [UsdcLedgerConsistent, usdcDepositStart, usdcLedger0, default, sumOver])
  exact usdcLedgerEffect_depositUSDC usdcDepositStart 50 1 usdcDepositPost [1]
    (by simp) (by simp [usdcDepositPost, execTrace, step, usdcDepositStart,
      usdcLedger0, default, emitEvent, mintApxUSD])

/-! ## R21 — a fixed-point redemption enters the payout boundary

This state makes the post-burn overcollateralization buffer non-decreasing,
so the public redemption succeeds and pays 50 USDC from a 100-USDC reserve. -/

def usdcRedeemStart : State :=
  { (default : State) with
      globalPause := false
      whitelist := fun a => a = 1
      apxUSDBal := fun a => if a = 1 then 50 else 0
      totalSupply_apxUSD := 50
      apxUSDMarketPrice := 0
      redemptionValue := ray
      totalCollateralValue := 50
      usdcReserve := 100 }

def usdcRedeemPost : State :=
  execTrace usdcRedeemStart [(Op.redeemApxUSD 50, 1)]

example : UsdcLedgerConsistent usdcRedeemPost [1] 100 := by
  apply usdcLedgerConsistent_effect usdcRedeemStart usdcRedeemPost [1] 100
    (by simp [UsdcLedgerConsistent, usdcRedeemStart, default, sumOver])
  exact usdcLedgerEffect_redeemApxUSD usdcRedeemStart 50 1 usdcRedeemPost [1]
    (by simp) (by simp [usdcRedeemPost, execTrace, step, usdcRedeemStart,
      default, emitEvent, burnApxUSD, overcollateralizationBuffer, ray])

/-! ## R22 — RFQ payout uses the requested user's support entry

The counterparty is address 2, but the USDC credit belongs to user 1. The
external support therefore contains user 1; adding only the counterparty would
not justify the ledger coverage theorem. -/

def usdcRfqStart : State :=
  { (default : State) with
      globalPause := false
      rfqCounterparties := [2]
      whitelist := fun a => a = 1
      rfqRequests := fun a => if a = 1 then 50 else 0
      apxUSDBal := fun a => if a = 1 then 50 else 0
      totalSupply_apxUSD := 50
      redemptionValue := ray
      usdcReserve := 100 }

def usdcRfqPost : State :=
  execTrace usdcRfqStart [(Op.executeRFQRedemption 1 50, 2)]

example : UsdcLedgerConsistent usdcRfqPost [1] 100 := by
  apply usdcLedgerConsistent_effect usdcRfqStart usdcRfqPost [1] 100
    (by simp [UsdcLedgerConsistent, usdcRfqStart, default, sumOver])
  exact usdcLedgerEffect_executeRFQRedemption usdcRfqStart 1 50 2 usdcRfqPost [1]
    (by simp) (by simp [usdcRfqPost, execTrace, step, usdcRfqStart,
      default, burnApxUSD, ray])

/-! ## R23 — the admin reserve payout uses the receiver's support entry -/

def usdcWithdrawReserveStart : State :=
  { (default : State) with usdcReserve := 100 }

def usdcWithdrawReservePost : State :=
  execTrace usdcWithdrawReserveStart [(Op.withdrawReserve 50 1, 0)]

example : UsdcLedgerConsistent usdcWithdrawReservePost [1] 100 := by
  apply usdcLedgerConsistent_effect usdcWithdrawReserveStart usdcWithdrawReservePost [1] 100
    (by simp [UsdcLedgerConsistent, usdcWithdrawReserveStart, default, sumOver])
  exact usdcLedgerEffect_withdrawReserve usdcWithdrawReserveStart 50 1 0
    usdcWithdrawReservePost [1] (by simp)
    (by simp [usdcWithdrawReservePost, execTrace, step, usdcWithdrawReserveStart,
         default])

/-! ## R24 — pool settlement pays the named receiver

The approved counterparty (address 2) burns its own apxUSD, while address 1
receives the USDC. The support set follows the USDC credit, not the caller. -/

def usdcPoolRedeemStart : State :=
  { (default : State) with
      globalPause := false
      rfqCounterparties := [2]
      apxUSDBal := fun a => if a = 2 then 50 else 0
      totalSupply_apxUSD := 50
      redemptionValue := ray
      usdcReserve := 100 }

def usdcPoolRedeemPost : State :=
  execTrace usdcPoolRedeemStart [(Op.poolRedeem 50 1 50, 2)]

example : UsdcLedgerConsistent usdcPoolRedeemPost [1] 100 := by
  apply usdcLedgerConsistent_effect usdcPoolRedeemStart usdcPoolRedeemPost [1] 100
    (by simp [UsdcLedgerConsistent, usdcPoolRedeemStart, default, sumOver])
  exact usdcLedgerEffect_poolRedeem usdcPoolRedeemStart 50 1 50 2 usdcPoolRedeemPost [1]
    (by simp) (by simp [usdcPoolRedeemPost, execTrace, step, usdcPoolRedeemStart,
      default, burnApxUSD, ray])

end Apyx
