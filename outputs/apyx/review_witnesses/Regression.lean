import D2fsSpecs.Safety

/-!
# Regression tests for the ERC-4626 pricing fix

These are the five counterexamples from `code_review_lean.md` §1.0, re-pointed at the **fixed**
model. Before the fix each of these files proved the model *violated* a README §4.2 headline
claim; each assertion below now pins the corrected behaviour instead, so the holes cannot
silently reopen.

The fix, grounded in the verified deployment (`../deployment_ground_truth.md`):

* `computeExchangeRate` is the **live** price `((totalAssets + 1) * ray) / (totalSupply_apyUSD + 1)`,
  matching `ApyUSD`'s stateless `totalAssets()`-based reads and OpenZeppelin 5.5.0's virtual
  share / virtual asset (`_decimalsOffset() = 0`, so `10**0 = 1`).
* Every conversion and every `step` branch prices off it. The `exchangeRate` **field** is now a
  published record only — it is never a pricing input.

All assertions are `by decide` / `rfl`; no `native_decide`.

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

/-- `no_dilution` now applies here with **no** side conditions — the `hbacked` and
    `0 < totalSupply_apyUSD` hypotheses it used to need are gone. -/
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

/-! ## R4 — the `x / 0 = 0` vault drain is structurally impossible

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

/-- **The fix.** Address `9` holds no shares, so the withdrawal reverts. -/
example : step u0 (Op.withdraw 100 9) 9 = none := by decide

/-- The denominator of the live rate is `totalSupply_apyUSD + 1`, so it is positive in every
    state — the whole `x / 0` class is unreachable, not merely unwitnessed. -/
example (s : State) : 0 < s.totalSupply_apyUSD + 1 := Nat.succ_pos _

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

end Apyx
