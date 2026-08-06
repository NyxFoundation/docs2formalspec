import D2fsSpecs.HolderValue

/-!
# One fee mechanism the model lacks, and one it models with the wrong shape

Everything here is read off verified sources fetched from sourcify for implementation
`0xfd616567ecc1607f61073951a1e822f7315bb112` (`src/ApyUSD.sol`, `src/FeeCurve.sol`; solidity
0.8.30, OpenZeppelin upgradeable 5.5.0), plus live reads against the proxy
`0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A`. See `deployment_ground_truth.md`.

The model in `Apyx.lean` was built from the documentation corpus. The corpus does not mention
mechanism A **at all**; it describes mechanism B, but describes it wrongly, and the model inherits
the error. Both mechanisms are live on chain today.

## A. The vault-side unlocking fee — absent from the model entirely

`ApyUSD._withdraw` charges a fee on **every** `withdraw`/`redeem` before minting the unlock
receipt, and forwards it out of the vault:

```solidity
uint256 fee = _feeOnRaw(assets, $.unlockingFee);
super._withdraw(caller, address(this), owner, assets + fee, shares);   // burn shares for GROSS
if (fee > 0 && feeRecipient != address(0) && feeRecipient != address(this))
    IERC20(asset()).safeTransfer(feeRecipient, fee);                   // fee LEAVES the vault
IERC20(asset()).approve(address($.unlockReceipt), assets);
uint256 tokenId = $.unlockReceipt.mint(receiver, SafeCast.toUint208(assets));
```

**Live values (block-latest read, 2026-07-30):** `unlockingFee() = 1e15` = **10 bps**, and
`feeWallet() = 0x6f93635f…29dc` — neither zero nor the vault itself, so the branch that routes
the fee out is the one that fires. This is not a dormant parameter.

The model's `Op.withdraw` burns shares for `assets` and moves `assets` into the position. The
deployment burns shares for `assets + fee` and moves `assets` into the receipt, with `fee`
leaving the system. So the model **under-charges the withdrawer** and **over-states the vault**,
by exactly the fee, on every unlock. Both are the permissive direction.

`_withdraw` also carries a guard the model lacks: `if (receiver != owner) revert InvalidCaller()`.

## B. The variable-unlock fee curve — modeled, but with the wrong shape

`FeeCurveLib.fee` is a clamped, parameterized decay, and its `minDuration` field is deliberately
overloaded:

> `minDuration` carries two roles intentionally: it is both the lock duration (a receipt becomes
> claimable at `createdAt + minDuration`) and the fee-curve zero point (the fee stays at `maxFee`
> for any elapsed time `<= minDuration` and only starts decaying after that).

The model instead hardcodes a linear ramp anchored at request time with a *separate*
`minFlexibleClaim = 3 day` lock against a `cooldownPeriod = 20 day` ramp — so by the first
claimable instant the model's fee has already decayed to 299 bps. That is the origin of the
report's §2.3 finding ("the advertised 3.5% start is never charged; the real maximum is 2.99%").
`feeRate_at_first_claim` shows the deployment ties the two so that the maximum **is** charged at
the first claimable instant, and the live curve confirms it: `liveCurve` below is the struct
returned by `UnlockReceipt.feeCurve()` on mainnet, and its `minDuration` is exactly the 3-day lock.

That read also settles two numbers the corpus got wrong and the model copied. The corpus says the
fee "declines linearly over time from 3.5% down to just 0.1%". Deployed, the decay is indeed
linear (`curvature = 1e18`, the library's linear shortcut) over `minDuration = 3 days` to
`maxDuration = 20 days` — but it runs from **3.4%**, not 3.5%, down to **0%**, not 0.1%. The
model's `flexibleUnlockFee` hardcodes the corpus's 350 bps and its 10 bps floor; both are wrong,
in opposite directions.
-/

namespace Apyx

/-! ## Fixed-point conventions

`FEE_PRECISION = 1e18` in both files; the model's own amounts are unscaled (`model.md` §5, "no
decimal scaling"), so fee *rates* carry the WAD and fee *amounts* come back out in model units.
-/

/-- `FeeCurveLib.FEE_PRECISION` / `ApyUSD.FEE_PRECISION` = `1e18`. -/
def wad : Nat := 1000000000000000000

/-- `FeeCurveLib.MAX_FEE` = `0.05e18` — the hard 5% ceiling both `setUnlockingFee` and
`FeeCurveLib.requireValid` enforce. -/
def maxFeeCap : Nat := 50000000000000000

/-- `FeeCurveLib.MAX_DURATION` = `90 days`. -/
def maxCurveDuration : Nat := 90 * day

/-- `FeeCurveLib.MIN_CURVATURE` = `0.1e18`. -/
def minCurvature : Nat := 100000000000000000

/-- `FeeCurveLib.MAX_CURVATURE` = `10e18`. -/
def maxCurvature : Nat := 10000000000000000000

/-- The live `unlockingFee()` read from the proxy: `1e15` = 10 bps. -/
def liveUnlockingFee : Nat := 1000000000000000

/-- Solidity's `Math.Rounding.Ceil` on a division. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-! ## A. The vault-side unlocking fee -/

/-- `ApyUSD._feeOnRaw` — the fee **added on top of** a pre-fee amount, Ceil-rounded:
`assets.mulDiv(feePercentage, FEE_PRECISION, Math.Rounding.Ceil)`. -/
def feeOnRaw (assets feePct : Nat) : Nat :=
  if feePct = 0 then 0 else ceilDiv (assets * feePct) wad

/-- `ApyUSD._feeOnTotal` — the fee **contained in** a fee-inclusive amount:
`assets.mulDiv(feePercentage, feePercentage + FEE_PRECISION, Math.Rounding.Ceil)`. -/
def feeOnTotal (assets feePct : Nat) : Nat :=
  if feePct = 0 then 0 else ceilDiv (assets * feePct) (feePct + wad)

/-- The gross the deployment burns shares against, for a withdrawal escrowing `assets`:
`super._withdraw(..., assets + fee, ...)`. The model burns against `assets` alone. -/
def withdrawGross (assets feePct : Nat) : Nat := assets + feeOnRaw assets feePct

/-- **The fee is never rounded away.** Ceil rounding means any positive withdrawal at a positive
rate costs at least one unit — the deployment's "the holder pays at least 1 wei whenever the rate
is non-zero". So *whenever the rate is non-zero* there is no dust regime in which the two agree;
at `feePct = 0` they agree exactly. As everywhere in this module, "the chain" means the
transcription of `_feeOnRaw` above. -/
theorem feeOnRaw_pos (assets feePct : Nat) (ha : 0 < assets) (hf : 0 < feePct) :
    0 < feeOnRaw assets feePct := by
  have hw : 0 < wad := by decide
  unfold feeOnRaw ceilDiv
  rw [if_neg (by omega)]
  apply Nat.div_pos _ hw
  have h1 : 1 * 1 ≤ assets * feePct := Nat.mul_le_mul ha hf
  omega
/-- **The model under-charges every withdrawal**, strictly, at any positive rate. The deployment
pulls `assets + fee` out of the vault against the withdrawer's shares; the model pulls `assets`.

Requires `0 < assets` and a positive rate. Since `withdrawShares` is monotone in its first
argument, the deployment's share cost is at least the model's — so **both** directions of model
statement are optimistic, not one looser and one tighter: "the withdrawer pays at most X shares"
may be violated on chain because the chain charges more, and "the vault retains at least Y" may
be violated because the chain retains less. Neither transfers without re-proof. -/
theorem model_undercharges_withdraw (assets feePct : Nat) (ha : 0 < assets) (hf : 0 < feePct) :
    assets < withdrawGross assets feePct := by
  have := feeOnRaw_pos assets feePct ha hf
  unfold withdrawGross
  omega

/-- The share cost the deployment charges dominates the model's, at any rate. (`withdrawShares`
is the model's own ceil-rounded conversion; the point is the argument it is applied to.) -/
theorem withdrawShares_gross_ge_net (assets feePct R : Nat) :
    withdrawShares assets R ≤ withdrawShares (withdrawGross assets feePct) R := by
  unfold withdrawShares withdrawGross
  have hm : assets * ray ≤ (assets + feeOnRaw assets feePct) * ray :=
    Nat.mul_le_mul_right _ (by omega)
  exact Nat.div_le_div_right (by omega)

/-! ### The leak, accumulated

The fee does not stay in the vault: `feeWallet` is set to an external address, so each unlock
moves `fee` out of the system entirely. The model has no such outflow, so the two ledgers diverge
linearly in the number of unlocks — this is the shape of the divergence, not a rounding artifact.
-/

/-- The deployment's vault balance after `n` unlocks of `a` each, at rate `φ`: each step removes
the gross. -/
def vaultAfterUnlocks (v a feePct : Nat) : Nat → Nat
  | 0 => v
  | n + 1 => vaultAfterUnlocks v a feePct n - withdrawGross a feePct

/-- The model's: each step removes the net only. -/
def modelVaultAfterUnlocks (v a : Nat) : Nat → Nat
  | 0 => v
  | n + 1 => modelVaultAfterUnlocks v a n - a

private theorem vaultAfterUnlocks_closed (v a feePct : Nat) :
    ∀ k, k * withdrawGross a feePct ≤ v →
      vaultAfterUnlocks v a feePct k = v - k * withdrawGross a feePct := by
  intro k
  induction k with
  | zero => intro _; simp [vaultAfterUnlocks]
  | succ j ih =>
    intro hj
    have hj' : j * withdrawGross a feePct ≤ v := by
      have : j * withdrawGross a feePct ≤ (j + 1) * withdrawGross a feePct := by
        rw [Nat.succ_mul]; omega
      omega
    show vaultAfterUnlocks v a feePct j - withdrawGross a feePct
        = v - (j + 1) * withdrawGross a feePct
    rw [ih hj', Nat.succ_mul]
    omega

private theorem modelVaultAfterUnlocks_closed (v a : Nat) :
    ∀ k, k * a ≤ v → modelVaultAfterUnlocks v a k = v - k * a := by
  intro k
  induction k with
  | zero => intro _; simp [modelVaultAfterUnlocks]
  | succ j ih =>
    intro hj
    have hj' : j * a ≤ v := by
      have : j * a ≤ (j + 1) * a := by rw [Nat.succ_mul]; omega
      omega
    show modelVaultAfterUnlocks v a j - a = v - (j + 1) * a
    rw [ih hj', Nat.succ_mul]
    omega

/-- **The divergence is linear in the unlock count.** With enough balance to avoid truncation,
the model over-states the vault by exactly `n * feeOnRaw a φ` after `n` unlocks.

At the live rate (10 bps) that is 0.1% of every unlocked amount, accumulating linearly across
the unlock flow — a systematic accounting gap, not a corner case. The two recursions abstract the
model's and the deployment's vault updates; neither is tied to `Apyx.step` by proof, so the
correspondence to `Op.withdraw` is by inspection. -/
theorem vault_leak_linear (v a feePct n : Nat)
    (h_fund : n * withdrawGross a feePct ≤ v) :
    modelVaultAfterUnlocks v a n = vaultAfterUnlocks v a feePct n + n * feeOnRaw a feePct := by
  have hsplit : n * withdrawGross a feePct = n * a + n * feeOnRaw a feePct := by
    unfold withdrawGross; rw [Nat.mul_add]
  have hna : n * a ≤ v := by omega
  rw [modelVaultAfterUnlocks_closed v a n hna, vaultAfterUnlocks_closed v a feePct n h_fund]
  omega

/-! ### The guard the model used to lack

`_withdraw` reverts with `InvalidCaller()` unless `receiver == owner`, "to prevent third parties
from minting the UnlockReceipt to themselves". The model's `Op.withdraw assets receiver` took an
arbitrary receiver and never compared it to the share owner, so it admitted steps the chain
refuses — the same "model more permissive than the chain" direction as the deny-list gaps of §9.3,
and found the same way.

It is gated now, under the identification of the model's caller with the chain's owner. The two
theorems below are what the old permissiveness result turned into.
-/

/-- A funded, non-degenerate vault: one holder owns the whole 100-share supply against 100
assets, so the live rate is exactly `ray` and a 100-asset withdrawal costs exactly 100 shares. -/
def withdrawWitness : State :=
  { (default : State) with
      globalPause := false
      totalSupply_apyUSD := 100
      apyUSDBal := fun a => if a = 1 then 100 else 0
      vaultApxUSDBal := 100 }

/-- **The general form: the receiver is pinned to the caller.** Not a witness — every successful
withdrawal in the model has the receipt landing on the caller, so no third party can be named. -/
theorem withdraw_receiver_is_caller (s : State) (assets : Nat) (receiver caller : Address)
    (s' : State) (h : step s (Op.withdraw assets receiver) caller = some s') :
    receiver = caller := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i g
    simp only [Bool.or_eq_true, not_or, bne_iff_ne, ne_eq, Decidable.not_not] at g
    exact g.2

/-! ## B. The variable-unlock fee curve

`FeeCurveLib.fee` clamps at both ends and decays in between. The interior shape depends on
`curvature` through `powWad`, which is not modeled here — instead the decay is taken as a
parameter `powK`, so every theorem below holds for **any** curvature, including the linear and
quadratic shortcuts the library special-cases. The clamps, which is where the protocol's
guarantees actually live, are exact.
-/

/-- `FeeCurve` as declared in `src/FeeCurve.sol`. -/
structure Curve where
  minFee : Nat
  maxFee : Nat
  minDuration : Nat
  maxDuration : Nat
  curvature : Nat

/-- `FeeCurveLib.isValid` / the conjunction `requireValid` enforces. -/
def Curve.isValid (c : Curve) : Prop :=
  c.minDuration ≠ 0 ∧ c.minDuration < c.maxDuration ∧ c.maxDuration ≤ maxCurveDuration ∧
  c.minFee ≤ c.maxFee ∧ c.maxFee ≤ maxFeeCap ∧
  minCurvature ≤ c.curvature ∧ c.curvature ≤ maxCurvature

/-- `tHat = (elapsed - minDuration) * 1e18 / (maxDuration - minDuration)`. -/
def Curve.tHat (c : Curve) (elapsed : Nat) : Nat :=
  (elapsed - c.minDuration) * wad / (c.maxDuration - c.minDuration)

/-- `FeeCurveLib.fee`, with the `powWad` step abstracted as `powK` so the result covers every
admissible curvature at once. -/
def Curve.feeRate (c : Curve) (powK : Nat → Nat) (elapsed : Nat) : Nat :=
  if c.maxDuration ≤ elapsed then c.minFee
  else if elapsed ≤ c.minDuration then c.maxFee
  else c.maxFee - (c.maxFee - c.minFee) * powK (c.tHat elapsed) / wad

/-- `FeeCurveLib.feeOnAssets` — Ceil-rounded, like the vault-side fee. -/
def Curve.feeOnAssets (c : Curve) (powK : Nat → Nat) (assets elapsed : Nat) : Nat :=
  ceilDiv (assets * c.feeRate powK elapsed) wad

/-- **The advertised maximum *is* charged, at the first claimable instant.**

A receipt becomes claimable at `createdAt + minDuration`, and `fee` returns `maxFee` for every
`elapsed ≤ minDuration` — so at `elapsed = minDuration`, the earliest claim the contract permits,
the rate is exactly `maxFee`. The overload of `minDuration` is what makes this hold, and the
source comment says it is intentional.

This is the correction to the report's §2.3. The model splits the two roles across
`minFlexibleClaim = 3 day` and `cooldownPeriod = 20 day`, so its schedule has already decayed to
299 bps by the time a claim is allowed, and the report reads that as "the advertised 3.5% start
is never charged". On the deployed curve there is no such gap: the maximum is reachable, and it
is the *first* thing a claimant meets. -/
theorem feeRate_at_first_claim (c : Curve) (powK : Nat → Nat) (h : c.isValid) :
    c.feeRate powK c.minDuration = c.maxFee := by
  obtain ⟨-, hlt, -, -, -, -, -⟩ := h
  unfold Curve.feeRate
  rw [if_neg (by omega), if_pos (Nat.le_refl _)]

/-- Symmetrically, the floor is reached exactly at `maxDuration` and held after. -/
theorem feeRate_at_max_duration (c : Curve) (powK : Nat → Nat) (elapsed : Nat)
    (h : c.maxDuration ≤ elapsed) :
    c.feeRate powK elapsed = c.minFee := by
  unfold Curve.feeRate
  rw [if_pos h]

/-- **`tHat` never exceeds one, for any `elapsed` below `maxDuration`** — a strictly wider
condition than the interior branch, which also needs `minDuration < elapsed`. The numerator
`elapsed - minDuration` cannot exceed the denominator `maxDuration - minDuration`, so the
WAD-scaled ratio is at most `1e18`. The library relies on exactly this when it casts to `int256`
for `powWad` ("`tHat <= 1e18` (numerator can't exceed denominator)"). -/
theorem tHat_le_wad (c : Curve) (elapsed : Nat) (h : elapsed < c.maxDuration) :
    c.tHat elapsed ≤ wad := by
  unfold Curve.tHat
  rcases Nat.eq_zero_or_pos (c.maxDuration - c.minDuration) with hd | hd
  · rw [hd]; simp
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    have hnum : elapsed - c.minDuration ≤ c.maxDuration - c.minDuration := by omega
    calc (elapsed - c.minDuration) * wad
        ≤ (c.maxDuration - c.minDuration) * wad := Nat.mul_le_mul_right _ hnum
      _ ≤ (c.maxDuration - c.minDuration) * wad + ((c.maxDuration - c.minDuration) - 1) := by omega

/-- And never falls below `minFee`, **assuming** `powK tHat ≤ 1e18`. That is a hypothesis here,
not a consequence: `tHat_le_wad` gives `tHat ≤ 1e18`, and real exponentiation preserves it for
`k ∈ [0.1, 10]`, but `powK` is an arbitrary `Nat → Nat` and Lean proves nothing about `powWad`.
The hypothesis is discharged outright only at the library's linear shortcut
(`feeRate_ge_minFee_linear`) — which, per `liveCurve_is_linear`, is the deployed configuration. -/
theorem feeRate_ge_minFee (c : Curve) (powK : Nat → Nat) (elapsed : Nat) (h : c.isValid)
    (hpow : powK (c.tHat elapsed) ≤ wad) :
    c.minFee ≤ c.feeRate powK elapsed := by
  obtain ⟨-, -, -, hfee, -, -, -⟩ := h
  have hw : 0 < wad := by decide
  have hred : (c.maxFee - c.minFee) * powK (c.tHat elapsed) / wad ≤ c.maxFee - c.minFee := by
    calc (c.maxFee - c.minFee) * powK (c.tHat elapsed) / wad
        ≤ (c.maxFee - c.minFee) * wad / wad :=
          Nat.div_le_div_right (Nat.mul_le_mul_left _ hpow)
      _ = c.maxFee - c.minFee := Nat.mul_div_cancel _ hw
  generalize hX : (c.maxFee - c.minFee) * powK (c.tHat elapsed) / wad = X at hred
  unfold Curve.feeRate
  rw [hX]
  split
  · exact Nat.le_refl _
  · split
    · exact hfee
    · omega

/-- The linear shortcut `curvature = 1e18` is the identity on `tHat`, so `feeRate_ge_minFee`'s
hypothesis is discharged for it outright and the floor **bound** holds unconditionally rather
than under an assumption about `powK`. It is a lower bound, not an attainment: the rate meeting
`minFee` is `feeRate_at_max_duration`, which `hlt : elapsed < c.maxDuration` excludes here. -/
theorem feeRate_ge_minFee_linear (c : Curve) (elapsed : Nat) (h : c.isValid)
    (hlt : elapsed < c.maxDuration) :
    c.minFee ≤ c.feeRate id elapsed :=
  feeRate_ge_minFee c id elapsed h (tHat_le_wad c elapsed hlt)

/-- The claim-side fee, like the vault-side one, is Ceil-rounded and so never vanishes on a
positive position at a positive rate. -/
theorem feeOnAssets_pos (c : Curve) (powK : Nat → Nat) (assets elapsed : Nat)
    (ha : 0 < assets) (hr : 0 < c.feeRate powK elapsed) :
    0 < c.feeOnAssets powK assets elapsed := by
  have hw : 0 < wad := by decide
  unfold Curve.feeOnAssets ceilDiv
  apply Nat.div_pos _ hw
  have h1 : 1 * 1 ≤ assets * c.feeRate powK elapsed := Nat.mul_le_mul ha hr
  omega


/-! ### The curve is read live, not snapshotted at mint

`UnlockReceipt` stores only `(assets, createdAt)` per position. Both the claim gate and the fee
read the **current** curve:

```solidity
function isClaimable(uint256 tokenId) public view returns (bool) {
    ...
    return uint48(block.timestamp) >= pos.createdAt + $.feeCurve.minDuration;
}
function currentFee(uint256 tokenId) public view returns (uint256 feeInAssets) {
    ...
    uint48 elapsed = uint48(block.timestamp) - pos.createdAt;
    feeInAssets = $.feeCurve.feeOnAssets(pos.assets, elapsed);
}
function setFeeCurve(FeeCurve calldata curve) external restricted { ... }   // no timelock
```

`setFeeCurve` is a plain admin call whose only check is `requireValid`. Because `minDuration` is
both the lock length and the curve's zero point, one call moves **both** at once on every
outstanding receipt: positions that were claimable become locked again, and the fee they will
eventually pay is reset to the new `maxFee` — up to the 5% ceiling.

This is the same class as `CommitToken.lean`'s `raising_the_delay_unclaims_pending_requests`,
which the model does carry for the commit-token vaults. It has no counterpart for the apyUSD
unlock receipt: the model's `flexibleUnlockFee` is a fixed formula over constants, with no
operation that can change it, so the model cannot state this at all.
-/

/-- An `UnlockReceipt` position: the contract stores nothing else. -/
structure Receipt where
  assets : Nat
  createdAt : Nat

/-- `claimableAfter(tokenId)` = `createdAt + feeCurve.minDuration`, off the **live** curve. -/
def Receipt.claimableAt (r : Receipt) (c : Curve) : Nat := r.createdAt + c.minDuration

/-- `isClaimable(tokenId)`, unpaused. -/
def Receipt.isClaimable (r : Receipt) (c : Curve) (now : Nat) : Bool :=
  decide (r.claimableAt c ≤ now)

/-- `currentFee(tokenId)` — the live curve applied to the receipt's own age. -/
def Receipt.feeNow (r : Receipt) (c : Curve) (powK : Nat → Nat) (now : Nat) : Nat :=
  c.feeOnAssets powK r.assets (now - r.createdAt)

/-- `previewClaim(tokenId)` = escrowed minus the live fee. -/
def Receipt.payout (r : Receipt) (c : Curve) (powK : Nat → Nat) (now : Nat) : Nat :=
  r.assets - r.feeNow c powK now

/-! ### The curve that is actually deployed

`UnlockReceipt.feeCurve()` read from mainnet, verbatim. Every claim below about "the deployed
curve" is this struct; nothing else here is a live reading.
-/

/-- `UnlockReceipt.feeCurve()` on mainnet: linear decay from 3.4% to 0%, over days 3 to 20. -/
def liveCurve : Curve :=
  { minFee := 0
    maxFee := 34000000000000000
    minDuration := 3 * day
    maxDuration := 20 * day
    curvature := wad }

theorem liveCurve_valid : liveCurve.isValid := by
  refine ⟨?_, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · unfold liveCurve day; decide
  · unfold liveCurve day; decide
  · unfold liveCurve maxCurveDuration day; decide
  · unfold liveCurve maxFeeCap; decide
  · unfold liveCurve minCurvature wad; decide
  · unfold liveCurve maxCurvature wad; decide

/-- **The deployed curve is the library's linear shortcut**, so `feeRate_ge_minFee`'s hypothesis
about `powWad` is not merely plausible at this configuration — it is discharged, by
`feeRate_ge_minFee_linear`. -/
theorem liveCurve_is_linear : liveCurve.curvature = wad := rfl

/-- **Two numbers the corpus states and the deployment contradicts**, both copied into the model's
`flexibleUnlockFee` as `350` and `10` basis points.

The corpus says the fee "declines linearly over time from 3.5% down to just 0.1%". Deployed, the
start is 3.4% — `34000000000000000` against a 3.5% of `35000000000000000` — and the floor is
**zero**, not one tenth of a percent. The model is wrong high at the top of the ramp and wrong
high at the bottom of it. -/
theorem liveCurve_bounds_contradict_the_corpus :
    liveCurve.maxFee ≠ 35000000000000000 ∧
    liveCurve.maxFee = 34000000000000000 ∧
    liveCurve.minFee = 0 ∧
    liveCurve.minFee ≠ 1000000000000000 :=
  ⟨by decide, rfl, rfl, by decide⟩

/-- A receipt minted under a short, free curve. -/
def curveBefore : Curve :=
  { minFee := 0, maxFee := 0, minDuration := 1, maxDuration := 2, curvature := wad }

/-- What one admin call can replace it with: a hundred-fold longer lock at the 5% ceiling. Both
curves pass `requireValid`, so `setFeeCurve` accepts the swap. -/
def curveAfter : Curve :=
  { minFee := 0, maxFee := maxFeeCap, minDuration := 100, maxDuration := 200, curvature := wad }

theorem curveBefore_valid : curveBefore.isValid := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_, ?_⟩
  · unfold curveBefore maxCurveDuration day; decide
  · unfold curveBefore minCurvature wad; decide
  · unfold curveBefore maxCurvature wad; decide

theorem curveAfter_valid : curveAfter.isValid := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_, ?_⟩
  · unfold curveAfter maxCurveDuration day; decide
  · unfold curveAfter minCurvature wad; decide
  · unfold curveAfter maxCurvature wad; decide

/-- **The same receipt is claimable under one valid curve and locked under another**, with the
claim date strictly later — 1 against 100, a factor of a hundred, pinned as a conjunct.

The receipt (1000 units of escrow, created at 0) is claimable at time 1 under `curveBefore` and
not at time 1 under `curveAfter`. Nothing about the receipt changed: `UnlockReceipt` stores only
`(assets, createdAt)` and snapshots neither the lock nor the fee at mint.

**What is not proved here.** There is no `setFeeCurve` operation, no admin, no role and no
timelock anywhere in this file, and no state transition connecting the two curves. That a single
admin call performs this swap is read off the source and the AccessManager: `setFeeCurve` is
`restricted` with `requireValid` as its only check, and the manager assigns it to **role 0**, the
admin role — *not* one of the scheduled roles (22 = 4-hour, 24 = 3-day) that gate the protocol's
other privileged setters. Both curves passing `requireValid` (proved above) is what makes the
swap ordinary configuration rather than a misconfiguration. Lean shows the two curves differ in
effect; the reachability of the swap is prose. -/
theorem receipt_relocked_by_curve_change :
    ({ assets := 1000, createdAt := 0 } : Receipt).isClaimable curveBefore 1 = true ∧
    ({ assets := 1000, createdAt := 0 } : Receipt).isClaimable curveAfter 1 = false ∧
    ({ assets := 1000, createdAt := 0 } : Receipt).claimableAt curveBefore
      < ({ assets := 1000, createdAt := 0 } : Receipt).claimableAt curveAfter :=
  ⟨rfl, rfl, by decide⟩

/-- And repriced: free under the curve in force at mint, 5% under the replacement, charged at
the new claim date because `minDuration` is also the curve's zero point. Holds for **every**
`powK` — both instants it evaluates at are clamp points, where the exponent plays no part, so the
result covers every admissible curvature at once. -/
theorem receipt_repriced_by_curve_change (powK : Nat → Nat) :
    ({ assets := 1000, createdAt := 0 } : Receipt).payout curveBefore powK 1 = 1000 ∧
    ({ assets := 1000, createdAt := 0 } : Receipt).payout curveAfter powK
      (({ assets := 1000, createdAt := 0 } : Receipt).claimableAt curveAfter) = 950 := by
  constructor
  · unfold Receipt.payout Receipt.feeNow Curve.feeOnAssets ceilDiv
    have hrate : curveBefore.feeRate powK (1 - 0) = 0 := rfl
    rw [hrate]
    unfold wad
    rfl
  · unfold Receipt.payout Receipt.feeNow Receipt.claimableAt Curve.feeOnAssets ceilDiv
    have hrate : curveAfter.feeRate powK (0 + curveAfter.minDuration - 0) = maxFeeCap := rfl
    rw [hrate]
    unfold maxFeeCap wad
    rfl

/-! ## Both fees compose on a single unlock

A holder who deposits, withdraws and later claims pays **twice**: the vault-side `unlockingFee`
when the receipt is minted, and the curve fee when it is claimed. The model charges nothing on
the vault path and a decayed-only version on the flexible path. That the *total* charge exceeds
what the model's theorems bound is an editorial reading — nothing here compares a total against a
bound proved in `Apyx.lean`; the two legs are stated separately below.
-/

/-- The **claim-side** net for an escrow of `assets`: what the curve fee leaves. The vault-side
fee is not in here — it is charged earlier, against the shares burned — so this is one leg, not
the holder's true net, which is worse. -/
def netFromUnlock (c : Curve) (powK : Nat → Nat) (assets elapsed : Nat) : Nat :=
  assets - c.feeOnAssets powK assets elapsed

/-- **Both fees bite at the earliest claim.** A holder unlocking at a positive vault rate has
strictly more than `assets` pulled from the vault against their shares, and — when the curve's
`maxFee` is positive, which `hmax` requires and `curveBefore` in this file does not satisfy —
receives strictly less than `assets` at claim. The model has no term for either side.

The first conjunct is an inequality between **asset amounts**, not share counts: the only
share-level result here, `withdrawShares_gross_ge_net`, is non-strict, because ceil-division can
map the two gross amounts to the same share count. -/
theorem both_fees_bite (c : Curve) (powK : Nat → Nat) (assets feePct : Nat)
    (h : c.isValid) (ha : 0 < assets) (hf : 0 < feePct) (hmax : 0 < c.maxFee) :
    assets < withdrawGross assets feePct ∧
    netFromUnlock c powK assets c.minDuration < assets := by
  refine ⟨model_undercharges_withdraw assets feePct ha hf, ?_⟩
  have hr : 0 < c.feeRate powK c.minDuration := by
    rw [feeRate_at_first_claim c powK h]; exact hmax
  have := feeOnAssets_pos c powK assets c.minDuration ha hr
  unfold netFromUnlock
  omega

end Apyx
