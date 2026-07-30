import D2fsSpecs.HolderValue

/-!
# Two fee mechanisms the model does not have, formalized from the deployed Solidity

Everything here is read off verified sources fetched from sourcify for implementation
`0xfd616567ecc1607f61073951a1e822f7315bb112` (`src/ApyUSD.sol`, `src/FeeCurve.sol`; solidity
0.8.30, OpenZeppelin upgradeable 5.5.0), plus live reads against the proxy
`0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A`. See `deployment_ground_truth.md`.

The model in `Apyx.lean` was built from the documentation corpus, and the corpus does not mention
either mechanism below. Both are live on chain today.

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
`feeRate_at_first_claim` below shows the deployment ties the two so that the maximum **is**
charged at the first claimable instant — the §2.3 gap is an artifact of the model's split
constants, not a property of the protocol.
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
is non-zero". So there is no dust regime in which the model and the chain agree. -/
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

Since `withdrawShares` is monotone in its first argument, the deployment's share cost is at least
the model's — so every "the withdrawer pays at most X shares" statement proved against the model
is *looser* than what the chain enforces, and every "the vault retains at least Y" statement is
*tighter* than what the chain delivers. -/
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

/-- The `redeem` counterpart. `previewRedeem` returns `gross - _feeOnTotal(gross, φ)`, so the
receipt escrows strictly **less** than the model's position credit, which is the full `gross`
(`redeem_receiver_position_gain`). Where `withdraw` under-charges the payer, `redeem`
over-credits the receiver — the model errs in the user's favour on both vault legs. -/
theorem model_overcredits_redeem (gross feePct : Nat) (hg : 0 < gross) (hf : 0 < feePct) :
    gross - feeOnTotal gross feePct < gross := by
  have hw : 0 < feePct + wad := by unfold wad; omega
  have hpos : 0 < feeOnTotal gross feePct := by
    unfold feeOnTotal ceilDiv
    rw [if_neg (by omega)]
    apply Nat.div_pos _ hw
    have h1 : 1 * 1 ≤ gross * feePct := Nat.mul_le_mul hg hf
    omega
  omega

/-- The live rate, pinned: at `unlockingFee() = 1e15` a 1000-unit withdrawal is charged exactly
one unit — 0.1%, matching the on-chain read. The model charges zero. -/
theorem live_fee_is_ten_bps : feeOnRaw (1000 * wad) liveUnlockingFee = wad := by
  unfold feeOnRaw ceilDiv liveUnlockingFee wad
  rfl

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

At the live rate (10 bps) that is 0.1% of every unlocked amount, compounding across the whole
unlock flow — a systematic accounting gap, not a corner case. -/
theorem vault_leak_linear (v a feePct n : Nat)
    (h_fund : n * withdrawGross a feePct ≤ v) :
    modelVaultAfterUnlocks v a n = vaultAfterUnlocks v a feePct n + n * feeOnRaw a feePct := by
  have hsplit : n * withdrawGross a feePct = n * a + n * feeOnRaw a feePct := by
    unfold withdrawGross; rw [Nat.mul_add]
  have hna : n * a ≤ v := by omega
  rw [modelVaultAfterUnlocks_closed v a n hna, vaultAfterUnlocks_closed v a feePct n h_fund]
  omega

/-! ### The guard the model lacks

`_withdraw` reverts with `InvalidCaller()` unless `receiver == owner`, "to prevent third parties
from minting the UnlockReceipt to themselves". The model's `Op.withdraw assets receiver` takes an
arbitrary receiver and never compares it to the share owner, so it admits steps the chain refuses
— the same "model more permissive than the chain" direction as the deny-list gaps of §9.3.
-/

/-- The deployment's guard, as a predicate on the model's operation shape. -/
def ReceiverIsOwner (receiver owner : Address) : Prop := receiver = owner

/-- **The model's withdrawal never constrains the receiver.** If a withdrawal succeeds for one
receiver it succeeds, from the same state and the same caller, for *every* receiver — the four
guards on `Op.withdraw` (`globalPause`, the zero-share check, the share balance, the vault
balance) mention only the caller and the amount.

The deployment does constrain it: `_withdraw` reverts with `InvalidCaller()` unless
`receiver == owner`, "to prevent third parties from minting the UnlockReceipt to themselves".
So the model is **more permissive than the chain** on this path — the same direction as the
deny-list gaps §9.3 closed, and the reason `holder_value_withdraw` has to carry a
`receiver ≠ caller` branch that on chain is unreachable.

Stated as a general receiver-independence result rather than a single witness: it says the guard
is absent from the model, not merely that one state slips through. -/
theorem withdraw_receiver_unconstrained (s : State) (assets : Nat) (r1 r2 caller : Address)
    (s1 : State) (h : step s (Op.withdraw assets r1) caller = some s1) :
    ∃ s2, step s (Op.withdraw assets r2) caller = some s2 := by
  simp only [step] at h ⊢
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i g1 g2 g3 g4
          rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4]
          exact ⟨_, rfl⟩

/-- A funded, non-degenerate vault: one holder owns the whole 100-share supply against 100
assets, so the live rate is exactly `ray` and a 100-asset withdrawal costs exactly 100 shares. -/
def withdrawWitness : State :=
  { (default : State) with
      globalPause := false
      totalSupply_apyUSD := 100
      apyUSDBal := fun a => if a = 1 then 100 else 0
      vaultApxUSDBal := 100 }

/-- **`withdraw_receiver_unconstrained` is not vacuous.** Successful withdrawals exist, and the
receiver really is free: the same caller, from the same state, succeeds while directing the
receipt to two different third parties. On chain both of these revert with `InvalidCaller()`. -/
theorem withdraw_third_party_receipts_succeed :
    (step withdrawWitness (Op.withdraw 100 2) 1).isSome = true ∧
    (step withdrawWitness (Op.withdraw 100 7) 1).isSome = true ∧
    computeExchangeRate (pullVestedYield withdrawWitness) = ray := by
  refine ⟨by decide, by decide, by decide⟩

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

/-- The rate never exceeds `maxFee`, at any elapsed time and any curvature — the clamp is
structural, not a consequence of the decay's shape. -/
theorem feeRate_le_maxFee (c : Curve) (powK : Nat → Nat) (elapsed : Nat) (h : c.isValid) :
    c.feeRate powK elapsed ≤ c.maxFee := by
  obtain ⟨-, -, -, hfee, -, -, -⟩ := h
  unfold Curve.feeRate
  split
  · exact hfee
  · split
    · exact Nat.le_refl _
    · exact Nat.sub_le _ _

/-- **`tHat` never exceeds one**, which is the fact `feeRate_ge_minFee`'s hypothesis rests on:
the numerator `elapsed - minDuration` is below the denominator `maxDuration - minDuration`
everywhere the interior branch is taken, so the WAD-scaled ratio is at most `1e18`. The library
relies on exactly this when it casts to `int256` for `powWad` ("`tHat <= 1e18` (numerator can't
exceed denominator)"). -/
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

/-- And never falls below `minFee`, given the one fact about `powWad` the library relies on:
`tHat ≤ 1e18` (`tHat_le_wad`), so `tHat ^ k ≤ 1e18` for the admissible exponents. Instantiating
`powK` at the library's own linear shortcut (`curvature = 1e18`, where `powWad` is the identity)
discharges the hypothesis outright, so the statement is not vacuous. -/
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
hypothesis holds for it with no side condition beyond the interior branch — the floor really is
reachable rather than assumed. -/
theorem feeRate_ge_minFee_linear (c : Curve) (elapsed : Nat) (h : c.isValid)
    (hlt : elapsed < c.maxDuration) :
    c.minFee ≤ c.feeRate id elapsed :=
  feeRate_ge_minFee c id elapsed h (tHat_le_wad c elapsed hlt)

/-- **The 5% ceiling is the real bound on the early-exit fee**, not the model's 3.5%: the
admin-settable `maxFee` is capped only by `MAX_FEE`, and by `feeRate_at_first_claim` a claimant
at the earliest permitted moment pays exactly it. The model's hardcoded 350 bps is one
configuration of a parameter whose ceiling is 5000 bps. -/
theorem first_claim_fee_bounded_by_cap (c : Curve) (powK : Nat → Nat) (h : c.isValid) :
    c.feeRate powK c.minDuration ≤ maxFeeCap := by
  have hcap : c.maxFee ≤ maxFeeCap := h.2.2.2.2.1
  rw [feeRate_at_first_claim c powK h]
  exact hcap

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

/-- **One admin call re-locks an outstanding receipt and reprices it at the ceiling.**

The receipt (1000 units of escrow, created at 0) is claimable at time 1 under the curve in force when it
was minted, and would pay out in full — that curve's `maxFee` is zero. After `setFeeCurve`, the
*same* receipt is not claimable at time 1; its claim date has moved from 1 to 100; and when that
date arrives the fee is the new `maxFee`, because `minDuration` is also the curve's zero point.
The holder waits a hundred times longer and receives 95% instead of 100%.

Nothing about the receipt changed — the contract snapshots neither the lock nor the fee at mint,
storing only `(assets, createdAt)`. Both curves satisfy `requireValid`, so this is ordinary admin
configuration rather than a misconfiguration, and there is no timelock on `setFeeCurve`.

The statement holds for **every** `powK`, i.e. every admissible curvature: the two instants it
speaks about are the clamp points, where the exponent plays no part. -/
theorem receipt_relocked_by_curve_change :
    ({ assets := 1000, createdAt := 0 } : Receipt).isClaimable curveBefore 1 = true ∧
    ({ assets := 1000, createdAt := 0 } : Receipt).isClaimable curveAfter 1 = false ∧
    ({ assets := 1000, createdAt := 0 } : Receipt).claimableAt curveBefore
      < ({ assets := 1000, createdAt := 0 } : Receipt).claimableAt curveAfter :=
  ⟨rfl, rfl, by decide⟩

/-- And repriced: free under the curve in force at mint, 5% under the replacement, charged at
the new claim date because `minDuration` is also the curve's zero point. Holds for every
`powK`, i.e. every admissible curvature — both instants are clamp points. -/
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

/-- **Both effects, from one `setFeeCurve` call**, with the curves' validity discharged so the
swap is ordinary admin configuration rather than a misconfiguration. -/
theorem admin_curve_change_relocks_and_reprices (powK : Nat → Nat) :
    curveBefore.isValid ∧ curveAfter.isValid ∧
    (({ assets := 1000, createdAt := 0 } : Receipt).isClaimable curveBefore 1 = true ∧
      ({ assets := 1000, createdAt := 0 } : Receipt).payout curveBefore powK 1 = 1000) ∧
    (({ assets := 1000, createdAt := 0 } : Receipt).isClaimable curveAfter 1 = false ∧
      ({ assets := 1000, createdAt := 0 } : Receipt).payout curveAfter powK
        (({ assets := 1000, createdAt := 0 } : Receipt).claimableAt curveAfter) = 950) :=
  ⟨curveBefore_valid, curveAfter_valid,
    ⟨receipt_relocked_by_curve_change.1, (receipt_repriced_by_curve_change powK).1⟩,
    ⟨receipt_relocked_by_curve_change.2.1, (receipt_repriced_by_curve_change powK).2⟩⟩

/-! ## Both fees compose on a single unlock

A holder who deposits, withdraws and later claims pays **twice**: the vault-side `unlockingFee`
when the receipt is minted, and the curve fee when it is claimed. The model charges neither on
the vault path and a decayed-only version on the flexible path, so the total charge a real user
meets is strictly larger than anything the model's theorems bound.
-/

/-- What a holder actually nets from an unlock of `assets`, on the deployment: the vault fee is
added to the shares burned, and the curve fee is deducted from the escrowed amount at claim. -/
def netFromUnlock (c : Curve) (powK : Nat → Nat) (assets elapsed : Nat) : Nat :=
  assets - c.feeOnAssets powK assets elapsed

/-- **Both fees bite at the earliest claim.** A holder unlocking at a positive vault rate and
claiming at the first permitted instant burns shares worth strictly more than `assets` and
receives strictly less than `assets` — the model has no term for either side. -/
theorem both_fees_bite (c : Curve) (powK : Nat → Nat) (assets feePct : Nat)
    (h : c.isValid) (ha : 0 < assets) (hf : 0 < feePct) (hmax : 0 < c.maxFee)
    (hsmall : c.feeOnAssets powK assets c.minDuration ≤ assets) :
    assets < withdrawGross assets feePct ∧
    netFromUnlock c powK assets c.minDuration < assets := by
  refine ⟨model_undercharges_withdraw assets feePct ha hf, ?_⟩
  have hr : 0 < c.feeRate powK c.minDuration := by
    rw [feeRate_at_first_claim c powK h]; exact hmax
  have := feeOnAssets_pos c powK assets c.minDuration ha hr
  unfold netFromUnlock
  omega

end Apyx
