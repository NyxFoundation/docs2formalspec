import D2fsSpecs.Apyx

/-!
# The ray-scaled rate as a fidelity deviation: signed, and exhibited at its corner

The report records an open item: OpenZeppelin's ERC-4626 does a **single** `mulDiv` per
conversion, whereas this model materialises a `ray`-scaled rate (`computeExchangeRate`) and then
divides a second time (`lockShares` / `redeemAssets` / `withdrawShares`). The two are close at
deployment scale — this module bounds their *direction*, not their gap, and proves no agreement
theorem — and diverge totally when the intermediate rate floors to `0`. That corner is the entire
reason `step` carries three zero-rate guards (`Regression.lean` §R4b/R4c).

Replacing the conversions outright would touch the rate at 229 call sites across six modules, and
this codebase has already seen a share-denominated operation break the exhaustive-`Op` proofs with
kernel deep recursion. So rather than swap blind, this module states the deployment-faithful forms
directly and **proves what the swap would buy**:

* `sharesOfCeil_pos` — under the single-`mulDiv` form the zero-share drain is *impossible*, not
  guarded. `withdraw`'s `0 < assets ∧ shares = 0` branch becomes unreachable.
* `redeemAssets_le_assetsOf` — the deviation is **one-directional and conservative** on the
  redemption side: the double division never pays a redeemer more than the deployment would.
* `sharesOf_le_lockShares` — the deposit leg runs the other way: the model never issues a
  depositor **fewer** shares than the deployment would. Proved as a `≤`; no strict-inequality
  witness is exhibited, so "can issue more" is not claimed.
* `rate_floors_to_zero_witness` — a concrete state where the model's rate is `0` and
  `withdrawShares` returns 0 shares for a positive withdrawal, while the deployment-faithful form
  returns `2 * ray + 1`. The guards are load-bearing precisely here.

Everything is additive: no existing definition or theorem changes.
-/

namespace Apyx

/-! ## The deployment-faithful conversions

`ApyUSD` inherits OpenZeppelin's `ERC4626Upgradeable` with `_decimalsOffset() = 0`, so
`10 ** _decimalsOffset() = 1` and the conversions are

```solidity
_convertToShares(assets, r) = assets.mulDiv(totalSupply() + 1, totalAssets() + 1, r)
_convertToAssets(shares, r) = shares.mulDiv(totalAssets() + 1, totalSupply() + 1, r)
```

with `r = Floor` for `deposit`/`redeem` and `r = Ceil` for `mint`/`withdraw`. No `ray` appears:
the scale factor is not part of the computation, which is exactly the difference. Both
denominators are `+1`-padded, hence structurally at least `1` — the property the ray-scaled form
loses when its own quotient floors away.
-/

/-- OpenZeppelin `_convertToShares(assets, Floor)`: one `mulDiv`, no intermediate rate. -/
def sharesOf (s : State) (assets : Nat) : Nat :=
  (assets * (s.totalSupply_apyUSD + 1)) / (totalAssets s + 1)

/-- OpenZeppelin `_convertToAssets(shares, Floor)`. -/
def assetsOf (s : State) (shares : Nat) : Nat :=
  (shares * (totalAssets s + 1)) / (s.totalSupply_apyUSD + 1)

/-- OpenZeppelin `previewWithdraw` = `_convertToShares(assets, Ceil)`: the share cost of a
withdrawal, rounded **up** so the withdrawer never under-pays. -/
def sharesOfCeil (s : State) (assets : Nat) : Nat :=
  (assets * (s.totalSupply_apyUSD + 1) + totalAssets s) / (totalAssets s + 1)

/-! ## Two `Nat` facts

Floor division does not distribute over multiplication, it only loses — in whichever position
the quotient sits. The direction is what is proved here; the magnitude of the loss is not
bounded anywhere in this module. Both orientations are needed below.
-/

private theorem mul_div_le_assoc (a b c : Nat) : a * (b / c) ≤ a * b / c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp
  · rw [Nat.le_div_iff_mul_le hc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left a (Nat.div_mul_le_self b c)

private theorem div_mul_le_assoc (a b c : Nat) : a / b * c ≤ a * c / b := by
  rw [Nat.mul_comm (a / b) c, Nat.mul_comm a c]
  exact mul_div_le_assoc c a b

/-! ## What the swap would buy, part 1: the zero-share drain becomes impossible

`Regression.lean` §R4b is the drain the guard exists for — an address holding no shares
withdrawing assets because the ray-scaled `withdrawShares` floored to `0`. Under the
deployment-faithful form that state cannot arise: the numerator of a positive withdrawal is
positive, the denominator is structurally at least `1`, and the ceiling keeps the quotient off
zero.
-/

/-- **A positive withdrawal always costs at least one share**, unconditionally — no hypothesis
about the state, no guard. This is the theorem the ray-scaled form cannot have, and its absence
is why `step`'s `withdraw` branch must test `0 < assets ∧ shares = 0` explicitly. -/
theorem sharesOfCeil_pos (s : State) (assets : Nat) (h : 0 < assets) :
    0 < sharesOfCeil s assets := by
  unfold sharesOfCeil
  apply Nat.div_pos _ (Nat.succ_pos _)
  have h1 : 1 * (s.totalSupply_apyUSD + 1) ≤ assets * (s.totalSupply_apyUSD + 1) :=
    Nat.mul_le_mul_right _ h
  omega

/-- The same for the floor-rounded deposit direction, but only under `totalAssets ≤ totalSupply`
— i.e. a share price of at most 1, which a yield-accruing vault leaves almost immediately, so this
covers the early life of the pool rather than its steady state. Above that price the floor form
genuinely can round a dust deposit to zero, on-chain as well; that is the ERC-4626 inflation
residue of §9.3, not a model artifact, and it is why only the ceiling form gets an unconditional
positivity result. -/
theorem sharesOf_pos (s : State) (assets : Nat) (h : 0 < assets)
    (h_pool : totalAssets s ≤ s.totalSupply_apyUSD) :
    0 < sharesOf s assets := by
  unfold sharesOf
  apply Nat.div_pos _ (Nat.succ_pos _)
  have h1 : 1 * (s.totalSupply_apyUSD + 1) ≤ assets * (s.totalSupply_apyUSD + 1) :=
    Nat.mul_le_mul_right _ h
  omega

/-! ## What the swap would buy, part 2: the deviation has a sign

Both conversions round toward the protocol *within* one `mulDiv`. The question this section
answers is what the **extra** division does, and the answer differs by direction — which is why
the deviation is worth a report line rather than a footnote.
-/

/-- **Redemption side: the deviation is conservative.** Pricing a redemption through the
materialised rate never pays out more than the deployment's single `mulDiv` would.

**And that is the direction in which bounds do *not* transfer.** A payout bound is an upper
bound — "the redeemer receives at most `X`" is `redeemAssets ≤ X` — and `assetsOf` sits *above*
`redeemAssets`, so nothing follows about the chain's payout. Redemption payout bounds proved
against this model must be re-proved against `assetsOf`; they do not carry over. -/
theorem redeemAssets_le_assetsOf (s : State) (shares : Nat) :
    redeemAssets shares (computeExchangeRate s) ≤ assetsOf s shares := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  unfold redeemAssets assetsOf computeExchangeRate
  calc shares * ((totalAssets s + 1) * ray / (s.totalSupply_apyUSD + 1)) / ray
      ≤ shares * ((totalAssets s + 1) * ray) / (s.totalSupply_apyUSD + 1) / ray :=
        Nat.div_le_div_right (mul_div_le_assoc _ _ _)
    _ = shares * ((totalAssets s + 1) * ray) / ((s.totalSupply_apyUSD + 1) * ray) :=
        Nat.div_div_eq_div_mul _ _ _
    _ = shares * (totalAssets s + 1) * ray / ((s.totalSupply_apyUSD + 1) * ray) := by
        rw [Nat.mul_assoc]
    _ = shares * (totalAssets s + 1) / (s.totalSupply_apyUSD + 1) :=
        Nat.mul_div_mul_right _ _ hray

/-- **Deposit side: the deviation is *not* conservative.** The materialised rate is floored
before it is divided *into*, and a smaller divisor yields a larger quotient — so the model can
mint a depositor **more** shares than the deployment would for the same assets.

Stated with the rate positive, which is the only regime where the model's deposit path is open
(`lockApxUSD` guards the zero rate). The direction is the honest reading of §9.3's deviation
note: bounds proved against `lockShares` are bounds on a model that is *more* generous to the
depositor than the chain, so they transfer; but any theorem reading "the depositor receives at
most X shares" is looser than the deployment's own guarantee, not tighter. -/
theorem sharesOf_le_lockShares (s : State) (assets : Nat)
    (hR : 0 < computeExchangeRate s) :
    sharesOf s assets ≤ lockShares assets (computeExchangeRate s) := by
  have hA : 0 < totalAssets s + 1 := Nat.succ_pos _
  unfold sharesOf lockShares
  rw [Nat.le_div_iff_mul_le hR]
  -- (assets * D / A) * R ≤ (assets * D * R) / A, and D * R ≤ A * ray, so the whole thing
  -- collapses to assets * ray after cancelling A
  calc assets * (s.totalSupply_apyUSD + 1) / (totalAssets s + 1) * computeExchangeRate s
      ≤ assets * (s.totalSupply_apyUSD + 1) * computeExchangeRate s / (totalAssets s + 1) :=
        div_mul_le_assoc _ _ _
    _ ≤ assets * ((totalAssets s + 1) * ray) / (totalAssets s + 1) := by
        apply Nat.div_le_div_right
        rw [Nat.mul_assoc]
        apply Nat.mul_le_mul_left
        show (s.totalSupply_apyUSD + 1) * computeExchangeRate s ≤ (totalAssets s + 1) * ray
        unfold computeExchangeRate
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
    _ = assets * ray := by
        rw [← Nat.mul_assoc, Nat.mul_comm assets (totalAssets s + 1), Nat.mul_assoc,
          Nat.mul_comm (totalAssets s + 1) (assets * ray), Nat.mul_div_assoc _ (Nat.dvd_refl _),
          Nat.div_self hA, Nat.mul_one]

/-! ## The corner the guards exist for, exhibited

`computeExchangeRate` is `(totalAssets + 1) * ray / (totalSupply_apyUSD + 1)`, so it floors to
zero as soon as the share supply exceeds the ray-scaled asset base. That needs a supply above
`ray`, which is large but is a perfectly ordinary `Nat` — the model has no invariant excluding
it, which is the point.
-/

/-- An empty vault carrying a share supply of `2 * ray`. No stated invariant excludes it — the
model caps no supply — but whether `step` can *reach* it is not established here, and the shape is
awkward: `lockApxUSD` mints shares against deposited assets, so `2 * ray` shares over a zero-asset
vault is exactly what a reachability argument would have to explain. It is exhibited as a state
the guards must survive, not as a claimed trace. -/
def zeroRateWitness : State :=
  { (default : State) with
      globalPause := false
      totalSupply_apyUSD := 2 * ray }

/-- **The rate floors to zero.** What that does to the conversions is proved separately, and
only for `withdrawShares` (`rate_floors_to_zero_witness`); `lockShares` is not shown here. -/
theorem zeroRate_witness_rate : computeExchangeRate zeroRateWitness = 0 := by
  have hTA : totalAssets zeroRateWitness = 0 := rfl
  unfold computeExchangeRate
  rw [hTA]
  exact Nat.div_eq_of_lt (by
    have : ray < 2 * ray + 1 := by
      have : 0 < ray := Nat.pow_pos (by decide)
      omega
    simpa [zeroRateWitness] using this)

/-- **The divergence, side by side.** For a one-unit withdrawal the model's ray-scaled form
charges **zero shares** — the `Regression.lean` §R4b drain, which only the explicit guard stops —
while the deployment-faithful form charges `2 * ray + 1`, the entire share supply plus the
virtual share. The two are not close; they are on opposite sides of the guard. -/
theorem rate_floors_to_zero_witness :
    withdrawShares 1 (computeExchangeRate zeroRateWitness) = 0 ∧
    sharesOfCeil zeroRateWitness 1 = 2 * ray + 1 ∧
    0 < sharesOfCeil zeroRateWitness 1 := by
  have hTA : totalAssets zeroRateWitness = 0 := rfl
  have hceil : sharesOfCeil zeroRateWitness 1 = 2 * ray + 1 := by
    unfold sharesOfCeil
    rw [hTA]
    simp [zeroRateWitness]
  refine ⟨?_, hceil, ?_⟩
  · rw [zeroRate_witness_rate]
    simp [withdrawShares]
  · exact sharesOfCeil_pos zeroRateWitness 1 (by decide)

/-! ## The recommendation this module supports

The swap is worth doing and is **not** attempted here. What the theorems above establish is that
it is a *correctness* change, not a cosmetic one:

1. it makes `step`'s `withdraw` zero-share branch **unreachable** rather than guarded
   (`sharesOfCeil_pos`). The deposit branch is only conditionally covered (`sharesOf_pos` needs
   `totalAssets ≤ totalSupply`), and the third zero-rate guard is not addressed here at all;
2. the deviation has opposite signs on the two legs, and only one of them is benign. The model
   never issues a depositor *fewer* shares than the deployment (`sharesOf_le_lockShares`), so a
   share-issuance **upper** bound proved here does carry over. It never pays a redeemer *more*
   (`redeemAssets_le_assetsOf`), so a payout upper bound proved here does **not** — that side
   must be re-proved against `assetsOf`;
3. the divergence is not asymptotic dust; at the corner it is total
   (`rate_floors_to_zero_witness`).

Point 2 is the cost estimate: the swap is not a rename. It touches `computeExchangeRate` at 229
sites, and the deposit-direction theorems change meaning rather than merely changing spelling.
-/

end Apyx
