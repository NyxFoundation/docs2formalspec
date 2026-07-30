import D2fsSpecs.BlastRadius

namespace Apyx

/-- Classic ERC-4626 inflation attack, non-degenerate state: attacker (3) holds the single
    outstanding share; the vault already holds 200 assets, so the share price is 200*ray.
    Victim (2) deposits 150 apxUSD -- below the price of one share -- and gets ZERO shares. -/
def t0 : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := 200 * ray
      vaultApxUSDBal := 200
      totalSupply_apyUSD := 1
      apyUSDBal := fun a => if a = 3 then 1 else 0
      apxUSDBal := fun a => if a = 2 then 150 else 0
      totalSupply_apxUSD := 150 }

-- the stored rate is the honest computeExchangeRate: no staleness needed here
example : computeExchangeRate t0 = 200 * ray := by decide
example : t0.exchangeRate * t0.totalSupply_apyUSD ≤ totalAssets t0 * ray := by decide

def t1 : State := execTrace t0 [(Op.lockApxUSD 150, 2)]
-- victim: 150 apxUSD in, 0 shares out
example : t1.apyUSDBal 2 = 0 := by decide
example : t1.apxUSDBal 2 = 0 := by decide
example : t1.totalSupply_apyUSD = 1 := by decide
-- attacker's single share appreciates from 200 to 350
example : t1.exchangeRate = 350 * ray := by decide
example : convertToAssets t0 (t0.apyUSDBal 3) = 200 := by decide
example : convertToAssets t1 (t1.apyUSDBal 3) = 350 := by decide
-- and no_dilution's conclusion is satisfied for the attacker (the protected "holder")
example : t1.apyUSDBal 3 = t0.apyUSDBal 3
    ∧ convertToAssets t0 (t0.apyUSDBal 3) ≤ convertToAssets t1 (t1.apyUSDBal 3) := by decide

-- Solvent's margin term is the *field* overcollateralizationBuffer, which no op ever raises
example : (default : State).overcollateralizationBuffer = 0 := rfl
example : t1.overcollateralizationBuffer = 0 := rfl
-- while the computed buffer (used by redeemApxUSD's guard) is a different quantity
def t2 : State := { t1 with totalCollateralValue := 500, redemptionValue := ray }
example : Apyx.overcollateralizationBuffer t2 = 500 := by decide
example : t2.overcollateralizationBuffer = 0 := rfl

end Apyx
