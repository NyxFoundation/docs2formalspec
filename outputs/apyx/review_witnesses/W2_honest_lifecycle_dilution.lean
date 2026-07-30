import D2fsSpecs.BlastRadius

namespace Apyx

/-- Fully rate-consistent start: TS = 0 so computeExchangeRate = ray = the stored rate. -/
def w0 : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := ray
      yieldDistributor := 5
      vestPeriod := 100 * day
      apxUSDBal := fun a => if a = 1 then 100 else if a = 2 then 100 else 0
      totalSupply_apxUSD := 200 }

example : w0.exchangeRate = computeExchangeRate w0 := by decide

/-- Honest lifecycle: A locks 100, the yield distributor credits 100, the vest fully
    streams, then B locks 100 -- pricing off the STALE stored rate. -/
def w4 : State := execTrace w0
  [ (Op.lockApxUSD 100, 1),
    (Op.creditYield 100, 5),
    (Op.tick (100 * day), 0),
    (Op.lockApxUSD 100, 2) ]

def w3 : State := execTrace w0
  [ (Op.lockApxUSD 100, 1), (Op.creditYield 100, 5), (Op.tick (100 * day), 0) ]

-- just before B's deposit: stored rate is stale at ray, true share price is 2*ray
example : w3.exchangeRate = ray := by decide
example : computeExchangeRate w3 = 2 * ray := by decide
example : w3.apyUSDBal 1 = 100 ∧ w3.totalSupply_apyUSD = 100 := by decide
-- no_dilution / exchange_rate_monotone_deposit hypotheses both hold at w3
example : 0 < w3.totalSupply_apyUSD := by decide
example : w3.exchangeRate * w3.totalSupply_apyUSD ≤ totalAssets w3 * ray := by decide

-- B gets 100 shares for 100 apxUSD; the fair number is 50
example : w4.apyUSDBal 2 = 100 := by decide
example : w4.exchangeRate = 3 * ray / 2 := by decide
-- A's true redeemable value drops 200 -> 150; B's 100 apxUSD becomes 150
example : redeemAssets (w3.apyUSDBal 1) (computeExchangeRate w3) = 200 := by decide
example : redeemAssets (w4.apyUSDBal 1) (computeExchangeRate w4) = 150 := by decide
example : redeemAssets (w4.apyUSDBal 2) (computeExchangeRate w4) = 150 := by decide
-- but the stale-rate measures used by the theorems report no harm
example : convertToAssets w3 (w3.apyUSDBal 1) = 100 := by decide
example : convertToAssets w4 (w4.apyUSDBal 1) = 150 := by decide
example : w3.exchangeRate ≤ w4.exchangeRate := by decide
-- and the true share price FELL, contradicting the README's "share-price monotonicity"
example : computeExchangeRate w4 < computeExchangeRate w3 := by decide

end Apyx
