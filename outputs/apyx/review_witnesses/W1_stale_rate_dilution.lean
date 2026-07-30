import D2fsSpecs.BlastRadius

namespace Apyx

def valueAtChk (R : Nat) (s : State) (a : Address) : Nat :=
  s.apxUSDBal a + redeemAssets (s.apyUSDBal a) R + s.usdcBal a

/-- A: holds 100 apyUSD shares. Vault holds 100 apxUSD, and 100 of credited yield has
    ALREADY fully vested (fullyVestedAmount = 100) but the stored exchangeRate is still ray
    because no vault op has run since. B (addr 2) holds 100 apxUSD. -/
def st : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := ray
      vaultApxUSDBal := 100
      fullyVestedAmount := 100
      totalSupply_apyUSD := 100
      apyUSDBal := fun a => if a = 1 then 100 else 0
      apxUSDBal := fun a => if a = 2 then 100 else 0
      totalSupply_apxUSD := 100 }

-- true share price before B's deposit is 2*ray (200 assets / 100 shares)
example : computeExchangeRate st = 2 * ray := by decide
-- stored rate is stale at ray
example : st.exchangeRate = ray := rfl
-- hbacked (no_dilution's hypothesis) is satisfied
example : st.exchangeRate * st.totalSupply_apyUSD ≤ totalAssets st * ray := by decide
example : 0 < st.totalSupply_apyUSD := by decide

def st' : State := execTrace st [(Op.lockApxUSD 100, 2)]

-- B gets 100 shares for 100 apxUSD, although fair price is 50 shares
example : st'.apyUSDBal 2 = 100 := by decide
example : st'.totalSupply_apyUSD = 200 := by decide
-- post-state stored rate: 300 assets / 200 shares = 1.5 ray
example : st'.exchangeRate = 3 * ray / 2 := by decide
example : computeExchangeRate st' = 3 * ray / 2 := by decide
-- A's TRUE redeemable value fell from 200 to 150
example : redeemAssets (st.apyUSDBal 1) (computeExchangeRate st) = 200 := by decide
example : redeemAssets (st'.apyUSDBal 1) (computeExchangeRate st') = 150 := by decide
-- yet no_dilution's stale-rate measure reports an INCREASE (100 -> 150)
example : convertToAssets st (st.apyUSDBal 1) = 100 := by decide
example : convertToAssets st' (st'.apyUSDBal 1) = 150 := by decide
-- and B's fixed-(pre-step)-rate value is flat, so caller_net_nonpositive sees nothing
example : valueAtChk st.exchangeRate st 2 = 100 := by decide
example : valueAtChk st.exchangeRate st' 2 = 100 := by decide
-- B's real gain: 100 shares now redeem for 150 apxUSD
example : redeemAssets (st'.apyUSDBal 2) st'.exchangeRate = 150 := by decide

end Apyx
