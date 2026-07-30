import D2fsSpecs.BlastRadius

namespace Apyx

/-- A fresh (default-derived) state: exchangeRate = 0, as `deriving Inhabited` gives.
    Victim (addr 2) holds 100 apxUSD; attacker (addr 3) holds 1 apxUSD. -/
def s0 : State :=
  { (default : State) with
      globalPause := false
      apxUSDBal := fun a => if a = 2 then 100 else if a = 3 then 1 else 0
      totalSupply_apxUSD := 101 }

example : s0.exchangeRate = 0 := rfl

-- victim locks 100 apxUSD and receives ZERO shares (lockShares _ 0 = 0): a pure donation
def s1 : State := execTrace s0 [(Op.lockApxUSD 100, 2)]
example : s1.apyUSDBal 2 = 0 := by decide
example : s1.totalSupply_apyUSD = 0 := by decide
example : s1.vaultApxUSDBal = 100 := by decide
example : s1.apxUSDBal 2 = 0 := by decide
example : s1.exchangeRate = ray := by decide

-- attacker then locks 1 apxUSD, gets 1 share, and redeems it for the WHOLE vault (101)
def s2 : State := execTrace s1 [(Op.lockApxUSD 1, 3)]
example : s2.apyUSDBal 3 = 1 := by decide
example : s2.exchangeRate = 101 * ray := by decide
def s3 : State := execTrace s2 [(Op.redeem 1 3, 3)]
-- the attacker's unlock position is 101 apxUSD, claimable after cooldown, for 1 paid in
example : s3.unlockRequests 0 = some (3, 101, s2.now + cooldownPeriod) := by decide
example : s3.vaultApxUSDBal = 0 := by decide

-- `no_inflation_attack` still "holds": it reports lockApxUSD with amount <= balance,
-- and says nothing about shares minted.
example : s1.vaultApxUSDBal = s0.vaultApxUSDBal + 100 ∧ (100 : Nat) ≤ s0.apxUSDBal 2 := by decide

end Apyx
