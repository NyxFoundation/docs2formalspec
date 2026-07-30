import D2fsSpecs.BlastRadius

namespace Apyx

/-- x/0 = 0 exploit: a state whose stored exchangeRate is 0 (the `default` value, and the
    state shape every trace theorem quantifies over) with a funded vault. -/
def u0 : State :=
  { (default : State) with
      globalPause := false
      exchangeRate := 0
      vaultApxUSDBal := 100
      totalSupply_apyUSD := 100
      apyUSDBal := fun a => if a = 1 then 100 else 0 }

example : withdrawShares 100 u0.exchangeRate = 0 := by decide
-- addr 9 holds NO shares at all, yet drains the whole vault into its own unlock position
def u1 : State := execTrace u0 [(Op.withdraw 100 9, 9)]
example : u0.apyUSDBal 9 = 0 := by decide
example : u1.apyUSDBal 9 = 0 := by decide
example : u1.unlockRequests 0 = some (9, 100, u0.now + cooldownPeriod) := by decide
example : u1.vaultApxUSDBal = 0 := by decide
example : u1.totalSupply_apyUSD = 100 := by decide   -- no shares burned at all

/-- `setVestPeriod 0` (admin) instantly realizes the whole remaining vest stream. -/
def v0 : State :=
  { (default : State) with
      globalPause := false
      admin := 7
      now := 1000
      vestStart := 1000
      vestPeriod := 100 * day
      vestTotal := 1000 }

example : vestedAmount v0 v0.now = 0 := by decide
def v1 : State := execTrace v0 [(Op.setVestPeriod 0, 7)]
example : vestedAmount v1 v1.now = 1000 := by decide     -- entire stream vested instantly
example : totalAssets v0 = 0 ∧ totalAssets v1 = 1000 := by decide

end Apyx
