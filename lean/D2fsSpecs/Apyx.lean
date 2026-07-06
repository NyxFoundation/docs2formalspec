import Std

namespace Apyx

-- Basic types
abbrev Address := Nat

-- Constants
def COOLDOWN_PERIOD : Nat := 20 * 24 * 3600
def FLEXIBLE_MIN_PERIOD : Nat := 3 * 24 * 3600
def FLEXIBLE_MAX_FEE_BPS : Nat := 350  -- 3.5% in basis points (1/100 of a percent)
def FLEXIBLE_MIN_FEE_BPS : Nat := 10   -- 0.1%
def FLEXIBLE_FEE_DECLINE_PERIOD : Nat := 20 * 24 * 3600
def RAY : Nat := 1000000000000000000000000000  -- 1e27
def CENT : Nat := 100  -- 1 dollar = 100 cents

-- Helper: linear vesting amount
def vestedAmount (s : State) : Nat :=
  let t := s.now
  if t < s.vestStart then 0
  else
    let elapsed := min t s.vestEnd - s.vestStart
    let totalDuration := s.vestEnd - s.vestStart
    if totalDuration = 0 then 0
    else s.totalVested * elapsed / totalDuration

-- Helper: total assets of the vault (apxUSD balance + vested yield)
def totalAssets (s : State) : Nat :=
  State.apxUSD_bal s s.vaultAddr + vestedAmount s

-- Helper: compute exchange rate (apyUSD -> apxUSD) in ray
def computeExchangeRate (s : State) : Nat :=
  let supply := s.totalSupply_apyUSD
  if supply = 0 then RAY
  else totalAssets s * RAY / supply

-- Helper: add address to holders list if not present
def addHolder (holders : List Address) (addr : Address) : List Address :=
  if holders.contains addr then holders else addr :: holders

structure State where
  now : Nat
  usdc_bal : Address → Nat
  apxUSD_bal : Address → Nat
  apyUSD_bal : Address → Nat
  totalSupply_apxUSD : Nat
  totalSupply_apyUSD : Nat
  totalCollateralValue : Nat
  redemptionValue : Nat
  overcollateralizationBuffer : Nat
  exchangeRate : Nat
  whitelist : Address → Bool
  denylist : Address → Bool
  globalPause : Bool
  yieldRateMonth : Nat
  vestPeriod : Nat
  vestStart : Nat
  vestEnd : Nat
  totalVested : Nat
  unlockTokens : Nat → Option (Address × Nat × Nat × Bool)  -- (owner, amount, requestTime, isFlexible)
  cooldownEnd : Address → Nat → Nat
  nextRequestId : Nat
  admins : List Address
  pausers : List Address
  govRole : List Address
  yieldDistributor : Address
  rfqCounterparties : List Address
  oracle : Address
  govTokenBal : Address → Nat
  govThreshold : Nat
  apxUSDHolders : List Address
  vaultAddr : Address
  unlockTokenAddr : Address
  treasuryAddr : Address
  linearVestV0Addr : Address
  deriving Inhabited

inductive Op
  | depositUSDC (amount : Nat)
  | mintApxUSD (to : Address) (amount : Nat)
  | lockApxUSD (amount : Nat)
  | depositForMinShares (assets : Nat) (minShares : Nat) (receiver : Address)
  | mintForMaxAssets (shares : Nat) (maxAssets : Nat) (receiver : Address)
  | requestUnlock (amount : Nat)
  | claimUnlock (requestId : Nat)
  | requestFlexibleUnlock (amount : Nat)
  | claimFlexibleUnlock (requestId : Nat)
  | redeemApxUSD (amount : Nat)
  | withdraw (assets : Nat) (receiver : Address)
  | withdrawForMaxShares (assets : Nat) (maxShares : Nat) (receiver : Address)
  | redeem (shares : Nat) (receiver : Address)
  | redeemForMinAssets (shares : Nat) (minAssets : Nat) (receiver : Address)
  | pause
  | unpause
  | addToWhitelist (addr : Address)
  | removeFromWhitelist (addr : Address)
  | addToDenylist (addr : Address)
  | removeFromDenylist (addr : Address)
  | setYieldRate (bps : Nat)
  | creditYield (amount : Nat)
  | voteBufferDeployment (amount : Nat)
  | executeRFQRedemption (user : Address) (amount : Nat)
  | updateRedemptionValue
  | handleStressEvent (amount : Nat)
  | catastrophicBackstop
  deriving Inhabited

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.depositUSDC amount =>
    if s.globalPause then none
    else if s.denylist caller then none
    else if amount = 0 then none
    else if s.usdc_bal caller < amount then none
    else
      let newUsdc := fun a => if a = caller then s.usdc_bal a - amount
                              else if a = s.treasuryAddr then s.usdc_bal a + amount
                              else s.usdc_bal a
      let newApx := fun a => if a = caller then s.apxUSD_bal a + amount else s.apxUSD_bal a
      let newHolders := addHolder s.apxUSDHolders caller
      some { s with
        usdc_bal := newUsdc,
        apxUSD_bal := newApx,
        totalSupply_apxUSD := s.totalSupply_apxUSD + amount,
        totalCollateralValue := s.totalCollateralValue + amount,
        apxUSDHolders := newHolders
      }
  | Op.mintApxUSD to amount =>
    if s.globalPause then none
    else if s.denylist caller then none
    else if !s.whitelist caller then none
    else if amount = 0 then none
    else if s.usdc_bal caller < amount then none
    else
      let newUsdc := fun a => if a = caller then s.usdc_bal a - amount
                              else if a = s.treasuryAddr then s.usdc_bal a + amount
                              else s.usdc_bal a
      let newApx := fun a => if a = to then s.apxUSD_bal a + amount else s.apxUSD_bal a
      let newHolders := addHolder s.apxUSDHolders to
      some { s with
        usdc_bal := newUsdc,
        apxUSD_bal := newApx,
        totalSupply_apxUSD := s.totalSupply_apxUSD + amount,
        totalCollateralValue := s.totalCollateralValue + amount,
        apxUSDHolders := newHolders
      }
  | Op.lockApxUSD amount =>
    if amount = 0 then none
    else if s.apxUSD_bal caller < amount then none
    else
      let shares := amount * RAY / s.exchangeRate
      if shares = 0 then none
      else
        let newApx := fun a => if a = caller then s.apxUSD_bal a - amount
                               else if a = s.vaultAddr then s.apxUSD_bal a + amount
                               else s.apxUSD_bal a
        let newApy := fun a => if a = caller then s.apyUSD_bal a + shares else s.apyUSD_bal a
        let newTotalSupply := s.totalSupply_apyUSD + shares
        let newRate := computeExchangeRate { s with
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply
        }
        if newRate < s.exchangeRate then none  -- non-decreasing
        else some { s with
          apxUSD_bal := newApx,
          apyUSD_bal := newApy,
          totalSupply_apyUSD := newTotalSupply,
          exchangeRate := newRate
        }
  | Op.depositForMinShares assets minShares receiver =>
    if s.globalPause then none
    else if s.denylist caller || s.denylist receiver then none
    else if assets = 0 then none
    else if s.apxUSD_bal caller < assets then none
    else
      let shares := assets * RAY / s.exchangeRate
      if shares < minShares then none
      else
        let newApx := fun a => if a = caller then s.apxUSD_bal a - assets
                               else if a = s.vaultAddr then s.apxUSD_bal a + assets
                               else s.apxUSD_bal a
        let newApy := fun a => if a = receiver then s.apyUSD_bal a + shares else s.apyUSD_bal a
        let newTotalSupply := s.totalSupply_apyUSD + shares
        let newRate := computeExchangeRate { s with
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply
        }
        if newRate < s.exchangeRate then none
        else some { s with
          apxUSD_bal := newApx,
          apyUSD_bal := newApy,
          totalSupply_apyUSD := newTotalSupply,
          exchangeRate := newRate
        }
  | Op.mintForMaxAssets shares maxAssets receiver =>
    if s.globalPause then none
    else if s.denylist caller || s.denylist receiver then none
    else if shares = 0 then none
    else
      let assets := shares * s.exchangeRate / RAY
      if assets > maxAssets then none
      else if s.apxUSD_bal caller < assets then none
      else
        let newApx := fun a => if a = caller then s.apxUSD_bal a - assets
                               else if a = s.vaultAddr then s.apxUSD_bal a + assets
                               else s.apxUSD_bal a
        let newApy := fun a => if a = receiver then s.apyUSD_bal a + shares else s.apyUSD_bal a
        let newTotalSupply := s.totalSupply_apyUSD + shares
        let newRate := computeExchangeRate { s with
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply
        }
        if newRate < s.exchangeRate then none
        else some { s with
          apxUSD_bal := newApx,
          apyUSD_bal := newApy,
          totalSupply_apyUSD := newTotalSupply,
          exchangeRate := newRate
        }
  | Op.requestUnlock amount =>
    if amount = 0 then none
    else if s.apyUSD_bal caller < amount then none
    else
      let apxUSDAmount := amount * s.exchangeRate / RAY
      if apxUSDAmount = 0 then none
      else if s.apxUSD_bal s.vaultAddr < apxUSDAmount then none
      else
        let newApy := fun a => if a = caller then s.apyUSD_bal a - amount else s.apyUSD_bal a
        let newApx := fun a => if a = s.vaultAddr then s.apxUSD_bal a - apxUSDAmount
                               else if a = s.unlockTokenAddr then s.apxUSD_bal a + apxUSDAmount
                               else s.apxUSD_bal a
        let newTotalSupply := s.totalSupply_apyUSD - amount
        let requestId := s.nextRequestId
        let newUnlockTokens := fun rid => if rid = requestId then some (caller, apxUSDAmount, s.now, false) else s.unlockTokens rid
        let newCooldown := fun u rid => if u = caller && rid = requestId then s.now + COOLDOWN_PERIOD else s.cooldownEnd u rid
        let newRate := computeExchangeRate { s with
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply
        }
        if newRate < s.exchangeRate then none
        else some { s with
          apyUSD_bal := newApy,
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply,
          unlockTokens := newUnlockTokens,
          cooldownEnd := newCooldown,
          nextRequestId := requestId + 1,
          exchangeRate := newRate
        }
  | Op.claimUnlock requestId =>
    match s.unlockTokens requestId with
    | none => none
    | some (owner, amount, requestTime, isFlexible) =>
      if owner != caller then none
      else if isFlexible then none  -- use claimFlexibleUnlock for flexible
      else if s.now < s.cooldownEnd caller requestId then none
      else
        let newApx := fun a => if a = s.unlockTokenAddr then s.apxUSD_bal a - amount
                               else if a = caller then s.apxUSD_bal a + amount
                               else s.apxUSD_bal a
        let newUnlockTokens := fun rid => if rid = requestId then none else s.unlockTokens rid
        let newCooldown := fun u rid => if u = caller && rid = requestId then 0 else s.cooldownEnd u rid
        some { s with
          apxUSD_bal := newApx,
          unlockTokens := newUnlockTokens,
          cooldownEnd := newCooldown
        }
  | Op.requestFlexibleUnlock amount =>
    if amount = 0 then none
    else if s.apyUSD_bal caller < amount then none
    else
      let apxUSDAmount := amount * s.exchangeRate / RAY
      if apxUSDAmount = 0 then none
      else if s.apxUSD_bal s.vaultAddr < apxUSDAmount then none
      else
        let newApy := fun a => if a = caller then s.apyUSD_bal a - amount else s.apyUSD_bal a
        let newApx := fun a => if a = s.vaultAddr then s.apxUSD_bal a - apxUSDAmount
                               else if a = s.unlockTokenAddr then s.apxUSD_bal a + apxUSDAmount
                               else s.apxUSD_bal a
        let newTotalSupply := s.totalSupply_apyUSD - amount
        let requestId := s.nextRequestId
        let newUnlockTokens := fun rid => if rid = requestId then some (caller, apxUSDAmount, s.now, true) else s.unlockTokens rid
        let newCooldown := fun u rid => if u = caller && rid = requestId then s.now + COOLDOWN_PERIOD else s.cooldownEnd u rid
        let newRate := computeExchangeRate { s with
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply
        }
        if newRate < s.exchangeRate then none
        else some { s with
          apyUSD_bal := newApy,
          apxUSD_bal := newApx,
          totalSupply_apyUSD := newTotalSupply,
          unlockTokens := newUnlockTokens,
          cooldownEnd := newCooldown,
          nextRequestId := requestId + 1,
          exchangeRate := newRate
        }
  | Op.claimFlexibleUnlock requestId =>
    match s.unlockTokens requestId with
    | none => none
    | some (owner, amount, requestTime, isFlexible) =>
      if owner != caller then none
      else if !isFlexible then none
      else if s.now < requestTime + FLEXIBLE_MIN_PERIOD then none
      else
        let elapsed := s.now - requestTime
        let feeBPS :=
          if elapsed >= FLEXIBLE_FEE_DECLINE_PERIOD then FLEXIBLE_MIN_FEE_BPS
          else
            let decline := (FLEXIBLE_MAX_FEE_BPS - FLEXIBLE_MIN_FEE_BPS) * elapsed / FLEXIBLE_FEE_DECLINE_PERIOD
            if FLEXIBLE_MAX_FEE_BPS > decline then FLEXIBLE_MAX_FEE_BPS - decline else FLEXIBLE_MIN_FEE_BPS
        let feeAmount := amount * feeBPS / 10000
        let userAmount := amount - feeAmount
        let newApx := fun a => if a = s.unlockTokenAddr then s.apxUSD_bal a - amount
                               else if a = caller then s.apxUSD_bal a + userAmount
                               else s.apxUSD_bal a
        let newBuffer := s.overcollateralizationBuffer + feeAmount
        let newCollateral := s.totalCollateralValue + feeAmount
        let newUnlockTokens := fun rid => if rid = requestId then none else s.unlockTokens rid
        let newCooldown := fun u rid => if u = caller && rid = requestId then 0 else s.cooldownEnd u rid
        some { s with
          apxUSD_bal := newApx,
          overcollateralizationBuffer := newBuffer,
          totalCollateralValue := newCollateral,
          unlockTokens := newUnlockTokens,
          cooldownEnd := newCooldown
        }
  | Op.redeemApxUSD amount =>
    if amount = 0 then none
    else if s.apxUSD_bal caller < amount then none
    else if s.redemptionValue != CENT then none  -- routine redemption only at $1
    else
      let usdcAmount := amount * s.redemptionValue / CENT
      if s.usdc_bal s.treasuryAddr < usdcAmount then none
      else
        let newApx := fun a => if a = caller then s.apxUSD_bal a - amount else s.apxUSD_bal a
        let newUsdc := fun a => if a = s.treasuryAddr then s.usdc_bal a - usdcAmount
                                else if a = caller then s.usdc_bal a + usdcAmount
                                else s.usdc_bal a
        let newTotalSupply := s.totalSupply_apxUSD - amount
        let newCollateral := s.totalCollateralValue - usdcAmount
        -- buffer preservation: ensure buffer not reduced
        let newBuffer := newCollateral - newTotalSupply * CENT
        if newBuffer < s.overcollateralizationBuffer then none
        else some { s with
          apxUSD_bal := newApx,
          usdc_bal := newUsdc,
          totalSupply_apxUSD := newTotalSupply,
          totalCollateralValue := newCollateral,
          overcollateralizationBuffer := newBuffer
        }
  | Op.withdraw assets receiver =>
    if assets = 0 then none
    else
      let shares := assets * RAY / s.exchangeRate
      if shares = 0 then none
      else if s.apyUSD_bal caller < shares then none
      else
        -- pull vested yield
        let vested := vestedAmount s
        let newLinearApx := fun a => if a = s.linearVestV0Addr then s.apxUSD_bal a - vested
                                     else if a = s.vaultAddr then s.apxUSD_bal a + vested
                                     else s.apxUSD_bal a
        let remainingVested := s.totalVested - vested
        let newVestStart := s.now
        let newVestEnd := s.now + s.vestPeriod
        -- now process withdrawal
        if s.apxUSD_bal s.vaultAddr + vested < assets then none  -- after pull, vault must have enough
        else
          let newApx := fun a => if a = s.vaultAddr then newLinearApx s.vaultAddr - assets
                                 else if a = s.unlockTokenAddr then s.apxUSD_bal a + assets
                                 else newLinearApx a
          let newApy := fun a => if a = caller then s.apyUSD_bal a - shares else s.apyUSD_bal a
          let newTotalSupply := s.totalSupply_apyUSD - shares
          let requestId := s.nextRequestId
          let newUnlockTokens := fun rid => if rid = requestId then some (receiver, assets, s.now, false) else s.unlockTokens rid
          let newCooldown := fun u rid => if u = receiver && rid = requestId then s.now + COOLDOWN_PERIOD else s.cooldownEnd u rid
          let newRate := computeExchangeRate { s with
            apxUSD_bal := newApx,
            totalSupply_apyUSD := newTotalSupply,
            totalVested := remainingVested,
            vestStart := newVestStart,
            vestEnd := newVestEnd
          }
          if newRate < s.exchangeRate then none
          else some { s with
            apxUSD_bal := newApx,
            apyUSD_bal := newApy,
            totalSupply_apyUSD := newTotalSupply,
            totalVested := remainingVested,
            vestStart := newVestStart,
            vestEnd := newVestEnd,
            unlockTokens := newUnlockTokens,
            cooldownEnd := newCooldown,
            nextRequestId := requestId + 1,
            exchangeRate := newRate
          }
  | Op.withdrawForMaxShares assets maxShares receiver =>
    if assets = 0 then none
    else
      let shares := assets * RAY / s.exchangeRate
      if shares > maxShares then none
      else step s (Op.withdraw assets receiver) caller  -- reuse withdraw logic
  | Op.redeem shares receiver =>
    if shares = 0 then none
    else if s.apyUSD_bal caller < shares then none
    else
      let assets := shares * s.exchangeRate / RAY
      if assets = 0 then none
      else step s (Op.withdraw assets receiver) caller
  | Op.redeemForMinAssets shares minAssets receiver =>
    if shares = 0 then none
    else
      let assets := shares * s.exchangeRate / RAY
      if assets < minAssets then none
      else step s (Op.redeem shares receiver) caller
  | Op.pause =>
    if s.pausers.contains caller then some { s with globalPause := true } else none
  | Op.unpause =>
    if s.pausers.contains caller then some { s with globalPause := false } else none
  | Op.addToWhitelist addr =>
    if s.admins.contains caller then some { s with whitelist := fun a => if a = addr then true else s.whitelist a } else none
  | Op.removeFromWhitelist addr =>
    if s.admins.contains caller then some { s with whitelist := fun a => if a = addr then false else s.whitelist a } else none
  | Op.addToDenylist addr =>
    if s.admins.contains caller then some { s with denylist := fun a => if a = addr then true else s.denylist a } else none
  | Op.removeFromDenylist addr =>
    if s.admins.contains caller then some { s with denylist := fun a => if a = addr then false else s.denylist a } else none
  | Op.setYieldRate bps =>
    if s.govRole.contains caller then some { s with yieldRateMonth := bps } else none
  | Op.creditYield amount =>
    if caller != s.yieldDistributor then none
    else if amount = 0 then none
    else
      -- credit yield: increase totalCollateralValue and deposit into LinearVestV0
      let newCollateral := s.totalCollateralValue + amount
      let newLinearApx := fun a => if a = s.linearVestV0Addr then s.apxUSD_bal a + amount else s.apxUSD_bal a
      let newTotalVested := s.totalVested + amount
      let newVestStart := s.now
      let newVestEnd := s.now + s.vestPeriod
      let newRate := computeExchangeRate { s with
        apxUSD_bal := newLinearApx,
        totalVested := newTotalVested,
        vestStart := newVestStart,
        vestEnd := newVestEnd,
        totalCollateralValue := newCollateral
      }
      if newRate < s.exchangeRate then none
      else some { s with
        totalCollateralValue := newCollateral,
        apxUSD_bal := newLinearApx,
        totalVested := newTotalVested,
        vestStart := newVestStart,
        vestEnd := newVestEnd,
        exchangeRate := newRate
      }
  | Op.voteBufferDeployment amount =>
    if s.govTokenBal caller < s.govThreshold then none
    else if amount = 0 then none
    else
      let newBuffer := s.overcollateralizationBuffer + amount
      let newCollateral := s.totalCollateralValue + amount
      some { s with
        overcollateralizationBuffer := newBuffer,
        totalCollateralValue := newCollateral
      }
  | Op.executeRFQRedemption user amount =>
    if !s.rfqCounterparties.contains caller then none
    else if !s.whitelist user then none
    else if amount = 0 then none
    else if s.apxUSD_bal user < amount then none
    else if s.redemptionValue != CENT then none  -- routine redemption at $1
    else
      let usdcAmount := amount * s.redemptionValue / CENT
      if s.usdc_bal s.treasuryAddr < usdcAmount then none
      else
        let newApx := fun a => if a = user then s.apxUSD_bal a - amount else s.apxUSD_bal a
        let newUsdc := fun a => if a = s.treasuryAddr then s.usdc_bal a - usdcAmount
                                else if a = user then s.usdc_bal a + usdcAmount
                                else s.usdc_bal a
        let newCollateral := s.totalCollateralValue - usdcAmount
        -- buffer preservation: ensure buffer not reduced
        let newBuffer := newCollateral - (s.totalSupply_apxUSD - amount) * CENT
        if newBuffer < s.overcollateralizationBuffer then none
        else some { s with
          apxUSD_bal := newApx,
          usdc_bal := newUsdc,
          totalSupply_apxUSD := s.totalSupply_apxUSD - amount,
          totalCollateralValue := newCollateral,
          overcollateralizationBuffer := newBuffer
        }
  | Op.updateRedemptionValue => sorry
  | Op.handleStressEvent amount => sorry
  | Op.catastrophicBackstop => sorry
  termination_by op
  decreasing_by
    all_goals (simp_wf; try omega)

end Apyx
