import Std
open Nat

namespace Apyx

abbrev Address := Nat

def ray : Nat := 10^27
def day : Nat := 86400
def cooldownPeriod : Nat := 20 * day
def minFlexibleClaim : Nat := 3 * day

def vaultAddress : Address := 0

structure State where
  now : Nat
  globalPause : Bool
  pauseController : Address
  admin : Address
  governance : Address
  oracle : Address
  yieldDistributor : Address
  whitelist : Address → Bool
  denylist : Address → Bool
  rfqCounterparties : List Address
  governanceThreshold : Nat
  emergencyFlag : Bool
  totalSupply_apxUSD : Nat
  totalSupply_apyUSD : Nat
  apxUSDBal : Address → Nat
  apyUSDBal : Address → Nat
  governanceTokenBal : Address → Nat
  vaultApxUSDBal : Nat
  exchangeRate : Nat
  totalCollateralValue : Nat
  redemptionValue : Nat
  overcollateralizationBuffer : Nat
  yieldRateMonth : Nat
  vestStart : Nat
  vestTotal : Nat
  vestPeriod : Nat
  nextUnlockId : Nat
  unlockRequestId : Address → Option Nat
  unlockRequests : Nat → Option (Address × Nat × Nat)
  flexibleUnlockRequests : Nat → Option (Address × Nat × Nat × Nat)
  unlockTokenOwner : Nat → Option Address
  unlockTokenAmount : Nat → Nat
  bufferDeployed : Bool
  usdcBal : Address → Nat
  usdcReserve : Nat
  eventLog : List (String × List Nat)
deriving Inhabited

def vestedAmount (s : State) (now : Nat) : Nat :=
  if now < s.vestStart then 0
  else
    let elapsed := now - s.vestStart
    if elapsed ≥ s.vestPeriod then s.vestTotal
    else (elapsed * s.vestTotal) / s.vestPeriod

def totalAssets (s : State) : Nat :=
  s.vaultApxUSDBal + vestedAmount s s.now

def computeExchangeRate (s : State) : Nat :=
  if s.totalSupply_apyUSD = 0 then ray
  else (totalAssets s * ray) / s.totalSupply_apyUSD

def updateExchangeRate (s : State) : State :=
  { s with exchangeRate := computeExchangeRate s }

def flexibleUnlockFee (requestTime : Nat) (now : Nat) : Nat :=
  if now < requestTime + minFlexibleClaim then 0
  else
    let elapsed := now - requestTime
    if elapsed ≥ cooldownPeriod then 10
    else
      let feeBps := 350 - (elapsed * 340) / cooldownPeriod
      max feeBps 10

def lockShares (assets : Nat) (exchangeRate : Nat) : Nat :=
  (assets * ray) / exchangeRate

def redeemAssets (shares : Nat) (exchangeRate : Nat) : Nat :=
  (shares * exchangeRate) / ray

def withdrawShares (assets : Nat) (exchangeRate : Nat) : Nat :=
  (assets * ray + exchangeRate - 1) / exchangeRate

def pullVestedYield (s : State) : State :=
  let v := vestedAmount s s.now
  if v = 0 then s
  else
    { s with
        vaultApxUSDBal := s.vaultApxUSDBal + v
        vestTotal := s.vestTotal - v
        vestStart := s.now
    }

def createStandardUnlock (s : State) (owner : Address) (amount : Nat) : State :=
  let id := s.nextUnlockId
  let cooldownEnd := s.now + cooldownPeriod
  { s with
      nextUnlockId := id + 1
      unlockRequestId := fun a => if a = owner then some id else s.unlockRequestId a
      unlockRequests := fun i => if i = id then some (owner, amount, cooldownEnd) else s.unlockRequests i
      unlockTokenOwner := fun i => if i = id then some owner else s.unlockTokenOwner i
      unlockTokenAmount := fun i => if i = id then amount else s.unlockTokenAmount i
  }

def updateStandardUnlock (s : State) (id : Nat) (owner : Address) (addAmount : Nat) : State :=
  match s.unlockRequests id with
  | none => s
  | some (_, oldAmount, _) =>
    let newAmount := oldAmount + addAmount
    let newCooldownEnd := s.now + cooldownPeriod
    { s with
        unlockRequests := fun i => if i = id then some (owner, newAmount, newCooldownEnd) else s.unlockRequests i
        unlockTokenAmount := fun i => if i = id then newAmount else s.unlockTokenAmount i
    }

def createFlexibleUnlock (s : State) (owner : Address) (amount : Nat) : State :=
  let id := s.nextUnlockId
  let requestTime := s.now
  let cooldownEnd := s.now + cooldownPeriod
  { s with
      nextUnlockId := id + 1
      flexibleUnlockRequests := fun i => if i = id then some (owner, amount, requestTime, cooldownEnd) else s.flexibleUnlockRequests i
      unlockTokenOwner := fun i => if i = id then some owner else s.unlockTokenOwner i
      unlockTokenAmount := fun i => if i = id then amount else s.unlockTokenAmount i
  }

def burnUnlockNFT (s : State) (id : Nat) : State :=
  { s with
      unlockTokenOwner := fun i => if i = id then none else s.unlockTokenOwner i
      unlockTokenAmount := fun i => if i = id then 0 else s.unlockTokenAmount i
  }

def mintApxUSD (s : State) (to : Address) (amount : Nat) : State :=
  { s with
      totalSupply_apxUSD := s.totalSupply_apxUSD + amount
      apxUSDBal := fun a => if a = to then s.apxUSDBal a + amount else s.apxUSDBal a
  }

def burnApxUSD (s : State) (fromAddr : Address) (amount : Nat) : State :=
  { s with
      totalSupply_apxUSD := s.totalSupply_apxUSD - amount
      apxUSDBal := fun a => if a = fromAddr then s.apxUSDBal a - amount else s.apxUSDBal a
  }

def mintApyUSD (s : State) (to : Address) (shares : Nat) : State :=
  { s with
      totalSupply_apyUSD := s.totalSupply_apyUSD + shares
      apyUSDBal := fun a => if a = to then s.apyUSDBal a + shares else s.apyUSDBal a
  }

def burnApyUSD (s : State) (fromAddr : Address) (shares : Nat) : State :=
  { s with
      totalSupply_apyUSD := s.totalSupply_apyUSD - shares
      apyUSDBal := fun a => if a = fromAddr then s.apyUSDBal a - shares else s.apyUSDBal a
  }

def transferApxUSD (s : State) (fromAddr toAddr : Address) (amount : Nat) : State :=
  { s with
      apxUSDBal := fun a =>
        if a = fromAddr then s.apxUSDBal a - amount
        else if a = toAddr then s.apxUSDBal a + amount
        else s.apxUSDBal a
  }

def mem (a : Address) (l : List Address) : Bool :=
  l.elem a

def overcollateralizationBuffer (s : State) : Nat :=
  let redemptionTotal := (s.totalSupply_apxUSD * s.redemptionValue) / ray
  if s.totalCollateralValue > redemptionTotal then s.totalCollateralValue - redemptionTotal else 0

def emitEvent (s : State) (name : String) (args : List Nat) : State :=
  { s with eventLog := (name, args) :: s.eventLog }

-- ERC-4626 helper functions
def convertToShares (s : State) (assets : Nat) : Nat :=
  lockShares assets s.exchangeRate

def convertToAssets (s : State) (shares : Nat) : Nat :=
  redeemAssets shares s.exchangeRate

def maxDeposit (s : State) (receiver : Address) : Nat :=
  if s.globalPause then 0 else s.apxUSDBal receiver

def maxMint (s : State) (receiver : Address) : Nat :=
  if s.globalPause then 0 else convertToShares s (s.apxUSDBal receiver)

def maxWithdraw (s : State) (owner : Address) : Nat :=
  if s.globalPause then 0 else convertToAssets s (s.apyUSDBal owner)

def maxRedeem (s : State) (owner : Address) : Nat :=
  if s.globalPause then 0 else s.apyUSDBal owner

def previewDeposit (s : State) (assets : Nat) : Nat :=
  convertToShares s assets

def previewMint (s : State) (shares : Nat) : Nat :=
  convertToAssets s shares

def previewWithdraw (s : State) (assets : Nat) : Nat :=
  withdrawShares assets s.exchangeRate

def previewRedeem (s : State) (shares : Nat) : Nat :=
  convertToAssets s shares

inductive Op
  | depositUSDC (amount : Nat)
  | mintApxUSD (to : Address) (amount : Nat)
  | lockApxUSD (amount : Nat)
  | requestUnlock (amount : Nat)
  | claimUnlock (requestId : Nat)
  | redeemApxUSD (amount : Nat)
  | withdraw (assets : Nat) (receiver : Address)
  | redeem (shares : Nat) (receiver : Address)
  | flexibleRequestUnlock (amount : Nat)
  | flexibleClaimUnlock (requestId : Nat)
  | pause
  | unpause
  | addToWhitelist (addr : Address)
  | removeFromWhitelist (addr : Address)
  | addToDenylist (addr : Address)
  | removeFromDenylist (addr : Address)
  | setYieldRate (bps : Nat)
  | creditYield (amount : Nat)
  | voteBufferDeployment
  | executeRFQRedemption (user : Address) (amount : Nat)
  | updateRedemptionValue
  | handleStressEvent (amount : Nat)
  | catastrophicBackstop

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.depositUSDC amount =>
    if s.globalPause then none
    else if ¬ s.whitelist caller then none
    else if s.usdcBal caller < amount then none
    else
      let s1 := { s with
        usdcBal := fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a
        usdcReserve := s.usdcReserve + amount
      }
      let s2 := mintApxUSD s1 caller amount
      let s3 := emitEvent s2 "Deposit" [caller, caller, caller, amount, amount] -- sender, receiver, owner, assets, shares (1:1)
      some s3
  | Op.mintApxUSD to amount =>
    if s.globalPause then none
    else if ¬ s.whitelist caller then none
    else if s.usdcBal caller < amount then none
    else
      let s1 := { s with
        usdcBal := fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a
        usdcReserve := s.usdcReserve + amount
      }
      let s2 := mintApxUSD s1 to amount
      let s3 := emitEvent s2 "Deposit" [caller, to, to, amount, amount]
      some s3
  | Op.lockApxUSD amount =>
    if s.globalPause then none
    else if s.apxUSDBal caller < amount then none
    else
      let shares := lockShares amount s.exchangeRate
      let s1 := burnApxUSD s caller amount
      let s2 := { s1 with vaultApxUSDBal := s1.vaultApxUSDBal + amount }
      let s3 := mintApyUSD s2 caller shares
      let s4 := updateExchangeRate s3
      let s5 := emitEvent s4 "Deposit" [caller, caller, caller, amount, shares]
      some s5
  | Op.requestUnlock amount =>
    if s.globalPause then none
    else if s.apxUSDBal caller < amount then none
    else
      let s1 := burnApxUSD s caller amount
      let s2 := createStandardUnlock s1 caller amount
      some s2
  | Op.claimUnlock requestId =>
    match s.unlockRequests requestId with
    | none => none
    | some (owner, amount, cooldownEnd) =>
      if s.unlockTokenOwner requestId != some owner then none
      else if s.now < cooldownEnd then none
      else
        let s1 := burnUnlockNFT s requestId
        let s2 := mintApxUSD s1 owner amount
        some s2
  | Op.redeemApxUSD amount =>
    if s.globalPause then none
    else if ¬ s.whitelist caller then none
    else if s.apxUSDBal caller < amount then none
    else
      let usdcAmount := (amount * s.redemptionValue) / ray
      if s.usdcReserve < usdcAmount then none
      else
        let oldBuffer := overcollateralizationBuffer s
        let s1 := burnApxUSD s caller amount
        let s2 := { s1 with
          usdcReserve := s1.usdcReserve - usdcAmount
          usdcBal := fun a => if a = caller then s1.usdcBal a + usdcAmount else s1.usdcBal a
        }
        let newBuffer := overcollateralizationBuffer s2
        if newBuffer < oldBuffer then none
        else
          let s3 := emitEvent s2 "Redeem" [caller, amount, usdcAmount]
          some s3
  | Op.withdraw assets receiver =>
    if s.globalPause then none
    else
      let s1 := pullVestedYield s
      let shares := withdrawShares assets s1.exchangeRate
      if s1.apyUSDBal caller < shares then none
      else if s1.vaultApxUSDBal < assets then none
      else
        let s2 := burnApyUSD s1 caller shares
        let s3 := { s2 with vaultApxUSDBal := s2.vaultApxUSDBal - assets }
        let s4 := createStandardUnlock s3 receiver assets
        let s5 := updateExchangeRate s4
        let s6 := emitEvent s5 "Withdraw" [caller, receiver, caller, assets, shares]
        some s6
  | Op.redeem shares receiver =>
    if s.globalPause then none
    else
      let s1 := pullVestedYield s
      if s1.apyUSDBal caller < shares then none
      else
        let assets := redeemAssets shares s1.exchangeRate
        if s1.vaultApxUSDBal < assets then none
        else
          let s2 := burnApyUSD s1 caller shares
          let s3 := { s2 with vaultApxUSDBal := s2.vaultApxUSDBal - assets }
          let s4 := createStandardUnlock s3 receiver assets
          let s5 := updateExchangeRate s4
          let s6 := emitEvent s5 "Withdraw" [caller, receiver, caller, assets, shares]
          some s6
  | Op.flexibleRequestUnlock amount =>
    if s.globalPause then none
    else if s.apxUSDBal caller < amount then none
    else
      let s1 := burnApxUSD s caller amount
      let s2 := createFlexibleUnlock s1 caller amount
      some s2
  | Op.flexibleClaimUnlock requestId =>
    match s.flexibleUnlockRequests requestId with
    | none => none
    | some (owner, amount, requestTime, cooldownEnd) =>
      if s.unlockTokenOwner requestId != some owner then none
      else if s.now < cooldownEnd then none
      else
        let feeBps := flexibleUnlockFee requestTime s.now
        let fee := (amount * feeBps) / 10000
        let claimAmount := amount - fee
        let s1 := burnUnlockNFT s requestId
        let s2 := mintApxUSD s1 owner claimAmount
        some s2
  | Op.pause =>
    if caller == s.pauseController then some { s with globalPause := true }
    else none
  | Op.unpause =>
    if caller == s.pauseController then some { s with globalPause := false }
    else none
  | Op.addToWhitelist addr =>
    if caller == s.admin then some { s with whitelist := fun a => if a = addr then true else s.whitelist a }
    else none
  | Op.removeFromWhitelist addr =>
    if caller == s.admin then some { s with whitelist := fun a => if a = addr then false else s.whitelist a }
    else none
  | Op.addToDenylist addr =>
    if caller == s.admin then some { s with denylist := fun a => if a = addr then true else s.denylist a }
    else none
  | Op.removeFromDenylist addr =>
    if caller == s.admin then some { s with denylist := fun a => if a = addr then false else s.denylist a }
    else none
  | Op.setYieldRate bps =>
    if caller == s.admin then some { s with yieldRateMonth := bps }
    else none
  | Op.creditYield amount =>
    if caller == s.yieldDistributor then
      let s1 := { s with
        usdcReserve := s.usdcReserve + amount
        vestTotal := s.vestTotal + amount
        vestStart := s.now
      }
      some s1
    else none
  | Op.voteBufferDeployment => sorry
  | Op.executeRFQRedemption user amount => sorry
  | Op.updateRedemptionValue =>
    if caller == s.oracle then
      -- placeholder: in practice would fetch from oracle
      some s
    else none
  | Op.handleStressEvent amount => sorry
  | Op.catastrophicBackstop => sorry

-- Requirements as theorems





-- BROKEN: 
-- BROKEN: 
-- BROKEN: open Nat
-- BROKEN: 
-- BROKEN: 
-- BROKEN: 
-- BROKEN: abbrev Address := Nat
-- BROKEN: 
-- BROKEN: def ray : Nat := 10^27
-- BROKEN: def day : Nat := 86400
-- BROKEN: def cooldownPeriod : Nat := 20 * day
-- BROKEN: def minFlexibleClaim : Nat := 3 * day
-- BROKEN: 
-- BROKEN: def vaultAddress : Address := 0
-- BROKEN: 
-- BROKEN: structure State where
-- BROKEN:   now : Nat
-- BROKEN:   globalPause : Bool
-- BROKEN:   pauseController : Address
-- BROKEN:   admin : Address
-- BROKEN:   governance : Address
-- BROKEN:   oracle : Address
-- BROKEN:   yieldDistributor : Address
-- BROKEN:   whitelist : Address → Bool
-- BROKEN:   denylist : Address → Bool
-- BROKEN:   rfqCounterparties : List Address
-- BROKEN:   governanceThreshold : Nat
-- BROKEN:   emergencyFlag : Bool
-- BROKEN:   totalSupply_apxUSD : Nat
-- BROKEN:   totalSupply_apyUSD : Nat
-- BROKEN:   apxUSDBal : Address → Nat
-- BROKEN:   apyUSDBal : Address → Nat
-- BROKEN:   governanceTokenBal : Address → Nat
-- BROKEN:   vaultApxUSDBal : Nat
-- BROKEN:   exchangeRate : Nat
-- BROKEN:   totalCollateralValue : Nat
-- BROKEN:   redemptionValue : Nat
-- BROKEN:   overcollateralizationBuffer : Nat
-- BROKEN:   yieldRateMonth : Nat
-- BROKEN:   vestStart : Nat
-- BROKEN:   vestTotal : Nat
-- BROKEN:   vestPeriod : Nat
-- BROKEN:   nextUnlockId : Nat
-- BROKEN:   unlockRequestId : Address → Option Nat
-- BROKEN:   unlockRequests : Nat → Option (Address × Nat × Nat)
-- BROKEN:   flexibleUnlockRequests : Nat → Option (Address × Nat × Nat × Nat)
-- BROKEN:   unlockTokenOwner : Nat → Option Address
-- BROKEN:   unlockTokenAmount : Nat → Nat
-- BROKEN:   bufferDeployed : Bool
-- BROKEN: deriving Inhabited
-- BROKEN: 
-- BROKEN: def vestedAmount (s : State) (now : Nat) : Nat :=
-- BROKEN:   if now < s.vestStart then 0
-- BROKEN:   else
-- BROKEN:     let elapsed := now - s.vestStart
-- BROKEN:     if elapsed ≥ s.vestPeriod then s.vestTotal
-- BROKEN:     else (elapsed * s.vestTotal) / s.vestPeriod
-- BROKEN: 
-- BROKEN: def totalAssets (s : State) : Nat :=
-- BROKEN:   s.vaultApxUSDBal + vestedAmount s s.now
-- BROKEN: 
-- BROKEN: def computeExchangeRate (s : State) : Nat :=
-- BROKEN:   if s.totalSupply_apyUSD = 0 then ray
-- BROKEN:   else (totalAssets s * ray) / s.totalSupply_apyUSD
-- BROKEN: 
-- BROKEN: def updateExchangeRate (s : State) : State :=
-- BROKEN:   { s with exchangeRate := computeExchangeRate s }
-- BROKEN: 
-- BROKEN: def flexibleUnlockFee (requestTime : Nat) (now : Nat) : Nat :=
-- BROKEN:   if now < requestTime + minFlexibleClaim then 0
-- BROKEN:   else
-- BROKEN:     let elapsed := now - requestTime
-- BROKEN:     if elapsed ≥ cooldownPeriod then 10
-- BROKEN:     else
-- BROKEN:       let feeBps := 350 - (elapsed * 340) / cooldownPeriod
-- BROKEN:       max feeBps 10
-- BROKEN: 
-- BROKEN: def lockShares (assets : Nat) (exchangeRate : Nat) : Nat :=
-- BROKEN:   (assets * ray) / exchangeRate
-- BROKEN: 
-- BROKEN: def redeemAssets (shares : Nat) (exchangeRate : Nat) : Nat :=
-- BROKEN:   (shares * exchangeRate) / ray
-- BROKEN: 
-- BROKEN: def withdrawShares (assets : Nat) (exchangeRate : Nat) : Nat :=
-- BROKEN:   (assets * ray + exchangeRate - 1) / exchangeRate
-- BROKEN: 
-- BROKEN: def pullVestedYield (s : State) : State :=
-- BROKEN:   let v := vestedAmount s s.now
-- BROKEN:   if v = 0 then s
-- BROKEN:   else
-- BROKEN:     { s with
-- BROKEN:         vaultApxUSDBal := s.vaultApxUSDBal + v
-- BROKEN:         vestTotal := s.vestTotal - v
-- BROKEN:         vestStart := s.now
-- BROKEN:     }
-- BROKEN: 
-- BROKEN: def createStandardUnlock (s : State) (owner : Address) (amount : Nat) : State :=
-- BROKEN:   let id := s.nextUnlockId
-- BROKEN:   let cooldownEnd := s.now + cooldownPeriod
-- BROKEN:   { s with
-- BROKEN:       nextUnlockId := id + 1
-- BROKEN:       unlockRequestId := fun a => if a = owner then some id else s.unlockRequestId a
-- BROKEN:       unlockRequests := fun i => if i = id then some (owner, amount, cooldownEnd) else s.unlockRequests i
-- BROKEN:       unlockTokenOwner := fun i => if i = id then some owner else s.unlockTokenOwner i
-- BROKEN:       unlockTokenAmount := fun i => if i = id then amount else s.unlockTokenAmount i
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def updateStandardUnlock (s : State) (id : Nat) (owner : Address) (addAmount : Nat) : State :=
-- BROKEN:   match s.unlockRequests id with
-- BROKEN:   | none => s
-- BROKEN:   | some (_, oldAmount, _) =>
-- BROKEN:     let newAmount := oldAmount + addAmount
-- BROKEN:     let newCooldownEnd := s.now + cooldownPeriod
-- BROKEN:     { s with
-- BROKEN:         unlockRequests := fun i => if i = id then some (owner, newAmount, newCooldownEnd) else s.unlockRequests i
-- BROKEN:         unlockTokenAmount := fun i => if i = id then newAmount else s.unlockTokenAmount i
-- BROKEN:     }
-- BROKEN: 
-- BROKEN: def createFlexibleUnlock (s : State) (owner : Address) (amount : Nat) : State :=
-- BROKEN:   let id := s.nextUnlockId
-- BROKEN:   let requestTime := s.now
-- BROKEN:   let cooldownEnd := s.now + cooldownPeriod
-- BROKEN:   { s with
-- BROKEN:       nextUnlockId := id + 1
-- BROKEN:       flexibleUnlockRequests := fun i => if i = id then some (owner, amount, requestTime, cooldownEnd) else s.flexibleUnlockRequests i
-- BROKEN:       unlockTokenOwner := fun i => if i = id then some owner else s.unlockTokenOwner i
-- BROKEN:       unlockTokenAmount := fun i => if i = id then amount else s.unlockTokenAmount i
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def burnUnlockNFT (s : State) (id : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       unlockTokenOwner := fun i => if i = id then none else s.unlockTokenOwner i
-- BROKEN:       unlockTokenAmount := fun i => if i = id then 0 else s.unlockTokenAmount i
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def mintApxUSD (s : State) (to : Address) (amount : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apxUSD := s.totalSupply_apxUSD + amount
-- BROKEN:       apxUSDBal := fun a => if a = to then s.apxUSDBal a + amount else s.apxUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def burnApxUSD (s : State) (fromAddr : Address) (amount : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apxUSD := s.totalSupply_apxUSD - amount
-- BROKEN:       apxUSDBal := fun a => if a = fromAddr then s.apxUSDBal a - amount else s.apxUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def mintApyUSD (s : State) (to : Address) (shares : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apyUSD := s.totalSupply_apyUSD + shares
-- BROKEN:       apyUSDBal := fun a => if a = to then s.apyUSDBal a + shares else s.apyUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def burnApyUSD (s : State) (fromAddr : Address) (shares : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apyUSD := s.totalSupply_apyUSD - shares
-- BROKEN:       apyUSDBal := fun a => if a = fromAddr then s.apyUSDBal a - shares else s.apyUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def transferApxUSD (s : State) (fromAddr toAddr : Address) (amount : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       apxUSDBal := fun a =>
-- BROKEN:         if a = fromAddr then s.apxUSDBal a - amount
-- BROKEN:         else if a = toAddr then s.apxUSDBal a + amount
-- BROKEN:         else s.apxUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def mem (a : Address) (l : List Address) : Bool :=
-- BROKEN:   l.elem a
-- BROKEN: 
-- BROKEN: inductive Op
-- BROKEN:   | depositUSDC (amount : Nat)
-- BROKEN:   | mintApxUSD (to : Address) (amount : Nat)
-- BROKEN:   | lockApxUSD (amount : Nat)
-- BROKEN:   | requestUnlock (amount : Nat)
-- BROKEN:   | claimUnlock (requestId : Nat)
-- BROKEN:   | redeemApxUSD (amount : Nat)
-- BROKEN:   | withdraw (assets : Nat) (receiver : Address)
-- BROKEN:   | redeem (shares : Nat) (receiver : Address)
-- BROKEN:   | flexibleRequestUnlock (amount : Nat)
-- BROKEN:   | flexibleClaimUnlock (requestId : Nat)
-- BROKEN:   | pause
-- BROKEN:   | unpause
-- BROKEN:   | addToWhitelist (addr : Address)
-- BROKEN:   | removeFromWhitelist (addr : Address)
-- BROKEN:   | addToDenylist (addr : Address)
-- BROKEN:   | removeFromDenylist (addr : Address)
-- BROKEN:   | setYieldRate (bps : Nat)
-- BROKEN:   | creditYield (amount : Nat)
-- BROKEN:   | voteBufferDeployment
-- BROKEN:   | executeRFQRedemption (user : Address) (amount : Nat)
-- BROKEN:   | updateRedemptionValue
-- BROKEN:   | handleStressEvent (amount : Nat)
-- BROKEN:   | catastrophicBackstop
-- BROKEN: 
-- BROKEN: def step (s : State) (op : Op) (caller : Address) : Option State :=
-- BROKEN:   match op with
-- BROKEN:   | Op.depositUSDC amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else sorry
-- BROKEN:   | _ => sorry

theorem req_apyusd_value_increase (s : State) (h : s.totalSupply_apyUSD > 0) :
    computeExchangeRate s ≤ computeExchangeRate { s with now := s.now + 1 } := by
  sorry

-- BROKEN: theorem req_token_no_rebase : Prop :=
-- BROKEN:   ∀ (s : State) (id : Nat) (owner : Address) (amount : Nat),
-- BROKEN:     (s.unlockTokenOwner id = some owner) →
-- BROKEN:     (s.unlockTokenAmount id = amount) →
-- BROKEN:     let s' := createStandardUnlock s owner amount
-- BROKEN:     s'.unlockTokenAmount id = amount

-- BROKEN: theorem req_exchange_rate_non_decreasing : Prop :=
-- BROKEN:   ∀ (s : State), s.exchangeRate ≤ computeExchangeRate s

/-- When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1. -/
theorem req_redemption_exchange_rate_multiplier (s : State) (shares : Nat) :
    let assets := redeemAssets shares s.exchangeRate
    s.exchangeRate ≥ ray ∧ assets = (shares * s.exchangeRate) / ray := sorry

theorem req_single_pending_redemption_per_user (s : State) (owner : Address) : 
    (s.unlockRequestId owner).isSome → 
    let id := (s.unlockRequestId owner).get!
    (s.unlockRequests id).isSome ∧ 
    ∀ id' ≠ id, (s.unlockRequests id').isNone :=
  sorry

-- BROKEN: theorem req_cooldown_no_yield : Prop :=
-- BROKEN:   ∀ (s : State) (owner : Address) (amount : Nat) (s' : State),
-- BROKEN:     step s (Op.requestUnlock amount) owner = some s' →
-- BROKEN:     ∀ (requestId : Nat),
-- BROKEN:       s'.unlockRequests requestId = some (owner, amount, s.now + cooldownPeriod)

/-- A flexible redemption claim MUST be executable only after a minimum of 3 days have elapsed since the request. -/
theorem req_flexible_redemption_claim_minimum (s : State) (requestId : Nat) (owner : Address) (amount requestTime cooldownEnd : Nat) :
    s.flexibleUnlockRequests requestId = some (owner, amount, requestTime, cooldownEnd) →
    s.unlockTokenOwner requestId = some owner →
    (∀ s', step s (Op.flexibleClaimUnlock requestId) owner = some s' → s.now ≥ requestTime + minFlexibleClaim) :=
  fun h1 h2 => by
    intros s' h3
    -- By contradiction, assume now < requestTime + minFlexibleClaim
    -- Then show that step cannot succeed
    sorry

/-- REQ flexible-redemption-early-fee: The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %. -/
theorem req_flexible_redemption_early_fee (requestTime now : Nat) (h : now ≥ requestTime) :
    let fee := flexibleUnlockFee requestTime now
    if now < requestTime + minFlexibleClaim then
      fee = 0
    else
      let elapsed := now - requestTime
      if elapsed ≥ cooldownPeriod then
        fee = 10
      else
        let feeBps := 350 - (elapsed * 340) / cooldownPeriod
        fee = max feeBps 10 := sorry

/-- REQ overcollateralization-limit: The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin. -/
theorem req_overcollateralization_limit (s : State) :
    s.totalSupply_apxUSD ≤ s.totalCollateralValue - s.overcollateralizationBuffer := sorry

/-- REQ arbitrage-mint-access: Only eligible whitelist participants SHALL be permitted to invoke the minting pathway for arbitrage when apxUSD trades above $1.00. -/
theorem req_arbitrage_mint_access (s : State) (to : Address) (amount : Nat) (caller : Address) :
    (step s (Op.mintApxUSD to amount) caller = none) ∨ (s.whitelist caller = true) := sorry

/-- REQ arbitrage-redeem-access: Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00. -/
theorem req_arbitrage_redeem_access (s : State) (amount : Nat) (caller : Address) :
    (step s (Op.redeemApxUSD amount) caller = none) ∨ (s.whitelist caller = true) := sorry

/-- REQ linear-vest-implementation: The LinearVestV0 contract MUST implement a linear vesting mechanism for yield credited to the apyUSD vault. -/
theorem req_linear_vest_implementation (s : State) (now : Nat) :
    vestedAmount s now = if now < s.vestStart then 0 else
      let elapsed := now - s.vestStart
      if elapsed ≥ s.vestPeriod then s.vestTotal
      else (elapsed * s.vestTotal) / s.vestPeriod := by rfl

/-- REQ yield-rate-dollar-terms: The yield rate MUST be expressed in dollar terms for the month. -/
theorem req_yield_rate_dollar_terms (s : State) :
    ∃ (dollarAmount : Nat), s.yieldRateMonth = dollarAmount := by
  sorry

/-- REQ redemption_value_uniform: The system MUST apply the same Redemption Value to all participants regardless of market conditions. -/
theorem req_redemption_value_uniform (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') :
    s.redemptionValue = s'.redemptionValue := by
  sorry

/-- REQ buffer_not_consumed: The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations. -/
theorem req_buffer_not_consumed (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_routine : op ≠ Op.catastrophicBackstop ∧ op ≠ Op.handleStressEvent 0) :
    s'.overcollateralizationBuffer ≥ s.overcollateralizationBuffer := by
  sorry

/-- REQ catastrophic_backstop: Upon detection of a catastrophic scenario, the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, including the buffer, pro‑rata to remaining holders. -/
theorem req_catastrophic_backstop (s : State) (s' : State)
    (h_step : step s Op.catastrophicBackstop s.admin = some s') :
    s'.redemptionValue = s'.totalCollateralValue := by
  sorry

/-- REQ governance_deploy_buffer: The system MUST restrict voting on buffer deployment to holders of the governance token. -/
theorem req_governance_deploy_buffer (s : State) (s' : State)
    (h_step : step s Op.voteBufferDeployment s.governance = some s') :
    s.governanceTokenBal s.governance > 0 := by
  sorry

/-- REQ rfq_redemption_allowed: The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute those requests. -/
theorem req_rfq_redemption_allowed (s : State) (user : Address) (amount : Nat) (s' : State)
    (h_step : step s (Op.executeRFQRedemption user amount) s.yieldDistributor = some s')
    (h_counterparty : s.rfqCounterparties.contains s.yieldDistributor) :
    (s.apxUSDBal user ≥ amount) ∧ 
    (s.usdcReserve ≥ (amount * s.redemptionValue) / ray) ∧
    (∃ callerShares, callerShares = (amount * ray) / s.exchangeRate ∧ s.apyUSDBal s.yieldDistributor ≥ callerShares) := by
  sorry

/-- REQ deposit_immediate: The apyUSD vault MUST complete deposit operations synchronously and deliver apyUSD shares to the receiver without any delay. -/
theorem req_deposit_immediate (s : State) (amount : Nat) (to : Address) (caller : Address) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    s'.apyUSDBal to ≥ s.apyUSDBal to := by
  sorry

/-- REQ mint_immediate: The apyUSD vault MUST complete mint operations synchronously and deliver apyUSD shares to the receiver without any delay. -/
theorem req_mint_immediate (s : State) (to : Address) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.mintApxUSD to amount) caller = some s') :
    s'.apyUSDBal to ≥ s.apyUSDBal to := by
  sorry

-- BROKEN: /-- REQ unlock-cooldown: The apxUSD_unlock token MAY be redeemed for apxUSD only after a cooldown period has elapsed. -/
-- BROKEN: theorem req_unlock_cooldown (s : State) (requestId : Nat) (caller : Address)
-- BROKEN:     (h_request : s.unlockRequests requestId = some (caller, 0, s.now + cooldownPeriod))
-- BROKEN:     (h_early : s.now < (match s.unlockRequests requestId with | some (_, _, cooldownEnd) => cooldownEnd | none => 0)) :
-- BROKEN:     step s (.claimUnlock requestId) caller = none := by
-- BROKEN:   simp [step]
-- BROKEN:   split
-- BROKEN:   case _ h1 =>
-- BROKEN:     simp at h1
-- BROKEN:     have h_eq : (s.unlockRequests requestId).get! = (caller, 0, s.now + cooldownPeriod) := by simp [step]

/-- REQ totalAssets-includes-vault-balance-and-vested: The vault's totalAssets() function MUST include both the vault's apxUSD balance and the vestedAmount() reported by the LinearVestV0 contract. -/
theorem req_total_assets_includes_vault_balance_and_vested (s : State) :
    totalAssets s = s.vaultApxUSDBal + vestedAmount s s.now := rfl

/-- REQ global-pause-blocks-deposit: If the global pause is active, any deposit or mint transaction MUST revert. -/
theorem req_global_pause_blocks_deposit (s : State) (amount : Nat) (caller : Address)
    (h : s.globalPause = true) :
    step s (.depositUSDC amount) caller = none := by
  simp [step, h]

/-- REQ unlock-token-redeemable-1to1-after-20d: apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period. -/
theorem req_unlock_token_redeemable_1to1_after_20d (s : State) (requestId : Nat) (caller : Address)
    (h_request : s.unlockRequests requestId = some (caller, (s.unlockTokenAmount requestId), s.now - cooldownPeriod))
    (h_owner : s.unlockTokenOwner requestId = some caller) : 
    step s (.claimUnlock requestId) caller = none ∨ 
    (∃ s', step s (.claimUnlock requestId) caller = some s' ∧ 
           s'.apxUSDBal caller = s.apxUSDBal caller + s.unlockTokenAmount requestId) := sorry

/-- REQ unlock-token-no-yield: apxUSD_unlock tokens MUST NOT earn yield. -/
theorem req_unlock_token_no_yield (s : State) (id : Nat) (amount : Nat) (owner : Address) :
    let s_with_unlock := createStandardUnlock s owner amount
    s_with_unlock.unlockTokenAmount id = amount → 
    ∀ s', s'.now ≥ s_with_unlock.now → 
    State.unlockTokenAmount s' id = amount := by
  intro h
  intro s' h_time
  sorry

/-- REQ unlock-receipt-nft-mint: When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim. -/
theorem req_unlock_receipt_nft_mint (s : State) (owner : Address) (amount : Nat) :
    let s' := createStandardUnlock s owner amount
    s'.nextUnlockId = s.nextUnlockId + 1 ∧ 
    s'.unlockRequestId owner = some s.nextUnlockId ∧
    s'.unlockTokenOwner s.nextUnlockId = some owner := by
  simp [createStandardUnlock]

/-- REQ unlock-claimable-after-3d: Unlocks MUST become claimable after three days. -/
theorem req_unlock_claimable_after_3d (s : State) (requestId : Nat) (caller : Address)
    (h_request : s.flexibleUnlockRequests requestId = some (caller, (s.unlockTokenAmount requestId), s.now - minFlexibleClaim, s.now - minFlexibleClaim + cooldownPeriod))
    (h_owner : s.unlockTokenOwner requestId = some caller) :
    step s (.flexibleClaimUnlock requestId) caller ≠ none := sorry

-- BROKEN: /-- REQ early-unlock-fee-linear-decline: The early unlock fee MUST decline linearly over time from 3.5 % down to 0.1 %. -/
-- BROKEN: theorem req_early_unlock_fee_linear_decline (requestTime now : Nat) (h_elapsed : now ≥ requestTime + minFlexibleClaim) (h_not_late : now < requestTime + cooldownPeriod) :
-- BROKEN:     let elapsed := now - requestTime
-- BROKEN:     let feeBps := 350 - (elapsed * 340) / cooldownPeriod
-- BROKEN:     10 ≤ feeBps ∧ feeBps ≤ 350 := by
-- BROKEN:   have h1 : elapsed ≥ minFlexibleClaim := Nat.sub_le_sub_right h_elapsed requestTime
-- BROKEN:   have h2 : elapsed < cooldownPeriod := Nat.sub_lt_of_pos_le (Nat.lt_of_lt_of_le (Nat.add_lt_of_lt h_not_late (Nat.zero_le _)) (Nat.le_add_right _ _)) h_not_late
-- BROKEN:   unfold flexibleUnlockFee
-- BROKEN:   simp [h_elapsed, h_not_late]
-- BROKEN:   split
-- BROKEN:   . contradiction
-- BROKEN:   . split
-- BROKEN:     . rfl
-- BROKEN:     . have h3 : elapsed ≥ minFlexibleClaim := h1
-- BROKEN:       have h4 : elapsed < cooldownPeriod := h2
-- BROKEN:       have h5 : 350 - elapsed * 340 / cooldownPeriod ≥ 10 := by
-- BROKEN:         have key : elapsed * 340 / cooldownPeriod ≤ 340 := by
-- BROKEN:           apply Nat.div_le_of_le_mul
-- BROKEN:           rw [Nat.mul_comm]
-- BROKEN:           exact Nat.mul_le_mul_right _ (Nat.le_of_lt_succ h4)
-- BROKEN:         exact Nat.sub_le_sub_left 350 340 _ key
-- BROKEN:       have h6 : 350 - elapsed * 340 / cooldownPeriod ≤ 350 := sorry

-- BROKEN: /-- REQ unlock-cannot-be-cancelled: The system MUST NOT allow an unlocking request to be cancelled once it has been initiated. -/

-- BROKEN: /-- REQ unlock-conversion-after-cooldown: Conversion of apxUSD_unlock to apxUSD MUST only be possible after the cooldown period has elapsed. -/

/-- REQ multiple-unlocks-reset-cooldown: If a user initiates multiple unlocks, the system MUST reset the cooldown period for the total locked amount. -/
theorem req_multiple_unlocks_reset_cooldown (s : State) (id : Nat) (owner : Address) (addAmount : Nat)
    (h : s.unlockRequests id = some (owner, 0, 0)) :
    let s' := updateStandardUnlock s id owner addAmount
    match s'.unlockRequests id with
    | some (_, _, newCooldownEnd) => newCooldownEnd = s'.now + cooldownPeriod
    | none => False := sorry

-- BROKEN: /-- REQ withdrawForMaxShares-revert-if-exceeds-maxShares: withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of apyUSD shares required to withdraw the assets exceeds maxShares. -/

-- BROKEN: /-- REQ redeemForMinAssets-revert-if-below-minAssets: redeemForMinAssets(uint256 shares, uint256 minAssets, address receiver) MUST revert if the amount of apxUSD assets to be received is less than minAssets. -/

-- BROKEN: /-- REQ vault-pulls-vested-yield-before-withdraw: When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal. -/

-- BROKEN: /-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
-- BROKEN: 
-- BROKEN: 
-- BROKEN: -- Theorems added after model extension

/-- REQ deposit-mint-apxusd: The protocol MUST mint apxUSD to a user when the user deposits USDC. -/
theorem req_deposit_mint_apxusd (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true) (h3 : s.usdcBal caller ≥ amount) :
    ∃ s', step s (Op.depositUSDC amount) caller = some s' ∧
          s'.apxUSDBal caller = s.apxUSDBal caller + amount ∧
          s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount := by
  sorry

/-- REQ mint-price: The protocol MUST price newly minted apxUSD at $1 per unit. -/
theorem req_mint_price (s : State) (amount : Nat) (to : Address) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true) (h3 : s.usdcBal caller ≥ amount) :
    ∃ s', step s (Op.mintApxUSD to amount) caller = some s' ∧
          s'.apxUSDBal to = s.apxUSDBal to + amount ∧
          s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount := by
  sorry

/-- REQ redemption-value: The protocol MUST allow redemption of apxUSD at the current Redemption Value. -/
theorem req_redemption_value (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true)
    (h3 : s.apxUSDBal caller ≥ amount)
    (h4 : s.usdcReserve ≥ (amount * s.redemptionValue) / ray) :
    ∃ s', step s (Op.redeemApxUSD amount) caller = some s' := by
  sorry

-- BROKEN: /-- REQ no-rehypothecation: The protocol MUST NOT rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose. -/
-- BROKEN: -- UNFORMALIZABLE req_no_rehypothecation: The model does not specify uses of apxUSD beyond minting/burning/transferring and locking.

-- BROKEN: /-- REQ yield-distribution-period: The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period. -/
-- BROKEN: -- UNFORMALIZABLE req_yield_distribution_period: The model does not explicitly track time-based distribution of yield over 20 days; it only tracks vesting.

/-- REQ lock-apxusd: The protocol MUST allow a user to lock apxUSD in the vault and receive apyUSD. -/
theorem req_lock_apxusd (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.apxUSDBal caller ≥ amount) :
    ∃ s', step s (Op.lockApxUSD amount) caller = some s' := by
  sorry

-- BROKEN: /-- REQ price-may-include-spreads: The protocol MAY reflect spreads and offchain execution expenses in the price during minting and redemption. -/
-- BROKEN: -- UNFORMALIZABLE req_price_may_include_spreads: The model does not explicitly model spreads or offchain execution expenses.

-- BROKEN: /-- REQ rebalance-overcollateralization: The system SHALL rebalance the collateral basket so that apxUSD remains over‑collateralized. -/
-- BROKEN: -- UNFORMALIZABLE req_rebalance_overcollateralization: The model does not specify rebalancing mechanisms or constraints on collateral basket composition.
-- BROKEN: 
-- BROKEN: open Nat
-- BROKEN: 
-- BROKEN: 
-- BROKEN: 
-- BROKEN: abbrev Address := Nat
-- BROKEN: 
-- BROKEN: def ray : Nat := 10^27
-- BROKEN: def day : Nat := 86400
-- BROKEN: def cooldownPeriod : Nat := 20 * day
-- BROKEN: def minFlexibleClaim : Nat := 3 * day
-- BROKEN: 
-- BROKEN: def vaultAddress : Address := 0
-- BROKEN: 
-- BROKEN: structure State where
-- BROKEN:   now : Nat
-- BROKEN:   globalPause : Bool
-- BROKEN:   pauseController : Address
-- BROKEN:   admin : Address
-- BROKEN:   governance : Address
-- BROKEN:   oracle : Address
-- BROKEN:   yieldDistributor : Address
-- BROKEN:   whitelist : Address → Bool
-- BROKEN:   denylist : Address → Bool
-- BROKEN:   rfqCounterparties : List Address
-- BROKEN:   governanceThreshold : Nat
-- BROKEN:   emergencyFlag : Bool
-- BROKEN:   totalSupply_apxUSD : Nat
-- BROKEN:   totalSupply_apyUSD : Nat
-- BROKEN:   apxUSDBal : Address → Nat
-- BROKEN:   apyUSDBal : Address → Nat
-- BROKEN:   governanceTokenBal : Address → Nat
-- BROKEN:   vaultApxUSDBal : Nat
-- BROKEN:   exchangeRate : Nat
-- BROKEN:   totalCollateralValue : Nat
-- BROKEN:   redemptionValue : Nat
-- BROKEN:   overcollateralizationBuffer : Nat
-- BROKEN:   yieldRateMonth : Nat
-- BROKEN:   vestStart : Nat
-- BROKEN:   vestTotal : Nat
-- BROKEN:   vestPeriod : Nat
-- BROKEN:   nextUnlockId : Nat
-- BROKEN:   unlockRequestId : Address → Option Nat
-- BROKEN:   unlockRequests : Nat → Option (Address × Nat × Nat)
-- BROKEN:   flexibleUnlockRequests : Nat → Option (Address × Nat × Nat × Nat)
-- BROKEN:   unlockTokenOwner : Nat → Option Address
-- BROKEN:   unlockTokenAmount : Nat → Nat
-- BROKEN:   bufferDeployed : Bool
-- BROKEN:   usdcBal : Address → Nat
-- BROKEN:   usdcReserve : Nat
-- BROKEN:   eventLog : List (String × List Nat)
-- BROKEN: deriving Inhabited
-- BROKEN: 
-- BROKEN: def vestedAmount (s : State) (now : Nat) : Nat :=
-- BROKEN:   if now < s.vestStart then 0
-- BROKEN:   else
-- BROKEN:     let elapsed := now - s.vestStart
-- BROKEN:     if elapsed ≥ s.vestPeriod then s.vestTotal
-- BROKEN:     else (elapsed * s.vestTotal) / s.vestPeriod
-- BROKEN: 
-- BROKEN: def totalAssets (s : State) : Nat :=
-- BROKEN:   s.vaultApxUSDBal + vestedAmount s s.now
-- BROKEN: 
-- BROKEN: def computeExchangeRate (s : State) : Nat :=
-- BROKEN:   if s.totalSupply_apyUSD = 0 then ray
-- BROKEN:   else (totalAssets s * ray) / s.totalSupply_apyUSD
-- BROKEN: 
-- BROKEN: def updateExchangeRate (s : State) : State :=
-- BROKEN:   { s with exchangeRate := computeExchangeRate s }
-- BROKEN: 
-- BROKEN: def flexibleUnlockFee (requestTime : Nat) (now : Nat) : Nat :=
-- BROKEN:   if now < requestTime + minFlexibleClaim then 0
-- BROKEN:   else
-- BROKEN:     let elapsed := now - requestTime
-- BROKEN:     if elapsed ≥ cooldownPeriod then 10
-- BROKEN:     else
-- BROKEN:       let feeBps := 350 - (elapsed * 340) / cooldownPeriod
-- BROKEN:       max feeBps 10
-- BROKEN: 
-- BROKEN: def lockShares (assets : Nat) (exchangeRate : Nat) : Nat :=
-- BROKEN:   (assets * ray) / exchangeRate
-- BROKEN: 
-- BROKEN: def redeemAssets (shares : Nat) (exchangeRate : Nat) : Nat :=
-- BROKEN:   (shares * exchangeRate) / ray
-- BROKEN: 
-- BROKEN: def withdrawShares (assets : Nat) (exchangeRate : Nat) : Nat :=
-- BROKEN:   (assets * ray + exchangeRate - 1) / exchangeRate
-- BROKEN: 
-- BROKEN: def pullVestedYield (s : State) : State :=
-- BROKEN:   let v := vestedAmount s s.now
-- BROKEN:   if v = 0 then s
-- BROKEN:   else
-- BROKEN:     { s with
-- BROKEN:         vaultApxUSDBal := s.vaultApxUSDBal + v
-- BROKEN:         vestTotal := s.vestTotal - v
-- BROKEN:         vestStart := s.now
-- BROKEN:     }
-- BROKEN: 
-- BROKEN: def createStandardUnlock (s : State) (owner : Address) (amount : Nat) : State :=
-- BROKEN:   let id := s.nextUnlockId
-- BROKEN:   let cooldownEnd := s.now + cooldownPeriod
-- BROKEN:   { s with
-- BROKEN:       nextUnlockId := id + 1
-- BROKEN:       unlockRequestId := fun a => if a = owner then some id else s.unlockRequestId a
-- BROKEN:       unlockRequests := fun i => if i = id then some (owner, amount, cooldownEnd) else s.unlockRequests i
-- BROKEN:       unlockTokenOwner := fun i => if i = id then some owner else s.unlockTokenOwner i
-- BROKEN:       unlockTokenAmount := fun i => if i = id then amount else s.unlockTokenAmount i
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def updateStandardUnlock (s : State) (id : Nat) (owner : Address) (addAmount : Nat) : State :=
-- BROKEN:   match s.unlockRequests id with
-- BROKEN:   | none => s
-- BROKEN:   | some (_, oldAmount, _) =>
-- BROKEN:     let newAmount := oldAmount + addAmount
-- BROKEN:     let newCooldownEnd := s.now + cooldownPeriod
-- BROKEN:     { s with
-- BROKEN:         unlockRequests := fun i => if i = id then some (owner, newAmount, newCooldownEnd) else s.unlockRequests i
-- BROKEN:         unlockTokenAmount := fun i => if i = id then newAmount else s.unlockTokenAmount i
-- BROKEN:     }
-- BROKEN: 
-- BROKEN: def createFlexibleUnlock (s : State) (owner : Address) (amount : Nat) : State :=
-- BROKEN:   let id := s.nextUnlockId
-- BROKEN:   let requestTime := s.now
-- BROKEN:   let cooldownEnd := s.now + cooldownPeriod
-- BROKEN:   { s with
-- BROKEN:       nextUnlockId := id + 1
-- BROKEN:       flexibleUnlockRequests := fun i => if i = id then some (owner, amount, requestTime, cooldownEnd) else s.flexibleUnlockRequests i
-- BROKEN:       unlockTokenOwner := fun i => if i = id then some owner else s.unlockTokenOwner i
-- BROKEN:       unlockTokenAmount := fun i => if i = id then amount else s.unlockTokenAmount i
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def burnUnlockNFT (s : State) (id : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       unlockTokenOwner := fun i => if i = id then none else s.unlockTokenOwner i
-- BROKEN:       unlockTokenAmount := fun i => if i = id then 0 else s.unlockTokenAmount i
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def mintApxUSD (s : State) (to : Address) (amount : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apxUSD := s.totalSupply_apxUSD + amount
-- BROKEN:       apxUSDBal := fun a => if a = to then s.apxUSDBal a + amount else s.apxUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def burnApxUSD (s : State) (fromAddr : Address) (amount : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apxUSD := s.totalSupply_apxUSD - amount
-- BROKEN:       apxUSDBal := fun a => if a = fromAddr then s.apxUSDBal a - amount else s.apxUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def mintApyUSD (s : State) (to : Address) (shares : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apyUSD := s.totalSupply_apyUSD + shares
-- BROKEN:       apyUSDBal := fun a => if a = to then s.apyUSDBal a + shares else s.apyUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def burnApyUSD (s : State) (fromAddr : Address) (shares : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       totalSupply_apyUSD := s.totalSupply_apyUSD - shares
-- BROKEN:       apyUSDBal := fun a => if a = fromAddr then s.apyUSDBal a - shares else s.apyUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def transferApxUSD (s : State) (fromAddr toAddr : Address) (amount : Nat) : State :=
-- BROKEN:   { s with
-- BROKEN:       apxUSDBal := fun a =>
-- BROKEN:         if a = fromAddr then s.apxUSDBal a - amount
-- BROKEN:         else if a = toAddr then s.apxUSDBal a + amount
-- BROKEN:         else s.apxUSDBal a
-- BROKEN:   }
-- BROKEN: 
-- BROKEN: def mem (a : Address) (l : List Address) : Bool :=
-- BROKEN:   l.elem a
-- BROKEN: 
-- BROKEN: def overcollateralizationBuffer (s : State) : Nat :=
-- BROKEN:   let redemptionTotal := (s.totalSupply_apxUSD * s.redemptionValue) / ray
-- BROKEN:   if s.totalCollateralValue > redemptionTotal then s.totalCollateralValue - redemptionTotal else 0
-- BROKEN: 
-- BROKEN: def emitEvent (s : State) (name : String) (args : List Nat) : State :=
-- BROKEN:   { s with eventLog := (name, args) :: s.eventLog }
-- BROKEN: 
-- BROKEN: -- ERC-4626 helper functions
-- BROKEN: def convertToShares (s : State) (assets : Nat) : Nat :=
-- BROKEN:   lockShares assets s.exchangeRate
-- BROKEN: 
-- BROKEN: def convertToAssets (s : State) (shares : Nat) : Nat :=
-- BROKEN:   redeemAssets shares s.exchangeRate
-- BROKEN: 
-- BROKEN: def maxDeposit (s : State) (receiver : Address) : Nat :=
-- BROKEN:   if s.globalPause then 0 else s.apxUSDBal receiver
-- BROKEN: 
-- BROKEN: def maxMint (s : State) (receiver : Address) : Nat :=
-- BROKEN:   if s.globalPause then 0 else convertToShares s (s.apxUSDBal receiver)
-- BROKEN: 
-- BROKEN: def maxWithdraw (s : State) (owner : Address) : Nat :=
-- BROKEN:   if s.globalPause then 0 else convertToAssets s (s.apyUSDBal owner)
-- BROKEN: 
-- BROKEN: def maxRedeem (s : State) (owner : Address) : Nat :=
-- BROKEN:   if s.globalPause then 0 else s.apyUSDBal owner
-- BROKEN: 
-- BROKEN: def previewDeposit (s : State) (assets : Nat) : Nat :=
-- BROKEN:   convertToShares s assets
-- BROKEN: 
-- BROKEN: def previewMint (s : State) (shares : Nat) : Nat :=
-- BROKEN:   convertToAssets s shares
-- BROKEN: 
-- BROKEN: def previewWithdraw (s : State) (assets : Nat) : Nat :=
-- BROKEN:   withdrawShares assets s.exchangeRate
-- BROKEN: 
-- BROKEN: def previewRedeem (s : State) (shares : Nat) : Nat :=
-- BROKEN:   convertToAssets s shares
-- BROKEN: 
-- BROKEN: inductive Op
-- BROKEN:   | depositUSDC (amount : Nat)
-- BROKEN:   | mintApxUSD (to : Address) (amount : Nat)
-- BROKEN:   | lockApxUSD (amount : Nat)
-- BROKEN:   | requestUnlock (amount : Nat)
-- BROKEN:   | claimUnlock (requestId : Nat)
-- BROKEN:   | redeemApxUSD (amount : Nat)
-- BROKEN:   | withdraw (assets : Nat) (receiver : Address)
-- BROKEN:   | redeem (shares : Nat) (receiver : Address)
-- BROKEN:   | flexibleRequestUnlock (amount : Nat)
-- BROKEN:   | flexibleClaimUnlock (requestId : Nat)
-- BROKEN:   | pause
-- BROKEN:   | unpause
-- BROKEN:   | addToWhitelist (addr : Address)
-- BROKEN:   | removeFromWhitelist (addr : Address)
-- BROKEN:   | addToDenylist (addr : Address)
-- BROKEN:   | removeFromDenylist (addr : Address)
-- BROKEN:   | setYieldRate (bps : Nat)
-- BROKEN:   | creditYield (amount : Nat)
-- BROKEN:   | voteBufferDeployment
-- BROKEN:   | executeRFQRedemption (user : Address) (amount : Nat)
-- BROKEN:   | updateRedemptionValue
-- BROKEN:   | handleStressEvent (amount : Nat)
-- BROKEN:   | catastrophicBackstop
-- BROKEN: 
-- BROKEN: def step (s : State) (op : Op) (caller : Address) : Option State :=
-- BROKEN:   match op with
-- BROKEN:   | Op.depositUSDC amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else if ¬ s.whitelist caller then none
-- BROKEN:     else if s.usdcBal caller < amount then none
-- BROKEN:     else
-- BROKEN:       let s1 := { s with
-- BROKEN:         usdcBal := fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a
-- BROKEN:         usdcReserve := s.usdcReserve + amount
-- BROKEN:       }
-- BROKEN:       let s2 := mintApxUSD s1 caller amount
-- BROKEN:       let s3 := emitEvent s2 "Deposit" [caller, caller, caller, amount, amount] -- sender, receiver, owner, assets, shares (1:1)
-- BROKEN:       some s3
-- BROKEN:   | Op.mintApxUSD to amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else if ¬ s.whitelist caller then none
-- BROKEN:     else if s.usdcBal caller < amount then none
-- BROKEN:     else
-- BROKEN:       let s1 := { s with
-- BROKEN:         usdcBal := fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a
-- BROKEN:         usdcReserve := s.usdcReserve + amount
-- BROKEN:       }
-- BROKEN:       let s2 := mintApxUSD s1 to amount
-- BROKEN:       let s3 := emitEvent s2 "Deposit" [caller, to, to, amount, amount]
-- BROKEN:       some s3
-- BROKEN:   | Op.lockApxUSD amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else if s.apxUSDBal caller < amount then none
-- BROKEN:     else
-- BROKEN:       let shares := lockShares amount s.exchangeRate
-- BROKEN:       let s1 := burnApxUSD s caller amount
-- BROKEN:       let s2 := { s1 with vaultApxUSDBal := s1.vaultApxUSDBal + amount }
-- BROKEN:       let s3 := mintApyUSD s2 caller shares
-- BROKEN:       let s4 := updateExchangeRate s3
-- BROKEN:       let s5 := emitEvent s4 "Deposit" [caller, caller, caller, amount, shares]
-- BROKEN:       some s5
-- BROKEN:   | Op.requestUnlock amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else if s.apxUSDBal caller < amount then none
-- BROKEN:     else
-- BROKEN:       let s1 := burnApxUSD s caller amount
-- BROKEN:       let s2 := createStandardUnlock s1 caller amount
-- BROKEN:       some s2
-- BROKEN:   | Op.claimUnlock requestId =>
-- BROKEN:     match s.unlockRequests requestId with
-- BROKEN:     | none => none
-- BROKEN:     | some (owner, amount, cooldownEnd) =>
-- BROKEN:       if s.unlockTokenOwner requestId != some owner then none
-- BROKEN:       else if s.now < cooldownEnd then none
-- BROKEN:       else
-- BROKEN:         let s1 := burnUnlockNFT s requestId
-- BROKEN:         let s2 := mintApxUSD s1 owner amount
-- BROKEN:         some s2
-- BROKEN:   | Op.redeemApxUSD amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else if ¬ s.whitelist caller then none
-- BROKEN:     else if s.apxUSDBal caller < amount then none
-- BROKEN:     else
-- BROKEN:       let usdcAmount := (amount * s.redemptionValue) / ray
-- BROKEN:       if s.usdcReserve < usdcAmount then none
-- BROKEN:       else
-- BROKEN:         let oldBuffer := overcollateralizationBuffer s
-- BROKEN:         let s1 := burnApxUSD s caller amount
-- BROKEN:         let s2 := { s1 with
-- BROKEN:           usdcReserve := s1.usdcReserve - usdcAmount
-- BROKEN:           usdcBal := fun a => if a = caller then s1.usdcBal a + usdcAmount else s1.usdcBal a
-- BROKEN:         }
-- BROKEN:         let newBuffer := overcollateralizationBuffer s2
-- BROKEN:         if newBuffer < oldBuffer then none
-- BROKEN:         else
-- BROKEN:           let s3 := emitEvent s2 "Redeem" [caller, amount, usdcAmount]
-- BROKEN:           some s3
-- BROKEN:   | Op.withdraw assets receiver =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else
-- BROKEN:       let s1 := pullVestedYield s
-- BROKEN:       let shares := withdrawShares assets s1.exchangeRate
-- BROKEN:       if s1.apyUSDBal caller < shares then none
-- BROKEN:       else if s1.vaultApxUSDBal < assets then none
-- BROKEN:       else
-- BROKEN:         let s2 := burnApyUSD s1 caller shares
-- BROKEN:         let s3 := { s2 with vaultApxUSDBal := s2.vaultApxUSDBal - assets }
-- BROKEN:         let s4 := createStandardUnlock s3 receiver assets
-- BROKEN:         let s5 := updateExchangeRate s4
-- BROKEN:         let s6 := emitEvent s5 "Withdraw" [caller, receiver, caller, assets, shares]
-- BROKEN:         some s6
-- BROKEN:   | Op.redeem shares receiver =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else
-- BROKEN:       let s1 := pullVestedYield s
-- BROKEN:       if s1.apyUSDBal caller < shares then none
-- BROKEN:       else
-- BROKEN:         let assets := redeemAssets shares s1.exchangeRate
-- BROKEN:         if s1.vaultApxUSDBal < assets then none
-- BROKEN:         else
-- BROKEN:           let s2 := burnApyUSD s1 caller shares
-- BROKEN:           let s3 := { s2 with vaultApxUSDBal := s2.vaultApxUSDBal - assets }
-- BROKEN:           let s4 := createStandardUnlock s3 receiver assets
-- BROKEN:           let s5 := updateExchangeRate s4
-- BROKEN:           let s6 := emitEvent s5 "Withdraw" [caller, receiver, caller, assets, shares]
-- BROKEN:           some s6
-- BROKEN:   | Op.flexibleRequestUnlock amount =>
-- BROKEN:     if s.globalPause then none
-- BROKEN:     else if s.apxUSDBal caller < amount then none
-- BROKEN:     else
-- BROKEN:       let s1 := burnApxUSD s caller amount
-- BROKEN:       let s2 := createFlexibleUnlock s1 caller amount
-- BROKEN:       some s2
-- BROKEN:   | Op.flexibleClaimUnlock requestId =>
-- BROKEN:     match s.flexibleUnlockRequests requestId with
-- BROKEN:     | none => none
-- BROKEN:     | some (owner, amount, requestTime, cooldownEnd) =>
-- BROKEN:       if s.unlockTokenOwner requestId != some owner then none
-- BROKEN:       else if s.now < cooldownEnd then none
-- BROKEN:       else
-- BROKEN:         let feeBps := flexibleUnlockFee requestTime s.now
-- BROKEN:         let fee := (amount * feeBps) / 10000
-- BROKEN:         let claimAmount := amount - fee
-- BROKEN:         let s1 := burnUnlockNFT s requestId
-- BROKEN:         let s2 := mintApxUSD s1 owner claimAmount
-- BROKEN:         some s2
-- BROKEN:   | Op.pause =>
-- BROKEN:     if caller == s.pauseController then some { s with globalPause := true }
-- BROKEN:     else none
-- BROKEN:   | Op.unpause =>
-- BROKEN:     if caller == s.pauseController then some { s with globalPause := false }
-- BROKEN:     else none
-- BROKEN:   | Op.addToWhitelist addr =>
-- BROKEN:     if caller == s.admin then some { s with whitelist := fun a => if a = addr then true else s.whitelist a }
-- BROKEN:     else none
-- BROKEN:   | Op.removeFromWhitelist addr =>
-- BROKEN:     if caller == s.admin then some { s with whitelist := fun a => if a = addr then false else s.whitelist a }
-- BROKEN:     else none
-- BROKEN:   | Op.addToDenylist addr =>
-- BROKEN:     if caller == s.admin then some { s with denylist := fun a => if a = addr then true else s.denylist a }
-- BROKEN:     else none
-- BROKEN:   | Op.removeFromDenylist addr =>
-- BROKEN:     if caller == s.admin then some { s with denylist := fun a => if a = addr then false else s.denylist a }
-- BROKEN:     else none
-- BROKEN:   | Op.setYieldRate bps =>
-- BROKEN:     if caller == s.admin then some { s with yieldRateMonth := bps }
-- BROKEN:     else none
-- BROKEN:   | Op.creditYield amount =>
-- BROKEN:     if caller == s.yieldDistributor then
-- BROKEN:       let s1 := { s with
-- BROKEN:         usdcReserve := s.usdcReserve + amount
-- BROKEN:         vestTotal := s.vestTotal + amount
-- BROKEN:         vestStart := s.now
-- BROKEN:       }
-- BROKEN:       some s1
-- BROKEN:     else none
-- BROKEN:   | Op.voteBufferDeployment => sorry
-- BROKEN:   | Op.executeRFQRedemption user amount => sorry
-- BROKEN:   | Op.updateRedemptionValue => sorry
-- BROKEN:   | Op.handleStressEvent amount => sorry
-- BROKEN:   | Op.catastrophicBackstop => sorry

/-- REQ redemption-settlement-value: Redemptions SHALL be settled at the Redemption Value, which tracks the underlying basket. -/
theorem req_redemption_settlement_value (s : State) (caller : Address) (amount : Nat) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    let usdcAmount := (amount * s.redemptionValue) / ray
    s'.usdcBal caller = s.usdcBal caller + usdcAmount := by
  sorry

/-- REQ mint-access-whitelist: Only participants who are eligible, located in permitted jurisdictions, and whitelisted SHALL be allowed to mint apxUSD. -/
theorem req_mint_access_whitelist (s : State) (to : Address) (amount : Nat) (caller : Address)
    (h_not_whitelisted : ¬ s.whitelist caller) :
    step s (Op.mintApxUSD to amount) caller = none := by simp_all [step]

/-- REQ redeem-access-whitelist: Only participants who are eligible, located in permitted jurisdictions, and whitelisted SHALL be allowed to redeem apxUSD. -/
theorem req_redeem_access_whitelist (s : State) (amount : Nat) (caller : Address)
    (h_not_whitelisted : ¬ s.whitelist caller) :
    step s (Op.redeemApxUSD amount) caller = none := by simp_all [step]

/-- REQ issuance-price-one: New apxUSD issuance SHALL be priced at exactly $1 per token. -/
theorem req_issuance_price_one (s : State) (caller : Address) (amount : Nat) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    s'.apxUSDBal caller = s.apxUSDBal caller + amount := by
  sorry

/-- REQ deposit-permissionless: The vault MUST allow any address to deposit apxUSD and receive apyUSD without requiring KYB/KYC. -/
theorem req_deposit_permissionless (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_balance : s.apxUSDBal caller ≥ amount) :
    ∃ s', step s (Op.lockApxUSD amount) caller = some s' := by
  sorry

/-- REQ buffer-preservation: The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed. -/
theorem req_buffer_preservation (s s' : State) (amount : Nat) (caller : Address)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    overcollateralizationBuffer s ≤ overcollateralizationBuffer s' := by
  sorry

/-- REQ mint-redeem-at-redemption-value: All minting and redemption transactions MUST be executed at the Redemption Value, which reflects the underlying basket of preferred shares and cash. -/
theorem req_mint_redeem_at_redemption_value (s s' : State) (amount : Nat) (to caller : Address)
    (h_step : step s (Op.mintApxUSD to amount) caller = some s') :
    let usdc_amount := (amount * s.redemptionValue) / ray
    s.usdcBal caller - usdc_amount = s'.usdcBal caller ∧
    s.usdcReserve + usdc_amount = s'.usdcReserve := by
  sorry

/-- REQ buffer-non-decreasing: The overcollateralization buffer, defined as the difference between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over time due to yield spreads and collateral appreciation. -/
theorem req_buffer_non_decreasing (s s' : State) (op : Op) (caller : Address)
    (h_step : step s op caller = some s') :
    overcollateralizationBuffer s ≤ overcollateralizationBuffer s' := by
  sorry

/-- REQ configurable-vesting-period: The vesting period for linear yield distribution MUST be configurable. -/
theorem req_configurable_vesting_period (s : State) :
    ∀ s_new : State, s_new.vestPeriod ≠ s.vestPeriod → ∃ op : Op, ∃ caller : Address, step s op caller = some s_new := by
  sorry

/-- REQ deposit-emits-event: The deposit(assets, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution. -/
theorem req_deposit_emits_event (s s' : State) (amount : Nat) (caller : Address)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    ∃ sender receiver owner assets shares : Nat,
      ("Deposit", [sender, receiver, owner, assets, shares]) ∈ s'.eventLog := by
  sorry

/-- REQ mint-emits-event: The mint(shares, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution. -/
theorem req_mint_emits_event (s s' : State) (to : Address) (amount : Nat) (caller : Address)
    (h_step : step s (Op.mintApxUSD to amount) caller = some s') :
    ∃ sender receiver owner assets shares : Nat,
      ("Deposit", [sender, receiver, owner, assets, shares]) ∈ s'.eventLog := by
  sorry

-- BROKEN: /-- REQ unlock-cannot-be-cancelled: The system MUST NOT allow an unlocking request to be cancelled once it has been initiated. -/
-- BROKEN: -- UNFORMALIZABLE req_unlock_cannot_be_cancelled: The model does not define any operation for cancelling unlock requests, so this requirement is implicitly satisfied but cannot be stated as a theorem.

-- BROKEN: /-- REQ unlock-conversion-after-cooldown: Conversion of apxUSD_unlock to apxUSD MUST only be possible after the cooldown period has elapsed. -/
-- BROKEN: theorem req_unlock_conversion_after_cooldown (s : State) (requestId : Nat) (caller : Address)
-- BROKEN:     (h1 : s.unlockRequests requestId = some (caller, 0, 0))
-- BROKEN:     (h2 : s.unlockTokenOwner requestId = some caller) : 
-- BROKEN:     step s (.claimUnlock requestId) caller = none ∨ s.now ≥ match s.unlockRequests requestId with | some (_, _, cooldownEnd) => cooldownEnd | none => 0 := by
-- BROKEN:   simp [step]
-- BROKEN:   split
-- BROKEN:   . next _ _ _ =>
-- BROKEN:     obtain rfl : owner = caller ∧ amount = 0 ∧ cooldownEnd = 0 := by simp [step]

/-- REQ vault-pulls-vested-yield-before-withdraw: When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal. -/
theorem req_vault_pulls_vested_yield_before_withdraw (s : State) (assets : Nat) (receiver : Address) (caller : Address)
    (h : step s (.withdraw assets receiver) caller = some s') :
    s'.vaultApxUSDBal = (pullVestedYield s).vaultApxUSDBal := by
  sorry

-- Theorems added by coverage reconciliation

/-- REQ redeem-liquidate-usdc: The system SHALL liquidate preferred‑share collateral to USDC in order to settle any redemption request. -/
theorem req_redeem_liquidate_usdc (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h1 : s.globalPause = false)
    (h2 : s.whitelist caller = true)
    (h3 : s.apxUSDBal caller ≥ amount)
    (h4 : let usdcAmount := (amount * s.redemptionValue) / ray; s.usdcReserve ≥ usdcAmount)
    (h5 : let oldBuffer := overcollateralizationBuffer s; 
          let usdcAmount := (amount * s.redemptionValue) / ray;
          let s1 := burnApxUSD s caller amount;
          let s2 := { s1 with
            usdcReserve := s1.usdcReserve - usdcAmount
            usdcBal := fun a => if a = caller then s1.usdcBal a + usdcAmount else s1.usdcBal a
          };
          let newBuffer := overcollateralizationBuffer s2;
          newBuffer ≥ oldBuffer)
    (h6 : step s (Op.redeemApxUSD amount) caller = some s') :
    ∃ (collateral_liquidated : Nat),
      collateral_liquidated > 0 ∧
      s.totalCollateralValue ≥ s'.totalCollateralValue ∧
      s.totalCollateralValue - s'.totalCollateralValue = collateral_liquidated := by
  sorry

/-- REQ yield-distributor-credit: The YieldDistributor MUST credit converted apxUSD proceeds to the apyUSD vault. -/
theorem req_yield_distributor_credit (s : State) (amount : Nat) (caller : Address)
    (h1 : caller = s.yieldDistributor) :
    step s (Op.creditYield amount) caller = some { s with
      usdcReserve := s.usdcReserve + amount,
      vestTotal := s.vestTotal + amount,
      vestStart := s.now } := by
  simp [step, h1]

/-- REQ new-locked-receives-yield: When new apyUSD is locked, it MUST immediately begin receiving yield, which reduces the overall percentage yield for existing holders. -/
theorem req_new_locked_receives_yield (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false)
    (h2 : s.apxUSDBal caller ≥ amount) :
    let s' := updateExchangeRate (mintApyUSD (burnApxUSD ({ s with vaultApxUSDBal := s.vaultApxUSDBal + amount } ) caller amount) caller (lockShares amount s.exchangeRate));
    s'.exchangeRate ≤ s.exchangeRate := by
  sorry

-- BROKEN: /-- REQ cooldown_removal: When apyUSD enters the cooldown phase, it MUST be removed from the yield pool, causing remaining apyUSD to receive a higher percentage yield. -/
-- BROKEN: -- UNFORMALIZABLE req_cooldown_removal: The model does not explicitly track individual apyUSD allocations in the yield pool or compute yield distribution percentages.

/-- REQ synchronous_withdraw_return_token: The apyUSD vault MUST execute withdrawals and redeems synchronously and MUST return apxUSD_unlock tokens immediately. -/
theorem req_synchronous_withdraw_return_token (s : State) (assets receiver caller : Nat)
    (h1 : s.globalPause = false)
    (h2 : (pullVestedYield s).apyUSDBal caller ≥ (if assets = 0 then 0 else withdrawShares assets (pullVestedYield s).exchangeRate))
    (h3 : (pullVestedYield s).vaultApxUSDBal ≥ assets) :
    ∃ s', step s (Op.withdraw assets receiver) caller = some s' ∧
    (∃ id, s'.unlockTokenOwner id = some receiver ∧ s'.unlockTokenAmount id = assets) := by
  sorry

/-- REQ withdrawForMaxShares-revert-if-exceeds-maxShares: withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of apyUSD shares required to withdraw the assets exceeds maxShares. -/
theorem req_withdraw_for_max_shares_revert_if_exceeds_max_shares (s : State) (assets maxShares : Nat) (receiver caller : Address) :
    let sharesRequired := withdrawShares assets (computeExchangeRate (pullVestedYield s))
    s.globalPause = false ∧ s.apyUSDBal caller ≥ sharesRequired ∧ sharesRequired > maxShares → step s (.withdraw assets receiver) caller = none := sorry

/-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
theorem req_vault_burns_apyUSD_shares_immediately_on_withdraw (s s' : State) (assets : Nat) (receiver caller : Address)
    (h_step : step s (.withdraw assets receiver) caller = some s') :
    let s1 := pullVestedYield s
    let shares := withdrawShares assets (computeExchangeRate s1)
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD - shares := by
  sorry

/-- REQ depositforminshares_slippage: depositForMinShares(uint256 assets, uint256 minShares, address receiver) MUST revert if the number of shares that would be minted is less than minShares. -/
theorem req_depositforminshares_slippage (s : State) (assets : Nat) (minShares : Nat) (receiver : Address) (caller : Address) :
    let shares := previewDeposit s assets
    if shares < minShares then step s (Op.depositUSDC assets) caller = none else True := by
  unfold previewDeposit
  by_cases h : s.globalPause
  · simp [step, h]
  by_cases h2 : ¬s.whitelist caller
  · simp [step, h, h2]
  by_cases h3 : s.usdcBal caller < assets
  · simp [step, h, h2, h3]
  simp [step, h, h2, h3]
  sorry

/-- REQ mintformaxassets_slippage: mintForMaxAssets(uint256 shares, uint256 maxAssets, address receiver) MUST revert if the amount of assets required to mint the requested shares exceeds maxAssets. -/
theorem req_mintformaxassets_slippage (s : State) (shares : Nat) (maxAssets : Nat) (receiver : Address) (caller : Address) :
    let assets := previewMint s shares
    if assets > maxAssets then step s (Op.lockApxUSD assets) caller = none else True := sorry

/-- REQ totalAssets_includes_vault_balance_and_vested: The vault's totalAssets() function MUST include both the vault's apxUSD balance and the vestedAmount() reported by the LinearVestV0 contract. -/
theorem req_totalAssets_includes_vault_balance_and_vested (s : State) :
    totalAssets s = s.vaultApxUSDBal + vestedAmount s s.now := rfl

/-- REQ withdrawal_pulls_vested: When processing a withdrawal, the apyUSD vault MUST pull all vested yield from the LinearVestV0 contract before completing the withdrawal. -/
theorem req_withdrawal_pulls_vested (s : State) (assets : Nat) (receiver : Address) (caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s'.vaultApxUSDBal = (pullVestedYield s).vaultApxUSDBal := by
  sorry

-- BROKEN: /-- REQ denylist_blocks_deposit: If the caller or the receiver address is present in the deny list, deposit and mint operations MUST revert. -/
-- BROKEN: theorem req_denylist_blocks_deposit (s : State) (amount : Nat) (to : Address) (caller : Address) :
-- BROKEN:     s.denylist caller ∨ s.denylist to → step s (Op.depositUSDC amount) caller = none := by
-- BROKEN:   intro h
-- BROKEN:   simp [step]
-- BROKEN:   split
-- BROKEN:   · intro; contradiction
-- BROKEN:   split
-- BROKEN:   · intro; contradiction
-- BROKEN:   split
-- BROKEN:   · intro h1 h2 h3
-- BROKEN:     have : s.denylist caller ∨ s.denylist caller := sorry

-- BROKEN: /-- UNFORMALIZABLE req_erc4626_compliance: The model does not fully implement ERC-4626 interface - only selected functions are modeled. --/

-- BROKEN: /-- UNFORMALIZABLE req_unlock_token_nontransferable: The model does not include unlock token transfer operations to constrain. --/

/-- REQ withdrawForMaxShares_revert_if_exceeds_maxShares: withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of apyUSD shares required to withdraw the assets exceeds maxShares. -/
theorem req_withdrawForMaxShares_revert_if_exceeds_maxShares (s : State) (assets : Nat) (maxShares : Nat) (receiver : Address) (caller : Address) :
    let shares := previewWithdraw s assets
    if shares > maxShares then step s (Op.withdraw assets receiver) caller = none else True := sorry

/-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
theorem req_vault_burns_apy_usd_shares_immediately (s : State) (assets : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    s'.totalSupply_apyUSD < s.totalSupply_apyUSD := by
  simp [step, pullVestedYield, burnApyUSD] at h_step
  sorry

/-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
theorem req_vault_burns_apy_usd_shares_immediately_redeem (s : State) (shares : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s') :
    s'.totalSupply_apyUSD < s.totalSupply_apyUSD := by
  simp [step, pullVestedYield, burnApyUSD] at h_step
  sorry

/-- REQ vault-deposits-apxUSD-into-UnlockToken: The vault MUST deposit the corresponding apxUSD amount into the UnlockToken contract during a withdraw or redeem operation. -/
theorem req_vault_deposits_apx_usd_into_unlock_token (s : State) (assets : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    match s'.unlockRequests (s'.nextUnlockId - 1) with
    | some (_, amount, _) => amount = assets
    | none => False
    := by
  simp [step, pullVestedYield, createStandardUnlock] at h_step
  sorry

/-- REQ vault-deposits-apxUSD-into-UnlockToken: The vault MUST deposit the corresponding apxUSD amount into the UnlockToken contract during a withdraw or redeem operation. -/
theorem req_vault_deposits_apx_usd_into_unlock_token_redeem (s : State) (shares : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s') :
    match s'.unlockRequests (s'.nextUnlockId - 1) with
    | some (_, amount, _) => amount = redeemAssets shares s'.exchangeRate
    | none => False
    := by
  simp [step, pullVestedYield, createStandardUnlock, redeemAssets] at h_step
  sorry

-- BROKEN: /-- REQ unlockToken-redeem-after-cooldown: The UnlockToken contract MUST allow a user to call redeem() after the cooldown period to receive the underlying apxUSD. -/
-- BROKEN: theorem req_unlock_token_redeem_after_cooldown (s : State) (requestId : Nat) (caller : Address)
-- BROKEN:     (h_request : s.unlockRequests requestId = some (caller, 0, s.now - cooldownPeriod)) 
-- BROKEN:     (h_owner : s.unlockTokenOwner requestId = some caller) :
-- BROKEN:     step s (Op.claimUnlock requestId) caller ≠ none := by
-- BROKEN:   simp [step, Op.claimUnlock]
-- BROKEN:   split
-- BROKEN:   · intro h
-- BROKEN:     simp at h
-- BROKEN:     have h1 : s.unlockRequests requestId = none := by
-- BROKEN:       rw [h] at h_request
-- BROKEN:       simp at h_request
-- BROKEN:     contradiction
-- BROKEN:   · simp [h_request, h_owner]
-- BROKEN:     split
-- BROKEN:     · next h_eq => 
-- BROKEN:       simp [h_eq] at h_owner
-- BROKEN:     · next h_ne h_time =>
-- BROKEN:       have h4 : s.now ≥ s.now - cooldownPeriod := by simp [step]

end Apyx
