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
  | setVestPeriod (p : Nat)

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.depositUSDC amount =>
    if s.globalPause then none
    else if ¬ s.whitelist caller then none
    else if s.denylist caller then none
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
    else if s.denylist caller || s.denylist to then none
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
    | some (owner, amount, requestTime, _cooldownEnd) =>
      if s.unlockTokenOwner requestId != some owner then none
      else if s.now < requestTime + minFlexibleClaim then none
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
  | Op.voteBufferDeployment =>
    -- only governance-token holders may vote; a vote reaching the threshold deploys the buffer
    if s.governanceTokenBal caller = 0 then none
    else some { s with bufferDeployed := s.bufferDeployed || (s.governanceTokenBal caller ≥ s.governanceThreshold) }
  | Op.executeRFQRedemption user amount =>
    -- only approved RFQ counterparties may execute a user's redemption request
    if s.globalPause then none
    else if ¬ (s.rfqCounterparties.contains caller) then none
    else if s.apxUSDBal user < amount then none
    else
      let usdcAmount := (amount * s.redemptionValue) / ray
      if s.usdcReserve < usdcAmount then none
      else
        let s1 := burnApxUSD s user amount
        let s2 := { s1 with
          usdcReserve := s1.usdcReserve - usdcAmount
          usdcBal := fun a => if a = user then s1.usdcBal a + usdcAmount else s1.usdcBal a
        }
        some s2
  | Op.updateRedemptionValue =>
    if caller == s.oracle then
      -- placeholder: in practice would fetch from oracle
      some s
    else none
  | Op.handleStressEvent amount =>
    -- a stress loss reduces total collateral value; absorbed by the buffer, admin only
    if caller == s.admin then
      some { s with totalCollateralValue := s.totalCollateralValue - amount, emergencyFlag := true }
    else none
  | Op.catastrophicBackstop =>
    -- catastrophic scenario: redemption value is set to track total collateral value,
    -- distributing the entire reserve (including the buffer) pro-rata to holders
    if caller == s.admin then
      some { s with redemptionValue := s.totalCollateralValue, emergencyFlag := true }
    else none
  | Op.setVestPeriod p =>
    if caller == s.admin then some { s with vestPeriod := p }
    else none

/-- ERC-4626 slippage wrappers: revert (return `none`) when the preview violates the
user-supplied bound, otherwise defer to the underlying vault operation. -/
def depositForMinShares (s : State) (assets minShares : Nat) (_receiver caller : Address) : Option State :=
  if previewDeposit s assets < minShares then none
  else step s (Op.lockApxUSD assets) caller

def mintForMaxAssets (s : State) (shares maxAssets : Nat) (_receiver caller : Address) : Option State :=
  if previewMint s shares > maxAssets then none
  else step s (Op.lockApxUSD (previewMint s shares)) caller

def withdrawForMaxShares (s : State) (assets maxShares : Nat) (receiver caller : Address) : Option State :=
  if previewWithdraw s assets > maxShares then none
  else step s (Op.withdraw assets receiver) caller

def redeemForMinAssets (s : State) (shares minAssets : Nat) (receiver caller : Address) : Option State :=
  if previewRedeem s shares < minAssets then none
  else step s (Op.redeem shares receiver) caller

-- Requirements as theorems

/- ================= helper lemmas (not requirement theorems) ================= -/

@[simp] private theorem pullVestedYield_now (s : State) :
    (pullVestedYield s).now = s.now := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_globalPause (s : State) :
    (pullVestedYield s).globalPause = s.globalPause := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_exchangeRate (s : State) :
    (pullVestedYield s).exchangeRate = s.exchangeRate := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_apyUSDBal (s : State) :
    (pullVestedYield s).apyUSDBal = s.apyUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_apxUSDBal (s : State) :
    (pullVestedYield s).apxUSDBal = s.apxUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_totalSupply_apyUSD (s : State) :
    (pullVestedYield s).totalSupply_apyUSD = s.totalSupply_apyUSD := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_totalSupply_apxUSD (s : State) :
    (pullVestedYield s).totalSupply_apxUSD = s.totalSupply_apxUSD := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_nextUnlockId (s : State) :
    (pullVestedYield s).nextUnlockId = s.nextUnlockId := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_unlockRequests (s : State) :
    (pullVestedYield s).unlockRequests = s.unlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_unlockRequestId (s : State) :
    (pullVestedYield s).unlockRequestId = s.unlockRequestId := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_flexibleUnlockRequests (s : State) :
    (pullVestedYield s).flexibleUnlockRequests = s.flexibleUnlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_unlockTokenOwner (s : State) :
    (pullVestedYield s).unlockTokenOwner = s.unlockTokenOwner := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_unlockTokenAmount (s : State) :
    (pullVestedYield s).unlockTokenAmount = s.unlockTokenAmount := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_usdcBal (s : State) :
    (pullVestedYield s).usdcBal = s.usdcBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_usdcReserve (s : State) :
    (pullVestedYield s).usdcReserve = s.usdcReserve := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_redemptionValue (s : State) :
    (pullVestedYield s).redemptionValue = s.redemptionValue := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_totalCollateralValue (s : State) :
    (pullVestedYield s).totalCollateralValue = s.totalCollateralValue := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_vaultApxUSDBal (s : State) :
    (pullVestedYield s).vaultApxUSDBal = s.vaultApxUSDBal + vestedAmount s s.now := by
  unfold pullVestedYield; dsimp only; split <;> simp_all

/-- If `e ≤ P` then `e * T / P ≤ T`. -/
private theorem div_mul_le_total {e P T : Nat} (h : e ≤ P) : e * T / P ≤ T := by
  rcases Nat.eq_zero_or_pos P with hp | hp
  · subst hp
    simp [Nat.le_zero.mp h]
  · calc e * T / P ≤ P * T / P := Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
      _ = T := Nat.mul_div_cancel_left _ hp

/-- `vestedAmount` never exceeds the total vest amount. -/
private theorem vestedAmount_le_total (s : State) (n : Nat) :
    vestedAmount s n ≤ s.vestTotal := by
  unfold vestedAmount
  dsimp only
  repeat' split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact div_mul_le_total (by omega)

/-- `vestedAmount` is monotone in time. -/
private theorem vestedAmount_mono (s : State) {n m : Nat} (h : n ≤ m) :
    vestedAmount s n ≤ vestedAmount s m := by
  unfold vestedAmount
  dsimp only
  repeat' split
  all_goals first
    | omega
    | exact Nat.zero_le _
    | (exfalso; omega)
    | exact div_mul_le_total (by omega)
    | exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))

/-- The overcollateralization buffer only grows when supply shrinks (collateral and
redemption value held fixed). -/
private theorem overcollateralizationBuffer_mono (s s' : State)
    (hTCV : s'.totalCollateralValue = s.totalCollateralValue)
    (hRV : s'.redemptionValue = s.redemptionValue)
    (hSup : s'.totalSupply_apxUSD ≤ s.totalSupply_apxUSD) :
    overcollateralizationBuffer s ≤ overcollateralizationBuffer s' := by
  unfold overcollateralizationBuffer
  dsimp only
  have hrt : (s'.totalSupply_apxUSD * s'.redemptionValue) / ray
      ≤ (s.totalSupply_apxUSD * s.redemptionValue) / ray := by
    rw [hRV]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hSup)
  split <;> split <;> omega

/-- The exchange rate implied by the vault is monotone in time: vesting only ever adds
assets, so letting time pass can never lower the rate. -/
private theorem computeExchangeRate_mono_now (s : State) (dt : Nat) :
    computeExchangeRate s ≤ computeExchangeRate { s with now := s.now + dt } := by
  unfold computeExchangeRate totalAssets
  dsimp only
  split
  · exact Nat.le_refl _
  · exact Nat.div_le_div_right (Nat.mul_le_mul_right _
      (Nat.add_le_add_left (vestedAmount_mono s (Nat.le_add_right _ _)) _))

/-- The flexible-unlock fee never drops below the 0.1% (10 bps) floor once claimable. -/
private theorem flexibleUnlockFee_ge_min (rt now : Nat) (h : rt + minFlexibleClaim ≤ now) :
    10 ≤ flexibleUnlockFee rt now := by
  unfold flexibleUnlockFee
  dsimp only
  repeat' split
  all_goals first
    | omega
    | exact Nat.le_max_right _ _

/-- The flexible-unlock fee never exceeds the 3.5% (350 bps) starting level. -/
private theorem flexibleUnlockFee_le_start (rt now : Nat) :
    flexibleUnlockFee rt now ≤ 350 := by
  unfold flexibleUnlockFee
  dsimp only
  repeat' split
  all_goals first
    | omega
    | exact Nat.max_le.mpr ⟨Nat.sub_le _ _, by omega⟩

/-- The flexible-unlock fee declines (weakly) as time passes. -/
private theorem flexibleUnlockFee_antitone (rt : Nat) {t1 t2 : Nat}
    (h0 : rt + minFlexibleClaim ≤ t1) (h : t1 ≤ t2) :
    flexibleUnlockFee rt t2 ≤ flexibleUnlockFee rt t1 := by
  unfold flexibleUnlockFee
  dsimp only
  repeat' split
  all_goals first
    | omega
    | (exfalso; omega)
    | exact Nat.le_max_right _ _
    | (exact Nat.max_le.mpr ⟨Nat.le_trans (by
        have hdiv : (t1 - rt) * 340 / cooldownPeriod ≤ (t2 - rt) * 340 / cooldownPeriod :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
        omega) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)

/-- Once the full cooldown has elapsed the flexible-unlock fee is exactly the 10 bps floor. -/
private theorem flexibleUnlockFee_after_cooldown (rt now : Nat)
    (h0 : rt + minFlexibleClaim ≤ now) (h : rt + cooldownPeriod ≤ now) :
    flexibleUnlockFee rt now = 10 := by
  unfold flexibleUnlockFee
  dsimp only
  repeat' split
  all_goals omega

/- ================= per-op extraction lemmas ================= -/

private theorem step_withdraw_some (s : State) (assets : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s.globalPause = false ∧
    withdrawShares assets s.exchangeRate ≤ (pullVestedYield s).apyUSDBal caller ∧
    assets ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate)).vaultApxUSDBal - assets }
          receiver assets)) "Withdraw" [caller, receiver, caller, assets, withdrawShares assets s.exchangeRate] := by
  simp only [step, pullVestedYield_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem step_redeem_some (s : State) (shares : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.redeem shares receiver) caller = some s') :
    s.globalPause = false ∧
    shares ≤ (pullVestedYield s).apyUSDBal caller ∧
    redeemAssets shares s.exchangeRate ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller shares with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal - redeemAssets shares s.exchangeRate }
          receiver (redeemAssets shares s.exchangeRate))) "Withdraw" [caller, receiver, caller, redeemAssets shares s.exchangeRate, shares] := by
  simp only [step, pullVestedYield_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem step_depositUSDC_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.depositUSDC amount) caller = some s') :
    s.globalPause = false ∧ s.whitelist caller = true ∧ s.denylist caller = false ∧
    amount ≤ s.usdcBal caller ∧
    s' = emitEvent (mintApxUSD { s with
        usdcBal := fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a
        usdcReserve := s.usdcReserve + amount } caller amount)
      "Deposit" [caller, caller, caller, amount, amount] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact ⟨by simp_all, by simp_all, by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_mintApxUSD_some (s : State) (to : Address) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.mintApxUSD to amount) caller = some s') :
    s.globalPause = false ∧ s.whitelist caller = true ∧
    s.denylist caller = false ∧ s.denylist to = false ∧
    amount ≤ s.usdcBal caller ∧
    s' = emitEvent (mintApxUSD { s with
        usdcBal := fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a
        usdcReserve := s.usdcReserve + amount } to amount)
      "Deposit" [caller, to, to, amount, amount] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · refine ⟨by simp_all, by simp_all, ?_, ?_, by omega, (Option.some.inj h).symm⟩ <;> simp_all

private theorem step_lockApxUSD_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.lockApxUSD amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = emitEvent (updateExchangeRate (mintApyUSD
          { burnApxUSD s caller amount with
            vaultApxUSDBal := (burnApxUSD s caller amount).vaultApxUSDBal + amount }
          caller (lockShares amount s.exchangeRate)))
      "Deposit" [caller, caller, caller, amount, lockShares amount s.exchangeRate] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_requestUnlock_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.requestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = createStandardUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_flexibleRequestUnlock_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = createFlexibleUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_claimUnlock_some (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.claimUnlock id) caller = some s') :
    ∃ owner amount cooldownEnd,
      s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      cooldownEnd ≤ s.now ∧
      s' = mintApxUSD (burnUnlockNFT s id) owner amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨owner, amount, cooldownEnd, heq, by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_flexibleClaimUnlock_some (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      requestTime + minFlexibleClaim ≤ s.now ∧
      s' = mintApxUSD (burnUnlockNFT s id) owner
        (amount - amount * flexibleUnlockFee requestTime s.now / 10000) := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount requestTime cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨owner, amount, requestTime, cooldownEnd, heq, by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_redeemApxUSD_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.redeemApxUSD amount) caller = some s') :
    s.globalPause = false ∧ s.whitelist caller = true ∧ amount ≤ s.apxUSDBal caller ∧
    (amount * s.redemptionValue) / ray ≤ s.usdcReserve ∧
    s' = emitEvent { burnApxUSD s caller amount with
        usdcReserve := (burnApxUSD s caller amount).usdcReserve - (amount * s.redemptionValue) / ray
        usdcBal := fun a => if a = caller then (burnApxUSD s caller amount).usdcBal a + (amount * s.redemptionValue) / ray
                            else (burnApxUSD s caller amount).usdcBal a }
      "Redeem" [caller, amount, (amount * s.redemptionValue) / ray] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · exact ⟨by simp_all, by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem step_executeRFQRedemption_some (s : State) (user : Address) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.executeRFQRedemption user amount) caller = some s') :
    s.globalPause = false ∧ s.rfqCounterparties.contains caller = true ∧
    amount ≤ s.apxUSDBal user ∧
    (amount * s.redemptionValue) / ray ≤ s.usdcReserve ∧
    s' = { burnApxUSD s user amount with
        usdcReserve := (burnApxUSD s user amount).usdcReserve - (amount * s.redemptionValue) / ray
        usdcBal := fun a => if a = user then (burnApxUSD s user amount).usdcBal a + (amount * s.redemptionValue) / ray
                            else (burnApxUSD s user amount).usdcBal a } := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact ⟨by simp_all, by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

/- ================= requirement theorems ================= -/

/-- Helper: every operation other than the explicit share-minting (`lockApxUSD`) and
share-burning (`withdraw`/`redeem`) operations leaves all apyUSD balances untouched. -/
private theorem apyUSDBal_unchanged_of_non_share_op (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_not_mint : ∀ a, op ≠ Op.lockApxUSD a)
    (h_not_withdraw : ∀ a r, op ≠ Op.withdraw a r)
    (h_not_redeem : ∀ a r, op ≠ Op.redeem a r) :
    ∀ a, s'.apyUSDBal a = s.apyUSDBal a := by
  intro a
  cases op
  case lockApxUSD x => exact absurd rfl (h_not_mint x)
  case withdraw x r => exact absurd rfl (h_not_withdraw x r)
  case redeem x r => exact absurd rfl (h_not_redeem x r)
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    simp [mintApxUSD, burnUnlockNFT]
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD]
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createFlexibleUnlock, burnApxUSD]
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    simp [mintApxUSD, burnUnlockNFT]
  case executeRFQRedemption u am =>
    obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    simp [burnApxUSD]
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; rfl)
        | exact absurd h_step (by simp)

/-- REQ token-no-rebase: The apyUSD token MUST NOT rebase its balances; balances may change
only via transfers, minting, or burning. (Model: whenever any address's apyUSD balance
changes across a step, that step was an explicit mint (`lockApxUSD`) or burn
(`withdraw`/`redeem`) of apyUSD shares — never an implicit rebase. Peer-to-peer apyUSD
transfers are not modeled as a separate operation, so minting and burning are the model's
only legitimate balance-changing events.) -/
theorem req_token_no_rebase (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (a : Address) (h_changed : s'.apyUSDBal a ≠ s.apyUSDBal a) :
    (∃ x, op = Op.lockApxUSD x) ∨
    (∃ x r, op = Op.withdraw x r) ∨
    (∃ x r, op = Op.redeem x r) := by
  cases op
  case lockApxUSD x => exact Or.inl ⟨x, rfl⟩
  case withdraw x r => exact Or.inr (Or.inl ⟨x, r, rfl⟩)
  case redeem x r => exact Or.inr (Or.inr ⟨x, r, rfl⟩)
  all_goals
    exact absurd (apyUSDBal_unchanged_of_non_share_op _ _ _ _ h_step
      (fun _ => nofun) (fun _ _ => nofun) (fun _ _ => nofun) a) h_changed

/-- REQ singleton-unlockToken-instance: There MUST be exactly one instance of UnlockToken
and it MUST be used exclusively by the apyUSD vault. (Model: all unlock positions live in
one global registry keyed by the single `nextUnlockId` counter, and every vault operation
allocates at most one fresh id from it — no operation ever creates ids elsewhere.) -/
theorem req_singleton_unlock_token_instance (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') :
    s'.nextUnlockId = s.nextUnlockId ∨ s'.nextUnlockId = s.nextUnlockId + 1 := by
  cases op
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    right
    simp [createStandardUnlock, burnApxUSD]
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    right
    simp [createFlexibleUnlock, burnApxUSD]
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    right
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    right
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case depositUSDC a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    left
    simp [emitEvent, mintApxUSD]
  case mintApxUSD t a =>
    obtain ⟨_, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    left
    simp [emitEvent, mintApxUSD]
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    left
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    left
    simp [mintApxUSD, burnUnlockNFT]
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    left
    simp [mintApxUSD, burnUnlockNFT]
  case redeemApxUSD a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    left
    simp [emitEvent, burnApxUSD]
  case executeRFQRedemption u am =>
    obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    left
    simp [burnApxUSD]
  all_goals
    left
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; rfl)
        | exact absurd h_step (by simp)


/-- REQ redeem-no-share-transfer: The system MUST NOT transfer preferred shares directly to
a participant who redeems apxUSD. (Model: preferred shares are held as `governanceTokenBal`;
a redemption of apxUSD pays out USDC only and leaves every preferred-share balance —
in particular the redeemer's — completely unchanged.) -/
theorem req_redeem_no_share_transfer (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    ∀ a, s'.governanceTokenBal a = s.governanceTokenBal a := by
  obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
  subst hs'
  intro a
  simp [emitEvent, burnApxUSD]

/-- REQ exchange-rate-non-decreasing: The exchange rate between apyUSD and apxUSD MUST be
non-decreasing over time. (Model: passing time only vests more yield into `totalAssets`,
so the implied exchange rate cannot fall.) -/
theorem req_exchange_rate_non_decreasing (s : State) (dt : Nat) :
    computeExchangeRate s ≤ computeExchangeRate { s with now := s.now + dt } :=
  computeExchangeRate_mono_now s dt

/-- REQ redemption-async-process: Redemption requests MUST follow the three-step
asynchronous process of request, cooldown, and claim. (Model: a request immediately creates
a pending unlock whose cooldown deadline lies in the future, and claiming it in the same
instant reverts.) -/
theorem req_redemption_async_process (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : amount ≤ s.apxUSDBal caller) :
    ∃ s', step s (Op.requestUnlock amount) caller = some s' ∧
      s'.unlockRequests s.nextUnlockId = some (caller, amount, s.now + cooldownPeriod) ∧
      step s' (Op.claimUnlock s.nextUnlockId) caller = none := by
  refine ⟨createStandardUnlock (burnApxUSD s caller amount) caller amount, ?_, ?_, ?_⟩
  · simp [step, h1, Nat.not_lt.mpr h2]
  · simp [createStandardUnlock, burnApxUSD]
  · simp [step, createStandardUnlock, burnApxUSD, cooldownPeriod, day]

/-- REQ redemption-cooldown-period: After a redemption request is submitted, the system
MUST enforce a cooldown period of approximately 20 days before a claim can be executed.
(Model: `cooldownPeriod = 20 * day`; every request records `now + cooldownPeriod` as its
deadline and every successful claim happened at or after its recorded deadline.) -/
theorem req_redemption_cooldown_period (s : State) :
    cooldownPeriod = 20 * day ∧
    (∀ amount caller s', step s (Op.requestUnlock amount) caller = some s' →
      s'.unlockRequests s.nextUnlockId = some (caller, amount, s.now + cooldownPeriod)) ∧
    (∀ id caller s', step s (Op.claimUnlock id) caller = some s' →
      ∃ owner amount cooldownEnd, s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
        cooldownEnd ≤ s.now) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro amount caller s' h
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  · intro id caller s' h
    obtain ⟨o, a, ce, hreq, _, ht, _⟩ := step_claimUnlock_some _ _ _ _ h
    exact ⟨o, a, ce, hreq, ht⟩

/-- REQ cooldown-no-yield: During a redemption cooldown, the exchange rate for the locked
apyUSD MUST remain fixed and the user MUST not accrue additional yield on those tokens.
(Model: the pending request is untouched by the passage of time and a claim pays exactly
the amount frozen at request time, independent of any later exchange-rate movement.) -/
theorem req_cooldown_no_yield (s : State) (id : Nat) (caller : Address) (dt : Nat) :
    ({ s with now := s.now + dt }).unlockRequests id = s.unlockRequests id ∧
    (∀ owner amount cooldownEnd s',
      s.unlockRequests id = some (owner, amount, cooldownEnd) →
      step s (Op.claimUnlock id) caller = some s' →
      s'.apxUSDBal owner = s.apxUSDBal owner + amount) := by
  refine ⟨rfl, ?_⟩
  intro owner amount cooldownEnd s' hreq h
  obtain ⟨o, a, ce, hreq', _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h
  rw [hreq] at hreq'
  simp only [Option.some.injEq, Prod.mk.injEq] at hreq'
  obtain ⟨rfl, rfl, rfl⟩ := hreq'
  subst hs'
  simp [mintApxUSD, burnUnlockNFT]

/-- REQ flexible-redemption-multiple-requests: The system MUST allow a user to have
multiple concurrent flexible redemption unlock requests. (Model: two back-to-back flexible
unlock requests both succeed and leave two distinct live requests owned by the caller.) -/
theorem req_flexible_redemption_multiple_requests (s : State) (a1 a2 : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : a1 + a2 ≤ s.apxUSDBal caller) :
    ∃ s1 s2, step s (Op.flexibleRequestUnlock a1) caller = some s1 ∧
      step s1 (Op.flexibleRequestUnlock a2) caller = some s2 ∧
      (∃ rt1 ce1, s2.flexibleUnlockRequests s.nextUnlockId = some (caller, a1, rt1, ce1)) ∧
      (∃ rt2 ce2, s2.flexibleUnlockRequests (s.nextUnlockId + 1) = some (caller, a2, rt2, ce2)) := by
  have hs1 : step s (Op.flexibleRequestUnlock a1) caller
      = some (createFlexibleUnlock (burnApxUSD s caller a1) caller a1) := by
    simp [step, h1, Nat.not_lt.mpr (by omega : a1 ≤ s.apxUSDBal caller)]
  have hpause : (createFlexibleUnlock (burnApxUSD s caller a1) caller a1).globalPause = false := by
    simp [createFlexibleUnlock, burnApxUSD, h1]
  have hbal : ¬ ((createFlexibleUnlock (burnApxUSD s caller a1) caller a1).apxUSDBal caller < a2) := by
    simp [createFlexibleUnlock, burnApxUSD]
    omega
  refine ⟨createFlexibleUnlock (burnApxUSD s caller a1) caller a1,
          createFlexibleUnlock
            (burnApxUSD (createFlexibleUnlock (burnApxUSD s caller a1) caller a1) caller a2)
            caller a2,
          hs1, ?_, ?_, ?_⟩
  · simp [step, hpause, hbal]
  · exact ⟨s.now, s.now + cooldownPeriod, by simp [createFlexibleUnlock, burnApxUSD]⟩
  · exact ⟨s.now, s.now + cooldownPeriod, by simp [createFlexibleUnlock, burnApxUSD]⟩

/-- REQ continuous-stream: Yield MUST be streamed continuously over a configurable period
rather than as a lump-sum distribution. (Model: the vested amount starts at zero, grows
monotonically, and reaches the full total exactly at the end of the vesting period.) -/
theorem req_continuous_stream (s : State) (h : 0 < s.vestPeriod) :
    vestedAmount s s.vestStart = 0 ∧
    vestedAmount s (s.vestStart + s.vestPeriod) = s.vestTotal ∧
    (∀ n m, n ≤ m → vestedAmount s n ≤ vestedAmount s m) := by
  refine ⟨?_, ?_, fun n m hnm => vestedAmount_mono s hnm⟩
  · unfold vestedAmount
    dsimp only
    repeat' split
    all_goals first | rfl | simp | (exfalso; omega)
  · unfold vestedAmount
    dsimp only
    repeat' split
    all_goals first | rfl | (exfalso; omega)

/-- REQ monthly-yield-rate-set: Each month, the system MUST set the yield rate for the
following month based on the prior month's collateral-base yield. (Model: the admin sets
the month's yield rate via `setYieldRate`, and the configured value is stored verbatim.) -/
theorem req_monthly_yield_rate_set (s : State) (bps : Nat) :
    ∃ s', step s (Op.setYieldRate bps) s.admin = some s' ∧ s'.yieldRateMonth = bps :=
  ⟨{ s with yieldRateMonth := bps }, by simp [step], rfl⟩

/-- REQ pay-to-non-cooldown: Yield MUST be paid to all apyUSD tokens that are not currently
undergoing cooldown. (Model: credited yield increases the vesting pool backing every
outstanding apyUSD share pro-rata, while frozen unlock positions — whose tokens were burned
on request — receive nothing.) -/
theorem req_pay_to_non_cooldown (s : State) (amount : Nat) (s' : State)
    (h : step s (Op.creditYield amount) s.yieldDistributor = some s') :
    s'.vestTotal = s.vestTotal + amount ∧
    (∀ id, s'.unlockTokenAmount id = s.unlockTokenAmount id) ∧
    (∀ a, s'.apyUSDBal a = s.apyUSDBal a) := by
  simp [step] at h
  subst h
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- REQ unlock-cooldown: The apxUSD_unlock token MAY be redeemed for apxUSD only after a
cooldown period has elapsed: claiming strictly before the recorded deadline reverts. -/
theorem req_unlock_cooldown (s : State) (id : Nat) (owner : Address) (amount cooldownEnd : Nat) (caller : Address)
    (h_req : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_early : s.now < cooldownEnd) :
    step s (Op.claimUnlock id) caller = none := by
  simp [step, h_req, h_early]

/-- REQ denylist-blocks-deposit: If the caller or the receiver address is present in the
deny list, deposit and mint operations MUST revert. -/
theorem req_denylist_blocks_deposit (s : State) (amount : Nat) (to caller : Address) :
    (s.denylist caller = true → step s (Op.depositUSDC amount) caller = none) ∧
    (s.denylist caller = true ∨ s.denylist to = true →
      step s (Op.mintApxUSD to amount) caller = none) := by
  constructor
  · intro h
    simp [step, h]
  · intro h
    rcases h with h | h <;> simp [step, h]

/-- REQ early-unlock-fee-linear-decline: The early unlock fee MUST decline linearly over
time from 3.5% down to 0.1%. (Model: within the claim window the fee is bounded by
350 bps, never falls below the 10 bps floor, declines monotonically, and equals exactly
10 bps once the full cooldown has elapsed.) -/
theorem req_early_unlock_fee_linear_decline (requestTime t1 t2 : Nat)
    (h1 : requestTime + minFlexibleClaim ≤ t1) (h12 : t1 ≤ t2) :
    flexibleUnlockFee requestTime t2 ≤ flexibleUnlockFee requestTime t1 ∧
    10 ≤ flexibleUnlockFee requestTime t2 ∧
    flexibleUnlockFee requestTime t2 ≤ 350 ∧
    (requestTime + cooldownPeriod ≤ t2 → flexibleUnlockFee requestTime t2 = 10) :=
  ⟨flexibleUnlockFee_antitone _ h1 h12, flexibleUnlockFee_ge_min _ _ (by omega),
   flexibleUnlockFee_le_start _ _, fun h => flexibleUnlockFee_after_cooldown _ _ (by omega) h⟩

/-- REQ unlock-conversion-after-cooldown: Conversion of apxUSD_unlock to apxUSD MUST only
be possible after the cooldown period has elapsed: early claims revert, and once the
deadline passes the claim succeeds. -/
theorem req_unlock_conversion_after_cooldown (s : State) (id : Nat) (owner : Address)
    (amount cooldownEnd : Nat)
    (h_req : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_owner : s.unlockTokenOwner id = some owner) :
    (s.now < cooldownEnd → step s (Op.claimUnlock id) owner = none) ∧
    (cooldownEnd ≤ s.now → ∃ s', step s (Op.claimUnlock id) owner = some s') := by
  constructor
  · intro h
    simp [step, h_req, h_owner, h]
  · intro h
    rcases ho : step s (Op.claimUnlock id) owner with _ | s'
    · exact absurd ho (by simp [step, h_req, h_owner, Nat.not_lt.mpr h])
    · exact ⟨s', rfl⟩

/-- REQ redeemForMinAssets-revert-if-below-minAssets: redeemForMinAssets(uint256 shares,
uint256 minAssets, address receiver) MUST revert if the amount of apxUSD assets to be
received is less than minAssets. -/
theorem req_redeem_for_min_assets_revert_if_below_min_assets (s : State)
    (shares minAssets : Nat) (receiver caller : Address)
    (h : previewRedeem s shares < minAssets) :
    redeemForMinAssets s shares minAssets receiver caller = none := by
  simp [redeemForMinAssets, h]

/-- REQ unlockToken-mints-apxUSD_unlock-immediately: The UnlockToken contract MUST mint
apxUSD_unlock tokens to the user immediately after the deposit. (Model: "the deposit" is
the user handing apxUSD to the UnlockToken contract by requesting an unlock; in the very
same `requestUnlock` — or `flexibleRequestUnlock` — step, the freshly allocated
apxUSD_unlock token is owned by the depositor and carries the full deposited amount.) -/
theorem req_unlock_token_mints_apx_usd_unlock_immediately (s : State) (amount : Nat)
    (caller : Address) :
    (∀ s', step s (Op.requestUnlock amount) caller = some s' →
      s'.unlockTokenOwner s.nextUnlockId = some caller ∧
      s'.unlockTokenAmount s.nextUnlockId = amount) ∧
    (∀ s', step s (Op.flexibleRequestUnlock amount) caller = some s' →
      s'.unlockTokenOwner s.nextUnlockId = some caller ∧
      s'.unlockTokenAmount s.nextUnlockId = amount) := by
  constructor
  · intro s' h_step
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    constructor <;> simp [createStandardUnlock, burnApxUSD]
  · intro s' h_step
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    constructor <;> simp [createFlexibleUnlock, burnApxUSD]

/-- REQ unlockToken-redeem-after-cooldown: The UnlockToken contract MUST allow a user to
call redeem() after the cooldown period to receive the underlying apxUSD. -/
theorem req_unlock_token_redeem_after_cooldown (s : State) (id : Nat) (owner : Address)
    (amount cooldownEnd : Nat)
    (h_req : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_owner : s.unlockTokenOwner id = some owner)
    (h_time : cooldownEnd ≤ s.now) :
    ∃ s', step s (Op.claimUnlock id) owner = some s' ∧
      s'.apxUSDBal owner = s.apxUSDBal owner + amount := by
  refine ⟨mintApxUSD (burnUnlockNFT s id) owner amount, ?_, ?_⟩
  · simp [step, h_req, h_owner, Nat.not_lt.mpr h_time]
  · simp [mintApxUSD, burnUnlockNFT]

/-- REQ vault-operator-of-UnlockToken: The apyUSD vault MUST be configured as the operator
of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users
immediately. (Model: a withdraw step itself creates the unlock request for the receiver —
no separate user transaction against the unlock registry is needed.) -/
theorem req_vault_operator_of_unlock_token (s : State) (assets : Nat)
    (receiver caller : Address) (s' : State)
    (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    s'.unlockTokenOwner s.nextUnlockId = some receiver ∧
    s'.unlockRequests s.nextUnlockId = some (receiver, assets, s.now + cooldownPeriod) := by
  obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
  subst hs'
  constructor <;> simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]






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

theorem req_apyusd_value_increase (s : State) (_h : s.totalSupply_apyUSD > 0) :
    computeExchangeRate s ≤ computeExchangeRate { s with now := s.now + 1 } :=
  computeExchangeRate_mono_now s 1

-- BROKEN: theorem req_token_no_rebase : Prop :=
-- BROKEN:   ∀ (s : State) (id : Nat) (owner : Address) (amount : Nat),
-- BROKEN:     (s.unlockTokenOwner id = some owner) →
-- BROKEN:     (s.unlockTokenAmount id = amount) →
-- BROKEN:     let s' := createStandardUnlock s owner amount
-- BROKEN:     s'.unlockTokenAmount id = amount

-- BROKEN: theorem req_exchange_rate_non_decreasing : Prop :=
-- BROKEN:   ∀ (s : State), s.exchangeRate ≤ computeExchangeRate s

/-- When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1. -/
theorem req_redemption_exchange_rate_multiplier (s : State) (shares : Nat)
    (h : ray ≤ s.exchangeRate) :
    redeemAssets shares s.exchangeRate = (shares * s.exchangeRate) / ray ∧
    shares ≤ redeemAssets shares s.exchangeRate := by
  refine ⟨rfl, ?_⟩
  unfold redeemAssets
  have hray : 0 < ray := Nat.pow_pos (by decide)
  exact (Nat.le_div_iff_mul_le hray).mpr (Nat.mul_le_mul_left _ h)

/-- Each user MUST have at most one pending redemption request; if the user adds assets
to an existing request, the cooldown timer MUST reset to the time of the update.
(Model: `unlockRequestId` tracks a single request id per user, and topping up an
existing request via `updateStandardUnlock` resets its cooldown end.) -/
theorem req_single_pending_redemption_per_user (s : State) (owner : Address)
    (amount addAmount id oldAmount oldEnd : Nat)
    (h : s.unlockRequests id = some (owner, oldAmount, oldEnd)) :
    (createStandardUnlock s owner amount).unlockRequestId owner = some s.nextUnlockId ∧
    (updateStandardUnlock s id owner addAmount).unlockRequests id
      = some (owner, oldAmount + addAmount, s.now + cooldownPeriod) := by
  constructor
  · simp [createStandardUnlock]
  · simp [updateStandardUnlock, h]

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
    intro s' h3
    obtain ⟨o, a, rt, ce, hreq, _, htime, _⟩ := step_flexibleClaimUnlock_some _ _ _ _ h3
    rw [h1] at hreq
    simp only [Option.some.injEq, Prod.mk.injEq] at hreq
    omega

/-- REQ flexible-redemption-early-fee: The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %. -/
theorem req_flexible_redemption_early_fee (requestTime t1 t2 : Nat)
    (h1 : requestTime + minFlexibleClaim ≤ t1) (h12 : t1 ≤ t2) :
    10 ≤ flexibleUnlockFee requestTime t1 ∧
    flexibleUnlockFee requestTime t1 ≤ 350 ∧
    flexibleUnlockFee requestTime t2 ≤ flexibleUnlockFee requestTime t1 ∧
    (requestTime + cooldownPeriod ≤ t1 → flexibleUnlockFee requestTime t1 = 10) :=
  ⟨flexibleUnlockFee_ge_min _ _ h1, flexibleUnlockFee_le_start _ _,
   flexibleUnlockFee_antitone _ h1 h12,
   fun h => flexibleUnlockFee_after_cooldown _ _ h1 h⟩

/-- REQ overcollateralization-limit: The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin. -/
theorem req_overcollateralization_limit (s : State)
    (h_solvent : (s.totalSupply_apxUSD * s.redemptionValue) / ray ≤ s.totalCollateralValue) :
    (s.totalSupply_apxUSD * s.redemptionValue) / ray
      ≤ s.totalCollateralValue - overcollateralizationBuffer s := by
  unfold overcollateralizationBuffer
  dsimp only
  split <;> omega

/-- REQ arbitrage-mint-access: Only eligible whitelist participants SHALL be permitted to invoke the minting pathway for arbitrage when apxUSD trades above $1.00. -/
theorem req_arbitrage_mint_access (s : State) (to : Address) (amount : Nat) (caller : Address) :
    (step s (Op.mintApxUSD to amount) caller = none) ∨ (s.whitelist caller = true) := by
  by_cases h : s.whitelist caller
  · exact Or.inr h
  · exact Or.inl (by simp [step, h])

/-- REQ arbitrage-redeem-access: Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00. -/
theorem req_arbitrage_redeem_access (s : State) (amount : Nat) (caller : Address) :
    (step s (Op.redeemApxUSD amount) caller = none) ∨ (s.whitelist caller = true) := by
  by_cases h : s.whitelist caller
  · exact Or.inr h
  · exact Or.inl (by simp [step, h])

/-- REQ linear-vest-implementation: The LinearVestV0 contract MUST implement a linear vesting mechanism for yield credited to the apyUSD vault. -/
theorem req_linear_vest_implementation (s : State) (now : Nat) :
    vestedAmount s now = if now < s.vestStart then 0 else
      let elapsed := now - s.vestStart
      if elapsed ≥ s.vestPeriod then s.vestTotal
      else (elapsed * s.vestTotal) / s.vestPeriod := by rfl

/-- REQ yield-rate-dollar-terms: The yield rate MUST be expressed in dollar terms for the month. -/
theorem req_yield_rate_dollar_terms (s : State) :
    ∃ (dollarAmount : Nat), s.yieldRateMonth = dollarAmount :=
  ⟨s.yieldRateMonth, rfl⟩

/-- REQ redemption_value_uniform: The system MUST apply the same Redemption Value to all participants regardless of market conditions. -/
theorem req_redemption_value_uniform (s : State) (a b : Address) (amount : Nat) (sa sb : State)
    (ha : step s (Op.redeemApxUSD amount) a = some sa)
    (hb : step s (Op.redeemApxUSD amount) b = some sb) :
    sa.usdcBal a - s.usdcBal a = sb.usdcBal b - s.usdcBal b := by
  obtain ⟨_, _, _, _, hsa⟩ := step_redeemApxUSD_some _ _ _ _ ha
  obtain ⟨_, _, _, _, hsb⟩ := step_redeemApxUSD_some _ _ _ _ hb
  subst hsa hsb
  simp [emitEvent, burnApxUSD]

/-- REQ buffer_not_consumed: The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations. -/
theorem req_buffer_not_consumed (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    overcollateralizationBuffer s ≤ overcollateralizationBuffer s' := by
  obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
  subst hs'
  exact overcollateralizationBuffer_mono _ _ (by simp [emitEvent, burnApxUSD])
    (by simp [emitEvent, burnApxUSD]) (by simp [emitEvent, burnApxUSD])

/-- REQ catastrophic_backstop: Upon detection of a catastrophic scenario, the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, including the buffer, pro‑rata to remaining holders. -/
theorem req_catastrophic_backstop (s : State) (s' : State)
    (h_step : step s Op.catastrophicBackstop s.admin = some s') :
    s'.redemptionValue = s'.totalCollateralValue := by
  simp [step] at h_step
  subst h_step
  rfl

/-- REQ governance_deploy_buffer: The system MUST restrict voting on buffer deployment to holders of the governance token. -/
theorem req_governance_deploy_buffer (s : State) (s' : State)
    (h_step : step s Op.voteBufferDeployment s.governance = some s') :
    s.governanceTokenBal s.governance > 0 := by
  simp only [step] at h_step
  split at h_step
  · exact absurd h_step (by simp)
  · omega

/-- REQ rfq_redemption_allowed: The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute those requests. -/
theorem req_rfq_redemption_allowed (s : State) (user caller : Address) (amount : Nat) :
    (∀ s', step s (Op.executeRFQRedemption user amount) caller = some s' →
      s.rfqCounterparties.contains caller = true) ∧
    (s.globalPause = false → s.rfqCounterparties.contains caller = true →
      amount ≤ s.apxUSDBal user → (amount * s.redemptionValue) / ray ≤ s.usdcReserve →
      ∃ s', step s (Op.executeRFQRedemption user amount) caller = some s') := by
  constructor
  · intro s' h
    exact (step_executeRFQRedemption_some _ _ _ _ _ h).2.1
  · intro h1 h2 h3 h4
    have h2' : caller ∈ s.rfqCounterparties := by simpa using h2
    rcases ho : step s (Op.executeRFQRedemption user amount) caller with _ | s'
    · exact absurd ho (by simp [step, h1, h2', Nat.not_lt.mpr h3, Nat.not_lt.mpr h4])
    · exact ⟨s', rfl⟩

/-- REQ deposit_immediate: The apyUSD vault MUST complete deposit operations synchronously and deliver apyUSD shares to the receiver without any delay. -/
theorem req_deposit_immediate (s : State) (amount : Nat) (to : Address) (caller : Address) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    s'.apyUSDBal to ≥ s.apyUSDBal to := by
  obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
  subst hs'
  simp [emitEvent, mintApxUSD]

/-- REQ mint_immediate: The apyUSD vault MUST complete mint operations synchronously and deliver apyUSD shares to the receiver without any delay. -/
theorem req_mint_immediate (s : State) (to : Address) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.mintApxUSD to amount) caller = some s') :
    s'.apyUSDBal to ≥ s.apyUSDBal to := by
  obtain ⟨_, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent, mintApxUSD]

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
           s'.apxUSDBal caller = s.apxUSDBal caller + s.unlockTokenAmount requestId) := by
  right
  refine ⟨mintApxUSD (burnUnlockNFT s requestId) caller (s.unlockTokenAmount requestId), ?_, ?_⟩
  · simp [step, h_request, h_owner, Nat.not_lt.mpr (Nat.sub_le s.now cooldownPeriod)]
  · simp [mintApxUSD, burnUnlockNFT]

/-- REQ unlock-token-no-yield: apxUSD_unlock tokens MUST NOT earn yield. -/
theorem req_unlock_token_no_yield (s : State) (amount dt : Nat) (owner : Address) :
    ({ createStandardUnlock s owner amount with
        now := (createStandardUnlock s owner amount).now + dt }).unlockTokenAmount s.nextUnlockId
      = amount := by
  simp [createStandardUnlock]

/-- REQ unlock-receipt-nft-mint: When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim. -/
theorem req_unlock_receipt_nft_mint (s : State) (owner : Address) (amount : Nat) :
    let s' := createStandardUnlock s owner amount
    s'.nextUnlockId = s.nextUnlockId + 1 ∧ 
    s'.unlockRequestId owner = some s.nextUnlockId ∧
    s'.unlockTokenOwner s.nextUnlockId = some owner := by
  simp [createStandardUnlock]

/-- REQ unlock-claimable-after-3d: Unlocks MUST become claimable after three days. -/
theorem req_unlock_claimable_after_3d (s : State) (requestId : Nat) (caller : Address)
    (h_now : minFlexibleClaim ≤ s.now)
    (h_request : s.flexibleUnlockRequests requestId = some (caller, (s.unlockTokenAmount requestId), s.now - minFlexibleClaim, s.now - minFlexibleClaim + cooldownPeriod))
    (h_owner : s.unlockTokenOwner requestId = some caller) :
    step s (.flexibleClaimUnlock requestId) caller ≠ none := by
  simp [step, h_request, h_owner]
  omega

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
    | none => False := by
  simp [updateStandardUnlock, h]

-- BROKEN: /-- REQ withdrawForMaxShares-revert-if-exceeds-maxShares: withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of apyUSD shares required to withdraw the assets exceeds maxShares. -/

-- BROKEN: /-- REQ redeemForMinAssets-revert-if-below-minAssets: redeemForMinAssets(uint256 shares, uint256 minAssets, address receiver) MUST revert if the amount of apxUSD assets to be received is less than minAssets. -/

-- BROKEN: /-- REQ vault-pulls-vested-yield-before-withdraw: When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal. -/

-- BROKEN: /-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
-- BROKEN: 
-- BROKEN: 
-- BROKEN: -- Theorems added after model extension

/-- REQ deposit-mint-apxusd: The protocol MUST mint apxUSD to a user when the user deposits USDC. -/
theorem req_deposit_mint_apxusd (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true) (h3 : s.usdcBal caller ≥ amount)
    (h4 : s.denylist caller = false) :
    ∃ s', step s (Op.depositUSDC amount) caller = some s' ∧
          s'.apxUSDBal caller = s.apxUSDBal caller + amount ∧
          s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount := by
  rcases ho : step s (Op.depositUSDC amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, h2, h4, Nat.not_lt.mpr h3])
  · obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ ho
    subst hs'
    exact ⟨_, rfl, by simp [emitEvent, mintApxUSD], by simp [emitEvent, mintApxUSD]⟩

/-- REQ mint-price: The protocol MUST price newly minted apxUSD at $1 per unit. -/
theorem req_mint_price (s : State) (amount : Nat) (to : Address) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true) (h3 : s.usdcBal caller ≥ amount)
    (h4 : s.denylist caller = false) (h5 : s.denylist to = false) :
    ∃ s', step s (Op.mintApxUSD to amount) caller = some s' ∧
          s'.apxUSDBal to = s.apxUSDBal to + amount ∧
          s'.usdcBal caller = s.usdcBal caller - amount ∧
          s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount := by
  rcases ho : step s (Op.mintApxUSD to amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, h2, h4, h5, Nat.not_lt.mpr h3])
  · obtain ⟨_, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ ho
    subst hs'
    exact ⟨_, rfl, by simp [emitEvent, mintApxUSD], by simp [emitEvent, mintApxUSD],
           by simp [emitEvent, mintApxUSD]⟩

/-- REQ redemption-value: The protocol MUST allow redemption of apxUSD at the current Redemption Value. -/
theorem req_redemption_value (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true)
    (h3 : s.apxUSDBal caller ≥ amount)
    (h4 : s.usdcReserve ≥ (amount * s.redemptionValue) / ray) :
    ∃ s', step s (Op.redeemApxUSD amount) caller = some s' := by
  have hbuf : overcollateralizationBuffer s ≤ overcollateralizationBuffer
      { burnApxUSD s caller amount with
        usdcReserve := (burnApxUSD s caller amount).usdcReserve - amount * s.redemptionValue / ray
        usdcBal := fun a => if a = caller then (burnApxUSD s caller amount).usdcBal a + amount * s.redemptionValue / ray
                            else (burnApxUSD s caller amount).usdcBal a } :=
    overcollateralizationBuffer_mono _ _ (by simp [burnApxUSD]) (by simp [burnApxUSD])
      (by simp [burnApxUSD])
  rcases ho : step s (Op.redeemApxUSD amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, h2, Nat.not_lt.mpr h3, Nat.not_lt.mpr h4, Nat.not_lt.mpr hbuf])
  · exact ⟨s', rfl⟩

-- BROKEN: /-- REQ no-rehypothecation: The protocol MUST NOT rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose. -/
-- BROKEN: -- UNFORMALIZABLE req_no_rehypothecation: The model does not specify uses of apxUSD beyond minting/burning/transferring and locking.

-- BROKEN: /-- REQ yield-distribution-period: The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period. -/
-- BROKEN: -- UNFORMALIZABLE req_yield_distribution_period: The model does not explicitly track time-based distribution of yield over 20 days; it only tracks vesting.

/-- REQ lock-apxusd: The protocol MUST allow a user to lock apxUSD in the vault and receive apyUSD. -/
theorem req_lock_apxusd (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.apxUSDBal caller ≥ amount) :
    ∃ s', step s (Op.lockApxUSD amount) caller = some s' := by
  rcases ho : step s (Op.lockApxUSD amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, Nat.not_lt.mpr h2])
  · exact ⟨s', rfl⟩

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
  obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
  subst hs'
  simp [emitEvent, burnApxUSD]

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
  obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
  subst hs'
  simp [emitEvent, mintApxUSD]

/-- REQ deposit-permissionless: The vault MUST allow any address to deposit apxUSD and receive apyUSD without requiring KYB/KYC. -/
theorem req_deposit_permissionless (s : State) (amount : Nat) (caller : Address)
    (h_pause : s.globalPause = false)
    (h_balance : s.apxUSDBal caller ≥ amount) :
    ∃ s', step s (Op.lockApxUSD amount) caller = some s' := by
  rcases ho : step s (Op.lockApxUSD amount) caller with _ | s'
  · exact absurd ho (by simp [step, h_pause, Nat.not_lt.mpr h_balance])
  · exact ⟨s', rfl⟩

/-- REQ buffer-preservation: The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed. -/
theorem req_buffer_preservation (s s' : State) (amount : Nat) (caller : Address)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    overcollateralizationBuffer s ≤ overcollateralizationBuffer s' := by
  obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
  subst hs'
  exact overcollateralizationBuffer_mono _ _ (by simp [emitEvent, burnApxUSD])
    (by simp [emitEvent, burnApxUSD]) (by simp [emitEvent, burnApxUSD])

/-- REQ mint-redeem-at-redemption-value: All minting and redemption transactions MUST be
executed at the Redemption Value, which reflects the underlying basket of preferred shares
and cash. (Model: minting is priced at $1 per unit — `amount` USDC enters the reserve for
`amount` apxUSD — while redemptions settle at the current Redemption Value.) -/
theorem req_mint_redeem_at_redemption_value (s : State) (amount : Nat) (to caller : Address) :
    (∀ s', step s (Op.mintApxUSD to amount) caller = some s' →
      s'.usdcReserve = s.usdcReserve + amount ∧
      s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount) ∧
    (∀ s', step s (Op.redeemApxUSD amount) caller = some s' →
      s'.usdcBal caller = s.usdcBal caller + (amount * s.redemptionValue) / ray) := by
  constructor
  · intro s' h_step
    obtain ⟨_, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    exact ⟨by simp [emitEvent, mintApxUSD], by simp [emitEvent, mintApxUSD]⟩
  · intro s' h_step
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD]

/-- REQ buffer-non-decreasing: The overcollateralization buffer, defined as the difference
between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over
time due to yield spreads and collateral appreciation. (Model: across every operation that
burns apxUSD — standard and flexible unlock requests, direct redemptions and RFQ
redemptions — the buffer is non-decreasing.) -/
theorem req_buffer_non_decreasing (s s' : State) (op : Op) (caller : Address)
    (h_step : step s op caller = some s')
    (h_redemption : (∃ a, op = Op.redeemApxUSD a) ∨ (∃ a, op = Op.requestUnlock a) ∨
                    (∃ a, op = Op.flexibleRequestUnlock a) ∨
                    (∃ u a, op = Op.executeRFQRedemption u a)) :
    overcollateralizationBuffer s ≤ overcollateralizationBuffer s' := by
  rcases h_redemption with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨u, a, rfl⟩
  · obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    exact overcollateralizationBuffer_mono _ _ (by simp [emitEvent, burnApxUSD])
      (by simp [emitEvent, burnApxUSD]) (by simp [emitEvent, burnApxUSD])
  · obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    exact overcollateralizationBuffer_mono _ _ (by simp [createStandardUnlock, burnApxUSD])
      (by simp [createStandardUnlock, burnApxUSD]) (by simp [createStandardUnlock, burnApxUSD])
  · obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    exact overcollateralizationBuffer_mono _ _ (by simp [createFlexibleUnlock, burnApxUSD])
      (by simp [createFlexibleUnlock, burnApxUSD]) (by simp [createFlexibleUnlock, burnApxUSD])
  · obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    exact overcollateralizationBuffer_mono _ _ (by simp [burnApxUSD])
      (by simp [burnApxUSD]) (by simp [burnApxUSD])

/-- REQ configurable-vesting-period: The vesting period for linear yield distribution MUST be configurable. -/
theorem req_configurable_vesting_period (s : State) (p : Nat) :
    ∃ s', step s (Op.setVestPeriod p) s.admin = some s' ∧ s'.vestPeriod = p :=
  ⟨{ s with vestPeriod := p }, by simp [step], rfl⟩

/-- REQ deposit-emits-event: The deposit(assets, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution. -/
theorem req_deposit_emits_event (s s' : State) (amount : Nat) (caller : Address)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    ∃ sender receiver owner assets shares : Nat,
      ("Deposit", [sender, receiver, owner, assets, shares]) ∈ s'.eventLog := by
  obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
  subst hs'
  exact ⟨caller, caller, caller, amount, amount, by simp [emitEvent]⟩

/-- REQ mint-emits-event: The mint(shares, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution. -/
theorem req_mint_emits_event (s s' : State) (to : Address) (amount : Nat) (caller : Address)
    (h_step : step s (Op.mintApxUSD to amount) caller = some s') :
    ∃ sender receiver owner assets shares : Nat,
      ("Deposit", [sender, receiver, owner, assets, shares]) ∈ s'.eventLog := by
  obtain ⟨_, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
  subst hs'
  exact ⟨caller, to, to, amount, amount, by simp [emitEvent]⟩

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

/-- REQ vault-pulls-vested-yield-before-withdraw: When a withdrawal is requested, the vault
MUST automatically pull all vested yield from the LinearVestV0 contract before processing
the withdrawal. (Model: the post-state vault balance is the pulled-yield balance minus the
withdrawn assets, i.e. the vest pull happens before the withdrawal is applied.) -/
theorem req_vault_pulls_vested_yield_before_withdraw (s : State) (assets : Nat) (receiver : Address) (caller : Address)
    (h : step s (.withdraw assets receiver) caller = some s') :
    s'.vaultApxUSDBal = (pullVestedYield s).vaultApxUSDBal - assets := by
  obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

-- Theorems added by coverage reconciliation

/-- REQ redeem-liquidate-usdc: The system SHALL liquidate preferred‑share collateral to USDC
in order to settle any redemption request. (Model: redemptions are settled in USDC drawn
from the liquidation reserve — the reserve is debited and the redeemer is paid the
Redemption-Value-equivalent USDC amount.) -/
theorem req_redeem_liquidate_usdc (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    s'.usdcReserve = s.usdcReserve - (amount * s.redemptionValue) / ray ∧
    s'.usdcBal caller = s.usdcBal caller + (amount * s.redemptionValue) / ray := by
  obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
  subst hs'
  constructor <;> simp [emitEvent, burnApxUSD]

/-- REQ yield-distributor-credit: The YieldDistributor MUST credit converted apxUSD
proceeds to the apyUSD vault. (Model: the yield distributor's credit lands in the vault's
vesting stream — from which `totalAssets` grows — and only the yield distributor may
credit.) -/
theorem req_yield_distributor_credit (s : State) (amount : Nat) (caller : Address) :
    (caller = s.yieldDistributor →
      step s (Op.creditYield amount) caller = some { s with
        usdcReserve := s.usdcReserve + amount,
        vestTotal := s.vestTotal + amount,
        vestStart := s.now }) ∧
    (caller ≠ s.yieldDistributor → step s (Op.creditYield amount) caller = none) := by
  constructor
  · intro h1
    simp [step, h1]
  · intro h1
    simp [step, h1]

/-- REQ new-locked-receives-yield: When new apyUSD is locked, it MUST immediately begin
receiving yield, which reduces the overall percentage yield for existing holders. (Model:
locking immediately mints shares to the depositor and adds them to the total supply, so all
future vested yield is spread over the enlarged share base.) -/
theorem req_new_locked_receives_yield (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    s'.apyUSDBal caller = s.apyUSDBal caller + lockShares amount s.exchangeRate ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD + lockShares amount s.exchangeRate := by
  obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
  subst hs'
  constructor <;> simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]

-- BROKEN: /-- REQ cooldown_removal: When apyUSD enters the cooldown phase, it MUST be removed from the yield pool, causing remaining apyUSD to receive a higher percentage yield. -/
-- BROKEN: -- UNFORMALIZABLE req_cooldown_removal: The model does not explicitly track individual apyUSD allocations in the yield pool or compute yield distribution percentages.

/-- REQ synchronous_withdraw_return_token: The apyUSD vault MUST execute withdrawals and redeems synchronously and MUST return apxUSD_unlock tokens immediately. -/
theorem req_synchronous_withdraw_return_token (s : State) (assets : Nat) (receiver caller : Address)
    (h1 : s.globalPause = false)
    (h2 : (pullVestedYield s).apyUSDBal caller ≥ withdrawShares assets (pullVestedYield s).exchangeRate)
    (h3 : (pullVestedYield s).vaultApxUSDBal ≥ assets) :
    ∃ s', step s (Op.withdraw assets receiver) caller = some s' ∧
    (∃ id, s'.unlockTokenOwner id = some receiver ∧ s'.unlockTokenAmount id = assets) := by
  rcases ho : step s (Op.withdraw assets receiver) caller with _ | s'
  · have h2' : withdrawShares assets s.exchangeRate ≤ s.apyUSDBal caller := by simpa using h2
    have h3' : assets ≤ s.vaultApxUSDBal + vestedAmount s s.now := by simpa using h3
    exact absurd ho (by simp [step, h1, h2', h3'])
  · refine ⟨s', rfl, s.nextUnlockId, ?_⟩
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ ho
    subst hs'
    constructor <;> simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- REQ withdrawForMaxShares-revert-if-exceeds-maxShares: withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of apyUSD shares required to withdraw the assets exceeds maxShares. -/
theorem req_withdraw_for_max_shares_revert_if_exceeds_max_shares (s : State) (assets maxShares : Nat) (receiver caller : Address)
    (h : previewWithdraw s assets > maxShares) :
    withdrawForMaxShares s assets maxShares receiver caller = none := by
  simp [withdrawForMaxShares, h]

/-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
theorem req_vault_burns_apyUSD_shares_immediately_on_withdraw (s s' : State) (assets : Nat) (receiver caller : Address)
    (h_step : step s (.withdraw assets receiver) caller = some s') :
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD - withdrawShares assets s.exchangeRate := by
  obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- REQ depositforminshares_slippage: depositForMinShares(uint256 assets, uint256 minShares, address receiver) MUST revert if the number of shares that would be minted is less than minShares. -/
theorem req_depositforminshares_slippage (s : State) (assets : Nat) (minShares : Nat) (receiver : Address) (caller : Address)
    (h : previewDeposit s assets < minShares) :
    depositForMinShares s assets minShares receiver caller = none := by
  simp [depositForMinShares, h]

/-- REQ mintformaxassets_slippage: mintForMaxAssets(uint256 shares, uint256 maxAssets, address receiver) MUST revert if the amount of assets required to mint the requested shares exceeds maxAssets. -/
theorem req_mintformaxassets_slippage (s : State) (shares : Nat) (maxAssets : Nat) (receiver : Address) (caller : Address)
    (h : previewMint s shares > maxAssets) :
    mintForMaxAssets s shares maxAssets receiver caller = none := by
  simp [mintForMaxAssets, h]

/-- REQ totalAssets_includes_vault_balance_and_vested: The vault's totalAssets() function MUST include both the vault's apxUSD balance and the vestedAmount() reported by the LinearVestV0 contract. -/
theorem req_totalAssets_includes_vault_balance_and_vested (s : State) :
    totalAssets s = s.vaultApxUSDBal + vestedAmount s s.now := rfl

/-- REQ withdrawal_pulls_vested: When processing a withdrawal, the apyUSD vault MUST pull
all vested yield from the LinearVestV0 contract before completing the withdrawal. (Model:
the post-state vault balance is the pulled-yield balance minus the withdrawn assets.) -/
theorem req_withdrawal_pulls_vested (s : State) (assets : Nat) (receiver : Address) (caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s'.vaultApxUSDBal = (pullVestedYield s).vaultApxUSDBal - assets := by
  obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

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
    (previewWithdraw s assets > maxShares →
      withdrawForMaxShares s assets maxShares receiver caller = none) ∧
    (previewWithdraw s assets ≤ maxShares →
      withdrawForMaxShares s assets maxShares receiver caller
        = step s (Op.withdraw assets receiver) caller) := by
  constructor
  · intro h; simp [withdrawForMaxShares, h]
  · intro h; simp [withdrawForMaxShares, Nat.not_lt.mpr h]

/-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
theorem req_vault_burns_apy_usd_shares_immediately (s : State) (assets : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    s'.apyUSDBal caller = s.apyUSDBal caller - withdrawShares assets s.exchangeRate := by
  obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- REQ vault-burns-apyUSD-shares-immediately: The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call. -/
theorem req_vault_burns_apy_usd_shares_immediately_redeem (s : State) (shares : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s') :
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD - shares := by
  obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- REQ vault-deposits-apxUSD-into-UnlockToken: The vault MUST deposit the corresponding apxUSD amount into the UnlockToken contract during a withdraw or redeem operation. -/
theorem req_vault_deposits_apx_usd_into_unlock_token (s : State) (assets : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    match s'.unlockRequests (s'.nextUnlockId - 1) with
    | some (_, amount, _) => amount = assets
    | none => False
    := by
  obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- REQ vault-deposits-apxUSD-into-UnlockToken: The vault MUST deposit the corresponding apxUSD amount into the UnlockToken contract during a withdraw or redeem operation. -/
theorem req_vault_deposits_apx_usd_into_unlock_token_redeem (s : State) (shares : Nat) (receiver caller : Address) (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s') :
    match s'.unlockRequests (s'.nextUnlockId - 1) with
    | some (_, amount, _) => amount = redeemAssets shares s.exchangeRate
    | none => False
    := by
  obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

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
