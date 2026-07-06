import Std.Data.HashMap

namespace Apyx

/-- Type abbreviations for clarity -/
abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat
abbrev ReceiptId := Nat

/-- State structure for the Apyx protocol -/
structure State where
  TCV : Amount                        -- Total Collateral Value
  RV : Amount                         -- Redemption Value
  liquidityBuffer : Amount            -- Liquidity buffer
  exchangeRate : Amount               -- Exchange rate (≥ 1e18)
  totalShares : Amount                -- Total apyUSD shares
  totalAssets : Amount                -- Vault assets (TCV - buffer + vestedYield)
  vestedYield : Amount                -- Vested yield available
  paused : Bool                       -- Global pause flag
  denyList : Address → Bool           -- Deny list mapping
  whitelist : Address → Bool          -- Whitelist for mint/redeem
  approvedCounterparties : Address → Bool  -- Approved RFQ counterparties
  unlockReceiptId : ReceiptId         -- Auto-incrementing receipt ID
  cooldownEnd : Address → Timestamp   -- Cooldown end time per user
  userPendingAmount : Address → Amount -- Amount pending unlock per user
  receiptOwners : ReceiptId → Address -- Owner of each unlock receipt
  receiptAmounts : ReceiptId → Amount -- Amount locked in each receipt
  receiptCooldownEnd : ReceiptId → Timestamp -- Cooldown end for each receipt
  bal : Address → Amount              -- apyUSD balances
  apxUSDBal : Address → Amount        -- apxUSD balances
  deriving Inhabited

/-- Operations in the Apyx protocol -/
inductive Op where
  | deposit (assets : Amount) (receiver : Address)
  | mint (shares : Amount) (receiver : Address)
  | withdraw (assets : Amount) (receiver : Address)
  | redeem (shares : Amount) (receiver : Address)
  | requestUnlock (amount : Amount)
  | claimUnlock (tokenId : ReceiptId)
  | submitRFQ (amount : Amount) (price : Amount) (expiry : Timestamp)
  | fulfilRFQ (requestId : ReceiptId)
  | pause
  | unpause
  | addToDenyList (addr : Address)
  | removeFromDenyList (addr : Address)
  | upgradeTo (newImpl : Address)
  | distributeYield (amount : Amount)
  deriving Inhabited

/-- Helper: compute shares from assets using exchange rate -/
def assetsToShares (assets : Amount) (exchangeRate : Amount) : Amount :=
  if exchangeRate = 0 then 0 else assets / exchangeRate

/-- Helper: compute assets from shares using exchange rate -/
def sharesToAssets (shares : Amount) (exchangeRate : Amount) : Amount :=
  shares * exchangeRate

/-- Helper: check if user is in cooldown -/
def isInCooldown (s : State) (user : Address) (now : Timestamp) : Bool :=
  now < s.cooldownEnd user

/-- Helper: apply early unlock fee (linear from 3.5% to 0.1% over 3 days) -/
def applyEarlyUnlockFee (amount : Amount) (elapsed : Amount) (cooldownDuration : Amount) : Amount :=
  let maxFeePercent := 35 -- 3.5% scaled by 10
  let minFeePercent := 1  -- 0.1% scaled by 10
  let feePercent := maxFeePercent - (elapsed * (maxFeePercent - minFeePercent) / cooldownDuration)
  amount - (amount * feePercent / 1000)

/-- Step function for the Apyx protocol -/
def step (s : State) (op : Op) (caller : Address) (now : Timestamp) : Option State :=
  match op with
  | Op.deposit assets _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let shares := assetsToShares assets s.exchangeRate
      let newTotalAssets := s.totalAssets + assets
      let newTotalShares := s.totalShares + shares
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = _receiver then s.bal a + shares else s.bal a
      }

  | Op.mint shares _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let requiredAssets := sharesToAssets shares s.exchangeRate
      let availableForMinting := s.TCV - s.liquidityBuffer
      if requiredAssets > availableForMinting then none
      else
        let newTotalAssets := s.totalAssets + requiredAssets
        let newTotalShares := s.totalShares + shares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = _receiver then s.bal a + shares else s.bal a
        }

  | Op.withdraw assets receiver =>
    let callerShares := s.bal caller
    let sharesNeeded := assetsToShares assets s.exchangeRate
    if assets > s.totalAssets ∨ sharesNeeded > callerShares ∨ isInCooldown s caller now then none
    else
      -- Pull vested yield before processing
      let newVestedYield := 0 -- Simplified: assume all vested yield is pulled
      let newTotalAssets := s.totalAssets - assets + newVestedYield
      let newTotalShares := s.totalShares - sharesNeeded
      let newUnlockReceiptId := s.unlockReceiptId + 1
      let cooldownEndTime := now + 20 * 24 * 3600 -- 20 days
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        vestedYield := newVestedYield
        unlockReceiptId := newUnlockReceiptId
        userPendingAmount := fun u => if u = caller then s.userPendingAmount u + assets else s.userPendingAmount u
        receiptOwners := fun id => if id = newUnlockReceiptId then caller else s.receiptOwners id
        receiptAmounts := fun id => if id = newUnlockReceiptId then assets else s.receiptAmounts id
        receiptCooldownEnd := fun id => if id = newUnlockReceiptId then cooldownEndTime else s.receiptCooldownEnd id
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
        cooldownEnd := fun u => if u = caller then cooldownEndTime else s.cooldownEnd u
      }

  | Op.redeem shares receiver =>
    let callerShares := s.bal caller
    if shares > callerShares ∨ s.exchangeRate < 1000000000000000000 then none -- exchangeRate ≥ 1e18
    else
      let assetsOut := sharesToAssets shares s.exchangeRate
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let newUnlockReceiptId := s.unlockReceiptId + 1
      let cooldownEndTime := now + 20 * 24 * 3600 -- 20 days
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        unlockReceiptId := newUnlockReceiptId
        userPendingAmount := fun u => if u = caller then s.userPendingAmount u + assetsOut else s.userPendingAmount u
        receiptOwners := fun id => if id = newUnlockReceiptId then caller else s.receiptOwners id
        receiptAmounts := fun id => if id = newUnlockReceiptId then assetsOut else s.receiptAmounts id
        receiptCooldownEnd := fun id => if id = newUnlockReceiptId then cooldownEndTime else s.receiptCooldownEnd id
        bal := fun a => if a = caller then s.bal a - shares else s.bal a
        cooldownEnd := fun u => if u = caller then cooldownEndTime else s.cooldownEnd u
      }

  | Op.requestUnlock amount =>
    let callerApxUSD := s.apxUSDBal caller
    if amount > callerApxUSD ∨ isInCooldown s caller now then none
    else
      let newUnlockReceiptId := s.unlockReceiptId + 1
      let cooldownEndTime := now + 20 * 24 * 3600 -- 20 days
      some {
        s with
        unlockReceiptId := newUnlockReceiptId
        userPendingAmount := fun u => if u = caller then s.userPendingAmount u + amount else s.userPendingAmount u
        receiptOwners := fun id => if id = newUnlockReceiptId then caller else s.receiptOwners id
        receiptAmounts := fun id => if id = newUnlockReceiptId then amount else s.receiptAmounts id
        receiptCooldownEnd := fun id => if id = newUnlockReceiptId then cooldownEndTime else s.receiptCooldownEnd id
        cooldownEnd := fun u => if u = caller then cooldownEndTime else s.cooldownEnd u
      }

  | Op.claimUnlock tokenId =>
    let owner := s.receiptOwners tokenId
    let amount := s.receiptAmounts tokenId
    let cooldownEnd := s.receiptCooldownEnd tokenId
    if owner ≠ caller ∨ now < cooldownEnd then none
    else
      -- Apply early unlock fee if claiming before full cooldown (simplified)
      let elapsed := now - (cooldownEnd - 20 * 24 * 3600)
      let cooldownDuration := 20 * 24 * 3600
      let finalAmount := if elapsed < 3 * 24 * 3600 then
        applyEarlyUnlockFee amount elapsed cooldownDuration
      else amount
      some {
        s with
        apxUSDBal := fun a => if a = caller then s.apxUSDBal a + finalAmount else s.apxUSDBal a
        receiptOwners := fun id => if id = tokenId then 0 else s.receiptOwners id -- Burn receipt
        receiptAmounts := fun id => if id = tokenId then 0 else s.receiptAmounts id
        userPendingAmount := fun u => if u = caller then s.userPendingAmount u - amount else s.userPendingAmount u
      }

  | Op.submitRFQ _amount _price _expiry =>
    if ¬s.approvedCounterparties caller then none
    else
      -- Record RFQ (simplified)
      some s

  | Op.fulfilRFQ requestId =>
    if ¬s.approvedCounterparties caller then none
    else
      let owner := s.receiptOwners requestId
      let amount := s.receiptAmounts requestId
      some {
        s with
        apxUSDBal := fun a => if a = owner then s.apxUSDBal a + amount else s.apxUSDBal a
        receiptOwners := fun id => if id = requestId then 0 else s.receiptOwners id -- Burn receipt
        receiptAmounts := fun id => if id = requestId then 0 else s.receiptAmounts id
        userPendingAmount := fun u => if u = owner then s.userPendingAmount u - amount else s.userPendingAmount u
      }

  | Op.pause =>
    if ¬s.whitelist caller then none -- Assuming governance/whitelist can pause
    else some { s with paused := true }

  | Op.unpause =>
    if ¬s.whitelist caller then none -- Assuming governance/whitelist can unpause
    else some { s with paused := false }

  | Op.addToDenyList addr =>
    if ¬s.whitelist caller then none -- Assuming governance/whitelist can modify deny list
    else some { s with denyList := fun a => if a = addr then true else s.denyList a }

  | Op.removeFromDenyList addr =>
    if ¬s.whitelist caller then none -- Assuming governance/whitelist can modify deny list
    else some { s with denyList := fun a => if a = addr then false else s.denyList a }

  | Op.upgradeTo _newImpl =>
    if ¬s.whitelist caller then none -- Assuming governance can upgrade
    else some s -- Simplified: no actual upgrade logic

  | Op.distributeYield amount =>
    if amount > s.vestedYield then none
    else
      let newVestedYield := s.vestedYield - amount
      let newTotalAssets := s.totalAssets + amount
      some {
        s with
        vestedYield := newVestedYield
        totalAssets := newTotalAssets
      }

end Apyx
