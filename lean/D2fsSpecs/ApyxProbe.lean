namespace ApyxProbe

-- Type abbreviations for clarity
abbrev Address := Nat
abbrev Amount := Nat
abbrev Timestamp := Nat
abbrev ReceiptId := Nat

-- Constants
def COOLDOWN_DURATION : Timestamp := 20 * 24 * 3600  -- 20 days in seconds
def MIN_COOLDOWN_CLAIM : Timestamp := 3 * 24 * 3600   -- 3 days in seconds
def EXCHANGE_RATE_SCALE : Amount := 1000000000000000000  -- 1e18
def EARLY_UNLOCK_FEE_MAX : Amount := 35  -- 3.5% scaled by 10
def EARLY_UNLOCK_FEE_MIN : Amount := 1   -- 0.1% scaled by 10

-- Linear Vesting Schedule Structure
structure VestingSchedule where
  startTime : Timestamp
  endTime : Timestamp
  totalAmount : Amount
  claimedAmount : Amount
  deriving Inhabited

-- Yield Rate Structure
structure YieldRate where
  periodStart : Timestamp
  periodEnd : Timestamp
  rateInDollars : Amount  -- Rate expressed in dollar terms
  deriving Inhabited

-- State structure
structure State where
  TCV : Amount                      -- Total Collateral Value
  RV : Amount                       -- Redemption Value
  liquidityBuffer : Amount          -- Liquidity buffer
  exchangeRate : Amount             -- Exchange rate (apyUSD to apxUSD)
  totalShares : Amount              -- Total apyUSD shares
  totalAssets : Amount              -- Total assets in vault
  vestedYield : Amount              -- Vested yield available
  paused : Bool                     -- Global pause flag
  denyList : Address → Bool         -- Deny list mapping
  whitelist : List Address          -- Whitelist for mint/redeem
  approvedCounterparties : List Address  -- Approved RFQ counterparties
  unlockReceiptId : ReceiptId       -- Auto-incrementing receipt ID
  cooldownEnd : Address → Timestamp -- Cooldown end time per user
  pendingUnlockAmount : Address → Amount  -- Pending unlock amount per user
  unlockReceiptOwner : ReceiptId → Address  -- Owner of each unlock receipt
  unlockReceiptAmount : ReceiptId → Amount  -- Amount locked in each receipt
  unlockReceiptCooldownEnd : ReceiptId → Timestamp  -- Cooldown end for each receipt
  bal : Address → Amount            -- apyUSD balance per address
  apxUsdBal : Address → Amount      -- apxUSD balance per address
  rfqRequests : ReceiptId → Option (Amount × Amount × Timestamp)  -- (amount, price, expiry)
  -- New fields for requirements
  currentTime : Timestamp           -- Current system time
  yieldRates : List YieldRate      -- Monthly yield rates
  vestingPeriod : Timestamp        -- Configurable vesting period
  userVestingSchedules : Address → Option VestingSchedule  -- Linear vesting per user
  unlockReceiptTransferable : Bool := false  -- Unlock tokens are non-transferable
  unlockReceiptCancelable : Bool := false    -- Unlock requests cannot be canceled
  deriving Inhabited

-- Operations
inductive Op
  | deposit (assets : Amount) (receiver : Address)
  | mint (shares : Amount) (receiver : Address)
  | withdraw (assets : Amount) (receiver : Address)
  | redeem (shares : Amount) (receiver : Address)
  | requestUnlock (amount : Amount)
  | claimUnlock (tokenId : ReceiptId)
  | submitRFQ (requestId : ReceiptId) (amount : Amount) (price : Amount) (expiry : Timestamp)
  | fulfilRFQ (requestId : ReceiptId)
  | pause
  | unpause
  | addToDenyList (addr : Address)
  | removeFromDenyList (addr : Address)
  | distributeYield (amount : Amount)
  -- New operations for requirements
  | depositForMinShares (assets : Amount) (minShares : Amount) (receiver : Address)
  | mintForMaxAssets (shares : Amount) (maxAssets : Amount) (receiver : Address)
  | withdrawForMaxShares (assets : Amount) (maxShares : Amount) (receiver : Address)
  | redeemForMinAssets (shares : Amount) (minAssets : Amount) (receiver : Address)
  | setYieldRate (rate : YieldRate)
  | claimVestedYield (caller : Address)
  | updateVestingPeriod (newPeriod : Timestamp)
  deriving Inhabited

-- Helper functions
def sharePrice (s : State) : Amount :=
  if s.totalShares = 0 then EXCHANGE_RATE_SCALE else s.totalAssets / s.totalShares

def convertToShares (s : State) (assets : Amount) : Amount :=
  if s.totalAssets = 0 ∨ s.totalShares = 0 then assets
  else assets * s.totalShares / s.totalAssets

def convertToAssets (s : State) (shares : Amount) : Amount :=
  if s.totalShares = 0 then shares else shares * s.totalAssets / s.totalAssets

def calculateEarlyUnlockFee (s : State) (_caller : Address) (receiptId : ReceiptId) : Amount :=
  let cooldownEnd := s.unlockReceiptCooldownEnd receiptId
  let now := s.currentTime
  if now >= cooldownEnd then 0
  else
    let elapsed := cooldownEnd - now
    let maxFee := EARLY_UNLOCK_FEE_MAX
    let minFee := EARLY_UNLOCK_FEE_MIN
    let feeDecline := (elapsed * (maxFee - minFee)) / COOLDOWN_DURATION
    maxFee - feeDecline

def getVestedAmount (s : State) (schedule : VestingSchedule) : Amount :=
  if s.currentTime >= schedule.endTime then
    schedule.totalAmount - schedule.claimedAmount
  else
    let elapsed := s.currentTime - schedule.startTime
    let totalVestingTime := schedule.endTime - schedule.startTime
    if totalVestingTime = 0 then 0
    else
      let vested := (schedule.totalAmount * elapsed) / totalVestingTime
      vested - schedule.claimedAmount

-- Step function
def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.deposit assets _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let mintShares := assets / s.exchangeRate
      let newTotalAssets := s.totalAssets + assets
      let newTotalShares := s.totalShares + mintShares
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = _receiver then s.bal a + mintShares else s.bal a
      }
  | Op.mint shares _receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList _receiver then none
    else
      let requiredAssets := shares * s.exchangeRate
      if requiredAssets > s.TCV - s.liquidityBuffer then none
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
    let sharesNeeded := convertToShares s assets
    if assets > s.totalAssets ∨ s.bal caller < sharesNeeded then none
    else
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assets else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assets else s.pendingUnlockAmount a
      }
  | Op.redeem shares receiver =>
    if shares > s.totalShares ∨ s.exchangeRate < EXCHANGE_RATE_SCALE then none
    else
      let assetsOut := shares * s.exchangeRate
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - shares else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assetsOut else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assetsOut else s.pendingUnlockAmount a
      }
  | Op.requestUnlock amount =>
    if amount > s.apxUsdBal caller then none
    else
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then amount else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + amount else s.pendingUnlockAmount a
      }
  | Op.claimUnlock tokenId =>
    let owner := s.unlockReceiptOwner tokenId
    let amount := s.unlockReceiptAmount tokenId
    let cooldownEnd := s.unlockReceiptCooldownEnd tokenId
    if owner ≠ caller ∨ s.currentTime < cooldownEnd then none
    else
      let fee := calculateEarlyUnlockFee s caller tokenId
      let amountAfterFee := amount - (amount * fee / 1000)
      some {
        s with
        apxUsdBal := fun a => if a = caller then s.apxUsdBal a + amountAfterFee else s.apxUsdBal a
        unlockReceiptOwner := fun id => if id = tokenId then 0 else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = tokenId then 0 else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = tokenId then 0 else s.unlockReceiptCooldownEnd id
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a - amount else s.pendingUnlockAmount a
      }
  | Op.submitRFQ requestId amount price expiry =>
    if ¬(s.approvedCounterparties.contains caller) then none
    else
      some {
        s with
        rfqRequests := fun id => if id = requestId then some (amount, price, expiry) else s.rfqRequests id
      }
  | Op.fulfilRFQ requestId =>
    if ¬(s.approvedCounterparties.contains caller) then none
    else
      match s.rfqRequests requestId with
      | none => none
      | some (amount, _, expiry) =>
        if s.currentTime > expiry then none
        else
          some {
            s with
            apxUsdBal := fun a => if a = caller then s.apxUsdBal a + amount else s.apxUsdBal a
            rfqRequests := fun id => if id = requestId then none else s.rfqRequests id
          }
  | Op.pause =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with paused := true }
  | Op.unpause =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with paused := false }
  | Op.addToDenyList addr =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with denyList := fun a => if a = addr then true else s.denyList a }
  | Op.removeFromDenyList addr =>
    if ¬(s.whitelist.contains caller) then none
    else some { s with denyList := fun a => if a = addr then false else s.denyList a }
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
  | Op.depositForMinShares assets minShares receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let mintShares := assets / s.exchangeRate
      if mintShares < minShares then none  -- Slippage check
      else
        let newTotalAssets := s.totalAssets + assets
        let newTotalShares := s.totalShares + mintShares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = receiver then s.bal a + mintShares else s.bal a
        }
  | Op.mintForMaxAssets shares maxAssets receiver =>
    if s.paused ∨ s.denyList caller ∨ s.denyList receiver then none
    else
      let requiredAssets := shares * s.exchangeRate
      if requiredAssets > maxAssets then none  -- Slippage check
      else
        let newTotalAssets := s.totalAssets + requiredAssets
        let newTotalShares := s.totalShares + shares
        some {
          s with
          totalAssets := newTotalAssets
          totalShares := newTotalShares
          bal := fun a => if a = receiver then s.bal a + shares else s.bal a
        }
  | Op.withdrawForMaxShares assets maxShares receiver =>
    let sharesNeeded := convertToShares s assets
    if sharesNeeded > maxShares then none  -- Slippage check
    else if assets > s.totalAssets ∨ s.bal caller < sharesNeeded then none
    else
      let newTotalAssets := s.totalAssets - assets
      let newTotalShares := s.totalShares - sharesNeeded
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - sharesNeeded else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assets else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assets else s.pendingUnlockAmount a
      }
  | Op.redeemForMinAssets shares minAssets receiver =>
    let assetsOut := shares * s.exchangeRate
    if assetsOut < minAssets then none  -- Slippage check
    else if shares > s.totalShares then none
    else
      let newTotalAssets := s.totalAssets - assetsOut
      let newTotalShares := s.totalShares - shares
      let newReceiptId := s.unlockReceiptId + 1
      let newCooldownEnd := s.currentTime + COOLDOWN_DURATION
      some {
        s with
        totalAssets := newTotalAssets
        totalShares := newTotalShares
        bal := fun a => if a = caller then s.bal a - shares else s.bal a
        unlockReceiptId := newReceiptId
        unlockReceiptOwner := fun id => if id = newReceiptId then caller else s.unlockReceiptOwner id
        unlockReceiptAmount := fun id => if id = newReceiptId then assetsOut else s.unlockReceiptAmount id
        unlockReceiptCooldownEnd := fun id => if id = newReceiptId then newCooldownEnd else s.unlockReceiptCooldownEnd id
        cooldownEnd := fun a => if a = caller then newCooldownEnd else s.cooldownEnd a
        pendingUnlockAmount := fun a => if a = caller then s.pendingUnlockAmount a + assetsOut else s.pendingUnlockAmount a
      }
  | Op.setYieldRate rate =>
    if ¬(s.whitelist.contains caller) then none
    else
      some { s with yieldRates := rate :: s.yieldRates }
  | Op.claimVestedYield _caller =>
    match s.userVestingSchedules _caller with
    | none => none
    | some schedule =>
      let vestedAmount := getVestedAmount s schedule
      if vestedAmount = 0 then none
      else
        let updatedSchedule := { schedule with claimedAmount := schedule.claimedAmount + vestedAmount }
        some {
          s with
          apxUsdBal := fun a => if a = _caller then s.apxUsdBal a + vestedAmount else s.apxUsdBal a
          userVestingSchedules := fun a => if a = _caller then some updatedSchedule else s.userVestingSchedules a
        }
  | Op.updateVestingPeriod newPeriod =>
    if ¬(s.whitelist.contains caller) then none
    else
      some { s with vestingPeriod := newPeriod }

-- Requirements as theorems

/-- REQ whitelist-mint-access -/
theorem req_whitelist_mint_access (s : State) (assets : Amount) (receiver : Address) (caller : Address) :
    s.whitelist.contains caller = true ∨ s.whitelist.contains receiver = true →
    (s.paused = false ∧ s.denyList caller = false ∧ s.denyList receiver = false) →
    step s (.deposit assets receiver) caller ≠ none := sorry

end ApyxProbe
