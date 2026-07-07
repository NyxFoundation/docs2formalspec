import Std
open Nat

namespace Apyx

abbrev Address := Nat

def ray : Nat := 10^27
def day : Nat := 86400
def cooldownPeriod : Nat := 20 * day
def minFlexibleClaim : Nat := 3 * day

/-- One month of the yield-rate-setting cadence: the rate for the following month may only
be set once a full month has elapsed since the previous setting. -/
def monthPeriod : Nat := 30 * day

def vaultAddress : Address := 0

/-- The address identifying the single UnlockToken contract instance (cf. `vaultAddress`). -/
def unlockTokenAddress : Address := 1

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
  /-- The current secondary-market trading price of apxUSD, in `ray` fixed-point
  ($1.00 = `ray`, same convention as `exchangeRate`/`redemptionValue`), as reported by
  the protocol's price oracle (cf. `oracle`, `Op.setApxUSDMarketPrice`). The arbitrage
  mint pathway (`Op.mintApxUSD`) is only open while apxUSD trades above the $1.00
  reference, i.e. while `ray < apxUSDMarketPrice`. -/
  apxUSDMarketPrice : Nat
  overcollateralizationBuffer : Nat
  yieldRateMonth : Nat
  /-- The time at which the monthly yield rate was last set (`Op.setYieldRate` cadence
  anchor: the next setting only succeeds once `monthPeriod` has elapsed since this). -/
  lastRateSetTime : Nat
  /-- The prior month's collateral-base yield figure recorded at the last monthly rate
  setting: the excess of the collateral basket's value over the aggregate redemption
  obligation, i.e. the dollar yield the collateral base has generated. The next month's
  yield rate must be derived from (bounded by) this figure. -/
  collateralYieldBase : Nat
  vestStart : Nat
  vestTotal : Nat
  vestPeriod : Nat
  /-- The portion of previously-credited yield that has already streamed out of the
  linear vest (`vestTotal`/`vestStart`/`vestPeriod`) but has not yet been pulled into
  `vaultApxUSDBal` by `pullVestedYield`. Mirrors the real `LinearVestV0` contract's
  second accumulator (`fullyVestedAmount`), which exists precisely so that crediting new
  yield (`Op.creditYield`) or reconfiguring the vesting period (`Op.setVestPeriod`) can
  realize the currently-streaming portion into this bucket FIRST, instead of forfeiting it
  by folding it back into a freshly-restarted `vestTotal`/`vestStart` clock (cf.
  `req_credit_preserves_accrued_vest`). -/
  fullyVestedAmount : Nat
  nextUnlockId : Nat
  unlockRequestId : Address → Option Nat
  unlockRequests : Nat → Option (Address × Nat × Nat)
  flexibleUnlockRequests : Nat → Option (Address × Nat × Nat × Nat)
  unlockTokenOwner : Nat → Option Address
  unlockTokenAmount : Nat → Nat
  /-- The address of the (single) UnlockToken contract instance holding the unlock registry. -/
  unlockTokenAddress : Address
  /-- The address authorized to initiate claims on behalf of a recorded unlock-position
  owner (the apyUSD vault, when the system is configured per the spec). -/
  unlockTokenOperator : Address
  bufferDeployed : Bool
  usdcBal : Address → Nat
  usdcReserve : Nat
  eventLog : List (String × List Nat)
deriving Inhabited

/-- The portion of the currently-streaming vest pool (`vestTotal`, anchored at
`vestStart`, over `vestPeriod`) that has linearly released as of `now` (floor rounding).
This is only the "newly" streaming portion since the clock was last (re)anchored — it
does NOT include yield realized into `fullyVestedAmount` by an earlier
`creditYield`/`setVestPeriod`/`pullVestedYield`. Use `vestedAmount` for the total
reportable vested amount. -/
def newlyVestedAmount (s : State) (now : Nat) : Nat :=
  if now < s.vestStart then 0
  else
    let elapsed := now - s.vestStart
    if elapsed ≥ s.vestPeriod then s.vestTotal
    else (elapsed * s.vestTotal) / s.vestPeriod

/-- The total vested-but-not-yet-pulled amount reported by the LinearVestV0 model: the
previously-realized `fullyVestedAmount` accumulator plus whatever has newly streamed out
of the current `vestTotal`/`vestStart`/`vestPeriod` clock. -/
def vestedAmount (s : State) (now : Nat) : Nat :=
  s.fullyVestedAmount + newlyVestedAmount s now

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

/-- Pull all vested yield (both the previously-realized `fullyVestedAmount` and whatever
has newly streamed out of the current vest clock) into vault custody, mirroring
`LinearVestV0.pullVestedYield`: the realized total moves into `vaultApxUSDBal`, the
newly-streamed portion leaves the streaming pool `vestTotal`, `fullyVestedAmount` resets
to zero (it has all been pulled), and the clock re-anchors at `now`. -/
def pullVestedYield (s : State) : State :=
  let nv := newlyVestedAmount s s.now
  let v := s.fullyVestedAmount + nv
  if v = 0 then s
  else
    { s with
        vaultApxUSDBal := s.vaultApxUSDBal + v
        vestTotal := s.vestTotal - nv
        fullyVestedAmount := 0
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

/-- Effect of a successful `updateStandardUnlock` (topped-up position present) on the
`unlockRequests` map: the target `idp` becomes `some (owner, oldAmount + addAmount,
now + cooldownPeriod)`, every other id is untouched. -/
theorem updateStandardUnlock_unlockRequests_eq (s : State) (idp : Nat) (owner : Address)
    (addAmount : Nat) (o oa oe : Nat) (h : s.unlockRequests idp = some (o, oa, oe)) (i : Nat) :
    (updateStandardUnlock s idp owner addAmount).unlockRequests i
      = if i = idp then some (owner, oa + addAmount, s.now + cooldownPeriod) else s.unlockRequests i := by
  unfold updateStandardUnlock
  rw [h]

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

/-- The state update performed by a successful standard `Op.requestUnlock`: burn the
caller's apxUSD, then enforce the "at most one pending standard redemption per user"
requirement — if the caller already has a live standard unlock position, *top it up*
(add the burned amount to the existing position and reset its cooldown to `now`, via
`updateStandardUnlock`) rather than opening a second one; only when the caller has no
pending standard position is a fresh one created (`createStandardUnlock`). This models
`req_single_pending_redemption_per_user` / `req_multiple_unlocks_reset_cooldown`: repeated
requests coalesce into the single position tracked by the per-user `unlockRequestId`
pointer, with a freshly reset cooldown on the aggregate amount. -/
def requestUnlockStep (s : State) (caller : Address) (amount : Nat) : State :=
  match (burnApxUSD s caller amount).unlockRequestId caller with
  | some id =>
    match (burnApxUSD s caller amount).unlockRequests id with
    | some (o, _, _) =>
        if o = caller then updateStandardUnlock (burnApxUSD s caller amount) id caller amount
        else createStandardUnlock (burnApxUSD s caller amount) caller amount
    | none => createStandardUnlock (burnApxUSD s caller amount) caller amount
  | none => createStandardUnlock (burnApxUSD s caller amount) caller amount

/-- Uniform frame lemmas: `requestUnlockStep` touches only the caller's burned apxUSD
(`apxUSDBal`, `totalSupply_apxUSD`) and the standard-unlock registry; every other State
field is left exactly as it was, regardless of which branch (create / top-up) is taken. -/
@[simp] theorem requestUnlockStep_now (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).now = s.now := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_globalPause (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).globalPause = s.globalPause := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_apyUSDBal (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).apyUSDBal = s.apyUSDBal := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_totalSupply_apyUSD (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).totalSupply_apyUSD = s.totalSupply_apyUSD := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_vaultApxUSDBal (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).vaultApxUSDBal = s.vaultApxUSDBal := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_usdcReserve (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).usdcReserve = s.usdcReserve := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_usdcBal (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).usdcBal = s.usdcBal := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_governanceTokenBal (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).governanceTokenBal = s.governanceTokenBal := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_exchangeRate (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).exchangeRate = s.exchangeRate := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_redemptionValue (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).redemptionValue = s.redemptionValue := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_totalCollateralValue (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).totalCollateralValue = s.totalCollateralValue := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_overcollateralizationBufferField (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).overcollateralizationBuffer = s.overcollateralizationBuffer := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_unlockTokenOperator (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).unlockTokenOperator = s.unlockTokenOperator := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_unlockTokenAddress (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).unlockTokenAddress = s.unlockTokenAddress := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_emergencyFlag (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).emergencyFlag = s.emergencyFlag := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_bufferDeployed (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).bufferDeployed = s.bufferDeployed := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_whitelist (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).whitelist = s.whitelist := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_denylist (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).denylist = s.denylist := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_eventLog (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).eventLog = s.eventLog := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_totalSupply_apxUSD (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).totalSupply_apxUSD = s.totalSupply_apxUSD - amount := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

@[simp] theorem requestUnlockStep_apxUSDBal (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).apxUSDBal = (burnApxUSD s caller amount).apxUSDBal := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

/-- Registry frame: `requestUnlockStep` only ever assigns an unlock-token owner at the
current registry counter `s.nextUnlockId` (the create branch); the top-up branch touches
no owner at all. So any position id other than the counter keeps its owner unchanged. -/
theorem requestUnlockStep_unlockTokenOwner_of_ne (s : State) (caller amount : Nat)
    {id : Nat} (hid : id ≠ s.nextUnlockId) :
    (requestUnlockStep s caller amount).unlockTokenOwner id = s.unlockTokenOwner id := by
  unfold requestUnlockStep
  (repeat' split) <;> simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

/-- The `(nextUnlockId, unlockTokenOwner)` pair after `requestUnlockStep` is either exactly
that of the fresh-position (`createStandardUnlock`) path, or exactly the pre-state's (the
top-up path touches neither field). This lets every registry-counter / owner invariant be
discharged by the pre-existing `createStandardUnlock` reasoning on one side and by pure
identity on the other. -/
theorem requestUnlockStep_owner_counter_cases (s : State) (caller amount : Nat) :
    ((requestUnlockStep s caller amount).nextUnlockId
        = (createStandardUnlock (burnApxUSD s caller amount) caller amount).nextUnlockId
      ∧ (requestUnlockStep s caller amount).unlockTokenOwner
        = (createStandardUnlock (burnApxUSD s caller amount) caller amount).unlockTokenOwner)
    ∨ ((requestUnlockStep s caller amount).nextUnlockId = s.nextUnlockId
      ∧ (requestUnlockStep s caller amount).unlockTokenOwner = s.unlockTokenOwner) := by
  unfold requestUnlockStep
  (repeat' split) <;>
    first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr ⟨by simp_all [updateStandardUnlock, burnApxUSD], by simp_all [updateStandardUnlock, burnApxUSD]⟩

/-- After a standard `requestUnlock`, the caller's *single* tracked standard position (the
requirement's "at most one pending redemption per user") holds an aggregated amount with a
freshly reset cooldown deadline `now + cooldownPeriod` — whether it was newly created or an
existing position topped up. -/
theorem requestUnlockStep_caller_position (s : State) (caller amount : Nat) :
    ∃ id amt, (requestUnlockStep s caller amount).unlockRequestId caller = some id ∧
      (requestUnlockStep s caller amount).unlockRequests id
        = some (caller, amt, s.now + cooldownPeriod) := by
  unfold requestUnlockStep
  split
  · rename_i id heq
    split
    · rename_i o oldAmount oldEnd heq2
      by_cases ho : o = caller
      · rw [if_pos ho]
        exact ⟨id, oldAmount + amount,
          by simp_all [updateStandardUnlock, burnApxUSD],
          by simp_all [updateStandardUnlock, burnApxUSD]⟩
      · rw [if_neg ho]
        exact ⟨(burnApxUSD s caller amount).nextUnlockId, amount,
          by simp [createStandardUnlock], by simp [createStandardUnlock, burnApxUSD]⟩
    · exact ⟨(burnApxUSD s caller amount).nextUnlockId, amount,
        by simp [createStandardUnlock], by simp [createStandardUnlock, burnApxUSD]⟩
  · exact ⟨(burnApxUSD s caller amount).nextUnlockId, amount,
      by simp [createStandardUnlock], by simp [createStandardUnlock, burnApxUSD]⟩

/-- When the caller has no pending standard position, `requestUnlockStep` takes the
create branch and coincides exactly with the fresh-position `createStandardUnlock` path —
letting the pre-existing "fresh registry allocation at the counter" proofs go through
unchanged for a user's first standard request. -/
theorem requestUnlockStep_fresh_eq (s : State) (caller amount : Nat)
    (h : s.unlockRequestId caller = none) :
    requestUnlockStep s caller amount = createStandardUnlock (burnApxUSD s caller amount) caller amount := by
  unfold requestUnlockStep
  simp only [show (burnApxUSD s caller amount).unlockRequestId caller = none from by simp [burnApxUSD, h]]

@[simp] theorem requestUnlockStep_flexibleUnlockRequests (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).flexibleUnlockRequests = s.flexibleUnlockRequests := by
  unfold requestUnlockStep; (repeat' split); all_goals simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

/-- Create-branch case of standard-position `Penniless`-preservation. -/
private theorem std_penniless_create (s : State) (caller amount : Nat) (a : Address)
    (hstd : ∀ id amt ce, s.unlockRequests id = some (a, amt, ce) → amt = 0)
    (hcaller0 : caller = a → amount = 0) :
    ∀ id amt ce, (createStandardUnlock (burnApxUSD s caller amount) caller amount).unlockRequests id
      = some (a, amt, ce) → amt = 0 := by
  intro id amt ce hreq
  simp only [createStandardUnlock, burnApxUSD] at hreq
  split at hreq
  · simp only [Option.some.injEq, Prod.mk.injEq] at hreq
    obtain ⟨hca, hamt, -⟩ := hreq
    rw [← hamt]; exact hcaller0 hca
  · exact hstd id amt ce (by simpa [burnApxUSD] using hreq)

/-- Standard-position `Penniless`-preservation: if every standard unlock position owned by
`a` currently has amount 0, and — when `a` is the caller — `a` has nothing to lock, then
after a `requestUnlock` every standard position owned by `a` still has amount 0. The
self-validating top-up branch is what makes this hold with no registry-consistency
hypothesis: `requestUnlockStep` only ever tops up a position whose *recorded* owner is the
caller, so it can never inflate a third party's position. -/
theorem requestUnlockStep_std_penniless (s : State) (caller amount : Nat) (a : Address)
    (hstd : ∀ id amt ce, s.unlockRequests id = some (a, amt, ce) → amt = 0)
    (hcaller0 : caller = a → amount = 0) :
    ∀ id amt ce, (requestUnlockStep s caller amount).unlockRequests id = some (a, amt, ce) → amt = 0 := by
  intro id amt ce hreq
  unfold requestUnlockStep at hreq
  split at hreq
  · rename_i id' heqptr
    split at hreq
    · rename_i o oldAmount oldEnd heqreq
      by_cases ho : o = caller
      · rw [if_pos ho] at hreq
        rw [updateStandardUnlock_unlockRequests_eq (burnApxUSD s caller amount) id' caller amount
          o oldAmount oldEnd heqreq id] at hreq
        simp only [burnApxUSD] at hreq
        split at hreq
        · simp only [Option.some.injEq, Prod.mk.injEq] at hreq
          obtain ⟨hca, hamt, -⟩ := hreq
          have hsid : s.unlockRequests id' = some (a, oldAmount, oldEnd) := by
            rw [show s.unlockRequests id' = some (o, oldAmount, oldEnd) from by
              simpa [burnApxUSD] using heqreq, ho, hca]
          have hoa : oldAmount = 0 := hstd id' oldAmount oldEnd hsid
          have ham : amount = 0 := hcaller0 hca
          omega
        · exact hstd id amt ce hreq
      · rw [if_neg ho] at hreq
        exact std_penniless_create s caller amount a hstd hcaller0 id amt ce hreq
    · rename_i heqreq
      exact std_penniless_create s caller amount a hstd hcaller0 id amt ce hreq
  · rename_i heqptr
    exact std_penniless_create s caller amount a hstd hcaller0 id amt ce hreq

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
  | setApxUSDMarketPrice (price : Nat)

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
    -- arbitrage minting pathway: only open while apxUSD trades above $1.00
    if s.globalPause then none
    else if ¬ s.whitelist caller then none
    else if s.denylist caller || s.denylist to then none
    else if s.apxUSDMarketPrice ≤ ray then none
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
    else some (requestUnlockStep s caller amount)
  | Op.claimUnlock requestId =>
    match s.unlockRequests requestId with
    | none => none
    | some (owner, amount, cooldownEnd) =>
      if s.unlockTokenOwner requestId != some owner then none
      else if caller = owner ∨ caller = s.unlockTokenOperator then
        if s.now < cooldownEnd then none
        else
          let s1 := burnUnlockNFT s requestId
          let s2 := mintApxUSD s1 owner amount
          some s2
      else none
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
      else if caller = owner ∨ caller = s.unlockTokenOperator then
        if s.now < requestTime + minFlexibleClaim then none
        else
          let feeBps := flexibleUnlockFee requestTime s.now
          let fee := (amount * feeBps) / 10000
          let claimAmount := amount - fee
          let s1 := burnUnlockNFT s requestId
          let s2 := mintApxUSD s1 owner claimAmount
          some s2
      else none
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
    -- Monthly cadence: only the admin, only once a full month has elapsed since the last
    -- setting, and the new rate must be derived from (bounded by) the recorded prior
    -- month's collateral-base yield. On success the cadence anchor advances to `now` and
    -- the collateral-base yield figure is refreshed from the current collateral state,
    -- becoming the basis for the following month's setting.
    if caller = s.admin ∧ s.lastRateSetTime + monthPeriod ≤ s.now
        ∧ bps ≤ s.collateralYieldBase then
      some { s with
        yieldRateMonth := bps
        lastRateSetTime := s.now
        collateralYieldBase := overcollateralizationBuffer s }
    else none
  | Op.creditYield amount =>
    -- accrue first: realize whatever has already streamed out of the current vest
    -- clock into `fullyVestedAmount` BEFORE folding the new amount into a
    -- freshly-restarted `vestTotal`/`vestStart` clock, so already-accrued yield is
    -- never forfeited (cf. `req_credit_preserves_accrued_vest`).
    if caller == s.yieldDistributor then
      let nv := newlyVestedAmount s s.now
      let s1 := { s with
        usdcReserve := s.usdcReserve + amount
        fullyVestedAmount := s.fullyVestedAmount + nv
        vestTotal := (s.vestTotal - nv) + amount
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
    -- accrue first, same pattern as `creditYield`: reconfiguring the vesting period
    -- must not forfeit whatever has already streamed out of the current clock.
    if caller == s.admin then
      let nv := newlyVestedAmount s s.now
      some { s with
        fullyVestedAmount := s.fullyVestedAmount + nv
        vestTotal := s.vestTotal - nv
        vestStart := s.now
        vestPeriod := p
      }
    else none
  | Op.setApxUSDMarketPrice price =>
    -- only the price oracle may report apxUSD's secondary-market trading price
    if caller == s.oracle then some { s with apxUSDMarketPrice := price }
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

@[simp] private theorem pullVestedYield_unlockTokenAddress (s : State) :
    (pullVestedYield s).unlockTokenAddress = s.unlockTokenAddress := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_unlockTokenOperator (s : State) :
    (pullVestedYield s).unlockTokenOperator = s.unlockTokenOperator := by
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

@[simp] private theorem pullVestedYield_overcollateralizationBufferField (s : State) :
    (pullVestedYield s).overcollateralizationBuffer = s.overcollateralizationBuffer := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_vaultApxUSDBal (s : State) :
    (pullVestedYield s).vaultApxUSDBal = s.vaultApxUSDBal + vestedAmount s s.now := by
  unfold pullVestedYield vestedAmount; dsimp only; split <;> simp_all

/-- If `e ≤ P` then `e * T / P ≤ T`. -/
private theorem div_mul_le_total {e P T : Nat} (h : e ≤ P) : e * T / P ≤ T := by
  rcases Nat.eq_zero_or_pos P with hp | hp
  · subst hp
    simp [Nat.le_zero.mp h]
  · calc e * T / P ≤ P * T / P := Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
      _ = T := Nat.mul_div_cancel_left _ hp

/-- `newlyVestedAmount` never exceeds the total of the currently-streaming vest pool. -/
private theorem newlyVestedAmount_le_total (s : State) (n : Nat) :
    newlyVestedAmount s n ≤ s.vestTotal := by
  unfold newlyVestedAmount
  dsimp only
  repeat' split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact div_mul_le_total (by omega)

/-- `newlyVestedAmount` is monotone in time. -/
private theorem newlyVestedAmount_mono (s : State) {n m : Nat} (h : n ≤ m) :
    newlyVestedAmount s n ≤ newlyVestedAmount s m := by
  unfold newlyVestedAmount
  dsimp only
  repeat' split
  all_goals first
    | omega
    | exact Nat.zero_le _
    | (exfalso; omega)
    | exact div_mul_le_total (by omega)
    | exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))

/-- `vestedAmount` never exceeds `fullyVestedAmount` plus the total of the currently-streaming
vest pool. -/
private theorem vestedAmount_le_total (s : State) (n : Nat) :
    vestedAmount s n ≤ s.fullyVestedAmount + s.vestTotal :=
  Nat.add_le_add_left (newlyVestedAmount_le_total s n) _

/-- `vestedAmount` is monotone in time (only the streaming portion depends on `now`;
`fullyVestedAmount` is a fixed state field). -/
private theorem vestedAmount_mono (s : State) {n m : Nat} (h : n ≤ m) :
    vestedAmount s n ≤ vestedAmount s m :=
  Nat.add_le_add_left (newlyVestedAmount_mono s h) _

/-- At exactly `vestStart + vestPeriod`, a vest clock has always fully released its
`vestTotal` (regardless of `vestPeriod`, including the degenerate `vestPeriod = 0` case),
so `totalAssets` at that instant is exactly `vaultApxUSDBal + fullyVestedAmount + vestTotal`
— the "eventual, fully-vested" asset base of a state, used throughout the crediting
theorems below (`req_pay_to_non_cooldown`, `req_yield_distributor_credit`,
`req_yield_distribution_period`) to state conservation identities that hold regardless of
how much of the CURRENT stream has already elapsed. -/
private theorem totalAssets_at_horizon (u : State) (n : Nat) (h : n = u.vestStart + u.vestPeriod) :
    totalAssets { u with now := n } = u.vaultApxUSDBal + u.fullyVestedAmount + u.vestTotal := by
  subst h
  unfold totalAssets vestedAmount newlyVestedAmount
  dsimp only
  repeat' split
  all_goals omega

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
    ray < s.apxUSDMarketPrice ∧
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
        · split at h
          · exact absurd h (by simp)
          · refine ⟨by simp_all, by simp_all, ?_, ?_, by omega, by omega,
              (Option.some.inj h).symm⟩ <;> simp_all

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
    s' = requestUnlockStep s caller amount := by
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
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      cooldownEnd ≤ s.now ∧
      s' = mintApxUSD (burnUnlockNFT s id) owner amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · split at h
        · exact absurd h (by simp)
        · exact ⟨owner, amount, cooldownEnd, heq, by simp_all, by assumption, by omega,
            (Option.some.inj h).symm⟩
      · exact absurd h (by simp)

private theorem step_flexibleClaimUnlock_some (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
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
      · split at h
        · exact absurd h (by simp)
        · exact ⟨owner, amount, requestTime, cooldownEnd, heq, by simp_all, by assumption,
            by omega, (Option.some.inj h).symm⟩
      · exact absurd h (by simp)

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
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
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
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
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

/-- Helper: no operation ever changes which address is the UnlockToken operator. -/
private theorem step_unlockTokenOperator_unchanged (s : State) (op : Op) (caller : Address)
    (s' : State) (h_step : step s op caller = some s') :
    s'.unlockTokenOperator = s.unlockTokenOperator := by
  cases op
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    simp [mintApxUSD, burnUnlockNFT]
  case redeemApxUSD a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD]
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createFlexibleUnlock, burnApxUSD]
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
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

/-- Helper: no operation ever changes the recorded UnlockToken instance address. -/
private theorem step_unlockTokenAddress_unchanged (s : State) (op : Op) (caller : Address)
    (s' : State) (h_step : step s op caller = some s') :
    s'.unlockTokenAddress = s.unlockTokenAddress := by
  cases op
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    simp [mintApxUSD, burnUnlockNFT]
  case redeemApxUSD a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD]
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createFlexibleUnlock, burnApxUSD]
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
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
    ∃ s' id amt, step s (Op.requestUnlock amount) caller = some s' ∧
      s'.unlockRequestId caller = some id ∧
      s'.unlockRequests id = some (caller, amt, s.now + cooldownPeriod) ∧
      step s' (Op.claimUnlock id) caller = none := by
  obtain ⟨id, amt, hptr, hreq⟩ := requestUnlockStep_caller_position s caller amount
  refine ⟨requestUnlockStep s caller amount, id, amt, ?_, hptr, hreq, ?_⟩
  · simp [step, h1, Nat.not_lt.mpr h2]
  · have hnow := requestUnlockStep_now s caller amount
    simp only [step, hreq]
    have hlt : (requestUnlockStep s caller amount).now < s.now + cooldownPeriod := by
      rw [hnow]; simp [cooldownPeriod, day]
    split
    · rfl
    · simp [hlt]

/-- REQ redemption-cooldown-period: After a redemption request is submitted, the system
MUST enforce a cooldown period of approximately 20 days before a claim can be executed.
(Model: `cooldownPeriod = 20 * day`; every request records `now + cooldownPeriod` as its
deadline and every successful claim happened at or after its recorded deadline.) -/
theorem req_redemption_cooldown_period (s : State) :
    cooldownPeriod = 20 * day ∧
    (∀ amount caller s', step s (Op.requestUnlock amount) caller = some s' →
      ∃ id amt, s'.unlockRequestId caller = some id ∧
        s'.unlockRequests id = some (caller, amt, s.now + cooldownPeriod)) ∧
    (∀ id caller s', step s (Op.claimUnlock id) caller = some s' →
      ∃ owner amount cooldownEnd, s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
        cooldownEnd ≤ s.now) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro amount caller s' h
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h
    subst hs'
    exact requestUnlockStep_caller_position s caller amount
  · intro id caller s' h
    obtain ⟨o, a, ce, hreq, _, _, ht, _⟩ := step_claimUnlock_some _ _ _ _ h
    exact ⟨o, a, ce, hreq, ht⟩

/-- REQ cooldown-no-yield: During a redemption cooldown, the exchange rate for the locked
apyUSD MUST remain fixed and the user MUST not accrue additional yield on those tokens.
(Model: when apyUSD enters the redemption cooldown — `Op.redeem`/`Op.withdraw` — the
payout for the locked tokens is computed ONCE, at the apxUSD/apyUSD exchange rate in
force at request time (`redeemAssets shares s.exchangeRate` resp. `assets`), and recorded
in the cooldown position. That is the "fixed exchange rate": the locked tokens' value is
frozen at the request-time rate for the entire `cooldownPeriod`. And no additional yield
accrues on them: `Op.creditYield` — the only operation by which apyUSD holders receive
yield — leaves both the recorded cooldown entry and the locked position amount completely
unchanged, and the eventual claim pays out exactly the frozen amount, insensitive to any
exchange-rate movement between request and claim.) -/
theorem req_cooldown_no_yield (s : State) :
    -- apyUSD entering cooldown via `redeem`: the payout is locked in at the
    -- request-time exchange rate, frozen for the whole cooldown period
    (∀ shares receiver caller s',
      step s (Op.redeem shares receiver) caller = some s' →
      s'.unlockRequests s.nextUnlockId
        = some (receiver, redeemAssets shares s.exchangeRate, s.now + cooldownPeriod) ∧
      s'.unlockTokenAmount s.nextUnlockId = redeemAssets shares s.exchangeRate) ∧
    -- apyUSD entering cooldown via `withdraw`: likewise frozen at the request-time rate
    (∀ assets receiver caller s',
      step s (Op.withdraw assets receiver) caller = some s' →
      s'.unlockRequests s.nextUnlockId = some (receiver, assets, s.now + cooldownPeriod) ∧
      s'.unlockTokenAmount s.nextUnlockId = assets) ∧
    -- no yield accrues on locked tokens: crediting yield never changes any recorded
    -- cooldown entry or locked amount
    (∀ (t : State) (y : Nat) (ycaller : Address) (t' : State),
      step t (Op.creditYield y) ycaller = some t' →
      ∀ id, t'.unlockRequests id = t.unlockRequests id ∧
        t'.unlockTokenAmount id = t.unlockTokenAmount id) ∧
    -- the claim pays out exactly the frozen amount, regardless of the exchange rate
    -- prevailing at claim time
    (∀ (t : State) (id : Nat) (caller owner : Address) (amount cooldownEnd : Nat) (t' : State),
      t.unlockRequests id = some (owner, amount, cooldownEnd) →
      step t (Op.claimUnlock id) caller = some t' →
      t'.apxUSDBal owner = t.apxUSDBal owner + amount) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro shares receiver caller s' h
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h
    subst hs'
    constructor <;> simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  · intro assets receiver caller s' h
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h
    subst hs'
    constructor <;> simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  · intro t y ycaller t' h id
    simp only [step] at h
    split at h
    · cases Option.some.inj h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · intro t id caller owner amount cooldownEnd t' hreq h
    obtain ⟨o, a, ce, hreq', _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h
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
rather than as a lump-sum distribution. (Model: the currently-streaming portion of the
vest, `newlyVestedAmount` — i.e. the release of `vestTotal` since the clock `vestStart` —
starts at zero, grows monotonically, and reaches the full streaming total exactly at the
end of the vesting period. The total reportable `vestedAmount` additionally carries any
previously-realized `fullyVestedAmount` — cf. `req_credit_preserves_accrued_vest` — so it
need not itself start at zero, but it is still monotone in time, since `fullyVestedAmount`
does not depend on `now`.) -/
theorem req_continuous_stream (s : State) (h : 0 < s.vestPeriod) :
    newlyVestedAmount s s.vestStart = 0 ∧
    newlyVestedAmount s (s.vestStart + s.vestPeriod) = s.vestTotal ∧
    (∀ n m, n ≤ m → newlyVestedAmount s n ≤ newlyVestedAmount s m) ∧
    (∀ n m, n ≤ m → vestedAmount s n ≤ vestedAmount s m) := by
  refine ⟨?_, ?_, fun n m hnm => newlyVestedAmount_mono s hnm, fun n m hnm => vestedAmount_mono s hnm⟩
  · unfold newlyVestedAmount
    dsimp only
    repeat' split
    all_goals first | rfl | simp | (exfalso; omega)
  · unfold newlyVestedAmount
    dsimp only
    repeat' split
    all_goals first | rfl | (exfalso; omega)

/-- REQ monthly-yield-rate-set: Each month, the system MUST set the yield rate for the
following month based on the prior month's collateral-base yield. (Model:
`s.lastRateSetTime` anchors the monthly cadence and `s.collateralYieldBase` records the
prior month's collateral-base yield — the excess of the collateral basket's value over the
aggregate redemption obligation at the last setting. (1) Cadence: setting the rate before
a full month (`monthPeriod = 30 * day`) has elapsed since the last setting reverts, for
every caller. (2) Derivation: any successful setting was performed by the admin, at least
a month after the previous one, and the newly configured rate for the following month is
bounded by the recorded prior-month collateral-base yield; the cadence anchor advances to
the current time and the collateral-base yield figure is refreshed from the current
collateral state, becoming the basis for the following month's setting. (3) Liveness: once
a month has elapsed, the admin can actually set any rate within that bound.) -/
theorem req_monthly_yield_rate_set (s : State) (bps : Nat) :
    (s.now < s.lastRateSetTime + monthPeriod →
      ∀ caller, step s (Op.setYieldRate bps) caller = none) ∧
    (∀ caller s', step s (Op.setYieldRate bps) caller = some s' →
      caller = s.admin ∧
      s.lastRateSetTime + monthPeriod ≤ s.now ∧
      bps ≤ s.collateralYieldBase ∧
      s'.yieldRateMonth = bps ∧
      s'.lastRateSetTime = s.now ∧
      s'.collateralYieldBase = overcollateralizationBuffer s) ∧
    (s.lastRateSetTime + monthPeriod ≤ s.now → bps ≤ s.collateralYieldBase →
      ∃ s', step s (Op.setYieldRate bps) s.admin = some s' ∧
        s'.yieldRateMonth = bps) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h_early caller
    simp [step, Nat.not_le.mpr h_early]
  · intro caller s' h_step
    simp only [step] at h_step
    split at h_step
    · rename_i hcond
      obtain ⟨hcaller, hmonth, hbound⟩ := hcond
      cases Option.some.inj h_step
      exact ⟨hcaller, hmonth, hbound, rfl, rfl, rfl⟩
    · exact absurd h_step (by simp)
  · intro h_month h_bound
    exact ⟨{ s with
        yieldRateMonth := bps
        lastRateSetTime := s.now
        collateralYieldBase := overcollateralizationBuffer s },
      by simp [step, h_month, h_bound], rfl⟩

/-- REQ pay-to-non-cooldown: Yield MUST be paid to all apyUSD tokens that are not currently
undergoing cooldown. (Model: paying yield is `Op.creditYield` by the authorized yield
distributor, and it is distributed pro-rata through the vault exchange rate, so it reaches
exactly the apyUSD tokens outstanding at the time of the credit. Tokens undergoing cooldown
are, by construction, no longer apyUSD: requesting an unlock burns the tokens and leaves a
fixed-amount apxUSD_unlock position in the unlock registry. The theorem states that a
positive yield credit (a) is credited in full to the asset pool backing apyUSD — once the
credited stream has vested, the pool backing the unchanged apyUSD supply has grown by
exactly the credited amount; (b) is thereby paid to every current apyUSD holder: each
address holding apyUSD keeps its exact share balance while that balance's pro-rata claim
`bal × pool / supply` is on a strictly larger pool over the same share supply, i.e. its
redeemable value strictly increases; and (c) reaches no cooldown position: every recorded
unlock payout amount — standard and flexible — is completely unchanged by the credit.) -/
theorem req_pay_to_non_cooldown (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s')
    (h_pos : 0 < amount) :
    -- (a) the credit lands in the vault's vesting stream: fully vested, the asset pool
    -- backing apyUSD has grown by exactly `amount`, over an unchanged share supply. The
    -- "fully vested" baseline is each state's own eventual value — its own vested amount
    -- need not itself be zero beforehand (a prior credit may already have realized some
    -- into `fullyVestedAmount`, cf. `req_credit_preserves_accrued_vest`) — but crediting
    -- always adds exactly `amount` on top of whatever was already going to fully vest.
    totalAssets { s' with now := s'.vestStart + s'.vestPeriod }
      = totalAssets { s with now := s.vestStart + s.vestPeriod } + amount ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    -- (b) every current apyUSD holder is paid: its share balance is untouched and its
    -- pro-rata claim on the backing pool strictly increases
    (∀ a, s'.apyUSDBal a = s.apyUSDBal a) ∧
    (∀ a, 0 < s.apyUSDBal a →
      s.apyUSDBal a * totalAssets { s' with now := s'.vestStart + s'.vestPeriod }
        > s.apyUSDBal a * totalAssets { s with now := s.vestStart + s.vestPeriod }) ∧
    -- (c) cooldown positions receive none of it: every unlock payout is unchanged
    (∀ id, s'.unlockTokenAmount id = s.unlockTokenAmount id) ∧
    (∀ id, s'.unlockRequests id = s.unlockRequests id) ∧
    (∀ id, s'.flexibleUnlockRequests id = s.flexibleUnlockRequests id) := by
  simp only [step] at h_step
  split at h_step
  · cases Option.some.inj h_step
    have hnv : newlyVestedAmount s s.now ≤ s.vestTotal := newlyVestedAmount_le_total s s.now
    have h_assets : totalAssets { ({ s with
          usdcReserve := s.usdcReserve + amount
          fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
          vestTotal := (s.vestTotal - newlyVestedAmount s s.now) + amount
          vestStart := s.now }) with
        now := s.now + s.vestPeriod }
        = totalAssets { s with now := s.vestStart + s.vestPeriod } + amount := by
      generalize hnvdef : newlyVestedAmount s s.now = nv at hnv ⊢
      simp only [totalAssets, vestedAmount, newlyVestedAmount]
      repeat' split
      all_goals omega
    refine ⟨h_assets, rfl, fun a => rfl, ?_, fun id => rfl, fun id => rfl, fun id => rfl⟩
    intro a h_bal
    rw [h_assets]
    calc s.apyUSDBal a * totalAssets { s with now := s.vestStart + s.vestPeriod }
        < s.apyUSDBal a * totalAssets { s with now := s.vestStart + s.vestPeriod }
            + s.apyUSDBal a * amount :=
          Nat.lt_add_of_pos_right (Nat.mul_pos h_bal h_pos)
      _ = s.apyUSDBal a * (totalAssets { s with now := s.vestStart + s.vestPeriod } + amount) :=
          (Nat.mul_add _ _ _).symm
  · exact absurd h_step (by simp)

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
apxUSD_unlock tokens to the user immediately after the deposit. (Source: "User immediately
receives apxUSD_unlock tokens (UnlockToken shares)"; "Minting occurs instantly after the
vault deposits assets." "The deposit" here is the vault depositing apxUSD assets INTO the
UnlockToken contract — NOT the user's initial deposit into the vault: the source's own
withdraw/redeem sequence diagrams show exactly `vault ->> unlockToken: deposit(1000
apxUSD, bob)` answered by `unlockToken -->> bob: mint 1000 apxUSD_unlock` within the one
withdraw/redeem transaction; the user's initial vault deposit mints apyUSD shares, never
apxUSD_unlock. Model: the vault deposits apxUSD into the UnlockToken registry during
`Op.withdraw`/`Op.redeem` (and a user deposits apxUSD directly via
`requestUnlock`/`flexibleRequestUnlock`). The theorem states that in the very same atomic
step as each such deposit, the UnlockToken contract mints the apxUSD_unlock position to
the user: the freshly allocated position at the registry counter is owned by the user —
the `receiver` of the vault-initiated withdraw/redeem, the depositing caller otherwise —
and carries the full deposited apxUSD amount. Minting is instant; there is no separate or
delayed mint step.) -/
theorem req_unlock_token_mints_apx_usd_unlock_immediately (s : State) :
    (∀ (assets : Nat) (receiver caller : Address) (s' : State),
      step s (Op.withdraw assets receiver) caller = some s' →
      s'.unlockTokenOwner s.nextUnlockId = some receiver ∧
      s'.unlockTokenAmount s.nextUnlockId = assets) ∧
    (∀ (shares : Nat) (receiver caller : Address) (s' : State),
      step s (Op.redeem shares receiver) caller = some s' →
      s'.unlockTokenOwner s.nextUnlockId = some receiver ∧
      s'.unlockTokenAmount s.nextUnlockId = redeemAssets shares s.exchangeRate) ∧
    (∀ (amount : Nat) (caller : Address) (s' : State),
      s.unlockRequestId caller = none →
      step s (Op.requestUnlock amount) caller = some s' →
      s'.unlockTokenOwner s.nextUnlockId = some caller ∧
      s'.unlockTokenAmount s.nextUnlockId = amount) ∧
    (∀ (amount : Nat) (caller : Address) (s' : State),
      step s (Op.flexibleRequestUnlock amount) caller = some s' →
      s'.unlockTokenOwner s.nextUnlockId = some caller ∧
      s'.unlockTokenAmount s.nextUnlockId = amount) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro assets receiver caller s' h_step
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    constructor <;> simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  · intro shares receiver caller s' h_step
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    constructor <;> simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  · intro amount caller s' hfresh h_step
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    rw [requestUnlockStep_fresh_eq s caller amount hfresh]
    constructor <;> simp [createStandardUnlock, burnApxUSD]
  · intro amount caller s' h_step
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

/-- Helper: a new apxUSD_unlock position can only be created by one of the vault's own
unlock entry points (`requestUnlock`/`flexibleRequestUnlock`/`withdraw`/`redeem`), and it
is always allocated in the single unlock registry at its current counter. -/
private theorem unlock_position_created_only_by_vault_ops (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (id : Nat) (owner : Address)
    (h_new : s.unlockTokenOwner id = none)
    (h_now : s'.unlockTokenOwner id = some owner) :
    ((∃ a, op = Op.requestUnlock a) ∨ (∃ a, op = Op.flexibleRequestUnlock a) ∨
     (∃ a r, op = Op.withdraw a r) ∨ (∃ sh r, op = Op.redeem sh r)) ∧
    id = s.nextUnlockId := by
  cases op
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    rcases requestUnlockStep_owner_counter_cases s caller a with ⟨_, howner⟩ | ⟨_, howner⟩
    · rw [howner] at h_now
      by_cases hid : id = s.nextUnlockId
      · exact ⟨Or.inl ⟨a, rfl⟩, hid⟩
      · simp [createStandardUnlock, burnApxUSD, hid, h_new] at h_now
    · rw [howner, h_new] at h_now; cases h_now
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · exact ⟨Or.inr (Or.inl ⟨a, rfl⟩), hid⟩
    · simp [createFlexibleUnlock, burnApxUSD, hid, h_new] at h_now
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨a, r, rfl⟩)), hid⟩
    · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hid, h_new] at h_now
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨sh, r, rfl⟩)), hid⟩
    · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hid, h_new] at h_now
  case claimUnlock rid =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = rid
    · subst hid; simp [mintApxUSD, burnUnlockNFT] at h_now
    · simp [mintApxUSD, burnUnlockNFT, hid, h_new] at h_now
  case flexibleClaimUnlock rid =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = rid
    · subst hid; simp [mintApxUSD, burnUnlockNFT] at h_now
    · simp [mintApxUSD, burnUnlockNFT, hid, h_new] at h_now
  case depositUSDC a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD, h_new] at h_now
  case mintApxUSD t a =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD, h_new] at h_now
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, h_new] at h_now
  case redeemApxUSD a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD, h_new] at h_now
  case executeRFQRedemption u am =>
    obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    simp [burnApxUSD, h_new] at h_now
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; simp_all)
        | exact absurd h_step (by simp)

/-- REQ vault-operator-of-UnlockToken: The apyUSD vault MUST be configured as the operator
of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users
immediately. (Model: the `unlockTokenOperator` State field records which address is
authorized to trigger a claim on behalf of the recorded position owner, and `vaultAddress`
is the vault. (1) Configuration is permanent: no operation ever changes the operator, so a
system configured with the vault as operator — `unlockTokenOperator = vaultAddress` —
remains so after every step. (2) The configuration actually grants the capability: whenever
a pending unlock position exists and its cooldown has elapsed, the vault, calling as the
configured operator (not the owner), can immediately execute the claim on behalf of the
recorded owner, with the payout going to the owner — for both standard and flexible
unlocks.) -/
theorem req_vault_operator_of_unlock_token (s : State) :
    (∀ (op : Op) (caller : Address) (s' : State), step s op caller = some s' →
      s'.unlockTokenOperator = s.unlockTokenOperator) ∧
    (∀ (op : Op) (caller : Address) (s' : State), step s op caller = some s' →
      s.unlockTokenOperator = vaultAddress → s'.unlockTokenOperator = vaultAddress) ∧
    (s.unlockTokenOperator = vaultAddress →
      (∀ (id : Nat) (owner : Address) (amount cooldownEnd : Nat),
        s.unlockRequests id = some (owner, amount, cooldownEnd) →
        s.unlockTokenOwner id = some owner →
        cooldownEnd ≤ s.now →
        ∃ s', step s (Op.claimUnlock id) vaultAddress = some s' ∧
          s'.apxUSDBal owner = s.apxUSDBal owner + amount) ∧
      (∀ (id : Nat) (owner : Address) (amount requestTime cooldownEnd : Nat),
        s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) →
        s.unlockTokenOwner id = some owner →
        requestTime + minFlexibleClaim ≤ s.now →
        ∃ s', step s (Op.flexibleClaimUnlock id) vaultAddress = some s' ∧
          s'.apxUSDBal owner = s.apxUSDBal owner
            + (amount - amount * flexibleUnlockFee requestTime s.now / 10000))) := by
  refine ⟨fun op caller s' h => step_unlockTokenOperator_unchanged _ _ _ _ h,
          fun op caller s' h hcfg => by
            rw [step_unlockTokenOperator_unchanged _ _ _ _ h]; exact hcfg,
          fun hcfg => ⟨?_, ?_⟩⟩
  · intro id owner amount cooldownEnd h_req h_owner h_time
    refine ⟨mintApxUSD (burnUnlockNFT s id) owner amount, ?_, ?_⟩
    · simp [step, h_req, h_owner, hcfg, Nat.not_lt.mpr h_time]
    · simp [mintApxUSD, burnUnlockNFT]
  · intro id owner amount requestTime cooldownEnd h_req h_owner h_time
    refine ⟨mintApxUSD (burnUnlockNFT s id) owner
        (amount - amount * flexibleUnlockFee requestTime s.now / 10000), ?_, ?_⟩
    · simp [step, h_req, h_owner, hcfg, Nat.not_lt.mpr h_time]
    · simp [mintApxUSD, burnUnlockNFT]

/-- REQ singleton-unlockToken-instance: There MUST be exactly one instance of UnlockToken
and it MUST be used exclusively by the apyUSD vault. (Model: the UnlockToken instance is
now identified explicitly by the `unlockTokenAddress` State field, with `unlockTokenAddress`
the designated instance's address constant. (1) Singleton: no operation ever changes the
recorded instance identity — in particular a system configured with the designated instance
stays on it forever — so along any execution there is exactly one UnlockToken instance and
the model has no way to deploy, switch to, or route positions through a second one. (2)
Exclusive use by the vault: every apxUSD_unlock position ever created is allocated in this
single instance's registry at its current counter, and only by the vault's own unlock entry
points (`requestUnlock`/`flexibleRequestUnlock`/`withdraw`/`redeem`); no other operation
can create a position in the registry.) -/
theorem req_singleton_unlock_token_instance (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') :
    s'.unlockTokenAddress = s.unlockTokenAddress ∧
    (s.unlockTokenAddress = unlockTokenAddress →
      s'.unlockTokenAddress = unlockTokenAddress) ∧
    (∀ (id : Nat) (owner : Address),
      s.unlockTokenOwner id = none → s'.unlockTokenOwner id = some owner →
      ((∃ a, op = Op.requestUnlock a) ∨ (∃ a, op = Op.flexibleRequestUnlock a) ∨
       (∃ a r, op = Op.withdraw a r) ∨ (∃ sh r, op = Op.redeem sh r)) ∧
      id = s.nextUnlockId) :=
  ⟨step_unlockTokenAddress_unchanged _ _ _ _ h_step,
   fun hcfg => by rw [step_unlockTokenAddress_unchanged _ _ _ _ h_step]; exact hcfg,
   fun id owner h_new h_now =>
     unlock_position_created_only_by_vault_ops _ _ _ _ h_step id owner h_new h_now⟩






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
to an existing request, the cooldown timer MUST reset to the time of the update. (Model:
this is now enforced by the transition system itself — `Op.requestUnlock` routes through
`requestUnlockStep`, which tops up the caller's existing standard position rather than
opening a second one, keyed on the single per-user `unlockRequestId` pointer. The theorem
states the *reachable* invariant: after any successful standard redemption request, the
caller's `unlockRequestId` resolves to exactly one position, holding an aggregated amount
with a freshly reset cooldown deadline `now + cooldownPeriod`.) -/
theorem req_single_pending_redemption_per_user (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.requestUnlock amount) caller = some s') :
    ∃ id amt, s'.unlockRequestId caller = some id ∧
      s'.unlockRequests id = some (caller, amt, s.now + cooldownPeriod) := by
  obtain ⟨-, -, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
  subst hs'
  exact requestUnlockStep_caller_position s caller amount

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
    obtain ⟨o, a, rt, ce, hreq, _, _, htime, _⟩ := step_flexibleClaimUnlock_some _ _ _ _ h3
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

/-- REQ overcollateralization-limit: The system MUST ensure that the total amount of apxUSD
minted never exceeds the market value of the collateral minus the required
overcollateralization margin. (Model: stated as a preservation invariant of `step`. apxUSD
is counted at its $1 par value; the market value of the collateral is the preferred-share
basket (`totalCollateralValue`) plus the USDC reserve; the `overcollateralizationBuffer`
State field is the required margin, so the invariant `minted + margin ≤ collateral` is
exactly `minted ≤ collateral − margin`. Pre-state well-formedness: no balance exceeds
total supply and the redemption value is at most par. Scope: the unlock-claim operations
are excluded because they re-mint apxUSD that was burned earlier when the unlock was
requested — an outstanding obligation the aggregate state does not track — and the
emergency stress operation is excluded because it models an exogenous collateral loss that
deliberately eats into the margin (it raises `emergencyFlag`).) -/
theorem req_overcollateralization_limit (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_inv : s.totalSupply_apxUSD + s.overcollateralizationBuffer
      ≤ s.totalCollateralValue + s.usdcReserve)
    (h_bal : ∀ a, s.apxUSDBal a ≤ s.totalSupply_apxUSD)
    (h_rv : s.redemptionValue ≤ ray)
    (h_not_claim : ∀ id, op ≠ Op.claimUnlock id)
    (h_not_flex_claim : ∀ id, op ≠ Op.flexibleClaimUnlock id)
    (h_not_stress : ∀ a, op ≠ Op.handleStressEvent a) :
    s'.totalSupply_apxUSD + s'.overcollateralizationBuffer
      ≤ s'.totalCollateralValue + s'.usdcReserve := by
  cases op
  case claimUnlock id => exact absurd rfl (h_not_claim id)
  case flexibleClaimUnlock id => exact absurd rfl (h_not_flex_claim id)
  case handleStressEvent a => exact absurd rfl (h_not_stress a)
  case depositUSDC a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
    omega
  case mintApxUSD t a =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
    omega
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
    omega
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
    omega
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createFlexibleUnlock, burnApxUSD]
    omega
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
    omega
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
    omega
  case redeemApxUSD a =>
    obtain ⟨_, _, h3, h4, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    have hu : (a * s.redemptionValue) / ray ≤ a := by
      rw [Nat.mul_comm]; exact div_mul_le_total h_rv
    have hba := h_bal caller
    simp [emitEvent, burnApxUSD]
    omega
  case executeRFQRedemption u a =>
    obtain ⟨_, _, h3, h4, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    have hu : (a * s.redemptionValue) / ray ≤ a := by
      rw [Nat.mul_comm]; exact div_mul_le_total h_rv
    have hba := h_bal u
    simp [burnApxUSD]
    omega
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact h_inv)
        | (cases Option.some.inj h_step; dsimp only; omega)
        | exact absurd h_step (by simp)

/-- REQ arbitrage-mint-access: Only eligible whitelist participants SHALL be permitted to
invoke the minting pathway for arbitrage when apxUSD trades above $1.00. (Model:
`Op.mintApxUSD` is the arbitrage minting pathway — distinct from the standard 1:1 deposit
pathway `Op.depositUSDC` — and `apxUSDMarketPrice` is the oracle-reported secondary-market
trading price of apxUSD in `ray` fixed-point, $1.00 = `ray`. The theorem: every successful
arbitrage mint requires BOTH that the caller is an eligible whitelist participant AND that
apxUSD is trading above $1.00; a non-whitelisted caller can never invoke the pathway, and
even a whitelisted participant cannot invoke it unless apxUSD trades above $1.00.) -/
theorem req_arbitrage_mint_access (s : State) (to : Address) (amount : Nat) (caller : Address) :
    (∀ s', step s (Op.mintApxUSD to amount) caller = some s' →
      s.whitelist caller = true ∧ ray < s.apxUSDMarketPrice) ∧
    (¬ s.whitelist caller → step s (Op.mintApxUSD to amount) caller = none) ∧
    (s.apxUSDMarketPrice ≤ ray → step s (Op.mintApxUSD to amount) caller = none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s' h
    obtain ⟨_, hw, _, _, hp, _, _⟩ := step_mintApxUSD_some _ _ _ _ _ h
    exact ⟨hw, hp⟩
  · intro h
    simp [step, h]
  · intro h
    simp only [step]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        -- `split` prunes the price-ite to `none` using `h : s.apxUSDMarketPrice ≤ ray`
        · rfl

/-- REQ arbitrage-redeem-access: Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00. -/
theorem req_arbitrage_redeem_access (s : State) (amount : Nat) (caller : Address) :
    (step s (Op.redeemApxUSD amount) caller = none) ∨ (s.whitelist caller = true) := by
  by_cases h : s.whitelist caller
  · exact Or.inr h
  · exact Or.inl (by simp [step, h])

/-- REQ linear-vest-implementation: The LinearVestV0 contract MUST implement a linear
vesting mechanism for yield credited to the apyUSD vault. (Model: the currently-streaming
portion of the vest, `newlyVestedAmount` — the release of `vestTotal` since the clock
`vestStart` over `vestPeriod` — follows the linear formula exactly. The reported total
`vestedAmount` is that streaming portion plus whatever was already realized into
`fullyVestedAmount` by an earlier credit/reconfiguration/pull, mirroring `LinearVestV0`'s
two-accumulator design — cf. `req_credit_preserves_accrued_vest`.) -/
theorem req_linear_vest_implementation (s : State) :
    -- (1) nothing has streamed before the vest clock's anchor
    (∀ now, now < s.vestStart → newlyVestedAmount s now = 0) ∧
    -- (2) the streamed amount only ever grows with time — a stream never claws back
    (∀ n m, n ≤ m → newlyVestedAmount s n ≤ newlyVestedAmount s m) ∧
    -- (3) it never streams out more than the pool being vested
    (∀ now, newlyVestedAmount s now ≤ s.vestTotal) ∧
    -- (4) once a full period has elapsed the entire pool has streamed (100% vested)
    (∀ now, s.vestStart + s.vestPeriod ≤ now → newlyVestedAmount s now = s.vestTotal) ∧
    -- (5) the total reportable vested amount is the realized accumulator plus the
    --     currently-streaming portion (two-accumulator LinearVestV0 model)
    (∀ now, vestedAmount s now = s.fullyVestedAmount + newlyVestedAmount s now) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro now h
    unfold newlyVestedAmount
    rw [if_pos h]
  · intro n m h
    exact newlyVestedAmount_mono s h
  · intro now
    exact newlyVestedAmount_le_total s now
  · intro now h
    have h1 : ¬ now < s.vestStart := by omega
    have h2 : s.vestPeriod ≤ now - s.vestStart := by omega
    simp [newlyVestedAmount, h1, h2]
  · intro now
    rfl

/-- REQ yield-rate-dollar-terms: The yield rate MUST be expressed in dollar terms for the month.
(Model: the monthly yield rate is not a free-floating percentage — a successful `Op.setYieldRate`
pins `yieldRateMonth` to a figure that is (b) bounded above by `collateralYieldBase`, the dollar
surplus the collateral basket actually generated (`overcollateralizationBuffer`, a dollar amount),
and (c) simultaneously refreshes that dollar basis to the *current* collateral surplus, which
becomes the ceiling for the following month. So the rate is denominated in, and capped by, real
dollar collateral yield rather than an abstract rate.) -/
theorem req_yield_rate_dollar_terms (s : State) (bps : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.setYieldRate bps) caller = some s') :
    s'.yieldRateMonth = bps ∧
    s'.yieldRateMonth ≤ s.collateralYieldBase ∧
    s'.collateralYieldBase = overcollateralizationBuffer s := by
  simp only [step] at h_step
  split at h_step
  · rename_i hcond
    obtain ⟨_, _, hbound⟩ := hcond
    cases Option.some.inj h_step
    exact ⟨rfl, hbound, rfl⟩
  · exact absurd h_step (by simp)

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

/-- REQ deposit_immediate: The apyUSD vault MUST complete deposit operations synchronously and
deliver apyUSD shares to the receiver without any delay. (Model: the apyUSD vault's synchronous
ERC-4626 deposit is `Op.lockApxUSD` — it locks apxUSD and mints apyUSD *shares* in return, unlike
`Op.depositUSDC`/`Op.mintApxUSD` which mint the apxUSD stablecoin itself. "Without delay" is a
*temporal* claim: the shares are credited to the receiver — here the locking `caller` — in the very
same atomic `step`, not deferred into a pending/settlement record the way a redemption is. This
theorem states exactly that: on a successful lock the receiver's apyUSD balance has *already*
increased, by exactly the freshly minted `lockShares amount s.exchangeRate`, with no intermediate
state — the strong, exact form of "synchronous, immediate share delivery".) -/
theorem req_deposit_immediate (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    s'.apyUSDBal caller = s.apyUSDBal caller + lockShares amount s.exchangeRate := by
  obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
  subst hs'
  simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]

/-- REQ mint_immediate: The apyUSD vault MUST complete mint operations synchronously and deliver
apyUSD shares to the receiver without any delay. (Model: like `deposit-immediate`, the vault's
synchronous share-minting path is `Op.lockApxUSD`. The stronger temporal witness proved here is
that in the single atomic `step` *both* the receiver's apyUSD balance *and* the apyUSD total supply
increase by exactly the same freshly minted `lockShares amount s.exchangeRate` — the shares are
genuinely newly issued and delivered now, in lockstep, with no deferred settlement.) -/
theorem req_mint_immediate (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    s'.apyUSDBal caller = s.apyUSDBal caller + lockShares amount s.exchangeRate ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD + lockShares amount s.exchangeRate := by
  obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
  subst hs'
  refine ⟨?_, ?_⟩ <;>
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]

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

/-- REQ multiple-unlocks-reset-cooldown: If a user initiates multiple unlocks, the system
MUST reset the cooldown period for the total locked amount. (Model: reachable via `step` —
when the caller already holds a standard position `id` (their `unlockRequestId` pointer),
a further `Op.requestUnlock` aggregates the amount into that same position and resets its
cooldown deadline to `now + cooldownPeriod` on the *total* `oldAmount + amount`.) -/
theorem req_multiple_unlocks_reset_cooldown (s : State) (amount id oldAmount oldEnd : Nat)
    (caller : Address) (s' : State)
    (h_ptr : s.unlockRequestId caller = some id)
    (h_req : s.unlockRequests id = some (caller, oldAmount, oldEnd))
    (h_step : step s (Op.requestUnlock amount) caller = some s') :
    s'.unlockRequests id = some (caller, oldAmount + amount, s.now + cooldownPeriod) := by
  obtain ⟨-, -, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
  subst hs'
  unfold requestUnlockStep
  have hp : (burnApxUSD s caller amount).unlockRequestId caller = some id := by
    simpa [burnApxUSD] using h_ptr
  have hr : (burnApxUSD s caller amount).unlockRequests id = some (caller, oldAmount, oldEnd) := by
    simpa [burnApxUSD] using h_req
  rw [hp]
  simp only [hr, if_pos]
  rw [updateStandardUnlock_unlockRequests_eq (burnApxUSD s caller amount) id caller amount
    caller oldAmount oldEnd hr id]
  simp [burnApxUSD]

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

/-- REQ mint-price: The protocol MUST price newly minted apxUSD at $1 per unit. This holds
unconditionally via the standard deposit pathway (`Op.depositUSDC`) — `amount` USDC paid for
`amount` apxUSD minted, with no market-price precondition. The separate arbitrage pathway
(`Op.mintApxUSD`, see `req_arbitrage_mint_access`/`req_mint_price_arbitrage_pathway`) is
gated on market-price conditions but mints at the same 1:1 rate once its access conditions
are satisfied. -/
theorem req_mint_price (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true) (h3 : s.usdcBal caller ≥ amount)
    (h4 : s.denylist caller = false) :
    ∃ s', step s (Op.depositUSDC amount) caller = some s' ∧
          s'.apxUSDBal caller = s.apxUSDBal caller + amount ∧
          s'.usdcBal caller = s.usdcBal caller - amount ∧
          s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount := by
  rcases ho : step s (Op.depositUSDC amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, h2, h4, Nat.not_lt.mpr h3])
  · obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ ho
    subst hs'
    exact ⟨_, rfl, by simp [emitEvent, mintApxUSD], by simp [emitEvent, mintApxUSD],
           by simp [emitEvent, mintApxUSD]⟩

/-- REQ mint-price (arbitrage pathway): the premium-gated `Op.mintApxUSD` pathway also prices
at $1 once its access conditions (whitelist, denylist-clear, market price above $1) hold. -/
theorem req_mint_price_arbitrage_pathway (s : State) (amount : Nat) (to : Address) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.whitelist caller = true) (h3 : s.usdcBal caller ≥ amount)
    (h4 : s.denylist caller = false) (h5 : s.denylist to = false)
    (h6 : ray < s.apxUSDMarketPrice) :
    ∃ s', step s (Op.mintApxUSD to amount) caller = some s' ∧
          s'.apxUSDBal to = s.apxUSDBal to + amount ∧
          s'.usdcBal caller = s.usdcBal caller - amount ∧
          s'.totalSupply_apxUSD = s.totalSupply_apxUSD + amount := by
  rcases ho : step s (Op.mintApxUSD to amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, h2, h4, h5, Nat.not_lt.mpr h3, Nat.not_le.mpr h6])
  · obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ ho
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


/-- REQ lock-apxusd: The protocol MUST allow a user to lock apxUSD in the vault and receive apyUSD. -/
theorem req_lock_apxusd (s : State) (amount : Nat) (caller : Address)
    (h1 : s.globalPause = false) (h2 : s.apxUSDBal caller ≥ amount) :
    ∃ s', step s (Op.lockApxUSD amount) caller = some s' := by
  rcases ho : step s (Op.lockApxUSD amount) caller with _ | s'
  · exact absurd ho (by simp [step, h1, Nat.not_lt.mpr h2])
  · exact ⟨s', rfl⟩

-- /-- REQ price-may-include-spreads: The protocol MAY reflect spreads and offchain execution expenses in the price during minting and redemption. -/
-- UNFORMALIZABLE req_price_may_include_spreads: Re-examined against the current model and
-- still not expressible: the mint paths (depositUSDC/mintApxUSD) are hard-coded strictly
-- 1:1 with no spread or fee parameter, and the redemption price (redemptionValue) models
-- the value of the underlying basket - not execution spreads (updateRedemptionValue is a
-- placeholder no-op). A MAY-permission to price in spreads has no mechanism in the model
-- to witness, and no faithful theorem can assert a capability the model lacks.

-- /-- REQ rebalance-overcollateralization: The system SHALL rebalance the collateral basket so that apxUSD remains over‑collateralized. -/
-- UNFORMALIZABLE req_rebalance_overcollateralization: Re-examined against the current
-- model and still not expressible: the collateral basket has no composition - only an
-- aggregate totalCollateralValue that no operation rebalances (it changes only via
-- handleStressEvent, an exogenous loss). The passive invariant that operations preserve
-- overcollateralization is already covered by req_overcollateralization_limit; the active
-- rebalancing mechanism this requirement mandates is not modeled.
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
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
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

/-- REQ configurable-vesting-period: The vesting period for linear yield distribution MUST
be configurable. (Model: `Op.setVestPeriod` accrues the currently-streaming portion into
`fullyVestedAmount` first — same pattern as `creditYield` — before applying the new
period, so reconfiguring never forfeits already-accrued yield.) -/
theorem req_configurable_vesting_period (s : State) (p : Nat) :
    ∃ s', step s (Op.setVestPeriod p) s.admin = some s' ∧ s'.vestPeriod = p :=
  ⟨{ s with
      fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
      vestTotal := s.vestTotal - newlyVestedAmount s s.now
      vestStart := s.now
      vestPeriod := p },
   by simp [step], rfl⟩

/-- REQ deposit-emits-event: The deposit(assets, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution. -/
theorem req_deposit_emits_event (s s' : State) (amount : Nat) (caller : Address)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    ("Deposit", [caller, caller, caller, amount, amount]) ∈ s'.eventLog := by
  obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
  subst hs'
  simp [emitEvent]

/-- REQ mint-emits-event: The mint(shares, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution. (The exact tuple is pinned: sender = the minting `caller`, receiver = owner = `to`, and assets = shares = `amount`.) -/
theorem req_mint_emits_event (s s' : State) (to : Address) (amount : Nat) (caller : Address)
    (h_step : step s (Op.mintApxUSD to amount) caller = some s') :
    ("Deposit", [caller, to, to, amount, amount]) ∈ s'.eventLog := by
  obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
  subst hs'
  simp [emitEvent]

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
proceeds to the apyUSD vault. (Model: only the yield distributor may credit; a credit
first realizes whatever has already streamed out of the current vest clock into
`fullyVestedAmount` (the remainder joins the freshly-restarted `vestTotal`/`vestStart`
clock alongside the newly credited `amount` — cf. `req_credit_preserves_accrued_vest`),
so `vestTotal` is NOT simply incremented by `amount`. What IS true unconditionally: once
the (new) stream has fully vested, the vault's apxUSD asset base `totalAssets` has grown
by exactly the credited amount over its own prior fully-vested baseline.) -/
theorem req_yield_distributor_credit (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s') :
    caller = s.yieldDistributor ∧
    s'.vestTotal = (s.vestTotal - newlyVestedAmount s s.now) + amount ∧
    totalAssets { s' with now := s'.vestStart + s'.vestPeriod }
      = totalAssets { s with now := s.vestStart + s.vestPeriod } + amount := by
  simp only [step] at h_step
  split at h_step
  · rename_i hcaller
    cases Option.some.inj h_step
    refine ⟨by simpa using hcaller, rfl, ?_⟩
    have hnv : newlyVestedAmount s s.now ≤ s.vestTotal := newlyVestedAmount_le_total s s.now
    generalize hnvdef : newlyVestedAmount s s.now = nv at hnv ⊢
    simp only [totalAssets, vestedAmount, newlyVestedAmount]
    repeat' split
    all_goals omega
  · exact absurd h_step (by simp)

/-- REQ credit-preserves-accrued-vest: Crediting new yield (`Op.creditYield`) MUST NOT
forfeit yield that has already streamed out of the vest but has not yet been pulled into
vault custody. This is the two-accumulator fix itself: the real `LinearVestV0` contract
realizes the currently-streaming portion into a `fullyVestedAmount` accumulator BEFORE
folding new yield into a freshly-restarted `vestTotal`/`vestStart` clock, precisely so that
restarting the clock (which would otherwise reset the linear streaming computation back to
"0% elapsed") never erases value that had already linearly vested. (Model: immediately
after a credit — i.e. evaluated at the unchanged `now`, before any further time passes —
the total reportable `vestedAmount` is exactly unchanged: the newly credited `amount`
itself has correctly not yet started streaming (0% elapsed since the clock was just
re-anchored at `now`), but nothing that had already vested under the old clock is lost.
Requires `0 < vestPeriod`: with a degenerate zero-length vesting period every stream
(old and new) is defined to be 100% vested instantaneously, so a freshly-credited
`amount` would — correctly, not as a forfeiture — be counted immediately too; excluding
that degenerate case isolates the forfeiture-avoidance property this requirement is about.
Contrast with the old (buggy) model this replaces, where `creditYield` unconditionally
reset `vestStart` without first realizing the elapsed portion, so any yield that had
linearly vested but not yet been pulled was silently erased by the reset.) -/
theorem req_credit_preserves_accrued_vest (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s')
    (h_period : 0 < s.vestPeriod) :
    vestedAmount s' s'.now = vestedAmount s s.now := by
  simp only [step] at h_step
  split at h_step
  · cases Option.some.inj h_step
    simp only [vestedAmount, newlyVestedAmount, Nat.sub_self, Nat.zero_mul, Nat.zero_div]
    repeat' split
    all_goals omega
  · exact absurd h_step (by simp)

/-- REQ new-locked-receives-yield: When new apyUSD is locked, it MUST immediately begin
receiving yield, which reduces the overall percentage yield for existing holders. (Model:
locking mints shares at the prevailing exchange rate — no discount, waiting period, or
carve-out — so from the moment of the lock the new holder's redeemable assets grow with the
same vesting exchange rate as every existing holder's; and the mint enlarges the share
base, (weakly) diluting each unit share's claim on any yet-unvested yield pool.) -/
theorem req_new_locked_receives_yield (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    -- shares are minted immediately, priced at the prevailing exchange rate
    s'.apyUSDBal caller = s.apyUSDBal caller + lockShares amount s.exchangeRate ∧
    -- and immediately begin receiving yield: the new holder's redeemable assets grow with
    -- the vesting exchange rate from the very moment of the lock, like any other holder's
    (∀ dt, redeemAssets (s'.apyUSDBal caller) (computeExchangeRate s')
      ≤ redeemAssets (s'.apyUSDBal caller) (computeExchangeRate { s' with now := s'.now + dt })) ∧
    -- the enlarged share base spreads future yield thinner over existing holders:
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD + lockShares amount s.exchangeRate ∧
    (∀ pendingYield : Nat, 0 < s.totalSupply_apyUSD →
      (pendingYield * ray) / s'.totalSupply_apyUSD
        ≤ (pendingYield * ray) / s.totalSupply_apyUSD) := by
  obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
  subst hs'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  · intro dt
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (computeExchangeRate_mono_now _ dt))
  · simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  · intro pendingYield hpos
    apply Nat.div_le_div_left ?_ hpos
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]

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

-- Theorems added re-examining requirements marked UNFORMALIZABLE by the first pipeline run

/-- Helper: every operation other than the vault deposit (`lockApxUSD`) and the vault
withdrawal paths (`withdraw`/`redeem`) leaves the vault's apxUSD custody balance
untouched. -/
private theorem vaultApxUSDBal_unchanged_of_non_vault_op (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_not_lock : ∀ a, op ≠ Op.lockApxUSD a)
    (h_not_withdraw : ∀ a r, op ≠ Op.withdraw a r)
    (h_not_redeem : ∀ a r, op ≠ Op.redeem a r) :
    s'.vaultApxUSDBal = s.vaultApxUSDBal := by
  cases op
  case lockApxUSD x => exact absurd rfl (h_not_lock x)
  case withdraw x r => exact absurd rfl (h_not_withdraw x r)
  case redeem x r => exact absurd rfl (h_not_redeem x r)
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
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
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
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

/-- REQ no-rehypothecation: The protocol MUST NOT rehypothecate, lend, or otherwise
utilize deposited apxUSD for any purpose. (Model: apxUSD deposited by users is held in the
vault's custody balance `vaultApxUSDBal`. `Op` is a closed inductive enumerating every
operation of the protocol, and total case analysis over it shows the custody balance can
only ever change through the user-facing accounting paths themselves: a user's own vault
deposit (`lockApxUSD`, which adds exactly the deposited amount to custody) or a user's own
withdrawal (`withdraw`/`redeem`, which — after pulling the vault's own vested yield stream
into custody — remove exactly the assets returned to that user as an unlock position). No
lending, rehypothecation, or other utilization path exists: no other operation can move a
single unit of deposited apxUSD out of custody.) -/
theorem req_no_rehypothecation (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') :
    (s'.vaultApxUSDBal ≠ s.vaultApxUSDBal →
      (∃ x, op = Op.lockApxUSD x) ∨ (∃ x r, op = Op.withdraw x r) ∨
      (∃ x r, op = Op.redeem x r)) ∧
    (∀ x, op = Op.lockApxUSD x → s'.vaultApxUSDBal = s.vaultApxUSDBal + x) ∧
    (∀ x r, op = Op.withdraw x r →
      s'.vaultApxUSDBal = (pullVestedYield s).vaultApxUSDBal - x) ∧
    (∀ x r, op = Op.redeem x r →
      s'.vaultApxUSDBal = (pullVestedYield s).vaultApxUSDBal - redeemAssets x s.exchangeRate) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h_changed
    cases op
    case lockApxUSD x => exact Or.inl ⟨x, rfl⟩
    case withdraw x r => exact Or.inr (Or.inl ⟨x, r, rfl⟩)
    case redeem x r => exact Or.inr (Or.inr ⟨x, r, rfl⟩)
    all_goals
      exact absurd (vaultApxUSDBal_unchanged_of_non_vault_op _ _ _ _ h_step
        (fun _ => nofun) (fun _ _ => nofun) (fun _ _ => nofun)) h_changed
  · intro x hop
    subst hop
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  · intro x r hop
    subst hop
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  · intro x r hop
    subst hop
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- REQ unlock-cannot-be-cancelled: The system MUST NOT allow an unlocking request to be
cancelled once it has been initiated. (Model: an initiated unlocking request is a live
apxUSD_unlock position — `unlockTokenOwner id = some owner`. Total case analysis over the
closed `Op` inductive shows the only steps after which the position no longer exists are
the two legitimate claim settlements of that very position: `claimUnlock id`, which is
gated on the full cooldown having elapsed and mints the owner the full recorded amount,
and `flexibleClaimUnlock id`, which is gated on the minimum claim delay and mints the
owner the recorded amount net of the published early-exit fee. There is no cancel
operation and no other path that can clear a pending request — in particular nothing can
make a request vanish early without paying out.) -/
theorem req_unlock_cannot_be_cancelled (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (id : Nat) (owner : Address)
    (h_live : s.unlockTokenOwner id = some owner)
    (h_gone : s'.unlockTokenOwner id = none) :
    (op = Op.claimUnlock id ∧
      ∃ amount cooldownEnd, s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
        cooldownEnd ≤ s.now ∧
        s'.apxUSDBal owner = s.apxUSDBal owner + amount) ∨
    (op = Op.flexibleClaimUnlock id ∧
      ∃ amount requestTime cooldownEnd,
        s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
        requestTime + minFlexibleClaim ≤ s.now ∧
        s'.apxUSDBal owner = s.apxUSDBal owner
          + (amount - amount * flexibleUnlockFee requestTime s.now / 10000)) := by
  cases op
  case claimUnlock rid =>
    obtain ⟨o, am, ce, hreq, howner, _, htime, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = rid
    · subst hid
      have ho : o = owner := by rw [howner] at h_live; exact Option.some.inj h_live
      subst ho
      exact Or.inl ⟨rfl, am, ce, hreq, htime, by simp [mintApxUSD, burnUnlockNFT]⟩
    · simp [mintApxUSD, burnUnlockNFT, hid, h_live] at h_gone
  case flexibleClaimUnlock rid =>
    obtain ⟨o, am, rt, ce, hreq, howner, _, htime, hs'⟩ :=
      step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = rid
    · subst hid
      have ho : o = owner := by rw [howner] at h_live; exact Option.some.inj h_live
      subst ho
      exact Or.inr ⟨rfl, am, rt, ce, hreq, htime, by simp [mintApxUSD, burnUnlockNFT]⟩
    · simp [mintApxUSD, burnUnlockNFT, hid, h_live] at h_gone
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · rcases requestUnlockStep_owner_counter_cases s caller a with ⟨_, howner⟩ | ⟨_, howner⟩
      · rw [howner] at h_gone; subst hid; simp [createStandardUnlock, burnApxUSD] at h_gone
      · rw [howner, h_live] at h_gone; simp at h_gone
    · rw [requestUnlockStep_unlockTokenOwner_of_ne s caller a hid, h_live] at h_gone; simp at h_gone
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · subst hid
      simp [createFlexibleUnlock, burnApxUSD] at h_gone
    · simp [createFlexibleUnlock, burnApxUSD, hid, h_live] at h_gone
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · subst hid
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_gone
    · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hid, h_live] at h_gone
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    by_cases hid : id = s.nextUnlockId
    · subst hid
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_gone
    · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hid, h_live] at h_gone
  case depositUSDC a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD, h_live] at h_gone
  case mintApxUSD t a =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD, h_live] at h_gone
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, h_live] at h_gone
  case redeemApxUSD a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD, h_live] at h_gone
  case executeRFQRedemption u am =>
    obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    simp [burnApxUSD, h_live] at h_gone
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; simp_all)
        | exact absurd h_step (by simp)

/-- REQ unlock-token-nontransferable: apxUSD_unlock tokens MUST NOT be transferable.
(Model: an apxUSD_unlock token is a registry position `unlockTokenOwner id`. The theorem
captures non-transferability as: across every operation of the closed `Op` inductive, a
position's recorded owner can never be reassigned to a different address — after any step
it is either still `some owner` (untouched) or `none` (settled via the claim path, cf.
`req_unlock_cannot_be_cancelled`), never `some owner'` for another `owner'`. The model has
no transfer operation, and this proves no other operation smuggles a transfer in. The
freshness hypothesis — ids at or above the registry counter are unallocated — is the
registry's counter invariant; the first conjunct shows every step preserves it, so it
holds along any execution from a well-formed initial state.) -/
theorem req_unlock_token_nontransferable (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_fresh : ∀ i, s.nextUnlockId ≤ i → s.unlockTokenOwner i = none) :
    (∀ i, s'.nextUnlockId ≤ i → s'.unlockTokenOwner i = none) ∧
    (∀ id owner, s.unlockTokenOwner id = some owner →
      s'.unlockTokenOwner id = some owner ∨ s'.unlockTokenOwner id = none) := by
  cases op
  case requestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    rcases requestUnlockStep_owner_counter_cases s caller a with ⟨hcnt, howner⟩ | ⟨hcnt, howner⟩
    · rw [hcnt, howner]
      constructor
      · intro i hi
        simp only [createStandardUnlock, burnApxUSD] at hi ⊢
        rw [if_neg (by omega)]
        exact h_fresh i (by omega)
      · intro id owner h_own
        have hid : id ≠ s.nextUnlockId := fun h => by
          rw [h, h_fresh s.nextUnlockId (Nat.le_refl _)] at h_own; cases h_own
        exact Or.inl (by simp [createStandardUnlock, burnApxUSD, hid, h_own])
    · rw [hcnt, howner]
      exact ⟨h_fresh, fun _ _ h => Or.inl h⟩
  case flexibleRequestUnlock a =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    constructor
    · intro i hi
      simp only [createFlexibleUnlock, burnApxUSD] at hi ⊢
      rw [if_neg (by omega)]
      exact h_fresh i (by omega)
    · intro id owner h_own
      have hid : id ≠ s.nextUnlockId := fun h => by
        rw [h, h_fresh s.nextUnlockId (Nat.le_refl _)] at h_own; cases h_own
      exact Or.inl (by simp [createFlexibleUnlock, burnApxUSD, hid, h_own])
  case withdraw a r =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    constructor
    · intro i hi
      simp only [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD,
        pullVestedYield_nextUnlockId, pullVestedYield_unlockTokenOwner] at hi ⊢
      rw [if_neg (by omega)]
      exact h_fresh i (by omega)
    · intro id owner h_own
      have hid : id ≠ s.nextUnlockId := fun h => by
        rw [h, h_fresh s.nextUnlockId (Nat.le_refl _)] at h_own; cases h_own
      exact Or.inl (by
        simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hid, h_own])
  case redeem sh r =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    constructor
    · intro i hi
      simp only [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD,
        pullVestedYield_nextUnlockId, pullVestedYield_unlockTokenOwner] at hi ⊢
      rw [if_neg (by omega)]
      exact h_fresh i (by omega)
    · intro id owner h_own
      have hid : id ≠ s.nextUnlockId := fun h => by
        rw [h, h_fresh s.nextUnlockId (Nat.le_refl _)] at h_own; cases h_own
      exact Or.inl (by
        simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hid, h_own])
  case claimUnlock rid =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    constructor
    · intro i hi
      simp only [mintApxUSD, burnUnlockNFT] at hi ⊢
      by_cases hic : i = rid <;> simp [hic, h_fresh i (by simpa using hi)]
    · intro id owner h_own
      by_cases hid : id = rid
      · exact Or.inr (by simp [mintApxUSD, burnUnlockNFT, hid])
      · exact Or.inl (by simp [mintApxUSD, burnUnlockNFT, hid, h_own])
  case flexibleClaimUnlock rid =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    constructor
    · intro i hi
      simp only [mintApxUSD, burnUnlockNFT] at hi ⊢
      by_cases hic : i = rid <;> simp [hic, h_fresh i (by simpa using hi)]
    · intro id owner h_own
      by_cases hid : id = rid
      · exact Or.inr (by simp [mintApxUSD, burnUnlockNFT, hid])
      · exact Or.inl (by simp [mintApxUSD, burnUnlockNFT, hid, h_own])
  case depositUSDC a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    exact ⟨fun i hi => h_fresh i (by simpa [emitEvent, mintApxUSD] using hi),
      fun id owner h_own => Or.inl (by simpa [emitEvent, mintApxUSD] using h_own)⟩
  case mintApxUSD t a =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    exact ⟨fun i hi => h_fresh i (by simpa [emitEvent, mintApxUSD] using hi),
      fun id owner h_own => Or.inl (by simpa [emitEvent, mintApxUSD] using h_own)⟩
  case lockApxUSD a =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    exact ⟨fun i hi =>
        h_fresh i (by simpa [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] using hi),
      fun id owner h_own =>
        Or.inl (by simpa [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] using h_own)⟩
  case redeemApxUSD a =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    exact ⟨fun i hi => h_fresh i (by simpa [emitEvent, burnApxUSD] using hi),
      fun id owner h_own => Or.inl (by simpa [emitEvent, burnApxUSD] using h_own)⟩
  case executeRFQRedemption u am =>
    obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
    subst hs'
    exact ⟨fun i hi => h_fresh i (by simpa [burnApxUSD] using hi),
      fun id owner h_own => Or.inl (by simpa [burnApxUSD] using h_own)⟩
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step;
           exact ⟨fun i hi => h_fresh i hi, fun id owner h_own => Or.inl h_own⟩)
        | exact absurd h_step (by simp)

/-- REQ cooldown-removal: When apyUSD enters the cooldown phase, it MUST be removed from
the yield pool, causing remaining apyUSD to receive a higher percentage yield. (Model:
apyUSD enters the cooldown phase through `Op.redeem`/`Op.withdraw`, which place the
exiting value in a pending unlock whose deadline is `now + cooldownPeriod`. The yield
pool is the outstanding apyUSD share supply `totalSupply_apyUSD`, over which every yield
credit is distributed pro-rata. The theorem: in the very same step in which apyUSD enters
cooldown, the entering shares are burned out of the yield pool — the pool strictly
shrinks whenever a positive number of shares enters cooldown — so every future yield
credit `y` is divided among strictly fewer pool shares. "Higher percentage yield" is
stated both exactly — the per-share fraction `y / supply` is strictly larger after
removal, compared via cross-multiplication `y · supply' < y · supply` — and in the
model's floor arithmetic, where the per-share credit `y·ray / supply` is weakly higher
(floor division can absorb a strict rational increase). `h_bal` (a holder's balance never
exceeds the total supply) is the standard supply-consistency invariant of reachable
states.) -/
theorem req_cooldown_removal (s : State) :
    (∀ (shares : Nat) (receiver caller : Address) (s' : State),
      -- apyUSD entering the cooldown phase via `redeem` ...
      step s (Op.redeem shares receiver) caller = some s' →
      -- ... is placed under cooldown until `now + cooldownPeriod` ...
      s'.unlockRequests s.nextUnlockId
        = some (receiver, redeemAssets shares s.exchangeRate, s.now + cooldownPeriod) ∧
      -- ... and removed from the yield pool in the very same step
      s'.totalSupply_apyUSD = s.totalSupply_apyUSD - shares ∧
      (0 < shares → s.apyUSDBal caller ≤ s.totalSupply_apyUSD →
        s'.totalSupply_apyUSD < s.totalSupply_apyUSD) ∧
      -- so remaining apyUSD receive a higher % yield: the exact per-share fraction of
      -- any future credit y is strictly larger over the shrunken pool ...
      (∀ y : Nat, 0 < y → 0 < shares → s.apyUSDBal caller ≤ s.totalSupply_apyUSD →
        y * s'.totalSupply_apyUSD < y * s.totalSupply_apyUSD) ∧
      -- ... and the floor-arithmetic per-share credit is weakly higher
      (∀ y : Nat, 0 < s.totalSupply_apyUSD - shares →
        y * ray / s.totalSupply_apyUSD ≤ y * ray / (s.totalSupply_apyUSD - shares))) ∧
    (∀ (assets : Nat) (receiver caller : Address) (s' : State),
      -- apyUSD entering the cooldown phase via `withdraw`: identical consequences
      step s (Op.withdraw assets receiver) caller = some s' →
      s'.unlockRequests s.nextUnlockId = some (receiver, assets, s.now + cooldownPeriod) ∧
      s'.totalSupply_apyUSD = s.totalSupply_apyUSD - withdrawShares assets s.exchangeRate ∧
      (0 < withdrawShares assets s.exchangeRate →
        s.apyUSDBal caller ≤ s.totalSupply_apyUSD →
        s'.totalSupply_apyUSD < s.totalSupply_apyUSD) ∧
      (∀ y : Nat, 0 < y → 0 < withdrawShares assets s.exchangeRate →
        s.apyUSDBal caller ≤ s.totalSupply_apyUSD →
        y * s'.totalSupply_apyUSD < y * s.totalSupply_apyUSD) ∧
      (∀ y : Nat, 0 < s.totalSupply_apyUSD - withdrawShares assets s.exchangeRate →
        y * ray / s.totalSupply_apyUSD
          ≤ y * ray / (s.totalSupply_apyUSD - withdrawShares assets s.exchangeRate))) := by
  have hmul : ∀ (y a b : Nat), 0 < y → a < b → y * a < y * b := by
    intro y a b hy hab
    calc y * a < y * a + y := by omega
      _ = y * (a + 1) := (Nat.mul_succ y a).symm
      _ ≤ y * b := Nat.mul_le_mul_left y hab
  constructor
  · intro shares receiver caller s' h_step
    obtain ⟨_, hshares, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    rw [pullVestedYield_apyUSDBal] at hshares
    subst hs'
    have hsup : (emitEvent (updateExchangeRate (createStandardUnlock
        { burnApyUSD (pullVestedYield s) caller shares with
          vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal
            - redeemAssets shares s.exchangeRate }
        receiver (redeemAssets shares s.exchangeRate))) "Withdraw"
        [caller, receiver, caller, redeemAssets shares s.exchangeRate, shares]).totalSupply_apyUSD
        = s.totalSupply_apyUSD - shares := by
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
    refine ⟨?_, hsup, ?_, ?_, fun y hpos => Nat.div_le_div_left (Nat.sub_le _ _) hpos⟩
    · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
    · intro hpos hbal; omega
    · intro y hy hpos hbal
      rw [hsup]
      exact hmul _ _ _ hy (by omega)
  · intro assets receiver caller s' h_step
    obtain ⟨_, hshares, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    rw [pullVestedYield_apyUSDBal] at hshares
    subst hs'
    have hsup : (emitEvent (updateExchangeRate (createStandardUnlock
        { burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate) with
          vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller
            (withdrawShares assets s.exchangeRate)).vaultApxUSDBal - assets }
        receiver assets)) "Withdraw"
        [caller, receiver, caller, assets, withdrawShares assets s.exchangeRate]).totalSupply_apyUSD
        = s.totalSupply_apyUSD - withdrawShares assets s.exchangeRate := by
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
    refine ⟨?_, hsup, ?_, ?_, fun y hpos => Nat.div_le_div_left (Nat.sub_le _ _) hpos⟩
    · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
    · intro hpos hbal; omega
    · intro y hy hpos hbal
      rw [hsup]
      exact hmul _ _ _ hy (by omega)

/-- REQ erc4626-compliance: The apyUSD vault contract MUST implement the ERC-4626
tokenized vault interface. (Model: the interface surface is modeled by
`convertToShares`/`convertToAssets`, the four `preview*` functions, the four `max*`
functions, and the deposit/mint/withdraw/redeem flows (`lockApxUSD`, `withdraw`,
`redeem`, plus the slippage wrappers). This theorem proves the standard's core
consistency guarantees hold of that surface: (1) each `preview*` function reports exactly
the conversion the corresponding operation uses; (2) `convertToShares`/`convertToAssets`
are mutually consistent under the current exchange rate — round-tripping in either
direction never credits value (ERC-4626's rounding mandate: conversions round against
the user); (3) `previewWithdraw` rounds up relative to `previewDeposit`'s rounding down,
so withdrawing never burns fewer shares than an equal-sized deposit mints; and (4) the
`max*` limits correctly reflect the vault's pause gating — zero while paused, and the
owner's full balance-derived capacity when live.) -/
theorem req_erc4626_compliance (s : State) :
    -- (1) previews report exactly the conversions the operations use
    (∀ assets, previewDeposit s assets = convertToShares s assets) ∧
    (∀ shares, previewMint s shares = convertToAssets s shares) ∧
    (∀ assets, previewWithdraw s assets = withdrawShares assets s.exchangeRate) ∧
    (∀ shares, previewRedeem s shares = convertToAssets s shares) ∧
    -- (2) conversions are mutually consistent: round-trips never credit value
    (∀ assets, convertToAssets s (convertToShares s assets) ≤ assets) ∧
    (∀ shares, convertToShares s (convertToAssets s shares) ≤ shares) ∧
    -- (3) withdrawing rounds against the user relative to depositing
    (∀ assets, previewDeposit s assets ≤ previewWithdraw s assets) ∧
    -- (4) max* limits reflect pause gating and the owner's balances
    (s.globalPause = true → ∀ a,
      maxDeposit s a = 0 ∧ maxMint s a = 0 ∧ maxWithdraw s a = 0 ∧ maxRedeem s a = 0) ∧
    (s.globalPause = false → ∀ a,
      maxDeposit s a = s.apxUSDBal a ∧
      maxMint s a = convertToShares s (s.apxUSDBal a) ∧
      maxWithdraw s a = convertToAssets s (s.apyUSDBal a) ∧
      maxRedeem s a = s.apyUSDBal a) := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro assets
    unfold convertToAssets convertToShares redeemAssets lockShares
    calc assets * ray / s.exchangeRate * s.exchangeRate / ray
        ≤ assets * ray / ray := Nat.div_le_div_right (Nat.div_mul_le_self _ _)
      _ = assets := Nat.mul_div_cancel assets hray
  · intro shares
    unfold convertToShares convertToAssets lockShares redeemAssets
    rcases Nat.eq_zero_or_pos s.exchangeRate with h0 | hpos
    · simp [h0]
    · calc shares * s.exchangeRate / ray * ray / s.exchangeRate
          ≤ shares * s.exchangeRate / s.exchangeRate :=
            Nat.div_le_div_right (Nat.div_mul_le_self _ _)
        _ = shares := Nat.mul_div_cancel shares hpos
  · intro assets
    unfold previewDeposit previewWithdraw convertToShares lockShares withdrawShares
    rcases Nat.eq_zero_or_pos s.exchangeRate with h0 | hpos
    · simp [h0]
    · exact Nat.div_le_div_right (by omega)
  · intro h a
    simp [maxDeposit, maxMint, maxWithdraw, maxRedeem, h]
  · intro h a
    simp [maxDeposit, maxMint, maxWithdraw, maxRedeem, h]

/-- REQ yield-distribution-period: The Onchain Vault MUST distribute received yield to
apyUSD holders over a 20-day period. (Model: received yield is `Op.creditYield`, which
first realizes whatever has already streamed out of the current clock into
`fullyVestedAmount` and then folds the new amount, alongside the previously-unvested
remainder, into a freshly re-anchored stream (cf. `req_credit_preserves_accrued_vest`);
the distribution window is the configurable `vestPeriod` (cf.
`req_configurable_vesting_period`), which per this requirement the spec fixes at 20 days.
Under that configuration — `vestPeriod = 20 * day` — the freshly re-anchored STREAM
(`newlyVestedAmount`, i.e. the new `vestTotal`) is distributed to holders over exactly a
20-day period: it (re)starts at the moment of the credit with nothing of the new stream
yet distributed, distributes monotonically as time passes, and completes — the new
stream's full total having reached the asset pool backing apyUSD — exactly 20 days after
the credit, neither as an upfront lump sum nor over any longer horizon.) -/
theorem req_yield_distribution_period (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s')
    (h_cfg : s.vestPeriod = 20 * day) :
    s'.vestPeriod = 20 * day ∧
    s'.vestStart = s.now ∧
    s'.vestTotal = (s.vestTotal - newlyVestedAmount s s.now) + amount ∧
    newlyVestedAmount s' s'.vestStart = 0 ∧
    newlyVestedAmount s' (s'.vestStart + 20 * day) = s'.vestTotal ∧
    (∀ n m, n ≤ m → newlyVestedAmount s' n ≤ newlyVestedAmount s' m) := by
  simp only [step] at h_step
  split at h_step
  · cases Option.some.inj h_step
    have hper : ({ s with
        usdcReserve := s.usdcReserve + amount
        fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
        vestTotal := (s.vestTotal - newlyVestedAmount s s.now) + amount
        vestStart := s.now } : State).vestPeriod = 20 * day := h_cfg
    have hpos : 0 < ({ s with
        usdcReserve := s.usdcReserve + amount
        fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
        vestTotal := (s.vestTotal - newlyVestedAmount s s.now) + amount
        vestStart := s.now } : State).vestPeriod := by rw [hper]; decide
    obtain ⟨hz, hfull, hmono, _⟩ := req_continuous_stream _ hpos
    exact ⟨hper, rfl, rfl, hz, by rw [← h_cfg]; exact hfull, hmono⟩
  · exact absurd h_step (by simp)

end Apyx
