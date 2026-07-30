import D2fsSpecs.BlastRadius

/-!
# A complete, signed, per-holder value ledger (`docs/06` §7.3 E3)

Two gaps in the existing safety statements are closed here, and they are the same gap seen from
two angles.

**The measure was incomplete.** `Safety.valueAt` prices an address's holdings as
`apxUSDBal + redeemAssets apyUSDBal + usdcBal` and **omits pending unlock positions** — which is
exactly where `requestUnlock`, `withdraw` and `redeem` put the payout. So
`caller_value_withdraw_fixedRate` could say "your measured value falls when you withdraw" only
because the proceeds were not being measured. Two independent reviews flagged this; it is the
substance of the "ある人視点" question — is the property stated from a named holder's point of
view, over everything that holder actually owns?

**The measure was unsigned.** `docs/06` §7.3 E3 asks for `netValue : State → Address → Int`,
because in `Nat` a loss is not a first-class quantity: `x - y` truncates at 0, so "this holder
ended 50 worse off" has to be encoded as a pair of inequalities and any statement about a
*deficit* is unrepresentable rather than false.

`holderValue` below is the complete measure, and `netValue` is its signed form. The summation
`docs/06` said the aggregate ledger could not express is available after all: positions live at
ids below `nextUnlockId`, so `List.range s.nextUnlockId` is a finite domain to fold over.

Scope: Apyx holders carry no debt, so `netValue` is never negative in a reachable state — the
`Int` is here to make *changes* honest, not to model insolvency. The per-account solvency family
of `docs/06` §8 remains inapplicable to Apyx by design (§8.1: aggregate ledger, no per-position
collateral).
-/

set_option maxRecDepth 20000

namespace Apyx

/-! ## The positions the old measure dropped -/

/-- What id `i` contributes to `a`'s standard-position total: the amount if `a` owns the
position there, otherwise nothing. -/
def stdAmt (s : State) (a : Address) (i : Nat) : Nat :=
  match s.unlockRequests i with
  | some (o, amt, _) => if o = a then amt else 0
  | none => 0

/-- Same, for flexible positions. -/
def flexAmt (s : State) (a : Address) (i : Nat) : Nat :=
  match s.flexibleUnlockRequests i with
  | some (o, amt, _, _) => if o = a then amt else 0
  | none => 0

/-- apxUSD held inside `a`'s pending **standard** unlock positions.

Summed over `List.range s.nextUnlockId`: `createStandardUnlock` only ever allocates at the
current counter and then increments it, so every live position sits at an id strictly below it.
That bound is what makes a `Σ` over positions available in a model whose registry is a bare
function — the summation `docs/06` recorded as unavailable. -/
def stdPositions (s : State) (a : Address) : Nat :=
  ((List.range s.nextUnlockId).map (stdAmt s a)).sum

/-- apxUSD held inside `a`'s pending **flexible** unlock positions. Same sum, same bound. -/
def flexPositions (s : State) (a : Address) : Nat :=
  ((List.range s.nextUnlockId).map (flexAmt s a)).sum

/-- Everything `a` owns, in apxUSD units, priced at the state's **live** rate.

The three terms the old `valueAt` had, plus the two it dropped. apxUSD and USDC are both counted
at par (the model treats them as commensurate — see `model.md` §5, "No decimal scaling"), apyUSD
is converted through `redeemAssets` at `computeExchangeRate`, and pending positions are counted
at face because that is what they settle to. -/
def holderValue (s : State) (a : Address) : Nat :=
  s.apxUSDBal a
  + redeemAssets (s.apyUSDBal a) (computeExchangeRate s)
  + s.usdcBal a
  + stdPositions s a
  + flexPositions s a

/-- The signed form (`docs/06` §7.3 E3). Differences of `netValue` are genuine signed
quantities, so a holder's loss across a step or a trace is expressible directly rather than as
a truncated `Nat` subtraction. -/
def netValue (s : State) (a : Address) : Int := (holderValue s a : Int)

/-- The signed change in `a`'s net value across a step. Negative means `a` lost value — the
statement `Nat` could not make. -/
def netDelta (s s' : State) (a : Address) : Int := netValue s' a - netValue s a

/-! ## Making the position sum computable across a step

Two facts suffice: the sum splits over `++`, and it depends on the registry only at the ids it
visits. `List.range_succ` then handles the one-id growth a fresh position causes.
-/

/-- The sum only depends on the registry at the ids it visits. -/
theorem stdPositions_congr_on (s s' : State) (a : Address) (n : Nat)
    (hn : s.nextUnlockId = n) (hn' : s'.nextUnlockId = n)
    (h : ∀ i, i < n → s.unlockRequests i = s'.unlockRequests i) :
    stdPositions s a = stdPositions s' a := by
  unfold stdPositions
  rw [hn, hn']
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [stdAmt, h i (List.mem_range.mp hi)]

/-- **Creating a fresh position adds exactly its amount to the owner's sum**, and nothing to
anyone else's. This is the general form the module's witnesses were standing in for. -/
theorem stdPositions_createStandardUnlock (s : State) (owner : Address) (amount : Nat)
    (a : Address) :
    stdPositions (createStandardUnlock s owner amount) a
      = stdPositions s a + (if owner = a then amount else 0) := by
  have hnext : (createStandardUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 := rfl
  unfold stdPositions
  rw [hnext, List.range_succ, List.map_append, List.sum_append]
  have hagree : ((List.range s.nextUnlockId).map (stdAmt (createStandardUnlock s owner amount) a))
      = (List.range s.nextUnlockId).map (stdAmt s a) := by
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt (List.mem_range.mp hi)
    simp [stdAmt, createStandardUnlock, hne]
  rw [hagree]
  congr 1
  simp [stdAmt, createStandardUnlock]

/-- A fresh standard position never touches the flexible sum: `createStandardUnlock` writes no
flexible entry, and the one new id it opens carries none. -/
theorem flexPositions_createStandardUnlock (s : State) (owner : Address) (amount : Nat)
    (a : Address) (h_unalloc : s.flexibleUnlockRequests s.nextUnlockId = none) :
    flexPositions (createStandardUnlock s owner amount) a = flexPositions s a := by
  have hnext : (createStandardUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 := rfl
  have hflex : (createStandardUnlock s owner amount).flexibleUnlockRequests
      = s.flexibleUnlockRequests := rfl
  unfold flexPositions
  rw [hnext, List.range_succ, List.map_append, List.sum_append]
  have hagree : ((List.range s.nextUnlockId).map (flexAmt (createStandardUnlock s owner amount) a))
      = (List.range s.nextUnlockId).map (flexAmt s a) := by
    apply List.map_congr_left
    intro i _
    simp [flexAmt, hflex]
  have hlast : flexAmt (createStandardUnlock s owner amount) a s.nextUnlockId = 0 := by
    simp [flexAmt, hflex, h_unalloc]
  rw [hagree]
  simp [hlast]

/-! ## The holder-centric law, as a general theorem

This is what the module exists for: under the *complete* measure, filing a standard redemption
does not move the filer's value. `Safety.valueAt` reported a strict fall here, purely because the
position the burn turns into was unmeasured.
-/

/-- **Filing a standard redemption is value-neutral for the filer**, under the complete measure.

The fresh-position branch: the caller has no live standard position, so `requestUnlockStep` takes
the `createStandardUnlock` route. The apxUSD leaves the balance and reappears in the position, at
face, and every other term of `holderValue` is untouched — `requestUnlock` moves no shares, no
USDC, and nothing the live rate depends on. -/
theorem requestUnlock_holderValue_neutral (s : State) (amount : Nat) (caller : Address)
    (s' : State)
    (h_step : step s (Op.requestUnlock amount) caller = some s')
    (h_fresh : s.unlockRequestId caller = none)
    (h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none)
    (h_bal : amount ≤ s.apxUSDBal caller) :
    holderValue s' caller = holderValue s caller := by
  -- invert the `requestUnlock` branch locally (`Apyx.lean`'s inversion lemma is `private`)
  have hs' : s' = requestUnlockStep s caller amount := by
    simp only [step] at h_step
    split at h_step
    · exact absurd h_step (by simp)
    · split at h_step
      · exact absurd h_step (by simp)
      · exact (Option.some.inj h_step).symm
  subst hs'
  have hstep_eq : requestUnlockStep s caller amount
      = createStandardUnlock (burnApxUSD s caller amount) caller amount := by
    unfold requestUnlockStep
    simp [burnApxUSD, h_fresh]
  rw [hstep_eq]
  unfold holderValue
  have hbal : (createStandardUnlock (burnApxUSD s caller amount) caller amount).apxUSDBal caller
      = s.apxUSDBal caller - amount := by
    simp [createStandardUnlock, burnApxUSD]
  have hstd : stdPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller
      = stdPositions s caller + amount := by
    rw [stdPositions_createStandardUnlock, if_pos rfl]
    congr 1
  have hflex : flexPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller
      = flexPositions s caller := by
    rw [flexPositions_createStandardUnlock (burnApxUSD s caller amount) caller amount caller
      h_unalloc_flex]
    rfl
  have hshares : (createStandardUnlock (burnApxUSD s caller amount) caller amount).apyUSDBal caller
      = s.apyUSDBal caller := by simp [createStandardUnlock, burnApxUSD]
  have husdc : (createStandardUnlock (burnApxUSD s caller amount) caller amount).usdcBal caller
      = s.usdcBal caller := by simp [createStandardUnlock, burnApxUSD]
  have hrate : computeExchangeRate (createStandardUnlock (burnApxUSD s caller amount) caller amount)
      = computeExchangeRate s := by
    simp [computeExchangeRate, totalAssets, vestedAmount, newlyVestedAmount, createStandardUnlock,
      burnApxUSD]
  rw [hbal, hstd, hflex, hshares, husdc, hrate]
  omega

/-- The signed form of the same statement. -/
theorem requestUnlock_netDelta_zero (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.requestUnlock amount) caller = some s')
    (h_fresh : s.unlockRequestId caller = none)
    (h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none)
    (h_bal : amount ≤ s.apxUSDBal caller) :
    netDelta s s' caller = 0 := by
  unfold netDelta netValue
  rw [requestUnlock_holderValue_neutral s amount caller s' h_step h_fresh h_unalloc_flex h_bal]
  omega

/-! ## Where a vault withdrawal's payout goes

`withdraw` and `redeem` differ from `requestUnlock` in two ways that matter.

The position is opened for a named **receiver**, who need not be the caller. And burning shares
moves `totalSupply_apyUSD`, so the step reprices the caller's *remaining* holdings — which means
**full value-neutrality is false for these two operations**, not merely unproved, and this module
does not claim it. What is provable, and what the old measure could not say at all, is where the
payout lands.

The statement below is derived from **projections only** — three facts about `nextUnlockId` and
`unlockRequests` — rather than by substituting the post-state record. Substituting it and rewriting
`stdPositions` against the result hits kernel deep recursion (`maxRecDepth` does not help; it is
the kernel's own limit), which is why the sum is computed from a projection-level lemma.
-/

@[simp] private theorem pv_nextUnlockId' (s : State) :
    (pullVestedYield s).nextUnlockId = s.nextUnlockId := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_unlockRequests' (s : State) :
    (pullVestedYield s).unlockRequests = s.unlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_now' (s : State) : (pullVestedYield s).now = s.now := by
  unfold pullVestedYield; dsimp only; split <;> rfl

/-- The position sum after a fresh entry, computed from projections alone.

Everything `stdPositions` can see is the id counter and the registry, so these three facts
determine it: the counter grew by one, the old ids read the same, and the new id carries the
entry. No post-state record appears. -/
theorem stdPositions_of_fresh_entry (s s' : State) (owner : Address) (amount ce : Nat)
    (a : Address)
    (hnext : s'.nextUnlockId = s.nextUnlockId + 1)
    (hold : ∀ i, i < s.nextUnlockId → s'.unlockRequests i = s.unlockRequests i)
    (hnew : s'.unlockRequests s.nextUnlockId = some (owner, amount, ce)) :
    stdPositions s' a = stdPositions s a + (if owner = a then amount else 0) := by
  unfold stdPositions
  rw [hnext, List.range_succ, List.map_append, List.sum_append]
  have hagree : ((List.range s.nextUnlockId).map (stdAmt s' a))
      = (List.range s.nextUnlockId).map (stdAmt s a) := by
    apply List.map_congr_left
    intro i hi
    simp only [stdAmt, hold i (List.mem_range.mp hi)]
  rw [hagree]
  congr 1
  simp [stdAmt, hnew]

/-- **A vault withdrawal's payout is measured.** The receiver's standard-position sum rises by
exactly the `assets` withdrawn.

This is the term `Safety.valueAt` dropped, and dropping it is why
`caller_value_withdraw_fixedRate` could report a withdrawal as a pure loss to the caller with no
corresponding gain anywhere. -/
theorem withdraw_receiver_position_gain (s : State) (assets : Nat) (receiver caller : Address)
    (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    stdPositions s' receiver = stdPositions s receiver + assets := by
  -- invert once, then read off projections only: `stdPositions s'` is never rewritten against
  -- the post-state record, which is what hits the kernel's recursion limit
  have hpost : s' = emitEvent (updateExchangeRate (createStandardUnlock
        { burnApyUSD (pullVestedYield s) caller
            (withdrawShares assets (computeExchangeRate (pullVestedYield s))) with
          vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller
            (withdrawShares assets (computeExchangeRate (pullVestedYield s)))).vaultApxUSDBal
              - assets }
        receiver assets)) "Withdraw"
      [caller, receiver, caller, assets,
        withdrawShares assets (computeExchangeRate (pullVestedYield s))] := by
    simp only [step] at h_step
    split at h_step
    · exact absurd h_step (by simp)
    · split at h_step
      · exact absurd h_step (by simp)
      · split at h_step
        · exact absurd h_step (by simp)
        · split at h_step
          · exact absurd h_step (by simp)
          · exact (Option.some.inj h_step).symm
  have hnext : s'.nextUnlockId = s.nextUnlockId + 1 := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hold : ∀ i, i < s.nextUnlockId → s'.unlockRequests i = s.unlockRequests i := by
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt hi
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hne]
  have hnew : s'.unlockRequests s.nextUnlockId
      = some (receiver, assets, s.now + cooldownPeriod) := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  rw [stdPositions_of_fresh_entry s s' receiver assets (s.now + cooldownPeriod) receiver
    hnext hold hnew, if_pos rfl]

/-- The same for the share-denominated `redeem`: the receiver's position rises by exactly the
assets the burned shares were priced at. -/
theorem redeem_receiver_position_gain (s : State) (shares : Nat) (receiver caller : Address)
    (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s') :
    stdPositions s' receiver
      = stdPositions s receiver
        + redeemAssets shares (computeExchangeRate (pullVestedYield s)) := by
  have hpost : s' = emitEvent (updateExchangeRate (createStandardUnlock
        { burnApyUSD (pullVestedYield s) caller shares with
          vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal
              - redeemAssets shares (computeExchangeRate (pullVestedYield s)) }
        receiver (redeemAssets shares (computeExchangeRate (pullVestedYield s))))) "Withdraw"
      [caller, receiver, caller,
        redeemAssets shares (computeExchangeRate (pullVestedYield s)), shares] := by
    simp only [step] at h_step
    split at h_step
    · exact absurd h_step (by simp)
    · split at h_step
      · exact absurd h_step (by simp)
      · split at h_step
        · exact absurd h_step (by simp)
        · split at h_step
          · exact absurd h_step (by simp)
          · exact (Option.some.inj h_step).symm
  have hnext : s'.nextUnlockId = s.nextUnlockId + 1 := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hold : ∀ i, i < s.nextUnlockId → s'.unlockRequests i = s.unlockRequests i := by
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt hi
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hne]
  have hnew : s'.unlockRequests s.nextUnlockId
      = some (receiver, redeemAssets shares (computeExchangeRate (pullVestedYield s)),
          s.now + cooldownPeriod) := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  rw [stdPositions_of_fresh_entry s s' receiver
    (redeemAssets shares (computeExchangeRate (pullVestedYield s))) (s.now + cooldownPeriod)
    receiver hnext hold hnew, if_pos rfl]

/-! ## The holder-centric laws

These are the statements the incomplete measure could not make. They are given here as
kernel-checked **witnesses** on concrete states rather than as general theorems: the general
form needs fold lemmas over `List.range (nextUnlockId + 1)` and is scoped as follow-up work in
`README` §9.3 rather than asserted here.
-/

/-- A holder with 100 apxUSD, no shares, no USDC, and an empty registry. -/
def hv0 : State :=
  { (default : State) with
      globalPause := false
      apxUSDBal := fun a => if a = 1 then 100 else 0
      totalSupply_apxUSD := 100 }

/-- After filing a standard redemption for the whole balance. -/
def hv1 : State := execTrace hv0 [(Op.requestUnlock 100, 1)]

/-- The balance really did leave, and a position really was created. -/
example : hv1.apxUSDBal 1 = 0 ∧ hv1.unlockRequests 0 = some (1, 100, cooldownPeriod)
    ∧ hv1.nextUnlockId = 1 := by decide

/-- **The position is now counted.** `stdPositions` sees the 100 that `Safety.valueAt` dropped. -/
example : stdPositions hv0 1 = 0 ∧ stdPositions hv1 1 = 100 := by decide

/-- **Filing is value-neutral under the complete measure.** The signed delta is exactly zero.

Under `Safety.valueAt` — which omits positions — the same step reads as a fall from 100 to 0.
That is the difference between "the holder is not extracting value", which is what the safety
argument needs and is true, and "the holder is losing value", which is what the old measure
said and is false. -/
example : netDelta hv0 hv1 1 = 0 := by decide

/-- Settling the matured position is value-neutral too: the position becomes apxUSD again. -/
def hv2 : State := execTrace hv1 [(Op.tick cooldownPeriod, 0), (Op.claimUnlock 0, 1)]

example : hv2.apxUSDBal 1 = 100 ∧ hv2.unlockRequests 0 = none := by decide
example : netDelta hv1 hv2 1 = 0 := by decide

/-! ## What the signed measure buys

A holder's loss is now a single signed quantity, so it can be *stated*. The witness below is the
timing exposure `BlastRadius.rfq_payout_is_set_by_execution_timing` exhibits: the same holder,
the same request, settled after an honest halving of the redemption price.
-/

/-- A whitelisted holder with an outstanding RFQ request for 100, a funded reserve, and the
    price at par. -/
def hvr0 : State :=
  { (default : State) with
      globalPause := false
      admin := 7
      whitelist := fun _ => true
      rfqCounterparties := [2]
      apxUSDBal := fun a => if a = 1 then 100 else 0
      totalSupply_apxUSD := 100
      rfqRequests := fun a => if a = 1 then 100 else 0
      usdcReserve := 100
      redemptionValue := ray }

/-- Settled immediately: the holder is made whole. -/
def hvRNow : State := execTrace hvr0 [(Op.executeRFQRedemption 1 100, 2)]

/-- Settled after the admin halves the price: the holder takes a 50 loss. -/
def hvRLate : State :=
  execTrace hvr0 [(Op.updateRedemptionValue (ray / 2), 7), (Op.executeRFQRedemption 1 100, 2)]

example : netDelta hvr0 hvRNow 1 = 0 := by decide

/-- **The loss is a first-class quantity.** `-50`, not a truncated `Nat` subtraction — and the
    counterparty chose which of the two traces to run. -/
example : netDelta hvr0 hvRLate 1 = -50 := by decide

/-- Both traces consume the request, so the holder has no second attempt. -/
example : hvRNow.rfqRequests 1 = 0 ∧ hvRLate.rfqRequests 1 = 0 := by decide

end Apyx
