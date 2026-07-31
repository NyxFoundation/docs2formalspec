import D2fsSpecs.Safety

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
ids below `nextUnlockId`, so `List.range s.nextUnlockId` is a finite domain to fold over. That
last clause is the load-bearing one and it is **proved** rather than assumed — `RegistryBounded`
below, preserved by fresh allocation, is what makes "complete" mean complete.

Scope: `netValue` is a coercion of a `Nat`, so it is non-negative in **every** state by
construction — not because Apyx holders carry no debt, though they do not. The signedness
therefore buys expressiveness only one level up, at `netDelta`, which is where a deficit becomes
representable. The per-account solvency family of `docs/06` §8 remains inapplicable to Apyx by
design (§8.1: aggregate ledger, no per-position collateral).
-/

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
flexible entry, so **provided** the fresh id carries no flexible entry — the hypothesis, which
`flex_unallocated_at_counter` discharges from the registry invariant — the flexible sum is
unchanged. -/
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

/-! ## The invariant the measure's completeness rests on

`stdPositions`/`flexPositions` fold over `List.range s.nextUnlockId`, so they **silently drop**
any registry entry at an id at or above the counter. Calling `holderValue` "everything `a` owns"
is therefore conditional on no such entry existing — which this module used to assert in prose and
never prove.

It is proved now, and in the core model rather than here: `Apyx.RegistryBounded`, with
`Apyx.flex_unallocated_at_counter` discharging the `h_unalloc_flex` hypothesis that several
theorems below carry, and `Apyx.registryBounded_createStandardUnlock` showing fresh allocation
preserves it. It sits in `Apyx.lean` because `BlastRadius.lean` needs the companion pointer
invariant and does not import this module.
-/

/-! ## The holder-centric law, as a general theorem

This is what the module exists for: under the *complete* measure, filing a standard redemption
does not move the filer's value. `Safety.valueAt` reported a strict fall here, purely because the
position the burn turns into was unmeasured.
-/

/-- **Filing a standard redemption is value-neutral for the filer**, under the complete measure —
on the fresh-position branch, with a balance that covers the amount and a registry whose fresh id
carries no flexible entry (`h_unalloc_flex`, discharged by `flex_unallocated_at_counter`).

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

/-! ## The bridge to `Safety.valueAt`

Making the relationship explicit, rather than leaving readers to compare two definitions by eye.
`Safety.callerValue` is exactly `holderValue` minus the two position sums — so every
`caller_value_*` theorem in `Safety.lean` is a statement about an *under*-count of what the
address owns, strict exactly when the address has a pending position and an equality otherwise.
The gap is precisely the pending-redemption channel.
-/

/-- `Safety.callerValue` is `holderValue` with the positions removed. -/
theorem callerValue_add_positions (s : State) (a : Address) :
    callerValue s a + stdPositions s a + flexPositions s a = holderValue s a := by
  unfold callerValue valueAt holderValue
  omega

/-- So the old measure never over-counts. -/
theorem callerValue_le_holderValue (s : State) (a : Address) :
    callerValue s a ≤ holderValue s a := by
  have h := callerValue_add_positions s a
  omega

/-- **What `caller_value_withdraw_fixedRate`'s "fall" actually is.** Withdrawing to yourself moves
none of your apxUSD or USDC, and the payout appears in your standard-position sum at face value.
(The flexible column is not among the conjuncts below — for that see `holder_value_withdraw`,
which needs `h_unalloc_flex` to say anything about it.)

`Safety.caller_value_withdraw_fixedRate` records this step as a decrease, and that reading is an
artifact of the missing term: `apxUSDBal` and `usdcBal` are untouched, so everything the old
measure saw leave went into the position it was not counting. -/
theorem withdraw_to_self_moves_only_shares (s : State) (assets : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.withdraw assets caller) caller = some s') :
    stdPositions s' caller = stdPositions s caller + assets ∧
    s'.apxUSDBal caller = s.apxUSDBal caller ∧
    s'.usdcBal caller = s.usdcBal caller := by
  refine ⟨withdraw_receiver_position_gain s assets caller caller s' h_step, ?_, ?_⟩
  · have hpost : s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller
              (withdrawShares assets (computeExchangeRate (pullVestedYield s))) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller
              (withdrawShares assets (computeExchangeRate (pullVestedYield s)))).vaultApxUSDBal
                - assets }
          caller assets)) "Withdraw"
        [caller, caller, caller, assets,
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
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  · have hpost : s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller
              (withdrawShares assets (computeExchangeRate (pullVestedYield s))) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller
              (withdrawShares assets (computeExchangeRate (pullVestedYield s)))).vaultApxUSDBal
                - assets }
          caller assets)) "Withdraw"
        [caller, caller, caller, assets,
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
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

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

/-- **The loss is a first-class quantity.** `-50`, not a truncated `Nat` subtraction.

    Note who does what: the lossy trace begins with `updateRedemptionValue`, which is **admin**-
    gated (address `7` is `hvr0.admin`), so the counterparty alone cannot produce it. The two
    traces differ by an admin reprice, not by a counterparty choice — the timing option is real
    but it is the *second* half of a two-role sequence. -/
example : netDelta hvr0 hvRLate 1 = -50 := by decide

/-- Both traces consume the request, so the holder has no second attempt. -/
example : hvRNow.rfqRequests 1 = 0 ∧ hvRLate.rfqRequests 1 = 0 := by decide

/-! ## The `caller_value_*` family, restated against the complete measure

`README` §9.3 left one item of the value-ledger work open: `Safety.lean`'s `caller_value_*`
theorems still price the caller with the incomplete `valueAt`. This section closes it.

`holderValueAt` is the rate-parameterized form of `holderValue`, mirroring `Safety.valueAt`'s
explicit-rate discipline (the reason for it is unchanged: three of the five ops move the live
rate within the step, so a clean single-step bound must price pre- and post-state at one rate).

The five op families split by what they do to the unlock registry:

* `depositUSDC`, `lockApxUSD`, `redeemApxUSD` never touch it, so the old theorems lift
  directly: the same bound, now over everything the caller owns.
* `withdraw`, `redeem` are the interesting pair — the payout lands in a position the old
  measure could not see, so `caller_value_withdraw_fixedRate`'s "the caller's value falls"
  was an artifact. The honest complete-measure statement is a **no-gain** law, and it must be
  priced at the rate the step executes at (`computeExchangeRate (pullVestedYield s)`): the
  shares are burned at that rate, so at any *other* rate the burned value and the credited
  position need not balance. What makes it true is the rounding direction — `withdrawShares`
  rounds the share cost **up**, so the value leaving the share column covers the `assets`
  arriving in the position column, and floor-division superadditivity does the rest.
-/

/-- `holderValue` at an explicit rate `R` — the complete-measure counterpart of
`Safety.valueAt`. -/
def holderValueAt (R : Nat) (s : State) (a : Address) : Nat :=
  valueAt R s a + stdPositions s a + flexPositions s a

/-- At the state's own live rate, the parameterized form is `holderValue`. -/
theorem holderValueAt_live (s : State) (a : Address) :
    holderValueAt (computeExchangeRate s) s a = holderValue s a := rfl

@[simp] private theorem pv_apxUSDBal' (s : State) :
    (pullVestedYield s).apxUSDBal = s.apxUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_apyUSDBal' (s : State) :
    (pullVestedYield s).apyUSDBal = s.apyUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_usdcBal' (s : State) :
    (pullVestedYield s).usdcBal = s.usdcBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_flexibleUnlockRequests' (s : State) :
    (pullVestedYield s).flexibleUnlockRequests = s.flexibleUnlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

/-- Registry-frame congruence for the flexible sum (mirror of `stdPositions_congr_on`,
with the registry equality taken whole because that is what the frame facts provide). -/
private theorem flexPositions_congr_on (s s' : State) (a : Address)
    (hn : s'.nextUnlockId = s.nextUnlockId)
    (h : s'.flexibleUnlockRequests = s.flexibleUnlockRequests) :
    flexPositions s' a = flexPositions s a := by
  unfold flexPositions
  rw [hn]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [flexAmt, h]

/-- A step that grows the id counter by one without writing the flexible registry leaves the
flexible sum alone — provided the fresh id was unallocated, the same reachability-shaped
hypothesis `requestUnlock_holderValue_neutral` takes. -/
private theorem flexPositions_of_fresh_id (s s' : State) (a : Address)
    (hnext : s'.nextUnlockId = s.nextUnlockId + 1)
    (hflex : s'.flexibleUnlockRequests = s.flexibleUnlockRequests)
    (h_unalloc : s.flexibleUnlockRequests s.nextUnlockId = none) :
    flexPositions s' a = flexPositions s a := by
  unfold flexPositions
  rw [hnext, List.range_succ, List.map_append, List.sum_append]
  have hagree : (List.range s.nextUnlockId).map (flexAmt s' a)
      = (List.range s.nextUnlockId).map (flexAmt s a) := by
    apply List.map_congr_left
    intro i _
    simp [flexAmt, hflex]
  have hlast : flexAmt s' a s.nextUnlockId = 0 := by
    simp [flexAmt, hflex, h_unalloc]
  rw [hagree]
  simp [hlast]

/-! ### Local step inversions

`Safety.lean`'s `inv_*` lemmas are `private` to that file, so the post-state shapes are
re-derived here — the same pattern this module already uses for `withdraw`/`redeem`. The
`withdraw` form additionally surfaces the zero-share guard, which the no-gain arithmetic
needs: a positive withdrawal costing zero shares is exactly the `Regression.lean` §R4b
drain, and the model refuses it. -/

private theorem post_depositUSDC (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.depositUSDC amount) caller = some s') :
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
        · exact (Option.some.inj h).symm

private theorem post_lockApxUSD (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.lockApxUSD amount) caller = some s') :
    s' = emitEvent (updateExchangeRate (mintApyUSD
          { burnApxUSD s caller amount with
            vaultApxUSDBal := (burnApxUSD s caller amount).vaultApxUSDBal + amount }
          caller (lockShares amount (computeExchangeRate s))))
      "Deposit" [caller, caller, caller, amount, lockShares amount (computeExchangeRate s)] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact (Option.some.inj h).symm

private theorem post_redeemApxUSD (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.redeemApxUSD amount) caller = some s') :
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
          · split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · exact (Option.some.inj h).symm

private theorem inv_withdraw' (s : State) (assets : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    ¬(0 < assets ∧ withdrawShares assets (computeExchangeRate (pullVestedYield s)) = 0) ∧
    withdrawShares assets (computeExchangeRate (pullVestedYield s))
      ≤ (pullVestedYield s).apyUSDBal caller ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller
              (withdrawShares assets (computeExchangeRate (pullVestedYield s))) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller
              (withdrawShares assets (computeExchangeRate (pullVestedYield s)))).vaultApxUSDBal
                - assets }
          receiver assets)) "Withdraw"
      [caller, receiver, caller, assets,
        withdrawShares assets (computeExchangeRate (pullVestedYield s))] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact ⟨by assumption, by omega, (Option.some.inj h).symm⟩

private theorem inv_redeem' (s : State) (shares : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.redeem shares receiver) caller = some s') :
    shares ≤ (pullVestedYield s).apyUSDBal caller ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller shares with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal
              - redeemAssets shares (computeExchangeRate (pullVestedYield s)) }
          receiver (redeemAssets shares (computeExchangeRate (pullVestedYield s))))) "Withdraw"
      [caller, receiver, caller,
        redeemAssets shares (computeExchangeRate (pullVestedYield s)), shares] := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact ⟨by omega, (Option.some.inj h).symm⟩

/-! ### The rounding arithmetic

Three `Nat` facts carry the two vault cases. Floor division is superadditive
(`x/d + y/d ≤ (x+y)/d`), so splitting a share balance can only lose dust; and the
**ceil**-rounded `withdrawShares` covers its `assets` — the share cost, priced back at the
same rate, is at least what the position receives. The zero-share guard is load-bearing:
without it `withdrawShares` returns 0 at a zero rate and the covering fact is false. -/

private theorem div_add_div_le (x y d : Nat) : x / d + y / d ≤ (x + y) / d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · rw [Nat.le_div_iff_mul_le h, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x d) (Nat.div_mul_le_self y d)

/-- Splitting a share balance across a burn loses at most dust, never gains:
the two pieces, each floor-priced, never exceed the whole floor-priced. -/
private theorem redeemAssets_superadd (b c R : Nat) (h : c ≤ b) :
    redeemAssets (b - c) R + redeemAssets c R ≤ redeemAssets b R := by
  unfold redeemAssets
  have hsplit := div_add_div_le ((b - c) * R) (c * R) ray
  rwa [← Nat.add_mul, Nat.sub_add_cancel h] at hsplit

/-- The ceil-rounded share cost of a withdrawal, floor-priced back at the same rate,
covers the withdrawn assets. Needs the cost to be nonzero — at `R = 0` the cost is 0
and covers nothing, which is exactly the state the step's zero-share guard refuses. -/
private theorem withdrawShares_covers (assets R : Nat)
    (hW : withdrawShares assets R ≠ 0) :
    assets ≤ redeemAssets (withdrawShares assets R) R := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR; simp [withdrawShares] at hW
  · have hray : 0 < ray := Nat.pow_pos (by decide)
    unfold withdrawShares redeemAssets
    have hmod := Nat.div_add_mod (assets * ray + R - 1) R
    have hlt : (assets * ray + R - 1) % R < R := Nat.mod_lt _ hR
    have h1 : assets * ray ≤ R * ((assets * ray + R - 1) / R) := by omega
    rw [Nat.le_div_iff_mul_le hray]
    calc assets * ray ≤ R * ((assets * ray + R - 1) / R) := h1
      _ = ((assets * ray + R - 1) / R) * R := Nat.mul_comm _ _

/-- The composed fact the `withdraw` case needs: after burning the ceil-rounded share cost,
the remaining share value plus the withdrawn `assets` never exceeds the original share
value — at the one rate everything in the step is priced at. -/
private theorem redeemAssets_sub_withdraw_le (b assets R : Nat)
    (hle : withdrawShares assets R ≤ b)
    (hguard : ¬(0 < assets ∧ withdrawShares assets R = 0)) :
    redeemAssets (b - withdrawShares assets R) R + assets ≤ redeemAssets b R := by
  rcases Nat.eq_zero_or_pos assets with ha | ha
  · subst ha
    have hmono : redeemAssets (b - withdrawShares 0 R) R ≤ redeemAssets b R := by
      unfold redeemAssets
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    omega
  · have hW : withdrawShares assets R ≠ 0 := fun h0 => hguard ⟨ha, h0⟩
    have hcov := withdrawShares_covers assets R hW
    have hsup := redeemAssets_superadd b (withdrawShares assets R) R hle
    omega

/-! ### The restated family -/

/-- `depositUSDC`, complete measure: exactly unchanged at the fixed pre-step rate — the 1:1
USDC/apxUSD swap was already exact under `valueAt`, and the op never touches the unlock
registry. Lift of `Safety.caller_value_depositUSDC`. -/
theorem holder_value_depositUSDC (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    holderValueAt (computeExchangeRate s) s' caller = holderValue s caller := by
  have hpost := post_depositUSDC s amount caller s' h_step
  have hnext : s'.nextUnlockId = s.nextUnlockId := by
    rw [hpost]; simp [emitEvent, mintApxUSD]
  have hreq : s'.unlockRequests = s.unlockRequests := by
    rw [hpost]; simp [emitEvent, mintApxUSD]
  have hflexreg : s'.flexibleUnlockRequests = s.flexibleUnlockRequests := by
    rw [hpost]; simp [emitEvent, mintApxUSD]
  have hstd : stdPositions s' caller = stdPositions s caller :=
    stdPositions_congr_on s' s caller s.nextUnlockId hnext rfl (fun i _ => by rw [hreq])
  have hflex : flexPositions s' caller = flexPositions s caller :=
    flexPositions_congr_on s s' caller hnext hflexreg
  have hval := caller_value_depositUSDC s amount caller s' h_step
  show valueAt (computeExchangeRate s) s' caller + stdPositions s' caller
      + flexPositions s' caller = holderValue s caller
  rw [hval, hstd, hflex]
  exact callerValue_add_positions s caller

/-- `depositUSDC` never moves the exchange rate, so the complete measure is exactly
unchanged at the live rate too. -/
theorem holder_value_depositUSDC_live (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    holderValue s' caller = holderValue s caller := by
  have hpost := post_depositUSDC s amount caller s' h_step
  have hr : computeExchangeRate s' = computeExchangeRate s := by
    rw [hpost]
    simp [emitEvent, mintApxUSD, computeExchangeRate, totalAssets, vestedAmount,
      newlyVestedAmount]
  rw [← holderValueAt_live, hr]
  exact holder_value_depositUSDC s amount caller s' h_step

/-- `lockApxUSD`, complete measure: non-increasing at the fixed pre-step rate — floor-rounded
share minting cannot manufacture value, and the op never touches the unlock registry. Lift of
`Safety.caller_value_lockApxUSD_fixedRate`; the live-rate reading stays honestly out of scope
for the same S4 pool-appreciation reason as there. -/
theorem holder_value_lockApxUSD_fixedRate (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    holderValueAt (computeExchangeRate s) s' caller ≤ holderValue s caller := by
  have hpost := post_lockApxUSD s amount caller s' h_step
  have hnext : s'.nextUnlockId = s.nextUnlockId := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hreq : s'.unlockRequests = s.unlockRequests := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hflexreg : s'.flexibleUnlockRequests = s.flexibleUnlockRequests := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hstd : stdPositions s' caller = stdPositions s caller :=
    stdPositions_congr_on s' s caller s.nextUnlockId hnext rfl (fun i _ => by rw [hreq])
  have hflex : flexPositions s' caller = flexPositions s caller :=
    flexPositions_congr_on s s' caller hnext hflexreg
  have hval := caller_value_lockApxUSD_fixedRate s amount caller s' h_step
  show valueAt (computeExchangeRate s) s' caller + stdPositions s' caller
      + flexPositions s' caller ≤ holderValue s caller
  rw [hstd, hflex, ← callerValue_add_positions s caller]
  omega

/-- `redeemApxUSD`, complete measure: non-increasing at the fixed pre-step rate, under the
standing `redemptionValue ≤ ray` no-premium invariant. Lift of
`Safety.caller_value_redeemApxUSD`; the registry is untouched. -/
theorem holder_value_redeemApxUSD (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s')
    (h_rv : s.redemptionValue ≤ ray) :
    holderValueAt (computeExchangeRate s) s' caller ≤ holderValue s caller := by
  have hpost := post_redeemApxUSD s amount caller s' h_step
  have hnext : s'.nextUnlockId = s.nextUnlockId := by
    rw [hpost]; simp [emitEvent, burnApxUSD]
  have hreq : s'.unlockRequests = s.unlockRequests := by
    rw [hpost]; simp [emitEvent, burnApxUSD]
  have hflexreg : s'.flexibleUnlockRequests = s.flexibleUnlockRequests := by
    rw [hpost]; simp [emitEvent, burnApxUSD]
  have hstd : stdPositions s' caller = stdPositions s caller :=
    stdPositions_congr_on s' s caller s.nextUnlockId hnext rfl (fun i _ => by rw [hreq])
  have hflex : flexPositions s' caller = flexPositions s caller :=
    flexPositions_congr_on s s' caller hnext hflexreg
  have hval := caller_value_redeemApxUSD s amount caller s' h_step h_rv
  show valueAt (computeExchangeRate s) s' caller + stdPositions s' caller
      + flexPositions s' caller ≤ holderValue s caller
  rw [hstd, hflex, ← callerValue_add_positions s caller]
  omega

/-- `redeemApxUSD` never moves the exchange rate: the bound holds at the live rate,
unqualified. -/
theorem holder_value_redeemApxUSD_live (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.redeemApxUSD amount) caller = some s')
    (h_rv : s.redemptionValue ≤ ray) :
    holderValue s' caller ≤ holderValue s caller := by
  have hpost := post_redeemApxUSD s amount caller s' h_step
  have hr : computeExchangeRate s' = computeExchangeRate s := by
    rw [hpost]
    simp [emitEvent, burnApxUSD, computeExchangeRate, totalAssets, vestedAmount,
      newlyVestedAmount]
  rw [← holderValueAt_live, hr]
  exact holder_value_redeemApxUSD s amount caller s' h_step h_rv

/-- **`withdraw`, complete measure: a no-gain law, priced at the execution rate.**

This is the theorem `caller_value_withdraw_fixedRate` was standing in for. That statement's
"the caller's value falls" was an artifact of the missing position term; the honest claim is
that the caller cannot come out *ahead*, and it holds at the rate the step actually executes
at — `computeExchangeRate (pullVestedYield s)`, the rate the share cost is ceil-rounded at.
Pricing at any other rate mixes denominators: a stale rate under-prices the burned shares
and the step would (spuriously) read as a gain.

Any `receiver`: if the position goes to someone else the caller pays (the bound is `≤`, and it is
not strict at `assets = 0`); if to the caller, the ceil-rounded share cost covers the position
credit (`withdrawShares_covers`), with the zero-share guard (`Regression.lean` §R4b) supplying the
nonzero cost. Assumes `h_unalloc_flex`, which `flex_unallocated_at_counter` discharges. -/
theorem holder_value_withdraw (s : State) (assets : Nat) (receiver caller : Address)
    (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s')
    (h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none) :
    holderValueAt (computeExchangeRate (pullVestedYield s)) s' caller
      ≤ holderValueAt (computeExchangeRate (pullVestedYield s)) s caller := by
  obtain ⟨hguard, hWle, hpost⟩ := inv_withdraw' s assets receiver caller s' h_step
  rw [pv_apyUSDBal'] at hWle
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller
      - withdrawShares assets (computeExchangeRate (pullVestedYield s)) := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hnext : s'.nextUnlockId = s.nextUnlockId + 1 := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hold : ∀ i, i < s.nextUnlockId → s'.unlockRequests i = s.unlockRequests i := by
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt hi
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hne]
  have hnew : s'.unlockRequests s.nextUnlockId
      = some (receiver, assets, s.now + cooldownPeriod) := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hflexreg : s'.flexibleUnlockRequests = s.flexibleUnlockRequests := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hstd : stdPositions s' caller
      = stdPositions s caller + (if receiver = caller then assets else 0) :=
    stdPositions_of_fresh_entry s s' receiver assets (s.now + cooldownPeriod) caller
      hnext hold hnew
  have hflex : flexPositions s' caller = flexPositions s caller :=
    flexPositions_of_fresh_id s s' caller hnext hflexreg h_unalloc_flex
  have hkey := redeemAssets_sub_withdraw_le (s.apyUSDBal caller) assets
    (computeExchangeRate (pullVestedYield s)) hWle hguard
  show valueAt _ s' caller + stdPositions s' caller + flexPositions s' caller
      ≤ valueAt _ s caller + stdPositions s caller + flexPositions s caller
  unfold valueAt
  rw [hx, hy, hu, hstd, hflex]
  split
  · omega
  · have hmono : redeemAssets (s.apyUSDBal caller
        - withdrawShares assets (computeExchangeRate (pullVestedYield s)))
          (computeExchangeRate (pullVestedYield s))
        ≤ redeemAssets (s.apyUSDBal caller) (computeExchangeRate (pullVestedYield s)) := by
      unfold redeemAssets
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    omega

/-- **`redeem`, complete measure: the same no-gain law**, at the same execution rate. Simpler
than `withdraw`: the position credit *is* the floor-priced value of the burned shares, so
floor superadditivity alone closes it — no ceil fact, no zero-share guard needed (at a zero
rate the caller burns shares for a zero-amount position, a pure loss, and the bound is
slack). -/
theorem holder_value_redeem (s : State) (shares : Nat) (receiver caller : Address)
    (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s')
    (h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none) :
    holderValueAt (computeExchangeRate (pullVestedYield s)) s' caller
      ≤ holderValueAt (computeExchangeRate (pullVestedYield s)) s caller := by
  obtain ⟨hle, hpost⟩ := inv_redeem' s shares receiver caller s' h_step
  rw [pv_apyUSDBal'] at hle
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller - shares := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
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
  have hflexreg : s'.flexibleUnlockRequests = s.flexibleUnlockRequests := by
    rw [hpost]; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hstd : stdPositions s' caller
      = stdPositions s caller + (if receiver = caller then
          redeemAssets shares (computeExchangeRate (pullVestedYield s)) else 0) :=
    stdPositions_of_fresh_entry s s' receiver
      (redeemAssets shares (computeExchangeRate (pullVestedYield s)))
      (s.now + cooldownPeriod) caller hnext hold hnew
  have hflex : flexPositions s' caller = flexPositions s caller :=
    flexPositions_of_fresh_id s s' caller hnext hflexreg h_unalloc_flex
  have hkey := redeemAssets_superadd (s.apyUSDBal caller) shares
    (computeExchangeRate (pullVestedYield s)) hle
  show valueAt _ s' caller + stdPositions s' caller + flexPositions s' caller
      ≤ valueAt _ s caller + stdPositions s caller + flexPositions s caller
  unfold valueAt
  rw [hx, hy, hu, hstd, hflex]
  split
  · omega
  · have hmono : redeemAssets (s.apyUSDBal caller - shares)
          (computeExchangeRate (pullVestedYield s))
        ≤ redeemAssets (s.apyUSDBal caller) (computeExchangeRate (pullVestedYield s)) := by
      unfold redeemAssets
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    omega

/-- **S6, complete-measure umbrella**: for each of the five op families
`Safety.caller_net_nonpositive` covers, **there exists** a pricing rate under which one step does
not raise the caller's *complete* holdings (balances, shares, and pending positions). For
`depositUSDC`/`lockApxUSD`/`redeemApxUSD` that rate is `computeExchangeRate s`; for
`withdraw`/`redeem` it is `computeExchangeRate (pullVestedYield s)` — the per-op theorems above
name each one and carry the exact (in)equality.

**Three things this does not say.** The rate is existentially quantified here, so the statement on
its own is weaker than the per-op theorems it packages. Because the rate *differs by family*, these
bounds do **not** chain along a trace — there is no `execTrace` statement anywhere in this module.
And it inherits two hypotheses: `redemptionValue ≤ ray`, and a registry whose fresh id carries no
flexible entry (`flex_unallocated_at_counter` discharges the second).

What it does do is retire the old umbrella's caveat that its ledger "does not track the
unlock-registry column": the column is tracked now, and the single-step bound survives. -/
theorem caller_net_nonpositive_complete (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (h_rv : s.redemptionValue ≤ ray)
    (h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none)
    (h_case :
      (∃ amount, op = Op.depositUSDC amount) ∨
      (∃ amount, op = Op.lockApxUSD amount) ∨
      (∃ amount, op = Op.redeemApxUSD amount) ∨
      (∃ amount r, op = Op.withdraw amount r) ∨
      (∃ shares r, op = Op.redeem shares r)) :
    ∃ R, holderValueAt R s' caller ≤ holderValueAt R s caller := by
  rcases h_case with ⟨amount, rfl⟩ | ⟨amount, rfl⟩ | ⟨amount, rfl⟩ | ⟨amount, r, rfl⟩
    | ⟨shares, r, rfl⟩
  · exact ⟨computeExchangeRate s,
      Nat.le_of_eq (holder_value_depositUSDC s amount caller s' h_step)⟩
  · exact ⟨computeExchangeRate s, holder_value_lockApxUSD_fixedRate s amount caller s' h_step⟩
  · exact ⟨computeExchangeRate s, holder_value_redeemApxUSD s amount caller s' h_step h_rv⟩
  · exact ⟨computeExchangeRate (pullVestedYield s),
      holder_value_withdraw s amount r caller s' h_step h_unalloc_flex⟩
  · exact ⟨computeExchangeRate (pullVestedYield s),
      holder_value_redeem s shares r caller s' h_step h_unalloc_flex⟩

end Apyx
