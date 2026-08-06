import D2fsSpecs.Safety
import D2fsSpecs.Registry

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

/-- A fresh flexible position adds exactly its amount to the owner's flexible
position total, provided the shared allocation counter is unoccupied in the
flexible registry. -/
theorem flexPositions_createFlexibleUnlock (s : State) (owner : Address) (amount : Nat)
    (a : Address) :
    flexPositions (createFlexibleUnlock s owner amount) a =
      flexPositions s a + (if owner = a then amount else 0) := by
  have hnext : (createFlexibleUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 := rfl
  unfold flexPositions
  rw [hnext, List.range_succ, List.map_append, List.sum_append]
  have hagree : ((List.range s.nextUnlockId).map (flexAmt (createFlexibleUnlock s owner amount) a))
      = (List.range s.nextUnlockId).map (flexAmt s a) := by
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt (List.mem_range.mp hi)
    simp [flexAmt, createFlexibleUnlock, hne]
  have hlast : flexAmt (createFlexibleUnlock s owner amount) a s.nextUnlockId =
      if owner = a then amount else 0 := by
    simp [flexAmt, createFlexibleUnlock]
  rw [hagree]
  simp [hlast]

/-- A flexible allocation leaves the standard-position sum unchanged, provided
the shared counter is unoccupied in the standard registry. -/
theorem stdPositions_createFlexibleUnlock (s : State) (owner : Address) (amount : Nat)
    (a : Address) (h_unalloc : s.unlockRequests s.nextUnlockId = none) :
    stdPositions (createFlexibleUnlock s owner amount) a = stdPositions s a := by
  have hnext : (createFlexibleUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 := rfl
  unfold stdPositions
  rw [hnext, List.range_succ, List.map_append, List.sum_append]
  have hagree : ((List.range s.nextUnlockId).map (stdAmt (createFlexibleUnlock s owner amount) a))
      = (List.range s.nextUnlockId).map (stdAmt s a) := by
    apply List.map_congr_left
    intro i hi
    simp [stdAmt, createFlexibleUnlock]
  have hlast : stdAmt (createFlexibleUnlock s owner amount) a s.nextUnlockId = 0 := by
    simp [stdAmt, createFlexibleUnlock, h_unalloc]
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

/-! ## Settling a standard position

The request-side conservation law records an amount in the standard registry. The
matching claim-side law removes that same amount from the finite position sum and
mints it back to the recorded owner. The helper below is deliberately generic: it
only says that one member of a finite `List.range` changes by a known amount. The
`id < nextUnlockId` premise is what prevents a position outside the modeled finite
support from being mistaken for an accounted liability.
-/

private theorem sum_range_replace (n id amount : Nat) (f g : Nat → Nat)
    (hid : id < n) (hat : f id = g id + amount)
    (hother : ∀ j, j < n → j ≠ id → f j = g j) :
    ((List.range n).map f).sum = ((List.range n).map g).sum + amount := by
  induction n generalizing id amount f g with
  | zero => omega
  | succ n ih =>
      by_cases hlast : id = n
      · subst id
        have hprefix : ((List.range n).map f).sum = ((List.range n).map g).sum := by
          congr 1
          apply List.map_congr_left
          intro j hj
          have hj' : j < n := List.mem_range.mp hj
          exact hother j (by omega) (by omega)
        simp only [List.range_succ, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [hprefix, hat]
        omega
      · have hid' : id < n := by omega
        have hother' : ∀ j, j < n → j ≠ id → f j = g j := by
          intro j hj hji
          exact hother j (by omega) hji
        have hrec := ih id amount f g hid' hat hother'
        simp only [List.range_succ, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [hrec]
        rw [hother n (by omega) (by omega)]
        omega

/-- The top-up branch changes one existing standard record in place. This is
the sum-level counterpart of `updateStandardUnlock_unlockRequests_eq`: once
the target record is known to be the caller's record, the caller's finite
position total grows by exactly the added amount. -/
theorem stdPositions_updateStandardUnlock (s : State) (id : Nat) (owner : Address)
    (oldAmount oldEnd addAmount : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, oldAmount, oldEnd)) :
    stdPositions (updateStandardUnlock s id owner addAmount) owner
      = stdPositions s owner + addAmount := by
  unfold stdPositions
  have hnext : (updateStandardUnlock s id owner addAmount).nextUnlockId = s.nextUnlockId := by
    simp [updateStandardUnlock, hreq]
  rw [hnext]
  have htarget : stdAmt (updateStandardUnlock s id owner addAmount) owner id =
      stdAmt s owner id + addAmount := by
    simp [stdAmt, updateStandardUnlock, hreq]
  apply sum_range_replace s.nextUnlockId id addAmount
    (stdAmt (updateStandardUnlock s id owner addAmount) owner) (stdAmt s owner)
    hid htarget
  intro j hj hne
  simp [stdAmt, updateStandardUnlock, hreq, hne]

/-- Updating a standard position owned by someone other than `a` does not
change `a`'s finite standard-position total. -/
theorem stdPositions_updateStandardUnlock_of_ne (s : State) (id : Nat) (owner : Address)
    (addAmount : Nat) (a : Address)
    (howner : owner ≠ a)
    (hreq : ∃ oldAmount oldEnd, s.unlockRequests id = some (owner, oldAmount, oldEnd)) :
    stdPositions (updateStandardUnlock s id owner addAmount) a = stdPositions s a := by
  obtain ⟨oldAmount, oldEnd, hentry⟩ := hreq
  unfold stdPositions
  have hnext : (updateStandardUnlock s id owner addAmount).nextUnlockId = s.nextUnlockId := by
    simp [updateStandardUnlock, hentry]
  rw [hnext]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hne : i = id
  · subst i
    simp [stdAmt, updateStandardUnlock, hentry, howner]
  · simp [stdAmt, updateStandardUnlock, hentry, hne]

/-- A standard top-up changes no flexible registry entry, so it leaves the
flexible-position sum unchanged. -/
theorem flexPositions_updateStandardUnlock (s : State) (id : Nat) (owner : Address)
    (addAmount : Nat) (a : Address)
    (hreq : ∃ oldOwner oldAmount oldEnd, s.unlockRequests id =
      some (oldOwner, oldAmount, oldEnd)) :
    flexPositions (updateStandardUnlock s id owner addAmount) a = flexPositions s a := by
  obtain ⟨oldOwner, oldAmount, oldEnd, hentry⟩ := hreq
  unfold flexPositions
  have hnext : (updateStandardUnlock s id owner addAmount).nextUnlockId = s.nextUnlockId := by
    simp [updateStandardUnlock, hentry]
  rw [hnext]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [flexAmt, updateStandardUnlock, hentry]

/-- A successful standard request is value-neutral for the caller on both
    model branches: opening a fresh position and topping up the existing one.
    `RegistryBounded` is required because the finite position ledger ranges
    only over ids below `nextUnlockId`; without it, a pointer could name an
    uncounted record and the top-up would not be represented in `stdPositions`.
    No pointer-ownership invariant is needed here: the request branch itself
    checks that the recorded owner equals the caller before it updates. -/
theorem requestUnlock_holderValueAt_neutral (s : State) (amount : Nat) (caller : Address)
    (s' : State)
    (h_step : step s (Op.requestUnlock amount) caller = some s')
    (h_registry : RegistryBounded s) :
    holderValue s' caller = holderValue s caller := by
  obtain ⟨_, h_bal, hs'⟩ := requestUnlockStep_effect s amount caller s' h_step
  subst hs'
  have h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none :=
    flex_unallocated_at_counter s h_registry
  have h_create :
      holderValue (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller =
        holderValue s caller := by
    unfold holderValue
    have hbal :
        (createStandardUnlock (burnApxUSD s caller amount) caller amount).apxUSDBal caller =
          s.apxUSDBal caller - amount := by
      simp [createStandardUnlock, burnApxUSD]
    have hstd :
        stdPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller =
          stdPositions s caller + amount := by
      rw [stdPositions_createStandardUnlock, if_pos rfl]
      congr 1
    have hflex :
        flexPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller =
          flexPositions s caller := by
      rw [flexPositions_createStandardUnlock (burnApxUSD s caller amount) caller amount caller
        h_unalloc_flex]
      rfl
    have hshares :
        (createStandardUnlock (burnApxUSD s caller amount) caller amount).apyUSDBal caller =
          s.apyUSDBal caller := by simp [createStandardUnlock, burnApxUSD]
    have husdc :
        (createStandardUnlock (burnApxUSD s caller amount) caller amount).usdcBal caller =
          s.usdcBal caller := by simp [createStandardUnlock, burnApxUSD]
    have hrate :
        computeExchangeRate (createStandardUnlock (burnApxUSD s caller amount) caller amount) =
          computeExchangeRate s := by
      simp [computeExchangeRate, totalAssets, vestedAmount, newlyVestedAmount,
        createStandardUnlock, burnApxUSD]
    rw [hbal, hstd, hflex, hshares, husdc, hrate]
    omega
  unfold requestUnlockStep
  split
  · rename_i id hptr
    split
    · rename_i recorded oldAmount oldEnd hentry
      by_cases ho : recorded = caller
      · subst recorded
        rw [if_pos rfl]
        have hptr' : s.unlockRequestId caller = some id := by
          simpa [burnApxUSD] using hptr
        have hentry' : s.unlockRequests id = some (caller, oldAmount, oldEnd) := by
          simpa [burnApxUSD] using hentry
        have hid : id < s.nextUnlockId := by
          by_cases hgood : id < s.nextUnlockId
          · exact hgood
          · have hge : s.nextUnlockId ≤ id := by omega
            have hnone := h_registry.1 id hge
            rw [hentry'] at hnone
            simp at hnone
        have hstd := stdPositions_updateStandardUnlock (burnApxUSD s caller amount) id caller
          oldAmount oldEnd amount hid hentry'
        have hbal' :
            (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).apxUSDBal caller =
              s.apxUSDBal caller - amount := by
          simp [updateStandardUnlock, burnApxUSD, hentry']
        have hflex' :
            flexPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) caller =
              flexPositions s caller := by
          calc
            flexPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) caller =
                flexPositions (burnApxUSD s caller amount) caller := by
                  have hnext :
                      (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).nextUnlockId =
                        (burnApxUSD s caller amount).nextUnlockId := by
                    simp [updateStandardUnlock, hentry]
                  have hflexmap :
                      (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).flexibleUnlockRequests =
                        (burnApxUSD s caller amount).flexibleUnlockRequests := by
                    simp [updateStandardUnlock, hentry]
                  unfold flexPositions
                  rw [hnext]
                  congr 1
                  apply List.map_congr_left
                  intro i hi
                  simp [flexAmt, hflexmap]
            _ = flexPositions s caller := by rfl
        have hstd' :
            stdPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) caller =
              stdPositions s caller + amount := by
          rw [hstd]
          rfl
        have hshares' :
            (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).apyUSDBal caller =
              s.apyUSDBal caller := by simp [updateStandardUnlock, burnApxUSD, hentry']
        have husdc' :
            (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).usdcBal caller =
              s.usdcBal caller := by simp [updateStandardUnlock, burnApxUSD, hentry']
        have hrate' :
            computeExchangeRate (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) =
              computeExchangeRate s := by
          simp [computeExchangeRate, totalAssets, vestedAmount, newlyVestedAmount,
            updateStandardUnlock, burnApxUSD, hentry']
        unfold holderValue
        rw [hbal', hstd', hflex', hshares', husdc', hrate']
        omega
      · rw [if_neg ho]
        exact h_create
    · exact h_create
  · exact h_create

/-! ## Fixed-rate holder value

`holderValueAt` is the rate-parameterized form used when a trace contains clock
steps. The live measure can change merely because vesting advances; that is a
pricing effect, not an unlock transfer. -/

/-- `holderValue` at an explicit rate `R` — the complete-measure counterpart of
`Safety.valueAt`. -/
def holderValueAt (R : Nat) (s : State) (a : Address) : Nat :=
  valueAt R s a + stdPositions s a + flexPositions s a

/-- At the state's own live rate, the parameterized form is `holderValue`. -/
theorem holderValueAt_live (s : State) (a : Address) :
    holderValueAt (computeExchangeRate s) s a = holderValue s a := rfl

/-- The fixed-rate ledger is monotone in its pricing parameter. This is the
bridge needed when a later state is priced at a lower rate than the rate used
by an earlier vault-exit step; it is not a conservation law for a rate rise. -/
theorem holderValueAt_mono_rate (s : State) (a : Address) (R₁ R₂ : Nat)
    (h_rate : R₁ ≤ R₂) :
    holderValueAt R₁ s a ≤ holderValueAt R₂ s a := by
  unfold holderValueAt valueAt
  have hshares : redeemAssets (s.apyUSDBal a) R₁ ≤
      redeemAssets (s.apyUSDBal a) R₂ := by
    unfold redeemAssets
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ h_rate)
  omega

/-- A standard request is neutral at any externally chosen pricing rate. This
is the fixed-rate form used by timed traces: advancing the clock may change
the live exchange rate through vesting, but the request itself only moves
apxUSD into the standard-position ledger. -/
theorem requestUnlock_holderValueAt_fixedRate (R : Nat) (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (h_step : step s (Op.requestUnlock amount) caller = some s')
    (h_registry : RegistryBounded s) :
    holderValueAt R s' caller = holderValueAt R s caller := by
  obtain ⟨-, h_bal, hs'⟩ := requestUnlockStep_effect s amount caller s' h_step
  subst hs'
  have h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none :=
    flex_unallocated_at_counter s h_registry
  have h_create :
      holderValueAt R (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller =
        holderValueAt R s caller := by
    unfold holderValueAt valueAt
    have hbal :
        (createStandardUnlock (burnApxUSD s caller amount) caller amount).apxUSDBal caller =
          s.apxUSDBal caller - amount := by
      simp [createStandardUnlock, burnApxUSD]
    have hstd :
        stdPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller =
          stdPositions s caller + amount := by
      rw [stdPositions_createStandardUnlock, if_pos rfl]
      congr 1
    have hflex :
        flexPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) caller =
          flexPositions s caller := by
      rw [flexPositions_createStandardUnlock (burnApxUSD s caller amount) caller amount caller
        h_unalloc_flex]
      rfl
    have hshares :
        (createStandardUnlock (burnApxUSD s caller amount) caller amount).apyUSDBal caller =
          s.apyUSDBal caller := by simp [createStandardUnlock, burnApxUSD]
    have husdc :
        (createStandardUnlock (burnApxUSD s caller amount) caller amount).usdcBal caller =
          s.usdcBal caller := by simp [createStandardUnlock, burnApxUSD]
    rw [hbal, hstd, hflex, hshares, husdc]
    omega
  unfold requestUnlockStep
  split
  · rename_i id hptr
    split
    · rename_i recorded oldAmount oldEnd hentry
      by_cases ho : recorded = caller
      · subst recorded
        rw [if_pos rfl]
        have hentry' : s.unlockRequests id = some (caller, oldAmount, oldEnd) := by
          simpa [burnApxUSD] using hentry
        have hid : id < s.nextUnlockId := by
          by_cases hgood : id < s.nextUnlockId
          · exact hgood
          · have hnone := h_registry.1 id (by omega)
            rw [hentry'] at hnone
            simp at hnone
        have hstd := stdPositions_updateStandardUnlock (burnApxUSD s caller amount) id caller
          oldAmount oldEnd amount hid hentry'
        have hbal' :
            (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).apxUSDBal caller =
              s.apxUSDBal caller - amount := by
          simp [updateStandardUnlock, burnApxUSD, hentry']
        have hflex' :
            flexPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) caller =
              flexPositions s caller := by
          calc
            flexPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) caller =
                flexPositions (burnApxUSD s caller amount) caller := by
                  have hnext :
                      (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).nextUnlockId =
                        (burnApxUSD s caller amount).nextUnlockId := by
                    simp [updateStandardUnlock, hentry]
                  have hflexmap :
                      (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).flexibleUnlockRequests =
                        (burnApxUSD s caller amount).flexibleUnlockRequests := by
                    simp [updateStandardUnlock, hentry]
                  unfold flexPositions
                  rw [hnext]
                  congr 1
                  apply List.map_congr_left
                  intro i hi
                  simp [flexAmt, hflexmap]
            _ = flexPositions s caller := by rfl
        have hstd' :
            stdPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) caller =
              stdPositions s caller + amount := by
          rw [hstd]
          rfl
        have hshares' :
            (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).apyUSDBal caller =
              s.apyUSDBal caller := by simp [updateStandardUnlock, burnApxUSD, hentry']
        have husdc' :
            (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).usdcBal caller =
              s.usdcBal caller := by simp [updateStandardUnlock, burnApxUSD, hentry']
        unfold holderValueAt valueAt
        rw [hbal', hstd', hflex', hshares', husdc']
        omega
      · rw [if_neg ho]
        exact h_create
    · exact h_create
  · exact h_create

/-- A request by another holder is a frame for `a`'s fixed-rate value. This
is the per-holder fact that removes the need to restrict a trace to one
caller; the new standard position belongs to `caller`, not to `a`. -/
theorem requestUnlock_holderValueAt_fixedRate_frame (R : Nat) (s : State) (amount : Nat)
    (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.requestUnlock amount) caller = some s')
    (h_registry : RegistryBounded s) :
    holderValueAt R s' a = holderValueAt R s a := by
  by_cases hsame : caller = a
  · subst caller
    exact requestUnlock_holderValueAt_fixedRate R s amount a s' h_step h_registry
  · obtain ⟨-, -, hpost⟩ := requestUnlockStep_effect s amount caller s' h_step
    subst s'
    have hsymm : a ≠ caller := Ne.symm hsame
    have h_unalloc_flex : s.flexibleUnlockRequests s.nextUnlockId = none :=
      flex_unallocated_at_counter s h_registry
    have h_create :
        holderValueAt R (createStandardUnlock (burnApxUSD s caller amount) caller amount) a =
          holderValueAt R s a := by
      unfold holderValueAt valueAt
      have hbal :
          (createStandardUnlock (burnApxUSD s caller amount) caller amount).apxUSDBal a =
            s.apxUSDBal a := by simp [createStandardUnlock, burnApxUSD, hsymm]
      have hstd :
          stdPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) a =
            stdPositions s a := by
        rw [stdPositions_createStandardUnlock]
        have hburn : stdPositions (burnApxUSD s caller amount) a = stdPositions s a := by rfl
        rw [hburn, if_neg hsame]
        simp
      have hflex :
          flexPositions (createStandardUnlock (burnApxUSD s caller amount) caller amount) a =
            flexPositions s a := by
        rw [flexPositions_createStandardUnlock (burnApxUSD s caller amount) caller amount a
          h_unalloc_flex]
        rfl
      have hshares :
          (createStandardUnlock (burnApxUSD s caller amount) caller amount).apyUSDBal a =
            s.apyUSDBal a := by simp [createStandardUnlock, burnApxUSD]
      have husdc :
          (createStandardUnlock (burnApxUSD s caller amount) caller amount).usdcBal a =
            s.usdcBal a := by simp [createStandardUnlock, burnApxUSD]
      rw [hbal, hstd, hflex, hshares, husdc]
    unfold requestUnlockStep
    split
    · rename_i id hptr
      split
      · rename_i recorded oldAmount oldEnd hentry
        by_cases ho : recorded = caller
        · subst recorded
          rw [if_pos rfl]
          have hentry' : s.unlockRequests id = some (caller, oldAmount, oldEnd) := by
            simpa [burnApxUSD] using hentry
          have hstd :
              stdPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) a =
                stdPositions s a := by
            rw [stdPositions_updateStandardUnlock_of_ne (burnApxUSD s caller amount) id caller
              amount a hsame ⟨oldAmount, oldEnd, hentry'⟩]
            rfl
          have hflex :
              flexPositions (updateStandardUnlock (burnApxUSD s caller amount) id caller amount) a =
                flexPositions s a := by
            rw [flexPositions_updateStandardUnlock (burnApxUSD s caller amount) id caller amount a
              ⟨caller, oldAmount, oldEnd, hentry'⟩]
            rfl
          have hbal :
              (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).apxUSDBal a =
                s.apxUSDBal a := by simp [updateStandardUnlock, burnApxUSD, hentry', hsymm]
          have hshares :
              (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).apyUSDBal a =
                s.apyUSDBal a := by simp [updateStandardUnlock, burnApxUSD, hentry']
          have husdc :
              (updateStandardUnlock (burnApxUSD s caller amount) id caller amount).usdcBal a =
                s.usdcBal a := by simp [updateStandardUnlock, burnApxUSD, hentry']
          unfold holderValueAt valueAt
          rw [hbal, hstd, hflex, hshares, husdc]
        · rw [if_neg ho]
          exact h_create
      · exact h_create
    · exact h_create

/-- A flexible request is neutral at a fixed rate: the burned apxUSD is added
to the caller's flexible position total. Unlike a standard request there is no
top-up branch, so only the shared fresh-id registry frame is needed. -/
theorem flexibleRequestUnlock_holderValueAt_fixedRate (R : Nat) (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (h_step : step s (Op.flexibleRequestUnlock amount) caller = some s')
    (h_registry : RegistryWellIndexed s) :
    holderValueAt R s' caller = holderValueAt R s caller := by
  obtain ⟨-, h_bal, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
  subst s'
  have hstd_unalloc :
      (burnApxUSD s caller amount).unlockRequests (burnApxUSD s caller amount).nextUnlockId = none := by
    simpa [burnApxUSD] using std_unallocated_at_counter s h_registry.1
  have hbal :
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount).apxUSDBal caller =
        s.apxUSDBal caller - amount := by
    simp [createFlexibleUnlock, burnApxUSD]
  have hstd :
      stdPositions (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) caller =
        stdPositions s caller := by
    rw [stdPositions_createFlexibleUnlock (burnApxUSD s caller amount) caller amount caller
      hstd_unalloc]
    rfl
  have hflex :
      flexPositions (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) caller =
        flexPositions s caller + amount := by
    rw [flexPositions_createFlexibleUnlock (burnApxUSD s caller amount) caller amount caller]
    have hflexburn : flexPositions (burnApxUSD s caller amount) caller = flexPositions s caller := by
      unfold flexPositions
      congr 1
    rw [hflexburn]
    simp
  have hshares :
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount).apyUSDBal caller =
        s.apyUSDBal caller := by simp [createFlexibleUnlock, burnApxUSD]
  have husdc :
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount).usdcBal caller =
        s.usdcBal caller := by simp [createFlexibleUnlock, burnApxUSD]
  unfold holderValueAt valueAt
  rw [hbal, hstd, hflex, hshares, husdc]
  omega

/-- A flexible request by another holder is a frame for `a`'s fixed-rate
value. The fresh flexible position belongs only to `caller`. -/
theorem flexibleRequestUnlock_holderValueAt_fixedRate_frame (R : Nat) (s : State)
    (amount : Nat) (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.flexibleRequestUnlock amount) caller = some s')
    (h_registry : RegistryWellIndexed s) (hsame : caller ≠ a) :
    holderValueAt R s' a = holderValueAt R s a := by
  obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
  subst s'
  have hsymm : a ≠ caller := Ne.symm hsame
  have hstd_unalloc :
      (burnApxUSD s caller amount).unlockRequests
          (burnApxUSD s caller amount).nextUnlockId = none := by
    simpa [burnApxUSD] using std_unallocated_at_counter s h_registry.1
  have hbal :
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount).apxUSDBal a =
        s.apxUSDBal a := by
    simp [createFlexibleUnlock, burnApxUSD, hsymm]
  have hstd : stdPositions
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) a =
        stdPositions s a := by
    rw [stdPositions_createFlexibleUnlock (burnApxUSD s caller amount) caller amount a
      hstd_unalloc]
    rfl
  have hflex : flexPositions
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) a =
        flexPositions s a := by
    rw [flexPositions_createFlexibleUnlock]
    have hburn : flexPositions (burnApxUSD s caller amount) a = flexPositions s a := by rfl
    rw [hburn, if_neg hsame]
    simp
  have hshares :
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount).apyUSDBal a =
        s.apyUSDBal a := by simp [createFlexibleUnlock, burnApxUSD]
  have husdc :
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount).usdcBal a =
        s.usdcBal a := by simp [createFlexibleUnlock, burnApxUSD]
  unfold holderValueAt valueAt
  rw [hbal, hstd, hflex, hshares, husdc]

/-- Retiring an in-range standard position removes exactly its recorded amount
from the owner's finite standard-position sum. Other positions, including any
additional positions for the same owner, remain accounted for. -/
theorem stdPositions_retireStandardUnlock (s : State) (id : Nat) (owner : Address)
    (amount cooldownEnd : Nat) (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd)) :
    stdPositions (retireStandardUnlock s id owner) owner + amount =
      stdPositions s owner := by
  let r := retireStandardUnlock s id owner
  have hat : stdAmt s owner id = stdAmt r owner id + amount := by
    simp [r, stdAmt, retireStandardUnlock, burnUnlockNFT, hreq]
  have hother : ∀ j, j < s.nextUnlockId → j ≠ id →
      stdAmt s owner j = stdAmt r owner j := by
    intro j hj hji
    simp [r, stdAmt, retireStandardUnlock, burnUnlockNFT, hji]
  have hsum := sum_range_replace s.nextUnlockId id amount
    (stdAmt s owner) (stdAmt r owner) hid hat hother
  exact hsum.symm

theorem stdPositions_retireStandardUnlock_of_ne (s : State) (id : Nat) (owner : Address)
    (amount cooldownEnd : Nat) (a : Address) (howner : owner ≠ a)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd)) :
    stdPositions (retireStandardUnlock s id owner) a = stdPositions s a := by
  unfold stdPositions
  have hnext : (retireStandardUnlock s id owner).nextUnlockId = s.nextUnlockId := by
    simp [retireStandardUnlock, burnUnlockNFT]
  rw [hnext]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hne : i = id
  · subst i
    simp [stdAmt, retireStandardUnlock, burnUnlockNFT, hreq, howner]
  · simp [stdAmt, retireStandardUnlock, burnUnlockNFT, hne]

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

/-- A successful standard claim is neutral for the recorded owner's complete
position value at every fixed pricing rate. The claim mints the recorded amount
back while retiring that amount from the finite standard-position ledger. The
`id < nextUnlockId` premise is the explicit finite-support boundary; no global
registry invariant is smuggled into this local settlement theorem. -/
theorem claimUnlock_holderValueAt_neutral (s : State) (id : Nat)
    (owner : Address) (amount cooldownEnd : Nat) (caller : Address) (s' : State)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_step : step s (Op.claimUnlock id) caller = some s') :
    ∀ R, holderValueAt R s' owner = holderValueAt R s owner := by
  intro R
  obtain ⟨recordedOwner, recordedAmount, recordedCooldown, hentry, _, _, _, hpost⟩ :=
    claimUnlockStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl⟩ := hentry
  subst s'
  have hstd := stdPositions_retireStandardUnlock s id owner amount cooldownEnd hid hreq
  have hstd' : stdPositions (mintApxUSD (retireStandardUnlock s id owner) owner amount) owner
      + amount = stdPositions s owner := by
    change stdPositions (retireStandardUnlock s id owner) owner + amount = stdPositions s owner
    exact hstd
  have hbalance : (mintApxUSD (retireStandardUnlock s id owner) owner amount).apxUSDBal owner
      = s.apxUSDBal owner + amount := by
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT]
  have hshares : (mintApxUSD (retireStandardUnlock s id owner) owner amount).apyUSDBal owner
      = s.apyUSDBal owner := by
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT]
  have husdc : (mintApxUSD (retireStandardUnlock s id owner) owner amount).usdcBal owner
      = s.usdcBal owner := by
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT]
  have hflex : flexPositions (mintApxUSD (retireStandardUnlock s id owner) owner amount) owner
      = flexPositions s owner := by
    change flexPositions (retireStandardUnlock s id owner) owner = flexPositions s owner
    rfl
  unfold holderValueAt valueAt
  rw [hbalance, hshares, husdc, hflex]
  omega

/-- A standard claim by a different owner is a frame for `a`'s fixed-rate value.
The claim retires and mints only the recorded owner's position; the operator is
irrelevant to the holder ledger. -/
theorem claimUnlock_holderValueAt_fixedRate_frame (R : Nat) (s : State) (id : Nat)
    (owner : Address) (amount cooldownEnd : Nat) (caller : Address) (s' : State)
    (a : Address)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_step : step s (Op.claimUnlock id) caller = some s')
    (howner : owner ≠ a) :
    holderValueAt R s' a = holderValueAt R s a := by
  obtain ⟨recordedOwner, recordedAmount, recordedCooldown, hentry, _, _, _, hpost⟩ :=
    claimUnlockStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl⟩ := hentry
  subst s'
  have hsymm : a ≠ owner := Ne.symm howner
  have hstd : stdPositions (mintApxUSD (retireStandardUnlock s id owner) owner amount) a =
      stdPositions s a := by
    change stdPositions (retireStandardUnlock s id owner) a = stdPositions s a
    exact stdPositions_retireStandardUnlock_of_ne s id owner amount cooldownEnd a howner hreq
  have hbalance : (mintApxUSD (retireStandardUnlock s id owner) owner amount).apxUSDBal a =
      s.apxUSDBal a := by
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT, hsymm]
  have hshares : (mintApxUSD (retireStandardUnlock s id owner) owner amount).apyUSDBal a =
      s.apyUSDBal a := by
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT]
  have husdc : (mintApxUSD (retireStandardUnlock s id owner) owner amount).usdcBal a =
      s.usdcBal a := by
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT]
  have hflex : flexPositions (mintApxUSD (retireStandardUnlock s id owner) owner amount) a =
      flexPositions s a := by
    change flexPositions (retireStandardUnlock s id owner) a = flexPositions s a
    rfl
  unfold holderValueAt valueAt
  rw [hbalance, hstd, hshares, husdc, hflex]

theorem flexPositions_retireFlexibleUnlock_of_ne (s : State) (id : Nat) (owner : Address)
    (amount requestTime cooldownEnd : Nat) (a : Address) (howner : owner ≠ a)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd)) :
    flexPositions (retireFlexibleUnlock s id) a = flexPositions s a := by
  unfold flexPositions
  have hnext : (retireFlexibleUnlock s id).nextUnlockId = s.nextUnlockId := by
    simp [retireFlexibleUnlock, burnUnlockNFT]
  rw [hnext]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases hne : i = id
  · subst i
    simp [flexAmt, retireFlexibleUnlock, burnUnlockNFT, hreq, howner]
  · simp [flexAmt, retireFlexibleUnlock, burnUnlockNFT, hne]

/-- A flexible claim by a different owner is a frame for `a`'s fixed-rate
value. The early-exit fee is charged to the recorded owner, so it does not
alter another holder's ledger. -/
theorem flexibleClaim_holderValueAt_fixedRate_frame (R : Nat) (s : State) (id : Nat)
    (owner : Address) (amount requestTime cooldownEnd : Nat) (caller : Address) (s' : State)
    (a : Address)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd))
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s')
    (howner : owner ≠ a) :
    holderValueAt R s' a = holderValueAt R s a := by
  obtain ⟨recordedOwner, recordedAmount, recordedRequestTime, recordedCooldownEnd,
    hentry, _, _, _, hpost⟩ := flexibleClaimStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hentry
  subst s'
  let fee := amount * flexibleUnlockFee requestTime s.now / 10000
  have hsymm : a ≠ owner := Ne.symm howner
  have hflex : flexPositions
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)) a =
      flexPositions s a := by
    change flexPositions (retireFlexibleUnlock s id) a = flexPositions s a
    exact flexPositions_retireFlexibleUnlock_of_ne s id owner amount requestTime cooldownEnd a
      howner hreq
  have hbalance :
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).apxUSDBal a =
        s.apxUSDBal a := by
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT, fee, hsymm]
  have hshares :
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).apyUSDBal a =
        s.apyUSDBal a := by
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT]
  have husdc :
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).usdcBal a =
        s.usdcBal a := by
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT]
  have hstd : stdPositions
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)) a =
      stdPositions s a := by
    change stdPositions (retireFlexibleUnlock s id) a = stdPositions s a
    rfl
  unfold holderValueAt valueAt
  rw [hbalance, hshares, husdc, hstd, hflex]

/-- Retiring an in-range flexible position removes exactly its recorded amount
from the owner's finite flexible-position sum. -/
theorem flexPositions_retireFlexibleUnlock (s : State) (id : Nat) (owner : Address)
    (amount requestTime cooldownEnd : Nat) (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd)) :
    flexPositions (retireFlexibleUnlock s id) owner + amount =
      flexPositions s owner := by
  let r := retireFlexibleUnlock s id
  have hat : flexAmt s owner id = flexAmt r owner id + amount := by
    simp [r, flexAmt, retireFlexibleUnlock, burnUnlockNFT, hreq]
  have hother : ∀ j, j < s.nextUnlockId → j ≠ id →
      flexAmt s owner j = flexAmt r owner j := by
    intro j hj hji
    simp [r, flexAmt, retireFlexibleUnlock, burnUnlockNFT, hji]
  have hsum := sum_range_replace s.nextUnlockId id amount
    (flexAmt s owner) (flexAmt r owner) hid hat hother
  exact hsum.symm

/-- A successful flexible claim preserves the owner's complete position value
up to the explicit early-exit fee. At any fixed rate, the fee is the only value
that leaves the holder: the net apxUSD mint plus the retired flexible position
equals the pre-claim position value. This is deliberately a fee-accounting law,
not a neutrality theorem. -/
theorem flexibleClaim_holderValueAt_fee (s : State) (id : Nat)
    (owner : Address) (amount requestTime cooldownEnd : Nat) (caller : Address) (s' : State)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd))
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∀ R, holderValueAt R s' owner +
      amount * flexibleUnlockFee requestTime s.now / 10000 =
        holderValueAt R s owner := by
  intro R
  obtain ⟨recordedOwner, recordedAmount, recordedRequestTime, recordedCooldownEnd,
    hentry, _, _, _, hpost⟩ := flexibleClaimStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hentry
  subst s'
  let fee := amount * flexibleUnlockFee requestTime s.now / 10000
  have hfee : fee ≤ amount := by
    exact flexibleClaimFee_le_amount amount requestTime s.now
  have hflex := flexPositions_retireFlexibleUnlock s id owner amount requestTime cooldownEnd hid hreq
  have hflex' : flexPositions
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)) owner + amount =
      flexPositions s owner := by
    change flexPositions (retireFlexibleUnlock s id) owner + amount = flexPositions s owner
    exact hflex
  have hbalance : (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).apxUSDBal owner
      = s.apxUSDBal owner + (amount - fee) := by
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT, fee]
  have hshares : (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).apyUSDBal owner
      = s.apyUSDBal owner := by
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT]
  have husdc : (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).usdcBal owner
      = s.usdcBal owner := by
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT]
  have hstd : stdPositions (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)) owner
      = stdPositions s owner := by
    change stdPositions (retireFlexibleUnlock s id) owner = stdPositions s owner
    rfl
  unfold holderValueAt valueAt
  rw [hbalance, hshares, husdc, hstd]
  dsimp [fee] at hfee hflex' ⊢
  omega

/-! ### Flexible unlock laws at the live rate

The fixed-rate flexible lemmas above can be lifted to `holderValue` because a
flexible request and claim do not change the exchange-rate inputs in this
model. Keeping that lift explicit prevents a later trace proof from silently
mixing a pre-state rate with a post-state live rate. -/

theorem flexibleRequestUnlock_holderValue_live (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (h_step : step s (Op.flexibleRequestUnlock amount) caller = some s')
    (h_registry : RegistryWellIndexed s) :
    holderValue s' caller = holderValue s caller := by
  obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
  subst s'
  have hfixed := flexibleRequestUnlock_holderValueAt_fixedRate
    (computeExchangeRate s) s amount caller
    (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) h_step h_registry
  have hrate : computeExchangeRate
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) =
      computeExchangeRate s := by
    simp [computeExchangeRate, totalAssets, vestedAmount, newlyVestedAmount,
      createFlexibleUnlock, burnApxUSD]
  calc
    holderValue (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) caller =
        holderValueAt (computeExchangeRate
          (createFlexibleUnlock (burnApxUSD s caller amount) caller amount))
          (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) caller :=
      (holderValueAt_live _ _).symm
    _ = holderValueAt (computeExchangeRate s)
        (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) caller := by
      rw [hrate]
    _ = holderValueAt (computeExchangeRate s) s caller := hfixed
    _ = holderValue s caller := holderValueAt_live s caller

theorem flexibleClaim_holderValue_live_nonincreasing (s : State) (id : Nat)
    (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s')
    (h_registry : RegistryWellIndexed s)
    (h_not_operator : a ≠ s.unlockTokenOperator)
    (h_caller : caller = a) :
    holderValue s' a ≤ holderValue s a := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, _, hcaller, _, hpost⟩ :=
    flexibleClaimStep_effect s id caller s' h_step
  have howner_eq : owner = a := by
    rcases hcaller with h | h
    · exact h_caller ▸ h.symm
    · exact False.elim (h_not_operator (h_caller ▸ h))
  subst owner
  have hid : id < s.nextUnlockId := by
    by_cases hlt : id < s.nextUnlockId
    · exact hlt
    · have hnone := h_registry.1.2 id (by omega)
      rw [hreq] at hnone
      simp at hnone
  have hfixed := flexibleClaim_holderValueAt_fee s id a amount requestTime cooldownEnd caller s'
    hid hreq h_step (computeExchangeRate s)
  have hrate : computeExchangeRate s' = computeExchangeRate s := by
    rw [hpost]
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT, computeExchangeRate,
      totalAssets, vestedAmount, newlyVestedAmount]
  let fee := amount * flexibleUnlockFee requestTime s.now / 10000
  have h_eq : holderValue s' a + fee = holderValue s a := by
    calc
      holderValue s' a + fee = holderValueAt (computeExchangeRate s) s' a + fee := by
        rw [← holderValueAt_live s' a, hrate]
      _ = holderValueAt (computeExchangeRate s) s a := hfixed
      _ = holderValue s a := holderValueAt_live s a
  omega

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

theorem div_add_div_le (x y d : Nat) : x / d + y / d ≤ (x + y) / d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · rw [Nat.le_div_iff_mul_le h, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x d) (Nat.div_mul_le_self y d)

/-- Splitting a share balance across a burn loses at most dust, never gains:
the two pieces, each floor-priced, never exceed the whole floor-priced. -/
theorem redeemAssets_superadd (b c R : Nat) (h : c ≤ b) :
    redeemAssets (b - c) R + redeemAssets c R ≤ redeemAssets b R := by
  unfold redeemAssets
  have hsplit := div_add_div_le ((b - c) * R) (c * R) ray
  rwa [← Nat.add_mul, Nat.sub_add_cancel h] at hsplit

/-- The ceil-rounded share cost of a withdrawal, floor-priced back at the same rate,
covers the withdrawn assets. Needs the cost to be nonzero — at `R = 0` the cost is 0
and covers nothing, which is exactly the state the step's zero-share guard refuses. -/
theorem withdrawShares_covers (assets R : Nat)
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
theorem redeemAssets_sub_withdraw_le (b assets R : Nat)
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

Stated for any `receiver`, though only one value is now reachable: `step`'s `receiver != caller`
guard pins the receipt to the caller (`DeploymentFees.withdraw_receiver_is_caller`), so the
"someone else" branch of the proof is dead weight kept for robustness against that guard changing.
On the live branch the ceil-rounded share cost covers the position credit
(`withdrawShares_covers`), with the zero-share guard (`Regression.lean` §R4b) supplying the
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
 these bounds do **not** chain along an arbitrary mixed trace. A stable live-rate sublanguage is
 handled below: it combines deposit/redeemApxUSD with both unlock channels, while vault exits and
 clock steps remain outside because they change the pricing context.
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

/-! ## A trace-level law, on the subfamily where the rate holds still

Every result above is single-step, and the umbrella says why they do not chain: the vault
operations are priced at `computeExchangeRate (pullVestedYield s)` while the others use
`computeExchangeRate s`, so a trace mixing them compares values at shifting rates.

There is a subfamily where that obstruction disappears. `depositUSDC` and `redeemApxUSD` move
neither `totalAssets` nor `totalSupply_apyUSD`, so the live rate is *invariant* across them — the
`_live` theorems above are exactly that observation — and their bounds telescope. The result is a
genuine no-free-money law on the **complete** measure over arbitrary-length traces, which is what
`caller_net_nonpositive_trace` provides for the incomplete one.

Scope: the trace is restricted to steps the tracked holder signs. Steps signed by *others* also
leave this holder's value alone (they touch neither the holder's columns nor the rate), but that
needs a frame result per operation that this module does not carry, so it is not claimed here.
-/

/-- The two operations whose live rate is fixed, as a predicate on a trace entry. -/
def RateFixedOp (op : Op) : Prop :=
  (∃ amt, op = Op.depositUSDC amt) ∨ (∃ amt, op = Op.redeemApxUSD amt)

/-- Neither writes the published price, so `PriceUnderPar` survives them. -/
private theorem priceUnderPar_rateFixed (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (h : s.redemptionValue ≤ ray)
    (h_op : RateFixedOp op) : s'.redemptionValue ≤ ray := by
  have hframe : s'.redemptionValue = s.redemptionValue := by
    refine redemptionValue_frame s op caller s' h_step ?_ ?_
    · rcases h_op with ⟨amt, rfl⟩ | ⟨amt, rfl⟩ <;> intro v <;> simp
    · rcases h_op with ⟨amt, rfl⟩ | ⟨amt, rfl⟩ <;> simp
  omega

/-- **No free money for a holder over a whole trace, on the complete measure.**

Along any trace of the holder's own `depositUSDC` and `redeemApxUSD` steps — any length, any
amounts, revert-skip included — the holder's complete holdings, priced at the live rate, never
rise. The single standing side condition is the no-premium-redemption invariant
`redemptionValue ≤ ray`, required only at the initial state: neither operation writes the price,
so it propagates (`priceUnderPar_rateFixed`).

This is the trace-level statement the module lacked. It is available for exactly these two
operations because they are the ones that hold the live rate still; the vault legs move it, which
is what stops the umbrella `caller_net_nonpositive_complete` from chaining. -/
theorem holderValue_trace_nonincreasing (s : State) (σ : List (Op × Address)) (a : Address)
    (h_price : s.redemptionValue ≤ ray)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, RateFixedOp p.1) :
    holderValue (execTrace s σ) a ≤ holderValue s a := by
  induction σ generalizing s with
  | nil => exact Nat.le_refl _
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have hhead_own : c = a := h_own (op, c) List.mem_cons_self
    have hhead_op : RateFixedOp op := h_ops (op, c) List.mem_cons_self
    have htail_own : ∀ q ∈ σ, q.2 = a := fun q hq => h_own q (List.mem_cons_of_mem _ hq)
    have htail_op : ∀ q ∈ σ, RateFixedOp q.1 := fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_price htail_own htail_op
    | some s1 =>
      have hstep1 : holderValue s1 a ≤ holderValue s a := by
        rw [← hhead_own]
        rcases hhead_op with ⟨amt, rfl⟩ | ⟨amt, rfl⟩
        · exact Nat.le_of_eq (holder_value_depositUSDC_live s amt c s1 hstep)
        · exact holder_value_redeemApxUSD_live s amt c s1 hstep h_price
      have hprice1 : s1.redemptionValue ≤ ray :=
        priceUnderPar_rateFixed s op c s1 hstep h_price hhead_op
      exact Nat.le_trans (ih s1 hprice1 htail_own htail_op) hstep1

/-- **And it is not vacuous.** A whitelisted holder with USDC deposits twice; both steps are
`RateFixedOp`s signed by that holder, the price starts at par, and the theorem applies. The value
is exactly preserved here — deposit swaps USDC for apxUSD at 1:1 — which is the equality case the
`≤` allows. -/
theorem holderValue_trace_witness :
    ∃ (s : State) (σ : List (Op × Address)) (a : Address),
      s.redemptionValue ≤ ray ∧
      (∀ p ∈ σ, p.2 = a) ∧ (∀ p ∈ σ, RateFixedOp p.1) ∧
      0 < σ.length ∧
      holderValue (execTrace s σ) a = holderValue s a := by
  refine ⟨{ (default : State) with
              globalPause := false
              whitelist := fun _ => true
              usdcBal := fun x => if x = 1 then 100 else 0
              redemptionValue := ray },
          [(Op.depositUSDC 40, 1), (Op.depositUSDC 60, 1)], 1, Nat.le_refl _, ?_, ?_, by decide,
          by decide⟩
  · intro p hp
    have : p = (Op.depositUSDC 40, 1) ∨ p = (Op.depositUSDC 60, 1) := by simpa using hp
    rcases this with rfl | rfl <;> rfl
  · intro p hp
    have : p = (Op.depositUSDC 40, 1) ∨ p = (Op.depositUSDC 60, 1) := by simpa using hp
    rcases this with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩

/-! ## Standard unlock request-to-claim traces

The previous local laws now compose on a deliberately narrow language. The trace
contains only requests and standard claims, is signed by the tracked holder, and
uses `RegistryWellIndexed` as the inductive finite-ledger invariant. The timed
fixed-rate variant below adds `tick`, so a claim can actually pass its cooldown.
The fixed-rate arbitrary-caller theorem covers operator-mediated claims; this
live-rate theorem remains restricted to the tracked holder's own calls. -/

/-- The standard unlock sublanguage used by the request-to-claim trace theorem. -/
def StandardUnlockOp (op : Op) : Prop :=
  (∃ amount, op = Op.requestUnlock amount) ∨
  (∃ requestId, op = Op.claimUnlock requestId)

/-- The timed standard-unlock sublanguage also permits waiting. Its holder
value theorem is stated at a fixed rate so vesting caused by `tick` is not
mistaken for value created or destroyed by the unlock mechanism. -/
def StandardUnlockTimedOp (op : Op) : Prop :=
  StandardUnlockOp op ∨ (∃ dt, op = Op.tick dt)

/-! ## A live-rate mixed ledger without vault exits

`withdraw` and `redeem` change the share supply and therefore require an
execution-rate relation rather than the live-rate telescope below. The
following sublanguage combines the operations whose live rate is stable with
both unlock channels. -/

def StableHolderValueOp (op : Op) : Prop :=
  RateFixedOp op ∨
  StandardUnlockOp op ∨
  (∃ amount, op = Op.flexibleRequestUnlock amount) ∨
  (∃ requestId, op = Op.flexibleClaimUnlock requestId)

private theorem tick_holderValueAt_frame (R : Nat) (s : State) (dt : Nat)
    (caller : Address) (s' : State)
    (h_step : step s (Op.tick dt) caller = some s') :
    holderValueAt R s' caller = holderValueAt R s caller := by
  simp only [step] at h_step
  cases Option.some.inj h_step
  rfl

private theorem tick_holderValueAt_frame_any (R : Nat) (s : State) (dt : Nat)
    (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.tick dt) caller = some s') :
    holderValueAt R s' a = holderValueAt R s a := by
  simp only [step] at h_step
  cases Option.some.inj h_step
  rfl

private theorem standardUnlock_operator_frame (s : State) (op : Op) (caller : Address)
    (s' : State) (h_op : StandardUnlockOp op)
    (h_step : step s op caller = some s') :
    s'.unlockTokenOperator = s.unlockTokenOperator := by
  rcases h_op with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
  · obtain ⟨-, -, hpost⟩ := requestUnlockStep_effect s amount caller s' h_step
    rw [hpost]
    simp [requestUnlockStep_unlockTokenOperator]
  · obtain ⟨owner, amount, cooldownEnd, hreq, howner, hcaller, htime, hpost⟩ :=
      claimUnlockStep_effect s requestId caller s' h_step
    rw [hpost]
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT]

private theorem standardUnlock_claim_neutral_live
    (s : State) (requestId : Nat) (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.claimUnlock requestId) caller = some s')
    (h_registry : RegistryWellIndexed s)
    (h_not_operator : a ≠ s.unlockTokenOperator)
    (h_caller : caller = a) :
    holderValue s' a = holderValue s a := by
  obtain ⟨owner, amount, cooldownEnd, hreq, howner, hcaller, htime, hpost⟩ :=
    claimUnlockStep_effect s requestId caller s' h_step
  have howner_eq : owner = a := by
    have hchoice : caller = owner ∨ caller = s.unlockTokenOperator := hcaller
    rcases hchoice with h | h
    · exact h_caller ▸ h.symm
    · exact False.elim (h_not_operator (h_caller ▸ h))
  subst owner
  have hid : requestId < s.nextUnlockId := by
    by_cases hlt : requestId < s.nextUnlockId
    · exact hlt
    · have hnone := h_registry.1.1 requestId (by omega)
      rw [hreq] at hnone
      simp at hnone
  have hneutral := claimUnlock_holderValueAt_neutral s requestId a amount cooldownEnd caller s'
    hid hreq h_step (computeExchangeRate s)
  have hrate : computeExchangeRate s' = computeExchangeRate s := by
    rw [hpost]
    simp [mintApxUSD, retireStandardUnlock, burnUnlockNFT, computeExchangeRate,
      totalAssets, vestedAmount, newlyVestedAmount]
  calc
    holderValue s' a = holderValueAt (computeExchangeRate s') s' a :=
      (holderValueAt_live s' a).symm
    _ = holderValueAt (computeExchangeRate s) s' a := by rw [hrate]
    _ = holderValueAt (computeExchangeRate s) s a := hneutral
    _ = holderValue s a := holderValueAt_live s a

private theorem stableHolderValue_operator_frame (s : State) (op : Op) (caller : Address)
    (s' : State) (h_op : StableHolderValueOp op)
    (h_step : step s op caller = some s') :
    s'.unlockTokenOperator = s.unlockTokenOperator := by
  rcases h_op with h_rate | h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
  · rcases h_rate with ⟨amount, rfl⟩ | ⟨amount, rfl⟩
    · have hpost := post_depositUSDC s amount caller s' h_step
      rw [hpost]
      simp [emitEvent, mintApxUSD]
    · have hpost := post_redeemApxUSD s amount caller s' h_step
      rw [hpost]
      simp [emitEvent, burnApxUSD]
  · exact standardUnlock_operator_frame s op caller s' h_standard h_step
  · obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
    rw [hpost]
    simp [createFlexibleUnlock, burnApxUSD]
  · obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, howner, hcaller, htime, hpost⟩ :=
      flexibleClaimStep_effect s requestId caller s' h_step
    rw [hpost]
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT]

private theorem stableHolderValue_price_frame (s : State) (op : Op) (caller : Address)
    (s' : State) (h_op : StableHolderValueOp op)
    (h_step : step s op caller = some s') (h_price : s.redemptionValue ≤ ray) :
    s'.redemptionValue ≤ ray := by
  have hframe : s'.redemptionValue = s.redemptionValue := by
    refine redemptionValue_frame s op caller s' h_step ?_ ?_
    · intro v hv
      rcases h_op with h_rate | h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
      · rcases h_rate with ⟨amount, rfl⟩ | ⟨amount, rfl⟩ <;> simp at hv
      · rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩ <;> simp at hv
      · simp at hv
      · simp at hv
    · intro hv
      rcases h_op with h_rate | h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
      · rcases h_rate with ⟨amount, rfl⟩ | ⟨amount, rfl⟩ <;> simp at hv
      · rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩ <;> simp at hv
      · simp at hv
      · simp at hv
  omega

/-! The operations below are closed under the live rate: deposit/redeemApxUSD
have their existing live theorems, standard unlock has its live request/claim
theorems, and the two flexible lifts were proved above. -/

theorem holderValue_stable_trace_nonincreasing (s : State) (σ : List (Op × Address))
    (a : Address) (h_registry : RegistryWellIndexed s)
    (h_price : s.redemptionValue ≤ ray)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, StableHolderValueOp p.1)
    (h_not_operator : a ≠ s.unlockTokenOperator) :
    holderValue (execTrace s σ) a ≤ holderValue s a := by
  induction σ generalizing s with
  | nil => exact Nat.le_refl _
  | cons p σ ih =>
    obtain ⟨op, caller⟩ := p
    have hcaller : caller = a := h_own (op, caller) List.mem_cons_self
    have hop : StableHolderValueOp op := h_ops (op, caller) List.mem_cons_self
    have htail_own : ∀ q ∈ σ, q.2 = a :=
      fun q hq => h_own q (List.mem_cons_of_mem _ hq)
    have htail_ops : ∀ q ∈ σ, StableHolderValueOp q.1 :=
      fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op caller with
    | none =>
        exact ih s h_registry h_price htail_own htail_ops h_not_operator
    | some s1 =>
        have h_step_bound : holderValue s1 a ≤ holderValue s a := by
          rcases hop with h_rate | h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
          · subst caller
            rcases h_rate with ⟨amount, rfl⟩ | ⟨amount, rfl⟩
            · exact Nat.le_of_eq
                (holder_value_depositUSDC_live s amount a s1 hstep)
            · exact holder_value_redeemApxUSD_live s amount a s1 hstep h_price
          · subst caller
            rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
            · exact Nat.le_of_eq
                (requestUnlock_holderValueAt_neutral s amount a s1 hstep h_registry.1)
            · exact Nat.le_of_eq
                (standardUnlock_claim_neutral_live s requestId a s1 a hstep h_registry
                  h_not_operator rfl)
          · subst caller
            exact Nat.le_of_eq
              (flexibleRequestUnlock_holderValue_live s amount a s1 hstep h_registry)
          · subst caller
            exact flexibleClaim_holderValue_live_nonincreasing s requestId a s1 a hstep
              h_registry h_not_operator rfl
        have h_registry1 : RegistryWellIndexed s1 :=
          registryWellIndexed_step s op caller s1 h_registry hstep
        have h_price1 : s1.redemptionValue ≤ ray :=
          stableHolderValue_price_frame s op caller s1 hop hstep h_price
        have h_operator1 : a ≠ s1.unlockTokenOperator := by
          have hframe := stableHolderValue_operator_frame s op caller s1 hop hstep
          intro hbad
          exact h_not_operator (hbad.trans hframe)
        exact Nat.le_trans
          (ih s1 h_registry1 h_price1 htail_own htail_ops h_operator1) h_step_bound

/-- A nonempty live-rate mixed-ledger trace. The request is a standard unlock
operation, so this witness also checks that the new stable sublanguage is not
defined only by the empty trace. -/
theorem holderValue_stable_trace_witness :
    let s : State :=
      { (default : State) with
          globalPause := false
          apxUSDBal := fun a => if a = 1 then 100 else 0
          totalSupply_apxUSD := 100 }
    let σ : List (Op × Address) := [(Op.requestUnlock 100, 1)]
    holderValue (execTrace s σ) 1 = holderValue s 1 := by
  dsimp only
  let s : State :=
    { (default : State) with
        globalPause := false
        apxUSDBal := fun a => if a = 1 then 100 else 0
        totalSupply_apxUSD := 100 }
  let σ : List (Op × Address) := [(Op.requestUnlock 100, 1)]
  have hsreg : RegistryWellIndexed s := by
    exact registryWellIndexed_of_frame (default : State) s
      ⟨rfl, rfl, rfl, rfl, rfl⟩ registryWellIndexed_default
  have hbound : holderValue (execTrace s σ) 1 ≤ holderValue s 1 := by
    apply holderValue_stable_trace_nonincreasing s σ 1 hsreg
      (by decide) (by
        intro p hp
        have : p = (Op.requestUnlock 100, 1) := by simpa [σ] using hp
        simp [this])
    · intro p hp
      have : p = (Op.requestUnlock 100, 1) := by simpa [σ] using hp
      subst p
      exact Or.inr (Or.inl (Or.inl ⟨100, rfl⟩))
    · decide
  exact Nat.le_antisymm hbound (by decide)

/-- A standard request/claim trace without waits preserves the tracked ordinary holder's
complete value. Failed operations are skipped by `execTrace` and therefore do
not affect the equality. The trace starts from `RegistryWellIndexed`, the
explicit model invariant connecting the finite registry ledger to successful
state transitions. The holder is required not to be the configured unlock
operator; operator-mediated claims for other owners need a separate frame law. -/
theorem standardUnlock_holderValue_trace_neutral
    (s : State) (σ : List (Op × Address)) (a : Address)
    (h_registry : RegistryWellIndexed s)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, StandardUnlockOp p.1)
    (h_not_operator : a ≠ s.unlockTokenOperator) :
    holderValue (execTrace s σ) a = holderValue s a := by
  induction σ generalizing s with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨op, caller⟩ := p
    have hcaller : caller = a := h_own (op, caller) List.mem_cons_self
    have hop : StandardUnlockOp op := h_ops (op, caller) List.mem_cons_self
    have htail_own : ∀ q ∈ σ, q.2 = a :=
      fun q hq => h_own q (List.mem_cons_of_mem _ hq)
    have htail_ops : ∀ q ∈ σ, StandardUnlockOp q.1 :=
      fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op caller with
    | none =>
        exact ih s h_registry htail_own htail_ops h_not_operator
    | some s1 =>
        have h_inv : RegistryWellIndexed s := h_registry
        have h_neutral : holderValue s1 a = holderValue s a := by
          subst caller
          rcases hop with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
          · exact requestUnlock_holderValueAt_neutral s amount a s1 hstep h_inv.1
          · exact standardUnlock_claim_neutral_live s requestId a s1 a hstep h_inv
              h_not_operator rfl
        have h_registry1 : RegistryWellIndexed s1 :=
          registryWellIndexed_step s op caller s1 h_registry hstep
        have h_operator1 : a ≠ s1.unlockTokenOperator := by
          have hframe := standardUnlock_operator_frame s op caller s1 hop hstep
          intro hbad
          exact h_not_operator (hbad.trans hframe)
        exact (ih s1 h_registry1 htail_own htail_ops h_operator1).trans h_neutral

private theorem standardUnlock_claim_neutral_fixed
    (R : Nat) (s : State) (requestId : Nat) (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.claimUnlock requestId) caller = some s')
    (h_registry : RegistryWellIndexed s)
    (h_not_operator : a ≠ s.unlockTokenOperator)
    (h_caller : caller = a) :
    holderValueAt R s' a = holderValueAt R s a := by
  obtain ⟨owner, amount, cooldownEnd, hreq, howner, hcaller, htime, hpost⟩ :=
    claimUnlockStep_effect s requestId caller s' h_step
  have howner_eq : owner = a := by
    have hchoice : caller = owner ∨ caller = s.unlockTokenOperator := hcaller
    rcases hchoice with h | h
    · exact h_caller ▸ h.symm
    · exact False.elim (h_not_operator (h_caller ▸ h))
  subst owner
  have hid : requestId < s.nextUnlockId := by
    by_cases hlt : requestId < s.nextUnlockId
    · exact hlt
    · have hnone := h_registry.1.1 requestId (by omega)
      rw [hreq] at hnone
      simp at hnone
  exact claimUnlock_holderValueAt_neutral s requestId a amount cooldownEnd caller s'
    hid hreq h_step R

private theorem standardUnlockTimed_operator_frame (s : State) (op : Op) (caller : Address)
    (s' : State) (h_op : StandardUnlockTimedOp op)
    (h_step : step s op caller = some s') :
    s'.unlockTokenOperator = s.unlockTokenOperator := by
  rcases h_op with h_standard | ⟨dt, rfl⟩
  · exact standardUnlock_operator_frame s op caller s' h_standard h_step
  · simp only [step] at h_step
    cases Option.some.inj h_step
    rfl

private theorem standardClaim_holderValueAt_fixedRate_any
    (R : Nat) (s : State) (requestId : Nat) (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.claimUnlock requestId) caller = some s')
    (h_registry : RegistryWellIndexed s) :
    holderValueAt R s' a = holderValueAt R s a := by
  obtain ⟨owner, amount, cooldownEnd, hreq, _, _, _, _⟩ :=
    claimUnlockStep_effect s requestId caller s' h_step
  have hid : requestId < s.nextUnlockId := by
    by_cases hlt : requestId < s.nextUnlockId
    · exact hlt
    · have hnone := h_registry.1.1 requestId (by omega)
      rw [hreq] at hnone
      simp at hnone
  by_cases howner : owner = a
  · subst owner
    exact claimUnlock_holderValueAt_neutral s requestId a amount cooldownEnd caller s'
      hid hreq h_step R
  · exact claimUnlock_holderValueAt_fixedRate_frame R s requestId owner amount cooldownEnd caller s'
      a hreq h_step howner

private theorem flexibleClaim_holderValueAt_nonincreasing_any
    (R : Nat) (s : State) (requestId : Nat) (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.flexibleClaimUnlock requestId) caller = some s')
    (h_registry : RegistryWellIndexed s) :
    holderValueAt R s' a ≤ holderValueAt R s a := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, _, _, _, _⟩ :=
    flexibleClaimStep_effect s requestId caller s' h_step
  have hid : requestId < s.nextUnlockId := by
    by_cases hlt : requestId < s.nextUnlockId
    · exact hlt
    · have hnone := h_registry.1.2 requestId (by omega)
      rw [hreq] at hnone
      simp at hnone
  by_cases howner : owner = a
  · subst owner
    have hfee := flexibleClaim_holderValueAt_fee s requestId a amount requestTime cooldownEnd caller s'
      hid hreq h_step R
    omega
  · have hframe := flexibleClaim_holderValueAt_fixedRate_frame R s requestId owner amount
      requestTime cooldownEnd caller s' a hreq h_step howner
    omega

/-- At a fixed pricing rate, a timed trace consisting of the holder's standard
requests, standard claims, and waits is neutral. This is the honest
request-to-claim ledger theorem: `tick` is included so a claim can actually
pass its cooldown, while the rate parameter keeps vesting from being confused
with an unlock transfer. Reverted requests and claims are skipped by
`execTrace`. -/
theorem standardUnlock_holderValueAt_trace_neutral
    (R : Nat) (s : State) (σ : List (Op × Address)) (a : Address)
    (h_registry : RegistryWellIndexed s)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, StandardUnlockTimedOp p.1)
    (h_not_operator : a ≠ s.unlockTokenOperator) :
    holderValueAt R (execTrace s σ) a = holderValueAt R s a := by
  induction σ generalizing s with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨op, caller⟩ := p
    have hcaller : caller = a := h_own (op, caller) List.mem_cons_self
    have hop : StandardUnlockTimedOp op := h_ops (op, caller) List.mem_cons_self
    have htail_own : ∀ q ∈ σ, q.2 = a :=
      fun q hq => h_own q (List.mem_cons_of_mem _ hq)
    have htail_ops : ∀ q ∈ σ, StandardUnlockTimedOp q.1 :=
      fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op caller with
    | none =>
        exact ih s h_registry htail_own htail_ops h_not_operator
    | some s1 =>
        have h_inv : RegistryWellIndexed s := h_registry
        have h_neutral : holderValueAt R s1 a = holderValueAt R s a := by
          rcases hop with h_standard | ⟨dt, rfl⟩
          · subst caller
            rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
            · exact requestUnlock_holderValueAt_fixedRate R s amount a s1 hstep h_inv.1
            · exact standardUnlock_claim_neutral_fixed R s requestId a s1 a hstep h_inv
                h_not_operator rfl
          · simpa [hcaller] using tick_holderValueAt_frame R s dt caller s1 hstep
        have h_registry1 : RegistryWellIndexed s1 :=
          registryWellIndexed_step s op caller s1 h_registry hstep
        have h_operator1 : a ≠ s1.unlockTokenOperator := by
          have hframe := standardUnlockTimed_operator_frame s op caller s1 hop hstep
          intro hbad
          exact h_not_operator (hbad.trans hframe)
        exact (ih s1 h_registry1 htail_own htail_ops h_operator1).trans h_neutral

/-- Non-vacuity witness: the holder requests all 100 apxUSD, waits out the
cooldown, and successfully claims the same standard position. The final
registry and balance facts ensure the claim was not merely skipped by
`execTrace`. -/
theorem standardUnlock_holderValueAt_trace_witness :
    let s : State :=
      { (default : State) with
          globalPause := false
          apxUSDBal := fun a => if a = 1 then 100 else 0
          totalSupply_apxUSD := 100 }
    let σ : List (Op × Address) :=
      [(Op.requestUnlock 100, 1), (Op.tick cooldownPeriod, 1), (Op.claimUnlock 0, 1)]
    holderValueAt ray (execTrace s σ) 1 = holderValueAt ray s 1 ∧
    (execTrace s σ).unlockRequests 0 = none ∧
    (execTrace s σ).apxUSDBal 1 = 100 := by
  dsimp only
  let s : State :=
    { (default : State) with
        globalPause := false
        apxUSDBal := fun a => if a = 1 then 100 else 0
        totalSupply_apxUSD := 100 }
  let σ : List (Op × Address) :=
    [(Op.requestUnlock 100, 1), (Op.tick cooldownPeriod, 1), (Op.claimUnlock 0, 1)]
  have hsreg : RegistryWellIndexed s := by
    exact registryWellIndexed_of_frame (default : State) s
      ⟨rfl, rfl, rfl, rfl, rfl⟩ registryWellIndexed_default
  constructor
  · apply standardUnlock_holderValueAt_trace_neutral ray s σ 1 hsreg
    · intro p hp
      have hp' : p = (Op.requestUnlock 100, 1) ∨
          p = (Op.tick cooldownPeriod, 1) ∨ p = (Op.claimUnlock 0, 1) := by
        simpa [σ] using hp
      rcases hp' with rfl | rfl | rfl <;> rfl
    · intro p hp
      have hp' : p = (Op.requestUnlock 100, 1) ∨
          p = (Op.tick cooldownPeriod, 1) ∨ p = (Op.claimUnlock 0, 1) := by
        simpa [σ] using hp
      rcases hp' with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨100, rfl⟩)
      · exact Or.inr ⟨cooldownPeriod, rfl⟩
      · exact Or.inl (Or.inr ⟨0, rfl⟩)
    · decide
  · decide

/-! ## Standard and flexible unlock traces

The flexible channel composes with the same fixed-rate ledger, but its claim
law is an inequality: the explicit early-exit fee leaves the holder no better
off. The trace theorem below therefore uses `≤`, while the standard-only
theorem above can use equality. -/

/-- Timed operations in either unlock channel, including waiting. -/
def UnlockLedgerTimedOp (op : Op) : Prop :=
  StandardUnlockTimedOp op ∨
  (∃ amount, op = Op.flexibleRequestUnlock amount) ∨
  (∃ requestId, op = Op.flexibleClaimUnlock requestId)

private theorem unlockLedgerTimed_operator_frame (s : State) (op : Op) (caller : Address)
    (s' : State) (h_op : UnlockLedgerTimedOp op)
    (h_step : step s op caller = some s') :
    s'.unlockTokenOperator = s.unlockTokenOperator := by
  rcases h_op with h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
  · exact standardUnlockTimed_operator_frame s op caller s' h_standard h_step
  · obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
    rw [hpost]
    simp [createFlexibleUnlock, burnApxUSD]
  · obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, howner, hcaller, htime, hpost⟩ :=
      flexibleClaimStep_effect s requestId caller s' h_step
    rw [hpost]
    simp [mintApxUSD, retireFlexibleUnlock, burnUnlockNFT]

private theorem flexibleClaim_holderValueAt_nonincreasing
    (R : Nat) (s : State) (requestId : Nat) (caller : Address) (s' : State) (a : Address)
    (h_step : step s (Op.flexibleClaimUnlock requestId) caller = some s')
    (h_registry : RegistryWellIndexed s)
    (h_not_operator : a ≠ s.unlockTokenOperator)
    (h_caller : caller = a) :
    holderValueAt R s' a ≤ holderValueAt R s a := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, howner, hcaller, htime, hpost⟩ :=
    flexibleClaimStep_effect s requestId caller s' h_step
  have howner_eq : owner = a := by
    have hchoice : caller = owner ∨ caller = s.unlockTokenOperator := hcaller
    rcases hchoice with h | h
    · exact h_caller ▸ h.symm
    · exact False.elim (h_not_operator (h_caller ▸ h))
  subst owner
  have hid : requestId < s.nextUnlockId := by
    by_cases hlt : requestId < s.nextUnlockId
    · exact hlt
    · have hnone := h_registry.1.2 requestId (by omega)
      rw [hreq] at hnone
      simp at hnone
  have hfee := flexibleClaim_holderValueAt_fee s requestId a amount requestTime cooldownEnd caller s'
    hid hreq h_step R
  omega

/-- At a fixed rate, a trace over both unlock channels and waits never raises
the tracked ordinary holder's complete value. Standard requests and claims
are neutral; a flexible claim may lower value by its explicit fee. -/
theorem unlockLedger_holderValueAt_trace_nonincreasing
    (R : Nat) (s : State) (σ : List (Op × Address)) (a : Address)
    (h_registry : RegistryWellIndexed s)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, UnlockLedgerTimedOp p.1)
    (h_not_operator : a ≠ s.unlockTokenOperator) :
    holderValueAt R (execTrace s σ) a ≤ holderValueAt R s a := by
  induction σ generalizing s with
  | nil => exact Nat.le_refl _
  | cons p σ ih =>
    obtain ⟨op, caller⟩ := p
    have hcaller : caller = a := h_own (op, caller) List.mem_cons_self
    have hop : UnlockLedgerTimedOp op := h_ops (op, caller) List.mem_cons_self
    have htail_own : ∀ q ∈ σ, q.2 = a :=
      fun q hq => h_own q (List.mem_cons_of_mem _ hq)
    have htail_ops : ∀ q ∈ σ, UnlockLedgerTimedOp q.1 :=
      fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op caller with
    | none =>
        exact ih s h_registry htail_own htail_ops h_not_operator
    | some s1 =>
        have h_inv : RegistryWellIndexed s := h_registry
        have h_step_bound : holderValueAt R s1 a ≤ holderValueAt R s a := by
          rcases hop with h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
          · rcases h_standard with h_standard | ⟨dt, rfl⟩
            · subst caller
              rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
              · exact Nat.le_of_eq
                  (requestUnlock_holderValueAt_fixedRate R s amount a s1 hstep h_inv.1)
              · exact Nat.le_of_eq
                  (standardUnlock_claim_neutral_fixed R s requestId a s1 a hstep h_inv
                    h_not_operator rfl)
            · exact Nat.le_of_eq (by
                simpa [hcaller] using tick_holderValueAt_frame R s dt caller s1 hstep)
          · subst caller
            exact Nat.le_of_eq
              (flexibleRequestUnlock_holderValueAt_fixedRate R s amount a s1 hstep h_inv)
          · subst caller
            exact flexibleClaim_holderValueAt_nonincreasing R s requestId a s1 a hstep h_inv
              h_not_operator rfl
        have h_registry1 : RegistryWellIndexed s1 :=
          registryWellIndexed_step s op caller s1 h_registry hstep
        have h_operator1 : a ≠ s1.unlockTokenOperator := by
          have hframe := unlockLedgerTimed_operator_frame s op caller s1 hop hstep
          intro hbad
          exact h_not_operator (hbad.trans hframe)
        exact Nat.le_trans (ih s1 h_registry1 htail_own htail_ops h_operator1) h_step_bound

/-- The same fixed-rate ledger bound with arbitrary callers. A caller may be
the tracked holder, another holder, or the registry operator: the per-owner
frame lemmas above decide which case applies. This is the trace-level form
used for protocol-level safety statements; restricting every caller to `a`
is only needed by the older compatibility theorem above. -/
theorem unlockLedger_holderValueAt_trace_nonincreasing_any_callers
    (R : Nat) (s : State) (σ : List (Op × Address)) (a : Address)
    (h_registry : RegistryWellIndexed s)
    (h_ops : ∀ p ∈ σ, UnlockLedgerTimedOp p.1) :
    holderValueAt R (execTrace s σ) a ≤ holderValueAt R s a := by
  induction σ generalizing s with
  | nil => exact Nat.le_refl _
  | cons p σ ih =>
    obtain ⟨op, caller⟩ := p
    have hop : UnlockLedgerTimedOp op := h_ops (op, caller) List.mem_cons_self
    have htail_ops : ∀ q ∈ σ, UnlockLedgerTimedOp q.1 :=
      fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op caller with
    | none =>
        exact ih s h_registry htail_ops
    | some s1 =>
        have h_step_bound : holderValueAt R s1 a ≤ holderValueAt R s a := by
          rcases hop with h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
          · rcases h_standard with h_standard | ⟨dt, rfl⟩
            · rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
              · by_cases hsame : caller = a
                · subst caller
                  exact Nat.le_of_eq
                    (requestUnlock_holderValueAt_fixedRate R s amount a s1 hstep h_registry.1)
                · exact Nat.le_of_eq
                    (requestUnlock_holderValueAt_fixedRate_frame R s amount caller s1 a hstep
                      h_registry.1)
              · exact Nat.le_of_eq
                  (standardClaim_holderValueAt_fixedRate_any R s requestId caller s1 a hstep
                    h_registry)
            · exact Nat.le_of_eq (tick_holderValueAt_frame_any R s dt caller s1 a hstep)
          · by_cases hsame : caller = a
            · subst caller
              exact Nat.le_of_eq
                (flexibleRequestUnlock_holderValueAt_fixedRate R s amount a s1 hstep h_registry)
            · exact Nat.le_of_eq
                (flexibleRequestUnlock_holderValueAt_fixedRate_frame R s amount caller s1 a hstep
                  h_registry hsame)
          · exact flexibleClaim_holderValueAt_nonincreasing_any R s requestId caller s1 a hstep
              h_registry
        have h_registry1 : RegistryWellIndexed s1 :=
          registryWellIndexed_step s op caller s1 h_registry hstep
        exact Nat.le_trans (ih s1 h_registry1 htail_ops) h_step_bound

/-- Non-vacuity witness for the fee-bearing branch: a 1000 apxUSD flexible
request, cooldown wait, and claim leaves 999 apxUSD because the 10 bps
post-cooldown fee floors to one unit. -/
theorem unlockLedger_holderValueAt_trace_witness :
    let s : State :=
      { (default : State) with
          globalPause := false
          apxUSDBal := fun a => if a = 1 then 1000 else 0
          totalSupply_apxUSD := 1000 }
    let σ : List (Op × Address) :=
      [(Op.flexibleRequestUnlock 1000, 1), (Op.tick cooldownPeriod, 1),
        (Op.flexibleClaimUnlock 0, 1)]
    holderValueAt ray (execTrace s σ) 1 ≤ holderValueAt ray s 1 ∧
    (execTrace s σ).flexibleUnlockRequests 0 = none ∧
    (execTrace s σ).apxUSDBal 1 = 999 := by
  dsimp only
  let s : State :=
    { (default : State) with
        globalPause := false
        apxUSDBal := fun a => if a = 1 then 1000 else 0
        totalSupply_apxUSD := 1000 }
  let σ : List (Op × Address) :=
    [(Op.flexibleRequestUnlock 1000, 1), (Op.tick cooldownPeriod, 1),
      (Op.flexibleClaimUnlock 0, 1)]
  have hsreg : RegistryWellIndexed s := by
    exact registryWellIndexed_of_frame (default : State) s
      ⟨rfl, rfl, rfl, rfl, rfl⟩ registryWellIndexed_default
  constructor
  · apply unlockLedger_holderValueAt_trace_nonincreasing ray s σ 1 hsreg
    · intro p hp
      have hp' : p = (Op.flexibleRequestUnlock 1000, 1) ∨
          p = (Op.tick cooldownPeriod, 1) ∨ p = (Op.flexibleClaimUnlock 0, 1) := by
        simpa [σ] using hp
      rcases hp' with rfl | rfl | rfl <;> rfl
    · intro p hp
      have hp' : p = (Op.flexibleRequestUnlock 1000, 1) ∨
          p = (Op.tick cooldownPeriod, 1) ∨ p = (Op.flexibleClaimUnlock 0, 1) := by
        simpa [σ] using hp
      rcases hp' with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨1000, rfl⟩)
      · exact Or.inl (Or.inr ⟨cooldownPeriod, rfl⟩)
      · exact Or.inr (Or.inr ⟨0, rfl⟩)
    · decide
  · decide

end Apyx
