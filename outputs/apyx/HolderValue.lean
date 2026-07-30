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

/-- apxUSD held inside `a`'s pending **standard** unlock positions.

Folded over `List.range s.nextUnlockId`: `createStandardUnlock` only ever allocates at the
current counter and then increments it, so every live position sits at an id strictly below it.
That bound is what makes a `Σ` over positions available in a model whose registry is a bare
function. -/
def stdPositions (s : State) (a : Address) : Nat :=
  (List.range s.nextUnlockId).foldl
    (fun acc i =>
      match s.unlockRequests i with
      | some (o, amt, _) => if o = a then acc + amt else acc
      | none => acc) 0

/-- apxUSD held inside `a`'s pending **flexible** unlock positions. Same fold, same bound. -/
def flexPositions (s : State) (a : Address) : Nat :=
  (List.range s.nextUnlockId).foldl
    (fun acc i =>
      match s.flexibleUnlockRequests i with
      | some (o, amt, _, _) => if o = a then acc + amt else acc
      | none => acc) 0

/-- Everything `a` owns, in apxUSD units, priced at the state's **live** rate.

The four terms the old `valueAt` had, plus the two it dropped. apxUSD and USDC are both counted
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

/-! ## The fold, and what it counts -/

/-- Folding an accumulator that only ever adds is monotone in the accumulator, and the fold
splits off its seed. Stated as the shape both position sums need. -/
private theorem foldl_add_seed (l : List Nat) (f : Nat → Nat) (z : Nat) :
    l.foldl (fun acc i => acc + f i) z = z + l.foldl (fun acc i => acc + f i) 0 := by
  induction l generalizing z with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih (z + f i), ih (0 + f i)]
    omega

/-- An all-`none` registry contributes nothing to the fold, over any id list. -/
private theorem foldl_positions_none (l : List Nat) (s : State) (a : Address)
    (h : ∀ i ∈ l, s.unlockRequests i = none) :
    l.foldl (fun acc i =>
      match s.unlockRequests i with
      | some (o, amt, _) => if o = a then acc + amt else acc
      | none => acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi : s.unlockRequests i = none := h i List.mem_cons_self
    simp only [List.foldl_cons, hi]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- Positions at ids the fold does not reach contribute nothing: the sum only looks below
`nextUnlockId`. -/
theorem stdPositions_eq_zero_of_no_positions (s : State) (a : Address)
    (h : ∀ i, i < s.nextUnlockId → s.unlockRequests i = none) :
    stdPositions s a = 0 :=
  foldl_positions_none _ s a (fun i hi => h i (List.mem_range.mp hi))

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
