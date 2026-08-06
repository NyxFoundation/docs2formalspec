import D2fsSpecs.Safety
import D2fsSpecs.Registry
import D2fsSpecs.Ledger

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

/-! ## Optional finite apyUSD accounting boundary

The core `State` stores apyUSD balances as an arbitrary address function, so
the holder-value theorems above do not silently pretend that
`totalSupply_apyUSD` is the sum of all balances. The predicate below is the
explicit finite-support relation needed before a pool-wide apyUSD appreciation
theorem can be stated. -/

def ApyUSDLedgerConsistent (s : State) : Prop :=
  ∃ holders : List Address,
    holders.Pairwise (· ≠ ·) ∧
    (∀ a, s.apyUSDBal a ≠ 0 → a ∈ holders) ∧
    sumOver s.apyUSDBal holders = s.totalSupply_apyUSD

theorem apyUSDLedgerConsistent_default :
    ApyUSDLedgerConsistent (default : State) := by
  refine ⟨[], List.Pairwise.nil, ?_, rfl⟩
  intro a hne
  exact absurd rfl hne

/-! ## Primitive apyUSD writers

The arbitrary address function is not, by itself, a reason to abandon the
finite ledger relation. Once the relation supplies a finite support list, the
two apyUSD writers can preserve it exactly. The underflow bound on burns is
essential: without it, truncated `Nat` subtraction can reduce one balance by
less than the amount removed from `totalSupply_apyUSD`. -/

theorem apyUSDLedgerConsistent_mint (s : State) (to : Address) (amount : Nat)
    (h : ApyUSDLedgerConsistent s) :
    ApyUSDLedgerConsistent (mintApyUSD s to amount) := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  by_cases hmem : to ∈ holders
  · refine ⟨holders, hnd, ?_, ?_⟩
    · intro a ha
      by_cases hat : a = to
      · subst hat; exact hmem
      · exact hcov a (by simpa [mintApyUSD, hat] using ha)
    · show sumOver (fun a => if a = to then s.apyUSDBal a + amount else s.apyUSDBal a)
          holders = s.totalSupply_apyUSD + amount
      rw [sumOver_update_add_mem s.apyUSDBal to amount hnd hmem, hsum]
  · have hzero : s.apyUSDBal to = 0 := by
      by_cases hz : s.apyUSDBal to = 0
      · exact hz
      · exact False.elim (hmem (hcov to hz))
    refine ⟨to :: holders, ?_, ?_, ?_⟩
    · refine List.Pairwise.cons ?_ hnd
      intro b hb heq
      subst heq
      exact hmem hb
    · intro a ha
      by_cases hat : a = to
      · exact List.mem_cons.mpr (Or.inl hat)
      · exact List.mem_cons.mpr (Or.inr (hcov a (by
          simpa [mintApyUSD, hat] using ha)))
    · show sumOver (fun a => if a = to then s.apyUSDBal a + amount else s.apyUSDBal a)
          (to :: holders) = s.totalSupply_apyUSD + amount
      have htail : sumOver (fun a => if a = to then s.apyUSDBal a + amount else s.apyUSDBal a)
          holders = sumOver s.apyUSDBal holders :=
        sumOver_congr (fun b hb => by
          by_cases hbt : b = to
          · subst b
            exact False.elim (hmem hb)
          · simp [hbt])
      simp only [sumOver_cons]
      simp [htail, hzero, hsum]
      omega

theorem apyUSDLedgerConsistent_burn (s : State) (fromAddr : Address) (amount : Nat)
    (hle : amount ≤ s.apyUSDBal fromAddr)
    (h : ApyUSDLedgerConsistent s) :
    ApyUSDLedgerConsistent (burnApyUSD s fromAddr amount) := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  refine ⟨holders, hnd, ?_, ?_⟩
  · intro a ha
    by_cases hat : a = fromAddr
    · subst a
      refine hcov fromAddr (fun hz => ha ?_)
      simp [burnApyUSD, hz]
    · exact hcov a (by simpa [burnApyUSD, hat] using ha)
  · by_cases hmem : fromAddr ∈ holders
    · show sumOver (fun a => if a = fromAddr then s.apyUSDBal a - amount else s.apyUSDBal a)
          holders = s.totalSupply_apyUSD - amount
      have hkey := sumOver_update_sub_mem s.apyUSDBal fromAddr amount hle hnd hmem
      omega
    · have hzero : s.apyUSDBal fromAddr = 0 := by
        by_cases hz : s.apyUSDBal fromAddr = 0
        · exact hz
        · exact False.elim (hmem (hcov fromAddr hz))
      have hamt : amount = 0 := by omega
      subst hamt
      show sumOver (fun a => if a = fromAddr then s.apyUSDBal a - 0 else s.apyUSDBal a)
          holders = s.totalSupply_apyUSD - 0
      have hcong : sumOver (fun a => if a = fromAddr then s.apyUSDBal a - 0 else s.apyUSDBal a)
          holders = sumOver s.apyUSDBal holders :=
        sumOver_congr (fun b _ => by simp)
      rw [hcong]
      omega

theorem apyUSDLedgerConsistent_of_projections_eq {s t : State}
    (hbal : s.apyUSDBal = t.apyUSDBal)
    (hsup : s.totalSupply_apyUSD = t.totalSupply_apyUSD)
    (h : ApyUSDLedgerConsistent t) : ApyUSDLedgerConsistent s := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  refine ⟨holders, hnd, ?_, ?_⟩
  · intro a ha
    refine hcov a ?_
    rw [← hbal]
    exact ha
  · rw [hbal, hsup]
    exact hsum

/-! ## Public-step projections

Only three `Op` constructors write the apyUSD ledger projections: `lockApxUSD`
mints apyUSD shares, while `withdraw` and `redeem` burn them. The successful
branch lemmas below expose precisely those primitive writers and their
underflow bounds. All other operations are handled as projection frames. -/

private theorem pullVestedYield_apyUSDBal_local (s : State) :
    (pullVestedYield s).apyUSDBal = s.apyUSDBal := by
  unfold pullVestedYield
  dsimp only
  split <;> rfl

private theorem step_lockApyUSD_ledgerProj (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h : step s (Op.lockApxUSD amount) caller = some s') :
    ∃ shares, s'.apyUSDBal = (mintApyUSD s caller shares).apyUSDBal ∧
      s'.totalSupply_apyUSD = (mintApyUSD s caller shares).totalSupply_apyUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · cases Option.some.inj h
        exact ⟨lockShares amount (computeExchangeRate s), by
          simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD], by
          simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]⟩

private theorem step_withdrawApyUSD_ledgerProj (s : State) (assets : Nat)
    (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    ∃ shares, shares ≤ s.apyUSDBal caller ∧
      s'.apyUSDBal = (burnApyUSD s caller shares).apyUSDBal ∧
      s'.totalSupply_apyUSD = (burnApyUSD s caller shares).totalSupply_apyUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · have hle : withdrawShares assets (computeExchangeRate (pullVestedYield s)) ≤
              s.apyUSDBal caller := by
            have hpull := pullVestedYield_apyUSDBal_local s
            rw [← hpull]
            omega
          cases Option.some.inj h
          refine ⟨withdrawShares assets (computeExchangeRate (pullVestedYield s)), hle, ?_, ?_⟩
          · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
          · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

private theorem step_redeemApyUSD_ledgerProj (s : State) (shares : Nat)
    (receiver caller : Address) (s' : State)
    (h : step s (Op.redeem shares receiver) caller = some s') :
    shares ≤ s.apyUSDBal caller ∧
      s'.apyUSDBal = (burnApyUSD s caller shares).apyUSDBal ∧
      s'.totalSupply_apyUSD = (burnApyUSD s caller shares).totalSupply_apyUSD := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · have hle : shares ≤ s.apyUSDBal caller := by
            have hpull := pullVestedYield_apyUSDBal_local s
            rw [← hpull]
            omega
          cases Option.some.inj h
          refine ⟨hle, ?_, ?_⟩
          · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
          · simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

theorem apyUSDLedgerConsistent_lock_step
    (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : ApyUSDLedgerConsistent s)
    (hstep : step s (Op.lockApxUSD amount) caller = some s') :
    ApyUSDLedgerConsistent s' := by
  obtain ⟨shares, hbal, hsup⟩ := step_lockApyUSD_ledgerProj s amount caller s' hstep
  exact apyUSDLedgerConsistent_of_projections_eq hbal hsup
    (apyUSDLedgerConsistent_mint s caller shares h)

theorem apyUSDLedgerConsistent_withdraw_step
    (s : State) (assets receiver caller : Address) (s' : State)
    (h : ApyUSDLedgerConsistent s)
    (hstep : step s (Op.withdraw assets receiver) caller = some s') :
    ApyUSDLedgerConsistent s' := by
  obtain ⟨shares, hle, hbal, hsup⟩ :=
    step_withdrawApyUSD_ledgerProj s assets receiver caller s' hstep
  exact apyUSDLedgerConsistent_of_projections_eq hbal hsup
    (apyUSDLedgerConsistent_burn s caller shares hle h)

theorem apyUSDLedgerConsistent_redeem_step
    (s : State) (shares receiver caller : Address) (s' : State)
    (h : ApyUSDLedgerConsistent s)
    (hstep : step s (Op.redeem shares receiver) caller = some s') :
    ApyUSDLedgerConsistent s' := by
  obtain ⟨hle, hbal, hsup⟩ :=
    step_redeemApyUSD_ledgerProj s shares receiver caller s' hstep
  exact apyUSDLedgerConsistent_of_projections_eq hbal hsup
    (apyUSDLedgerConsistent_burn s caller shares hle h)

inductive ApyLedgerFrameOp : Op → Prop where
  | depositUSDC (amount : Nat) : ApyLedgerFrameOp (Op.depositUSDC amount)
  | mintApxUSD (to : Address) (amount : Nat) : ApyLedgerFrameOp (Op.mintApxUSD to amount)
  | requestUnlock (amount : Nat) : ApyLedgerFrameOp (Op.requestUnlock amount)
  | claimUnlock (id : Nat) : ApyLedgerFrameOp (Op.claimUnlock id)
  | redeemApxUSD (amount : Nat) : ApyLedgerFrameOp (Op.redeemApxUSD amount)
  | flexibleRequestUnlock (amount : Nat) :
      ApyLedgerFrameOp (Op.flexibleRequestUnlock amount)
  | flexibleClaimUnlock (id : Nat) : ApyLedgerFrameOp (Op.flexibleClaimUnlock id)
  | pause : ApyLedgerFrameOp Op.pause
  | unpause : ApyLedgerFrameOp Op.unpause
  | addToWhitelist (addr : Address) : ApyLedgerFrameOp (Op.addToWhitelist addr)
  | removeFromWhitelist (addr : Address) : ApyLedgerFrameOp (Op.removeFromWhitelist addr)
  | addToDenylist (addr : Address) : ApyLedgerFrameOp (Op.addToDenylist addr)
  | removeFromDenylist (addr : Address) : ApyLedgerFrameOp (Op.removeFromDenylist addr)
  | setYieldRate (bps : Nat) : ApyLedgerFrameOp (Op.setYieldRate bps)
  | creditYield (amount : Nat) : ApyLedgerFrameOp (Op.creditYield amount)
  | voteBufferDeployment : ApyLedgerFrameOp Op.voteBufferDeployment
  | submitRFQRequest (amount : Nat) : ApyLedgerFrameOp (Op.submitRFQRequest amount)
  | executeRFQRedemption (user : Address) (amount : Nat) :
      ApyLedgerFrameOp (Op.executeRFQRedemption user amount)
  | updateRedemptionValue (newValue : Nat) :
      ApyLedgerFrameOp (Op.updateRedemptionValue newValue)
  | handleStressEvent (amount : Nat) : ApyLedgerFrameOp (Op.handleStressEvent amount)
  | catastrophicBackstop : ApyLedgerFrameOp Op.catastrophicBackstop
  | setVestPeriod (p : Nat) : ApyLedgerFrameOp (Op.setVestPeriod p)
  | setApxUSDMarketPrice (price : Nat) : ApyLedgerFrameOp (Op.setApxUSDMarketPrice price)
  | withdrawReserve (amount : Nat) (receiver : Address) :
      ApyLedgerFrameOp (Op.withdrawReserve amount receiver)
  | poolRedeem (amount : Nat) (receiver : Address) (minOut : Nat) :
      ApyLedgerFrameOp (Op.poolRedeem amount receiver minOut)
  | tick (dt : Nat) : ApyLedgerFrameOp (Op.tick dt)

theorem apyUSDLedgerConsistent_frame_step
    (s s' : State) (op : Op) (caller : Address) (hop : ApyLedgerFrameOp op)
    (hstep : step s op caller = some s') :
    s'.apyUSDBal = s.apyUSDBal ∧ s'.totalSupply_apyUSD = s.totalSupply_apyUSD := by
  cases hop <;>
    simp only [step] at hstep
  all_goals
    repeat' split at hstep
    all_goals
      cases hstep <;>
        constructor <;>
          simp [burnApxUSD, mintApxUSD, emitEvent, createFlexibleUnlock, retireStandardUnlock,
            retireFlexibleUnlock, burnUnlockNFT]

inductive ApyLedgerCoveredOp : Op → Prop where
  | lock (amount : Nat) : ApyLedgerCoveredOp (Op.lockApxUSD amount)
  | withdraw (assets : Nat) (receiver : Address) :
      ApyLedgerCoveredOp (Op.withdraw assets receiver)
  | redeem (shares : Nat) (receiver : Address) :
      ApyLedgerCoveredOp (Op.redeem shares receiver)
  | frame {op : Op} (h : ApyLedgerFrameOp op) : ApyLedgerCoveredOp op

theorem apyLedgerCoveredOp_all (op : Op) : ApyLedgerCoveredOp op := by
  cases op with
  | depositUSDC amount => exact .frame (.depositUSDC amount)
  | mintApxUSD to amount => exact .frame (.mintApxUSD to amount)
  | lockApxUSD amount => exact .lock amount
  | requestUnlock amount => exact .frame (.requestUnlock amount)
  | claimUnlock id => exact .frame (.claimUnlock id)
  | redeemApxUSD amount => exact .frame (.redeemApxUSD amount)
  | withdraw assets receiver => exact .withdraw assets receiver
  | redeem shares receiver => exact .redeem shares receiver
  | flexibleRequestUnlock amount => exact .frame (.flexibleRequestUnlock amount)
  | flexibleClaimUnlock id => exact .frame (.flexibleClaimUnlock id)
  | pause => exact .frame .pause
  | unpause => exact .frame .unpause
  | addToWhitelist addr => exact .frame (.addToWhitelist addr)
  | removeFromWhitelist addr => exact .frame (.removeFromWhitelist addr)
  | addToDenylist addr => exact .frame (.addToDenylist addr)
  | removeFromDenylist addr => exact .frame (.removeFromDenylist addr)
  | setYieldRate bps => exact .frame (.setYieldRate bps)
  | creditYield amount => exact .frame (.creditYield amount)
  | voteBufferDeployment => exact .frame .voteBufferDeployment
  | submitRFQRequest amount => exact .frame (.submitRFQRequest amount)
  | executeRFQRedemption user amount => exact .frame (.executeRFQRedemption user amount)
  | updateRedemptionValue newValue => exact .frame (.updateRedemptionValue newValue)
  | handleStressEvent amount => exact .frame (.handleStressEvent amount)
  | catastrophicBackstop => exact .frame .catastrophicBackstop
  | setVestPeriod p => exact .frame (.setVestPeriod p)
  | setApxUSDMarketPrice price => exact .frame (.setApxUSDMarketPrice price)
  | withdrawReserve amount receiver => exact .frame (.withdrawReserve amount receiver)
  | poolRedeem amount receiver minOut => exact .frame (.poolRedeem amount receiver minOut)
  | tick dt => exact .frame (.tick dt)

theorem apyUSDLedgerConsistent_covered_step
    (s s' : State) (op : Op) (caller : Address)
    (hop : ApyLedgerCoveredOp op) (h : ApyUSDLedgerConsistent s)
    (hstep : step s op caller = some s') :
    ApyUSDLedgerConsistent s' := by
  cases hop with
  | lock amount => exact apyUSDLedgerConsistent_lock_step s amount caller s' h hstep
  | withdraw assets receiver =>
      exact apyUSDLedgerConsistent_withdraw_step s assets receiver caller s' h hstep
  | redeem shares receiver =>
      exact apyUSDLedgerConsistent_redeem_step s shares receiver caller s' h hstep
  | frame hframe =>
      obtain ⟨hbal, hsup⟩ := apyUSDLedgerConsistent_frame_step s s' op caller hframe hstep
      exact apyUSDLedgerConsistent_of_projections_eq hbal hsup h

theorem apyUSDLedgerConsistent_step
    (s s' : State) (op : Op) (caller : Address)
    (h : ApyUSDLedgerConsistent s)
    (hstep : step s op caller = some s') :
    ApyUSDLedgerConsistent s' :=
  apyUSDLedgerConsistent_covered_step s s' op caller
    (apyLedgerCoveredOp_all op) h hstep

theorem apyUSDLedgerConsistent_trace (s : State) (σ : List (Op × Address))
    (h : ApyUSDLedgerConsistent s) :
    ApyUSDLedgerConsistent (execTrace s σ) := by
  induction σ generalizing s with
  | nil => exact h
  | cons p σ ih =>
      obtain ⟨op, caller⟩ := p
      simp only [execTrace]
      cases hstep : step s op caller with
      | none => exact ih s h
      | some s' =>
          exact ih s' (apyUSDLedgerConsistent_step s s' op caller h hstep)

/-! An explicit model-gap witness is still useful after proving preservation:
the predicate is a reachable-state invariant, not a restriction built into the
`State` type. -/

def apyUSDLedgerGapWitness : State :=
  { (default : State) with
      apyUSDBal := fun a => if a = 0 then 1 else if a = 1 then 1 else 0
      totalSupply_apyUSD := 1 }

theorem apyUSDLedgerGapWitness_two_holders_exceed_supply :
    apyUSDLedgerGapWitness.apyUSDBal 0 + apyUSDLedgerGapWitness.apyUSDBal 1
      > apyUSDLedgerGapWitness.totalSupply_apyUSD := by
  decide

theorem apyUSDLedgerGapWitness_not_consistent :
    ¬ ApyUSDLedgerConsistent apyUSDLedgerGapWitness := by
  intro h
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  have h0 : 0 ∈ holders := hcov 0 (by decide)
  have h1 : 1 ∈ holders := hcov 1 (by decide)
  have htwo := sumOver_two_mem_le apyUSDLedgerGapWitness.apyUSDBal
    (by decide : (0 : Address) ≠ 1) h0 h1
  rw [hsum] at htwo
  have hgt :
    apyUSDLedgerGapWitness.apyUSDBal 0 + apyUSDLedgerGapWitness.apyUSDBal 1
      > apyUSDLedgerGapWitness.totalSupply_apyUSD := by decide
  omega

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

/-! ## Aggregate pending-apxUSD boundary

`stdPositions` and `flexPositions` are holder-facing views. The following
totals deliberately sum the registries by position id instead: they do not
need a finite address list and therefore do not pretend that the `usdcBal`
function or the protocol's custody fields already form a complete asset
ledger. Adding the current apxUSD supply gives the amount of apxUSD that is
either circulating or owed by a pending unlock claim.
-/

/-- Total face amount in the finite standard-unlock registry. -/
def standardUnlockTotal (s : State) : Nat :=
  ((List.range s.nextUnlockId).map (fun i =>
    match s.unlockRequests i with
    | some (_, amount, _) => amount
    | none => 0)).sum

/-- Total face amount in the finite flexible-unlock registry. -/
def flexibleUnlockTotal (s : State) : Nat :=
  ((List.range s.nextUnlockId).map (fun i =>
    match s.flexibleUnlockRequests i with
    | some (_, amount, _, _) => amount
    | none => 0)).sum

/-- The two pending unlock registries, counted in apxUSD face units. -/
def pendingApxUSD (s : State) : Nat :=
  standardUnlockTotal s + flexibleUnlockTotal s

/-- Circulating apxUSD plus the face amount promised by pending unlocks. -/
def outstandingApxUSD (s : State) : Nat :=
  s.totalSupply_apxUSD + pendingApxUSD s

/-- A flow measure for the modeled apxUSD subsystem: circulating supply,
pending unlock face amounts, and apxUSD currently held in vault custody. This
is an internal custody-flow boundary, not a reserve-solvency claim. Vested but
not yet pulled yield is intentionally outside this measure; its realization is
an external inflow into custody and must be handled by a separate live-assets
theorem. -/
def apxUSDFlow (s : State) : Nat :=
  s.vaultApxUSDBal + outstandingApxUSD s

theorem standardUnlockTotal_of_projections_eq {s t : State}
    (hnext : s.nextUnlockId = t.nextUnlockId)
    (hrequests : s.unlockRequests = t.unlockRequests) :
    standardUnlockTotal s = standardUnlockTotal t := by
  unfold standardUnlockTotal
  rw [hnext, hrequests]

theorem flexibleUnlockTotal_of_projections_eq {s t : State}
    (hnext : s.nextUnlockId = t.nextUnlockId)
    (hrequests : s.flexibleUnlockRequests = t.flexibleUnlockRequests) :
    flexibleUnlockTotal s = flexibleUnlockTotal t := by
  unfold flexibleUnlockTotal
  rw [hnext, hrequests]

theorem outstandingApxUSD_of_projections_eq {s t : State}
    (hsupply : s.totalSupply_apxUSD = t.totalSupply_apxUSD)
    (hnext : s.nextUnlockId = t.nextUnlockId)
    (hstandard : s.unlockRequests = t.unlockRequests)
    (hflexible : s.flexibleUnlockRequests = t.flexibleUnlockRequests) :
    outstandingApxUSD s = outstandingApxUSD t := by
  unfold outstandingApxUSD pendingApxUSD
  rw [hsupply, standardUnlockTotal_of_projections_eq hnext hstandard,
    flexibleUnlockTotal_of_projections_eq hnext hflexible]

/-! ## Unlock-token amount consistency

`RegistryWellIndexed` relates owners and ids, but it intentionally does not
relate a pending registry amount to the amount carried by the corresponding
unlock token. The latter is a separate accounting identity: without it,
`outstandingApxUSD` can count one face amount while a claim mints another.
This predicate closes that model-local gap without pretending that the fee
wallet or the USDC supply is already represented in `State`. -/

def UnlockTokenLedgerConsistent (s : State) : Prop :=
  ∀ id, id < s.nextUnlockId →
    match s.unlockRequests id, s.flexibleUnlockRequests id with
    | some (owner, amount, _), none =>
        s.unlockTokenOwner id = some owner ∧ s.unlockTokenAmount id = amount
    | none, some (owner, amount, _, _) =>
        s.unlockTokenOwner id = some owner ∧ s.unlockTokenAmount id = amount
    | none, none =>
        s.unlockTokenOwner id = none ∧ s.unlockTokenAmount id = 0
    | some _, some _ => False

theorem unlockTokenLedgerConsistent_default :
    UnlockTokenLedgerConsistent (default : State) := by
  unfold UnlockTokenLedgerConsistent
  intro id hid
  simp [default] at hid

theorem unlockTokenLedgerConsistent_burnApxUSD
    (s : State) (caller : Address) (amount : Nat)
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (burnApxUSD s caller amount) := by
  intro id hid
  simpa [burnApxUSD] using h id hid

theorem unlockTokenLedgerConsistent_mintApxUSD
    (s : State) (to : Address) (amount : Nat)
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (mintApxUSD s to amount) := by
  intro id hid
  simpa [mintApxUSD] using h id hid

def UnlockTokenLedgerFrame (s s' : State) : Prop :=
  s'.nextUnlockId = s.nextUnlockId ∧
  s'.unlockRequests = s.unlockRequests ∧
  s'.flexibleUnlockRequests = s.flexibleUnlockRequests ∧
  s'.unlockTokenOwner = s.unlockTokenOwner ∧
  s'.unlockTokenAmount = s.unlockTokenAmount

theorem unlockTokenLedgerConsistent_of_frame (s s' : State)
    (hframe : UnlockTokenLedgerFrame s s')
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent s' := by
  rcases hframe with ⟨hnext, hstd, hflex, howner, hamount⟩
  intro id hid
  have hid' : id < s.nextUnlockId := by
    simpa [hnext] using hid
  simpa [hnext, hstd, hflex, howner, hamount] using h id hid'

theorem unlockTokenLedgerConsistent_createStandardUnlock
    (s : State) (owner : Address) (amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (createStandardUnlock s owner amount) := by
  intro id hid
  have hid_le : id ≤ s.nextUnlockId := by
    simp [createStandardUnlock] at hid
    omega
  rcases Nat.lt_or_eq_of_le hid_le with hid_old | rfl
  · have hne : id ≠ s.nextUnlockId := by omega
    simpa [createStandardUnlock, hne] using h id hid_old
  · have hflex : s.flexibleUnlockRequests s.nextUnlockId = none :=
      hregistry.1.2 s.nextUnlockId (Nat.le_refl _)
    simp [createStandardUnlock, hflex]

theorem unlockTokenLedgerConsistent_createFlexibleUnlock
    (s : State) (owner : Address) (amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (createFlexibleUnlock s owner amount) := by
  intro id hid
  have hid_le : id ≤ s.nextUnlockId := by
    simp [createFlexibleUnlock] at hid
    omega
  rcases Nat.lt_or_eq_of_le hid_le with hid_old | rfl
  · have hne : id ≠ s.nextUnlockId := by omega
    simpa [createFlexibleUnlock, hne] using h id hid_old
  · have hstd : s.unlockRequests s.nextUnlockId = none :=
      hregistry.1.1 s.nextUnlockId (Nat.le_refl _)
    simp [createFlexibleUnlock, hstd]

theorem unlockTokenLedgerConsistent_updateStandardUnlock
    (s : State) (id : Nat) (owner : Address) (oldAmount oldEnd addAmount : Nat)
    (hreq : s.unlockRequests id = some (owner, oldAmount, oldEnd))
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (updateStandardUnlock s id owner addAmount) := by
  intro i hi
  have hnext : (updateStandardUnlock s id owner addAmount).nextUnlockId = s.nextUnlockId := by
    simp [updateStandardUnlock, hreq]
  have hi' : i < s.nextUnlockId := by
    rw [hnext] at hi
    exact hi
  have hpre := h i hi'
  by_cases heq : i = id
  · subst i
    cases hflex : s.flexibleUnlockRequests id with
    | none =>
        have htoken : s.unlockTokenOwner id = some owner ∧
            s.unlockTokenAmount id = oldAmount := by
          simpa [hreq, hflex] using hpre
        simp [updateStandardUnlock, hreq, hflex, htoken.1]
    | some entry =>
        simp [hreq, hflex] at hpre
  · simpa [updateStandardUnlock, hreq, heq] using hpre

theorem unlockTokenLedgerConsistent_retireStandardUnlock
    (s : State) (id : Nat) (owner : Address) (amount cooldownEnd : Nat)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (retireStandardUnlock s id owner) := by
  intro i hi
  have hpre := h i hi
  by_cases heq : i = id
  · subst i
    cases hflex : s.flexibleUnlockRequests id with
    | none =>
        simp [retireStandardUnlock, burnUnlockNFT, hflex]
    | some entry =>
        simp [hreq, hflex] at hpre
  · simpa [retireStandardUnlock, burnUnlockNFT, heq] using hpre

theorem unlockTokenLedgerConsistent_retireFlexibleUnlock
    (s : State) (id : Nat)
    (hreq : s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd))
    (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (retireFlexibleUnlock s id) := by
  intro i hi
  have hpre := h i hi
  by_cases heq : i = id
  · subst i
    cases hstd : s.unlockRequests id with
    | none =>
        simp [retireFlexibleUnlock, burnUnlockNFT, hstd]
    | some entry =>
        simp [hstd, hreq] at hpre
  · simpa [retireFlexibleUnlock, burnUnlockNFT, heq] using hpre

theorem unlockTokenLedgerConsistent_requestUnlockStep
    (s : State) (caller : Address) (amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (hledger : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (requestUnlockStep s caller amount) := by
  let b := burnApxUSD s caller amount
  have hb : UnlockTokenLedgerConsistent b := by
    simpa [b] using unlockTokenLedgerConsistent_burnApxUSD s caller amount hledger
  have hregb : RegistryWellIndexed b := by
    simpa [b] using registryWellIndexed_burnApxUSD s caller amount hregistry
  change UnlockTokenLedgerConsistent (match b.unlockRequestId caller with
    | some id =>
      match b.unlockRequests id with
      | some (o, _, _) =>
        if o = caller then updateStandardUnlock b id caller amount
        else createStandardUnlock b caller amount
      | none => createStandardUnlock b caller amount
    | none => createStandardUnlock b caller amount)
  generalize hptr : b.unlockRequestId caller = ptr
  cases ptr with
  | none =>
      simpa using unlockTokenLedgerConsistent_createStandardUnlock b caller amount hregb hb
  | some id =>
      generalize hentry : b.unlockRequests id = entry
      cases entry with
      | none =>
          simpa [hentry] using
            unlockTokenLedgerConsistent_createStandardUnlock b caller amount hregb hb
      | some triple =>
          rcases triple with ⟨o, oldAmount, oldEnd⟩
          by_cases ho : o = caller
          · subst o
            have hentry' : b.unlockRequests id = some (caller, oldAmount, oldEnd) := hentry
            simpa [hentry] using
              unlockTokenLedgerConsistent_updateStandardUnlock b id caller oldAmount oldEnd
                amount hentry' hb
          · simpa [hentry, ho] using
              unlockTokenLedgerConsistent_createStandardUnlock b caller amount hregb hb

theorem unlockTokenLedgerConsistent_requestUnlock
    (s : State) (amount : Nat) (caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hledger : UnlockTokenLedgerConsistent s)
    (h_step : step s (Op.requestUnlock amount) caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  obtain ⟨-, -, hpost⟩ := requestUnlockStep_effect s amount caller s' h_step
  subst s'
  exact unlockTokenLedgerConsistent_requestUnlockStep s caller amount hregistry hledger

theorem unlockTokenLedgerConsistent_flexibleRequestUnlock
    (s : State) (amount : Nat) (caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hledger : UnlockTokenLedgerConsistent s)
    (h_step : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
  subst s'
  have hb := unlockTokenLedgerConsistent_burnApxUSD s caller amount hledger
  have hregb := registryWellIndexed_burnApxUSD s caller amount hregistry
  exact unlockTokenLedgerConsistent_createFlexibleUnlock
    (burnApxUSD s caller amount) caller amount hregb hb

theorem unlockTokenLedgerConsistent_claimUnlock
    (s : State) (id : Nat) (caller : Address) (s' : State)
    (hledger : UnlockTokenLedgerConsistent s)
    (h_step : step s (Op.claimUnlock id) caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  obtain ⟨owner, amount, cooldownEnd, hreq, _, _, _, hpost⟩ :=
    claimUnlockStep_effect s id caller s' h_step
  subst s'
  have hret := unlockTokenLedgerConsistent_retireStandardUnlock
    s id owner amount cooldownEnd hreq hledger
  exact unlockTokenLedgerConsistent_mintApxUSD
    (retireStandardUnlock s id owner) owner amount hret

theorem unlockTokenLedgerConsistent_flexibleClaimUnlock
    (s : State) (id : Nat) (caller : Address) (s' : State)
    (hledger : UnlockTokenLedgerConsistent s)
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, _, _, _, hpost⟩ :=
    flexibleClaimStep_effect s id caller s' h_step
  subst s'
  have hret := unlockTokenLedgerConsistent_retireFlexibleUnlock
    s id hreq hledger
  exact unlockTokenLedgerConsistent_mintApxUSD
    (retireFlexibleUnlock s id) owner
      (amount - amount * flexibleUnlockFee requestTime s.now / 10000) hret

theorem unlockTokenLedgerConsistent_pullVestedYield
    (s : State) (h : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (pullVestedYield s) := by
  apply unlockTokenLedgerConsistent_of_frame s (pullVestedYield s) ?_ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold pullVestedYield <;> dsimp only <;> split <;> rfl

theorem unlockTokenLedgerConsistent_vaultExitChain
    (s1 : State) (caller shares assets : Nat)
    (receiver : Address) (name : String) (evArgs : List Nat)
    (hregistry : RegistryWellIndexed s1)
    (hledger : UnlockTokenLedgerConsistent s1) :
    UnlockTokenLedgerConsistent (emitEvent (updateExchangeRate (createStandardUnlock
      { burnApyUSD s1 caller shares with
          vaultApxUSDBal := (burnApyUSD s1 caller shares).vaultApxUSDBal - assets }
      receiver assets)) name evArgs) := by
  let u : State := { burnApyUSD s1 caller shares with
      vaultApxUSDBal := (burnApyUSD s1 caller shares).vaultApxUSDBal - assets }
  have hu : UnlockTokenLedgerConsistent u := by
    intro id hid
    simpa [u, burnApyUSD] using hledger id hid
  have hregu : RegistryWellIndexed u := by
    dsimp [u]
    exact registryWellIndexed_of_frame s1 _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hregistry
  have hcreated : UnlockTokenLedgerConsistent (createStandardUnlock u receiver assets) :=
    unlockTokenLedgerConsistent_createStandardUnlock u receiver assets hregu hu
  have hframe : UnlockTokenLedgerFrame (createStandardUnlock u receiver assets)
      (emitEvent (updateExchangeRate (createStandardUnlock u receiver assets)) name evArgs) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [emitEvent, updateExchangeRate]
  have hfinal := unlockTokenLedgerConsistent_of_frame
    (createStandardUnlock u receiver assets)
    (emitEvent (updateExchangeRate (createStandardUnlock u receiver assets)) name evArgs)
    hframe hcreated
  simpa [u] using hfinal

theorem unlockTokenLedgerConsistent_withdraw
    (s : State) (assets : Nat) (receiver caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hledger : UnlockTokenLedgerConsistent s)
    (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  obtain ⟨-, -, -, hpost⟩ := withdrawStep_effect s assets receiver caller s' h_step
  subst s'
  exact unlockTokenLedgerConsistent_vaultExitChain
    (pullVestedYield s) caller
      (withdrawShares assets (computeExchangeRate (pullVestedYield s))) assets
      receiver "Withdraw"
      [caller, receiver, caller, assets,
        withdrawShares assets (computeExchangeRate (pullVestedYield s))]
      (registryWellIndexed_pullVestedYield s hregistry)
      (unlockTokenLedgerConsistent_pullVestedYield s hledger)

theorem unlockTokenLedgerConsistent_redeem
    (s : State) (shares : Nat) (receiver caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hledger : UnlockTokenLedgerConsistent s)
    (h_step : step s (Op.redeem shares receiver) caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  obtain ⟨-, -, -, hpost⟩ := redeemStep_effect s shares receiver caller s' h_step
  subst s'
  exact unlockTokenLedgerConsistent_vaultExitChain
    (pullVestedYield s) caller shares
      (redeemAssets shares (computeExchangeRate (pullVestedYield s))) receiver "Withdraw"
      [caller, receiver, caller,
        redeemAssets shares (computeExchangeRate (pullVestedYield s)), shares]
      (registryWellIndexed_pullVestedYield s hregistry)
      (unlockTokenLedgerConsistent_pullVestedYield s hledger)

inductive UnlockTokenLedgerCoveredOp : Op → Prop
  | requestUnlock (amount : Nat) : UnlockTokenLedgerCoveredOp (Op.requestUnlock amount)
  | claimUnlock (id : Nat) : UnlockTokenLedgerCoveredOp (Op.claimUnlock id)
  | withdraw (assets : Nat) (receiver : Address) :
      UnlockTokenLedgerCoveredOp (Op.withdraw assets receiver)
  | redeem (shares : Nat) (receiver : Address) :
      UnlockTokenLedgerCoveredOp (Op.redeem shares receiver)
  | flexibleRequestUnlock (amount : Nat) :
      UnlockTokenLedgerCoveredOp (Op.flexibleRequestUnlock amount)
  | flexibleClaimUnlock (id : Nat) :
      UnlockTokenLedgerCoveredOp (Op.flexibleClaimUnlock id)
  | frame {op : Op} (h : RegistryStaticOp op) : UnlockTokenLedgerCoveredOp op

theorem unlockTokenLedgerConsistent_covered_step
    (s s' : State) (op : Op) (caller : Address)
    (hregistry : RegistryWellIndexed s)
    (hop : UnlockTokenLedgerCoveredOp op)
    (hledger : UnlockTokenLedgerConsistent s)
    (hstep : step s op caller = some s') :
    UnlockTokenLedgerConsistent s' := by
  cases hop with
  | requestUnlock amount =>
      exact unlockTokenLedgerConsistent_requestUnlock s amount caller s'
        hregistry hledger hstep
  | claimUnlock id =>
      exact unlockTokenLedgerConsistent_claimUnlock s id caller s' hledger hstep
  | withdraw assets receiver =>
      exact unlockTokenLedgerConsistent_withdraw s assets receiver caller s'
        hregistry hledger hstep
  | redeem shares receiver =>
      exact unlockTokenLedgerConsistent_redeem s shares receiver caller s'
        hregistry hledger hstep
  | flexibleRequestUnlock amount =>
      exact unlockTokenLedgerConsistent_flexibleRequestUnlock s amount caller s'
        hregistry hledger hstep
  | flexibleClaimUnlock id =>
      exact unlockTokenLedgerConsistent_flexibleClaimUnlock s id caller s' hledger hstep
  | frame hframe =>
      cases op with
      | requestUnlock n => exact False.elim (hframe.1 n rfl)
      | claimUnlock n => exact False.elim (hframe.2.1 n rfl)
      | withdraw n r => exact False.elim (hframe.2.2.1 n r rfl)
      | redeem n r => exact False.elim (hframe.2.2.2.1 n r rfl)
      | flexibleRequestUnlock n => exact False.elim (hframe.2.2.2.2.1 n rfl)
      | flexibleClaimUnlock n => exact False.elim (hframe.2.2.2.2.2 n rfl)
      | _ =>
          simp only [step] at hstep
          (repeat' split at hstep) <;>
            first
              | cases Option.some.inj hstep
                exact unlockTokenLedgerConsistent_of_frame s _
                  ⟨rfl, rfl, rfl, rfl, rfl⟩ hledger
              | exact absurd hstep (by simp)

theorem unlockTokenLedgerCoveredOp_all (op : Op) :
    UnlockTokenLedgerCoveredOp op := by
  cases op with
  | requestUnlock amount => exact .requestUnlock amount
  | claimUnlock id => exact .claimUnlock id
  | withdraw assets receiver => exact .withdraw assets receiver
  | redeem shares receiver => exact .redeem shares receiver
  | flexibleRequestUnlock amount => exact .flexibleRequestUnlock amount
  | flexibleClaimUnlock id => exact .flexibleClaimUnlock id
  | depositUSDC amount => exact .frame (by simp [RegistryStaticOp])
  | mintApxUSD to amount => exact .frame (by simp [RegistryStaticOp])
  | lockApxUSD amount => exact .frame (by simp [RegistryStaticOp])
  | redeemApxUSD amount => exact .frame (by simp [RegistryStaticOp])
  | pause => exact .frame (by simp [RegistryStaticOp])
  | unpause => exact .frame (by simp [RegistryStaticOp])
  | addToWhitelist addr => exact .frame (by simp [RegistryStaticOp])
  | removeFromWhitelist addr => exact .frame (by simp [RegistryStaticOp])
  | addToDenylist addr => exact .frame (by simp [RegistryStaticOp])
  | removeFromDenylist addr => exact .frame (by simp [RegistryStaticOp])
  | setYieldRate bps => exact .frame (by simp [RegistryStaticOp])
  | creditYield amount => exact .frame (by simp [RegistryStaticOp])
  | voteBufferDeployment => exact .frame (by simp [RegistryStaticOp])
  | submitRFQRequest amount => exact .frame (by simp [RegistryStaticOp])
  | executeRFQRedemption user amount => exact .frame (by simp [RegistryStaticOp])
  | updateRedemptionValue newValue => exact .frame (by simp [RegistryStaticOp])
  | handleStressEvent amount => exact .frame (by simp [RegistryStaticOp])
  | catastrophicBackstop => exact .frame (by simp [RegistryStaticOp])
  | setVestPeriod p => exact .frame (by simp [RegistryStaticOp])
  | setApxUSDMarketPrice price => exact .frame (by simp [RegistryStaticOp])
  | withdrawReserve amount receiver => exact .frame (by simp [RegistryStaticOp])
  | poolRedeem amount receiver minOut => exact .frame (by simp [RegistryStaticOp])
  | tick dt => exact .frame (by simp [RegistryStaticOp])

theorem unlockTokenLedgerConsistent_step
    (s s' : State) (op : Op) (caller : Address)
    (hregistry : RegistryWellIndexed s)
    (hledger : UnlockTokenLedgerConsistent s)
    (hstep : step s op caller = some s') :
    UnlockTokenLedgerConsistent s' :=
  unlockTokenLedgerConsistent_covered_step s s' op caller hregistry
    (unlockTokenLedgerCoveredOp_all op) hledger hstep

theorem unlockTokenLedgerConsistent_trace (s : State) (σ : List (Op × Address))
    (hregistry : RegistryReach s)
    (hledger : UnlockTokenLedgerConsistent s) :
    UnlockTokenLedgerConsistent (execTrace s σ) := by
  induction σ generalizing s with
  | nil => exact hledger
  | cons p σ ih =>
      obtain ⟨op, caller⟩ := p
      simp only [execTrace]
      cases hstep : step s op caller with
      | none => exact ih s hregistry hledger
      | some s' =>
          have hregistry' : RegistryReach s' := RegistryReach.next hregistry hstep
          exact ih s' hregistry'
            (unlockTokenLedgerConsistent_step s s' op caller
              (registryWellIndexed_reachable s hregistry) hledger hstep)

/-! ## The missing USDC ledger, stated without inventing a State field

The model has `usdcBal` and `usdcReserve`, but no finite holder support and no
USDC total-supply field. The following relation is therefore parameterized by
an externally supplied holder list and total supply. It is an accounting
interface, not a reachable-state invariant of the current `State`. The two
arithmetic lemmas below show exactly what a `depositUSDC` debit and a reserve
payout must preserve once the missing support and total-supply facts are
provided. -/

def UsdcLedgerConsistent (s : State) (holders : List Address) (totalSupply : Nat) : Prop :=
  holders.Pairwise (· ≠ ·) ∧
  (∀ a, s.usdcBal a ≠ 0 → a ∈ holders) ∧
  sumOver s.usdcBal holders + s.usdcReserve = totalSupply

theorem usdcLedgerConsistent_default :
    UsdcLedgerConsistent (default : State) [] 0 := by
  simp [UsdcLedgerConsistent, default, sumOver]

theorem usdcLedgerConsistent_debit_to_reserve
    (s s' : State) (holders : List Address) (totalSupply : Nat)
    (hledger : UsdcLedgerConsistent s holders totalSupply)
    (caller : Address) (amount : Nat)
    (hmem : caller ∈ holders) (hle : amount ≤ s.usdcBal caller)
    (hbal : s'.usdcBal = fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a)
    (hreserve : s'.usdcReserve = s.usdcReserve + amount) :
    UsdcLedgerConsistent s' holders totalSupply := by
  obtain ⟨hnd, hcov, hsum⟩ := hledger
  refine ⟨hnd, ?_, ?_⟩
  · intro a ha
    rw [hbal] at ha
    by_cases hac : a = caller
    · simpa [hac] using hmem
    · apply hcov a
      intro hzero
      apply ha
      simp [hac, hzero]
  · rw [hbal, hreserve]
    have hdelta := sumOver_update_sub_mem s.usdcBal caller amount hle hnd hmem
    omega

theorem usdcLedgerConsistent_reserve_payout
    (s s' : State) (holders : List Address) (totalSupply : Nat)
    (hledger : UsdcLedgerConsistent s holders totalSupply)
    (receiver : Address) (amount : Nat)
    (hmem : receiver ∈ holders) (hle : amount ≤ s.usdcReserve)
    (hbal : s'.usdcBal = fun a => if a = receiver then s.usdcBal a + amount else s.usdcBal a)
    (hreserve : s'.usdcReserve = s.usdcReserve - amount) :
    UsdcLedgerConsistent s' holders totalSupply := by
  obtain ⟨hnd, hcov, hsum⟩ := hledger
  refine ⟨hnd, ?_, ?_⟩
  · intro a ha
    rw [hbal] at ha
    by_cases hac : a = receiver
    · simpa [hac] using hmem
    · apply hcov a
      intro hzero
      apply ha
      simp [hac, hzero]
  · rw [hbal, hreserve]
    have hdelta := sumOver_update_add_mem s.usdcBal receiver amount hnd hmem
    omega

/-- A USDC frame changes neither the finite holder balances nor the reserve.
This is deliberately a projection boundary: it can be discharged by a public
step-effect theorem without unfolding unrelated State fields. -/
def UsdcLedgerFrame (s s' : State) : Prop :=
  s'.usdcBal = s.usdcBal ∧ s'.usdcReserve = s.usdcReserve

theorem usdcLedgerConsistent_of_frame
    (s s' : State) (holders : List Address) (totalSupply : Nat)
    (hledger : UsdcLedgerConsistent s holders totalSupply)
    (hframe : UsdcLedgerFrame s s') :
    UsdcLedgerConsistent s' holders totalSupply := by
  rcases hledger with ⟨hnd, hcov, hsum⟩
  rcases hframe with ⟨hbal, hreserve⟩
  refine ⟨hnd, ?_, ?_⟩
  · intro a ha
    rw [hbal] at ha
    exact hcov a ha
  · rw [hbal, hreserve]
    exact hsum

/-- The USDC accounting cases that a dispatcher or SPECA effect theorem must
expose. This predicate intentionally does not mention `Op`: the current State
does not contain a total-supply field or finite support, so the connection from
a concrete public operation to one of these effects remains an explicit
implementation/specification obligation. -/
def UsdcLedgerEffect (s s' : State) (holders : List Address) : Prop :=
  (∃ caller amount,
    caller ∈ holders ∧
    amount ≤ s.usdcBal caller ∧
    s'.usdcBal = fun a => if a = caller then s.usdcBal a - amount else s.usdcBal a ∧
    s'.usdcReserve = s.usdcReserve + amount) ∨
  (∃ receiver amount,
    receiver ∈ holders ∧
    amount ≤ s.usdcReserve ∧
    s'.usdcBal = fun a => if a = receiver then s.usdcBal a + amount else s.usdcBal a ∧
    s'.usdcReserve = s.usdcReserve - amount) ∨
  UsdcLedgerFrame s s'

theorem usdcLedgerEffect_depositUSDC
    (s : State) (amount : Nat) (caller : Address) (s' : State)
    (holders : List Address) (hmem : caller ∈ holders)
    (hstep : step s (Op.depositUSDC amount) caller = some s') :
    UsdcLedgerEffect s s' holders := by
  obtain ⟨-, -, -, hle, hpost⟩ := depositUSDCStep_effect s amount caller s' hstep
  left
  refine ⟨caller, amount, hmem, hle, ?_, ?_⟩
  · rw [hpost]
    simp [emitEvent, mintApxUSD]
  · rw [hpost]
    simp [emitEvent, mintApxUSD]

theorem usdcLedgerEffect_mintApxUSD
    (s : State) (to : Address) (amount : Nat) (caller : Address) (s' : State)
    (holders : List Address) (hmem : caller ∈ holders)
    (hstep : step s (Op.mintApxUSD to amount) caller = some s') :
    UsdcLedgerEffect s s' holders := by
  obtain ⟨-, -, -, -, -, hle, hpost⟩ :=
    mintApxUSDStep_effect s to amount caller s' hstep
  left
  refine ⟨caller, amount, hmem, hle, ?_, ?_⟩
  · rw [hpost]
    simp [emitEvent, mintApxUSD]
  · rw [hpost]
    simp [emitEvent, mintApxUSD]

theorem usdcLedgerConsistent_effect
    (s s' : State) (holders : List Address) (totalSupply : Nat)
    (hledger : UsdcLedgerConsistent s holders totalSupply)
    (heffect : UsdcLedgerEffect s s' holders) :
    UsdcLedgerConsistent s' holders totalSupply := by
  rcases heffect with hdebit | hpayout | hframe
  · rcases hdebit with ⟨caller, amount, hmem, hle, hbal, hreserve⟩
    exact usdcLedgerConsistent_debit_to_reserve s s' holders totalSupply
      hledger caller amount hmem hle hbal hreserve
  · rcases hpayout with ⟨receiver, amount, hmem, hle, hbal, hreserve⟩
    exact usdcLedgerConsistent_reserve_payout s s' holders totalSupply
      hledger receiver amount hmem hle hbal hreserve
  · exact usdcLedgerConsistent_of_frame s s' holders totalSupply hledger hframe

/-- Pulling the live vest adds exactly the newly realized amount to custody;
the circulating and pending obligation ledger is framed. -/
theorem apxUSDFlow_pullVestedYield (s : State) :
    apxUSDFlow (pullVestedYield s) =
      apxUSDFlow s + vestedAmount s s.now := by
  have hvault : (pullVestedYield s).vaultApxUSDBal =
      s.vaultApxUSDBal + vestedAmount s s.now :=
    pullVestedYield_moves_exactly_vested s
  have hout : outstandingApxUSD (pullVestedYield s) = outstandingApxUSD s := by
    apply outstandingApxUSD_of_projections_eq
    · unfold pullVestedYield
      dsimp only
      split <;> rfl
    · unfold pullVestedYield
      dsimp only
      split <;> rfl
    · unfold pullVestedYield
      dsimp only
      split <;> rfl
    · unfold pullVestedYield
      dsimp only
      split <;> rfl
  unfold apxUSDFlow
  rw [hvault, hout]
  omega

theorem standardUnlockTotal_createStandardUnlock (s : State) (owner : Address)
    (amount : Nat) :
    standardUnlockTotal (createStandardUnlock s owner amount) =
      standardUnlockTotal s + amount := by
  unfold standardUnlockTotal
  rw [show (createStandardUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 by rfl,
    List.range_succ, List.map_append, List.sum_append]
  have hsame : ((List.range s.nextUnlockId).map (fun i =>
      match (createStandardUnlock s owner amount).unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0)) =
      ((List.range s.nextUnlockId).map (fun i =>
      match s.unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0)) := by
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt (List.mem_range.mp hi)
    simp [createStandardUnlock, hne]
  rw [hsame]
  simp [createStandardUnlock]

theorem flexibleUnlockTotal_createFlexibleUnlock (s : State) (owner : Address)
    (amount : Nat) :
    flexibleUnlockTotal (createFlexibleUnlock s owner amount) =
      flexibleUnlockTotal s + amount := by
  unfold flexibleUnlockTotal
  rw [show (createFlexibleUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 by rfl,
    List.range_succ, List.map_append, List.sum_append]
  have hsame : ((List.range s.nextUnlockId).map (fun i =>
      match (createFlexibleUnlock s owner amount).flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0)) =
      ((List.range s.nextUnlockId).map (fun i =>
      match s.flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0)) := by
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ s.nextUnlockId := Nat.ne_of_lt (List.mem_range.mp hi)
    simp [createFlexibleUnlock, hne]
  rw [hsame]
  simp [createFlexibleUnlock]

theorem standardUnlockTotal_createFlexibleUnlock (s : State) (owner : Address)
    (amount : Nat) (h_unalloc : s.unlockRequests s.nextUnlockId = none) :
    standardUnlockTotal (createFlexibleUnlock s owner amount) =
      standardUnlockTotal s := by
  unfold standardUnlockTotal
  rw [show (createFlexibleUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 by rfl,
    List.range_succ, List.map_append, List.sum_append]
  have hsame : ((List.range s.nextUnlockId).map (fun i =>
      match (createFlexibleUnlock s owner amount).unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0)) =
      ((List.range s.nextUnlockId).map (fun i =>
      match s.unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0)) := by
    apply List.map_congr_left
    intro i hi
    simp [createFlexibleUnlock]
  rw [hsame]
  simp [createFlexibleUnlock, h_unalloc]

theorem standardUnlockTotal_updateStandardUnlock (s : State) (id : Nat)
    (owner : Address) (oldAmount oldEnd addAmount : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, oldAmount, oldEnd)) :
    standardUnlockTotal (updateStandardUnlock s id owner addAmount) =
      standardUnlockTotal s + addAmount := by
  unfold standardUnlockTotal
  have hnext : (updateStandardUnlock s id owner addAmount).nextUnlockId = s.nextUnlockId := by
    simp [updateStandardUnlock, hreq]
  rw [hnext]
  have htarget : (fun i =>
      match (updateStandardUnlock s id owner addAmount).unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0) id =
      (fun i => match s.unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0) id + addAmount := by
    simp [updateStandardUnlock, hreq]
  apply sum_range_replace s.nextUnlockId id addAmount _ _ hid htarget
  intro j hj hne
  simp [updateStandardUnlock, hreq, hne]

theorem flexibleUnlockTotal_retireFlexibleUnlock (s : State) (id : Nat)
    (owner : Address) (amount requestTime cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd)) :
    flexibleUnlockTotal (retireFlexibleUnlock s id) + amount =
      flexibleUnlockTotal s := by
  unfold flexibleUnlockTotal
  have hnext : (retireFlexibleUnlock s id).nextUnlockId = s.nextUnlockId := by
    simp [retireFlexibleUnlock, burnUnlockNFT]
  rw [hnext]
  have htarget : (fun i => match s.flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0) id =
      (fun i => match (retireFlexibleUnlock s id).flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0) id + amount := by
    simp [retireFlexibleUnlock, burnUnlockNFT, hreq]
  have hother : ∀ j, j < s.nextUnlockId → j ≠ id →
      (fun i => match s.flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0) j =
      (fun i => match (retireFlexibleUnlock s id).flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0) j := by
    intro j hj hne
    simp [retireFlexibleUnlock, burnUnlockNFT, hne]
  exact (sum_range_replace s.nextUnlockId id amount _ _ hid htarget hother).symm

theorem standardUnlockTotal_retireStandardUnlock (s : State) (id : Nat)
    (owner : Address) (amount cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd)) :
    standardUnlockTotal (retireStandardUnlock s id owner) + amount =
      standardUnlockTotal s := by
  unfold standardUnlockTotal
  have hnext : (retireStandardUnlock s id owner).nextUnlockId = s.nextUnlockId := by
    simp [retireStandardUnlock, burnUnlockNFT]
  rw [hnext]
  have htarget : (fun i => match s.unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0) id =
      (fun i => match (retireStandardUnlock s id owner).unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0) id + amount := by
    simp [retireStandardUnlock, burnUnlockNFT, hreq]
  have hother : ∀ j, j < s.nextUnlockId → j ≠ id →
      (fun i => match s.unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0) j =
      (fun i => match (retireStandardUnlock s id owner).unlockRequests i with
      | some (_, amount, _) => amount
      | none => 0) j := by
    intro j hj hne
    simp [retireStandardUnlock, burnUnlockNFT, hne]
  exact (sum_range_replace s.nextUnlockId id amount _ _ hid htarget hother).symm

theorem flexibleUnlockTotal_createStandardUnlock (s : State) (owner : Address)
    (amount : Nat) (h_unalloc : s.flexibleUnlockRequests s.nextUnlockId = none) :
    flexibleUnlockTotal (createStandardUnlock s owner amount) =
      flexibleUnlockTotal s := by
  unfold flexibleUnlockTotal
  rw [show (createStandardUnlock s owner amount).nextUnlockId = s.nextUnlockId + 1 by rfl,
    List.range_succ, List.map_append, List.sum_append]
  have hsame : ((List.range s.nextUnlockId).map (fun i =>
      match (createStandardUnlock s owner amount).flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0)) =
      ((List.range s.nextUnlockId).map (fun i =>
      match s.flexibleUnlockRequests i with
      | some (_, amount, _, _) => amount
      | none => 0)) := by
    apply List.map_congr_left
    intro i hi
    simp [createStandardUnlock]
  rw [hsame]
  simp [createStandardUnlock, h_unalloc]

theorem outstandingApxUSD_createStandardUnlock (s : State) (owner : Address)
    (amount : Nat) (hregistry : RegistryWellIndexed s) :
    outstandingApxUSD (createStandardUnlock s owner amount) =
      outstandingApxUSD s + amount := by
  have hb : RegistryBounded s := hregistry.1
  have hflex := flexibleUnlockTotal_createStandardUnlock s owner amount
    (hb.2 _ (Nat.le_refl _))
  unfold outstandingApxUSD pendingApxUSD
  rw [standardUnlockTotal_createStandardUnlock, hflex]
  simp [createStandardUnlock]
  omega

/-! ### Request-level obligation conservation

The pointer and registry assumptions are explicit here. Without boundedness, a
stale pointer could update a record at or above `nextUnlockId`, which the finite
aggregate would not see; proving that case would silently overstate the model.
-/

theorem standardUnlockTotal_requestUnlockStep (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s) :
    standardUnlockTotal (requestUnlockStep s caller amount) =
      standardUnlockTotal s + amount := by
  have hb : RegistryBounded (burnApxUSD s caller amount) :=
    (registryWellIndexed_burnApxUSD s caller amount hregistry).1
  have hburn : standardUnlockTotal (burnApxUSD s caller amount) =
      standardUnlockTotal s := by rfl
  unfold requestUnlockStep
  split
  · rename_i id hptr
    split
    · rename_i owner oldAmount oldEnd hentry
      by_cases howner : owner = caller
      · rw [if_pos howner]
        subst owner
        have hid : id < (burnApxUSD s caller amount).nextUnlockId := by
          by_cases hlt : id < (burnApxUSD s caller amount).nextUnlockId
          · exact hlt
          · have hge : (burnApxUSD s caller amount).nextUnlockId ≤ id := Nat.le_of_not_gt hlt
            rw [hb.1 id hge] at hentry
            cases hentry
        have hupdate := standardUnlockTotal_updateStandardUnlock
          (burnApxUSD s caller amount) id caller oldAmount oldEnd amount hid hentry
        rw [hburn] at hupdate
        exact hupdate
      · rw [if_neg howner]
        have hcreate := standardUnlockTotal_createStandardUnlock
          (burnApxUSD s caller amount) caller amount
        rw [hburn] at hcreate
        exact hcreate
    · have hcreate := standardUnlockTotal_createStandardUnlock
        (burnApxUSD s caller amount) caller amount
      rw [hburn] at hcreate
      exact hcreate
  · have hcreate := standardUnlockTotal_createStandardUnlock
      (burnApxUSD s caller amount) caller amount
    rw [hburn] at hcreate
    exact hcreate

theorem flexibleUnlockTotal_requestUnlockStep (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s) :
    flexibleUnlockTotal (requestUnlockStep s caller amount) =
      flexibleUnlockTotal s := by
  have hb : RegistryBounded (burnApxUSD s caller amount) :=
    (registryWellIndexed_burnApxUSD s caller amount hregistry).1
  unfold requestUnlockStep
  split
  · rename_i id hptr
    split
    · rename_i owner oldAmount oldEnd hentry
      by_cases howner : owner = caller
      · rw [if_pos howner]
        have hburnflex : flexibleUnlockTotal (burnApxUSD s caller amount) =
            flexibleUnlockTotal s := by rfl
        unfold flexibleUnlockTotal
        have hnext : (updateStandardUnlock (burnApxUSD s caller amount)
            id caller amount).nextUnlockId =
            (burnApxUSD s caller amount).nextUnlockId := by
          simp [updateStandardUnlock, hentry]
        have hflex : (updateStandardUnlock (burnApxUSD s caller amount)
            id caller amount).flexibleUnlockRequests =
            (burnApxUSD s caller amount).flexibleUnlockRequests := by
          simp [updateStandardUnlock, hentry]
        rw [hnext, hflex]
        simpa [flexibleUnlockTotal] using hburnflex
      · rw [if_neg howner]
        have h_unalloc : (burnApxUSD s caller amount).flexibleUnlockRequests
            (burnApxUSD s caller amount).nextUnlockId = none :=
          hb.2 _ (Nat.le_refl _)
        exact flexibleUnlockTotal_createStandardUnlock
          (burnApxUSD s caller amount) caller amount h_unalloc
    · have h_unalloc : (burnApxUSD s caller amount).flexibleUnlockRequests
          (burnApxUSD s caller amount).nextUnlockId = none :=
        hb.2 _ (Nat.le_refl _)
      exact flexibleUnlockTotal_createStandardUnlock
        (burnApxUSD s caller amount) caller amount h_unalloc
  · have h_unalloc : (burnApxUSD s caller amount).flexibleUnlockRequests
        (burnApxUSD s caller amount).nextUnlockId = none :=
      hb.2 _ (Nat.le_refl _)
    exact flexibleUnlockTotal_createStandardUnlock
      (burnApxUSD s caller amount) caller amount h_unalloc

/-- A successful standard request moves face value from circulating apxUSD into
the standard registry: the combined circulating-plus-pending obligation is
unchanged. The supply-underflow premise is separate from the registry premise
because `burnApxUSD` uses truncated natural subtraction. -/
theorem outstandingApxUSD_requestUnlockStep (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD) :
    outstandingApxUSD (requestUnlockStep s caller amount) =
      outstandingApxUSD s := by
  unfold outstandingApxUSD pendingApxUSD
  rw [requestUnlockStep_totalSupply_apxUSD,
    standardUnlockTotal_requestUnlockStep s caller amount hregistry,
    flexibleUnlockTotal_requestUnlockStep s caller amount hregistry]
  omega

theorem outstandingApxUSD_requestUnlock (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD)
    (h_step : step s (Op.requestUnlock amount) caller = some s') :
    outstandingApxUSD s' = outstandingApxUSD s := by
  obtain ⟨-, -, hpost⟩ := requestUnlockStep_effect s amount caller s' h_step
  subst s'
  exact outstandingApxUSD_requestUnlockStep s caller amount hregistry hsupply

theorem standardUnlockTotal_flexibleRequestUnlockStep (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s) :
    standardUnlockTotal (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) =
      standardUnlockTotal s := by
  have hb : RegistryBounded (burnApxUSD s caller amount) :=
    (registryWellIndexed_burnApxUSD s caller amount hregistry).1
  have h_unalloc : (burnApxUSD s caller amount).unlockRequests
      (burnApxUSD s caller amount).nextUnlockId = none :=
    hb.1 _ (Nat.le_refl _)
  have hcreate := standardUnlockTotal_createFlexibleUnlock
    (burnApxUSD s caller amount) caller amount h_unalloc
  have hburn : standardUnlockTotal (burnApxUSD s caller amount) =
      standardUnlockTotal s := by rfl
  rw [hburn] at hcreate
  exact hcreate

theorem outstandingApxUSD_flexibleRequestUnlock (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD) :
    outstandingApxUSD (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) =
      outstandingApxUSD s := by
  have hstd := standardUnlockTotal_flexibleRequestUnlockStep s caller amount hregistry
  have hflex := flexibleUnlockTotal_createFlexibleUnlock
    (burnApxUSD s caller amount) caller amount
  have hburnflex : flexibleUnlockTotal (burnApxUSD s caller amount) =
      flexibleUnlockTotal s := by rfl
  have hpostSupply : (createFlexibleUnlock (burnApxUSD s caller amount)
      caller amount).totalSupply_apxUSD = s.totalSupply_apxUSD - amount := by rfl
  have hpostStd : standardUnlockTotal
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) =
      standardUnlockTotal s := hstd
  have hpostFlex : flexibleUnlockTotal
      (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) =
      flexibleUnlockTotal s + amount := by
    rw [hflex, hburnflex]
  unfold outstandingApxUSD pendingApxUSD
  rw [hpostSupply, hpostStd, hpostFlex]
  omega

theorem outstandingApxUSD_flexibleRequestUnlock_step (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD)
    (h_step : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    outstandingApxUSD s' = outstandingApxUSD s := by
  obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
  subst s'
  exact outstandingApxUSD_flexibleRequestUnlock s caller amount hregistry hsupply

theorem flexibleUnlockTotal_retireStandardUnlock (s : State) (id : Nat)
    (owner : Address) :
    flexibleUnlockTotal (retireStandardUnlock s id owner) =
      flexibleUnlockTotal s := by
  unfold flexibleUnlockTotal
  simp [retireStandardUnlock, burnUnlockNFT]

/-- A successful standard claim moves the face amount back from the standard
registry into circulating apxUSD, preserving the combined obligation. -/
theorem outstandingApxUSD_claimUnlock (s : State) (id : Nat)
    (owner : Address) (amount cooldownEnd : Nat) (caller : Address) (s' : State)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_step : step s (Op.claimUnlock id) caller = some s') :
    outstandingApxUSD s' = outstandingApxUSD s := by
  obtain ⟨recordedOwner, recordedAmount, recordedCooldown, hentry, _, _, _, hpost⟩ :=
    claimUnlockStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl⟩ := hentry
  subst s'
  have hstd := standardUnlockTotal_retireStandardUnlock s id owner amount cooldownEnd hid hreq
  have hflex := flexibleUnlockTotal_retireStandardUnlock s id owner
  have hstdmint : standardUnlockTotal
      (mintApxUSD (retireStandardUnlock s id owner) owner amount) =
      standardUnlockTotal (retireStandardUnlock s id owner) := by rfl
  have hflexmint : flexibleUnlockTotal
      (mintApxUSD (retireStandardUnlock s id owner) owner amount) =
      flexibleUnlockTotal (retireStandardUnlock s id owner) := by rfl
  have hsupply : (mintApxUSD (retireStandardUnlock s id owner) owner amount).totalSupply_apxUSD =
      s.totalSupply_apxUSD + amount := by rfl
  unfold outstandingApxUSD pendingApxUSD
  rw [hsupply, hstdmint, hflexmint, hflex]
  omega

/-- A successful flexible claim preserves the outstanding face obligation up
to the explicit fee. The theorem records the fee as a sink because the current
`State` has no fee-wallet balance; it does not pretend that the fee is still
held by the protocol. -/
theorem outstandingApxUSD_flexibleClaimUnlock (s : State) (id : Nat)
    (owner : Address) (amount requestTime cooldownEnd : Nat) (caller : Address) (s' : State)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd))
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s') :
    outstandingApxUSD s' + amount * flexibleUnlockFee requestTime s.now / 10000 =
      outstandingApxUSD s := by
  obtain ⟨recordedOwner, recordedAmount, recordedRequestTime, recordedCooldownEnd,
    hentry, _, _, _, hpost⟩ := flexibleClaimStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hentry
  subst s'
  let fee := amount * flexibleUnlockFee requestTime s.now / 10000
  have hfee : fee ≤ amount := by
    exact flexibleClaimFee_le_amount amount requestTime s.now
  have hflex := flexibleUnlockTotal_retireFlexibleUnlock
    s id owner amount requestTime cooldownEnd hid hreq
  have hstd : standardUnlockTotal (retireFlexibleUnlock s id) =
      standardUnlockTotal s := by rfl
  have hstdmint : standardUnlockTotal
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)) =
      standardUnlockTotal (retireFlexibleUnlock s id) := by rfl
  have hflexmint : flexibleUnlockTotal
      (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)) =
      flexibleUnlockTotal (retireFlexibleUnlock s id) := by rfl
  have hsupply : (mintApxUSD (retireFlexibleUnlock s id) owner (amount - fee)).totalSupply_apxUSD =
      s.totalSupply_apxUSD + (amount - fee) := by rfl
  unfold outstandingApxUSD pendingApxUSD
  rw [hsupply, hstdmint, hflexmint, hstd]
  dsimp [fee] at hfee hflex ⊢
  omega

/-- Standard requests only move value between circulating supply and the
pending registry, so the internal apxUSD flow is unchanged. -/
theorem apxUSDFlow_requestUnlockStep (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD) :
    apxUSDFlow (requestUnlockStep s caller amount) = apxUSDFlow s := by
  have hassets : (requestUnlockStep s caller amount).vaultApxUSDBal =
      s.vaultApxUSDBal := requestUnlockStep_vaultApxUSDBal s caller amount
  unfold apxUSDFlow
  rw [hassets, outstandingApxUSD_requestUnlockStep s caller amount hregistry hsupply]

/-- The public standard-request boundary is the same flow identity. -/
theorem apxUSDFlow_requestUnlock (s : State) (amount : Nat) (caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD)
    (h_step : step s (Op.requestUnlock amount) caller = some s') :
    apxUSDFlow s' = apxUSDFlow s := by
  obtain ⟨-, -, hpost⟩ := requestUnlockStep_effect s amount caller s' h_step
  subst s'
  exact apxUSDFlow_requestUnlockStep s caller amount hregistry hsupply

/-- Flexible requests have the same internal flow identity. -/
theorem apxUSDFlow_flexibleRequestUnlock (s : State) (caller amount : Nat)
    (hregistry : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD) :
    apxUSDFlow (createFlexibleUnlock (burnApxUSD s caller amount) caller amount) =
      apxUSDFlow s := by
  have hassets : (createFlexibleUnlock (burnApxUSD s caller amount)
      caller amount).vaultApxUSDBal = s.vaultApxUSDBal := by rfl
  unfold apxUSDFlow
  rw [hassets, outstandingApxUSD_flexibleRequestUnlock s caller amount hregistry hsupply]

/-- Standard settlement transfers a pending face amount into circulating
apxUSD without changing the internal flow. -/
theorem apxUSDFlow_claimUnlock (s : State) (id : Nat)
    (owner : Address) (amount cooldownEnd : Nat) (caller : Address) (s' : State)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd))
    (h_step : step s (Op.claimUnlock id) caller = some s') :
    apxUSDFlow s' = apxUSDFlow s := by
  obtain ⟨recordedOwner, recordedAmount, recordedCooldown, hentry, _, _, _, hpost⟩ :=
    claimUnlockStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl⟩ := hentry
  subst s'
  have hassets : (mintApxUSD (retireStandardUnlock s id owner) owner amount).vaultApxUSDBal =
      s.vaultApxUSDBal := by rfl
  have hout := outstandingApxUSD_claimUnlock s id owner amount cooldownEnd caller
    (mintApxUSD (retireStandardUnlock s id owner) owner amount) hid hreq h_step
  unfold apxUSDFlow
  rw [hassets]
  omega

/-- Flexible settlement exposes the fee as the only decrease in the internal
flow, because the current model has no fee-wallet custody field. -/
theorem apxUSDFlow_flexibleClaimUnlock (s : State) (id : Nat)
    (owner : Address) (amount requestTime cooldownEnd : Nat) (caller : Address) (s' : State)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd))
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s') :
    apxUSDFlow s' + amount * flexibleUnlockFee requestTime s.now / 10000 =
      apxUSDFlow s := by
  obtain ⟨recordedOwner, recordedAmount, recordedRequestTime, recordedCooldownEnd,
    hentry, _, _, _, hpost⟩ := flexibleClaimStep_effect s id caller s' h_step
  rw [hreq] at hentry
  simp only [Option.some.injEq, Prod.mk.injEq] at hentry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hentry
  subst s'
  have hassets : (mintApxUSD (retireFlexibleUnlock s id) owner
      (amount - amount * flexibleUnlockFee requestTime s.now / 10000)).vaultApxUSDBal =
      s.vaultApxUSDBal := by rfl
  have hout := outstandingApxUSD_flexibleClaimUnlock s id owner amount requestTime
    cooldownEnd caller
    (mintApxUSD (retireFlexibleUnlock s id) owner
      (amount - amount * flexibleUnlockFee requestTime s.now / 10000)) hid hreq h_step
  unfold apxUSDFlow
  rw [hassets]
  omega

/-- Generic vault-exit flow identity at the state where the live vest has
already been pulled. The custody debit and the newly created standard claim
cancel exactly; the caller's share burn is an apyUSD operation and does not
alter this apxUSD flow. -/
theorem apxUSDFlow_vaultWithdrawPost (p : State) (assets shares : Nat)
    (receiver caller : Address) (name : String) (evArgs : List Nat)
    (hregistry : RegistryWellIndexed p)
    (hassets : assets ≤ p.vaultApxUSDBal) :
    apxUSDFlow (emitEvent (updateExchangeRate (createStandardUnlock
      { burnApyUSD p caller shares with
          vaultApxUSDBal := (burnApyUSD p caller shares).vaultApxUSDBal - assets }
      receiver assets)) name evArgs) = apxUSDFlow p := by
  let u : State := { burnApyUSD p caller shares with
      vaultApxUSDBal := (burnApyUSD p caller shares).vaultApxUSDBal - assets }
  have hu : RegistryWellIndexed u := by
    dsimp [u]
    exact registryWellIndexed_of_frame p _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hregistry
  have hbase : outstandingApxUSD u = outstandingApxUSD p := by rfl
  have hcreated : outstandingApxUSD (createStandardUnlock u receiver assets) =
      outstandingApxUSD p + assets := by
    rw [outstandingApxUSD_createStandardUnlock u receiver assets hu, hbase]
  have hvault : (emitEvent (updateExchangeRate (createStandardUnlock u receiver assets))
      name evArgs).vaultApxUSDBal = p.vaultApxUSDBal - assets := by
    simp [u, emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hout : outstandingApxUSD
      (emitEvent (updateExchangeRate (createStandardUnlock u receiver assets)) name evArgs) =
      outstandingApxUSD p + assets := by
    have hframe : outstandingApxUSD
        (emitEvent (updateExchangeRate (createStandardUnlock u receiver assets)) name evArgs) =
        outstandingApxUSD (createStandardUnlock u receiver assets) := by
      apply outstandingApxUSD_of_projections_eq
      · simp [emitEvent, updateExchangeRate]
      · simp [emitEvent, updateExchangeRate]
      · simp [emitEvent, updateExchangeRate]
      · simp [emitEvent, updateExchangeRate]
    rw [hframe]
    exact hcreated
  unfold apxUSDFlow
  rw [hvault, hout]
  omega

/-- A successful `withdraw` preserves the custody flow measured immediately
after the step's mandatory vest pull. The difference between that state and
the pre-state is the separately modeled vested-yield inflow. -/
theorem apxUSDFlow_withdraw (s : State) (assets : Nat)
    (receiver caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    apxUSDFlow s' = apxUSDFlow (pullVestedYield s) := by
  obtain ⟨-, -, hassets, hpost⟩ := withdrawStep_effect s assets receiver caller s' h_step
  subst s'
  exact apxUSDFlow_vaultWithdrawPost (pullVestedYield s) assets
    (withdrawShares assets (computeExchangeRate (pullVestedYield s)))
    receiver caller "Withdraw"
    [caller, receiver, caller, assets,
      withdrawShares assets (computeExchangeRate (pullVestedYield s))]
    (registryWellIndexed_pullVestedYield s hregistry) hassets

/-- The share-denominated `redeem` has the same custody-flow boundary. -/
theorem apxUSDFlow_redeem (s : State) (shares : Nat)
    (receiver caller : Address) (s' : State)
    (hregistry : RegistryWellIndexed s)
    (h_step : step s (Op.redeem shares receiver) caller = some s') :
    apxUSDFlow s' = apxUSDFlow (pullVestedYield s) := by
  obtain ⟨-, -, hassets, hpost⟩ := redeemStep_effect s shares receiver caller s' h_step
  subst s'
  exact apxUSDFlow_vaultWithdrawPost (pullVestedYield s)
    (redeemAssets shares (computeExchangeRate (pullVestedYield s))) shares
    receiver caller "Withdraw"
    [caller, receiver, caller,
      redeemAssets shares (computeExchangeRate (pullVestedYield s)), shares]
    (registryWellIndexed_pullVestedYield s hregistry) hassets

/-! ## Internal apxUSD flow traces

The next trace layer deliberately has a narrow alphabet. It covers the two
unlock channels and time passing, but not vault exits: a vault exit first
pulls live vesting yield, so its pre-state delta is an external inflow rather
than a conservation-free internal transfer. Flexible-claim fees are recorded
in a separate accumulator because the current `State` has no fee-wallet
balance. This is therefore an internal obligation-flow theorem, not a
protocol-wide asset-conservation theorem. -/

def apxUSDFlowStepFee (s : State) (p : Op × Address) : Nat :=
  match p.1 with
  | Op.flexibleClaimUnlock id =>
      match s.flexibleUnlockRequests id with
      | some (_, amount, requestTime, _) =>
          amount * flexibleUnlockFee requestTime s.now / 10000
      | none => 0
  | _ => 0

inductive ApxUSDFlowStep : State → (Op × Address) → State → Prop where
  | standardRequest (s : State) (amount : Nat) (caller : Address) (s' : State)
      (hregistry : RegistryWellIndexed s)
      (hsupply : amount ≤ s.totalSupply_apxUSD)
      (hstep : step s (Op.requestUnlock amount) caller = some s') :
      ApxUSDFlowStep s (Op.requestUnlock amount, caller) s'
  | flexibleRequest (s : State) (amount : Nat) (caller : Address) (s' : State)
      (hregistry : RegistryWellIndexed s)
      (hsupply : amount ≤ s.totalSupply_apxUSD)
      (hstep : step s (Op.flexibleRequestUnlock amount) caller = some s') :
      ApxUSDFlowStep s (Op.flexibleRequestUnlock amount, caller) s'
  | standardClaim (s : State) (id : Nat) (owner : Address) (amount cooldownEnd : Nat)
      (caller : Address) (s' : State)
      (hid : id < s.nextUnlockId)
      (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd))
      (hstep : step s (Op.claimUnlock id) caller = some s') :
      ApxUSDFlowStep s (Op.claimUnlock id, caller) s'
  | flexibleClaim (s : State) (id : Nat) (owner : Address)
      (amount requestTime cooldownEnd : Nat) (caller : Address) (s' : State)
      (hid : id < s.nextUnlockId)
      (hreq : s.flexibleUnlockRequests id =
        some (owner, amount, requestTime, cooldownEnd))
      (hstep : step s (Op.flexibleClaimUnlock id) caller = some s') :
      ApxUSDFlowStep s (Op.flexibleClaimUnlock id, caller) s'
  | tick (s : State) (dt : Nat) (caller : Address) :
      ApxUSDFlowStep s (Op.tick dt, caller) {s with now := s.now + dt}

inductive ApxUSDFlowTrace : State → List (Op × Address) → State → Nat → Prop where
  | nil (s : State) : ApxUSDFlowTrace s [] s 0
  | cons {s s₁ s₂ : State} {p : Op × Address} {ps : List (Op × Address)}
      {fees : Nat}
      (hstep : ApxUSDFlowStep s p s₁)
      (htail : ApxUSDFlowTrace s₁ ps s₂ fees) :
      ApxUSDFlowTrace s (p :: ps) s₂ (apxUSDFlowStepFee s p + fees)

theorem apxUSDFlow_step (h : ApxUSDFlowStep s p s') :
    apxUSDFlow s' + apxUSDFlowStepFee s p = apxUSDFlow s := by
  cases h with
  | standardRequest amount caller s' hregistry hsupply hstep =>
      have hflow := apxUSDFlow_requestUnlock s amount caller s'
        hregistry hsupply hstep
      simpa [apxUSDFlowStepFee] using hflow
  | flexibleRequest amount caller s' hregistry hsupply hstep =>
      have hflow := apxUSDFlow_flexibleRequestUnlock s caller amount
        hregistry hsupply
      obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' hstep
      simpa [hpost, apxUSDFlowStepFee] using hflow
  | standardClaim id owner amount cooldownEnd caller s' hid hreq hstep =>
      have hflow := apxUSDFlow_claimUnlock s id owner amount cooldownEnd caller s'
        hid hreq hstep
      simpa [apxUSDFlowStepFee] using hflow
  | flexibleClaim id owner amount requestTime cooldownEnd caller s' hid hreq hstep =>
      have hflow := apxUSDFlow_flexibleClaimUnlock s id owner amount requestTime
        cooldownEnd caller s' hid hreq hstep
      simpa [apxUSDFlowStepFee, hreq] using hflow
  | tick dt caller =>
      simp [apxUSDFlowStepFee, apxUSDFlow, outstandingApxUSD,
        pendingApxUSD, standardUnlockTotal, flexibleUnlockTotal]

theorem execTrace_cons_of_apxUSDFlowStep
    (hstep : ApxUSDFlowStep s p s') (ps : List (Op × Address)) :
    execTrace s (p :: ps) = execTrace s' ps := by
  cases hstep with
  | standardRequest amount caller s' hregistry hsupply hstep =>
      simp [execTrace, hstep]
  | flexibleRequest amount caller s' hregistry hsupply hstep =>
      simp [execTrace, hstep]
  | standardClaim id owner amount cooldownEnd caller s' hid hreq hstep =>
      simp [execTrace, hstep]
  | flexibleClaim id owner amount requestTime cooldownEnd caller s' hid hreq hstep =>
      simp [execTrace, hstep]
  | tick dt caller =>
      simp [execTrace, step]

theorem apxUSDFlow_trace
    (h : ApxUSDFlowTrace s σ s' fees) :
    execTrace s σ = s' ∧ apxUSDFlow s' + fees = apxUSDFlow s := by
  induction h with
  | nil s => simp [execTrace]
  | @cons s s₁ s₂ p ps fees hstep htail ih =>
      have hlocal := apxUSDFlow_step hstep
      have hexec := execTrace_cons_of_apxUSDFlowStep hstep ps
      constructor
      · rw [hexec, ih.1]
      · omega

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

/-- The signed change in a holder's apyUSD component caused solely by changing
the pricing rate from `R₁` to `R₂`. This is deliberately separate from the
effect of a protocol operation. -/
def holderRateDelta (s : State) (a : Address) (R₁ R₂ : Nat) : Int :=
  (redeemAssets (s.apyUSDBal a) R₂ : Int) -
    (redeemAssets (s.apyUSDBal a) R₁ : Int)

/-- Changing only the pricing rate changes the complete fixed-rate ledger by
exactly `holderRateDelta`; all balance and pending-position terms cancel. -/
theorem holderValueAt_rateDelta (s : State) (a : Address) (R₁ R₂ : Nat) :
    (holderValueAt R₂ s a : Int) - (holderValueAt R₁ s a : Int) =
      holderRateDelta s a R₁ R₂ := by
  unfold holderValueAt holderRateDelta valueAt
  omega

/-! A finite list makes the holder-level rate accounting aggregable without
claiming that the current unbounded `State` already has such a pool ledger. -/

def finitePoolValueAt (R : Nat) (s : State) (holders : List Address) : Int :=
  (holders.map (fun a => (holderValueAt R s a : Int))).sum

def finitePoolRateDelta (s : State) (holders : List Address) (R₁ R₂ : Nat) : Int :=
  (holders.map (fun a => holderRateDelta s a R₁ R₂)).sum

def finiteApyUSDValueAt (R : Nat) (s : State) (holders : List Address) : Nat :=
  (holders.map (fun a => redeemAssets (s.apyUSDBal a) R)).sum

def finiteApyUSDNumerator (R : Nat) (s : State) (holders : List Address) : Nat :=
  (holders.map (fun a => s.apyUSDBal a * R)).sum

theorem finitePoolValueAt_rateDelta (s : State) (holders : List Address)
    (R₁ R₂ : Nat) :
    finitePoolValueAt R₂ s holders - finitePoolValueAt R₁ s holders =
      finitePoolRateDelta s holders R₁ R₂ := by
  induction holders with
  | nil => rfl
  | cons a holders ih =>
      simp only [finitePoolValueAt, finitePoolRateDelta, List.map_cons, List.sum_cons] at ih ⊢
      have ha := holderValueAt_rateDelta s a R₁ R₂
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

theorem finiteApyUSDValueAt_le_redeemAssets_sum (R : Nat) (s : State)
    (holders : List Address) :
    finiteApyUSDValueAt R s holders ≤
      redeemAssets (sumOver s.apyUSDBal holders) R := by
  induction holders with
  | nil => simp [finiteApyUSDValueAt, sumOver, redeemAssets]
  | cons a holders ih =>
      simp only [finiteApyUSDValueAt, List.map_cons, List.sum_cons, sumOver_cons]
      calc
        redeemAssets (s.apyUSDBal a) R +
              (holders.map (fun b => redeemAssets (s.apyUSDBal b) R)).sum ≤
            redeemAssets (s.apyUSDBal a) R +
              redeemAssets (sumOver s.apyUSDBal holders) R :=
          Nat.add_le_add_left ih _
        _ ≤ redeemAssets (s.apyUSDBal a + sumOver s.apyUSDBal holders) R := by
          unfold redeemAssets
          simpa [Nat.add_mul] using
            (div_add_div_le (s.apyUSDBal a * R)
              (sumOver s.apyUSDBal holders * R) ray)

theorem finiteApyUSDNumerator_eq_sum_mul (R : Nat) (s : State)
    (holders : List Address) :
    finiteApyUSDNumerator R s holders = sumOver s.apyUSDBal holders * R := by
  induction holders with
  | nil => simp [finiteApyUSDNumerator, sumOver]
  | cons a holders ih =>
      simp only [finiteApyUSDNumerator, List.map_cons, List.sum_cons, sumOver_cons] at ih ⊢
      rw [ih, Nat.add_mul]

theorem apyUSDLedgerConsistent_finiteApyUSDValueAt_bound
    (R : Nat) (s : State) (h : ApyUSDLedgerConsistent s) :
    ∃ holders : List Address,
      holders.Pairwise (· ≠ ·) ∧
      (∀ a, s.apyUSDBal a ≠ 0 → a ∈ holders) ∧
      finiteApyUSDValueAt R s holders ≤ redeemAssets s.totalSupply_apyUSD R := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  refine ⟨holders, hnd, hcov, ?_⟩
  rw [← hsum]
  exact finiteApyUSDValueAt_le_redeemAssets_sum R s holders

theorem apyUSDLedgerConsistent_finiteApyUSDNumerator
    (R : Nat) (s : State) (h : ApyUSDLedgerConsistent s) :
    ∃ holders : List Address,
      holders.Pairwise (· ≠ ·) ∧
      (∀ a, s.apyUSDBal a ≠ 0 → a ∈ holders) ∧
      finiteApyUSDNumerator R s holders = s.totalSupply_apyUSD * R := by
  obtain ⟨holders, hnd, hcov, hsum⟩ := h
  refine ⟨holders, hnd, hcov, ?_⟩
  rw [finiteApyUSDNumerator_eq_sum_mul, hsum]

theorem apyUSDLedgerConsistent_finiteApyUSDValueAt_single_floor
    (R : Nat) (s : State) (h : ApyUSDLedgerConsistent s) :
    ∃ holders : List Address,
      holders.Pairwise (· ≠ ·) ∧
      (∀ a, s.apyUSDBal a ≠ 0 → a ∈ holders) ∧
      finiteApyUSDNumerator R s holders / ray =
        redeemAssets s.totalSupply_apyUSD R := by
  obtain ⟨holders, hnd, hcov, hnum⟩ :=
    apyUSDLedgerConsistent_finiteApyUSDNumerator R s h
  refine ⟨holders, hnd, hcov, ?_⟩
  rw [hnum]
  rfl

def apyUSDValueRoundingGapWitness : State :=
  { (default : State) with
      apyUSDBal := fun a => if a = 0 then 1 else if a = 1 then 1 else 0
      totalSupply_apyUSD := 2 }

theorem apyUSDValueRoundingGapWitness_consistent :
    ApyUSDLedgerConsistent apyUSDValueRoundingGapWitness := by
  refine ⟨[0, 1], by decide, ?_, ?_⟩
  · intro a ha
    by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;>
      simp [apyUSDValueRoundingGapWitness, h0, h1] at ha ⊢
  · decide

theorem finiteApyUSDValueAt_rounding_gap :
    finiteApyUSDValueAt (ray / 2) apyUSDValueRoundingGapWitness [0, 1] = 0 ∧
      redeemAssets apyUSDValueRoundingGapWitness.totalSupply_apyUSD (ray / 2) = 1 := by
  decide

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
    exact Nat.le_of_eq hframe

/-! ## Rate-aware traces including vault exits

The live-rate theorem cannot simply add `withdraw` and `redeem`: their local
no-gain facts are priced at the rate used by that step. The following relation
records those execution rates and appends the terminal live rate. A pairwise
non-increasing schedule is the exact condition under which the fixed-rate
local facts can be telescoped using `holderValueAt_mono_rate`. -/

def RateAwareHolderValueOp (op : Op) : Prop :=
  StableHolderValueOp op ∨
  (∃ amount, op = Op.lockApxUSD amount) ∨
  (∃ assets receiver, op = Op.withdraw assets receiver) ∨
  (∃ shares receiver, op = Op.redeem shares receiver)

def holderValueExecutionRate (s : State) (op : Op) : Nat :=
  match op with
  | Op.withdraw _ _ => computeExchangeRate (pullVestedYield s)
  | Op.redeem _ _ => computeExchangeRate (pullVestedYield s)
  | _ => computeExchangeRate s

theorem holderValueExecutionRate_eq_live_of_rateAware
    (s : State) (op : Op) (h_op : RateAwareHolderValueOp op)
    (h_period : 0 < s.vestPeriod) :
    holderValueExecutionRate s op = computeExchangeRate s := by
  rcases h_op with h_stable | ⟨amount, rfl⟩ | ⟨assets, receiver, rfl⟩ | ⟨shares, receiver, rfl⟩
  · rcases h_stable with h_rate | h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
    · rcases h_rate with ⟨amount, rfl⟩ | ⟨amount, rfl⟩ <;> rfl
    · rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩ <;> rfl
    · rfl
    · rfl
  · rfl
  · unfold holderValueExecutionRate computeExchangeRate
    rw [totalAssets_pullVestedYield_of_pos_period s h_period]
    simp
  · unfold holderValueExecutionRate computeExchangeRate
    rw [totalAssets_pullVestedYield_of_pos_period s h_period]
    simp

def traceNextState (s : State) (p : Op × Address) : State :=
  match step s p.1 p.2 with
  | none => s
  | some s' => s'

def liveRateSequence (s : State) : List (Op × Address) → List Nat
  | [] => [computeExchangeRate s]
  | p :: σ => holderValueExecutionRate s p.1 ::
      liveRateSequence (traceNextState s p) σ

/-- The pairwise schedule is not an invariant of the current model. A dust-sized
`lockApxUSD` can mint zero shares while adding one asset to the vault, so the
live rate rises and the terminal rate is not below the execution rate. -/
theorem rateAware_schedule_not_automatic :
    let s : State :=
      { (default : State) with
          apxUSDBal := fun a => if a = 1 then 1 else 0
          vaultApxUSDBal := 1
          totalSupply_apyUSD := 0 }
    let σ : List (Op × Address) := [(Op.lockApxUSD 1, 1)]
    ¬ List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁) (liveRateSequence s σ) := by
  decide

/-- The schedule can also rise without a zero-share deposit. A one-asset
withdrawal from a two-share pool burns the ceil-rounded cost of two shares in
this concrete state, leaving a one-ray pool rate. -/
theorem rateAware_schedule_not_automatic_without_dust :
    let s : State :=
      { (default : State) with
          apyUSDBal := fun a => if a = 1 then 2 else 0
          vaultApxUSDBal := 1
          totalSupply_apyUSD := 2 }
    let σ : List (Op × Address) := [(Op.withdraw 1 1, 1)]
    ¬ List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁) (liveRateSequence s σ) := by
  decide

/-! The rate-aware composition needs the no-premium redemption bound at every
prefix state. It does not need a separate operator exclusion: this trace is
holder-signed, and the fixed-rate claim frames already cover the successful
claim branches used here. -/
def RateAwareSideCondition (s : State) : List (Op × Address) → Prop
  | [] => s.redemptionValue ≤ ray
  | p :: σ =>
      s.redemptionValue ≤ ray ∧
        RateAwareSideCondition (traceNextState s p) σ

/-! Rate adjustments between consecutive execution prices. For a singleton
trace this records the final live-rate revaluation; for a longer trace it
records the revaluation from one operation's execution rate to the next
operation's execution rate. -/
def traceRateAdjustments (s : State) (a : Address) : List (Op × Address) → List Int
  | [] => []
  | [p] =>
      [holderRateDelta (traceNextState s p) a
        (holderValueExecutionRate s p.1)
        (computeExchangeRate (traceNextState s p))]
  | p :: q :: σ =>
      holderRateDelta (traceNextState s p) a
        (holderValueExecutionRate s p.1)
        (holderValueExecutionRate (traceNextState s p) q.1) ::
        traceRateAdjustments (traceNextState s p) a (q :: σ)

private theorem holderValueAt_executionRate_step
    (s : State) (op : Op) (caller : Address) (s' : State) (a : Address)
    (h_op : RateAwareHolderValueOp op) (h_caller : caller = a)
    (h_registry : RegistryWellIndexed s) (h_price : s.redemptionValue ≤ ray)
    (h_step : step s op caller = some s') :
    holderValueAt (holderValueExecutionRate s op) s' a ≤
      holderValueAt (holderValueExecutionRate s op) s a := by
  rcases h_op with h_stable | ⟨amount, rfl⟩ | ⟨assets, receiver, rfl⟩ | ⟨shares, receiver, rfl⟩
  · subst caller
    rcases h_stable with h_rate | h_standard | ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
    · rcases h_rate with ⟨amount, rfl⟩ | ⟨amount, rfl⟩
      · exact Nat.le_of_eq (holder_value_depositUSDC s amount a s' h_step)
      · exact holder_value_redeemApxUSD s amount a s' h_step h_price
    · rcases h_standard with ⟨amount, rfl⟩ | ⟨requestId, rfl⟩
      · exact Nat.le_of_eq
          (requestUnlock_holderValueAt_fixedRate (computeExchangeRate s) s amount a s'
            h_step h_registry.1)
      · exact Nat.le_of_eq
          (standardClaim_holderValueAt_fixedRate_any (computeExchangeRate s) s requestId a s' a
            h_step h_registry)
    · exact Nat.le_of_eq
        (flexibleRequestUnlock_holderValueAt_fixedRate (computeExchangeRate s) s amount a s'
          h_step h_registry)
    · exact flexibleClaim_holderValueAt_nonincreasing_any (computeExchangeRate s) s requestId a s' a
        h_step h_registry
  · subst caller
    calc
      holderValueAt (computeExchangeRate s) s' a ≤ holderValue s a :=
        holder_value_lockApxUSD_fixedRate s amount a s' h_step
      _ = holderValueAt (computeExchangeRate s) s a := (holderValueAt_live s a).symm
  · subst caller
    exact holder_value_withdraw s assets receiver a s' h_step
      (flex_unallocated_at_counter s h_registry.1)
  · subst caller
    exact holder_value_redeem s shares receiver a s' h_step
      (flex_unallocated_at_counter s h_registry.1)

/-- One successful step can be separated into two effects: the operation's
fixed-rate holder-value bound, plus the signed revaluation caused by moving
from that execution rate to the post-state live rate. This bridge does not
assume the rate moves downward. -/
theorem holderValueAt_executionRate_step_with_rateDelta
    (s : State) (op : Op) (caller : Address) (s' : State) (a : Address)
    (h_op : RateAwareHolderValueOp op) (h_caller : caller = a)
    (h_registry : RegistryWellIndexed s) (h_price : s.redemptionValue ≤ ray)
    (h_step : step s op caller = some s') :
    (holderValueAt (computeExchangeRate s') s' a : Int) ≤
      (holderValueAt (holderValueExecutionRate s op) s a : Int) +
        holderRateDelta s' a (holderValueExecutionRate s op) (computeExchangeRate s') := by
  have hlocal := holderValueAt_executionRate_step s op caller s' a h_op h_caller
    h_registry h_price h_step
  have hlocal_int :
      (holderValueAt (holderValueExecutionRate s op) s' a : Int) ≤
        (holderValueAt (holderValueExecutionRate s op) s a : Int) :=
    Int.ofNat_le.mpr hlocal
  have hdelta := holderValueAt_rateDelta s' a (holderValueExecutionRate s op)
    (computeExchangeRate s')
  omega

set_option maxRecDepth 10000 in
theorem holderValueAt_rateAware_trace_rateAdjusted
    (s : State) (σ : List (Op × Address)) (a : Address) (R₀ : Nat)
    (h_registry : RegistryWellIndexed s)
    (h_safe : RateAwareSideCondition s σ)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, RateAwareHolderValueOp p.1)
    (h_nonempty : σ ≠ [])
    (h_rate : match σ with
      | [] => True
      | p :: _ => R₀ = holderValueExecutionRate s p.1) :
    (holderValueAt (computeExchangeRate (execTrace s σ)) (execTrace s σ) a : Int) ≤
      (holderValueAt R₀ s a : Int) + (traceRateAdjustments s a σ).sum := by
  induction σ generalizing s R₀ with
  | nil => exact False.elim (h_nonempty rfl)
  | cons p σ ih =>
      obtain ⟨op, caller⟩ := p
      have hcaller : caller = a := h_own (op, caller) List.mem_cons_self
      have hop : RateAwareHolderValueOp op := h_ops (op, caller) List.mem_cons_self
      have htail_own : ∀ q ∈ σ, q.2 = a :=
        fun q hq => h_own q (List.mem_cons_of_mem _ hq)
      have htail_ops : ∀ q ∈ σ, RateAwareHolderValueOp q.1 :=
        fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
      have hrate : R₀ = holderValueExecutionRate s op := by simpa using h_rate
      subst R₀
      cases σ with
      | nil =>
          cases hstep : step s op caller with
          | none =>
              have hdelta := holderValueAt_rateDelta s a
                (holderValueExecutionRate s op) (computeExchangeRate s)
              have hbound :
                  (holderValueAt (computeExchangeRate s) s a : Int) ≤
                    (holderValueAt (holderValueExecutionRate s op) s a : Int) +
                      holderRateDelta s a (holderValueExecutionRate s op)
                        (computeExchangeRate s) := by
                omega
              simpa [execTrace, traceNextState, traceRateAdjustments, hstep] using hbound
          | some s1 =>
              have hbound := holderValueAt_executionRate_step_with_rateDelta s op caller s1 a
                hop hcaller h_registry h_safe.1 hstep
              simpa [execTrace, traceNextState, traceRateAdjustments, hstep] using hbound
      | cons q σ =>
          cases hstep : step s op caller with
          | none =>
              have hsafe_tail : RateAwareSideCondition s (q :: σ) := by
                simpa [traceNextState, hstep] using h_safe.2
              have hbound := ih s (holderValueExecutionRate s q.1) h_registry hsafe_tail
                htail_own htail_ops (by simp) rfl
              have hdelta := holderValueAt_rateDelta s a
                (holderValueExecutionRate s op) (holderValueExecutionRate s q.1)
              have hcombined :
                  (holderValueAt (computeExchangeRate (execTrace s (q :: σ)))
                      (execTrace s (q :: σ)) a : Int) ≤
                    (holderValueAt (holderValueExecutionRate s op) s a : Int) +
                      (holderRateDelta s a (holderValueExecutionRate s op)
                        (holderValueExecutionRate s q.1) +
                      (traceRateAdjustments s a (q :: σ)).sum) := by
                omega
              simpa [execTrace, traceNextState, traceRateAdjustments, hstep] using hcombined
          | some s1 =>
              have hsafe_tail : RateAwareSideCondition s1 (q :: σ) := by
                simpa [traceNextState, hstep] using h_safe.2
              have h_registry1 : RegistryWellIndexed s1 :=
                registryWellIndexed_step s op caller s1 h_registry hstep
              have hbound := ih s1 (holderValueExecutionRate s1 q.1) h_registry1 hsafe_tail
                htail_own htail_ops (by simp) rfl
              have hlocal := holderValueAt_executionRate_step s op caller s1 a hop hcaller
                h_registry h_safe.1 hstep
              have hdelta := holderValueAt_rateDelta s1 a
                (holderValueExecutionRate s op) (holderValueExecutionRate s1 q.1)
              have hlocal_int :
                  (holderValueAt (holderValueExecutionRate s op) s1 a : Int) ≤
                    (holderValueAt (holderValueExecutionRate s op) s a : Int) :=
                Int.ofNat_le.mpr hlocal
              have hcombined :
                  (holderValueAt (computeExchangeRate (execTrace s1 (q :: σ)))
                      (execTrace s1 (q :: σ)) a : Int) ≤
                    (holderValueAt (holderValueExecutionRate s op) s a : Int) +
                      (holderRateDelta s1 a (holderValueExecutionRate s op)
                        (holderValueExecutionRate s1 q.1) +
                      (traceRateAdjustments s1 a (q :: σ)).sum) := by
                omega
              simpa [execTrace, traceNextState, traceRateAdjustments, hstep] using hcombined

set_option maxRecDepth 10000 in
theorem holderValue_rateAware_trace_rateAdjusted
    (s : State) (σ : List (Op × Address)) (a : Address) (R₀ : Nat)
    (h_registry : RegistryWellIndexed s)
    (h_safe : RateAwareSideCondition s σ)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, RateAwareHolderValueOp p.1)
    (h_nonempty : σ ≠ [])
    (h_rate : match σ with
      | [] => True
      | p :: _ => R₀ = holderValueExecutionRate s p.1)
    (h_period : 0 < s.vestPeriod) :
    (holderValue (execTrace s σ) a : Int) ≤
      (holderValue s a : Int) + (traceRateAdjustments s a σ).sum := by
  cases σ with
  | nil => exact False.elim (h_nonempty rfl)
  | cons p σ =>
      have hfirst_op : RateAwareHolderValueOp p.1 := h_ops p List.mem_cons_self
      have hfirst_rate := holderValueExecutionRate_eq_live_of_rateAware s p.1 hfirst_op h_period
      have hR : R₀ = holderValueExecutionRate s p.1 := by simpa using h_rate
      have hbound := holderValueAt_rateAware_trace_rateAdjusted s (p :: σ) a R₀
        h_registry h_safe h_own h_ops h_nonempty h_rate
      calc
        (holderValue (execTrace s (p :: σ)) a : Int) =
            (holderValueAt (computeExchangeRate (execTrace s (p :: σ)))
              (execTrace s (p :: σ)) a : Int) := by
          rw [holderValueAt_live]
        _ ≤ (holderValueAt R₀ s a : Int) +
              (traceRateAdjustments s a (p :: σ)).sum := hbound
        _ = (holderValue s a : Int) +
              (traceRateAdjustments s a (p :: σ)).sum := by
          rw [hR, hfirst_rate, holderValueAt_live]

private theorem liveRateSequence_pairwise_tail (s : State) (p : Op × Address)
    (σ : List (Op × Address))
    (h : List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁) (liveRateSequence s (p :: σ))) :
    List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
      (liveRateSequence (traceNextState s p) σ) := by
  change List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
    (holderValueExecutionRate s p.1 :: liveRateSequence (traceNextState s p) σ) at h
  exact (List.pairwise_cons.mp h).2

private theorem liveRateSequence_head_bound (s : State) (p : Op × Address)
    (σ : List (Op × Address))
    (h : List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁) (liveRateSequence s (p :: σ))) :
    ∀ x ∈ liveRateSequence (traceNextState s p) σ,
      x ≤ holderValueExecutionRate s p.1 := by
  change List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
    (holderValueExecutionRate s p.1 :: liveRateSequence (traceNextState s p) σ) at h
  exact (List.pairwise_cons.mp h).1

set_option maxRecDepth 10000 in
theorem holderValueAt_rateAware_trace_bound
    (s : State) (σ : List (Op × Address)) (a : Address) (R₀ : Nat)
    (h_registry : RegistryWellIndexed s)
    (h_safe : RateAwareSideCondition s σ)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, RateAwareHolderValueOp p.1)
    (h_nonempty : σ ≠ [])
    (h_rate : match σ with
      | [] => True
      | p :: _ => R₀ = holderValueExecutionRate s p.1)
    (h_rates : List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
      (liveRateSequence s σ)) :
    holderValueAt (computeExchangeRate (execTrace s σ)) (execTrace s σ) a ≤
      holderValueAt R₀ s a := by
  induction σ generalizing s R₀ with
  | nil => exact False.elim (h_nonempty rfl)
  | cons p σ ih =>
      obtain ⟨op, caller⟩ := p
      have hcaller : caller = a := h_own (op, caller) List.mem_cons_self
      have hop : RateAwareHolderValueOp op := h_ops (op, caller) List.mem_cons_self
      have htail_own : ∀ q ∈ σ, q.2 = a :=
        fun q hq => h_own q (List.mem_cons_of_mem _ hq)
      have htail_ops : ∀ q ∈ σ, RateAwareHolderValueOp q.1 :=
        fun q hq => h_ops q (List.mem_cons_of_mem _ hq)
      have hrate : R₀ = holderValueExecutionRate s op := by simpa using h_rate
      subst R₀
      cases σ with
      | nil =>
          have hpair := List.pairwise_cons.mp h_rates
          have hterminal : computeExchangeRate (traceNextState s (op, caller)) ≤
              holderValueExecutionRate s op := by
            apply hpair.1
            simp [liveRateSequence]
          cases hstep : step s op caller with
          | none =>
              simpa [execTrace, traceNextState, hstep] using
                holderValueAt_mono_rate s a _ _ hterminal
          | some s1 =>
              have hlocal := holderValueAt_executionRate_step s op caller s1 a hop hcaller
                h_registry h_safe.1 hstep
              have hterminal' : computeExchangeRate s1 ≤
                  holderValueExecutionRate s op := by
                simpa [traceNextState, hstep] using hterminal
              have hpostrate := holderValueAt_mono_rate s1 a _ _ hterminal'
              simpa [execTrace, traceNextState, hstep] using Nat.le_trans hpostrate hlocal
      | cons q σ =>
          have htail_pair := liveRateSequence_pairwise_tail s (op, caller) (q :: σ) h_rates
          have hhead := liveRateSequence_head_bound s (op, caller) (q :: σ) h_rates
          cases hstep : step s op caller with
          | none =>
              have hsafe_tail : RateAwareSideCondition s (q :: σ) := by
                simpa [traceNextState, hstep] using h_safe.2
              have htail_pair' : List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
                  (liveRateSequence s (q :: σ)) := by
                simpa only [liveRateSequence, traceNextState, hstep] using htail_pair
              have hbound := ih s (holderValueExecutionRate s q.1) h_registry hsafe_tail
                htail_own htail_ops (by simp) rfl htail_pair'
              have hnext_rate : holderValueExecutionRate s q.1 ≤
                  holderValueExecutionRate s op := by
                exact hhead _ (by simp [liveRateSequence, traceNextState, hstep])
              have hpostrate := holderValueAt_mono_rate s a _ _ hnext_rate
              simpa [execTrace, traceNextState, hstep] using
                Nat.le_trans hbound hpostrate
          | some s1 =>
              have hsafe_tail : RateAwareSideCondition s1 (q :: σ) := by
                simpa [traceNextState, hstep] using h_safe.2
              have h_registry1 : RegistryWellIndexed s1 :=
                registryWellIndexed_step s op caller s1 h_registry hstep
              have htail_pair' : List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
                  (liveRateSequence s1 (q :: σ)) := by
                simpa only [liveRateSequence, traceNextState, hstep] using htail_pair
              have hbound := ih s1 (holderValueExecutionRate s1 q.1) h_registry1 hsafe_tail
                htail_own htail_ops (by simp) rfl htail_pair'
              have hlocal := holderValueAt_executionRate_step s op caller s1 a hop hcaller
                h_registry h_safe.1 hstep
              have hnext_rate : holderValueExecutionRate s1 q.1 ≤
                  holderValueExecutionRate s op := by
                exact hhead _ (by simp [liveRateSequence, traceNextState, hstep])
              have hpostrate := holderValueAt_mono_rate s1 a _ _ hnext_rate
              simpa [execTrace, traceNextState, hstep] using
                Nat.le_trans hbound (Nat.le_trans hpostrate hlocal)

/-- A live-value corollary for a positive-period model. The first execution
rate is derived to equal the initial live rate; later rate movement remains
represented by the explicit pairwise execution-rate schedule. -/
theorem holderValue_rateAware_trace_nonincreasing
    (s : State) (σ : List (Op × Address)) (a : Address) (R₀ : Nat)
    (h_registry : RegistryWellIndexed s)
    (h_safe : RateAwareSideCondition s σ)
    (h_own : ∀ p ∈ σ, p.2 = a)
    (h_ops : ∀ p ∈ σ, RateAwareHolderValueOp p.1)
    (h_nonempty : σ ≠ [])
    (h_rate : match σ with
      | [] => True
      | p :: _ => R₀ = holderValueExecutionRate s p.1)
    (h_rates : List.Pairwise (fun r₁ r₂ => r₂ ≤ r₁)
      (liveRateSequence s σ))
    (h_period : 0 < s.vestPeriod) :
    holderValue (execTrace s σ) a ≤ holderValue s a := by
  cases σ with
  | nil => exact False.elim (h_nonempty rfl)
  | cons p σ =>
    have hfirst_op : RateAwareHolderValueOp p.1 := h_ops p List.mem_cons_self
    have hfirst_rate := holderValueExecutionRate_eq_live_of_rateAware s p.1 hfirst_op h_period
    have h_initial_rate : R₀ ≤ computeExchangeRate s := by
      have hR : R₀ = holderValueExecutionRate s p.1 := by simpa using h_rate
      rw [hR, hfirst_rate]
      exact Nat.le_refl _
    have hbound := holderValueAt_rateAware_trace_bound s (p :: σ) a R₀ h_registry h_safe h_own h_ops
      h_nonempty h_rate h_rates
    have hmono := holderValueAt_mono_rate s a R₀ (computeExchangeRate s) h_initial_rate
    calc
      holderValue (execTrace s (p :: σ)) a =
          holderValueAt (computeExchangeRate (execTrace s (p :: σ)))
            (execTrace s (p :: σ)) a :=
        (holderValueAt_live (execTrace s (p :: σ)) a).symm
      _ ≤ holderValueAt R₀ s a := hbound
      _ ≤ holderValueAt (computeExchangeRate s) s a := hmono
      _ = holderValue s a := holderValueAt_live s a

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
