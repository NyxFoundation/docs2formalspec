import D2fsSpecs.Apyx

/-!
# Blast-radius theorems: damage upper bounds under privileged-key compromise

This module implements the Tier-1 theorem list (T1-T4) of `docs/05-blast-radius.md`:
upper bounds on user-asset loss when a privileged role's key is fully compromised
(the social-engineering threat model, cf. Bybit 2025).

Threat model: the attacker holds the private key of one or more role addresses
(`pauseController`, `yieldDistributor`, `admin`, `oracle`, ...) and can submit an
arbitrary sequence of operations with those callers, interleaved with honest traffic.
A failed operation reverts (state unchanged), so a trace executes with revert-skip
semantics (`execTrace`).

Contents:

* **Exact-effect (frame) theorems** for every role-gated operation: a successful
  `pause`/`unpause`/`creditYield`/admin-op/oracle-op is shown to equal the
  pre-state with only its named non-asset fields overridden, so no balance, supply,
  reserve, or unlock-position field can move.
* **Balance-field forms** (T1-T3): the frame results instantiated on every balance
  and supply field, by exhaustive case analysis over the closed `Op` inductive —
  the same pattern as the requirement theorems in `Apyx.lean`.
* **Trace forms**: the frame results are lifted by induction to arbitrarily
  long attack traces (`execTrace`), giving the memo's headline shape
  `userLoss(execSeq s₀ σ) ≤ B(R, s₀)` with `B` read off the surviving fields.
* **Non-custodial theorems (T4)**: the single-step debit analyses
  (`no_role_transfers_user_funds`, `no_role_burns_user_shares`,
  `no_role_debits_usdc`), governance-token immutability, unlock-position seizure
  bounds, and the trace-level headline: even if **every** operator key is stolen,
  a user who signs nothing and is not targeted by an approved RFQ counterparty
  cannot lose a single unit of any balance.
* **Tier-2 stepping stones**: redemption-price provenance and the reserve-outflow
  law, the single-step characterizations behind T5/T6.

Everything here is additive: the ground-truth model and its 81 requirement theorems
in `D2fsSpecs/Apyx.lean` are untouched. Because that file's helper lemmas are
`private`, the small set of step-inversion lemmas needed here is re-derived locally
(named `inv_*`).
-/

namespace Apyx

/-! ## Trace execution (revert-skip semantics)

An attack trace is a list of `(op, caller)` pairs executed in order. An operation
whose guard fails reverts and leaves the state unchanged — exactly like a reverted
transaction on chain — and the trace continues. -/

/-- Execute a list of `(op, caller)` pairs in order; failed operations revert
(leave the state unchanged) and the trace continues. -/
def execTrace (s : State) : List (Op × Address) → State
  | [] => s
  | (op, c) :: σ =>
    match step s op c with
    | some s' => execTrace s' σ
    | none => execTrace s σ

/-! ## Role-gated operation classes

Each predicate lists exactly the operations whose *authorization* is the given role.
The exact-effect theorems below show (a) each such operation indeed demands the role
(soundness of the classification) and (b) its complete state effect. Note that a
compromised role key can of course also submit non-role-gated operations from the
role address, but those are covered by the universal non-custodial theorems (T4),
which hold for arbitrary callers. -/

/-- Operations authorized by the `pauseController` role. -/
def PauserOp (op : Op) : Prop := op = Op.pause ∨ op = Op.unpause

/-- Operations authorized by the `yieldDistributor` role. -/
def DistributorOp (op : Op) : Prop := ∃ amount, op = Op.creditYield amount

/-- Operations authorized by the `oracle` role. -/
def OracleOp (op : Op) : Prop :=
  ∃ price, op = Op.setApxUSDMarketPrice price

/-- Operations authorized by the `admin` role. -/
def AdminOp (op : Op) : Prop :=
  (∃ a, op = Op.addToWhitelist a) ∨ (∃ a, op = Op.removeFromWhitelist a) ∨
  (∃ a, op = Op.addToDenylist a) ∨ (∃ a, op = Op.removeFromDenylist a) ∨
  (∃ bps, op = Op.setYieldRate bps) ∨ (∃ amount, op = Op.handleStressEvent amount) ∨
  op = Op.catastrophicBackstop ∨ (∃ p, op = Op.setVestPeriod p) ∨
  (∃ v, op = Op.updateRedemptionValue v) ∨ (∃ amt r, op = Op.withdrawReserve amt r)

/-- Decidable mirror of `AdminOp`, for use in the `step2tl` guard. `AdminOp` is a disjunction of
existentials, so it carries no `Decidable` instance; this matches on the constructor instead. -/
def isAdminOp : Op → Bool
  | Op.addToWhitelist _ => true
  | Op.removeFromWhitelist _ => true
  | Op.addToDenylist _ => true
  | Op.removeFromDenylist _ => true
  | Op.setYieldRate _ => true
  | Op.handleStressEvent _ => true
  | Op.catastrophicBackstop => true
  | Op.setVestPeriod _ => true
  | Op.updateRedemptionValue _ => true
  | Op.withdrawReserve _ _ => true
  | _ => false

/-- The mirror agrees with the predicate, in both directions. -/
theorem isAdminOp_iff (op : Op) : isAdminOp op = true ↔ AdminOp op := by
  constructor
  · intro h
    cases op <;> simp only [isAdminOp] at h <;> unfold AdminOp <;> simp_all
  · intro h
    unfold AdminOp at h
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-! ## Local frame lemmas for `pullVestedYield`

(Re-derived: the equivalents in `Apyx.lean` are `private`.) -/

@[simp] private theorem pv_exchangeRate (s : State) :
    (pullVestedYield s).exchangeRate = s.exchangeRate := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_apyUSDBal (s : State) :
    (pullVestedYield s).apyUSDBal = s.apyUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_apxUSDBal (s : State) :
    (pullVestedYield s).apxUSDBal = s.apxUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_usdcBal (s : State) :
    (pullVestedYield s).usdcBal = s.usdcBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_governanceTokenBal (s : State) :
    (pullVestedYield s).governanceTokenBal = s.governanceTokenBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_nextUnlockId (s : State) :
    (pullVestedYield s).nextUnlockId = s.nextUnlockId := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_unlockTokenOwner (s : State) :
    (pullVestedYield s).unlockTokenOwner = s.unlockTokenOwner := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_unlockTokenAmount (s : State) :
    (pullVestedYield s).unlockTokenAmount = s.unlockTokenAmount := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_unlockTokenOperator (s : State) :
    (pullVestedYield s).unlockTokenOperator = s.unlockTokenOperator := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_unlockRequests (s : State) :
    (pullVestedYield s).unlockRequests = s.unlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pv_flexibleUnlockRequests (s : State) :
    (pullVestedYield s).flexibleUnlockRequests = s.flexibleUnlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

/-! ## Local lemma for `newlyVestedAmount`

(Re-derived: the equivalent in `Apyx.lean`, `newlyVestedAmount_le_total`, is
`private`.) Needed to show that `creditYield`/`setVestPeriod`'s accrue-first step
(`vestTotal := (s.vestTotal - newlyVestedAmount s s.now) + amount`, resp.
`s.vestTotal - newlyVestedAmount s s.now`) never truncates: the streamed-out
portion being folded into `fullyVestedAmount` never exceeds the pool it is drawn
from, so the `Nat`-subtraction is exact and the accrued value is conserved, not
lost. -/

/-- `e * T / P ≤ T` whenever `e ≤ P` (with the `P = 0` case handled separately,
since then the division is `0 / 0 = 0`). -/
private theorem div_mul_le_total {e P T : Nat} (h : e ≤ P) : e * T / P ≤ T := by
  rcases Nat.eq_zero_or_pos P with hp | hp
  · subst hp
    simp [Nat.le_zero.mp h]
  · calc e * T / P ≤ P * T / P := Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
      _ = T := Nat.mul_div_cancel_left _ hp

/-- `newlyVestedAmount` never exceeds the total of the currently-streaming vest
pool it is drawn from. -/
private theorem newlyVestedAmount_le_vestTotal (s : State) (n : Nat) :
    newlyVestedAmount s n ≤ s.vestTotal := by
  unfold newlyVestedAmount
  dsimp only
  repeat' split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact div_mul_le_total (by omega)

/-! ## Local step-inversion lemmas

(Re-derived: the equivalents in `Apyx.lean` are `private`.) Each characterizes the
guard conditions and the exact successor state of one operation. -/

private theorem inv_depositUSDC (s : State) (amount : Nat) (caller : Address) (s' : State)
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

private theorem inv_mintApxUSD (s : State) (to : Address) (amount : Nat) (caller : Address) (s' : State)
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

private theorem inv_lockApxUSD (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.lockApxUSD amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
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
      · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem inv_requestUnlock (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.requestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = requestUnlockStep s caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

/-- A standard `requestUnlock` only ever assigns an unlock-token owner at the current
registry counter; any other position keeps its owner. (Re-derived locally over
`requestUnlockStep`.) -/
private theorem inv_requestUnlock_owner_of_ne (s : State) (caller amount : Nat) {id : Nat}
    (hid : id ≠ s.nextUnlockId) :
    (requestUnlockStep s caller amount).unlockTokenOwner id = s.unlockTokenOwner id := by
  unfold requestUnlockStep
  (repeat' split) <;> simp_all [createStandardUnlock, updateStandardUnlock, burnApxUSD]

/-- Non-seizure of amounts: given the registry well-formedness that a caller's pending
standard-request pointer references a position the caller itself owns (an invariant every
reachable state satisfies, since the pointer is only ever set by the caller's own request),
a `requestUnlock` by `caller` never changes the recorded amount of a *different* user's
position — the top-up branch only ever touches the caller's own tracked id. -/
private theorem inv_requestUnlock_amount_of_other (s : State) (caller amount id : Nat) (u : Address)
    (h_ne_next : id ≠ s.nextUnlockId)
    (h_live : s.unlockTokenOwner id = some u) (h_not_owner : caller ≠ u)
    (h_wf : ∀ i, s.unlockRequestId caller = some i → s.unlockTokenOwner i = some caller) :
    (requestUnlockStep s caller amount).unlockTokenAmount id = s.unlockTokenAmount id := by
  unfold requestUnlockStep
  split
  · rename_i id' heqptr
    have hptr : s.unlockRequestId caller = some id' := by simpa [burnApxUSD] using heqptr
    have hne : id ≠ id' := by
      intro he
      rw [he, h_wf id' hptr] at h_live
      exact h_not_owner (Option.some.inj h_live)
    split
    · rename_i o oldAmount oldEnd heqreq
      by_cases ho : o = caller
      · rw [if_pos ho]
        simp only [updateStandardUnlock, heqreq]
        simp [burnApxUSD, hne]
      · rw [if_neg ho]
        simp [createStandardUnlock, burnApxUSD, h_ne_next]
    · simp [createStandardUnlock, burnApxUSD, h_ne_next]
  · simp [createStandardUnlock, burnApxUSD, h_ne_next]

private theorem inv_flexibleRequestUnlock (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = createFlexibleUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem inv_claimUnlock (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.claimUnlock id) caller = some s') :
    ∃ owner amount cooldownEnd,
      s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      cooldownEnd ≤ s.now ∧
      s' = mintApxUSD (retireStandardUnlock s id owner) owner amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · exact ⟨owner, amount, cooldownEnd, heq, by simp_all, by assumption, by omega,
              (Option.some.inj h).symm⟩
        · exact absurd h (by simp)

private theorem inv_flexibleClaimUnlock (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      requestTime + minFlexibleClaim ≤ s.now ∧
      s' = mintApxUSD (retireFlexibleUnlock s id) owner
        (amount - amount * flexibleUnlockFee requestTime s.now / 10000) := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount requestTime cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · exact ⟨owner, amount, requestTime, cooldownEnd, heq, by simp_all, by assumption,
              by omega, (Option.some.inj h).symm⟩
        · exact absurd h (by simp)

private theorem inv_redeemApxUSD (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.redeemApxUSD amount) caller = some s') :
    s.globalPause = false ∧ s.whitelist caller = true ∧ amount ≤ s.apxUSDBal caller ∧
    (amount * s.redemptionValue) / ray ≤ s.usdcReserve ∧ s.apxUSDMarketPrice < ray ∧
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
              · exact ⟨by simp_all, by simp_all, by omega, by omega, by omega,
                  (Option.some.inj h).symm⟩

private theorem inv_withdraw (s : State) (assets : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s.globalPause = false ∧
    withdrawShares assets (computeExchangeRate (pullVestedYield s)) ≤ (pullVestedYield s).apyUSDBal caller ∧
    assets ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller (withdrawShares assets (computeExchangeRate (pullVestedYield s))) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller (withdrawShares assets (computeExchangeRate (pullVestedYield s)))).vaultApxUSDBal - assets }
          receiver assets)) "Withdraw" [caller, receiver, caller, assets, withdrawShares assets (computeExchangeRate (pullVestedYield s))] := by
  simp only [step, pv_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem inv_redeem (s : State) (shares : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.redeem shares receiver) caller = some s') :
    s.globalPause = false ∧
    shares ≤ (pullVestedYield s).apyUSDBal caller ∧
    redeemAssets shares (computeExchangeRate (pullVestedYield s)) ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller shares with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal - redeemAssets shares (computeExchangeRate (pullVestedYield s)) }
          receiver (redeemAssets shares (computeExchangeRate (pullVestedYield s))))) "Withdraw" [caller, receiver, caller, redeemAssets shares (computeExchangeRate (pullVestedYield s)), shares] := by
  simp only [step, pv_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem inv_executeRFQRedemption (s : State) (user : Address) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.executeRFQRedemption user amount) caller = some s') :
    s.globalPause = false ∧ s.rfqCounterparties.contains caller = true ∧
    s.whitelist user = true ∧
    amount ≤ s.rfqRequests user ∧
    amount ≤ s.apxUSDBal user ∧
    (amount * s.redemptionValue) / ray ≤ s.usdcReserve ∧
    s' = { burnApxUSD s user amount with
        rfqRequests := fun a => if a = user then (burnApxUSD s user amount).rfqRequests a - amount
                                else (burnApxUSD s user amount).rfqRequests a
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
        · split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · exact ⟨by simp_all, by simp_all, by simp_all, by omega, by omega, by omega,
                (Option.some.inj h).symm⟩

/-! ## T1: `pauser_cannot_extract`

Full compromise of the `pauseController` key can only toggle the `globalPause` bit.
The damage is a loss of liveness (operations are frozen / unfrozen at the attacker's
whim), never a loss of assets: no balance, supply, reserve, or unlock-position field
is reachable from the pauser role. -/

/-- Exact effect of `pause`: it demands the pauser role and sets the pause bit;
every other field of the state is untouched. -/
theorem step_pause_exact (s : State) (caller : Address) (s' : State)
    (h : step s Op.pause caller = some s') :
    caller = s.pauseController ∧ s' = { s with globalPause := true } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `unpause`: it demands the pauser role and clears the pause bit;
every other field of the state is untouched. -/
theorem step_unpause_exact (s : State) (caller : Address) (s' : State)
    (h : step s Op.unpause caller = some s') :
    caller = s.pauseController ∧ s' = { s with globalPause := false } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- T1 (single step): a pauser-gated operation demands the pauser role, and the
post-state agrees with the pre-state on **every** field other than `globalPause`
(stated as: overriding `globalPause` with any common value makes the states equal). -/
theorem pauser_cannot_extract (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : PauserOp op) (h_step : step s op caller = some s') :
    caller = s.pauseController ∧
    ∀ b, { s' with globalPause := b } = { s with globalPause := b } := by
  obtain rfl | rfl := h_gated
  · obtain ⟨hc, rfl⟩ := step_pause_exact s caller s' h_step
    exact ⟨hc, fun _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_unpause_exact s caller s' h_step
    exact ⟨hc, fun _ => rfl⟩

/-- T1, asset-field corollary: pauser-gated operations move no asset whatsoever —
all token balances, supplies, the USDC reserve, the vault balance, the vest pool,
and the entire unlock-position registry are unchanged. -/
theorem pauser_cannot_extract_assets (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : PauserOp op) (h_step : step s op caller = some s') :
    s'.apxUSDBal = s.apxUSDBal ∧ s'.apyUSDBal = s.apyUSDBal ∧
    s'.usdcBal = s.usdcBal ∧ s'.governanceTokenBal = s.governanceTokenBal ∧
    s'.usdcReserve = s.usdcReserve ∧
    s'.totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    s'.vaultApxUSDBal = s.vaultApxUSDBal ∧
    s'.vestTotal = s.vestTotal ∧
    s'.unlockTokenOwner = s.unlockTokenOwner ∧
    s'.unlockTokenAmount = s.unlockTokenAmount := by
  obtain rfl | rfl := h_gated
  · obtain ⟨-, rfl⟩ := step_pause_exact s caller s' h_step
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨-, rfl⟩ := step_unpause_exact s caller s' h_step
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- T1 (trace form): an arbitrarily long attack trace consisting solely of
pauser-gated operations — the complete capability set of a stolen pauser key acting
through its role — leaves every field of the state except `globalPause` unchanged.
The blast radius of a pauseController compromise is exactly the pause bit. -/
theorem pauser_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, PauserOp p.1) :
    ∀ b, { execTrace s σ with globalPause := b } = { s with globalPause := b } := by
  induction σ generalizing s with
  | nil => intro b; rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    intro b
    have h_tail : ∀ q ∈ σ, PauserOp q.1 := fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail b
    | some s1 =>
      obtain ⟨-, hframe⟩ :=
        pauser_cannot_extract s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      calc { execTrace s1 σ with globalPause := b }
          = { s1 with globalPause := b } := ih s1 h_tail b
        _ = { s with globalPause := b } := hframe b

/-! ## T2: `yield_distributor_cannot_extract`

Full compromise of the `yieldDistributor` key cannot extract assets: the only
operation the role authorizes is `creditYield`. `creditYield` is accrue-first (cf.
`Apyx.lean`'s `req_credit_preserves_accrued_vest`): it first realizes whatever has
already linearly streamed out of the current vest clock into `fullyVestedAmount`,
*then* folds the remainder alongside the newly credited `amount` into a
freshly-restarted `vestTotal`/`vestStart` clock. Because of this, `vestTotal` alone
is **not** monotone — a credit can shrink `vestTotal` (when the already-streamed
portion `newlyVestedAmount` exceeds `amount`) — but no value is ever lost: exactly
that streamed portion moves into `fullyVestedAmount` instead, so the combined pool
`fullyVestedAmount + vestTotal` always grows by exactly the credited `amount`.
`usdcReserve` increases unconditionally. No user balance, supply, or unlock
position is reachable.

Liveness caveat (documented, not a safety violation): because `creditYield` resets
`vestStart := now`, a compromised distributor can repeatedly credit `0` to postpone
the vesting of already-accrued yield indefinitely. The combined pool
(`fullyVestedAmount + vestTotal`) and the reserve never decrease, so no asset is
lost. -/

/-- Exact effect of `creditYield`: it demands the yieldDistributor role, adds the
amount to the USDC reserve, realizes the currently-streamed portion of the vest
into `fullyVestedAmount`, folds the remainder plus the new amount into a
freshly-restarted `vestTotal`, resets the vesting clock, and touches nothing
else. -/
theorem step_creditYield_exact (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.creditYield amount) caller = some s') :
    caller = s.yieldDistributor ∧
    s' = { s with fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
                  vestTotal := (s.vestTotal - newlyVestedAmount s s.now) + amount
                  vestStart := s.now } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- T2 (single step, frame form): a distributor-gated operation demands the
yieldDistributor role, agrees with the pre-state on every field other than
`usdcReserve`/`vestTotal`/`vestStart`/`fullyVestedAmount`, the reserve can only
**increase**, and the combined vest pool `fullyVestedAmount + vestTotal` can only
**increase** — the role can pay in, never extract. (`vestTotal` alone is NOT
monotone in general — the accrue-first step can shrink it while growing
`fullyVestedAmount` by the same amount; see the section note above. The exact
per-field effect, including the precise increments, is `step_creditYield_exact`
above.) -/
theorem yield_distributor_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : DistributorOp op) (h_step : step s op caller = some s') :
    caller = s.yieldDistributor ∧
    (∀ r v w f, { s' with usdcReserve := r, vestTotal := v, vestStart := w,
                          fullyVestedAmount := f }
            = { s with usdcReserve := r, vestTotal := v, vestStart := w,
                       fullyVestedAmount := f }) ∧
    -- STRONGER than the previous `s.usdcReserve ≤ s'.usdcReserve`: now that `creditYield`
    -- models `IVesting.depositYield` alone, the distributor cannot touch the USDC redemption
    -- reserve at all — that lives in `RedemptionPoolV0`, a different contract.
    s'.usdcReserve = s.usdcReserve ∧
    s.fullyVestedAmount + s.vestTotal ≤ s'.fullyVestedAmount + s'.vestTotal := by
  obtain ⟨amount, rfl⟩ := h_gated
  obtain ⟨hc, rfl⟩ := step_creditYield_exact s amount caller s' h_step
  refine ⟨hc, fun _ _ _ _ => rfl, rfl, ?_⟩
  have hnv := newlyVestedAmount_le_vestTotal s s.now
  dsimp only
  omega

/-- T2 (trace form): an arbitrarily long attack trace consisting solely of
distributor-gated operations leaves every field except
`usdcReserve`/`vestTotal`/`vestStart`/`fullyVestedAmount` unchanged, the reserve
never decreases, and the combined vest pool `fullyVestedAmount + vestTotal` never
decreases. A yieldDistributor compromise cannot remove a single unit of value from
the system (it can only reshuffle it between the "already streamed" and "still
streaming" accumulators, and postpone when the still-streaming portion is
released). -/
theorem yield_distributor_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, DistributorOp p.1) :
    (∀ r v w f, { execTrace s σ with usdcReserve := r, vestTotal := v, vestStart := w,
                                     fullyVestedAmount := f }
            = { s with usdcReserve := r, vestTotal := v, vestStart := w,
                       fullyVestedAmount := f }) ∧
    -- equality, not `≤`: `creditYield` no longer touches the USDC reserve at all
    (execTrace s σ).usdcReserve = s.usdcReserve ∧
    s.fullyVestedAmount + s.vestTotal
      ≤ (execTrace s σ).fullyVestedAmount + (execTrace s σ).vestTotal := by
  induction σ generalizing s with
  | nil => exact ⟨fun _ _ _ _ => rfl, rfl, Nat.le_refl _⟩
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have h_tail : ∀ q ∈ σ, DistributorOp q.1 :=
      fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail
    | some s1 =>
      obtain ⟨-, hframe, hres, hvest⟩ :=
        yield_distributor_frame s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      obtain ⟨ihframe, ihres, ihvest⟩ := ih s1 h_tail
      refine ⟨fun r v w f => ?_, ihres.trans hres, Nat.le_trans hvest ihvest⟩
      calc { execTrace s1 σ with usdcReserve := r, vestTotal := v, vestStart := w,
                                 fullyVestedAmount := f }
          = { s1 with usdcReserve := r, vestTotal := v, vestStart := w,
                      fullyVestedAmount := f } := ihframe r v w f
        _ = { s with usdcReserve := r, vestTotal := v, vestStart := w,
                     fullyVestedAmount := f } := hframe r v w f

/-! ## T3: `admin_cannot_touch_balances`, frame and trace forms

Full compromise of the `admin` key reaches exactly nine fields — the two access
lists and seven pricing/schedule parameters — and no balance, supply, reserve, or
unlock-position field. Each of the eight admin-gated operations gets an
*exact-effect* lemma (the entire post-state is the pre-state with named fields
overridden), the frames are combined into the single-step balance statement
`admin_cannot_touch_balances`, and lifted to arbitrary-length admin-only traces.

Scope caveats (what a compromised admin CAN do, all deferred effects on future
operations rather than debits of recorded holdings):
* `removeFromWhitelist`/`addToDenylist` block a user's future deposits/redemptions
  (liveness attack; cf. T8 `timelock_escape_guarantee` — admin changes are
  immediate in this model, so there is no escape window);
* `handleStressEvent` rewrites `totalCollateralValue` (and raises the emergency
  flag), and — once the flag is up — `catastrophicBackstop` publishes
  `redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD`, repricing
  all *future* redemptions (including RFQ redemptions executed against a user's
  outstanding request by a counterparty) — quantifying that channel is Tier 2's T6
  `oracle_blast_radius`; the backstop simultaneously pays the entire USDC reserve
  out to apxUSD holders pro-rata (credit-only; the model.md compensation leg);
* `setYieldRate`/`setVestPeriod` distort future yield accrual timing. -/

/-- Exact effect of `addToWhitelist`. -/
theorem step_addToWhitelist_exact (s : State) (a : Address) (caller : Address) (s' : State)
    (h : step s (Op.addToWhitelist a) caller = some s') :
    caller = s.admin ∧
    s' = { s with whitelist := fun x => if x = a then true else s.whitelist x } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `removeFromWhitelist`. -/
theorem step_removeFromWhitelist_exact (s : State) (a : Address) (caller : Address) (s' : State)
    (h : step s (Op.removeFromWhitelist a) caller = some s') :
    caller = s.admin ∧
    s' = { s with whitelist := fun x => if x = a then false else s.whitelist x } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `addToDenylist`. -/
theorem step_addToDenylist_exact (s : State) (a : Address) (caller : Address) (s' : State)
    (h : step s (Op.addToDenylist a) caller = some s') :
    caller = s.admin ∧
    s' = { s with denylist := fun x => if x = a then true else s.denylist x } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `removeFromDenylist`. -/
theorem step_removeFromDenylist_exact (s : State) (a : Address) (caller : Address) (s' : State)
    (h : step s (Op.removeFromDenylist a) caller = some s') :
    caller = s.admin ∧
    s' = { s with denylist := fun x => if x = a then false else s.denylist x } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `setYieldRate` (also surfaces its cadence guard). -/
theorem step_setYieldRate_exact (s : State) (bps : Nat) (caller : Address) (s' : State)
    (h : step s (Op.setYieldRate bps) caller = some s') :
    caller = s.admin ∧ s.lastRateSetTime + monthPeriod ≤ s.now ∧
    bps ≤ s.collateralYieldBase ∧
    s' = { s with yieldRateMonth := bps
                  lastRateSetTime := s.now
                  collateralYieldBase := overcollateralizationBuffer s } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2.1, hc.2.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `handleStressEvent`. -/
theorem step_handleStressEvent_exact (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.handleStressEvent amount) caller = some s') :
    caller = s.admin ∧
    s' = { s with totalCollateralValue := s.totalCollateralValue - amount
                  emergencyFlag := true } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `catastrophicBackstop`: it demands the admin role AND the
governance emergency flag already set in the pre-state (the backstop cannot raise
the flag for itself — model.md guard "Governance emergency flag set"); it reprices
every claim to track collateral (`redemptionValue := totalCollateralValue * ray /
totalSupply_apxUSD`, the per-token `ray` fixed-point form), distributes the entire
USDC reserve pro-rata to apxUSD holders, and zeroes the reserve and the recorded
overcollateralization buffer. -/
theorem step_catastrophicBackstop_exact (s : State) (caller : Address) (s' : State)
    (h : step s Op.catastrophicBackstop caller = some s') :
    caller = s.admin ∧ s.emergencyFlag = true ∧
    s' = { s with
             redemptionValue := (s.totalCollateralValue * ray) / s.totalSupply_apxUSD
             usdcBal := fun a =>
               s.usdcBal a + (s.usdcReserve * s.apxUSDBal a) / s.totalSupply_apxUSD
             usdcReserve := 0
             overcollateralizationBuffer := 0 } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `setVestPeriod`: it demands the admin role and, like
`creditYield`, is accrue-first — it realizes the currently-streamed portion of
the vest into `fullyVestedAmount` before reconfiguring the period, so
reconfiguring never forfeits already-streamed yield (cf. `Apyx.lean`'s
`req_configurable_vesting_period`). -/
theorem step_setVestPeriod_exact (s : State) (p : Nat) (caller : Address) (s' : State)
    (h : step s (Op.setVestPeriod p) caller = some s') :
    caller = s.admin ∧
    s' = { s with
             fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
             vestTotal := s.vestTotal - newlyVestedAmount s s.now
             vestStart := s.now
             vestPeriod := p } := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i hc
      exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-- T3 (single step, frame form): an admin-gated operation demands the admin role
and agrees with the pre-state on **every** field other than the ten
admin-parameter fields (`whitelist`, `denylist`, `yieldRateMonth`,
`lastRateSetTime`, `collateralYieldBase`, `totalCollateralValue`,
`redemptionValue`, `emergencyFlag`, `vestPeriod`, `overcollateralizationBuffer`),
the three vest-clock accumulator fields `setVestPeriod` also touches
(`vestStart`, `vestTotal`, `fullyVestedAmount` — accrue-first, same pattern as
`creditYield`; see `step_setVestPeriod_exact`), and the two USDC fields the
backstop's compensation leg touches (`usdcBal`, `usdcReserve` — the pro-rata
distribution of the reserve to holders; see `step_catastrophicBackstop_exact`).
In particular no apxUSD/apyUSD balance, supply, vault-custody, or unlock-registry
field is reachable from the admin role, and the only USDC movement is the
backstop's credit-only payout (`admin_cannot_touch_balances` pins its direction). -/
theorem admin_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : AdminOp op) (h_step : step s op caller = some s') :
    caller = s.admin ∧
    ∀ wl dl yr lt cy tcv rv ef vp vs vt fv ub ur ob,
      { s' with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                lastRateSetTime := lt, collateralYieldBase := cy,
                totalCollateralValue := tcv, redemptionValue := rv,
                emergencyFlag := ef, vestPeriod := vp,
                vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
                usdcBal := ub, usdcReserve := ur, overcollateralizationBuffer := ob }
    = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
               lastRateSetTime := lt, collateralYieldBase := cy,
               totalCollateralValue := tcv, redemptionValue := rv,
               emergencyFlag := ef, vestPeriod := vp,
               vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
               usdcBal := ub, usdcReserve := ur, overcollateralizationBuffer := ob } := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨bps, rfl⟩ | ⟨amt, rfl⟩ | rfl | ⟨p, rfl⟩ |
    ⟨v, rfl⟩ | ⟨amt, r, rfl⟩ := h_gated
  · obtain ⟨hc, rfl⟩ := step_addToWhitelist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_removeFromWhitelist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_addToDenylist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_removeFromDenylist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, -, -, rfl⟩ := step_setYieldRate_exact s bps caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_handleStressEvent_exact s amt caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, -, rfl⟩ := step_catastrophicBackstop_exact s caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_setVestPeriod_exact s p caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · -- `updateRedemptionValue`: writes only `redemptionValue`, already outside the frame.
    simp only [step] at h_step
    repeat' split at h_step
    · exact absurd h_step (by simp)
    · rename_i hc _
      cases Option.some.inj h_step
      exact ⟨by simpa using hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · exact absurd h_step (by simp)
  · -- `withdrawReserve`: writes only `usdcBal` and `usdcReserve`, both outside the frame.
    simp only [step] at h_step
    repeat' split at h_step
    · exact absurd h_step (by simp)
    · rename_i hc _
      cases Option.some.inj h_step
      exact ⟨by simpa using hc, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · exact absurd h_step (by simp)

/-- T3 `admin_cannot_touch_balances` (docs/05-blast-radius.md, Tier 1) — the
single-step balance-field form.

Threat model: the `admin` key is fully compromised. The operations gated on
`caller = s.admin` in `step` are exactly the eight of `AdminOp`: `addToWhitelist`,
`removeFromWhitelist`, `addToDenylist`, `removeFromDenylist`, `setYieldRate`,
`handleStressEvent`, `catastrophicBackstop`, and `setVestPeriod`.

Claim: none of these operations debits anyone — every apxUSD and apyUSD balance,
both total supplies, and the vault's apxUSD holdings are bitwise unchanged; every
USDC balance is non-decreasing (pointwise); and the USDC reserve is non-increasing.
The one admin operation that moves USDC at all is `catastrophicBackstop`, whose
model.md-mandated compensation leg pays the entire reserve **out to apxUSD holders
pro-rata** — a credit-only distribution (and only under a pre-set emergency flag);
every other `AdminOp` leaves both USDC fields bitwise unchanged. A compromised
admin cannot *directly* move or destroy a single unit of anyone's funds — the only
reachable movement is reserve → holders, never holder → anywhere.

Scope note (what is NOT claimed): the admin can still attack *future liveness and
economics* — denylisting/de-whitelisting blocks a user's future deposits and
redemptions, `setVestPeriod`/`setYieldRate` distort future yield accrual, and
`handleStressEvent`/`catastrophicBackstop` rewrite `totalCollateralValue`/
`redemptionValue`, changing the USDC value paid out by *future* redemptions. Those are
parameter attacks on future operations (Tier 2/Tier 3 territory, cf. T6/T8 in the
memo), not direct debits of recorded holdings — which is precisely the honest scope of
this theorem. -/
theorem admin_cannot_touch_balances (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : AdminOp op) (h_step : step s op caller = some s') :
    s'.apxUSDBal = s.apxUSDBal ∧
    s'.apyUSDBal = s.apyUSDBal ∧
    (∀ a, s.usdcBal a ≤ s'.usdcBal a) ∧
    s'.totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    s'.vaultApxUSDBal = s.vaultApxUSDBal ∧
    s'.usdcReserve ≤ s.usdcReserve := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨bps, rfl⟩ | ⟨amt, rfl⟩ | rfl | ⟨p, rfl⟩ |
    ⟨v, rfl⟩ | ⟨amt, r, rfl⟩ := h_gated
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` and
    -- `Op.withdrawReserve` have two each.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step;
            exact ⟨rfl, rfl, fun _ => Nat.le_add_right _ _, rfl, rfl, rfl, Nat.zero_le _⟩)
        | (cases Option.some.inj h_step;
            exact ⟨rfl, rfl, fun _ => Nat.le_refl _, rfl, rfl, rfl, Nat.le_refl _⟩)
        -- `withdrawReserve`: the admin's second USDC channel. Still credit-only pointwise
        -- (the named receiver gains, nobody is debited) and still reserve-non-increasing,
        -- so the theorem survives — but the reserve now falls for a reason other than the
        -- backstop's pro-rata payout.
        | (cases Option.some.inj h_step;
            refine ⟨rfl, rfl, fun _ => ?_, rfl, rfl, rfl, Nat.sub_le _ _⟩;
            dsimp only; split <;> omega)
        | exact absurd h_step (by simp)

/-- T3 (trace form): an arbitrarily long attack trace consisting solely of
admin-gated operations leaves every field outside the ten admin-parameter fields,
the three vest-clock accumulator fields, and the backstop's two USDC
compensation-leg fields (`usdcBal`, `usdcReserve`) unchanged. A compromised admin
key can rewrite access lists and pricing/schedule parameters (and, once the
emergency flag is up, pay the reserve out to holders via the backstop) — with the
deferred consequences listed in the section header — but cannot move a single unit
of any apxUSD/apyUSD balance, supply, vault custody, or unlock position, and its
only USDC channel is the backstop's credit-only pro-rata payout
(`admin_cannot_touch_balances`). -/
theorem admin_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, AdminOp p.1) :
    ∀ wl dl yr lt cy tcv rv ef vp vs vt fv ub ur ob,
      { execTrace s σ with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                           lastRateSetTime := lt, collateralYieldBase := cy,
                           totalCollateralValue := tcv, redemptionValue := rv,
                           emergencyFlag := ef, vestPeriod := vp,
                           vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
                           usdcBal := ub, usdcReserve := ur,
                           overcollateralizationBuffer := ob }
    = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
               lastRateSetTime := lt, collateralYieldBase := cy,
               totalCollateralValue := tcv, redemptionValue := rv,
               emergencyFlag := ef, vestPeriod := vp,
               vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
               usdcBal := ub, usdcReserve := ur,
               overcollateralizationBuffer := ob } := by
  induction σ generalizing s with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    intro wl dl yr lt cy tcv rv ef vp vs vt fv ub ur ob
    have h_tail : ∀ q ∈ σ, AdminOp q.1 := fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail wl dl yr lt cy tcv rv ef vp vs vt fv ub ur ob
    | some s1 =>
      obtain ⟨-, hframe⟩ :=
        admin_frame s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      calc { execTrace s1 σ with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                                 lastRateSetTime := lt, collateralYieldBase := cy,
                                 totalCollateralValue := tcv, redemptionValue := rv,
                                 emergencyFlag := ef, vestPeriod := vp,
                                 vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
                                 usdcBal := ub, usdcReserve := ur,
                                 overcollateralizationBuffer := ob }
          = { s1 with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                      lastRateSetTime := lt, collateralYieldBase := cy,
                      totalCollateralValue := tcv, redemptionValue := rv,
                      emergencyFlag := ef, vestPeriod := vp,
                      vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
                      usdcBal := ub, usdcReserve := ur,
                      overcollateralizationBuffer := ob } :=
            ih s1 h_tail wl dl yr lt cy tcv rv ef vp vs vt fv ub ur ob
        _ = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                     lastRateSetTime := lt, collateralYieldBase := cy,
                     totalCollateralValue := tcv, redemptionValue := rv,
                     emergencyFlag := ef, vestPeriod := vp,
                     vestStart := vs, vestTotal := vt, fullyVestedAmount := fv,
                     usdcBal := ub, usdcReserve := ur,
                     overcollateralizationBuffer := ob } :=
            hframe wl dl yr lt cy tcv rv ef vp vs vt fv ub ur ob

/-! ## Oracle role: direct frame (the indirect channel is Tier 2's T6)

The oracle's two operations are `updateRedemptionValue` (a no-op placeholder in
this model — notably, `redemptionValue` is writable only through the admin's
`catastrophicBackstop`) and `setApxUSDMarketPrice`. Their *direct* blast radius is
exactly the reported market-price field; the security-relevant channel is indirect:
`apxUSDMarketPrice` gates the arbitrage mint pathway (`ray < apxUSDMarketPrice` in
`Op.mintApxUSD`), which still takes 1 USDC per apxUSD minted from the *minter*.
Quantifying worst-case extraction through mispricing is T6 (`oracle_blast_radius`,
Tier 2). -/

/-- Exact effect of `updateRedemptionValue`: demands the oracle role, rejects zero, and
publishes the supplied value verbatim as the new redemption price.

Until the clock work this case was a no-op placeholder, which made `catastrophicBackstop`
the sole writer of `redemptionValue` and left an honest-operations price move — the thing
an RFQ counterparty would time its execution against — inexpressible. The deployed setters
(`ApxUSDRateOracle.setRate`, `RedemptionPoolV0.setExchangeRate`) enforce exactly one
condition, `newRate != 0`; there is no cap, floor, bounded per-update move or cadence, so
the model does not invent one either. -/
theorem step_updateRedemptionValue_exact (s : State) (newValue : Nat) (caller : Address)
    (s' : State) (h : step s (Op.updateRedemptionValue newValue) caller = some s') :
    caller = s.admin ∧ newValue ≠ 0 ∧ s' = { s with redemptionValue := newValue } := by
  simp only [step] at h
  split at h
  · rename_i hc
    split at h
    · exact absurd h (by simp)
    · rename_i hz
      exact ⟨by simpa using hc, hz, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `setApxUSDMarketPrice`: demands the oracle role and overrides
only the reported market price. -/
theorem step_setApxUSDMarketPrice_exact (s : State) (price : Nat) (caller : Address) (s' : State)
    (h : step s (Op.setApxUSDMarketPrice price) caller = some s') :
    caller = s.oracle ∧ s' = { s with apxUSDMarketPrice := price } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Oracle frame (single step): an oracle-gated operation demands the oracle role and
agrees with the pre-state on every field other than `apxUSDMarketPrice`.

The redemption price is **not** in this frame, and the reason is a source-tracing correction
rather than a modelling choice: `Roles.assignAdminTargetsFor` assigns
`RedemptionPoolV0.setExchangeRate` to `ADMIN_ROLE`, and the deployment's own access-control
suite pins it (`RedemptionPool/Access.t.sol::test_RevertWhen_SetExchangeRateNotAdmin`). The
oracle role publishes the reported market price and nothing else. -/
theorem oracle_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : OracleOp op) (h_step : step s op caller = some s') :
    caller = s.oracle ∧
    ∀ mp, { s' with apxUSDMarketPrice := mp } = { s with apxUSDMarketPrice := mp } := by
  obtain ⟨price, rfl⟩ := h_gated
  obtain ⟨hc, rfl⟩ := step_setApxUSDMarketPrice_exact s price caller s' h_step
  exact ⟨hc, fun _ => rfl⟩

/-- Oracle trace form: an arbitrarily long attack trace consisting solely of
oracle-gated operations changes nothing except the reported market price. The
oracle's entire direct blast radius is one price field; all asset movement it can
cause is mediated by *other* parties' subsequent operations (T6, Tier 2). -/
theorem oracle_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, OracleOp p.1) :
    ∀ mp, { execTrace s σ with apxUSDMarketPrice := mp }
        = { s with apxUSDMarketPrice := mp } := by
  induction σ generalizing s with
  | nil => intro _; rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    intro mp
    have h_tail : ∀ q ∈ σ, OracleOp q.1 := fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail mp
    | some s1 =>
      obtain ⟨-, hframe⟩ :=
        oracle_frame s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      calc { execTrace s1 σ with apxUSDMarketPrice := mp }
          = { s1 with apxUSDMarketPrice := mp } := ih s1 h_tail mp
        _ = { s with apxUSDMarketPrice := mp } := hframe mp

/-! ## T4: the non-custodial invariants and the trace headline

First the single-step non-custodial invariants for the three fungible balances
(apxUSD, apyUSD shares, external USDC) — by total case analysis over every
operation — then the two remaining asset classes (governance tokens, unlock
positions), and finally the trace-level statement that is the memo's headline. -/

/-- T4 `no_role_transfers_user_funds` (docs/05-blast-radius.md, Tier 1) — the
non-custodial invariant for apxUSD.

Threat model: ANY set of privileged keys (admin, oracle, pauseController,
yieldDistributor, governance — all of them at once) is compromised, e.g. the whole team
is phished. Can the attacker move an arbitrary user's apxUSD?

Claim: total case analysis over every operation shows that if any address `a`'s apxUSD
balance strictly decreased across a successful step, then either
* `a` was the caller of that very operation (the debit was self-initiated: `lockApxUSD`,
  `requestUnlock`, `flexibleRequestUnlock`, or `redeemApxUSD` spending the caller's own
  tokens), or
* the operation was `executeRFQRedemption a amount` — the single carve-out — in which
  case the caller was an approved RFQ counterparty, the amount was covered by **`a`'s
  own outstanding RFQ redemption request** (`amount ≤ rfqRequests a` — the request
  registry `Op.submitRFQRequest` fills; a counterparty cannot execute against a user
  who has not asked), and `a` was *simultaneously compensated in the same step* with
  the full redemption payout (`amount * redemptionValue / ray` USDC credited to `a`'s
  USDC balance).

No privileged role has any pathway to debit an arbitrary user's apxUSD: pause/unpause,
list management, rate/period setting, yield crediting, oracle updates, stress handling,
and the backstop all leave every apxUSD balance unchanged (they fall into the
contradiction branch of this proof; the backstop's compensation leg touches only USDC,
credit-only).

Carve-out honesty: `executeRFQRedemption` genuinely debits a non-caller, so the naive
"only the caller can be debited" claim is FALSE of this model and is not what we prove.
The carve-out is a *user-requested swap*, not a theft — it settles the debited user's
own pending request, atomically paying the corresponding USDC at the recorded
`redemptionValue`. Note that a compromised admin can first move `redemptionValue` via
`catastrophicBackstop` (only under a pre-set emergency flag; and RFQ counterparty
onboarding is not itself an `Op`, so `rfqCounterparties` is effectively static
in-model); pricing the worst case of that combination is exactly Tier 2's
`oracle_blast_radius` (T6), not this theorem. -/
theorem no_role_transfers_user_funds (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (a : Address)
    (h_dec : s'.apxUSDBal a < s.apxUSDBal a) :
    a = caller ∨
    ∃ amount, op = Op.executeRFQRedemption a amount ∧
      s.rfqCounterparties.contains caller = true ∧
      amount ≤ s.rfqRequests a ∧
      s'.usdcBal a = s.usdcBal a + (amount * s.redemptionValue) / ray := by
  cases op
  case poolRedeem amount receiver minOut =>
    -- The on-chain settlement leg burns `burnFrom(msg.sender)`: the only apxUSD it can debit
    -- is the redeemer's own. It cannot reach a third party's balance at all — unlike
    -- `executeRFQRedemption`, which models the documented process and debits the *user*.
    simp only [step] at h_step
    repeat' split at h_step
    all_goals first
      | (cases Option.some.inj h_step
         by_cases hac : a = caller
         · exact Or.inl hac
         · exact absurd h_dec (by simp [burnApxUSD, hac]))
      | exact absurd h_step (by simp)
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, mintApxUSD] at h_dec
    split at h_dec <;> omega
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, mintApxUSD] at h_dec
    split at h_dec <;> omega
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, hac] at h_dec
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [createStandardUnlock, burnApxUSD, hac] at h_dec
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT] at h_dec
    split at h_dec <;> omega
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [emitEvent, burnApxUSD, hac] at h_dec
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [createFlexibleUnlock, burnApxUSD, hac] at h_dec
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT] at h_dec
    split at h_dec <;> omega
  case executeRFQRedemption user amount =>
    obtain ⟨_, hrfq, _, hreq, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    by_cases hau : a = user
    · subst hau
      refine Or.inr ⟨amount, rfl, hrfq, hreq, ?_⟩
      simp [burnApxUSD]
    · exfalso
      simp [burnApxUSD, hau] at h_dec
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` has two.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; exact absurd h_dec (Nat.lt_irrefl _))
        | exact absurd h_step (by simp)

/-- T4 companion — the non-custodial invariant for apyUSD (vault shares).

Threat model: as in `no_role_transfers_user_funds`, arbitrary role compromise.

Claim: if any address `a`'s apyUSD share balance strictly decreased across a successful
step, then `a` itself was the caller. Here the statement needs NO carve-out at all: the
only operations that ever burn apyUSD are `withdraw` and `redeem`, and both burn
exclusively from the caller. No privileged role — and no RFQ counterparty — can debit
anyone else's vault shares. -/
theorem no_role_burns_user_shares (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (a : Address)
    (h_dec : s'.apyUSDBal a < s.apyUSDBal a) :
    a = caller := by
  rcases req_token_no_rebase s op caller s' h_step a (Nat.ne_of_lt h_dec) with
    ⟨x, rfl⟩ | ⟨x, r, rfl⟩ | ⟨x, r, rfl⟩
  · -- lockApxUSD only mints apyUSD (to the caller); a strict decrease is impossible
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] at h_dec
    split at h_dec <;> omega
  · -- withdraw burns shares from the caller only
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hac] at h_dec
  · -- redeem burns shares from the caller only
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hac] at h_dec

/-- T4 companion — the non-custodial invariant for external USDC balances.

Threat model: as in `no_role_transfers_user_funds`, arbitrary role compromise.

Claim: if any address `a`'s USDC balance strictly decreased across a successful step,
then `a` itself was the caller — again with NO carve-out. The only operations that ever
debit a USDC balance are `depositUSDC` and the arbitrage `mintApxUSD`, and both spend
exclusively the caller's USDC (every other operation, including both redemption payouts
and `executeRFQRedemption`, only *credits* USDC balances or leaves them unchanged). -/
theorem no_role_debits_usdc (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (a : Address)
    (h_dec : s'.usdcBal a < s.usdcBal a) :
    a = caller := by
  cases op
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, mintApxUSD, hac] at h_dec
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, mintApxUSD, hac] at h_dec
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] at h_dec
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [createStandardUnlock, burnApxUSD] at h_dec
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT] at h_dec
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, burnApxUSD] at h_dec
    split at h_dec <;>
      first
        | exact absurd h_dec (Nat.not_lt.mpr (Nat.le_add_right _ _))
        | exact absurd h_dec (Nat.lt_irrefl _)
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [createFlexibleUnlock, burnApxUSD] at h_dec
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT] at h_dec
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [burnApxUSD] at h_dec
    split at h_dec <;>
      first
        | exact absurd h_dec (Nat.not_lt.mpr (Nat.le_add_right _ _))
        | exact absurd h_dec (Nat.lt_irrefl _)
  case catastrophicBackstop =>
    -- the backstop's compensation leg only *credits* USDC balances (pro-rata
    -- distribution of the reserve), so a strict decrease is impossible
    obtain ⟨-, -, hs'⟩ := step_catastrophicBackstop_exact _ _ _ h_step
    subst hs'
    exact absurd h_dec (Nat.not_lt.mpr (Nat.le_add_right _ _))
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` and
    -- `Op.withdrawReserve` have two each.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; exact absurd h_dec (Nat.lt_irrefl _))
        -- `withdrawReserve` credits its named receiver and debits nobody, so no USDC
        -- balance falls. (The *reserve* falls — that is `reserve_outflow_only_via_redemption`.)
        | (cases Option.some.inj h_step; revert h_dec; dsimp only; split <;> omega)
        | exact absurd h_step (by simp)

/-- T4 companion — governance-token immutability: **no** operation, by **any**
caller, ever changes **any** address's governance-token balance. The model has no
transfer/mint/burn pathway for the governance token at all, so this holding is
untouchable even under total key compromise. -/
theorem governance_token_balances_immutable (s : State) (op : Op) (caller : Address)
    (s' : State) (h_step : step s op caller = some s') :
    s'.governanceTokenBal = s.governanceTokenBal := by
  cases op
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, mintApxUSD]
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    simp [createStandardUnlock, burnApxUSD]
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    simp [emitEvent, burnApxUSD]
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    simp [createFlexibleUnlock, burnApxUSD]
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    simp [burnApxUSD]
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` has two.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; rfl)
        | exact absurd h_step (by simp)

/-- Local copy of `Apyx.lean`'s private fee-cap lemma: the flexible-unlock fee never
exceeds the 3.5% (350 bps) starting level. -/
private theorem fee_le_start (rt now : Nat) : flexibleUnlockFee rt now ≤ 350 := by
  unfold flexibleUnlockFee
  dsimp only
  repeat' split
  all_goals first
    | omega
    | exact Nat.max_le.mpr ⟨Nat.sub_le _ _, by omega⟩

/-- T4 companion — unlock positions cannot be seized. If address `u` holds a live
unlock position `id` (recorded below the id counter, as every position created by
`step` is) and **anyone other than `u`** — any compromised role, including the
UnlockToken operator — executes any operation, then either

* the position is completely untouched (same owner, same amount), or
* the operation was the operator settling that very position **to its owner**:
  a standard claim pays `u` the full recorded amount, and a flexible claim pays `u`
  the recorded amount minus the published early-exit fee, which is capped at
  350 bps of the position — the worst-case damage of an operator-key compromise
  per position is 3.5%, and only for positions sitting in a flexible request.

No pathway re-assigns a position to another owner or destroys it without paying
its owner. -/
theorem no_role_seizes_unlock_position (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (id : Nat) (u : Address)
    (h_live : s.unlockTokenOwner id = some u)
    (h_fresh : id < s.nextUnlockId)
    (h_not_owner : caller ≠ u)
    (h_wf : ∀ i, s.unlockRequestId caller = some i → s.unlockTokenOwner i = some caller) :
    (s'.unlockTokenOwner id = some u ∧ s'.unlockTokenAmount id = s.unlockTokenAmount id) ∨
    (op = Op.claimUnlock id ∧ caller = s.unlockTokenOperator ∧
      ∃ amount cooldownEnd, s.unlockRequests id = some (u, amount, cooldownEnd) ∧
        cooldownEnd ≤ s.now ∧
        s'.apxUSDBal u = s.apxUSDBal u + amount) ∨
    (op = Op.flexibleClaimUnlock id ∧ caller = s.unlockTokenOperator ∧
      ∃ amount requestTime cooldownEnd,
        s.flexibleUnlockRequests id = some (u, amount, requestTime, cooldownEnd) ∧
        requestTime + minFlexibleClaim ≤ s.now ∧
        s'.apxUSDBal u = s.apxUSDBal u
          + (amount - amount * flexibleUnlockFee requestTime s.now / 10000) ∧
        amount * flexibleUnlockFee requestTime s.now / 10000 ≤ amount * 350 / 10000) := by
  have h_ne_next : id ≠ s.nextUnlockId := Nat.ne_of_lt h_fresh
  cases op
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [emitEvent, mintApxUSD] using h_live, by simp [emitEvent, mintApxUSD]⟩
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [emitEvent, mintApxUSD] using h_live, by simp [emitEvent, mintApxUSD]⟩
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] using h_live,
      by simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]⟩
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    refine Or.inl ⟨?_, ?_⟩
    · rw [inv_requestUnlock_owner_of_ne s caller amount h_ne_next]; exact h_live
    · exact inv_requestUnlock_amount_of_other s caller amount id u h_ne_next h_live h_not_owner h_wf
  case claimUnlock rid =>
    obtain ⟨o, am, ce, hreq, howner, hcaller, hnow, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    by_cases hrid : rid = id
    · subst hrid
      have hou : o = u := by
        rw [h_live] at howner
        exact (Option.some.inj howner).symm
      subst hou
      have hop : caller = s.unlockTokenOperator := by
        rcases hcaller with h | h
        · exact absurd h h_not_owner
        · exact h
      refine Or.inr (Or.inl ⟨rfl, hop, am, ce, hreq, hnow, ?_⟩)
      simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]
    · have h_ne : id ≠ rid := fun h => hrid h.symm
      exact Or.inl ⟨by simpa [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT, h_ne] using h_live,
        by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT, h_ne]⟩
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [emitEvent, burnApxUSD] using h_live, by simp [emitEvent, burnApxUSD]⟩
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD,
        h_ne_next] using h_live,
      by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, h_ne_next]⟩
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD,
        h_ne_next] using h_live,
      by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, h_ne_next]⟩
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [createFlexibleUnlock, burnApxUSD, h_ne_next] using h_live,
      by simp [createFlexibleUnlock, burnApxUSD, h_ne_next]⟩
  case flexibleClaimUnlock rid =>
    obtain ⟨o, am, rt, ce, hreq, howner, hcaller, hnow, hs'⟩ := inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    by_cases hrid : rid = id
    · subst hrid
      have hou : o = u := by
        rw [h_live] at howner
        exact (Option.some.inj howner).symm
      subst hou
      have hop : caller = s.unlockTokenOperator := by
        rcases hcaller with h | h
        · exact absurd h h_not_owner
        · exact h
      refine Or.inr (Or.inr ⟨rfl, hop, am, rt, ce, hreq, hnow, ?_, ?_⟩)
      · simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]
      · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (fee_le_start rt s.now))
    · have h_ne : id ≠ rid := fun h => hrid h.symm
      exact Or.inl ⟨by simpa [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT, h_ne] using h_live,
        by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT, h_ne]⟩
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [burnApxUSD] using h_live, by simp [burnApxUSD]⟩
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` has two.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; exact Or.inl ⟨h_live, rfl⟩)
        | exact absurd h_step (by simp)

/-- T4 headline (trace form) — total-compromise immunity for passive users.

Threat model: **every** privileged key at once — admin, oracle, pauseController,
yieldDistributor, governance, plus any number of ordinary accounts — is controlled
by the attacker, who runs an arbitrarily long trace of operations. The only
assumptions are that user `u` signs nothing in the trace (`u` is never a caller)
and that no approved RFQ counterparty executes an RFQ redemption *against `u`*
(that compensated-swap pathway is priced separately; cf.
`no_role_transfers_user_funds` and T6).

Claim: none of `u`'s four recorded holdings can decrease — apxUSD, apyUSD vault
shares, external USDC, and governance tokens (the last is bitwise unchanged). The
team being fully phished cannot move your balances. -/
theorem user_assets_immune_to_total_key_compromise
    (s : State) (σ : List (Op × Address)) (u : Address)
    (h_u : ∀ p ∈ σ, p.2 ≠ u)
    (h_rfq : ∀ p ∈ σ, ∀ amount, p.1 ≠ Op.executeRFQRedemption u amount) :
    s.apxUSDBal u ≤ (execTrace s σ).apxUSDBal u ∧
    s.apyUSDBal u ≤ (execTrace s σ).apyUSDBal u ∧
    s.usdcBal u ≤ (execTrace s σ).usdcBal u ∧
    (execTrace s σ).governanceTokenBal u = s.governanceTokenBal u := by
  induction σ generalizing s with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, rfl⟩
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have h_u_tail : ∀ q ∈ σ, q.2 ≠ u := fun q hq => h_u q (List.mem_cons_of_mem _ hq)
    have h_rfq_tail : ∀ q ∈ σ, ∀ amount, q.1 ≠ Op.executeRFQRedemption u amount :=
      fun q hq => h_rfq q (List.mem_cons_of_mem _ hq)
    have hcu : ¬ u = c := fun h => h_u (op, c) List.mem_cons_self h.symm
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_u_tail h_rfq_tail
    | some s1 =>
      obtain ⟨ih_apx, ih_apy, ih_usdc, ih_gov⟩ := ih s1 h_u_tail h_rfq_tail
      have h_apx : s.apxUSDBal u ≤ s1.apxUSDBal u := by
        rcases Nat.lt_or_ge (s1.apxUSDBal u) (s.apxUSDBal u) with hlt | hge
        · rcases no_role_transfers_user_funds s op c s1 hstep u hlt with
            huc | ⟨amount, hop, -, -, -⟩
          · exact absurd huc hcu
          · exact absurd hop (h_rfq (op, c) List.mem_cons_self amount)
        · exact hge
      have h_apy : s.apyUSDBal u ≤ s1.apyUSDBal u := by
        rcases Nat.lt_or_ge (s1.apyUSDBal u) (s.apyUSDBal u) with hlt | hge
        · exact absurd (no_role_burns_user_shares s op c s1 hstep u hlt) hcu
        · exact hge
      have h_usdc : s.usdcBal u ≤ s1.usdcBal u := by
        rcases Nat.lt_or_ge (s1.usdcBal u) (s.usdcBal u) with hlt | hge
        · exact absurd (no_role_debits_usdc s op c s1 hstep u hlt) hcu
        · exact hge
      have h_gov : s1.governanceTokenBal u = s.governanceTokenBal u :=
        congrFun (governance_token_balances_immutable s op c s1 hstep) u
      exact ⟨Nat.le_trans h_apx ih_apx, Nat.le_trans h_apy ih_apy,
        Nat.le_trans h_usdc ih_usdc, ih_gov.trans h_gov⟩

/-! ## Toward Tier 2 (T5 `no_theft_ledger` / T6 `oracle_blast_radius`)

Two single-step characterizations that are the induction steps for the Tier-2
ledger arguments. They also settle the *attribution* question for T6 in this model:
the redemption price is not an oracle-controlled quantity at all — it is writable
exclusively by the admin's `catastrophicBackstop` (the model's `updateRedemptionValue`
writes `redemptionValue` (it was a placeholder no-op in an earlier revision; `step_updateRedemptionValue_exact` and `admin_alone_moves_redemption_price` now pin its effect)). The real-world analogue (Yearn's finding that Apyx's
`ApxUSDRateOracle.setRate` sits behind a 0-second timelock) therefore maps to the
*admin coalition* here: worst case, `handleStressEvent` drives
`totalCollateralValue` to 0 (raising the emergency flag the backstop requires) and
`catastrophicBackstop` publishes `redemptionValue = 0 * ray / supply = 0`, after
which an approved RFQ counterparty can settle users' **outstanding RFQ requests**
at zero USDC. Pricing that coalition is T10's table; the theorems below pin
down the only channels through which it can act. -/

/-- **Who can write the redemption price.** Exhaustive over `Op`: a step that changes
`redemptionValue` was one of exactly two operations.

* `catastrophicBackstop` — admin role, governance emergency flag already up, and the new
  value forced to the per-token collateral price `totalCollateralValue * ray /
  totalSupply_apxUSD`. A *loud* write: the same step zeroes the reserve and the buffer.
* `updateRedemptionValue v` — **also the admin role**, `v` arbitrary and merely non-zero. A
  *quiet* write: no side effect anywhere else in the state.

Both writers are the same key. `Roles.assignAdminTargetsFor` puts
`RedemptionPoolV0.setExchangeRate` under `ADMIN_ROLE`, and the deployment's own
`RedemptionPool/Access.t.sol::test_RevertWhen_SetExchangeRateNotAdmin` pins it there, so the
earlier reading of this theorem — that reaching the redemption price at all required an
emergency — was an artifact of the model, not a property of the protocol.

The second disjunct did not exist while `updateRedemptionValue` was a no-op placeholder,
and its absence is what made the earlier "admin-only" reading of this theorem possible.
It does not hold on-chain: `ApxUSDRateOracle.setRate` and
`RedemptionPoolV0.setExchangeRate` are role-gated setters whose only guard is
`newRate != 0`, with no cap, floor, bounded move or cadence. Any blast-radius claim that
treats the redemption price as reachable only under an emergency has to carry this
disjunct. -/
theorem redemption_price_writers (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_changed : s'.redemptionValue ≠ s.redemptionValue) :
    (op = Op.catastrophicBackstop ∧ caller = s.admin ∧ s.emergencyFlag = true ∧
      s'.redemptionValue = (s.totalCollateralValue * ray) / s.totalSupply_apxUSD)
    ∨ (∃ v, op = Op.updateRedemptionValue v ∧ caller = s.admin ∧ v ≠ 0 ∧
      s'.redemptionValue = v) := by
  cases op
  case catastrophicBackstop =>
    obtain ⟨hc, hf, rfl⟩ := step_catastrophicBackstop_exact s caller s' h_step
    exact Or.inl ⟨rfl, hc, hf, rfl⟩
  case updateRedemptionValue v =>
    obtain ⟨hc, hz, rfl⟩ := step_updateRedemptionValue_exact s v caller s' h_step
    exact Or.inr ⟨v, rfl, hc, hz, rfl⟩
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [emitEvent, mintApxUSD]) h_changed
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [emitEvent, mintApxUSD]) h_changed
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]) h_changed
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [createStandardUnlock, burnApxUSD]) h_changed
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]) h_changed
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [emitEvent, burnApxUSD]) h_changed
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD])
      h_changed
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD])
      h_changed
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [createFlexibleUnlock, burnApxUSD]) h_changed
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]) h_changed
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [burnApxUSD]) h_changed
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` has two.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; exact absurd rfl h_changed)
        | exact absurd h_step (by simp)

/-- The original admin-only characterization, kept under its own name and now carrying the
hypothesis that makes it true: rule the oracle's own setter out and the backstop is the
only remaining writer. Reports citing this must state the exclusion. -/
theorem redemption_price_admin_only (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_not_oracle_setter : ∀ v, op ≠ Op.updateRedemptionValue v)
    (h_changed : s'.redemptionValue ≠ s.redemptionValue) :
    op = Op.catastrophicBackstop ∧ caller = s.admin ∧ s.emergencyFlag = true ∧
    s'.redemptionValue = (s.totalCollateralValue * ray) / s.totalSupply_apxUSD := by
  rcases redemption_price_writers s op caller s' h_step h_changed with h | ⟨v, hv, -, -, -⟩
  · exact h
  · exact absurd hv (h_not_oracle_setter v)

/-- Reserve outflows happen only through redemption **or the catastrophic
backstop's wind-down distribution**. On the redemption paths, every unit that
leaves the reserve is paid to the address whose apxUSD is simultaneously burned,
priced at the recorded `redemptionValue` — via `redeemApxUSD` (self-initiated) or
`executeRFQRedemption` (counterparty-initiated against the user's outstanding RFQ
request, same pricing). The backstop path is the model.md-mandated compensation
leg: admin-triggered under a pre-set emergency flag, it zeroes the reserve while
crediting **every** holder its exact pro-rata share — a credit-only distribution
that burns nothing. This is the induction step for T5's no-theft ledger: USDC
never exits a user's column, and it exits the reserve only against a matching
burn of the payee or as the wind-down payout to all holders. -/
theorem reserve_outflow_only_via_redemption (s : State) (op : Op) (caller : Address)
    (s' : State) (h_step : step s op caller = some s')
    (h_dec : s'.usdcReserve < s.usdcReserve) :
    (∃ user amount,
      ((op = Op.redeemApxUSD amount ∧ user = caller) ∨
        op = Op.executeRFQRedemption user amount) ∧
      amount ≤ s.apxUSDBal user ∧
      s'.apxUSDBal user = s.apxUSDBal user - amount ∧
      s'.usdcBal user = s.usdcBal user + amount * s.redemptionValue / ray ∧
      s'.usdcReserve = s.usdcReserve - amount * s.redemptionValue / ray ∧
      s'.totalSupply_apxUSD = s.totalSupply_apxUSD - amount) ∨
    (op = Op.catastrophicBackstop ∧ caller = s.admin ∧ s.emergencyFlag = true ∧
      s'.usdcReserve = 0 ∧
      (∀ b, s'.usdcBal b
        = s.usdcBal b + (s.usdcReserve * s.apxUSDBal b) / s.totalSupply_apxUSD) ∧
      s'.apxUSDBal = s.apxUSDBal ∧
      s'.totalSupply_apxUSD = s.totalSupply_apxUSD) ∨
    -- The third exit, and the one that is not a redemption at all: an admin withdrawal
    -- straight out of the reserve. Mirrors `RedemptionPoolV0.withdraw`/`withdrawTokens`
    -- (`ADMIN_ROLE` per `Roles.assignAdminTargetsFor`). Nothing is burned, no claim is
    -- settled, no holder is compensated — the reserve simply moves to a named address.
    (∃ amount receiver, op = Op.withdrawReserve amount receiver ∧ caller = s.admin ∧
      s'.usdcReserve = s.usdcReserve - amount ∧
      s'.usdcBal receiver = s.usdcBal receiver + amount) ∨
    -- The on-chain settlement leg. It *is* a redemption, but the burn and the credit land on
    -- different addresses: `burnFrom(msg.sender)` takes the redeemer's apxUSD and the USDC goes
    -- to a `receiver` the redeemer names. The holder is neither, until they have handed their
    -- tokens over — so the price protection on this path (`minOut`) is the redeemer's, not theirs.
    (∃ amount receiver minOut, op = Op.poolRedeem amount receiver minOut ∧
      s.rfqCounterparties.contains caller = true ∧
      s'.apxUSDBal caller = s.apxUSDBal caller - amount ∧
      s'.usdcBal receiver = s.usdcBal receiver + amount * s.redemptionValue / ray ∧
      s'.usdcReserve = s.usdcReserve - amount * s.redemptionValue / ray) := by
  cases op
  case poolRedeem amount receiver minOut =>
    simp only [step] at h_step
    repeat' split at h_step
    all_goals first
      | (cases Option.some.inj h_step
         refine Or.inr (Or.inr (Or.inr ⟨amount, receiver, minOut, rfl, ?_, ?_, ?_, ?_⟩)) <;>
           simp_all [burnApxUSD])
      | exact absurd h_step (by simp)
  case redeemApxUSD amount =>
    obtain ⟨_, _, hbal, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨caller, amount, Or.inl ⟨rfl, rfl⟩, hbal,
      by simp [emitEvent, burnApxUSD],
      by simp [emitEvent, burnApxUSD],
      by simp [emitEvent, burnApxUSD],
      by simp [emitEvent, burnApxUSD]⟩
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hbal, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨user, amount, Or.inr rfl, hbal,
      by simp [burnApxUSD],
      by simp [burnApxUSD],
      by simp [burnApxUSD],
      by simp [burnApxUSD]⟩
  case catastrophicBackstop =>
    obtain ⟨hc, hf, hs'⟩ := step_catastrophicBackstop_exact _ _ _ h_step
    subst hs'
    exact Or.inr (Or.inl ⟨rfl, hc, hf, rfl, fun b => rfl, rfl, rfl⟩)
  case depositUSDC amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [emitEvent, mintApxUSD] <;> omega)
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [emitEvent, mintApxUSD] <;> omega)
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD])
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [createStandardUnlock, burnApxUSD])
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT])
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    exact absurd h_dec
      (by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD])
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    exact absurd h_dec
      (by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD])
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [createFlexibleUnlock, burnApxUSD])
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    exact absurd h_dec (by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT])
  case withdrawReserve amount receiver =>
    simp only [step] at h_step
    repeat' split at h_step
    · exact absurd h_step (by simp)
    · rename_i hc _
      cases Option.some.inj h_step
      exact Or.inr (Or.inr (Or.inl ⟨amount, receiver, rfl, by simpa using hc, rfl, by simp⟩))
    · exact absurd h_step (by simp)
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` has two.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; exact absurd h_dec (by simp <;> omega))
        | exact absurd h_step (by simp)

/-! ## T5 `no_theft_ledger` — first-principles conservation for a passive bystander

The trace-level unification of T4: a fixed victim address `a` who **signs nothing**
(never a caller anywhere in `σ`) and is **never the user-argument of an
`executeRFQRedemption`** anywhere in `σ` cannot lose any of their transferable
holdings, no matter what operations — including every privileged-role operation, in
any order — the attacker interleaves around them. This is the memo's headline "even
if the whole team is phished, your balance can't be moved," stated over the whole
trace.

Ledger design (per Task 2): rather than adding a ledger field to `State` (which would
touch the ground-truth 81-theorem file), the ledger is a **module-local derived
function over the trace state** — `netHoldings`, the sum of an address's three
transferable balances. Conservation is then "`netHoldings` is non-decreasing across
the trace for the passive `a`", proved by combining the three per-field bounds. The
governance token is separately, absolutely immutable
(`governance_token_balances_immutable`), so it is not part of the mutable ledger. -/

/-- The per-address transferable-holdings ledger: the sum of an address's apxUSD,
apyUSD vault shares, and external USDC. A module-local derived quantity over the
trace state — no field is added to `State`. -/
def netHoldings (s : State) (a : Address) : Nat :=
  s.apxUSDBal a + s.apyUSDBal a + s.usdcBal a

/-- T5 `no_theft_ledger` (docs/05-blast-radius.md, Tier 2) — no-theft conservation
for a passive bystander.

Threat model: **every** privileged key at once (admin, oracle, pauseController,
yieldDistributor, governance) plus any number of ordinary accounts is the attacker,
running an arbitrarily long trace `σ`. Two carve-outs, stated as hypotheses:
`h_never_signs` (`a` is never a caller in `σ`) and `h_never_rfq_target` (`a` is
never the user-argument of an `executeRFQRedemption` — the one compensated-swap
pathway that can debit a non-caller; a priced swap, not theft; pricing it is T6).

Claim: each of `a`'s three transferable balances is non-decreasing across the
entire trace, hence so is the derived ledger `netHoldings` — proved by lifting the
single-step non-custodial lemmas through the trace via
`user_assets_immune_to_total_key_compromise`. -/
theorem no_theft_ledger (s : State) (σ : List (Op × Address)) (a : Address)
    (h_never_signs : ∀ p ∈ σ, p.2 ≠ a)
    (h_never_rfq_target : ∀ p ∈ σ, ∀ amount, p.1 ≠ Op.executeRFQRedemption a amount) :
    s.apxUSDBal a ≤ (execTrace s σ).apxUSDBal a ∧
    s.apyUSDBal a ≤ (execTrace s σ).apyUSDBal a ∧
    s.usdcBal a ≤ (execTrace s σ).usdcBal a ∧
    netHoldings s a ≤ netHoldings (execTrace s σ) a := by
  obtain ⟨hapx, hapy, husdc, _⟩ :=
    user_assets_immune_to_total_key_compromise s σ a h_never_signs h_never_rfq_target
  refine ⟨hapx, hapy, husdc, ?_⟩
  unfold netHoldings
  omega

/-! ## T6 `oracle_blast_radius` — what an oracle-key compromise can extract

Two honest results.

**(a)** The oracle key acting *alone* extracts exactly zero: a trace of only
`OracleOp`s (`updateRedemptionValue`/`setApxUSDMarketPrice`) moves no balance,
supply, or reserve — its entire footprint is the reported market-price parameter
`apxUSDMarketPrice`. (`oracle_alone_preserves_balances`, from the oracle trace frame.)

**(b)** The danger is a *coalition*, and the finding is that **the model places no
clamp on the redemption price**, so the USDC paid out on a single redeem is unbounded
above — there is no in-model invariant capping it. We prove this positively:

* `redeem_payout_formula`: a successful `redeemApxUSD amount` pays the caller exactly
  `amount * redemptionValue / ray` USDC out of the reserve;
* `redeem_payout_has_no_cap`: for **any** target `N`, there is a state and a
  *single-token* redeem whose payout is `≥ N`. The witness fixes `amount = 1` and
  scales `redemptionValue` to `N * ray`, so one apxUSD is redeemed for `N` USDC. No
  guard in `redeemApxUSD` (nor in the price writer `catastrophicBackstop`, which sets
  `redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD` with no upper
  bound — cf. `redemption_price_admin_only`) bounds `redemptionValue`, so no upper
  bound on payout is provable: the absence of a model-level cap, itself the key finding.

This is exactly the memo's T6 conclusion "in the current clamp-free model f =
usdcReserve (full drain)" and the real-world analogue of Yearn's finding that Apyx's
`ApxUSDRateOracle.setRate` sits behind a 0-second timelock. It motivates Tier 3's
rate-limit / clamp. Attribution note (`redemption_price_admin_only`): in *this* model
the redemption price is written by the admin's `catastrophicBackstop`, not the oracle
op, so the extraction coalition is admin (price) + redeemer/RFQ-counterparty (drain);
`updateRedemptionValue` writes `redemptionValue` (it was a placeholder no-op in an earlier revision; `step_updateRedemptionValue_exact` and `admin_alone_moves_redemption_price` now pin its effect). -/

/-- T6(a) `oracle_alone_preserves_balances`: an arbitrarily long trace whose operations
are ALL oracle-gated leaves every balance, supply, and reserve field bitwise unchanged.
The oracle key acting alone extracts exactly zero — its only reachable field is the
reported market price `apxUSDMarketPrice` (`oracle_trace_blast_radius`), and the
redemption price in particular is untouched (`redemptionValue` unchanged) — because
writing it is an **admin** capability, not an oracle one
(`Roles.assignAdminTargetsFor`; see `admin_alone_moves_redemption_price` below). -/
theorem oracle_alone_preserves_balances (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, OracleOp p.1) :
    (execTrace s σ).apxUSDBal = s.apxUSDBal ∧
    (execTrace s σ).apyUSDBal = s.apyUSDBal ∧
    (execTrace s σ).usdcBal = s.usdcBal ∧
    (execTrace s σ).governanceTokenBal = s.governanceTokenBal ∧
    (execTrace s σ).usdcReserve = s.usdcReserve ∧
    (execTrace s σ).totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    (execTrace s σ).totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    (execTrace s σ).vaultApxUSDBal = s.vaultApxUSDBal ∧
    (execTrace s σ).vestTotal = s.vestTotal ∧
    (execTrace s σ).redemptionValue = s.redemptionValue := by
  have h := oracle_trace_blast_radius s σ h_gated 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg State.apxUSDBal h
  · simpa using congrArg State.apyUSDBal h
  · simpa using congrArg State.usdcBal h
  · simpa using congrArg State.governanceTokenBal h
  · simpa using congrArg State.usdcReserve h
  · simpa using congrArg State.totalSupply_apxUSD h
  · simpa using congrArg State.totalSupply_apyUSD h
  · simpa using congrArg State.vaultApxUSDBal h
  · simpa using congrArg State.vestTotal h
  · simpa using congrArg State.redemptionValue h

/-- **The admin's quiet route to the redemption price.** No emergency flag, no compromised
second key, no side effect anywhere else in the state: one step publishes any non-zero price.
No cap, no floor, no bounded per-update move, no cadence — the model now says exactly what
`RedemptionPoolV0.setExchangeRate` says, and the role it demands is the one
`Roles.assignAdminTargetsFor` assigns.

Contrast `catastrophicBackstop`, the admin's *loud* route: it needs the emergency flag, forces
the value to the pro-rata price, and zeroes the reserve and the buffer in the same step. Only
the loud one is visible to a monitor watching protocol state. -/
theorem admin_alone_moves_redemption_price (s : State) (v : Nat) (hv : v ≠ 0) :
    ∃ s', step s (Op.updateRedemptionValue v) s.admin = some s' ∧ s'.redemptionValue = v := by
  refine ⟨{ s with redemptionValue := v }, ?_, rfl⟩
  simp [step, hv]

/-- **And the admin's route out of the reserve, with no redemption at all.** Mirrors
`RedemptionPoolV0.withdraw` / `withdrawTokens`. Nothing is burned, no claim is settled: the
reserve simply moves to an address the admin names. This is the operation whose absence made
`reserve_outflow_only_via_redemption` read as an exhaustive account of reserve exits. -/
theorem admin_alone_drains_reserve (s : State) (amount : Nat) (r : Address)
    (h : amount ≤ s.usdcReserve) :
    ∃ s', step s (Op.withdrawReserve amount r) s.admin = some s' ∧
      s'.usdcReserve = s.usdcReserve - amount ∧ s'.usdcBal r = s.usdcBal r + amount := by
  refine ⟨{ s with usdcReserve := s.usdcReserve - amount,
                   usdcBal := fun a => if a = r then s.usdcBal a + amount else s.usdcBal a },
          ?_, rfl, ?_⟩ <;> simp [step, Nat.not_lt.mpr h]

/-- T6(b), payout formula: a successful `redeemApxUSD amount` credits the caller
exactly `amount * redemptionValue / ray` USDC (removed from the reserve) against a burn
of `amount` apxUSD. The payout is a bare linear function of the redemption price with
no cap term — the object of the no-cap witness below. (Specialization of
`reserve_outflow_only_via_redemption` to the self-service path.) -/
theorem redeem_payout_formula (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') :
    s'.usdcBal caller = s.usdcBal caller + amount * s.redemptionValue / ray ∧
    s'.usdcReserve = s.usdcReserve - amount * s.redemptionValue / ray ∧
    s'.apxUSDBal caller = s.apxUSDBal caller - amount := by
  obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
  subst hs'
  refine ⟨?_, ?_, ?_⟩ <;> simp [emitEvent, burnApxUSD]

/-- Witness state for `redeem_payout_has_no_cap`: defaults except a whitelisted holder
of one apxUSD, a reserve of `N`, and a redemption price of `N * ray` (i.e. `N` dollars
per apxUSD). One apxUSD redeems for `N` USDC. -/
private def noCapWitness (N : Nat) : State :=
  { (default : State) with
      -- set explicitly: `default` is not a reliable source for fields a
      -- witness depends on (`Regression.lean` §R11)
      denylist := fun _ => false,
      whitelist := fun _ => true
      apxUSDBal := fun _ => 1
      redemptionValue := N * ray
      usdcReserve := N }

/-- T6(b), the finding: **the single-redeem payout has no upper bound in the model.**

For any target `N`, there is a state and a single-token (`amount = 1`) redemption whose
USDC payout to the redeemer is at least `N`: the witness sets `redemptionValue = N * ray`
(everything else at defaults, whitelisted caller with one apxUSD and an `N`-unit
reserve), so one apxUSD redeems for `N` USDC. Because `redeemApxUSD` has **no guard**
bounding `redemptionValue`, and its only writer `catastrophicBackstop` sets it to the
unbounded `totalCollateralValue * ray / totalSupply_apxUSD`
(`redemption_price_admin_only`), there is no
in-model invariant capping the payout — no upper bound is provable, because none
exists. This is the honest T6 result: in the current clamp-free model the extractable
amount is limited only by the reserve, motivating a Tier-3 rate-limit / price clamp.

(Not a claim that the model is *wrong*: it is a faithful mirror of a real design whose
rate oracle has a 0-second timelock. The theorem *characterizes the missing cap*.) -/
theorem redeem_payout_has_no_cap (N : Nat) :
    ∃ (s s' : State) (amount : Nat) (caller : Address),
      step s (Op.redeemApxUSD amount) caller = some s' ∧
      s.usdcBal caller = 0 ∧
      N ≤ s'.usdcBal caller := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  have hpay : (1 : Nat) * (N * ray) / ray = N := by
    rw [Nat.one_mul, Nat.mul_div_cancel _ hray]
  have h0 : (noCapWitness N).usdcBal 0 = 0 := rfl
  have hrv : (noCapWitness N).redemptionValue = N * ray := rfl
  have hts : (default : State).totalSupply_apxUSD = 0 := rfl
  have htc : (default : State).totalCollateralValue = 0 := rfl
  cases hs : step (noCapWitness N) (Op.redeemApxUSD 1) 0 with
  | none =>
      -- all guards pass on the witness (price 0 < ray, buffer stays at 0), so it cannot revert
      simp [noCapWitness, step, overcollateralizationBuffer, hts, htc] at hs
      rw [Nat.mul_div_cancel N hray] at hs
      exact absurd (hs rfl hray) (Nat.lt_irrefl _)
  | some s' =>
      refine ⟨noCapWitness N, s', 1, 0, hs, h0, ?_⟩
      obtain ⟨hbal, _, _⟩ := redeem_payout_formula (noCapWitness N) 1 0 s' hs
      rw [hbal, h0, hrv, Nat.one_mul, Nat.mul_div_cancel _ hray]
      omega

/-! ## Active no-extraction: every apxUSD credit is backed (caller-side dual of T5)

T5 (`no_theft_ledger`) bounds what a *passive* victim who never signs can lose:
nothing. This section is the **active** complement: an attacker who DOES sign — with
any keys, including every privileged role at once — cannot create apxUSD value from
nothing. Exhaustive case analysis over the closed `step` shows the model has **no
`step` case that mints apxUSD to an address without either an equal USDC payment
into the reserve or the settlement of that address's own pre-existing recorded
locked position** — no free-mint path exists for any caller. Cite together with T5:
passive users cannot lose (T5), active callers cannot gain unbacked value (this).

RFQ carve-out note: `executeRFQRedemption` never *credits* apxUSD (it burns the
user's apxUSD and pays USDC), so it does not appear in the credit disjunction at
all. Its USDC leg is priced at the admin-controlled `redemptionValue` with no cap
(`redeem_payout_has_no_cap`, T6) and is exactly the outflow channel tracked by
`reserve_outflow_only_via_redemption` — the unbounded coalition channel is USDC
*outflow* at a corrupted price, never apxUSD *creation*. -/

/-- Active no-extraction, single step: **every apxUSD credit is backed**.

Threat model: arbitrary caller (any compromised role, or any ordinary account).
If any address `a`'s apxUSD balance strictly increased across a successful step,
total case analysis over `step` shows the operation is one of exactly three backed
channels:

1. **Paid mint** — `depositUSDC amount` (with `a` the caller) or `mintApxUSD a amount`
   (the arbitrage mint to `a`): the credit is exactly `amount`, and in the *same
   atomic step* the **caller paid `amount` USDC** — the caller held at least `amount`
   USDC, their balance is debited by `amount`, and the reserve grows by `amount`.
   Strict 1:1 backing; no free value for anyone (for the arbitrage mint the payer is
   the caller, so a mint directed at a third party is a gift from the caller, not a
   mint from nothing).
2. **Standard claim** — `claimUnlock id` settling a recorded unlock position **owned
   by `a`** (`unlockRequests id = some (a, amount, _)` and
   `unlockTokenOwner id = some a`, cooldown elapsed): the credit is exactly the
   recorded `amount`, i.e. value `a` locked earlier via the apxUSD burns in
   `requestUnlock`/`withdraw`/`redeem`.
3. **Flexible claim** — `flexibleClaimUnlock id` settling `a`'s recorded flexible
   position: the credit is the recorded amount *minus* the early-exit fee, hence
   never exceeds the recorded amount.

No other case credits apxUSD: `lockApxUSD`, `requestUnlock`, `flexibleRequestUnlock`,
`redeemApxUSD`, and `executeRFQRedemption` only *burn* it, `withdraw`/`redeem` and
every role-gated operation leave every apxUSD balance unchanged (they land in the
contradiction branches of this proof).

This lemma is the induction step for the trace-level summed conservation
("`a`'s total apxUSD received across `execTrace` ≤ initial holdings + USDC paid in
+ own positions settled"); the summed form additionally needs a finite ledger of
`a`'s live unlock-position amounts (to price channels 2-3 at trace start) and is
left as the stated next step. -/
theorem apxUSD_credit_is_backed (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (a : Address)
    (h_inc : s.apxUSDBal a < s'.apxUSDBal a) :
    (∃ amount,
        ((op = Op.depositUSDC amount ∧ a = caller) ∨ op = Op.mintApxUSD a amount) ∧
        amount ≤ s.usdcBal caller ∧
        s'.usdcBal caller = s.usdcBal caller - amount ∧
        s'.usdcReserve = s.usdcReserve + amount ∧
        s'.apxUSDBal a = s.apxUSDBal a + amount) ∨
    (∃ id amount cooldownEnd,
        op = Op.claimUnlock id ∧
        s.unlockRequests id = some (a, amount, cooldownEnd) ∧
        s.unlockTokenOwner id = some a ∧
        cooldownEnd ≤ s.now ∧
        s'.apxUSDBal a = s.apxUSDBal a + amount) ∨
    (∃ id amount requestTime cooldownEnd,
        op = Op.flexibleClaimUnlock id ∧
        s.flexibleUnlockRequests id = some (a, amount, requestTime, cooldownEnd) ∧
        s.unlockTokenOwner id = some a ∧
        requestTime + minFlexibleClaim ≤ s.now ∧
        s'.apxUSDBal a
          = s.apxUSDBal a + (amount - amount * flexibleUnlockFee requestTime s.now / 10000) ∧
        s'.apxUSDBal a ≤ s.apxUSDBal a + amount) := by
  cases op
  case poolRedeem amount receiver minOut =>
    -- Settlement only ever burns apxUSD; no balance rises.
    simp only [step] at h_step
    repeat' split at h_step
    all_goals first
      | (cases Option.some.inj h_step
         by_cases hac : a = caller
         · subst hac; exact absurd h_inc (by simp [burnApxUSD])
         · exact absurd h_inc (by simp [burnApxUSD, hac]))
      | exact absurd h_step (by simp)
  case depositUSDC amount =>
    obtain ⟨_, _, _, hle, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · subst hac
      refine Or.inl ⟨amount, Or.inl ⟨rfl, rfl⟩, hle, ?_, ?_, ?_⟩ <;>
        simp [emitEvent, mintApxUSD]
    · exfalso
      simp [emitEvent, mintApxUSD, hac] at h_inc
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, hle, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    by_cases hat : a = to
    · subst hat
      refine Or.inl ⟨amount, Or.inr rfl, hle, ?_, ?_, ?_⟩ <;>
        simp [emitEvent, mintApxUSD]
    · exfalso
      simp [emitEvent, mintApxUSD, hat] at h_inc
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] at h_inc
    split at h_inc <;> omega
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [createStandardUnlock, burnApxUSD] at h_inc
    split at h_inc <;> omega
  case claimUnlock id =>
    obtain ⟨o, am, ce, hreq, howner, hcaller, hnow, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    by_cases hao : a = o
    · subst hao
      exact Or.inr (Or.inl ⟨id, am, ce, rfl, hreq, howner, hnow,
        by simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]⟩)
    · exfalso
      simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT, hao] at h_inc
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, burnApxUSD] at h_inc
    split at h_inc <;> omega
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_inc
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_inc
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    exfalso
    simp [createFlexibleUnlock, burnApxUSD] at h_inc
    split at h_inc <;> omega
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, hreq, howner, hcaller, hnow, hs'⟩ :=
      inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    by_cases hao : a = o
    · subst hao
      have heq : (mintApxUSD (retireFlexibleUnlock s id) a
            (am - am * flexibleUnlockFee rt s.now / 10000)).apxUSDBal a
          = s.apxUSDBal a + (am - am * flexibleUnlockFee rt s.now / 10000) := by
        simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT]
      refine Or.inr (Or.inr ⟨id, am, rt, ce, rfl, hreq, howner, hnow, heq, ?_⟩)
      rw [heq]
      exact Nat.add_le_add_left (Nat.sub_le _ _) _
    · exfalso
      simp [mintApxUSD, retireStandardUnlock, retireFlexibleUnlock, burnUnlockNFT, hao] at h_inc
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [burnApxUSD] at h_inc
    split at h_inc <;> omega
  all_goals
    simp only [step] at h_step
    -- `repeat'`: `Op.tick` has no guard to split on, `Op.updateRedemptionValue` has two.
    (repeat' split at h_step) <;>
      first
        | (cases Option.some.inj h_step; exact absurd h_inc (Nat.lt_irrefl _))
        | exact absurd h_step (by simp)

/-! ## T7 `rate_limit_linear_bound` — a per-window outflow cap makes damage linear in time

**DESIGN theorem** (docs/05-blast-radius.md, Tier 3): this section models the defence
mechanism itself — an ERC-7265-style circuit breaker that caps USDC reserve outflow per
window of elapsed time — and proves what it would guarantee. The base Apyx model has **no**
such limiter (per T6's `redeem_payout_has_no_cap`, one corrupted-price redemption can drain
the whole reserve), so this is a statement about the *value of adopting the mechanism*, not a
property of the current protocol.

**The clock is the base clock.** An earlier version of this wrapper carried its own
`RLOp.advanceEpoch` action — free, permissionless, and unrelated to `base.now` — so the bound
counted markers the attacker had put in their own trace and did **not** mean "linear in
elapsed time". That was the defect `code_review_lean.md` §1.2 recorded. The wrapper now has no
clock of its own: it steps on plain base operations, and the allowance is *derived* from
`base.now`, which only `Op.tick` moves. `docs/06` §7.3's E1 asks for exactly this — the clock
in `Op`, with `execTrace` advancing it — so the wrapper is now an instance of E1 rather than a
parallel mechanism beside it.

Headline (`rate_limit_linear_bound`): over an arbitrary trace, cumulative reserve outflow is
at most `cap * (elapsed / window + 1)` where `elapsed = base.now - t0` — one allowance for the
window in progress plus one for each completed window. That is the memo's
`userLoss(t) ≤ cap × ⌈t/window⌉`. -/

/-- Rate-limited wrapper state: the untouched base `State`, the clock reading at which the
limiter was installed, the window length and per-window allowance (policy parameters `step2`
never changes), and the cumulative outflow charged since `t0`. -/
structure RLState where
  base : State
  /-- `base.now` when the limiter was installed. Immutable. -/
  t0 : Nat
  /-- Window length in clock units. Immutable. -/
  window : Nat
  /-- Allowance released per window. Immutable. -/
  cap : Nat
  /-- Cumulative reserve outflow charged since `t0`. -/
  spent : Nat

/-- The allowance the **clock** has released: one `cap` for the window in progress plus one
for every window completed since `t0`. It depends on `base.now` and the three immutable
parameters and on nothing else — in particular no action raises it directly. -/
def allowance (rs : RLState) : Nat := rs.cap * ((rs.base.now - rs.t0) / rs.window + 1)

/-- What one base step costs the protocol's holders, as the meter charges it.

Two quantities matter and they are not the same. `usdcReserve - usdcReserve'` is value that left
the reserve — a transfer out. `totalSupply_apxUSD - totalSupply_apxUSD'` is claims destroyed,
valued at par — what holders gave up. A fair redemption makes them equal. A redemption at a
crashed `redemptionValue` burns claims for **nothing**, so the reserve does not move and metering
outflow alone charges zero: that was the residual `code_review_lean.md` §1.2 recorded after the
clock fix, and it let a reprice-to-zero drain pass an arbitrarily tight limiter untouched.

Charging the **larger** of the two closes it while leaving honest traffic priced as before: a fair
redemption still costs its face value, `withdrawReserve` still costs what it moves, and a
zero-payout burn now costs the claims it destroyed.

Written with truncated subtraction rather than `Nat.max` so `omega` can see through it; the two
agree, which `stepCost_eq_max` records. -/
def stepCost (s s' : State) : Nat :=
  (s.usdcReserve - s'.usdcReserve)
    + ((s.totalSupply_apxUSD - s'.totalSupply_apxUSD) - (s.usdcReserve - s'.usdcReserve))

theorem stepCost_eq_max (s s' : State) :
    stepCost s s' = Nat.max (s.usdcReserve - s'.usdcReserve)
      (s.totalSupply_apxUSD - s'.totalSupply_apxUSD) := by
  unfold stepCost
  simp only [Nat.max_def]
  split <;> omega

/-- The meter always charges at least the reserve outflow. -/
theorem reserve_out_le_stepCost (s s' : State) :
    s.usdcReserve - s'.usdcReserve ≤ stepCost s s' := by unfold stepCost; omega

/-- …and at least the claims destroyed at par. This is the half that a reprice-to-zero drain
used to escape. -/
theorem claims_out_le_stepCost (s s' : State) :
    s.totalSupply_apxUSD - s'.totalSupply_apxUSD ≤ stepCost s s' := by unfold stepCost; omega

/-- Rate-limited step. The base operation runs unmodified; its cost (`stepCost`) is added to the
cumulative meter, and the operation **reverts** if the meter would pass the clock-derived
allowance. The allowance is evaluated at the *post*-state, so a trace that ticks the clock
forward and then spends is allowed exactly what the elapsed time buys. -/
def step2 (rs : RLState) (op : Op) (caller : Address) : Option RLState :=
  match step rs.base op caller with
  | none => none
  | some s' =>
    -- `allowance` at the post-state, inlined: the policy parameters are copied from `rs`, so
    -- only `now` differs. Written out so `split` can discharge the guard.
    if rs.cap * ((s'.now - rs.t0) / rs.window + 1)
        < rs.spent + stepCost rs.base s' then none
    else some { rs with
      base := s'
      spent := rs.spent + stepCost rs.base s' }

/-- Trace executor for the wrapper (revert-skip semantics, like `execTrace`). The trace is a
list of plain base operations: the wrapper contributes no clock action of its own. -/
def execTrace2 (rs : RLState) : List (Op × Address) → RLState
  | [] => rs
  | (op, c) :: τ =>
    match step2 rs op c with
    | some rs' => execTrace2 rs' τ
    | none => execTrace2 rs τ

private theorem execTrace2_cons_some (rs rs' : RLState) (op : Op) (c : Address)
    (τ : List (Op × Address)) (h : step2 rs op c = some rs') :
    execTrace2 rs ((op, c) :: τ) = execTrace2 rs' τ := by
  simp [execTrace2, h]

private theorem execTrace2_cons_none (rs : RLState) (op : Op) (c : Address)
    (τ : List (Op × Address)) (h : step2 rs op c = none) :
    execTrace2 rs ((op, c) :: τ) = execTrace2 rs τ := by
  simp [execTrace2, h]

/-- The three policy parameters are immutable. -/
private theorem step2_params (rs rs' : RLState) (op : Op) (c : Address)
    (h : step2 rs op c = some rs') :
    rs'.t0 = rs.t0 ∧ rs'.window = rs.window ∧ rs'.cap = rs.cap := by
  simp only [step2] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases Option.some.inj h; exact ⟨rfl, rfl, rfl⟩

private theorem execTrace2_params (rs : RLState) (τ : List (Op × Address)) :
    (execTrace2 rs τ).t0 = rs.t0 ∧ (execTrace2 rs τ).window = rs.window ∧
      (execTrace2 rs τ).cap = rs.cap := by
  induction τ generalizing rs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons p τ ih =>
    obtain ⟨op, c⟩ := p
    cases hstep : step2 rs op c with
    | none => rw [execTrace2_cons_none rs op c τ hstep]; exact ih rs
    | some rs1 =>
      rw [execTrace2_cons_some rs rs1 op c τ hstep]
      obtain ⟨h1, h2, h3⟩ := ih rs1
      obtain ⟨g1, g2, g3⟩ := step2_params rs rs1 op c hstep
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3⟩

/-- **The meter never passes the allowance the clock has released.** This is the limiter's own
invariant, and it is where the time-derived bound comes from. -/
theorem rl_spent_le_allowance (rs : RLState) (τ : List (Op × Address))
    (h : rs.spent ≤ allowance rs) :
    (execTrace2 rs τ).spent ≤ allowance (execTrace2 rs τ) := by
  induction τ generalizing rs with
  | nil => exact h
  | cons p τ ih =>
    obtain ⟨op, c⟩ := p
    cases hstep : step2 rs op c with
    | none => rw [execTrace2_cons_none rs op c τ hstep]; exact ih rs h
    | some rs1 =>
      rw [execTrace2_cons_some rs rs1 op c τ hstep]
      refine ih rs1 ?_
      simp only [step2] at hstep
      split at hstep
      · exact absurd hstep (by simp)
      · split at hstep
        · exact absurd hstep (by simp)
        · rename_i hg
          cases Option.some.inj hstep
          simpa [allowance] using Nat.not_lt.mp hg

/-- Cumulative reserve outflow is bounded by the meter: every step charges its own decrease,
and steps that raise the reserve are charged nothing. -/
private theorem rl_outflow_le_spent (rs : RLState) (τ : List (Op × Address)) :
    rs.base.usdcReserve - (execTrace2 rs τ).base.usdcReserve + rs.spent
      ≤ (execTrace2 rs τ).spent := by
  induction τ generalizing rs with
  | nil => simp [execTrace2]
  | cons p τ ih =>
    obtain ⟨op, c⟩ := p
    cases hstep : step2 rs op c with
    | none => rw [execTrace2_cons_none rs op c τ hstep]; exact ih rs
    | some rs1 =>
      rw [execTrace2_cons_some rs rs1 op c τ hstep]
      have hih := ih rs1
      simp only [step2] at hstep
      split at hstep
      · exact absurd hstep (by simp)
      · split at hstep
        · exact absurd hstep (by simp)
        · cases Option.some.inj hstep
          simp only at hih
          simp only [stepCost] at hih ⊢
          omega

/-- T7 `rate_limit_linear_bound` (docs/05-blast-radius.md, Tier 3) — **the rate limiter caps
cumulative loss linearly in elapsed time**, with "elapsed" meaning the base clock.

Threat model: the attacker holds **every** key and submits an arbitrary trace of base
operations with any callers. They may include `Op.tick` freely — that is the point. Ticking
buys allowance, but it also *is* the passage of time, so the allowance it buys is exactly what
the mechanism promises for that much time. No action available to the attacker raises the
allowance without advancing `base.now`.

Claim: net USDC reserve outflow over the whole run is at most `cap * (elapsed / window + 1)`,
where `elapsed` is the base clock's advance. Within any single window the attacker can sequence
redemptions however they like (including at an admin-corrupted `redemptionValue`, cf. T6); the
gate reverts anything past the allowance. This is the design value of an ERC-7265-style
breaker: it buys detection and response time. -/
theorem rate_limit_linear_bound (rs : RLState) (τ : List (Op × Address))
    (h : rs.spent ≤ allowance rs) :
    rs.base.usdcReserve - (execTrace2 rs τ).base.usdcReserve
      ≤ rs.cap * (((execTrace2 rs τ).base.now - rs.t0) / rs.window + 1) := by
  have h1 := rl_outflow_le_spent rs τ
  have h2 := rl_spent_le_allowance rs τ h
  obtain ⟨p1, p2, p3⟩ := execTrace2_params rs τ
  unfold allowance at h2
  rw [p1, p2, p3] at h2
  omega

/-- T7, fresh-wrapper corollary: installing the limiter with an empty meter at the base state's
current clock reading, any attack trace's reserve outflow is at most
`cap * (elapsed / window + 1)`. -/
theorem rate_limit_linear_bound_fresh (base0 : State) (window cap : Nat)
    (τ : List (Op × Address)) :
    base0.usdcReserve - (execTrace2 ⟨base0, base0.now, window, cap, 0⟩ τ).base.usdcReserve
      ≤ cap * (((execTrace2 ⟨base0, base0.now, window, cap, 0⟩ τ).base.now - base0.now)
          / window + 1) :=
  rate_limit_linear_bound ⟨base0, base0.now, window, cap, 0⟩ τ (Nat.zero_le _)

/-! ## T8 `timelock_escape_guarantee` — Half 1: the base model has NO escape window

The memo's T8 asks for the escape-hatch guarantee "after a malicious privileged
change is queued, users have a `delay`-long window to exit before it lands." That
property cannot even be *stated* over the base Apyx model, because the base model
has no queue: every privileged operation takes effect **in the very step that
requests it**. The two theorems below characterize this absence precisely (this is
the honest negative result — the base model's timelock is zero seconds, exactly
Yearn's real-world finding about `ApxUSDRateOracle.setRate`); the wrapper in the
second half then *adds* the mechanism and proves what it buys. -/

/-- T8 Half 1, universal form: **privileged repricing is instantaneous in the base
model.** Whenever `catastrophicBackstop` (one of the two writers of the redemption price (`redemption_price_writers`; the other is `updateRedemptionValue`),
`redemption_price_admin_only`) succeeds, the new price is already in force in the
post-state of that same step, and the clock has not advanced by even one unit
(`s'.now = s.now`). There is no pending interval — no state in which the change is
"announced but not yet effective" — during which a user could still redeem at the
old price. Direct projection of `step_catastrophicBackstop_exact`. -/
theorem catastrophicBackstop_is_instantaneous (s : State) (caller : Address) (s' : State)
    (h : step s Op.catastrophicBackstop caller = some s') :
    caller = s.admin ∧ s'.now = s.now ∧
    s'.redemptionValue = (s.totalCollateralValue * ray) / s.totalSupply_apxUSD := by
  obtain ⟨hc, -, rfl⟩ := step_catastrophicBackstop_exact s caller s' h
  exact ⟨hc, rfl, rfl⟩

/-- T8 Half 1, witness form: `base_model_has_no_timelock`. There is a state in which
the admin's `catastrophicBackstop` succeeds, **actually changes** the redemption
price, and does so at an unchanged clock (`s'.now = s.now`) — zero elapsed time
between the request and the effect. Together with the universal form above this
shows the base model provably has no timelock on privileged repricing: the escape
window has length exactly 0. NOT a vacuous claim about an unreachable guard — the
witness step succeeds and the price moves. (The witness pre-sets the governance
emergency flag, since the document-faithful backstop only fires once the flag is
already up — the timelock finding is about the absence of a *delay between request
and effect*, which the flag guard does not add.) (Why this matters: the exit
guarantee of Half 2 is a property of the *queue mechanism*, so it must be proved of
a wrapper; any attempt to prove it of the base model is falsified by this witness.) -/
theorem base_model_has_no_timelock :
    ∃ (s s' : State),
      step s Op.catastrophicBackstop s.admin = some s' ∧
      s'.redemptionValue ≠ s.redemptionValue ∧
      s'.now = s.now := by
  -- The document-faithful backstop only fires once the emergency flag is already up, so the
  -- witness pre-sets it; the timelock finding is about the absence of a delay between request
  -- and effect, which the flag guard does not add. `totalSupply_apxUSD := ray` keeps the
  -- redemption-value arithmetic to `1 * ray / ray = 1 ≠ 0` (robust, no `10^27` `decide`).
  have hray : 0 < ray := Nat.pow_pos (by decide)
  refine ⟨{ (default : State) with
              emergencyFlag := true
              totalCollateralValue := 1
              totalSupply_apxUSD := ray }, _, rfl, ?_, rfl⟩
  show (1 : Nat) * ray / ray ≠ (0 : Nat)
  rw [Nat.one_mul, Nat.div_self hray]; decide

/-! ## T8 Half 2 — a timelock wrapper DOES give the escape guarantee (DESIGN theorem)

**DESIGN theorem** (like T7): this section models the defence mechanism itself — a
timelock queue for privileged operations — and proves the guarantee it would
provide. The base Apyx model has no such queue (Half 1 above), so everything here
is a statement about the *value of adopting the mechanism*, not a property of the
current protocol.

The wrapper adds no field to `State` (mirroring T7's `RLState`): `TLState` layers a
wrapper clock, a pending queue, and a fixed `delay` policy parameter over the
untouched base state. Privileged operations enter through `queue`, which only
*records* `(op, caller, tl.base.now)` — the base state is untouched, so users can still
transact (in particular exit) against the old parameters. `direct` runs a
**non-privileged** operation immediately, bypassing the queue: that is what makes the
escape window usable, and it is also the only way the clock moves, because `Op.tick`
is not an `AdminOp`. `execute i` runs the stored base operation via the unmodified base
`step`, and **reverts unless the entry's stamp is at least `delay` old on the base
clock** (`t₀ + delay ≤ base.now`).

Two defects of the earlier version are what this shape fixes
(`code_review_lean.md` §1.2):

* it carried its **own** clock field, advanced by a free `TLOp.tick` with no relation
  to `base.now` or `Op.tick`, so the guarantee counted wrapper tokens rather than
  elapsed time;
* `queue` accepted **any** operation and `execute` was the only route to the base
  state, so a user wanting to exit had to queue their own redemption and wait the same
  `delay` — by which time the attacker's earlier-queued change had already matured.
  The wrapper therefore did not provide the window its name claimed.

Headline (`timelock_escape_guarantee`): if an operation queued at the current instant
is later executed — after any further wrapper trace `τ` the attacker likes — then the
**base clock has advanced by at least `delay`** since the stamp. Since only `direct`
touches the base state before that point, and `direct` admits no privileged operation,
the pre-change parameters really are the ones in force throughout the window. -/

/-- Timelocked wrapper state: the untouched base `State` (whose `now` **is** the
wrapper's clock — there is no second one), the queue of pending privileged operations
— each entry `(op, caller, queuedAt)` stamped with the base clock reading at which it
was queued — and the fixed timelock length `delay` (a policy parameter; `step2tl` never
changes it). -/
structure TLState where
  base : State
  pending : List (Op × Address × Nat)
  delay : Nat

/-- Operations of the timelocked wrapper.

`queue` announces a privileged base operation (recording it without running it).
`direct op caller` runs a **non-privileged** operation at once — user traffic, and in
particular `Op.tick`, so the clock advances through the base `step` like everywhere
else. `execute i` attempts to run the `i`-th pending entry. -/
inductive TLOp
  | queue (op : Op) (caller : Address)
  | direct (op : Op) (caller : Address)
  | execute (i : Nat)

/-- Timelocked step.

`queue` appends `(op, caller, tl.base.now)` and does **not** run the operation.
`direct op caller` reverts if `op` is an `AdminOp` — privileged changes must go through
the queue — and otherwise runs the unmodified base `step`. `execute i` looks up the
`i`-th pending entry and reverts unless its stamp is at least `delay` old **on the base
clock** (`queuedAt + delay ≤ base.now`), in which case it runs the base `step` and
removes the entry. -/
def step2tl (tl : TLState) : TLOp → Option TLState
  | TLOp.queue op caller =>
    some { tl with pending := tl.pending ++ [(op, caller, tl.base.now)] }
  | TLOp.direct op caller =>
    if isAdminOp op then none
    else
      match step tl.base op caller with
      | none => none
      | some b' => some { tl with base := b' }
  | TLOp.execute i =>
    match tl.pending[i]? with
    | none => none
    | some (op, caller, t₀) =>
      if t₀ + tl.delay ≤ tl.base.now then
        match step tl.base op caller with
        | none => none
        | some b' => some { tl with base := b', pending := tl.pending.eraseIdx i }
      else none

/-- Trace executor for the timelocked wrapper (revert-skip semantics, like
`execTrace`/`execTrace2`). -/
def execTraceTL (tl : TLState) : List TLOp → TLState
  | [] => tl
  | o :: τ =>
    match step2tl tl o with
    | some tl' => execTraceTL tl' τ
    | none => execTraceTL tl τ

/-- Exact effect of `queue`: it always succeeds, appends the entry stamped with the
current **base** clock reading, and touches nothing else — in particular the base state
is bitwise unchanged, so announcing a privileged change applies none of it. -/
theorem step2tl_queue_exact (tl : TLState) (op : Op) (caller : Address) :
    step2tl tl (TLOp.queue op caller)
      = some { tl with pending := tl.pending ++ [(op, caller, tl.base.now)] } := rfl

/-- `direct` refuses privileged operations: the queue is the only route for those. -/
theorem step2tl_direct_rejects_privileged (tl : TLState) (op : Op) (caller : Address)
    (h : AdminOp op) : step2tl tl (TLOp.direct op caller) = none := by
  simp only [step2tl, (isAdminOp_iff op).mpr h, if_true]

/-- The clock advances through the base `step`, exactly as in the unwrapped model:
`Op.tick` is not privileged, so it is available via `direct`, and its effect is the
base one. -/
theorem step2tl_direct_tick (tl : TLState) (dt : Nat) (caller : Address) :
    step2tl tl (TLOp.direct (Op.tick dt) caller)
      = some { tl with base := { tl.base with now := tl.base.now + dt } } := by
  have hna : isAdminOp (Op.tick dt) = false := rfl
  simp only [step2tl, hna, if_false, step]
  rfl

private theorem inv_step2tl_execute (tl : TLState) (i : Nat) (tl' : TLState)
    (h : step2tl tl (TLOp.execute i) = some tl') :
    ∃ op caller t₀ b',
      tl.pending[i]? = some (op, caller, t₀) ∧
      t₀ + tl.delay ≤ tl.base.now ∧
      step tl.base op caller = some b' ∧
      tl' = { tl with base := b', pending := tl.pending.eraseIdx i } := by
  simp only [step2tl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i op caller t₀ heq
    split at h
    · rename_i ht
      split at h
      · exact absurd h (by simp)
      · rename_i b' hb
        exact ⟨op, caller, t₀, b', heq, ht, hb, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-- The base state moves only via `execute` and `direct`; `queue` never touches it. -/
theorem tl_base_untouched_by_queue (tl : TLState) (op : Op) (caller : Address)
    (tl' : TLState) (h : step2tl tl (TLOp.queue op caller) = some tl') :
    tl'.base = tl.base := by
  cases Option.some.inj (h.symm.trans (step2tl_queue_exact tl op caller)); rfl

private theorem execTraceTL_cons_some (tl tl' : TLState) (o : TLOp) (τ : List TLOp)
    (h : step2tl tl o = some tl') : execTraceTL tl (o :: τ) = execTraceTL tl' τ := by
  simp [execTraceTL, h]

private theorem execTraceTL_cons_none (tl : TLState) (o : TLOp) (τ : List TLOp)
    (h : step2tl tl o = none) : execTraceTL tl (o :: τ) = execTraceTL tl τ := by
  simp [execTraceTL, h]

/-- The timelock length is a constant of the wrapper: no wrapper operation changes
`delay`. -/
theorem execTraceTL_delay (tl : TLState) (τ : List TLOp) :
    (execTraceTL tl τ).delay = tl.delay := by
  induction τ generalizing tl with
  | nil => rfl
  | cons o τ ih =>
    cases h : step2tl tl o with
    | none => rw [execTraceTL_cons_none tl o τ h]; exact ih tl
    | some tl1 =>
      rw [execTraceTL_cons_some tl tl1 o τ h]
      have hd : tl1.delay = tl.delay := by
        cases o with
        | queue op caller =>
          cases Option.some.inj (h.symm.trans (step2tl_queue_exact tl op caller)); rfl
        | direct op caller =>
          simp only [step2tl] at h
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · cases Option.some.inj h; rfl
        | execute i =>
          obtain ⟨-, -, -, -, -, -, -, rfl⟩ := inv_step2tl_execute tl i tl1 h
          rfl
      exact (ih tl1).trans hd

/-- **`execute` cannot land early**, measured on the base clock. If the `i`-th pending
entry carries stamp `t₀` and its `execute` succeeds, then `t₀ + delay ≤ base.now`. -/
theorem tl_execute_requires_delay (tl : TLState) (i : Nat) (tl' : TLState)
    (op : Op) (c : Address) (t₀ : Nat)
    (h_entry : tl.pending[i]? = some (op, c, t₀))
    (h_exec : step2tl tl (TLOp.execute i) = some tl') :
    t₀ + tl.delay ≤ tl.base.now := by
  obtain ⟨op', c', t₀', -, heq, ht, -, -⟩ := inv_step2tl_execute tl i tl' h_exec
  rw [h_entry] at heq
  have h3 : op = op' ∧ c = c' ∧ t₀ = t₀' := by simpa using heq
  obtain ⟨-, -, h4⟩ := h3
  omega

/-- T8 `timelock_escape_guarantee` (docs/05-blast-radius.md, Tier 3) — **the timelock
wrapper provably gives a `delay`-long window of real elapsed time.**

DESIGN theorem: the base Apyx model has no timelock (`base_model_has_no_timelock` —
privileged repricing is instantaneous); this proves what adding the queue would buy.

Threat model: the attacker holds every key. At some reachable wrapper state they
`queue` a privileged base operation (e.g. `catastrophicBackstop`, stamped with the
current base clock reading), then submit **any** further wrapper trace `τ` — more
queues, direct user traffic, ticks and executes in any pattern — after which an
`execute` consuming that entry succeeds.

Claim: the base clock at that moment is at least `delay` past the stamp. Because the
clock lives in the base state and moves only through the base `step` (reached via
`direct`, which refuses every `AdminOp`), this is elapsed protocol time, not a count
of wrapper tokens. And `queue` leaves the base state bitwise unchanged
(`step2tl_queue_exact`, `tl_base_untouched_by_queue`), so throughout the window the
queued operation has contributed nothing — users transacting via `direct` are still
facing the pre-change parameters. Contrast Half 1, where the window has length 0. -/
theorem timelock_escape_guarantee (tl : TLState) (op : Op) (c : Address)
    (τ : List TLOp) (i : Nat) (tl' : TLState)
    (h_entry : (execTraceTL { tl with pending := tl.pending ++ [(op, c, tl.base.now)] } τ).pending[i]?
        = some (op, c, tl.base.now))
    (h_exec : step2tl (execTraceTL { tl with pending := tl.pending ++ [(op, c, tl.base.now)] } τ)
        (TLOp.execute i) = some tl') :
    tl.base.now + tl.delay
      ≤ (execTraceTL { tl with pending := tl.pending ++ [(op, c, tl.base.now)] } τ).base.now := by
  have h1 := tl_execute_requires_delay _ i tl' op c tl.base.now h_entry h_exec
  have h3 := execTraceTL_delay { tl with pending := tl.pending ++ [(op, c, tl.base.now)] } τ
  dsimp only at h3
  omega

/-- Non-vacuity of the wrapper: the escape guarantee is not achieved by making
`execute` unsatisfiable. A concrete run — queue the admin's `catastrophicBackstop`,
let `delay` of **base** time pass through `direct (Op.tick delay)`, then execute —
succeeds and actually changes the base redemption price. The timelock delays
privileged changes; it does not block them. -/
theorem timelock_wrapper_is_live :
    ∃ (tl : TLState) (τ : List TLOp),
      (execTraceTL tl τ).base.now = tl.base.now + tl.delay ∧
      (execTraceTL tl τ).base.redemptionValue ≠ tl.base.redemptionValue := by
  -- Document-faithful backstop fires only with the emergency flag already up (see
  -- `base_model_has_no_timelock`); the witness pre-sets it. `totalSupply_apxUSD := ray`
  -- makes the per-unit price land on `totalCollateralValue`, here 1.
  refine ⟨{ base := { (default : State) with
                        emergencyFlag := true
                        admin := 7
                        totalSupply_apxUSD := ray
                        totalCollateralValue := 1
                        redemptionValue := 0 }
            pending := []
            delay := 1 },
          [TLOp.queue Op.catastrophicBackstop 7, TLOp.direct (Op.tick 1) 0,
            TLOp.execute 0], ?_, ?_⟩
  · decide
  · decide

/-! ## T9 `compartmentalization` — a role compromise's footprint is confined to its subsystem

Base-model theorems (not wrapper/DESIGN): faithful field-level projections of the
Tier-1 trace frames, stating each compromise's blast radius as a *compartment*.

* The yield-distributor compartment is the **vesting pool and its USDC inflow**
  (`vestTotal`/`fullyVestedAmount`/`usdcReserve`/`vestStart`): an all-distributor
  trace leaves every principal field — user apxUSD/apyUSD/USDC/governance
  balances, both supplies, the vault's apxUSD, i.e. everything users own or that
  backs what they own — bitwise unchanged, the reserve cannot move at all
  (the role pays in, never out), and the combined vest pool
  `fullyVestedAmount + vestTotal` cannot move at all too (`vestTotal` alone
  is NOT monotone — an accrue-first credit can shrink it while growing
  `fullyVestedAmount` by the same amount, cf. T2's `yield_distributor_frame`). A
  distributor compromise can distort *future yield accrual timing*, never
  principal.
* The pauser compartment is the **`globalPause` liveness bit alone**: an all-pauser
  trace leaves every principal field *and* every pricing parameter unchanged. A
  pauser compromise is a freeze, never a loss. -/

/-- T9 `distributor_compartmentalized` (docs/05-blast-radius.md, Tier 3):
a yieldDistributor compromise is confined to the vesting-pool compartment.
Over any all-`DistributorOp` trace the principal fields are all bitwise unchanged,
the USDC reserve is untouched (it is a different contract on-chain), and the combined vest pool
`fullyVestedAmount + vestTotal` moves only upward (`vestTotal` alone can shrink
when an accrue-first credit realizes more into `fullyVestedAmount` than it adds —
see the section note above; `vestStart`, the vesting clock anchor, may also be
rewritten; that is the liveness caveat documented at T2). Projection of
`yield_distributor_trace_blast_radius`. -/
theorem distributor_compartmentalized (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, DistributorOp p.1) :
    (execTrace s σ).apxUSDBal = s.apxUSDBal ∧
    (execTrace s σ).apyUSDBal = s.apyUSDBal ∧
    (execTrace s σ).usdcBal = s.usdcBal ∧
    (execTrace s σ).governanceTokenBal = s.governanceTokenBal ∧
    (execTrace s σ).vaultApxUSDBal = s.vaultApxUSDBal ∧
    (execTrace s σ).totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    (execTrace s σ).totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    -- the reserve is now *untouched* by this role, not merely non-decreasing
    (execTrace s σ).usdcReserve = s.usdcReserve ∧
    s.fullyVestedAmount + s.vestTotal
      ≤ (execTrace s σ).fullyVestedAmount + (execTrace s σ).vestTotal := by
  obtain ⟨hframe, hres, hvest⟩ := yield_distributor_trace_blast_radius s σ h_gated
  have h := hframe 0 0 0 0
  exact ⟨by simpa using congrArg State.apxUSDBal h,
    by simpa using congrArg State.apyUSDBal h,
    by simpa using congrArg State.usdcBal h,
    by simpa using congrArg State.governanceTokenBal h,
    by simpa using congrArg State.vaultApxUSDBal h,
    by simpa using congrArg State.totalSupply_apxUSD h,
    by simpa using congrArg State.totalSupply_apyUSD h,
    hres, hvest⟩

/-- T9 companion, `pauser_compartmentalized`: a pauseController compromise is
confined to the `globalPause` liveness bit. Over any all-`PauserOp` trace every
principal field and every pricing parameter — in particular `redemptionValue` — is
bitwise unchanged. (The complete frame, covering *all* fields at once, is
`pauser_trace_blast_radius`; this is its named-field projection for the coalition
table.) -/
theorem pauser_compartmentalized (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, PauserOp p.1) :
    (execTrace s σ).apxUSDBal = s.apxUSDBal ∧
    (execTrace s σ).apyUSDBal = s.apyUSDBal ∧
    (execTrace s σ).usdcBal = s.usdcBal ∧
    (execTrace s σ).governanceTokenBal = s.governanceTokenBal ∧
    (execTrace s σ).vaultApxUSDBal = s.vaultApxUSDBal ∧
    (execTrace s σ).totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    (execTrace s σ).totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    (execTrace s σ).usdcReserve = s.usdcReserve ∧
    (execTrace s σ).vestTotal = s.vestTotal ∧
    (execTrace s σ).redemptionValue = s.redemptionValue := by
  have h := pauser_trace_blast_radius s σ h_gated false
  exact ⟨by simpa using congrArg State.apxUSDBal h,
    by simpa using congrArg State.apyUSDBal h,
    by simpa using congrArg State.usdcBal h,
    by simpa using congrArg State.governanceTokenBal h,
    by simpa using congrArg State.vaultApxUSDBal h,
    by simpa using congrArg State.totalSupply_apxUSD h,
    by simpa using congrArg State.totalSupply_apyUSD h,
    by simpa using congrArg State.usdcReserve h,
    by simpa using congrArg State.vestTotal h,
    by simpa using congrArg State.redemptionValue h⟩

/-! ## T10 `coalition_bound` — quantifying the worst coalition (base-model theorems)

The headline finding. Two results contrasting single-key impotence with a specific
two-key coalition that drains a victim's principal:

* `single_key_bounds`: a corollary **table** — for any victim `u`, over any
  single-role attack trace, **no single key extracts principal**. Oracle-alone and
  pauser-alone leave every user balance *and* the reserve bitwise unchanged;
  distributor-alone leaves user balances unchanged and can only *grow* the reserve
  (it pays in); admin-alone leaves every apxUSD balance unchanged and can only
  *shrink* the reserve **into holders' own pockets** (the backstop's credit-only
  pro-rata payout) — extraction of user principal is 0 in every row. Each row is a
  projection of the corresponding Tier-1/2 trace theorem.
* `admin_rfq_coalition_drains`: the **quantitative coalition** result, on the
  document-faithful model. Preconditions baked into the witness: the governance
  emergency flag is already up (a stress event occurred), the collateral and the
  reserve are already at 0 (so the backstop's pro-rata compensation leg pays 0),
  and the victim has an **outstanding RFQ redemption request** of their full
  balance, submitted while the published price was still healthy (`ray`). Then the
  admin's `catastrophicBackstop` reprices to `0 * ray / supply = 0` and the
  counterparty's `executeRFQRedemption` settles the victim's own pending request at
  the crashed price — burning all of their apxUSD for `amount * 0 / ray = 0` USDC.
  Net loss = 100% of the requested holdings, in stark contrast to the single-key
  rows.

* `admin_rfq_coalition_drains_funded`: the same coalition on a **funded** witness
  (reserve 100, victim diluted to half the supply), where the pre-attack
  counterfactual — the victim's own `redeemApxUSD` paying in full — is a
  machine-checked conjunct. The loss becomes attributable: half the principal,
  redistributed to a passive bystander by the backstop's own pro-rata leg.

Headline conclusion (see the docstrings): for users with in-flight RFQ requests,
fund security against a compromised admin rests **entirely** on the RFQ
counterparty set and on the absence of a rate limit / redemption-price floor —
exactly the mechanisms T7 (rate limit) and T8 (timelock) add. In the current model
neither exists (cf. T6 `redeem_payout_has_no_cap`). -/

/-- The RFQ redemption's exact effect on the targeted user, unconditionally: a
successful `executeRFQRedemption user amount` burns `amount` of the user's apxUSD
and credits them exactly `amount * redemptionValue / ray` USDC — the payout is a
bare linear function of the admin-controlled redemption price, with no floor. (The
counterparty-initiated dual of `redeem_payout_formula`; specialization of
`inv_executeRFQRedemption`.) -/
theorem rfq_payout_formula (s : State) (user : Address) (amount : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.executeRFQRedemption user amount) caller = some s') :
    s'.apxUSDBal user = s.apxUSDBal user - amount ∧
    s'.usdcBal user = s.usdcBal user + amount * s.redemptionValue / ray := by
  obtain ⟨_, _, _, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
  subst hs'
  exact ⟨by simp [burnApxUSD], by simp [burnApxUSD]⟩

/-- Forward direction for `catastrophicBackstop`: with the governance emergency
flag already up, the admin's call succeeds, publishing the per-unit collateral price
`redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD` and paying the
whole reserve out to holders pro-rata. -/
private theorem step_catastrophicBackstop_forward (s : State)
    (hf : s.emergencyFlag = true) :
    step s Op.catastrophicBackstop s.admin
      = some { s with
          redemptionValue := (s.totalCollateralValue * ray) / s.totalSupply_apxUSD
          usdcBal := fun a =>
            s.usdcBal a + (s.usdcReserve * s.apxUSDBal a) / s.totalSupply_apxUSD
          usdcReserve := 0
          overcollateralizationBuffer := 0 } := by
  show (if s.admin = s.admin ∧ s.emergencyFlag = true then _ else none) = _
  rw [if_pos ⟨rfl, hf⟩]

/-- Forward direction for `executeRFQRedemption`: with the six guards discharged —
including the whitelist check on the targeted user and the user's own outstanding
RFQ request covering the amount — the call succeeds, and its exact effect is the
`burnApxUSD` of the user plus the priced USDC credit, consuming the request. -/
private theorem step_executeRFQRedemption_forward (s : State) (user : Address)
    (amount : Nat) (caller : Address)
    (hgp : s.globalPause = false)
    (hcp : s.rfqCounterparties.contains caller = true)
    (hwl : s.whitelist user = true)
    (hrq : amount ≤ s.rfqRequests user)
    (hbal : amount ≤ s.apxUSDBal user)
    (hres : amount * s.redemptionValue / ray ≤ s.usdcReserve) :
    step s (Op.executeRFQRedemption user amount) caller
      = some { burnApxUSD s user amount with
          rfqRequests := fun a => if a = user then
              (burnApxUSD s user amount).rfqRequests a - amount
            else (burnApxUSD s user amount).rfqRequests a
          usdcReserve := (burnApxUSD s user amount).usdcReserve - amount * s.redemptionValue / ray
          usdcBal := fun a => if a = user then
              (burnApxUSD s user amount).usdcBal a + amount * s.redemptionValue / ray
            else (burnApxUSD s user amount).usdcBal a } := by
  simp only [step]
  rw [if_neg (by rw [hgp]; decide), if_neg (by rw [hcp]; decide),
      if_neg (by rw [hwl]; decide), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

/-- Companion for the admin row of `single_key_bounds`: across an admin-only trace
the USDC reserve is non-increasing — bitwise unchanged at every step except the
backstop's wind-down payout, which moves it into holders' own USDC balances
(credit-only; `admin_cannot_touch_balances`). -/
private theorem admin_trace_reserve_nonincreasing (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, AdminOp p.1) :
    (execTrace s σ).usdcReserve ≤ s.usdcReserve := by
  induction σ generalizing s with
  | nil => exact Nat.le_refl _
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have h_tail : ∀ q ∈ σ, AdminOp q.1 := fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail
    | some s1 =>
      obtain ⟨-, -, -, -, -, -, hres⟩ :=
        admin_cannot_touch_balances s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      exact Nat.le_trans (ih s1 h_tail) hres

/-- T10 `single_key_bounds` (docs/05-blast-radius.md, Tier 3) — **no single
compromised key extracts principal.**

For an arbitrary victim `u` and four independent attack traces, each consisting
solely of one role's operations:

* **oracle alone** (`oracle_alone_preserves_balances`): every apxUSD balance and the
  USDC reserve are bitwise unchanged — extraction 0;
* **pauser alone** (`pauser_compartmentalized`): likewise unchanged — extraction 0;
* **distributor alone** (`distributor_compartmentalized`): user apxUSD balances
  unchanged and the reserve is untouched — the role pays into the vesting contract, not the reserve, extraction 0;
* **admin alone** (`admin_trace_blast_radius` /
  `admin_trace_reserve_nonincreasing`): every apxUSD balance unchanged, and the
  reserve is non-increasing — the only admin channel that moves it is the
  backstop's wind-down payout, which distributes it **to the apxUSD holders
  themselves**, pro-rata, never to the admin's discretion (each holder's USDC
  balance is credit-only under every `AdminOp`; `admin_cannot_touch_balances`) —
  extraction of user principal is 0.

The contrast with `admin_rfq_coalition_drains` (two keys ⇒ 100% loss of a pending
RFQ request) is the value of key separation: it takes a *coalition* to touch
principal. -/
theorem single_key_bounds (s : State) (σO σP σD σA : List (Op × Address))
    (hO : ∀ p ∈ σO, OracleOp p.1) (hP : ∀ p ∈ σP, PauserOp p.1)
    (hD : ∀ p ∈ σD, DistributorOp p.1) (hA : ∀ p ∈ σA, AdminOp p.1) :
    ((execTrace s σO).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σO).usdcReserve = s.usdcReserve) ∧
    ((execTrace s σP).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σP).usdcReserve = s.usdcReserve) ∧
    ((execTrace s σD).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σD).usdcReserve = s.usdcReserve) ∧
    ((execTrace s σA).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σA).usdcReserve ≤ s.usdcReserve) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨ho1, _, _, _, ho5, _⟩ := oracle_alone_preserves_balances s σO hO
    exact ⟨ho1, ho5⟩
  · obtain ⟨hp1, _, _, _, _, _, _, hp8, _⟩ := pauser_compartmentalized s σP hP
    exact ⟨hp1, hp8⟩
  · obtain ⟨hd1, _, _, _, _, _, _, hd8, _⟩ := distributor_compartmentalized s σD hD
    exact ⟨hd1, hd8⟩
  · have h := admin_trace_blast_radius s σA hA
      s.whitelist s.denylist 0 0 0 0 0 false 0 0 0 0 s.usdcBal 0 0
    exact ⟨by simpa using congrArg State.apxUSDBal h,
      admin_trace_reserve_nonincreasing s σA hA⟩

/-- Witness for the coalition drain: a victim (address `0`) is whitelisted, holds
100 apxUSD (the whole 100-token supply) and no USDC, and has an **outstanding RFQ
redemption request** for all 100 — submitted while the published redemption price
was still healthy (`ray` = $1.00). The catastrophe has already struck: the
governance emergency flag is up and both `totalCollateralValue` and the USDC
reserve are 0, so the backstop's pro-rata compensation leg has nothing left to
distribute. The admin is address `1`; the approved RFQ counterparty is address `2`. -/
private def coalWitness : State :=
  { (default : State) with
      admin := 1
      rfqCounterparties := [2]
      whitelist := fun a => a == 0
      emergencyFlag := true
      totalSupply_apxUSD := 100
      apxUSDBal := fun a => if a = 0 then 100 else 0
      rfqRequests := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      totalCollateralValue := 0 }

/-- T10 `admin_rfq_coalition_drains` (docs/05-blast-radius.md, Tier 3) — **the worst
coalition, quantified: `{admin, RFQ-counterparty}` inflicts 100% loss on a user's
pending RFQ request.**

Threat model: the admin key and one approved RFQ-counterparty key are both
compromised, **after** a catastrophe has already struck — the governance emergency
flag is up (the document-faithful backstop can only fire under a pre-set flag) and
the collateral and the USDC reserve are both at 0, so the backstop's mandated
pro-rata compensation leg (which this model formalizes in full) has nothing to pay.
The victim (address `0`) is whitelisted, holds 100 apxUSD, no USDC, and — crucially
— has an **outstanding RFQ redemption request** for all 100, submitted while the
published redemption price was still `ray` (= $1.00). The counterparty can only
execute against that request (`req_rfq_redemption_allowed`); a user with no pending
request cannot be touched by this path at all.

The coalition acts in two steps:
1. the **admin** calls `catastrophicBackstop`, which publishes
   `redemptionValue := totalCollateralValue * ray / totalSupply = 0 * ray / 100 = 0`
   (`redemption_price_admin_only`; the price crashes from `ray` to 0 with no floor
   and no delay — cf. T8's `base_model_has_no_timelock`), and distributes the
   reserve pro-rata — here `0`, since nothing remains;
2. the approved **RFQ counterparty** calls `executeRFQRedemption victim 100`,
   settling the victim's own pending request at the crashed price: all 100 of the
   victim's apxUSD are burned for `100 * 0 / ray = 0` USDC (`rfq_payout_formula`).

Outcome (proved on the concrete witness): the victim's apxUSD goes 100 → 0 while
their USDC stays 0 — a **total loss of the requested principal**, uncompensated
because the reserve was already empty. Contrast every row of `single_key_bounds`,
where each key alone extracts 0. The honest headline on the document-faithful
model: for a user with an in-flight RFQ request, fund security against a
compromised admin rests entirely on the RFQ counterparty set and on the missing
rate-limit / price-floor (T7/T8) — the request is settled at whatever price holds
at execution time, with no floor and no consent-at-price step. -/
theorem admin_rfq_coalition_drains :
    ∃ (s s1 s2 : State) (victim counterparty amount : Nat),
      0 < amount ∧
      s.apxUSDBal victim = amount ∧ s.usdcBal victim = 0 ∧
      s.whitelist victim = true ∧
      s.rfqRequests victim = amount ∧
      s.emergencyFlag = true ∧
      s.usdcReserve = 0 ∧
      ray ≤ s.redemptionValue ∧
      s.rfqCounterparties.contains counterparty = true ∧
      step s Op.catastrophicBackstop s.admin = some s1 ∧
      s1.redemptionValue = 0 ∧
      step s1 (Op.executeRFQRedemption victim amount) counterparty = some s2 ∧
      s2.apxUSDBal victim = 0 ∧ s2.usdcBal victim = 0 := by
  -- step 1: admin publishes redemptionValue = 0 * ray / 100 = 0; the pro-rata
  -- compensation leg distributes the (empty) reserve
  let R : State :=
    { coalWitness with
        redemptionValue :=
          (coalWitness.totalCollateralValue * ray) / coalWitness.totalSupply_apxUSD
        usdcBal := fun a => coalWitness.usdcBal a
          + (coalWitness.usdcReserve * coalWitness.apxUSDBal a)
            / coalWitness.totalSupply_apxUSD
        usdcReserve := 0
        overcollateralizationBuffer := 0 }
  have h1 : step coalWitness Op.catastrophicBackstop coalWitness.admin = some R :=
    step_catastrophicBackstop_forward coalWitness rfl
  have hgp : R.globalPause = false := rfl
  have hcp : R.rfqCounterparties.contains 2 = true := rfl
  have hwl : R.whitelist 0 = true := rfl
  have hrq : (100 : Nat) ≤ R.rfqRequests 0 := Nat.le_refl _
  have hbal : (100 : Nat) ≤ R.apxUSDBal 0 := Nat.le_refl _
  have hres : 100 * R.redemptionValue / ray ≤ R.usdcReserve := by
    rw [show R.redemptionValue = 0 from rfl, Nat.mul_zero, Nat.zero_div]
    exact Nat.zero_le _
  -- step 2: the counterparty settles the victim's pending request at price 0,
  -- burning all 100 apxUSD for 0 USDC
  have h2 := step_executeRFQRedemption_forward R 0 100 2 hgp hcp hwl hrq hbal hres
  obtain ⟨hapx, husdc⟩ := rfq_payout_formula R 0 100 2 _ h2
  refine ⟨coalWitness, R, _, 0, 2, 100, by decide, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, by decide, h1, rfl, h2, ?_, ?_⟩
  · rw [hapx, show R.apxUSDBal 0 = 100 from rfl]
  · rw [husdc, show R.redemptionValue = 0 from rfl, show R.usdcBal 0 = 0 from rfl,
      Nat.mul_zero, Nat.zero_div]

/-- Witness for the **funded** coalition drain: same cast as `coalWitness`, but the
catastrophe has not consumed the reserve — 100 USDC remain — and the victim's
100 apxUSD are half of a 200-token supply; a passive bystander (address `4`) holds
the other half. The collateral valuation is 0 and the emergency flag is up, so the
backstop can fire; but with a funded reserve the pre-attack counterfactual is now
*true*: the whitelisted victim could have called `redeemApxUSD 100` themselves and
received the full 100 USDC (the below-peg gate is open, `apxUSDMarketPrice = 0 < ray`,
and the reserve covers the payout). -/
private def coalWitnessFunded : State :=
  { (default : State) with
      admin := 1
      rfqCounterparties := [2]
      whitelist := fun a => a == 0
      emergencyFlag := true
      totalSupply_apxUSD := 200
      apxUSDBal := fun a => if a = 0 then 100 else if a = 4 then 100 else 0
      rfqRequests := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      totalCollateralValue := 0
      usdcReserve := 100 }

/-- T10 `admin_rfq_coalition_drains_funded` — **the funded variant recommended by the
human review: an attributable loss, not just a mechanism.**

`admin_rfq_coalition_drains` above holds the reserve at 0, so the victim's total loss
is uncompensated but no value is actually redistributed — the human review
(`human_review_admin_rfq_coalition_drains.md`, F3) read it as demonstrating the
mechanism rather than an attributable harm, and recommended a funded witness. The
literal fix it proposed (fund the reserve, keep the victim as sole holder) no longer
produces a loss on the current model: the backstop's pro-rata leg — which this model
now formalizes in full — would hand a sole holder the whole reserve back. The funded
witness therefore needs *dilution*:

* supply 200 — the victim (address `0`) holds 100, a passive bystander (address `4`)
  holds the other 100;
* the reserve holds 100 USDC; the collateral valuation is 0 and the emergency flag
  is up, so the document-faithful backstop can fire;
* the published price is still `ray`, and the victim's full balance sits in an
  outstanding RFQ request filed at that healthy price.

**The counterfactual is machine-checked this time** (the review's F3 point): the
statement exhibits a successful `redeemApxUSD 100` *by the victim* from the initial
state — every guard passes, including the below-peg gate and the reserve check —
paying the full `amount` in USDC. Instead the coalition acts first:

1. the **admin**'s `catastrophicBackstop` reprices to `0 * ray / 200 = 0` and pays
   the reserve out pro-rata — 50 to the victim, 50 to the bystander;
2. the **counterparty**'s `executeRFQRedemption victim 100` settles the pending
   request at the crashed price: 100 apxUSD burn for `100 * 0 / ray = 0` USDC.

Outcome (final conjuncts): the victim ends with 0 apxUSD and strictly less USDC
than the counterfactual pays — concretely 50 against 100 — an attributable loss of
half the principal. The other half of the reserve was routed to the bystander by
the coalition's own first step, so the harm is a redistribution, not bookkeeping.

Model-boundary assumptions carried by both coalition theorems (review action 2):
the *filing* of the victim's RFQ request is state (`rfqRequests`) and its
settlement is guarded on it (`req_rfq_redemption_allowed`), but the off-chain
quote/consent flow around filing is out of scope (§6.1 of the report);
`catastrophicBackstop` fires on the admin's sole signature once `emergencyFlag` is
up — any off-chain governance process gating that flag is likewise out of scope;
and the backstop's pro-rata compensation leg **is** modeled — it is exactly what
pays the bystander here. -/
theorem admin_rfq_coalition_drains_funded :
    ∃ (s s1 s2 : State) (victim counterparty amount : Nat),
      0 < amount ∧
      s.apxUSDBal victim = amount ∧ s.usdcBal victim = 0 ∧
      s.whitelist victim = true ∧
      s.rfqRequests victim = amount ∧
      s.emergencyFlag = true ∧
      ray ≤ s.redemptionValue ∧
      s.rfqCounterparties.contains counterparty = true ∧
      (∃ s3 : State, step s (Op.redeemApxUSD amount) victim = some s3 ∧
        s3.usdcBal victim = amount) ∧
      step s Op.catastrophicBackstop s.admin = some s1 ∧
      s1.redemptionValue = 0 ∧
      step s1 (Op.executeRFQRedemption victim amount) counterparty = some s2 ∧
      s2.apxUSDBal victim = 0 ∧
      s2.usdcBal victim < amount := by
  -- step 1: the backstop reprices to 0 * ray / 200 = 0 and pays the reserve
  -- pro-rata: 50 to the victim, 50 to the bystander
  let R : State :=
    { coalWitnessFunded with
        redemptionValue :=
          (coalWitnessFunded.totalCollateralValue * ray) / coalWitnessFunded.totalSupply_apxUSD
        usdcBal := fun a => coalWitnessFunded.usdcBal a
          + (coalWitnessFunded.usdcReserve * coalWitnessFunded.apxUSDBal a)
            / coalWitnessFunded.totalSupply_apxUSD
        usdcReserve := 0
        overcollateralizationBuffer := 0 }
  have h1 : step coalWitnessFunded Op.catastrophicBackstop coalWitnessFunded.admin = some R :=
    step_catastrophicBackstop_forward coalWitnessFunded rfl
  have hgp : R.globalPause = false := rfl
  have hcp : R.rfqCounterparties.contains 2 = true := rfl
  have hwl : R.whitelist 0 = true := rfl
  have hrq : (100 : Nat) ≤ R.rfqRequests 0 := Nat.le_refl _
  have hbal : (100 : Nat) ≤ R.apxUSDBal 0 := Nat.le_refl _
  have hres : 100 * R.redemptionValue / ray ≤ R.usdcReserve := by
    rw [show R.redemptionValue = 0 from rfl, Nat.mul_zero, Nat.zero_div]
    exact Nat.zero_le _
  -- step 2: the counterparty settles the victim's pending request at price 0,
  -- burning all 100 apxUSD for 0 USDC — while the victim's pro-rata credit is only 50
  have h2 := step_executeRFQRedemption_forward R 0 100 2 hgp hcp hwl hrq hbal hres
  obtain ⟨hapx, husdc⟩ := rfq_payout_formula R 0 100 2 _ h2
  refine ⟨coalWitnessFunded, R, _, 0, 2, 100, by decide, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, by decide, ⟨_, rfl, rfl⟩, h1, rfl, h2, ?_, ?_⟩
  · rw [hapx, show R.apxUSDBal 0 = 100 from rfl]
  · rw [husdc, show R.redemptionValue = 0 from rfl, Nat.mul_zero, Nat.zero_div,
      show R.usdcBal 0 = 50 from rfl]
    decide

/-! ## T11: the RFQ counterparty's timing option

Newly stateable. Two model changes were needed and neither is about the RFQ path itself:
`Op.tick` (so a trace can contain more than one instant) and a working
`updateRedemptionValue` (so the redemption price can move under *honest* operations rather
than only under the admin's emergency backstop). Until both landed, "the counterparty picks
the moment" was not a property this model could express — which is why `admin_rfq_coalition_drains`
below it is stated as a **two-key** coalition. That is a fact about the model's reach, not a
bound on the adversary.

The witness holds the reserve full and the emergency flag down: nothing here is a
catastrophe, and no key is compromised except that we let the counterparty choose when to
act. -/

private def timingWitness : State :=
  { (default : State) with
      globalPause := false
      admin := 3
      rfqCounterparties := [2]
      whitelist := fun a => a == 0
      usdcBal := fun _ => 0
      totalSupply_apxUSD := 100
      apxUSDBal := fun a => if a = 0 then 100 else 0
      rfqRequests := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      usdcReserve := 100 }

/-- **T11 `rfq_payout_is_set_by_execution_timing`** — the user's realized payout on a
submitted RFQ request is fixed by *when* the counterparty executes, and the user has no
input into that moment.

Same starting state, same user, same request of 100 apxUSD, same counterparty:

* executed straight away, at the published price `ray` ($1.00), the user is paid **100**;
* executed after one honest oracle update to `ray / 2`, the user is paid **50**.

Both traces are permitted, both leave the request consumed, and the counterparty selects
between them unilaterally. No key is compromised in either. This is the Apyx instance of
the settlement-timing option that `docs/06` §7 files as S10 — the difference being that
there the payout rule takes the protocol-favourable side of the two prices, whereas here
the price at execution is simply taken as given. -/
theorem rfq_payout_is_set_by_execution_timing :
    (execTrace timingWitness [(Op.executeRFQRedemption 0 100, 2)]).usdcBal 0 = 100 ∧
    (execTrace timingWitness [(Op.updateRedemptionValue (ray / 2), 3),
                              (Op.executeRFQRedemption 0 100, 2)]).usdcBal 0 = 50 ∧
    (execTrace timingWitness [(Op.updateRedemptionValue (ray / 2), 3),
                              (Op.executeRFQRedemption 0 100, 2)]).rfqRequests 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [execTrace, step, timingWitness, burnApxUSD, ray]

/-! ## T12: on the settlement leg, the price protection belongs to the wrong party

`RedemptionPoolV0.redeem` takes a `minReserveAssetOut` and reverts on `SlippageExceeded`, so
the path does carry a price floor. But `redeem` is `ROLE_REDEEMER`-gated — `Access.t.sol`
asserts the revert for an ordinary holder *and* for the admin — and it burns
`burnFrom(msg.sender)`. The caller is therefore the redeemer, never the holder; the holder has
already parted with their apxUSD by the time this runs. The floor is a parameter of the party
that is not exposed. -/

private def poolWitness : State :=
  { (default : State) with
      globalPause := false
      admin := 3
      -- set explicitly: `default` is not a reliable source for fields a witness depends on
      -- (`Regression.lean` §R11)
      denylist := fun _ => false
      rfqCounterparties := [2]
      totalSupply_apxUSD := 100
      apxUSDBal := fun a => if a = 2 then 100 else 0
      usdcBal := fun _ => 0
      redemptionValue := ray
      usdcReserve := 100 }

/-- **T12 `pool_redeem_floor_is_the_redeemers`.** One state, one redeemer (`2`), one receiver
(`1`), one 100-apxUSD settlement, three runs:

1. settled at par, the receiver is paid **100**;
2. settled after one honest admin price update to `ray / 2`, the receiver is paid **50** — and
   the call is *accepted*, because the floor was `0` and the floor is the redeemer's to choose;
3. the redeemer, facing that same halved price, can simply decline: with a floor of `100` the
   call reverts.

Run 3 is the point. The lever exists, and it belongs to the party whose apxUSD is being burned
— which, on this path, is the redeemer and not the holder. The holder's exposure is settled by
whatever price holds when someone else decides to act, exactly as in
`rfq_payout_is_set_by_execution_timing`, with the custody handover on top. -/
theorem pool_redeem_floor_is_the_redeemers :
    (execTrace poolWitness [(Op.poolRedeem 100 1 0, 2)]).usdcBal 1 = 100 ∧
    (execTrace poolWitness [(Op.updateRedemptionValue (ray / 2), 3),
                            (Op.poolRedeem 100 1 0, 2)]).usdcBal 1 = 50 ∧
    step (execTrace poolWitness [(Op.updateRedemptionValue (ray / 2), 3)])
      (Op.poolRedeem 100 1 100) 2 = none := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [execTrace, step, poolWitness, burnApxUSD, ray]

end Apyx
