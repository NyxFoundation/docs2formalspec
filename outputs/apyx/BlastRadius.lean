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
  op = Op.updateRedemptionValue ∨ ∃ price, op = Op.setApxUSDMarketPrice price

/-- Operations authorized by the `admin` role. -/
def AdminOp (op : Op) : Prop :=
  (∃ a, op = Op.addToWhitelist a) ∨ (∃ a, op = Op.removeFromWhitelist a) ∨
  (∃ a, op = Op.addToDenylist a) ∨ (∃ a, op = Op.removeFromDenylist a) ∨
  (∃ bps, op = Op.setYieldRate bps) ∨ (∃ amount, op = Op.handleStressEvent amount) ∨
  op = Op.catastrophicBackstop ∨ (∃ p, op = Op.setVestPeriod p)

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
          caller (lockShares amount s.exchangeRate)))
      "Deposit" [caller, caller, caller, amount, lockShares amount s.exchangeRate] := by
  simp only [step] at h
  split at h
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
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem inv_claimUnlock (s : State) (id : Nat) (caller : Address) (s' : State)
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

private theorem inv_flexibleClaimUnlock (s : State) (id : Nat) (caller : Address) (s' : State)
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
            · exact ⟨by simp_all, by simp_all, by omega, by omega, by omega, (Option.some.inj h).symm⟩

private theorem inv_withdraw (s : State) (assets : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s.globalPause = false ∧
    withdrawShares assets s.exchangeRate ≤ (pullVestedYield s).apyUSDBal caller ∧
    assets ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate)).vaultApxUSDBal - assets }
          receiver assets)) "Withdraw" [caller, receiver, caller, assets, withdrawShares assets s.exchangeRate] := by
  simp only [step, pv_exchangeRate] at h
  split at h
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
    redeemAssets shares s.exchangeRate ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller shares with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal - redeemAssets shares s.exchangeRate }
          receiver (redeemAssets shares s.exchangeRate))) "Withdraw" [caller, receiver, caller, redeemAssets shares s.exchangeRate, shares] := by
  simp only [step, pv_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem inv_executeRFQRedemption (s : State) (user : Address) (amount : Nat) (caller : Address) (s' : State)
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
    s' = { s with usdcReserve := s.usdcReserve + amount
                  fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now
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
    s.usdcReserve ≤ s'.usdcReserve ∧
    s.fullyVestedAmount + s.vestTotal ≤ s'.fullyVestedAmount + s'.vestTotal := by
  obtain ⟨amount, rfl⟩ := h_gated
  obtain ⟨hc, rfl⟩ := step_creditYield_exact s amount caller s' h_step
  refine ⟨hc, fun _ _ _ _ => rfl, Nat.le_add_right _ _, ?_⟩
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
    s.usdcReserve ≤ (execTrace s σ).usdcReserve ∧
    s.fullyVestedAmount + s.vestTotal
      ≤ (execTrace s σ).fullyVestedAmount + (execTrace s σ).vestTotal := by
  induction σ generalizing s with
  | nil => exact ⟨fun _ _ _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
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
      refine ⟨fun r v w f => ?_, Nat.le_trans hres ihres, Nat.le_trans hvest ihvest⟩
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
* `handleStressEvent` + `catastrophicBackstop` rewrite `totalCollateralValue` and
  then set `redemptionValue := totalCollateralValue`, repricing all *future*
  redemptions (including RFQ redemptions executed against a user by a counterparty)
  — quantifying that channel is Tier 2's T6 `oracle_blast_radius`;
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

/-- Exact effect of `catastrophicBackstop`. -/
theorem step_catastrophicBackstop_exact (s : State) (caller : Address) (s' : State)
    (h : step s Op.catastrophicBackstop caller = some s') :
    caller = s.admin ∧
    s' = { s with redemptionValue := s.totalCollateralValue * ray / s.totalSupply_apxUSD
                  emergencyFlag := true } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
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
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- T3 (single step, frame form): an admin-gated operation demands the admin role
and agrees with the pre-state on **every** field other than the nine
admin-parameter fields (`whitelist`, `denylist`, `yieldRateMonth`,
`lastRateSetTime`, `collateralYieldBase`, `totalCollateralValue`,
`redemptionValue`, `emergencyFlag`, `vestPeriod`) plus the three vest-clock
accumulator fields `setVestPeriod` also touches (`vestStart`, `vestTotal`,
`fullyVestedAmount` — accrue-first, same pattern as `creditYield`; see
`step_setVestPeriod_exact`). In particular no balance, supply, reserve, or
unlock-registry field is reachable from the admin role. -/
theorem admin_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : AdminOp op) (h_step : step s op caller = some s') :
    caller = s.admin ∧
    ∀ wl dl yr lt cy tcv rv ef vp vs vt fv,
      { s' with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                lastRateSetTime := lt, collateralYieldBase := cy,
                totalCollateralValue := tcv, redemptionValue := rv,
                emergencyFlag := ef, vestPeriod := vp,
                vestStart := vs, vestTotal := vt, fullyVestedAmount := fv }
    = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
               lastRateSetTime := lt, collateralYieldBase := cy,
               totalCollateralValue := tcv, redemptionValue := rv,
               emergencyFlag := ef, vestPeriod := vp,
               vestStart := vs, vestTotal := vt, fullyVestedAmount := fv } := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨bps, rfl⟩ | ⟨amt, rfl⟩ | rfl | ⟨p, rfl⟩ :=
    h_gated
  · obtain ⟨hc, rfl⟩ := step_addToWhitelist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_removeFromWhitelist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_addToDenylist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_removeFromDenylist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, -, -, rfl⟩ := step_setYieldRate_exact s bps caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_handleStressEvent_exact s amt caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_catastrophicBackstop_exact s caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_setVestPeriod_exact s p caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

/-- T3 `admin_cannot_touch_balances` (docs/05-blast-radius.md, Tier 1) — the
single-step balance-field form.

Threat model: the `admin` key is fully compromised. The operations gated on
`caller = s.admin` in `step` are exactly the eight of `AdminOp`: `addToWhitelist`,
`removeFromWhitelist`, `addToDenylist`, `removeFromDenylist`, `setYieldRate`,
`handleStressEvent`, `catastrophicBackstop`, and `setVestPeriod`.

Claim: none of these operations changes any balance or supply field — every apxUSD,
apyUSD, and USDC balance, both total supplies, the vault's apxUSD holdings, and the
USDC reserve are unchanged. A compromised admin cannot *directly* move or destroy a
single unit of anyone's funds.

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
    s'.usdcBal = s.usdcBal ∧
    s'.totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    s'.vaultApxUSDBal = s.vaultApxUSDBal ∧
    s'.usdcReserve = s.usdcReserve := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨bps, rfl⟩ | ⟨amt, rfl⟩ | rfl | ⟨p, rfl⟩ :=
    h_gated
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | exact absurd h_step (by simp)

/-- T3 (trace form): an arbitrarily long attack trace consisting solely of
admin-gated operations leaves every field outside the nine admin-parameter fields
and the three vest-clock accumulator fields unchanged. A compromised admin key can
rewrite access lists and pricing/schedule parameters (and the vest clock's
internal bookkeeping via `setVestPeriod`) at will — with the deferred
consequences listed in the section header — but cannot move a single unit of any
recorded balance, supply, reserve, or unlock position. -/
theorem admin_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, AdminOp p.1) :
    ∀ wl dl yr lt cy tcv rv ef vp vs vt fv,
      { execTrace s σ with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                           lastRateSetTime := lt, collateralYieldBase := cy,
                           totalCollateralValue := tcv, redemptionValue := rv,
                           emergencyFlag := ef, vestPeriod := vp,
                           vestStart := vs, vestTotal := vt, fullyVestedAmount := fv }
    = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
               lastRateSetTime := lt, collateralYieldBase := cy,
               totalCollateralValue := tcv, redemptionValue := rv,
               emergencyFlag := ef, vestPeriod := vp,
               vestStart := vs, vestTotal := vt, fullyVestedAmount := fv } := by
  induction σ generalizing s with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    intro wl dl yr lt cy tcv rv ef vp vs vt fv
    have h_tail : ∀ q ∈ σ, AdminOp q.1 := fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail wl dl yr lt cy tcv rv ef vp vs vt fv
    | some s1 =>
      obtain ⟨-, hframe⟩ :=
        admin_frame s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      calc { execTrace s1 σ with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                                 lastRateSetTime := lt, collateralYieldBase := cy,
                                 totalCollateralValue := tcv, redemptionValue := rv,
                                 emergencyFlag := ef, vestPeriod := vp,
                                 vestStart := vs, vestTotal := vt, fullyVestedAmount := fv }
          = { s1 with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                      lastRateSetTime := lt, collateralYieldBase := cy,
                      totalCollateralValue := tcv, redemptionValue := rv,
                      emergencyFlag := ef, vestPeriod := vp,
                      vestStart := vs, vestTotal := vt, fullyVestedAmount := fv } :=
            ih s1 h_tail wl dl yr lt cy tcv rv ef vp vs vt fv
        _ = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                     lastRateSetTime := lt, collateralYieldBase := cy,
                     totalCollateralValue := tcv, redemptionValue := rv,
                     emergencyFlag := ef, vestPeriod := vp,
                     vestStart := vs, vestTotal := vt, fullyVestedAmount := fv } :=
            hframe wl dl yr lt cy tcv rv ef vp vs vt fv

/-! ## Oracle role: direct frame (the indirect channel is Tier 2's T6)

The oracle's two operations are `updateRedemptionValue` (a no-op placeholder in
this model — notably, `redemptionValue` is writable only through the admin's
`catastrophicBackstop`) and `setApxUSDMarketPrice`. Their *direct* blast radius is
exactly the reported market-price field; the security-relevant channel is indirect:
`apxUSDMarketPrice` gates the arbitrage mint pathway (`ray < apxUSDMarketPrice` in
`Op.mintApxUSD`), which still takes 1 USDC per apxUSD minted from the *minter*.
Quantifying worst-case extraction through mispricing is T6 (`oracle_blast_radius`,
Tier 2). -/

/-- Exact effect of `updateRedemptionValue`: demands the oracle role and — in this
model — changes nothing at all. -/
theorem step_updateRedemptionValue_exact (s : State) (caller : Address) (s' : State)
    (h : step s Op.updateRedemptionValue caller = some s') :
    caller = s.oracle ∧ s' = s := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
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

/-- Oracle frame (single step): an oracle-gated operation demands the oracle role
and agrees with the pre-state on every field other than `apxUSDMarketPrice`. -/
theorem oracle_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : OracleOp op) (h_step : step s op caller = some s') :
    caller = s.oracle ∧
    ∀ mp, { s' with apxUSDMarketPrice := mp } = { s with apxUSDMarketPrice := mp } := by
  obtain rfl | ⟨price, rfl⟩ := h_gated
  · obtain ⟨hc, rfl⟩ := step_updateRedemptionValue_exact s caller s' h_step
    exact ⟨hc, fun _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_setApxUSDMarketPrice_exact s price caller s' h_step
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
  case the caller was an approved RFQ counterparty and `a` was *simultaneously
  compensated in the same step* with the full redemption payout
  (`amount * redemptionValue / ray` USDC credited to `a`'s USDC balance).

No privileged role has any pathway to debit an arbitrary user's apxUSD: pause/unpause,
list management, rate/period setting, yield crediting, oracle updates, stress handling,
and the backstop all leave every apxUSD balance unchanged (they fall into the
contradiction branch of this proof).

Carve-out honesty: `executeRFQRedemption` genuinely debits a non-caller, so the naive
"only the caller can be debited" claim is FALSE of this model and is not what we prove.
The carve-out is a *swap*, not a theft — the debited user atomically receives the
corresponding USDC at the recorded `redemptionValue`. Note that a compromised admin can
first move `redemptionValue` via `catastrophicBackstop` (and RFQ counterparty onboarding
is not itself an `Op`, so `rfqCounterparties` is effectively static in-model); pricing
the worst case of that combination is exactly Tier 2's `oracle_blast_radius` (T6), not
this theorem. -/
theorem no_role_transfers_user_funds (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (a : Address)
    (h_dec : s'.apxUSDBal a < s.apxUSDBal a) :
    a = caller ∨
    ∃ amount, op = Op.executeRFQRedemption a amount ∧
      s.rfqCounterparties.contains caller = true ∧
      s'.usdcBal a = s.usdcBal a + (amount * s.redemptionValue) / ray := by
  cases op
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
    simp [mintApxUSD, burnUnlockNFT] at h_dec
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
    simp [mintApxUSD, burnUnlockNFT] at h_dec
    split at h_dec <;> omega
  case executeRFQRedemption user amount =>
    obtain ⟨_, hrfq, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    by_cases hau : a = user
    · subst hau
      refine Or.inr ⟨amount, rfl, hrfq, ?_⟩
      simp [burnApxUSD]
    · exfalso
      simp [burnApxUSD, hau] at h_dec
  all_goals
    simp only [step] at h_step
    split at h_step <;>
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
    simp [mintApxUSD, burnUnlockNFT] at h_dec
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
    simp [mintApxUSD, burnUnlockNFT] at h_dec
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [burnApxUSD] at h_dec
    split at h_dec <;>
      first
        | exact absurd h_dec (Nat.not_lt.mpr (Nat.le_add_right _ _))
        | exact absurd h_dec (Nat.lt_irrefl _)
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact absurd h_dec (Nat.lt_irrefl _))
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
    simp [mintApxUSD, burnUnlockNFT]
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
    simp [mintApxUSD, burnUnlockNFT]
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    simp [burnApxUSD]
  all_goals
    simp only [step] at h_step
    split at h_step <;>
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
      simp [mintApxUSD, burnUnlockNFT]
    · have h_ne : id ≠ rid := fun h => hrid h.symm
      exact Or.inl ⟨by simpa [mintApxUSD, burnUnlockNFT, h_ne] using h_live,
        by simp [mintApxUSD, burnUnlockNFT, h_ne]⟩
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
      · simp [mintApxUSD, burnUnlockNFT]
      · exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (fee_le_start rt s.now))
    · have h_ne : id ≠ rid := fun h => hrid h.symm
      exact Or.inl ⟨by simpa [mintApxUSD, burnUnlockNFT, h_ne] using h_live,
        by simp [mintApxUSD, burnUnlockNFT, h_ne]⟩
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exact Or.inl ⟨by simpa [burnApxUSD] using h_live, by simp [burnApxUSD]⟩
  all_goals
    simp only [step] at h_step
    split at h_step <;>
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
            huc | ⟨amount, hop, -, -⟩
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
is a placeholder no-op). The real-world analogue (Yearn's finding that Apyx's
`ApxUSDRateOracle.setRate` sits behind a 0-second timelock) therefore maps to the
*admin coalition* here: worst case, `handleStressEvent` drives
`totalCollateralValue` to 0 and `catastrophicBackstop` publishes
`redemptionValue = 0`, after which an approved RFQ counterparty can burn users'
apxUSD for zero USDC. Pricing that coalition is T10's table; the theorems below pin
down the only channels through which it can act. -/

/-- The redemption price is admin-gated: if a step changes `redemptionValue`, the
operation was `catastrophicBackstop`, the caller held the admin role, and the new
value is the recorded `totalCollateralValue`. In particular the oracle role has
**no** influence over the redemption price in this model. -/
theorem redemption_price_admin_only (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s')
    (h_changed : s'.redemptionValue ≠ s.redemptionValue) :
    op = Op.catastrophicBackstop ∧ caller = s.admin ∧
    s'.redemptionValue = s.totalCollateralValue * ray / s.totalSupply_apxUSD := by
  cases op
  case catastrophicBackstop =>
    obtain ⟨hc, rfl⟩ := step_catastrophicBackstop_exact s caller s' h_step
    exact ⟨rfl, hc, rfl⟩
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
    exact absurd (by simp [mintApxUSD, burnUnlockNFT]) h_changed
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
    exact absurd (by simp [mintApxUSD, burnUnlockNFT]) h_changed
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exact absurd (by simp [burnApxUSD]) h_changed
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact absurd rfl h_changed)
        | exact absurd h_step (by simp)

/-- Reserve outflows happen only through redemption, and every unit that leaves the
reserve is paid to the address whose apxUSD is simultaneously burned, priced at the
recorded `redemptionValue`. This is the induction step for T5's no-theft ledger:
USDC can exit the system only against a matching apxUSD burn of the payee, via
`redeemApxUSD` (self-initiated) or `executeRFQRedemption` (counterparty-initiated,
same pricing). -/
theorem reserve_outflow_only_via_redemption (s : State) (op : Op) (caller : Address)
    (s' : State) (h_step : step s op caller = some s')
    (h_dec : s'.usdcReserve < s.usdcReserve) :
    ∃ user amount,
      ((op = Op.redeemApxUSD amount ∧ user = caller) ∨
        op = Op.executeRFQRedemption user amount) ∧
      amount ≤ s.apxUSDBal user ∧
      s'.apxUSDBal user = s.apxUSDBal user - amount ∧
      s'.usdcBal user = s.usdcBal user + amount * s.redemptionValue / ray ∧
      s'.usdcReserve = s.usdcReserve - amount * s.redemptionValue / ray ∧
      s'.totalSupply_apxUSD = s.totalSupply_apxUSD - amount := by
  cases op
  case redeemApxUSD amount =>
    obtain ⟨_, _, hbal, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    exact ⟨caller, amount, Or.inl ⟨rfl, rfl⟩, hbal,
      by simp [emitEvent, burnApxUSD],
      by simp [emitEvent, burnApxUSD],
      by simp [emitEvent, burnApxUSD],
      by simp [emitEvent, burnApxUSD]⟩
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, hbal, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exact ⟨user, amount, Or.inr rfl, hbal,
      by simp [burnApxUSD],
      by simp [burnApxUSD],
      by simp [burnApxUSD],
      by simp [burnApxUSD]⟩
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
    exact absurd h_dec (by simp [mintApxUSD, burnUnlockNFT])
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
    exact absurd h_dec (by simp [mintApxUSD, burnUnlockNFT])
  all_goals
    simp only [step] at h_step
    split at h_step <;>
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
running an arbitrarily long trace `σ`.

Hypotheses (the two carve-outs stated explicitly):
* `h_never_signs`: `a` is never the caller of any operation in `σ`;
* `h_never_rfq_target`: `a` is never the user-argument of an `executeRFQRedemption`
  anywhere in `σ` (the one compensated-swap pathway that can debit a non-caller; it
  is a priced swap, not theft, and is carved out here — pricing it is T6).

Claim: each of `a`'s three transferable balances is non-decreasing across the entire
trace, hence so is the derived ledger `netHoldings`. A passive bystander who signs
nothing and is not RFQ-targeted cannot be made to lose a single unit of any holding.
Proved by lifting the single-step non-custodial lemmas
(`no_role_transfers_user_funds`/`no_role_burns_user_shares`/`no_role_debits_usdc`)
through the trace — the induction is packaged in
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
  `redemptionValue := totalCollateralValue` with no upper bound — cf.
  `redemption_price_admin_only`) bounds `redemptionValue`, so no upper bound on payout
  is provable: the absence of a model-level cap, itself the key finding.

This is exactly the memo's T6 conclusion "in the current clamp-free model f =
usdcReserve (full drain)" and the real-world analogue of Yearn's finding that Apyx's
`ApxUSDRateOracle.setRate` sits behind a 0-second timelock. It motivates Tier 3's
rate-limit / clamp. Attribution note (`redemption_price_admin_only`): in *this* model
the redemption price is written by the admin's `catastrophicBackstop`, not the oracle
op, so the extraction coalition is admin (price) + redeemer/RFQ-counterparty (drain);
`updateRedemptionValue` is a placeholder no-op. -/

/-- T6(a) `oracle_alone_preserves_balances`: an arbitrarily long trace whose operations
are ALL oracle-gated leaves every balance, supply, and reserve field bitwise unchanged.
The oracle key acting alone extracts exactly zero — its only reachable field is the
reported market price `apxUSDMarketPrice` (`oracle_trace_blast_radius`), and the
redemption price in particular is untouched (`redemptionValue` unchanged). -/
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
unbounded `totalCollateralValue` (`redemption_price_admin_only`), there is no
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
        by simp [mintApxUSD, burnUnlockNFT]⟩)
    · exfalso
      simp [mintApxUSD, burnUnlockNFT, hao] at h_inc
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
      have heq : (mintApxUSD (burnUnlockNFT s id) a
            (am - am * flexibleUnlockFee rt s.now / 10000)).apxUSDBal a
          = s.apxUSDBal a + (am - am * flexibleUnlockFee rt s.now / 10000) := by
        simp [mintApxUSD, burnUnlockNFT]
      refine Or.inr (Or.inr ⟨id, am, rt, ce, rfl, hreq, howner, hnow, heq, ?_⟩)
      rw [heq]
      exact Nat.add_le_add_left (Nat.sub_le _ _) _
    · exfalso
      simp [mintApxUSD, burnUnlockNFT, hao] at h_inc
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [burnApxUSD] at h_inc
    split at h_inc <;> omega
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact absurd h_inc (Nat.lt_irrefl _))
        | exact absurd h_step (by simp)

/-! ## T7 `rate_limit_linear_bound` — a per-epoch outflow cap makes damage linear in time

**DESIGN theorem** (docs/05-blast-radius.md, Tier 3): this section models the
defence mechanism itself — an ERC-7265-style circuit breaker that caps the USDC
reserve outflow charged per epoch — and proves what it would guarantee. The base
Apyx model has **no** such limiter (per the memo, and per T6's
`redeem_payout_has_no_cap` a single corrupted-price redemption can drain the whole
reserve), so this is a statement about the *value of adopting the mechanism*, not a
property of the current protocol.

The wrapper adds no field to `State`: a new structure `RLState` layers an epoch
counter, a per-epoch spent meter, and a fixed cap over the untouched base state, and
`step2` runs the unmodified base `step` behind an outflow gate. By
`reserve_outflow_only_via_redemption`, the only base transitions the gate ever
charges are the two redemption paths (`step2_charge_only_for_redemption` below) —
everything else passes through unmetered because it cannot decrease the reserve.

Headline: across an arbitrary `execTrace2` run containing `k` `advanceEpoch` clock
actions, the net reserve outflow is `≤ cap * (k + 1)` — **damage is at most linear
in elapsed epochs**, no matter how an attacker holding every key sequences
operations inside each epoch. -/

/-- Rate-limited wrapper state: the untouched base `State` plus an epoch counter, the
reserve outflow already charged in the current epoch, and the fixed per-epoch outflow
cap (a policy parameter; `step2` never changes it). -/
structure RLState where
  base : State
  epoch : Nat
  spentThisEpoch : Nat
  cap : Nat

/-- Operations of the rate-limited wrapper: any base operation (with its caller), or
the distinguished `advanceEpoch` clock action that opens a fresh epoch budget. -/
inductive RLOp
  | base (op : Op) (caller : Address)
  | advanceEpoch

/-- Rate-limited step. A base operation first runs the unmodified base `step`; its
reserve outflow `d := usdcReserve - usdcReserve'` (0 when the reserve did not
decrease — `Nat` truncation) is charged against the epoch budget, and the whole
operation **reverts** (`none`) if the charge would exceed the cap. `advanceEpoch`
resets the meter and increments the epoch counter. -/
def step2 (rs : RLState) : RLOp → Option RLState
  | RLOp.base op caller =>
    match step rs.base op caller with
    | none => none
    | some s' =>
      if rs.cap < rs.spentThisEpoch + (rs.base.usdcReserve - s'.usdcReserve) then none
      else some { rs with
        base := s'
        spentThisEpoch := rs.spentThisEpoch + (rs.base.usdcReserve - s'.usdcReserve) }
  | RLOp.advanceEpoch =>
    some { rs with epoch := rs.epoch + 1, spentThisEpoch := 0 }

/-- Trace executor for the rate-limited wrapper (revert-skip semantics, like
`execTrace`). -/
def execTrace2 (rs : RLState) : List RLOp → RLState
  | [] => rs
  | o :: τ =>
    match step2 rs o with
    | some rs' => execTrace2 rs' τ
    | none => execTrace2 rs τ

/-- Number of `advanceEpoch` clock actions in a wrapper trace — the number of epoch
boundaries the trace crosses. -/
def countEpochs : List RLOp → Nat
  | [] => 0
  | RLOp.advanceEpoch :: τ => countEpochs τ + 1
  | RLOp.base _ _ :: τ => countEpochs τ

private theorem execTrace2_cons_some (rs rs' : RLState) (o : RLOp) (τ : List RLOp)
    (h : step2 rs o = some rs') : execTrace2 rs (o :: τ) = execTrace2 rs' τ := by
  simp [execTrace2, h]

private theorem execTrace2_cons_none (rs : RLState) (o : RLOp) (τ : List RLOp)
    (h : step2 rs o = none) : execTrace2 rs (o :: τ) = execTrace2 rs τ := by
  simp [execTrace2, h]

/-- Inversion for a successful rate-limited base step: the base `step` succeeded, the
charged budget respects the cap, and the successor is exactly the base successor with
the meter advanced by the outflow. -/
private theorem inv_step2_base (rs : RLState) (op : Op) (caller : Address) (rs' : RLState)
    (h : step2 rs (RLOp.base op caller) = some rs') :
    ∃ s', step rs.base op caller = some s' ∧
      rs.spentThisEpoch + (rs.base.usdcReserve - s'.usdcReserve) ≤ rs.cap ∧
      rs' = { rs with
        base := s'
        spentThisEpoch := rs.spentThisEpoch + (rs.base.usdcReserve - s'.usdcReserve) } := by
  simp only [step2] at h
  split at h
  · exact absurd h (by simp)
  · rename_i s' hs
    split at h
    · exact absurd h (by simp)
    · rename_i hgate
      exact ⟨s', hs, by omega, (Option.some.inj h).symm⟩

/-- The gate hook, made explicit via `reserve_outflow_only_via_redemption`: the only
accepted base operations that consume epoch budget (strictly increase the meter) are
the two redemption paths — `redeemApxUSD` by the payee itself or
`executeRFQRedemption` by an approved counterparty — and in either case the payee is
compensated at the recorded `redemptionValue` in the same step. Every other base
operation passes through the rate limiter unmetered. -/
theorem step2_charge_only_for_redemption (rs : RLState) (op : Op) (caller : Address)
    (rs' : RLState) (h : step2 rs (RLOp.base op caller) = some rs')
    (h_pos : rs.spentThisEpoch < rs'.spentThisEpoch) :
    ∃ user amount,
      ((op = Op.redeemApxUSD amount ∧ user = caller) ∨
        op = Op.executeRFQRedemption user amount) ∧
      amount ≤ rs.base.apxUSDBal user ∧
      rs'.base.apxUSDBal user = rs.base.apxUSDBal user - amount ∧
      rs'.base.usdcBal user
        = rs.base.usdcBal user + amount * rs.base.redemptionValue / ray := by
  obtain ⟨s', hs, hgate, rfl⟩ := inv_step2_base rs op caller rs' h
  dsimp only at h_pos ⊢
  have hdec : s'.usdcReserve < rs.base.usdcReserve := by omega
  obtain ⟨user, amount, hop, hbal, hapx, husdc, -, -⟩ :=
    reserve_outflow_only_via_redemption rs.base op caller s' hs hdec
  exact ⟨user, amount, hop, hbal, hapx, husdc⟩

/-- The rate limiter's local invariant is self-establishing: after any accepted
`step2` — with no assumption on the pre-state — `spentThisEpoch ≤ cap` holds (base
ops by the gate, `advanceEpoch` by the reset). -/
theorem step2_spent_le_cap (rs : RLState) (o : RLOp) (rs' : RLState)
    (h : step2 rs o = some rs') :
    rs'.spentThisEpoch ≤ rs'.cap := by
  cases o with
  | base op caller =>
    obtain ⟨s', -, hgate, rfl⟩ := inv_step2_base rs op caller rs' h
    exact hgate
  | advanceEpoch =>
    cases Option.some.inj h
    exact Nat.zero_le _

/-- Strengthened induction invariant for T7: with `spentThisEpoch ≤ cap` at the start,
the final reserve is below the initial one by at most the remaining budget of the
current epoch plus one full cap per epoch boundary crossed. -/
theorem execTrace2_reserve_lower_bound (rs : RLState) (τ : List RLOp)
    (h : rs.spentThisEpoch ≤ rs.cap) :
    rs.base.usdcReserve
      ≤ (execTrace2 rs τ).base.usdcReserve
        + (rs.cap - rs.spentThisEpoch) + rs.cap * countEpochs τ := by
  induction τ generalizing rs with
  | nil =>
    simp only [execTrace2, countEpochs, Nat.mul_zero, Nat.add_zero]
    omega
  | cons o τ ih =>
    cases o with
    | base op caller =>
      have hcount : countEpochs (RLOp.base op caller :: τ) = countEpochs τ := rfl
      rw [hcount]
      cases h2 : step2 rs (RLOp.base op caller) with
      | none =>
        rw [execTrace2_cons_none rs _ τ h2]
        exact ih rs h
      | some rs' =>
        rw [execTrace2_cons_some rs rs' _ τ h2]
        obtain ⟨s', -, hgate, rfl⟩ := inv_step2_base rs op caller rs' h2
        have hrec := ih { rs with
          base := s'
          spentThisEpoch := rs.spentThisEpoch + (rs.base.usdcReserve - s'.usdcReserve) } hgate
        dsimp only at hrec ⊢
        revert hrec
        generalize rs.cap * countEpochs τ = K
        intro hrec
        omega
    | advanceEpoch =>
      have hcount : countEpochs (RLOp.advanceEpoch :: τ) = countEpochs τ + 1 := rfl
      rw [hcount]
      rw [execTrace2_cons_some rs { rs with epoch := rs.epoch + 1, spentThisEpoch := 0 }
        RLOp.advanceEpoch τ rfl]
      have hrec := ih { rs with epoch := rs.epoch + 1, spentThisEpoch := 0 } (Nat.zero_le _)
      dsimp only at hrec
      rw [Nat.mul_add, Nat.mul_one]
      revert hrec
      generalize rs.cap * countEpochs τ = K
      intro hrec
      omega

/-- T7 `rate_limit_linear_bound` (docs/05-blast-radius.md, Tier 3) — **the rate
limiter provably caps cumulative loss linearly in elapsed time**.

Threat model: the attacker holds **every** key and submits an arbitrary wrapper
trace `τ` — any base operations with any callers, interleaved with `advanceEpoch`
clock actions in any pattern (the clock is not attacker-favourable: more epochs only
means more elapsed time). The only assumption is the limiter's own invariant at the
start, `spentThisEpoch ≤ cap` (true of any freshly initialized wrapper, e.g.
`spentThisEpoch = 0`; it is self-maintaining, `step2_spent_le_cap`).

Claim: the net USDC reserve outflow over the whole run is at most
`cap * (countEpochs τ + 1)` — one budget for the current epoch plus one per epoch
boundary crossed, i.e. the memo's `userLoss(t) ≤ cap × ⌈t/epoch⌉`. Within any single
epoch the attacker can sequence redemptions however they like (including at an
admin-corrupted `redemptionValue`, cf. T6); the gate reverts anything past the cap,
so damage accumulates at most linearly with time — buying detection/response time,
which is exactly the design value of an ERC-7265-style circuit breaker.

DESIGN theorem: the base Apyx model contains no such limiter, and T6
(`redeem_payout_has_no_cap`) shows its unlimited counterpart; this theorem proves
what adding the limiter would buy. -/
theorem rate_limit_linear_bound (rs : RLState) (τ : List RLOp)
    (h : rs.spentThisEpoch ≤ rs.cap) :
    rs.base.usdcReserve - (execTrace2 rs τ).base.usdcReserve
      ≤ rs.cap * (countEpochs τ + 1) := by
  have hrec := execTrace2_reserve_lower_bound rs τ h
  rw [Nat.mul_add, Nat.mul_one]
  revert hrec
  generalize rs.cap * countEpochs τ = K
  intro hrec
  omega

/-- T7, fresh-wrapper corollary: starting the rate limiter with an empty meter over
any base state, the reserve outflow of any attack trace is at most
`cap * (epochs crossed + 1)`. -/
theorem rate_limit_linear_bound_fresh (base0 : State) (cap : Nat) (τ : List RLOp) :
    base0.usdcReserve - (execTrace2 ⟨base0, 0, 0, cap⟩ τ).base.usdcReserve
      ≤ cap * (countEpochs τ + 1) :=
  rate_limit_linear_bound ⟨base0, 0, 0, cap⟩ τ (Nat.zero_le _)

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
model.** Whenever `catastrophicBackstop` (the sole writer of the redemption price,
`redemption_price_admin_only`) succeeds, the new price is already in force in the
post-state of that same step, and the clock has not advanced by even one unit
(`s'.now = s.now`). There is no pending interval — no state in which the change is
"announced but not yet effective" — during which a user could still redeem at the
old price. Direct projection of `step_catastrophicBackstop_exact`. -/
theorem catastrophicBackstop_is_instantaneous (s : State) (caller : Address) (s' : State)
    (h : step s Op.catastrophicBackstop caller = some s') :
    caller = s.admin ∧ s'.now = s.now ∧
    s'.redemptionValue = s.totalCollateralValue * ray / s.totalSupply_apxUSD := by
  obtain ⟨hc, rfl⟩ := step_catastrophicBackstop_exact s caller s' h
  exact ⟨hc, rfl, rfl⟩

/-- T8 Half 1, witness form: `base_model_has_no_timelock`. There is a state in which
the admin's `catastrophicBackstop` succeeds, **actually changes** the redemption
price, and does so at an unchanged clock (`s'.now = s.now`) — zero elapsed time
between the request and the effect. Together with the universal form above this
shows the base model provably has no timelock on privileged repricing: the escape
window has length exactly 0. NOT a vacuous claim about an unreachable guard — the
witness step succeeds and the price moves. (Why this matters: the exit guarantee of
Half 2 is a property of the *queue mechanism*, so it must be proved of a wrapper;
any attempt to prove it of the base model is falsified by this witness.) -/
theorem base_model_has_no_timelock :
    ∃ (s s' : State),
      step s Op.catastrophicBackstop s.admin = some s' ∧
      s'.redemptionValue ≠ s.redemptionValue ∧
      s'.now = s.now := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  refine ⟨{ (default : State) with totalCollateralValue := 1, totalSupply_apxUSD := ray }, _, rfl, ?_, rfl⟩
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
*records* `(op, caller, tl.now)` — the base state is untouched, so users can still
transact (in particular exit) against the old parameters. `tick` advances the
wrapper clock by one. `execute i` runs the stored base operation via the unmodified
base `step`, and **reverts unless the entry's queue timestamp is at least `delay`
old** (`t₀ + delay ≤ now`).

Headline (`timelock_escape_guarantee`): if an operation queued at the current
instant is later executed — after any further wrapper trace `τ` the attacker
likes — then `τ` contains at least `delay` `tick` actions. Since the wrapper clock
moves only via `tick` (`execTraceTL_now`), this is exactly "a guaranteed
`delay`-tick-long window elapses between the announcement and the effect," the
escape hatch of Eyal & Sirer / the memo's T8. -/

/-- Timelocked wrapper state: the untouched base `State`, a wrapper clock, the
queue of pending privileged operations — each entry `(op, caller, queuedAt)`
records the wrapper time at which it was queued — and the fixed timelock length
`delay` (a policy parameter; `step2tl` never changes it). -/
structure TLState where
  base : State
  now : Nat
  pending : List (Op × Address × Nat)
  delay : Nat

/-- Operations of the timelocked wrapper: `queue` announces a privileged base
operation (recording it without running it), `tick` advances the wrapper clock by
one, and `execute i` attempts to run the `i`-th pending entry. -/
inductive TLOp
  | queue (op : Op) (caller : Address)
  | tick
  | execute (i : Nat)

/-- Timelocked step. `queue` appends `(op, caller, tl.now)` — stamped with the
*current* wrapper time — and does **not** run the operation; `tick` advances the
clock; `execute i` looks up the `i`-th pending entry and reverts (`none`) unless
its timelock has fully elapsed (`queuedAt + delay ≤ now`), in which case it runs
the unmodified base `step` and removes the entry. -/
def step2tl (tl : TLState) : TLOp → Option TLState
  | TLOp.queue op caller =>
    some { tl with pending := tl.pending ++ [(op, caller, tl.now)] }
  | TLOp.tick =>
    some { tl with now := tl.now + 1 }
  | TLOp.execute i =>
    match tl.pending[i]? with
    | none => none
    | some (op, caller, t₀) =>
      if t₀ + tl.delay ≤ tl.now then
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

/-- Number of `tick` clock actions in a wrapper trace — the wrapper time the trace
makes elapse. -/
def countTicks : List TLOp → Nat
  | [] => 0
  | TLOp.tick :: τ => countTicks τ + 1
  | TLOp.queue _ _ :: τ => countTicks τ
  | TLOp.execute _ :: τ => countTicks τ

/-- Exact effect of `queue`: it always succeeds, appends the entry stamped with the
current wrapper time, and touches nothing else — in particular the **base state is
bitwise unchanged**: announcing a privileged change does not yet apply any of it. -/
theorem step2tl_queue_exact (tl : TLState) (op : Op) (caller : Address) :
    step2tl tl (TLOp.queue op caller)
      = some { tl with pending := tl.pending ++ [(op, caller, tl.now)] } := rfl

/-- Exact effect of `tick`: the wrapper clock advances by one and nothing else
changes — in particular the base state is bitwise unchanged. -/
theorem step2tl_tick_exact (tl : TLState) :
    step2tl tl TLOp.tick = some { tl with now := tl.now + 1 } := rfl

/-- Inversion for a successful `execute`: the entry exists, its timelock has fully
elapsed, the base `step` succeeded on the stored operation, and the successor is
exactly the base successor with that entry removed. -/
private theorem inv_step2tl_execute (tl : TLState) (i : Nat) (tl' : TLState)
    (h : step2tl tl (TLOp.execute i) = some tl') :
    ∃ op caller t₀ b',
      tl.pending[i]? = some (op, caller, t₀) ∧
      t₀ + tl.delay ≤ tl.now ∧
      step tl.base op caller = some b' ∧
      tl' = { tl with base := b', pending := tl.pending.eraseIdx i } := by
  simp only [step2tl] at h
  split at h
  · exact absurd h (by simp)
  · rename_i op caller t₀ heq
    split at h
    · rename_i hdelay
      split at h
      · exact absurd h (by simp)
      · rename_i b' hb
        exact ⟨op, caller, t₀, b', heq, hdelay, hb, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-- In the timelocked wrapper, the base protocol state changes **only** through
`execute` of a matured entry: any accepted wrapper step that changed `base` was an
`execute i` whose entry's timelock had fully elapsed, and the base transition is
exactly the stored operation run through the unmodified base `step`. (`queue` and
`tick` leave `base` bitwise unchanged.) -/
theorem tl_base_changes_only_via_execute (tl : TLState) (o : TLOp) (tl' : TLState)
    (h : step2tl tl o = some tl') (h_changed : tl'.base ≠ tl.base) :
    ∃ i op caller t₀,
      o = TLOp.execute i ∧
      tl.pending[i]? = some (op, caller, t₀) ∧
      t₀ + tl.delay ≤ tl.now ∧
      step tl.base op caller = some tl'.base := by
  cases o with
  | queue op caller =>
    cases Option.some.inj h
    exact absurd rfl h_changed
  | tick =>
    cases Option.some.inj h
    exact absurd rfl h_changed
  | execute i =>
    obtain ⟨op, caller, t₀, b', heq, hdelay, hb, rfl⟩ := inv_step2tl_execute tl i tl' h
    exact ⟨i, op, caller, t₀, rfl, heq, hdelay, hb⟩

private theorem execTraceTL_cons_some (tl tl' : TLState) (o : TLOp) (τ : List TLOp)
    (h : step2tl tl o = some tl') : execTraceTL tl (o :: τ) = execTraceTL tl' τ := by
  simp [execTraceTL, h]

private theorem execTraceTL_cons_none (tl : TLState) (o : TLOp) (τ : List TLOp)
    (h : step2tl tl o = none) : execTraceTL tl (o :: τ) = execTraceTL tl τ := by
  simp [execTraceTL, h]

/-- The wrapper clock is exactly the tick count: across any wrapper trace (accepted
and reverted steps alike), `now` grows by precisely the number of `tick` actions.
So "`delay` wrapper-time units" and "`delay` `tick` actions" are interchangeable. -/
theorem execTraceTL_now (tl : TLState) (τ : List TLOp) :
    (execTraceTL tl τ).now = tl.now + countTicks τ := by
  induction τ generalizing tl with
  | nil => simp [execTraceTL, countTicks]
  | cons o τ ih =>
    cases o with
    | queue op caller =>
      rw [execTraceTL_cons_some tl { tl with pending := tl.pending ++ [(op, caller, tl.now)] }
        _ τ rfl]
      have h := ih { tl with pending := tl.pending ++ [(op, caller, tl.now)] }
      dsimp only at h
      rw [h]
      rfl
    | tick =>
      rw [execTraceTL_cons_some tl { tl with now := tl.now + 1 } _ τ rfl]
      have h := ih { tl with now := tl.now + 1 }
      dsimp only at h
      rw [h]
      show tl.now + 1 + countTicks τ = tl.now + (countTicks τ + 1)
      omega
    | execute i =>
      cases h : step2tl tl (TLOp.execute i) with
      | none =>
        rw [execTraceTL_cons_none tl _ τ h, ih tl]
        rfl
      | some tl' =>
        obtain ⟨op, caller, t₀, b', -, -, -, rfl⟩ := inv_step2tl_execute tl i tl' h
        rw [execTraceTL_cons_some tl _ _ τ h]
        have h2 := ih { tl with base := b', pending := tl.pending.eraseIdx i }
        dsimp only at h2
        rw [h2]
        rfl

/-- The timelock length is a constant of the wrapper: no wrapper operation ever
changes `delay`. -/
theorem execTraceTL_delay (tl : TLState) (τ : List TLOp) :
    (execTraceTL tl τ).delay = tl.delay := by
  induction τ generalizing tl with
  | nil => rfl
  | cons o τ ih =>
    cases o with
    | queue op caller =>
      rw [execTraceTL_cons_some tl { tl with pending := tl.pending ++ [(op, caller, tl.now)] }
        _ τ rfl]
      exact ih { tl with pending := tl.pending ++ [(op, caller, tl.now)] }
    | tick =>
      rw [execTraceTL_cons_some tl { tl with now := tl.now + 1 } _ τ rfl]
      exact ih { tl with now := tl.now + 1 }
    | execute i =>
      cases h : step2tl tl (TLOp.execute i) with
      | none =>
        rw [execTraceTL_cons_none tl _ τ h]
        exact ih tl
      | some tl' =>
        obtain ⟨op, caller, t₀, b', -, -, -, rfl⟩ := inv_step2tl_execute tl i tl' h
        rw [execTraceTL_cons_some tl _ _ τ h]
        exact ih { tl with base := b', pending := tl.pending.eraseIdx i }

/-- T8 Half 2, single-step form: **`execute` cannot land early.** If the `i`-th
pending entry carries queue timestamp `t₀` and `execute i` succeeds, the wrapper
clock has already reached `t₀ + delay`. (The contrapositive is the operational
reading: at any instant `now < t₀ + delay` the execution reverts, so the queued
change is provably not yet in force.) -/
theorem tl_execute_requires_delay (tl : TLState) (i : Nat) (tl' : TLState)
    (op : Op) (caller : Address) (t₀ : Nat)
    (h_entry : tl.pending[i]? = some (op, caller, t₀))
    (h : step2tl tl (TLOp.execute i) = some tl') :
    t₀ + tl.delay ≤ tl.now := by
  obtain ⟨op', caller', t₀', b', heq, hdelay, -, -⟩ := inv_step2tl_execute tl i tl' h
  rw [h_entry] at heq
  have h3 : op = op' ∧ caller = caller' ∧ t₀ = t₀' := by simpa using heq
  obtain ⟨-, -, h4⟩ := h3
  omega

/-- T8 `timelock_escape_guarantee` (docs/05-blast-radius.md, Tier 3) — **the
timelock wrapper provably guarantees a `delay`-long exit window.**

DESIGN theorem: the base Apyx model has no timelock (`base_model_has_no_timelock`
— privileged repricing is instantaneous); this theorem proves what adding the
queue mechanism would buy.

Threat model: the attacker holds every key. At some reachable wrapper state `tl`
they `queue` a privileged base operation `op` (e.g. `catastrophicBackstop`,
stamped with the current wrapper time `tl.now`), then submit **any** further
wrapper trace `τ` — more queues, ticks, and executes in any pattern — after which
an `execute` that consumes an entry carrying that stamp succeeds.

Claim: `τ` contains at least `delay` `tick` actions. Since the wrapper clock
advances only via `tick` (`execTraceTL_now`) and `queue` leaves the base state
bitwise untouched (`step2tl_queue_exact`), a full `delay` units of wrapper time
provably separate the public announcement of the change from the earliest instant
it can take effect — and throughout that window the queued operation has
contributed nothing to the base state (`tl_base_changes_only_via_execute`), so
users can still exit against the pre-change parameters. This is the memo's
"escape hatch" guarantee; contrast Half 1, where the window has length 0. -/
theorem timelock_escape_guarantee (tl : TLState) (op : Op) (c : Address)
    (τ : List TLOp) (i : Nat) (tl' : TLState)
    (h_entry : (execTraceTL { tl with pending := tl.pending ++ [(op, c, tl.now)] } τ).pending[i]?
        = some (op, c, tl.now))
    (h_exec : step2tl (execTraceTL { tl with pending := tl.pending ++ [(op, c, tl.now)] } τ)
        (TLOp.execute i) = some tl') :
    tl.delay ≤ countTicks τ := by
  have h1 := tl_execute_requires_delay _ i tl' op c tl.now h_entry h_exec
  have h2 := execTraceTL_now { tl with pending := tl.pending ++ [(op, c, tl.now)] } τ
  have h3 := execTraceTL_delay { tl with pending := tl.pending ++ [(op, c, tl.now)] } τ
  dsimp only at h2 h3
  omega

/-- Non-vacuity of the wrapper (liveness witness): the escape guarantee above is
not achieved by making `execute` unsatisfiable. A concrete run — queue the admin's
`catastrophicBackstop`, let exactly `delay` ticks pass, then execute — succeeds
and actually changes the base redemption price. The timelock delays privileged
changes; it does not block them. -/
theorem timelock_wrapper_is_live :
    ∃ (tl : TLState) (τ : List TLOp),
      countTicks τ = tl.delay ∧
      (execTraceTL tl τ).base.redemptionValue ≠ tl.base.redemptionValue := by
  refine ⟨⟨{ (default : State) with totalCollateralValue := 1, totalSupply_apxUSD := ray }, 0, [], 1⟩,
    [TLOp.queue Op.catastrophicBackstop 0, TLOp.tick, TLOp.execute 0], rfl, ?_⟩
  decide

/-! ## T9 `compartmentalization` — a role compromise's footprint is confined to its subsystem

Base-model theorems (not wrapper/DESIGN): faithful field-level projections of the
Tier-1 trace frames, stating each compromise's blast radius as a *compartment*.

* The yield-distributor compartment is the **vesting pool and its USDC inflow**
  (`vestTotal`/`fullyVestedAmount`/`usdcReserve`/`vestStart`): an all-distributor
  trace leaves every principal field — user apxUSD/apyUSD/USDC/governance
  balances, both supplies, the vault's apxUSD, i.e. everything users own or that
  backs what they own — bitwise unchanged, the reserve can only move **upward**
  (the role pays in, never out), and the combined vest pool
  `fullyVestedAmount + vestTotal` can only move **upward** too (`vestTotal` alone
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
the reserve `usdcReserve` it feeds moves only upward, and the combined vest pool
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
    s.usdcReserve ≤ (execTrace s σ).usdcReserve ∧
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
  single-role attack trace, **no single key extracts principal**. Oracle-alone,
  pauser-alone, and admin-alone leave every user balance *and* the reserve bitwise
  unchanged; distributor-alone leaves user balances unchanged and can only *grow*
  the reserve (it pays in). Each row is a projection of the corresponding Tier-1/2
  trace theorem.
* `admin_rfq_coalition_drains`: the **quantitative coalition** result. The
  `{admin, approved-RFQ-counterparty}` pair drains a victim's entire apxUSD for
  zero USDC — the admin publishes `redemptionValue = 0` via `catastrophicBackstop`
  (dropping it from a healthy `ray`), after which the counterparty's
  `executeRFQRedemption` burns all of the victim's apxUSD and credits exactly
  `amount * 0 / ray = 0` USDC. Net loss = 100% of holdings, in stark contrast to
  the single-key rows.

Headline conclusion (see the docstrings): the security of user funds against a
compromised admin rests **entirely** on the RFQ counterparty set and on the absence
of a rate limit / redemption-price floor — exactly the mechanisms T7 (rate limit)
and T8 (timelock) add. In the current model neither exists, so the coalition drain
is unbounded (cf. T6 `redeem_payout_has_no_cap`). -/

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
  obtain ⟨_, _, _, _, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
  subst hs'
  exact ⟨by simp [burnApxUSD], by simp [burnApxUSD]⟩

/-- Forward direction for `catastrophicBackstop`: the admin's call always succeeds and
publishes the per-unit `redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD`. -/
private theorem step_catastrophicBackstop_forward (s : State) :
    step s Op.catastrophicBackstop s.admin
      = some { s with redemptionValue := s.totalCollateralValue * ray / s.totalSupply_apxUSD,
                      emergencyFlag := true } := by
  show (if (s.admin == s.admin) = true then
          some { s with redemptionValue := s.totalCollateralValue * ray / s.totalSupply_apxUSD,
                        emergencyFlag := true }
        else none) = _
  rw [if_pos (beq_self_eq_true _)]

/-- Forward direction for `executeRFQRedemption`: with the four guards discharged,
the call succeeds and its exact effect is the `burnApxUSD` of the user plus the
priced USDC credit. -/
private theorem step_executeRFQRedemption_forward (s : State) (user : Address)
    (amount : Nat) (caller : Address)
    (hgp : s.globalPause = false)
    (hcp : s.rfqCounterparties.contains caller = true)
    (hbal : amount ≤ s.apxUSDBal user)
    (hres : amount * s.redemptionValue / ray ≤ s.usdcReserve) :
    step s (Op.executeRFQRedemption user amount) caller
      = some { burnApxUSD s user amount with
          usdcReserve := (burnApxUSD s user amount).usdcReserve - amount * s.redemptionValue / ray
          usdcBal := fun a => if a = user then
              (burnApxUSD s user amount).usdcBal a + amount * s.redemptionValue / ray
            else (burnApxUSD s user amount).usdcBal a } := by
  simp only [step]
  rw [if_neg (by rw [hgp]; decide), if_neg (by rw [hcp]; decide),
      if_neg (by omega), if_neg (by omega)]

/-- T10 `single_key_bounds` (docs/05-blast-radius.md, Tier 3) — **no single
compromised key extracts principal.**

For an arbitrary victim `u` and four independent attack traces, each consisting
solely of one role's operations:

* **oracle alone** (`oracle_alone_preserves_balances`): every apxUSD balance and the
  USDC reserve are bitwise unchanged — extraction 0;
* **pauser alone** (`pauser_compartmentalized`): likewise unchanged — extraction 0;
* **distributor alone** (`distributor_compartmentalized`): user apxUSD balances
  unchanged and the reserve only *grows* — the role pays in, extraction 0;
* **admin alone** (`admin_trace_blast_radius`): balances and reserve untouched —
  extraction 0 (the admin's power is over *future* pricing/liveness, not recorded
  holdings; cf. `admin_cannot_touch_balances`).

The contrast with `admin_rfq_coalition_drains` (two keys ⇒ 100% loss) is the value
of key separation: it takes a *coalition* to touch principal. -/
theorem single_key_bounds (s : State) (σO σP σD σA : List (Op × Address))
    (hO : ∀ p ∈ σO, OracleOp p.1) (hP : ∀ p ∈ σP, PauserOp p.1)
    (hD : ∀ p ∈ σD, DistributorOp p.1) (hA : ∀ p ∈ σA, AdminOp p.1) :
    ((execTrace s σO).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σO).usdcReserve = s.usdcReserve) ∧
    ((execTrace s σP).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σP).usdcReserve = s.usdcReserve) ∧
    ((execTrace s σD).apxUSDBal = s.apxUSDBal ∧
      s.usdcReserve ≤ (execTrace s σD).usdcReserve) ∧
    ((execTrace s σA).apxUSDBal = s.apxUSDBal ∧
      (execTrace s σA).usdcReserve = s.usdcReserve) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨ho1, _, _, _, ho5, _⟩ := oracle_alone_preserves_balances s σO hO
    exact ⟨ho1, ho5⟩
  · obtain ⟨hp1, _, _, _, _, _, _, hp8, _⟩ := pauser_compartmentalized s σP hP
    exact ⟨hp1, hp8⟩
  · obtain ⟨hd1, _, _, _, _, _, _, hd8, _⟩ := distributor_compartmentalized s σD hD
    exact ⟨hd1, hd8⟩
  · have h := admin_trace_blast_radius s σA hA
      s.whitelist s.denylist 0 0 0 0 0 false 0 0 0 0
    exact ⟨by simpa using congrArg State.apxUSDBal h,
      by simpa using congrArg State.usdcReserve h⟩

/-- Witness for the coalition drain: a victim (address `0`) holds 100 apxUSD and no
USDC, the redemption price is healthy (`ray` = $1.00) but `totalCollateralValue` is
0, the admin is address `1`, and the approved RFQ counterparty is address `2`. -/
private def coalWitness : State :=
  { (default : State) with
      admin := 1
      rfqCounterparties := [2]
      apxUSDBal := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      totalCollateralValue := 0 }

/-- T10 `admin_rfq_coalition_drains` (docs/05-blast-radius.md, Tier 3) — **the worst
coalition, quantified: `{admin, RFQ-counterparty}` inflicts 100% loss.**

Threat model: the admin key and one approved RFQ-counterparty key are both
compromised. The victim (address `0`) holds 100 apxUSD, no USDC, and the redemption
price starts healthy at `ray` (= $1.00 — the victim could redeem 100 apxUSD for 100
USDC).

The coalition acts in two steps:
1. the **admin** calls `catastrophicBackstop`, which publishes
   `redemptionValue := totalCollateralValue = 0` (`redemption_price_admin_only`;
   the price crashes from `ray` to 0 with no floor and no delay — cf. T8's
   `base_model_has_no_timelock`);
2. the approved **RFQ counterparty** calls `executeRFQRedemption victim 100`, which
   burns all 100 of the victim's apxUSD and credits them `100 * 0 / ray = 0` USDC
   (`rfq_payout_formula`).

Outcome (proved on the concrete witness): the victim's apxUSD goes 100 → 0 while
their USDC stays 0 — a **total, uncompensated loss of principal**. Contrast every
row of `single_key_bounds`, where each key alone extracts 0. This is the memo's
headline: user-fund security against a compromised admin rests entirely on the RFQ
counterparty set and on the missing rate-limit / price-floor (T7/T8). -/
theorem admin_rfq_coalition_drains :
    ∃ (s s1 s2 : State) (victim counterparty amount : Nat),
      0 < amount ∧
      s.apxUSDBal victim = amount ∧ s.usdcBal victim = 0 ∧
      ray ≤ s.redemptionValue ∧
      s.rfqCounterparties.contains counterparty = true ∧
      step s Op.catastrophicBackstop s.admin = some s1 ∧
      s1.redemptionValue = 0 ∧
      step s1 (Op.executeRFQRedemption victim amount) counterparty = some s2 ∧
      s2.apxUSDBal victim = 0 ∧ s2.usdcBal victim = 0 := by
  -- step 1: admin publishes redemptionValue = totalCollateralValue = 0
  let R : State :=
    { coalWitness with redemptionValue := coalWitness.totalCollateralValue,
                       emergencyFlag := true }
  have h1 : step coalWitness Op.catastrophicBackstop coalWitness.admin = some R :=
    step_catastrophicBackstop_forward coalWitness
  have hgp : R.globalPause = false := rfl
  have hcp : R.rfqCounterparties.contains 2 = true := rfl
  have hbal : (100 : Nat) ≤ R.apxUSDBal 0 := Nat.le_refl _
  have hres : 100 * R.redemptionValue / ray ≤ R.usdcReserve := by
    rw [show R.redemptionValue = 0 from rfl, Nat.mul_zero, Nat.zero_div]
    exact Nat.zero_le _
  -- step 2: the approved RFQ counterparty burns the victim's entire apxUSD for 0 USDC
  have h2 := step_executeRFQRedemption_forward R 0 100 2 hgp hcp hbal hres
  obtain ⟨hapx, husdc⟩ := rfq_payout_formula R 0 100 2 _ h2
  refine ⟨coalWitness, R, _, 0, 2, 100, by decide, rfl, rfl, Nat.le_refl _, by decide,
    h1, rfl, h2, ?_, ?_⟩
  · rw [hapx, show R.apxUSDBal 0 = 100 from rfl]
  · rw [husdc, show R.redemptionValue = 0 from rfl, show R.usdcBal 0 = 0 from rfl,
      Nat.mul_zero, Nat.zero_div]

end Apyx
