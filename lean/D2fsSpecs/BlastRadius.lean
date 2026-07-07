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
    s' = createStandardUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

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
operation the role authorizes is `creditYield`, which strictly *adds* funds
(`usdcReserve` and `vestTotal` both increase by the credited amount) and resets the
vesting clock. No user balance, supply, or unlock position is reachable.

Liveness caveat (documented, not a safety violation): because `creditYield` resets
`vestStart := now`, a compromised distributor can repeatedly credit `0` to postpone
the vesting of already-credited yield indefinitely. The vest pool itself
(`vestTotal`) and the reserve never decrease, so no asset is lost. -/

/-- Exact effect of `creditYield`: it demands the yieldDistributor role, adds the
amount to both the USDC reserve and the vest pool, resets the vesting clock, and
touches nothing else. -/
theorem step_creditYield_exact (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.creditYield amount) caller = some s') :
    caller = s.yieldDistributor ∧
    s' = { s with usdcReserve := s.usdcReserve + amount
                  vestTotal := s.vestTotal + amount
                  vestStart := s.now } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- T2 (single step, frame form): a distributor-gated operation demands the
yieldDistributor role, agrees with the pre-state on every field other than
`usdcReserve`/`vestTotal`/`vestStart`, and the two asset-bearing fields among those
can only **increase** — the role can pay in, never extract. (The exact per-field
effect, including the precise `+ amount` increments, is `step_creditYield_exact`
above.) -/
theorem yield_distributor_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : DistributorOp op) (h_step : step s op caller = some s') :
    caller = s.yieldDistributor ∧
    (∀ r v w, { s' with usdcReserve := r, vestTotal := v, vestStart := w }
            = { s with usdcReserve := r, vestTotal := v, vestStart := w }) ∧
    s.usdcReserve ≤ s'.usdcReserve ∧
    s.vestTotal ≤ s'.vestTotal := by
  obtain ⟨amount, rfl⟩ := h_gated
  obtain ⟨hc, rfl⟩ := step_creditYield_exact s amount caller s' h_step
  exact ⟨hc, fun _ _ _ => rfl, Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- T2 (trace form): an arbitrarily long attack trace consisting solely of
distributor-gated operations leaves every field except
`usdcReserve`/`vestTotal`/`vestStart` unchanged, and the reserve and vest pool
never decrease. A yieldDistributor compromise cannot remove a single unit of
value from the system. -/
theorem yield_distributor_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, DistributorOp p.1) :
    (∀ r v w, { execTrace s σ with usdcReserve := r, vestTotal := v, vestStart := w }
            = { s with usdcReserve := r, vestTotal := v, vestStart := w }) ∧
    s.usdcReserve ≤ (execTrace s σ).usdcReserve ∧
    s.vestTotal ≤ (execTrace s σ).vestTotal := by
  induction σ generalizing s with
  | nil => exact ⟨fun _ _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩
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
      refine ⟨fun r v w => ?_, Nat.le_trans hres ihres, Nat.le_trans hvest ihvest⟩
      calc { execTrace s1 σ with usdcReserve := r, vestTotal := v, vestStart := w }
          = { s1 with usdcReserve := r, vestTotal := v, vestStart := w } := ihframe r v w
        _ = { s with usdcReserve := r, vestTotal := v, vestStart := w } := hframe r v w

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
    s' = { s with redemptionValue := s.totalCollateralValue
                  emergencyFlag := true } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Exact effect of `setVestPeriod`. -/
theorem step_setVestPeriod_exact (s : State) (p : Nat) (caller : Address) (s' : State)
    (h : step s (Op.setVestPeriod p) caller = some s') :
    caller = s.admin ∧ s' = { s with vestPeriod := p } := by
  simp only [step] at h
  split at h
  · rename_i hc
    exact ⟨by simpa using hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- T3 (single step, frame form): an admin-gated operation demands the admin role
and agrees with the pre-state on **every** field other than the nine
admin-parameter fields (`whitelist`, `denylist`, `yieldRateMonth`,
`lastRateSetTime`, `collateralYieldBase`, `totalCollateralValue`,
`redemptionValue`, `emergencyFlag`, `vestPeriod`). In particular no balance,
supply, reserve, vest-pool, or unlock-registry field is reachable from the admin
role. -/
theorem admin_frame (s : State) (op : Op) (caller : Address) (s' : State)
    (h_gated : AdminOp op) (h_step : step s op caller = some s') :
    caller = s.admin ∧
    ∀ wl dl yr lt cy tcv rv ef vp,
      { s' with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                lastRateSetTime := lt, collateralYieldBase := cy,
                totalCollateralValue := tcv, redemptionValue := rv,
                emergencyFlag := ef, vestPeriod := vp }
    = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
               lastRateSetTime := lt, collateralYieldBase := cy,
               totalCollateralValue := tcv, redemptionValue := rv,
               emergencyFlag := ef, vestPeriod := vp } := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨bps, rfl⟩ | ⟨amt, rfl⟩ | rfl | ⟨p, rfl⟩ :=
    h_gated
  · obtain ⟨hc, rfl⟩ := step_addToWhitelist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_removeFromWhitelist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_addToDenylist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_removeFromDenylist_exact s a caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, -, -, rfl⟩ := step_setYieldRate_exact s bps caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_handleStressEvent_exact s amt caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_catastrophicBackstop_exact s caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨hc, rfl⟩ := step_setVestPeriod_exact s p caller s' h_step
    exact ⟨hc, fun _ _ _ _ _ _ _ _ _ => rfl⟩

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
unchanged. A compromised admin key can rewrite access lists and pricing/schedule
parameters at will — with the deferred consequences listed in the section header —
but cannot move a single unit of any recorded balance, supply, reserve, or unlock
position. -/
theorem admin_trace_blast_radius (s : State) (σ : List (Op × Address))
    (h_gated : ∀ p ∈ σ, AdminOp p.1) :
    ∀ wl dl yr lt cy tcv rv ef vp,
      { execTrace s σ with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                           lastRateSetTime := lt, collateralYieldBase := cy,
                           totalCollateralValue := tcv, redemptionValue := rv,
                           emergencyFlag := ef, vestPeriod := vp }
    = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
               lastRateSetTime := lt, collateralYieldBase := cy,
               totalCollateralValue := tcv, redemptionValue := rv,
               emergencyFlag := ef, vestPeriod := vp } := by
  induction σ generalizing s with
  | nil => intro _ _ _ _ _ _ _ _ _; rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    intro wl dl yr lt cy tcv rv ef vp
    have h_tail : ∀ q ∈ σ, AdminOp q.1 := fun q hq => h_gated q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail wl dl yr lt cy tcv rv ef vp
    | some s1 =>
      obtain ⟨-, hframe⟩ :=
        admin_frame s op c s1 (h_gated (op, c) List.mem_cons_self) hstep
      calc { execTrace s1 σ with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                                 lastRateSetTime := lt, collateralYieldBase := cy,
                                 totalCollateralValue := tcv, redemptionValue := rv,
                                 emergencyFlag := ef, vestPeriod := vp }
          = { s1 with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                      lastRateSetTime := lt, collateralYieldBase := cy,
                      totalCollateralValue := tcv, redemptionValue := rv,
                      emergencyFlag := ef, vestPeriod := vp } :=
            ih s1 h_tail wl dl yr lt cy tcv rv ef vp
        _ = { s with whitelist := wl, denylist := dl, yieldRateMonth := yr,
                     lastRateSetTime := lt, collateralYieldBase := cy,
                     totalCollateralValue := tcv, redemptionValue := rv,
                     emergencyFlag := ef, vestPeriod := vp } :=
            hframe wl dl yr lt cy tcv rv ef vp

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
    obtain ⟨_, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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
    obtain ⟨_, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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
    obtain ⟨_, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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
    (h_not_owner : caller ≠ u) :
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
    exact Or.inl ⟨by simpa [createStandardUnlock, burnApxUSD, h_ne_next] using h_live,
      by simp [createStandardUnlock, burnApxUSD, h_ne_next]⟩
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
    obtain ⟨_, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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
    s'.redemptionValue = s.totalCollateralValue := by
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
    obtain ⟨_, _, _, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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
    obtain ⟨_, _, hbal, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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

end Apyx
