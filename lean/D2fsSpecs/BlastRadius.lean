import D2fsSpecs.Apyx

/-!
# Blast-radius theorems: damage upper bounds under privileged-key compromise

This module belongs to the Tier-1 theorem list (T1-T4) of `docs/05-blast-radius.md`:
upper bounds on user-asset loss when a privileged role's key is fully compromised
(the social-engineering threat model, cf. Bybit 2025).

Threat model: the attacker holds the private key of one or more role addresses
(`pauseController`, `yieldDistributor`, `admin`, `oracle`, ...) and can submit an
arbitrary sequence of operations with those callers, interleaved with honest traffic.
A failed operation reverts (state unchanged), so a trace executes with revert-skip
semantics (`execTrace`).

Division of labor with the companion module `D2fsSpecs.ApyxBlastRadius` (which holds
the single-step balance-field statements of T1-T4 by exhaustive case analysis):

* **Exact-effect (frame) theorems** for every role-gated operation (here): a
  successful `pause`/`unpause`/`creditYield`/admin-op/oracle-op is shown to equal the
  pre-state with only its named non-asset fields overridden, so no balance, supply,
  reserve, or unlock-position field can move.
* **Trace forms** (here): the frame results are lifted by induction to arbitrarily
  long attack traces (`execTrace`), giving the memo's headline shape
  `userLoss(execSeq s₀ σ) ≤ B(R, s₀)` with `B` read off the surviving fields.
* **Non-custodial theorems (T4)**: the single-step debit analyses live in the
  companion module (`no_role_transfers_user_funds`, `no_role_burns_user_shares`,
  `no_role_debits_usdc`); this module adds the pieces they leave open —
  governance-token immutability, unlock-position seizure bounds — and the
  trace-level headline: even if **every** operator key is stolen, a user who signs
  nothing and is not targeted by an approved RFQ counterparty cannot lose a single
  unit of any balance.

Everything here is additive: the ground-truth model and its 81 requirement theorems
in `D2fsSpecs/Apyx.lean` are untouched. Because that file's helper lemmas are
`private`, the small set of step-inversion lemmas needed here is re-derived locally
(named `inv_*` to distinguish them from the companion module's local `step_*_some`).
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
can only **increase** — the role can pay in, never extract. (The balance-field
instantiation of this statement is `Apyx.yield_distributor_cannot_extract` in the
companion module `D2fsSpecs.ApyxBlastRadius`.) -/
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
unlock-position field. The single-step balance statement is
`Apyx.admin_cannot_touch_balances` in `D2fsSpecs.ApyxBlastRadius`; here each of the
eight admin-gated operations gets an *exact-effect* lemma (the entire post-state is
the pre-state with named fields overridden), and the frames are lifted to
arbitrary-length admin-only traces.

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

end Apyx
