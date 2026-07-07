import D2fsSpecs.BlastRadius

/-!
# In-scope safety: protocol-design soundness against an ordinary (honest-roles) attacker

Third verification pillar (see `docs/06-safety-properties.md`). Distinct from requirement
conformance (`Apyx.lean`) and key-compromise blast radius (`BlastRadius.lean`): here every role
behaves honestly, and we ask whether the *design itself* lets a normal attacker — using only
legitimate operations in a clever order/amount/timing — extract value unfairly or create value
from nothing. Mostly trace-level generalizations of single-step lemmas already proved elsewhere.

Additive: `Apyx.lean` and `BlastRadius.lean` are untouched.
-/

namespace Apyx

/-! ## Local frame lemmas for `pullVestedYield`

(Re-derived: the equivalents in `Apyx.lean` and `BlastRadius.lean` are `private`.) -/

@[simp] private theorem pvS_exchangeRate (s : State) :
    (pullVestedYield s).exchangeRate = s.exchangeRate := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_apxUSDBal (s : State) :
    (pullVestedYield s).apxUSDBal = s.apxUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_apyUSDBal (s : State) :
    (pullVestedYield s).apyUSDBal = s.apyUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_usdcBal (s : State) :
    (pullVestedYield s).usdcBal = s.usdcBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_totalSupply_apxUSD (s : State) :
    (pullVestedYield s).totalSupply_apxUSD = s.totalSupply_apxUSD := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_unlockRequests (s : State) :
    (pullVestedYield s).unlockRequests = s.unlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_flexibleUnlockRequests (s : State) :
    (pullVestedYield s).flexibleUnlockRequests = s.flexibleUnlockRequests := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_nextUnlockId (s : State) :
    (pullVestedYield s).nextUnlockId = s.nextUnlockId := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pvS_vaultApxUSDBal (s : State) :
    (pullVestedYield s).vaultApxUSDBal = s.vaultApxUSDBal + vestedAmount s s.now := by
  unfold pullVestedYield vestedAmount; dsimp only; split <;> simp_all

/-! ## Local step-inversion lemmas

(Re-derived: the equivalents in `BlastRadius.lean` are `private`.) Each characterizes
the guard conditions and the exact successor state of one operation. -/

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
  simp only [step, pvS_exchangeRate] at h
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
  simp only [step, pvS_exchangeRate] at h
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

/-! ## S1 `no_free_value_trace` — no apxUSD value created from nothing

Trace-level lift of the single-step lemma `apxUSD_credit_is_backed`
(`BlastRadius.lean`), which shows that every apxUSD credit is backed by one of
exactly three channels: (1) a 1:1 USDC payment (`depositUSDC` by the credited
address, or `mintApxUSD` paid by the caller), (2) settlement of a standard unlock
position previously funded by the credited address's own apxUSD burn, or
(3) settlement of such a flexible position, minus the early-exit fee.

The contrapositive, lifted by induction over `execTrace`: an address that starts
**penniless** — zero apxUSD, zero USDC to pay in, and no recorded unlock position
of positive amount — and receives no third-party gift, ends **any** trace with
zero apxUSD, no matter what operations it (or anyone else) executes, in any order,
with any amounts. There is no free-mint path at trace level.

The "no third-party gift" hypotheses are honest exclusions, not weaknesses: the
three excluded shapes (`mintApxUSD a _`, `withdraw _ a`, `redeem _ a`) all direct
value to `a` that is fully paid for by the *caller* (USDC at 1:1, or the caller's
own burned apyUSD shares), so they are transfers, not creation. Everything else —
including `a` itself calling every operation with every amount — is quantified
over. -/

/-- `a` holds no extractable value: no apxUSD, no USDC to pay in to a mint, and
every unlock position recorded for `a` (standard or flexible) has amount zero, so
no claim can ever credit `a` with a positive settlement. -/
def Penniless (a : Address) (s : State) : Prop :=
  s.apxUSDBal a = 0 ∧
  s.usdcBal a = 0 ∧
  (∀ id amount cooldownEnd,
    s.unlockRequests id = some (a, amount, cooldownEnd) → amount = 0) ∧
  (∀ id amount requestTime cooldownEnd,
    s.flexibleUnlockRequests id = some (a, amount, requestTime, cooldownEnd) → amount = 0)

/-- Induction step for S1: a single successful operation preserves `Penniless a`,
provided the operation is not a third-party gift directed at `a` (an arbitrage
mint to `a`, or a vault withdraw/redeem naming `a` as receiver — those are paid
for by the caller, hence transfers, and are excluded from the headline). -/
private theorem penniless_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (a : Address) (h : Penniless a s)
    (h_no_mint_gift : ∀ n, op ≠ Op.mintApxUSD a n)
    (h_no_withdraw_gift : ∀ n, op ≠ Op.withdraw n a)
    (h_no_redeem_gift : ∀ n, op ≠ Op.redeem n a) :
    Penniless a s' := by
  obtain ⟨hx, hu, hstd, hflex⟩ := h
  cases op
  case depositUSDC amount =>
    obtain ⟨-, -, -, hle, hs'⟩ := inv_depositUSDC _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · subst hac
      have h0 : amount = 0 := by omega
      subst h0
      exact ⟨by simp [emitEvent, mintApxUSD, hx], by simp [emitEvent, mintApxUSD, hu],
        by simpa [emitEvent, mintApxUSD] using hstd,
        by simpa [emitEvent, mintApxUSD] using hflex⟩
    · exact ⟨by simp [emitEvent, mintApxUSD, hac, hx],
        by simp [emitEvent, mintApxUSD, hac, hu],
        by simpa [emitEvent, mintApxUSD] using hstd,
        by simpa [emitEvent, mintApxUSD] using hflex⟩
  case mintApxUSD to amount =>
    have hta : a ≠ to := fun hr => h_no_mint_gift amount (by rw [hr])
    obtain ⟨-, -, -, -, -, hle, hs'⟩ := inv_mintApxUSD _ _ _ _ _ h_step
    subst hs'
    refine ⟨by simp [emitEvent, mintApxUSD, hta, hx], ?_,
      by simpa [emitEvent, mintApxUSD] using hstd,
      by simpa [emitEvent, mintApxUSD] using hflex⟩
    by_cases hac : a = caller
    · subst hac
      have h0 : amount = 0 := by omega
      simp [emitEvent, mintApxUSD, h0, hu]
    · simp [emitEvent, mintApxUSD, hac, hu]
  case lockApxUSD amount =>
    obtain ⟨-, hle, hs'⟩ := inv_lockApxUSD _ _ _ _ h_step
    subst hs'
    refine ⟨?_, by simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, hu],
      by simpa [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] using hstd,
      by simpa [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] using hflex⟩
    by_cases hac : a = caller
    · subst hac
      have h0 : amount = 0 := by omega
      simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, h0, hx]
    · simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, hac, hx]
  case requestUnlock amount =>
    obtain ⟨-, hle, hs'⟩ := inv_requestUnlock _ _ _ _ h_step
    subst hs'
    refine ⟨?_, by simpa using hu, ?_, by simpa using hflex⟩
    · rw [requestUnlockStep_apxUSDBal]
      by_cases hac : a = caller
      · subst hac
        have h0 : amount = 0 := by omega
        simp [burnApxUSD, h0, hx]
      · simp [burnApxUSD, hac, hx]
    · exact requestUnlockStep_std_penniless s caller amount a hstd (fun h => by rw [h] at hle; omega)
  case claimUnlock id =>
    obtain ⟨owner, amount, cooldownEnd, hreq, -, -, -, hs'⟩ := inv_claimUnlock _ _ _ _ h_step
    subst hs'
    refine ⟨?_, by simp [mintApxUSD, burnUnlockNFT, hu],
      by simpa [mintApxUSD, burnUnlockNFT] using hstd,
      by simpa [mintApxUSD, burnUnlockNFT] using hflex⟩
    by_cases hao : a = owner
    · subst hao
      have h0 : amount = 0 := hstd id amount cooldownEnd hreq
      simp [mintApxUSD, burnUnlockNFT, h0, hx]
    · simp [mintApxUSD, burnUnlockNFT, hao, hx]
  case redeemApxUSD amount =>
    obtain ⟨-, -, hle, -, _, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
    subst hs'
    refine ⟨?_, ?_,
      by simpa [emitEvent, burnApxUSD] using hstd,
      by simpa [emitEvent, burnApxUSD] using hflex⟩ <;>
    · by_cases hac : a = caller
      · subst hac
        have h0 : amount = 0 := by omega
        simp [emitEvent, burnApxUSD, h0, hx, hu]
      · simp [emitEvent, burnApxUSD, hac, hx, hu]
  case withdraw assets receiver =>
    have hra : receiver ≠ a := fun hr => h_no_withdraw_gift assets (by rw [hr])
    obtain ⟨-, -, -, hs'⟩ := inv_withdraw _ _ _ _ _ h_step
    subst hs'
    refine ⟨by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hx],
      by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hu], ?_,
      by simpa [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] using hflex⟩
    intro id amt ce hreq
    simp only [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD,
      pvS_unlockRequests] at hreq
    split at hreq
    · obtain ⟨hca, -, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj hreq
      exact absurd hca hra
    · exact hstd id amt ce hreq
  case redeem shares receiver =>
    have hra : receiver ≠ a := fun hr => h_no_redeem_gift shares (by rw [hr])
    obtain ⟨-, -, -, hs'⟩ := inv_redeem _ _ _ _ _ h_step
    subst hs'
    refine ⟨by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hx],
      by simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hu], ?_,
      by simpa [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] using hflex⟩
    intro id amt ce hreq
    simp only [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD,
      pvS_unlockRequests] at hreq
    split at hreq
    · obtain ⟨hca, -, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj hreq
      exact absurd hca hra
    · exact hstd id amt ce hreq
  case flexibleRequestUnlock amount =>
    obtain ⟨-, hle, hs'⟩ := inv_flexibleRequestUnlock _ _ _ _ h_step
    subst hs'
    refine ⟨?_, by simp [createFlexibleUnlock, burnApxUSD, hu],
      by simpa [createFlexibleUnlock, burnApxUSD] using hstd, ?_⟩
    · by_cases hac : a = caller
      · subst hac
        have h0 : amount = 0 := by omega
        simp [createFlexibleUnlock, burnApxUSD, h0, hx]
      · simp [createFlexibleUnlock, burnApxUSD, hac, hx]
    · intro id amt rt ce hreq
      simp only [createFlexibleUnlock, burnApxUSD] at hreq
      split at hreq
      · obtain ⟨hca, hamt, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj hreq
        subst hca
        omega
      · exact hflex id amt rt ce hreq
  case flexibleClaimUnlock id =>
    obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, -, -, -, hs'⟩ :=
      inv_flexibleClaimUnlock _ _ _ _ h_step
    subst hs'
    refine ⟨?_, by simp [mintApxUSD, burnUnlockNFT, hu],
      by simpa [mintApxUSD, burnUnlockNFT] using hstd,
      by simpa [mintApxUSD, burnUnlockNFT] using hflex⟩
    by_cases hao : a = owner
    · subst hao
      have h0 : amount = 0 := hflex id amount requestTime cooldownEnd hreq
      simp [mintApxUSD, burnUnlockNFT, h0, hx]
    · simp [mintApxUSD, burnUnlockNFT, hao, hx]
  case executeRFQRedemption user amount =>
    obtain ⟨-, -, hle, -, hs'⟩ := inv_executeRFQRedemption _ _ _ _ _ h_step
    subst hs'
    refine ⟨?_, ?_,
      by simpa [burnApxUSD] using hstd,
      by simpa [burnApxUSD] using hflex⟩ <;>
    · by_cases hua : a = user
      · subst hua
        have h0 : amount = 0 := by omega
        simp [burnApxUSD, h0, hx, hu]
      · simp [burnApxUSD, hua, hx, hu]
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact ⟨hx, hu, hstd, hflex⟩)
        | exact absurd h_step (by simp)

/-- The `Penniless` invariant holds across arbitrary traces (revert-skip
semantics), given only that no operation in the trace is a third-party gift
directed at `a`. -/
theorem penniless_invariant (s : State) (σ : List (Op × Address)) (a : Address)
    (h0 : Penniless a s)
    (h_no_gift : ∀ p ∈ σ, (∀ n, p.1 ≠ Op.mintApxUSD a n) ∧
      (∀ n, p.1 ≠ Op.withdraw n a) ∧ (∀ n, p.1 ≠ Op.redeem n a)) :
    Penniless a (execTrace s σ) := by
  induction σ generalizing s with
  | nil => exact h0
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have hhead := h_no_gift (op, c) List.mem_cons_self
    have htail : ∀ q ∈ σ, (∀ n, q.1 ≠ Op.mintApxUSD a n) ∧
        (∀ n, q.1 ≠ Op.withdraw n a) ∧ (∀ n, q.1 ≠ Op.redeem n a) :=
      fun q hq => h_no_gift q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h0 htail
    | some s1 =>
      exact ih s1 (penniless_step s op c s1 hstep a h0 hhead.1 hhead.2.1 hhead.2.2) htail

/-- **S1 `no_free_value_trace`** (docs/06-safety-properties.md, Tier A): no apxUSD
value can be created from nothing, at trace level.

There is no operation sequence `σ` — of any length, any callers, any amounts,
including arbitrary operations signed by `a` itself — by which an address `a`
that starts with zero apxUSD, has zero USDC to pay in, holds no unlock position
of positive amount, and is not the target of a third-party gift
(`mintApxUSD a _` / `withdraw _ a` / `redeem _ a`, each fully paid by its caller),
ends `execTrace` holding a single unit of apxUSD.

This is the trace-level contrapositive of the single-step
`apxUSD_credit_is_backed` (`BlastRadius.lean`): since every apxUSD credit is
backed by a USDC payment or by settlement of the recipient's own previously
funded unlock position, an address with no funding source can never be credited. -/
@[formalMeta "No free value"
  "No operation sequence of any length — including operations signed by the address itself — lets an address that starts penniless and receives no third-party gift end up holding a single unit of apxUSD: value cannot be created from nothing."
  mainTheorem]
theorem no_free_value_trace (s : State) (σ : List (Op × Address)) (a : Address)
    (h0 : Penniless a s)
    (h_no_gift : ∀ p ∈ σ, (∀ n, p.1 ≠ Op.mintApxUSD a n) ∧
      (∀ n, p.1 ≠ Op.withdraw n a) ∧ (∀ n, p.1 ≠ Op.redeem n a)) :
    (execTrace s σ).apxUSDBal a = 0 :=
  (penniless_invariant s σ a h0 h_no_gift).1

/-! ## S2 `solvency_preserved` — aggregate overcollateralization is maintained

Trace-level lift of the single-step `req_overcollateralization_limit` (`Apyx.lean`):
the total apxUSD claim outstanding (supply plus the required overcollateralization
margin) never exceeds the market value of what backs it (the collateral basket plus
the USDC reserve).

`req_overcollateralization_limit` needs two side-conditions at the pre-state, beyond
the invariant itself: `h_bal` (no single address's apxUSD balance exceeds total
supply) and `h_rv` (the redemption price is at most par, `≤ ray`). In a real
ERC-20-style ledger both are automatic corollaries of the ledger identity
`Σ_a balance a = totalSupply` — a conservation fact maintained by construction
because `mintApxUSD`/`burnApxUSD` always move one address's balance and the total by
the *same* amount in lockstep. But this abstract model represents `apxUSDBal` as a
bare `Address → Nat` with no finite-support/summation structure recording that
identity, so the per-address bound cannot honestly be *re-derived* from scratch at
every step of an arbitrary trace: e.g. knowing `bal x ≤ total` and `bal y ≤ total`
individually does not, by itself, bound `bal x` against the *smaller* total left
after burning from `y`, without also knowing how `x` and `y`'s claims sum against
the total — exactly the fact this model does not carry. Rather than paper over that
gap, `solvency_preserved` takes `WellFormed` as an honest hypothesis re-supplied at
*every* point along the trace (`∀ n, WellFormed (execTrace s (σ.take n))`), not
something it manufactures from a bare initial condition.

Scope, exactly mirroring `req_overcollateralization_limit`: `claimUnlock` and
`flexibleClaimUnlock` are excluded because they re-mint apxUSD against an unlock
obligation the aggregate state does not track as a liability, and
`handleStressEvent` is excluded because it models an exogenous collateral loss that
deliberately eats into the margin. `catastrophicBackstop` needs no separate
exclusion here: it does not move any of the four quantities `Solvent` compares, so it
trivially preserves solvency itself — it only pushes `redemptionValue` (potentially
above `ray`) for *future* steps, which surfaces honestly as a heavier `WellFormed`
proof burden on the caller for the remainder of the trace, not as unsoundness. -/

/-- `Solvent s`: aggregate collateralization is maintained — outstanding apxUSD claims
plus the required margin never exceed the collateral basket plus the USDC reserve.
Exactly `req_overcollateralization_limit`'s invariant, named for trace-level use. -/
def Solvent (s : State) : Prop :=
  s.totalSupply_apxUSD + s.overcollateralizationBuffer ≤ s.totalCollateralValue + s.usdcReserve

/-- The two ledger-consistency side-conditions `req_overcollateralization_limit` needs
at every step: no address's apxUSD balance exceeds total supply, and the redemption
price is at most par. See the module docstring above for why this is taken as a
hypothesis re-verified along the trace rather than derived from a bare initial
condition. -/
def WellFormed (s : State) : Prop :=
  (∀ a, s.apxUSDBal a ≤ s.totalSupply_apxUSD) ∧ s.redemptionValue ≤ ray

/-- Induction step for S2: a single successful operation preserves `Solvent`, given
`WellFormed` at the pre-state and that the operation is none of the three
`req_overcollateralization_limit` must exclude. This *is*
`req_overcollateralization_limit`, restated with the `Solvent`/`WellFormed` names. -/
theorem solvency_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (h_solvent : Solvent s) (h_wf : WellFormed s)
    (h_not_claim : ∀ id, op ≠ Op.claimUnlock id)
    (h_not_flex_claim : ∀ id, op ≠ Op.flexibleClaimUnlock id)
    (h_not_stress : ∀ a, op ≠ Op.handleStressEvent a) :
    Solvent s' :=
  req_overcollateralization_limit s op caller s' h_step h_solvent h_wf.1 h_wf.2
    h_not_claim h_not_flex_claim h_not_stress

/-- **S2 `solvency_preserved`** (docs/06-safety-properties.md, Tier A): aggregate
overcollateralization is preserved across arbitrary traces (revert-skip semantics),
given that ledger well-formedness holds at every point visited along the way and the
trace never calls `claimUnlock`/`flexibleClaimUnlock`/`handleStressEvent`. -/
@[formalMeta "Solvency preservation"
  "Aggregate overcollateralization (apxUSD supply + buffer ≤ collateral + USDC reserve) is preserved across arbitrary operation traces, given ledger well-formedness at every step and excluding the three documented margin-consuming operations."
  mainTheorem]
theorem solvency_preserved (s : State) (σ : List (Op × Address))
    (h_solvent : Solvent s)
    (h_wf : ∀ n, WellFormed (execTrace s (σ.take n)))
    (h_excl : ∀ p ∈ σ, (∀ id, p.1 ≠ Op.claimUnlock id) ∧
      (∀ id, p.1 ≠ Op.flexibleClaimUnlock id) ∧ (∀ a, p.1 ≠ Op.handleStressEvent a)) :
    Solvent (execTrace s σ) := by
  induction σ generalizing s with
  | nil => exact h_solvent
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have hhead := h_excl (op, c) List.mem_cons_self
    have htail : ∀ q ∈ σ, (∀ id, q.1 ≠ Op.claimUnlock id) ∧
        (∀ id, q.1 ≠ Op.flexibleClaimUnlock id) ∧ (∀ a, q.1 ≠ Op.handleStressEvent a) :=
      fun q hq => h_excl q (List.mem_cons_of_mem _ hq)
    have hwf0 : WellFormed s := by simpa [execTrace] using h_wf 0
    simp only [execTrace]
    cases hstep : step s op c with
    | none =>
      refine ih s h_solvent ?_ htail
      intro n
      simpa [execTrace, hstep] using h_wf (n + 1)
    | some s1 =>
      have hsolvent1 : Solvent s1 :=
        solvency_step s op c s1 hstep h_solvent hwf0 hhead.1 hhead.2.1 hhead.2.2
      refine ih s1 hsolvent1 ?_ htail
      intro n
      simpa [execTrace, hstep] using h_wf (n + 1)

/-! ## S3 `rounding_favors_protocol` — vault conversions round in the protocol's favor

Pure `Nat`-arithmetic strengthening of `req_erc4626_compliance` (`Apyx.lean`), which
already proves (2) both conversion round-trips never credit the user (`convertToAssets
∘ convertToShares ≤ id` and its mirror `convertToShares ∘ convertToAssets ≤ id`) and (3)
`previewDeposit ≤ previewWithdraw` (`lockShares` rounds down relative to
`withdrawShares`'s round-up). New here is the direct payoff of that withdraw-side
rounding: redeeming the shares `withdrawShares` prescribes for a target asset amount
returns *at least* that amount back, i.e. the vault never under-collects shares for
what it pays out. No `step`/`Op` case analysis anywhere in this section — these are
small, self-contained facts about `Nat` division, so there is no deep-recursion risk. -/

/-- Ceiling division always rounds its own numerator down against itself: for any
positive divisor `d`, `(n + d - 1) / d * d ≥ n`. Core `Nat` fact, no protocol
definitions involved. -/
private theorem nat_ceilDiv_mul_ge (n d : Nat) (hd : 0 < d) :
    n ≤ (n + d - 1) / d * d := by
  rw [Nat.mul_comm]
  have hdm : d * ((n + d - 1) / d) + (n + d - 1) % d = n + d - 1 :=
    Nat.div_add_mod (n + d - 1) d
  have hmod : (n + d - 1) % d < d := Nat.mod_lt _ hd
  omega

/-- The `withdrawShares` conversion rounds up: burning the number of shares it
prescribes for a target `assets` amount, then converting those shares back through
`redeemAssets`, returns *at least* the originally requested `assets` — the vault never
under-collects shares for what it pays out. The mirror image of the round-down
direction already established by `req_erc4626_compliance`. -/
theorem withdrawShares_rounds_up (assets rate : Nat) (hrate : 0 < rate) :
    assets ≤ redeemAssets (withdrawShares assets rate) rate := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  unfold redeemAssets withdrawShares
  exact (Nat.le_div_iff_mul_le hray).mpr (nat_ceilDiv_mul_ge (assets * ray) rate hrate)

/-- **S3 `rounding_favors_protocol`** (docs/06-safety-properties.md, Tier A): the
vault's share/asset conversions round in the protocol's favor in every direction of
both conversion families, so no user can extract value purely through rounding.

(1) and (2) restate the two round-trip bounds already proved in `req_erc4626_compliance`
(`Apyx.lean`): converting assets to shares and back (`convertToShares` then
`convertToAssets`), or shares to assets and back, never credits the user more value
than they started with — ERC-4626's core rounding mandate, "round against the user."

(3) is new: applying the same mandate to the *withdraw* direction. `withdrawShares` —
used by `Op.withdraw` to compute how many shares to burn for a target asset amount —
rounds up (`withdrawShares_rounds_up`, built on `nat_ceilDiv_mul_ge`), the mirror image
of `convertToShares`'s round-down. So redeeming the prescribed shares back through
`convertToAssets` returns at least the originally requested amount: the vault never
under-collects shares for what it pays out on a withdrawal. Together, (1)-(3) show
every conversion direction in the vault rounds against the depositor/withdrawer and in
favor of the protocol's solvency. -/
theorem rounding_favors_protocol (s : State) :
    (∀ assets, convertToAssets s (convertToShares s assets) ≤ assets) ∧
    (∀ shares, convertToShares s (convertToAssets s shares) ≤ shares) ∧
    (∀ assets, 0 < s.exchangeRate →
      assets ≤ convertToAssets s (withdrawShares assets s.exchangeRate)) :=
  ⟨(req_erc4626_compliance s).2.2.2.2.1,
   (req_erc4626_compliance s).2.2.2.2.2.1,
   fun assets hrate => withdrawShares_rounds_up assets s.exchangeRate hrate⟩

/-! ## S4 `no_dilution` — a new deposit does not reduce an existing holder's
redeemable value

`req_exchange_rate_non_decreasing` (`Apyx.lean`) only tracks monotonicity across the
*passage of time* (`s.now := s.now + dt`); it says nothing about monotonicity across a
`lockApxUSD` deposit by someone else, which is the actual dilution question. That fact
is established fresh here: floor-rounding the newly minted shares
(`lockShares amount s.exchangeRate = amount * ray / s.exchangeRate`) means a deposit can
only raise, never lower, the implied exchange rate of the enlarged pool — new shares
are minted at a rate no more generous than the true backing ratio, so existing
holders' claim per share cannot fall. Proved via the single-op inversion lemma
`inv_lockApxUSD` plus this fresh arithmetic fact — no `cases op`. -/

/-- Pure `Nat` fact underlying `no_dilution`: minting `amount * ray / R` new shares
against `TA + amount` enlarged backing (a fresh `lockApxUSD amount` deposit priced at
rate `R`) never lowers `R`, provided `R` does not already overstate the pre-deposit
backing (`R * TS ≤ TA * ray`, satisfied whenever `R` is the true `computeExchangeRate`
of the pre-state) and there is at least one pre-existing share (`TS > 0`, i.e. an
existing holder to protect from dilution). -/
@[simp] private theorem computeExchangeRate_emitEvent (s : State) (n : String) (a : List Nat) :
    computeExchangeRate (emitEvent s n a) = computeExchangeRate s := by
  simp [emitEvent, computeExchangeRate, totalAssets, vestedAmount, newlyVestedAmount]

@[simp] private theorem computeExchangeRate_updateExchangeRate (s : State) :
    computeExchangeRate (updateExchangeRate s) = computeExchangeRate s := by
  simp [updateExchangeRate, computeExchangeRate, totalAssets, vestedAmount, newlyVestedAmount]

private theorem rate_non_decreasing_of_deposit
    (TA TS amount R : Nat) (hTS : 0 < TS) (hbacked : R * TS ≤ TA * ray) :
    R ≤ (TA + amount) * ray / (TS + amount * ray / R) := by
  have hshpos : 0 < TS + amount * ray / R :=
    calc 0 < TS := hTS
      _ ≤ TS + amount * ray / R := Nat.le_add_right _ _
  rw [Nat.le_div_iff_mul_le hshpos]
  have h2 : R * (amount * ray / R) ≤ amount * ray := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  calc R * (TS + amount * ray / R)
      = R * TS + R * (amount * ray / R) := Nat.mul_add R TS (amount * ray / R)
    _ ≤ TA * ray + amount * ray := Nat.add_le_add hbacked h2
    _ = (TA + amount) * ray := (Nat.add_mul TA amount ray).symm

/-- **S4 `no_dilution`** (docs/06-safety-properties.md, Tier A): a new deposit by a
different caller does not reduce an existing holder's redeemable apxUSD value.

For a holder `h` distinct from the depositing `caller`: (a) `h`'s apyUSD balance is
untouched by the lock (`Op.lockApxUSD` mints only to `caller`, via `inv_lockApxUSD`),
and (b) the implied exchange rate does not fall (`rate_non_decreasing_of_deposit`),
given the pre-state rate `s.exchangeRate` does not already overstate backing
(`hbacked`) and there is at least one existing share (`hTS`, i.e. someone to protect).
Combining (a) and (b): `h`'s redeemable value under `convertToAssets`, computed at the
same (unchanged) share balance, can only rise. -/
theorem no_dilution (s : State) (amount : Nat) (caller h : Address) (s' : State)
    (h_step : step s (Op.lockApxUSD amount) caller = some s')
    (hh : h ≠ caller) (hTS : 0 < s.totalSupply_apyUSD)
    (hbacked : s.exchangeRate * s.totalSupply_apyUSD ≤ totalAssets s * ray) :
    s'.apyUSDBal h = s.apyUSDBal h ∧
    convertToAssets s (s.apyUSDBal h) ≤ convertToAssets s' (s'.apyUSDBal h) := by
  obtain ⟨-, -, hs'⟩ := inv_lockApxUSD s amount caller s' h_step
  have hbal : s'.apyUSDBal h = s.apyUSDBal h := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, hh]
  have hvs : s'.vestStart = s.vestStart := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hvt : s'.vestTotal = s.vestTotal := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hnow : s'.now = s.now := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hvp : s'.vestPeriod = s.vestPeriod := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hfv : s'.fullyVestedAmount = s.fullyVestedAmount := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hvbal : s'.vaultApxUSDBal = s.vaultApxUSDBal + amount := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hva : vestedAmount s' s'.now = vestedAmount s s.now := by
    unfold vestedAmount newlyVestedAmount; rw [hfv, hvs, hvt, hnow, hvp]
  have hTA : totalAssets s' = totalAssets s + amount := by
    unfold totalAssets; rw [hvbal, hva]; omega
  have hTS' : s'.totalSupply_apyUSD = s.totalSupply_apyUSD + lockShares amount s.exchangeRate := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, lockShares]
  have hTSpos : s'.totalSupply_apyUSD ≠ 0 := by rw [hTS']; omega
  have hcomp : s'.exchangeRate = computeExchangeRate s' := by
    rw [hs']
    simp [emitEvent, updateExchangeRate, computeExchangeRate, totalAssets, vestedAmount,
      newlyVestedAmount, mintApyUSD, burnApxUSD]
  have hrate : s'.exchangeRate
      = (totalAssets s + amount) * ray / (s.totalSupply_apyUSD + lockShares amount s.exchangeRate) := by
    rw [hcomp]; unfold computeExchangeRate
    rw [if_neg hTSpos, hTA, hTS']
  have hmono : s.exchangeRate ≤ s'.exchangeRate := by
    rw [hrate]
    exact rate_non_decreasing_of_deposit (totalAssets s) s.totalSupply_apyUSD amount
      s.exchangeRate hTS hbacked
  refine ⟨hbal, ?_⟩
  rw [hbal]
  unfold convertToAssets redeemAssets
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hmono)

/-! ## S5 `no_inflation_attack` — vault custody cannot be inflated for free

The classic ERC-4626 donation/inflation attack — an attacker directly injecting assets
into the vault's custody balance without minting shares, to skew the exchange rate
against later depositors' rounding — requires a "raw transfer into custody" primitive.
`req_no_rehypothecation` (`Apyx.lean`) already proves, by exhaustive case analysis over
all constructors of the closed `Op` type, that only three operations can ever change
`vaultApxUSDBal` at all: `lockApxUSD`, `withdraw`, `redeem`. We reuse that theorem
directly (rather than re-deriving it, which is what risks the kernel deep-recursion
this file must avoid) to characterize exactly when `vaultApxUSDBal` can *rise*.

**Narrowing versus the anticipated shape.** The original working hypothesis (see the
design memo) was that `lockApxUSD` and `creditYield` are the two channels able to raise
`vaultApxUSDBal`. That hypothesis is refined by this audit in two directions:

* `creditYield` is **refuted** as a same-step raising channel: `step_creditYield_exact`
  (`BlastRadius.lean`) shows a single `creditYield` step touches only
  `usdcReserve`/`vestTotal`/`vestStart`, leaving `vaultApxUSDBal` completely unchanged
  (`donation_free_no_creditYield` below). `creditYield` funds the *future* vesting
  stream; it does not itself move custody.
* `withdraw`/`redeem` are **added**: both first call `pullVestedYield` internally
  (realizing the vault's already-vested-but-not-yet-materialized yield into custody)
  before paying assets out. If the payout is smaller than the freshly realized vested
  amount, custody nets *higher* than before the step. This is not a donation, though:
  `totalAssets` (`vaultApxUSDBal` plus the *unrealized* vested remainder) is exactly
  conserved by `pullVestedYield` — realizing vested yield only moves value from the
  unrealized column to the realized one, never creates it — so the realized-side rise
  is capped by, and exactly offset within, `vestedAmount s s.now`, a quantity that only
  the privileged `creditYield` (yield-distributor) channel can ever grow, and one
  already priced into every holder's `convertToAssets` (via `exchangeRate`/
  `totalAssets`) even before it is realized. -/

/-- Narrowing note: a single `creditYield` step never changes `vaultApxUSDBal` at all
(so in particular it never raises it) — refuting the audit's initial working
hypothesis that `creditYield` was a second same-step raising channel alongside
`lockApxUSD`. -/
theorem donation_free_no_creditYield (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s') :
    s'.vaultApxUSDBal = s.vaultApxUSDBal := by
  obtain ⟨-, hs'⟩ := step_creditYield_exact s amount caller s' h_step
  rw [hs']

/-- **S5 `donation_free`** (single-step): whenever a step strictly raises the vault's
custody balance, it is exactly one of the three channels `req_no_rehypothecation`
identifies, with the exact arithmetic of the rise pinned down: `lockApxUSD` raises it
by precisely the deposited `amount`; `withdraw`/`redeem` can raise it only up to
`vestedAmount s s.now` above the pre-state value (bounded realization of already-vested,
already-priced-in yield — see the module docstring above for why this is not a
donation). -/
theorem donation_free (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (h_gt : s.vaultApxUSDBal < s'.vaultApxUSDBal) :
    (∃ amount, op = Op.lockApxUSD amount ∧ s'.vaultApxUSDBal = s.vaultApxUSDBal + amount) ∨
    (∃ amount r, op = Op.withdraw amount r ∧
      s'.vaultApxUSDBal ≤ s.vaultApxUSDBal + vestedAmount s s.now) ∨
    (∃ shares r, op = Op.redeem shares r ∧
      s'.vaultApxUSDBal ≤ s.vaultApxUSDBal + vestedAmount s s.now) := by
  have h_ne : s'.vaultApxUSDBal ≠ s.vaultApxUSDBal := by omega
  obtain ⟨h_case, h_lock, h_wd, h_rd⟩ := req_no_rehypothecation s op caller s' h_step
  rcases h_case h_ne with ⟨x, hx⟩ | ⟨x, r, hx⟩ | ⟨x, r, hx⟩
  · exact Or.inl ⟨x, hx, h_lock x hx⟩
  · refine Or.inr (Or.inl ⟨x, r, hx, ?_⟩)
    rw [h_wd x r hx, pvS_vaultApxUSDBal]; omega
  · refine Or.inr (Or.inr ⟨x, r, hx, ?_⟩)
    rw [h_rd x r hx, pvS_vaultApxUSDBal]; omega

/-- **S5 `no_inflation_attack`** (docs/06-safety-properties.md, Tier A): the classic
ERC-4626 donation/inflation attack is structurally impossible in this model for an
ordinary (non-privileged) attacker. Restated positively from `donation_free`: whenever
a single step raises the vault's custody balance, either (a) it is `lockApxUSD`, and
the raise is exactly the caller's own paid-in deposit — one-for-one matched by an equal
debit to the caller's own apxUSD balance (`inv_lockApxUSD`'s `amount ≤ s.apxUSDBal
caller`) — a purchase, not a donation; or (b)/(c) it is `withdraw`/`redeem` realizing
already-vested yield ahead of paying it out, a channel only the privileged `creditYield`
role can ever grow and which is already priced into every holder's redeemable value
before realization. There is no operation in the closed `Op` type — exhaustively, by
`req_no_rehypothecation` — that credits `vaultApxUSDBal` outside these two accounted,
backed channels: no "raw donation" primitive exists. -/
theorem no_inflation_attack (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (h_gt : s.vaultApxUSDBal < s'.vaultApxUSDBal) :
    (∃ amount, op = Op.lockApxUSD amount ∧ amount ≤ s.apxUSDBal caller ∧
      s'.vaultApxUSDBal = s.vaultApxUSDBal + amount) ∨
    (∃ amount r, op = Op.withdraw amount r) ∨
    (∃ shares r, op = Op.redeem shares r) := by
  rcases donation_free s op caller s' h_step h_gt with
    ⟨x, hx, heq⟩ | ⟨x, r, hx, -⟩ | ⟨x, r, hx, -⟩
  · subst hx
    obtain ⟨-, hle, -⟩ := inv_lockApxUSD s x caller s' h_step
    exact Or.inl ⟨x, rfl, hle, heq⟩
  · exact Or.inr (Or.inl ⟨x, r, hx⟩)
  · exact Or.inr (Or.inr ⟨x, r, hx⟩)

/-! ## S6 `caller_net_nonpositive` — value-weighted no-free-money for the acting caller

S1 covers apxUSD-count only. The full in-scope no-free-money law is value-weighted: an
address's holdings, summed in one common accounting unit, cannot rise for the address
*acting as caller* except by what it itself pays into the step. `valueAt R s a` is that
common unit: apxUSD and USDC both at par (1 raw unit = 1 raw unit), apyUSD converted to
its redeemable apxUSD via `redeemAssets` at an explicit rate `R`. `callerValue` is the
headline reading of that ledger at a state's own *live* rate (`s.exchangeRate`) — the
same rate `convertToAssets`/ERC4626 `previewRedeem` would quote right now.

**Why `valueAt` takes `R` explicitly instead of always reading the live rate.** Three of
the four value-moving ops (`lockApxUSD`, `withdraw`, `redeem`) call `updateExchangeRate`
before returning, so `s'.exchangeRate` can differ from `s.exchangeRate` *within the same
step*. That drift is the S4 phenomenon (rate is non-decreasing, rounding-favors-protocol
surplus spread pro-rata over the whole pool) — a diffuse, pool-wide appreciation shared by
every current apyUSD holder, not value the acting caller personally extracts from this one
step. Bounding the *caller's own delta* cleanly requires pricing both the pre- and
post-state holdings at the **same** rate; mixing rates (pre-state holdings at the old rate,
post-state holdings at the new, already-bumped rate) reduces to a genuinely harder question
— by how much can a single `updateExchangeRate` recomputation move the rate, expressed as a
bound on the whole pool rather than one address — that is exactly the kind of fiddly
cross-denominator Nat arithmetic the design memo flags as a risk for the trace-level sum.
Rather than force it, the fixed-rate law below is proved exactly, for all five op instances
across the four named families (deposit/lock/redeem/withdraw), and it is noted for the two
ops that never touch the rate (`depositUSDC`, `redeemApxUSD`) that the fixed-rate and
live-rate readings coincide, so those two carry the *full, unqualified* live result. -/

/-- `a`'s holdings priced in one common unit at an explicit rate `R`: apxUSD and USDC both
at par, apyUSD converted to its redeemable apxUSD equivalent via `redeemAssets R`. -/
def valueAt (R : Nat) (s : State) (a : Address) : Nat :=
  s.apxUSDBal a + redeemAssets (s.apyUSDBal a) R + s.usdcBal a

/-- **`callerValue`**: the headline S6 ledger, `a`'s holdings priced at the state's own
live (mark-to-market) exchange rate. -/
def callerValue (s : State) (a : Address) : Nat := valueAt s.exchangeRate s a

/-- Core arithmetic fact behind the `lockApxUSD` case: converting a fresh deposit of
`amount` into shares (`lockShares`, floor rounding) and immediately pricing the enlarged
share balance back at the *same* rate `R` never returns more than the pre-existing balance's
value plus the deposited `amount` — the floor rounding in `lockShares` cannot manufacture
extra redeemable value for the depositor at a fixed rate. Pure `Nat` fact, no protocol
definitions beyond `lockShares`/`redeemAssets` unfolded. -/
private theorem redeemAssets_add_lockShares_le (x amount R : Nat) :
    redeemAssets (x + lockShares amount R) R ≤ redeemAssets x R + amount := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  have hy : amount * ray / R * R ≤ amount * ray := Nat.div_mul_le_self _ _
  unfold redeemAssets lockShares
  calc (x + amount * ray / R) * R / ray
      = (x * R + amount * ray / R * R) / ray := by rw [Nat.add_mul]
    _ ≤ (x * R + amount * ray) / ray := Nat.div_le_div_right (Nat.add_le_add_left hy _)
    _ = x * R / ray + amount := Nat.add_mul_div_right _ _ hray

/-- Ceiling-rounded redemption price never exceeds `ray`-scaled par by more than what the
`redemptionValue ≤ ray` no-premium-redemption invariant already bounds: paying out
`amount * R / ray` USDC for `amount` burned apxUSD, at `R ≤ ray`, never exceeds `amount`.
Same side-condition `S2`'s `WellFormed` already carries (`redemptionValue ≤ ray`). -/
private theorem redemptionValue_div_ray_le (amount R : Nat) (h_rv : R ≤ ray) :
    amount * R / ray ≤ amount := by
  have hray : 0 < ray := Nat.pow_pos (by decide)
  calc amount * R / ray ≤ amount * ray / ray := Nat.div_le_div_right (Nat.mul_le_mul_left amount h_rv)
    _ = amount := Nat.mul_div_cancel amount hray

/-- `depositUSDC`: the caller's `callerValue` (at the fixed pre-step rate) is exactly
unchanged — USDC converts to apxUSD 1:1, no rounding, no rate movement. -/
theorem caller_value_depositUSDC (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    valueAt s.exchangeRate s' caller = callerValue s caller := by
  obtain ⟨-, -, -, hle, hs'⟩ := inv_depositUSDC s amount caller s' h_step
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller + amount := by
    rw [hs']; simp [emitEvent, mintApxUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller := by
    rw [hs']; simp [emitEvent, mintApxUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller - amount := by
    rw [hs']; simp [emitEvent, mintApxUSD]
  unfold callerValue valueAt
  rw [hx, hy, hu]
  omega

/-- `depositUSDC` never moves the exchange rate, so the fixed-rate and live readings of
`callerValue` coincide: the deposit case carries the full, unqualified live-rate result. -/
theorem caller_value_depositUSDC_live (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.depositUSDC amount) caller = some s') :
    callerValue s' caller = callerValue s caller := by
  obtain ⟨-, -, -, -, hs'⟩ := inv_depositUSDC s amount caller s' h_step
  have hr : s'.exchangeRate = s.exchangeRate := by rw [hs']; simp [emitEvent, mintApxUSD]
  show valueAt s'.exchangeRate s' caller = callerValue s caller
  rw [hr]
  exact caller_value_depositUSDC s amount caller s' h_step

/-- `lockApxUSD`: at the fixed pre-step rate, the caller's `callerValue` cannot rise beyond
the `amount` it locked — floor-rounding the newly minted shares (`lockShares`) cannot
manufacture redeemable value beyond what was paid in. The live-rate reading may still be
*higher* than this (S4's pool-wide rate appreciation, shared by every holder) — an honestly
scoped, distinct effect, not the caller's own extraction from this step. -/
theorem caller_value_lockApxUSD_fixedRate (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    valueAt s.exchangeRate s' caller ≤ callerValue s caller := by
  obtain ⟨-, hle, hs'⟩ := inv_lockApxUSD s amount caller s' h_step
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller - amount := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller + lockShares amount s.exchangeRate := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller := by
    rw [hs']; simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
  unfold callerValue valueAt
  rw [hx, hy, hu]
  have hb := redeemAssets_add_lockShares_le (s.apyUSDBal caller) amount s.exchangeRate
  omega

/-- `redeemApxUSD` (ERC-20-style redemption): at the fixed pre-step rate (the op never
touches `exchangeRate` at all, so this is also the live-rate result), the caller's
`callerValue` cannot rise beyond rounding: the USDC credited for `amount` burned apxUSD is
`amount * redemptionValue / ray`, which — given the standing no-premium-redemption
invariant `redemptionValue ≤ ray` (the same side-condition `S2`'s `WellFormed` carries) —
never exceeds `amount`. -/
theorem caller_value_redeemApxUSD (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') (h_rv : s.redemptionValue ≤ ray) :
    valueAt s.exchangeRate s' caller ≤ callerValue s caller := by
  obtain ⟨-, -, hle, -, _, hs'⟩ := inv_redeemApxUSD s amount caller s' h_step
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller - amount := by
    rw [hs']; simp [emitEvent, burnApxUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller := by
    rw [hs']; simp [emitEvent, burnApxUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller + amount * s.redemptionValue / ray := by
    rw [hs']; simp [emitEvent, burnApxUSD]
  unfold callerValue valueAt
  rw [hx, hy, hu]
  have hb := redemptionValue_div_ray_le amount s.redemptionValue h_rv
  omega

/-- `redeemApxUSD` never moves the exchange rate: the fixed-rate result above is also the
full, unqualified live-rate result. -/
theorem caller_value_redeemApxUSD_live (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.redeemApxUSD amount) caller = some s') (h_rv : s.redemptionValue ≤ ray) :
    callerValue s' caller ≤ callerValue s caller := by
  obtain ⟨-, -, -, -, _, hs'⟩ := inv_redeemApxUSD s amount caller s' h_step
  have hr : s'.exchangeRate = s.exchangeRate := by rw [hs']; simp [emitEvent, burnApxUSD]
  show valueAt s'.exchangeRate s' caller ≤ callerValue s caller
  rw [hr]
  exact caller_value_redeemApxUSD s amount caller s' h_step h_rv

/-- `withdraw`: the withdrawn `assets` leave the caller's `apyUSDBal` (via `pullVestedYield`
then `burnApyUSD`) and land in a cooldown *unlock request*, not directly in `apxUSDBal`/
`usdcBal` — the three fields `callerValue` tracks. So, at the fixed pre-step rate, the
caller's `callerValue` can only *fall* here: `apxUSDBal`/`usdcBal` are untouched and
`apyUSDBal` only shrinks (monotone `redeemAssets` in the first argument). The eventual
`claimUnlock` crediting `apxUSDBal` later is exactly the transfer S1 already excludes as a
caller-paid-for credit, not a gift. -/
theorem caller_value_withdraw_fixedRate (s : State) (assets : Nat) (receiver caller : Address)
    (s' : State) (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    valueAt s.exchangeRate s' caller ≤ callerValue s caller := by
  obtain ⟨-, -, -, hs'⟩ := inv_withdraw s assets receiver caller s' h_step
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller := by
    rw [hs']; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller - withdrawShares assets s.exchangeRate := by
    rw [hs']; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller := by
    rw [hs']; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  unfold callerValue valueAt
  rw [hx, hy, hu]
  have hmono : redeemAssets (s.apyUSDBal caller - withdrawShares assets s.exchangeRate) s.exchangeRate
      ≤ redeemAssets (s.apyUSDBal caller) s.exchangeRate :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  omega

/-- `redeem` (vault, share-denominated): identical shape to `withdraw` above — the
redeemed assets land in a cooldown unlock request, not in `apxUSDBal`/`usdcBal`, so at the
fixed pre-step rate the caller's `callerValue` can only fall (`apyUSDBal` only shrinks by
the burned `shares`). -/
theorem caller_value_redeem_fixedRate (s : State) (shares : Nat) (receiver caller : Address)
    (s' : State) (h_step : step s (Op.redeem shares receiver) caller = some s') :
    valueAt s.exchangeRate s' caller ≤ callerValue s caller := by
  obtain ⟨-, -, -, hs'⟩ := inv_redeem s shares receiver caller s' h_step
  have hx : s'.apxUSDBal caller = s.apxUSDBal caller := by
    rw [hs']; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hy : s'.apyUSDBal caller = s.apyUSDBal caller - shares := by
    rw [hs']; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  have hu : s'.usdcBal caller = s.usdcBal caller := by
    rw [hs']; simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]
  unfold callerValue valueAt
  rw [hx, hy, hu]
  have hmono : redeemAssets (s.apyUSDBal caller - shares) s.exchangeRate
      ≤ redeemAssets (s.apyUSDBal caller) s.exchangeRate :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  omega

/-- **S6 `caller_net_nonpositive`** (docs/06-safety-properties.md, Tier B): the
value-weighted no-free-money law for the acting caller, across the four named
value-moving op families (`depositUSDC`, `lockApxUSD`, `redeemApxUSD`, `withdraw`,
`redeem` — five op instances). Priced at the rate in force when the step began, the
caller's `callerValue` never rises beyond what it paid into the step: flat for
`depositUSDC` (1:1 USDC/apxUSD, no rounding), flat-or-lower for `redeemApxUSD` (given the
standing `redemptionValue ≤ ray` invariant), and non-increasing for `lockApxUSD`/
`withdraw`/`redeem` (rounding-favors-protocol / monotone-burn arguments above).

**Scope, honestly**: this is the single-step fragment, not the trace-level sum. Composing
it across a trace would need to reconcile each step's fixed *reference* rate with the
*next* step's live rate — exactly the rate-drift arithmetic flagged above as out of scope,
and the reason the design memo calls the trace-level Nat telescoping "fiddly": summing
`valueAt R_i` terms across steps that each recompute `R_i` from a shifting `totalAssets`/
`totalSupply` ratio does not telescope cleanly in `Nat` without re-deriving a single-step
rate-movement bound first. Excluded operations: `mintApxUSD` (credits an address `to` that
may differ from `caller` — already the S1/S5 "arbitrage mint" case, a purchase paid by
`caller` for `to`, not a `caller`-value question), `requestUnlock`/`claimUnlock`/
`flexibleRequestUnlock`/`flexibleClaimUnlock` (move value into/out of the unlock-registry
column that `callerValue` does not track — covered instead by S1's `Penniless` argument),
and `executeRFQRedemption` (the caller is a privileged RFQ counterparty acting on behalf of
`user`, not an ordinary self-directed operation). -/
theorem caller_net_nonpositive (s : State) (op : Op) (caller : Address) (s' : State)
    (h_step : step s op caller = some s') (h_rv : s.redemptionValue ≤ ray)
    (h_case :
      (∃ amount, op = Op.depositUSDC amount) ∨
      (∃ amount, op = Op.lockApxUSD amount) ∨
      (∃ amount, op = Op.redeemApxUSD amount) ∨
      (∃ amount r, op = Op.withdraw amount r) ∨
      (∃ shares r, op = Op.redeem shares r)) :
    valueAt s.exchangeRate s' caller ≤ callerValue s caller := by
  rcases h_case with ⟨amount, rfl⟩ | ⟨amount, rfl⟩ | ⟨amount, rfl⟩ | ⟨amount, r, rfl⟩ | ⟨shares, r, rfl⟩
  · exact Nat.le_of_eq (caller_value_depositUSDC s amount caller s' h_step)
  · exact caller_value_lockApxUSD_fixedRate s amount caller s' h_step
  · exact caller_value_redeemApxUSD s amount caller s' h_step h_rv
  · exact caller_value_withdraw_fixedRate s amount r caller s' h_step
  · exact caller_value_redeem_fixedRate s shares r caller s' h_step

/-! ## S7 `vest_no_early_drain` — vested yield cannot be pulled forward ahead of schedule

`vestedAmount` is the two-accumulator read of the pool: the previously-realized
`fullyVestedAmount` plus whatever has newly streamed out of the current `vestTotal`/
`vestStart`/`vestPeriod` clock (`min (linear elapsed-based amount) vestTotal`). The
no-early-drain property is three arithmetic/definitional facts about it and about
`pullVestedYield`'s interaction with it — no `step`/`Op` case analysis, so no
deep-recursion risk. (Re-derived from scratch: the equivalents `vestedAmount_mono`/
`vestedAmount_le_total` in `Apyx.lean` are `private` to that file.) -/

/-- If `e ≤ P` then `e * T / P ≤ T`. (Re-derived local copy of `Apyx.lean`'s private
`div_mul_le_total`.) -/
private theorem div_mul_le_total (e P T : Nat) (h : e ≤ P) : e * T / P ≤ T := by
  rcases Nat.eq_zero_or_pos P with hp | hp
  · subst hp; simp [Nat.le_zero.mp h]
  · calc e * T / P ≤ P * T / P := Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
      _ = T := Nat.mul_div_cancel_left _ hp

/-- (b) `vestedAmount` never exceeds the previously-realized `fullyVestedAmount`
accumulator plus the total of the currently-streaming pool `vestTotal`: the vest
stream (in either accumulator) can never realize more value than was ever credited
to it. (Two-accumulator model: `vestedAmount s n ≤ s.vestTotal` alone is now FALSE —
`fullyVestedAmount` can be positive with `vestTotal = 0`, e.g. right after a
`pullVestedYield`-adjacent credit. This is the re-derived local copy of `Apyx.lean`'s
private `vestedAmount_le_total`, via the streaming-only bound
`newlyVestedAmount_le_vestTotal` below.) -/
private theorem newlyVestedAmount_le_vestTotal (s : State) (n : Nat) :
    newlyVestedAmount s n ≤ s.vestTotal := by
  unfold newlyVestedAmount
  dsimp only
  repeat' split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact div_mul_le_total _ _ _ (by omega)

theorem vestedAmount_le_total (s : State) (n : Nat) :
    vestedAmount s n ≤ s.fullyVestedAmount + s.vestTotal :=
  Nat.add_le_add_left (newlyVestedAmount_le_vestTotal s n) _

/-- `newlyVestedAmount` is monotone in time (re-derived local copy of `Apyx.lean`'s
private `newlyVestedAmount_mono`). -/
private theorem newlyVestedAmount_monotone (s : State) {n m : Nat} (h : n ≤ m) :
    newlyVestedAmount s n ≤ newlyVestedAmount s m := by
  unfold newlyVestedAmount
  dsimp only
  repeat' split
  all_goals first
    | omega
    | exact Nat.zero_le _
    | (exfalso; omega)
    | exact div_mul_le_total _ _ _ (by omega)
    | exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))

/-- (a) `vestedAmount` is monotone non-decreasing in the time argument: the realizable
share of the vest pool never shrinks as time passes, so it cannot be "pulled forward" and
then un-pulled — realization only ever catches up to the linear schedule, never ahead of
it (that half is (b)) and never behind where it already was (this half). Only the
streaming portion (`newlyVestedAmount`) depends on `now`; `fullyVestedAmount` is a fixed
state field, so monotonicity of the sum follows directly from monotonicity of the
streaming term. -/
theorem vestedAmount_monotone (s : State) {n m : Nat} (h : n ≤ m) :
    vestedAmount s n ≤ vestedAmount s m :=
  Nat.add_le_add_left (newlyVestedAmount_monotone s h) _

/-- (c) `pullVestedYield` moves *exactly* `vestedAmount s s.now` into custody
(`vaultApxUSDBal`) and no more — restated from the local frame lemma `pvS_vaultApxUSDBal`
for use as part of the S7 bundle. -/
theorem pullVestedYield_moves_exactly_vested (s : State) :
    (pullVestedYield s).vaultApxUSDBal = s.vaultApxUSDBal + vestedAmount s s.now :=
  pvS_vaultApxUSDBal s

/-- **S7 `vest_no_early_drain`** (docs/06-safety-properties.md, Tier B): the vest pool's
already-vested-but-unrealized yield cannot be pulled forward faster than its linear
schedule and cannot be over-realized. (a) `vestedAmount` is monotone non-decreasing in
time — realization only ever advances, never regresses, so there is no way to "double-dip"
by rewinding the clock. (b) `vestedAmount s n` never exceeds `s.fullyVestedAmount +
s.vestTotal` for any `n` — no sequence of calls at any times can ever realize more than
what was ever credited to the pool, across *either* accumulator of the two-accumulator
model (the previously-realized `fullyVestedAmount` plus whatever remains in the
currently-streaming `vestTotal`). (c) `pullVestedYield` — the sole channel by which
`withdraw`/`redeem` realize vested yield into spendable custody (`vaultApxUSDBal`) —
moves *exactly* `vestedAmount s s.now`, no more: a single call cannot over-drain the
currently-vested amount, and by (a)/(b) no sequence of calls (at whatever times) can
exceed `fullyVestedAmount + vestTotal` in aggregate either. -/
theorem vest_no_early_drain (s : State) :
    (∀ n m, n ≤ m → vestedAmount s n ≤ vestedAmount s m) ∧
    (∀ n, vestedAmount s n ≤ s.fullyVestedAmount + s.vestTotal) ∧
    (pullVestedYield s).vaultApxUSDBal = s.vaultApxUSDBal + vestedAmount s s.now :=
  ⟨fun _ _ h => vestedAmount_monotone s h, vestedAmount_le_total s,
   pullVestedYield_moves_exactly_vested s⟩

/-! ## Investigation — does `creditYield`'s `vestStart` reset forfeit already-accrued
yield? (design memo §4b) — **resolved: no, it does not.**

`Op.creditYield` (`yieldDistributor`-gated; see `step_creditYield_exact`, `BlastRadius.lean`)
resets `vestStart := s.now`, but the *model* — like the underlying `LinearVestV0` contract —
realizes the currently-streaming portion of the old clock into the `fullyVestedAmount`
accumulator FIRST (`fullyVestedAmount := s.fullyVestedAmount + newlyVestedAmount s s.now`),
*before* folding the remainder plus the fresh `amount` into the freshly-restarted
`vestTotal`/`vestStart` clock (`vestTotal := (s.vestTotal - newlyVestedAmount s s.now) +
amount`). This is the two-accumulator, "accrue-first" design.

**Earlier finding, now superseded.** An earlier revision of this model had `creditYield`
reset `vestStart` *without* first realizing the elapsed portion into any accumulator, so the
reset silently erased whatever had already linearly vested but not yet been pulled into
`vaultApxUSDBal` — a genuine forfeiture, captured at the time by a theorem of this name that
proved `vestedAmount s' s'.now = 0` and `totalAssets s' < totalAssets s` immediately after a
credit. Cross-checking `LinearVestV0.sol` showed the real contract does **not** have this
bug: it accrues the streamed portion into its own `fullyVestedAmount`-equivalent accumulator
before restarting the clock. The model was corrected to match (see `Apyx.lean`'s `State`,
`pullVestedYield`, `Op.creditYield`, `Op.setVestPeriod`, and
`req_credit_preserves_accrued_vest`), and the theorem below now proves the conservation the
contract actually guarantees: crediting new yield never forfeits — nor even moves — any
value that had already accrued. -/

/-- **`creditYield_preserves_accrued_vest`** (resolves the design-memo §4b forfeiture
question, now negatively): crediting new yield via `Op.creditYield` does **not** forfeit
value that has already streamed out of the vest but has not yet been pulled into vault
custody. Immediately after the credit — evaluated at the unchanged `now`, before any further
time passes — the total reportable `vestedAmount` is exactly unchanged: the newly credited
`amount` itself has correctly not yet started streaming (0% elapsed since the clock was just
re-anchored at `now`), but nothing that had already vested under the old clock is lost — it
was realized into `fullyVestedAmount` first. Since `vaultApxUSDBal` itself is untouched by
`creditYield` (`donation_free_no_creditYield` above) and `vestedAmount` is exactly preserved,
`totalAssets` (`vaultApxUSDBal + vestedAmount s s.now`) is preserved too: a `withdraw`/
`redeem`/exchange-rate read taken immediately after a `creditYield` quotes exactly the same
`totalAssets`, `exchangeRate`, and payout per apyUSD share as it would have without the
credit (the fresh `amount` joins the still-streaming pool for its own future vesting, on
top). Requires `0 < vestPeriod`: with a degenerate zero-length vesting period every stream
(old and new) is defined to be 100% vested instantaneously, which is a distinct, correctly
non-forfeiting degenerate case this theorem does not need to isolate. Mirrors `Apyx.lean`'s
`req_credit_preserves_accrued_vest`, re-derived here via the public `step_creditYield_exact`
(`BlastRadius.lean`) rather than unfolding `step` directly. -/
theorem creditYield_preserves_accrued_vest (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.creditYield amount) caller = some s')
    (hvp : 0 < s.vestPeriod) :
    vestedAmount s' s'.now = vestedAmount s s.now ∧
    totalAssets s' = totalAssets s := by
  obtain ⟨-, hs'⟩ := step_creditYield_exact s amount caller s' h_step
  have hvbal : s'.vaultApxUSDBal = s.vaultApxUSDBal := by rw [hs']
  have hva : vestedAmount s' s'.now = vestedAmount s s.now := by
    rw [hs']
    simp only [vestedAmount, newlyVestedAmount, Nat.sub_self, Nat.zero_mul, Nat.zero_div]
    repeat' split
    all_goals omega
  refine ⟨hva, ?_⟩
  unfold totalAssets
  rw [hvbal, hva]

/-- **`setVestPeriod_preserves_accrued_vest`** — the twin of
`creditYield_preserves_accrued_vest` for the *other* accrue-first code path.
`Op.setVestPeriod` (admin-gated; see `step_setVestPeriod_exact`, `BlastRadius.lean`)
reconfigures the vesting period and re-anchors the clock at `s.now`, but — exactly like
`creditYield` and like the real `LinearVestV0.setVestingPeriod` — it realizes the
currently-streaming portion into `fullyVestedAmount` FIRST, so reconfiguring the period
never forfeits nor even moves value that has already vested. Immediately after the call
(evaluated at the unchanged `now`) the total reportable `vestedAmount` is exactly
preserved, and since `setVestPeriod` leaves `vaultApxUSDBal` untouched, so is
`totalAssets`. Requires `0 < p`: a degenerate zero-length new period would define the
whole remaining pool as 100% vested instantaneously — a distinct, still non-forfeiting
degenerate case this equality does not isolate (the same side-condition
`creditYield_preserves_accrued_vest` places on the *old* period). This closes the design
gap noted in review: the accrue-first `setVestPeriod` path was asserted safe in prose
(`Apyx.lean`'s `Op.setVestPeriod` docstring) but, unlike its `creditYield` twin, had no
theorem proving the conservation the contract actually guarantees. Mirrors the structure
of `creditYield_preserves_accrued_vest`, re-derived via the public
`step_setVestPeriod_exact` (`BlastRadius.lean`) rather than unfolding `step` directly. -/
theorem setVestPeriod_preserves_accrued_vest (s : State) (p : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.setVestPeriod p) caller = some s')
    (hp : 0 < p) :
    vestedAmount s' s'.now = vestedAmount s s.now ∧
    totalAssets s' = totalAssets s := by
  obtain ⟨-, hs'⟩ := step_setVestPeriod_exact s p caller s' h_step
  have hvbal : s'.vaultApxUSDBal = s.vaultApxUSDBal := by rw [hs']
  have hva : vestedAmount s' s'.now = vestedAmount s s.now := by
    rw [hs']
    simp only [vestedAmount, newlyVestedAmount, Nat.sub_self, Nat.zero_mul, Nat.zero_div]
    repeat' split
    all_goals omega
  refine ⟨hva, ?_⟩
  unfold totalAssets
  rw [hvbal, hva]

end Apyx
