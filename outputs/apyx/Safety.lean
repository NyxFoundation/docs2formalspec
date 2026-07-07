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
    refine ⟨?_, by simp [createStandardUnlock, burnApxUSD, hu], ?_,
      by simpa [createStandardUnlock, burnApxUSD] using hflex⟩
    · by_cases hac : a = caller
      · subst hac
        have h0 : amount = 0 := by omega
        simp [createStandardUnlock, burnApxUSD, h0, hx]
      · simp [createStandardUnlock, burnApxUSD, hac, hx]
    · intro id amt ce hreq
      simp only [createStandardUnlock, burnApxUSD] at hreq
      split at hreq
      · obtain ⟨hca, hamt, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj hreq
        subst hca
        omega
      · exact hstd id amt ce hreq
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
    obtain ⟨-, -, hle, -, hs'⟩ := inv_redeemApxUSD _ _ _ _ h_step
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
theorem no_free_value_trace (s : State) (σ : List (Op × Address)) (a : Address)
    (h0 : Penniless a s)
    (h_no_gift : ∀ p ∈ σ, (∀ n, p.1 ≠ Op.mintApxUSD a n) ∧
      (∀ n, p.1 ≠ Op.withdraw n a) ∧ (∀ n, p.1 ≠ Op.redeem n a)) :
    (execTrace s σ).apxUSDBal a = 0 :=
  (penniless_invariant s σ a h0 h_no_gift).1

end Apyx
