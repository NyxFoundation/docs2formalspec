import D2fsSpecs.Apyx

/-!
# Blast-radius theorems (Tier 1): damage bounds under compromised privileged roles

Companion module to `D2fsSpecs.Apyx` implementing Tier 1 (T1-T4) of
`docs/05-blast-radius.md`: instead of asking "does the system behave correctly for a
well-behaved caller?", these theorems ask "if a privileged role's key is fully controlled
by an attacker, how much user-asset damage can that attacker do?".

All theorems are proved against the unchanged `State`/`Op`/`step` model by exhaustive
case analysis over the closed `Op` inductive — the same pattern as the requirement
theorems in `Apyx.lean`. Helper extraction lemmas that are `private` in `Apyx.lean` are
re-derived locally here rather than exposed there.

Declarations live in the nested namespace `Apyx.Tier1`: the sibling module
`D2fsSpecs.BlastRadius` develops some of the same memo properties (plus trace-level
forms) directly in the `Apyx` namespace, and the nesting keeps the two independent
developments importable side by side without name collisions.
-/

namespace Apyx
namespace Tier1

/- ================= local helper lemmas =================
These re-derive (verbatim) helpers that exist in `D2fsSpecs.Apyx` but are `private`
there and hence not visible in this module. -/

@[simp] private theorem pullVestedYield_exchangeRate (s : State) :
    (pullVestedYield s).exchangeRate = s.exchangeRate := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_apxUSDBal (s : State) :
    (pullVestedYield s).apxUSDBal = s.apxUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_apyUSDBal (s : State) :
    (pullVestedYield s).apyUSDBal = s.apyUSDBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

@[simp] private theorem pullVestedYield_usdcBal (s : State) :
    (pullVestedYield s).usdcBal = s.usdcBal := by
  unfold pullVestedYield; dsimp only; split <;> rfl

private theorem step_depositUSDC_some (s : State) (amount : Nat) (caller : Address) (s' : State)
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

private theorem step_mintApxUSD_some (s : State) (to : Address) (amount : Nat) (caller : Address) (s' : State)
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

private theorem step_lockApxUSD_some (s : State) (amount : Nat) (caller : Address) (s' : State)
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

private theorem step_requestUnlock_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.requestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = createStandardUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_flexibleRequestUnlock_some (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = createFlexibleUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

private theorem step_claimUnlock_some (s : State) (id : Nat) (caller : Address) (s' : State)
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

private theorem step_flexibleClaimUnlock_some (s : State) (id : Nat) (caller : Address) (s' : State)
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

private theorem step_redeemApxUSD_some (s : State) (amount : Nat) (caller : Address) (s' : State)
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

private theorem step_withdraw_some (s : State) (assets : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s.globalPause = false ∧
    withdrawShares assets s.exchangeRate ≤ (pullVestedYield s).apyUSDBal caller ∧
    assets ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate) with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller (withdrawShares assets s.exchangeRate)).vaultApxUSDBal - assets }
          receiver assets)) "Withdraw" [caller, receiver, caller, assets, withdrawShares assets s.exchangeRate] := by
  simp only [step, pullVestedYield_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem step_redeem_some (s : State) (shares : Nat) (receiver caller : Address) (s' : State)
    (h : step s (Op.redeem shares receiver) caller = some s') :
    s.globalPause = false ∧
    shares ≤ (pullVestedYield s).apyUSDBal caller ∧
    redeemAssets shares s.exchangeRate ≤ (pullVestedYield s).vaultApxUSDBal ∧
    s' = emitEvent (updateExchangeRate (createStandardUnlock
          { burnApyUSD (pullVestedYield s) caller shares with
            vaultApxUSDBal := (burnApyUSD (pullVestedYield s) caller shares).vaultApxUSDBal - redeemAssets shares s.exchangeRate }
          receiver (redeemAssets shares s.exchangeRate))) "Withdraw" [caller, receiver, caller, redeemAssets shares s.exchangeRate, shares] := by
  simp only [step, pullVestedYield_exchangeRate] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, by omega, (Option.some.inj h).symm⟩

private theorem step_executeRFQRedemption_some (s : State) (user : Address) (amount : Nat) (caller : Address) (s' : State)
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

/- ================= T1: pauser cannot extract ================= -/

/-- Frame lemma for `Op.pause`: a successful pause proves the caller held the
`pauseController` role and the *entire* post-state is the pre-state with only
`globalPause` set — no other field of `State` (in particular no balance, supply,
or reserve) is touched. -/
theorem step_pause_frame (s : State) (caller : Address) (s' : State)
    (h : step s Op.pause caller = some s') :
    caller = s.pauseController ∧ s' = { s with globalPause := true } := by
  simp only [step] at h
  split at h
  · exact ⟨by simp_all, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- Frame lemma for `Op.unpause`: exact mirror of `step_pause_frame`. -/
theorem step_unpause_frame (s : State) (caller : Address) (s' : State)
    (h : step s Op.unpause caller = some s') :
    caller = s.pauseController ∧ s' = { s with globalPause := false } := by
  simp only [step] at h
  split at h
  · exact ⟨by simp_all, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- T1 `pauser_cannot_extract` (docs/05-blast-radius.md, Tier 1).

Threat model: the `pauseController` key is fully compromised. The attacker can then
succeed at `Op.pause`/`Op.unpause` (the only operations gated on that role).

Claim: those two operations move no value whatsoever — every balance and supply field
(`apxUSDBal`, `apyUSDBal`, both total supplies, the vault's apxUSD holdings, the USDC
reserve, and every external USDC balance) is bitwise unchanged. Together with the frame
lemmas `step_pause_frame`/`step_unpause_frame` (which show the whole post-state equals
the pre-state except `globalPause`), the blast radius of a compromised pauser is exactly
a liveness attack (freezing/unfreezing), never asset extraction.

Scope note: this theorem bounds what the *pause/unpause operations* can do. A pauser
address that additionally holds user funds or another role can of course use the
ordinary user pathways for its own funds, like any address; those pathways are covered
by T4 (`no_role_transfers_user_funds`). -/
theorem pauser_cannot_extract (s : State) (op : Op) (caller : Address) (s' : State)
    (h_op : op = Op.pause ∨ op = Op.unpause)
    (h_step : step s op caller = some s') :
    caller = s.pauseController ∧
    s'.apxUSDBal = s.apxUSDBal ∧
    s'.apyUSDBal = s.apyUSDBal ∧
    s'.totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    s'.vaultApxUSDBal = s.vaultApxUSDBal ∧
    s'.usdcReserve = s.usdcReserve ∧
    s'.usdcBal = s.usdcBal := by
  rcases h_op with rfl | rfl
  · obtain ⟨hc, hs'⟩ := step_pause_frame s caller s' h_step
    subst hs'
    exact ⟨hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hc, hs'⟩ := step_unpause_frame s caller s' h_step
    subst hs'
    exact ⟨hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- ================= T2: yield distributor cannot extract ================= -/

/-- T2 `yield_distributor_cannot_extract` (docs/05-blast-radius.md, Tier 1).

Threat model: the `yieldDistributor` key is fully compromised. `Op.creditYield` is the
only operation gated on that role.

Claim: `creditYield` can only *donate*, never extract. A successful `creditYield` leaves
every user-facing holding untouched — all apxUSD balances, all apyUSD balances, all
external USDC balances, both total supplies, and the vault's apxUSD holdings — and its
only effect on value-bearing fields is to *increase* the USDC reserve and the vest pool
by exactly the credited amount (plus resetting the vest clock `vestStart`). So a
compromised yield distributor can at worst waste its own funds and distort the vesting
schedule's timing; it cannot decrease any user's holdings.

Scope note: resetting `vestStart` re-anchors the linear vesting of the (enlarged) vest
pool; that is a timing distortion of not-yet-vested yield, not a debit of any recorded
balance. -/
theorem yield_distributor_cannot_extract (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s') :
    caller = s.yieldDistributor ∧
    s'.apxUSDBal = s.apxUSDBal ∧
    s'.apyUSDBal = s.apyUSDBal ∧
    s'.usdcBal = s.usdcBal ∧
    s'.totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    s'.vaultApxUSDBal = s.vaultApxUSDBal ∧
    s'.usdcReserve = s.usdcReserve + amount ∧
    s'.vestTotal = s.vestTotal + amount := by
  simp only [step] at h_step
  split at h_step
  · cases Option.some.inj h_step
    exact ⟨by simp_all, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd h_step (by simp)

/- ================= T3: admin cannot touch balances ================= -/

/-- T3 `admin_cannot_touch_balances` (docs/05-blast-radius.md, Tier 1).

Threat model: the `admin` key is fully compromised. The operations gated on
`caller = s.admin` in `step` are exactly: `addToWhitelist`, `removeFromWhitelist`,
`addToDenylist`, `removeFromDenylist`, `setYieldRate`, `setVestPeriod`,
`handleStressEvent`, and `catastrophicBackstop` — all eight are covered here.

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
    (h_admin :
      (∃ a, op = Op.addToWhitelist a) ∨ (∃ a, op = Op.removeFromWhitelist a) ∨
      (∃ a, op = Op.addToDenylist a) ∨ (∃ a, op = Op.removeFromDenylist a) ∨
      (∃ bps, op = Op.setYieldRate bps) ∨ (∃ p, op = Op.setVestPeriod p) ∨
      (∃ x, op = Op.handleStressEvent x) ∨ op = Op.catastrophicBackstop)
    (h_step : step s op caller = some s') :
    s'.apxUSDBal = s.apxUSDBal ∧
    s'.apyUSDBal = s.apyUSDBal ∧
    s'.usdcBal = s.usdcBal ∧
    s'.totalSupply_apxUSD = s.totalSupply_apxUSD ∧
    s'.totalSupply_apyUSD = s.totalSupply_apyUSD ∧
    s'.vaultApxUSDBal = s.vaultApxUSDBal ∧
    s'.usdcReserve = s.usdcReserve := by
  rcases h_admin with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨bps, rfl⟩ | ⟨p, rfl⟩ |
    ⟨x, rfl⟩ | rfl
  all_goals
    simp only [step] at h_step
    split at h_step <;>
      first
        | (cases Option.some.inj h_step; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | exact absurd h_step (by simp)

/- ================= T4: non-custodial invariant ================= -/

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
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, mintApxUSD] at h_dec
    split at h_dec <;> omega
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, mintApxUSD] at h_dec
    split at h_dec <;> omega
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD, hac] at h_dec
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [createStandardUnlock, burnApxUSD, hac] at h_dec
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, burnUnlockNFT] at h_dec
    split at h_dec <;> omega
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [emitEvent, burnApxUSD, hac] at h_dec
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact Or.inl hac
    · exfalso
      simp [createFlexibleUnlock, burnApxUSD, hac] at h_dec
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, burnUnlockNFT] at h_dec
    split at h_dec <;> omega
  case executeRFQRedemption user amount =>
    obtain ⟨_, hrfq, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
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
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] at h_dec
    split at h_dec <;> omega
  · -- withdraw burns shares from the caller only
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD, hac] at h_dec
  · -- redeem burns shares from the caller only
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
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
    obtain ⟨_, _, _, _, hs'⟩ := step_depositUSDC_some _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, mintApxUSD, hac] at h_dec
  case mintApxUSD to amount =>
    obtain ⟨_, _, _, _, _, _, hs'⟩ := step_mintApxUSD_some _ _ _ _ _ h_step
    subst hs'
    by_cases hac : a = caller
    · exact hac
    · exfalso
      simp [emitEvent, mintApxUSD, hac] at h_dec
  case lockApxUSD amount =>
    obtain ⟨_, _, hs'⟩ := step_lockApxUSD_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD] at h_dec
  case requestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_requestUnlock_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [createStandardUnlock, burnApxUSD] at h_dec
  case claimUnlock id =>
    obtain ⟨o, am, ce, _, _, _, _, hs'⟩ := step_claimUnlock_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, burnUnlockNFT] at h_dec
  case redeemApxUSD amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_redeemApxUSD_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, burnApxUSD] at h_dec
    split at h_dec <;>
      first
        | exact absurd h_dec (Nat.not_lt.mpr (Nat.le_add_right _ _))
        | exact absurd h_dec (Nat.lt_irrefl _)
  case withdraw assets receiver =>
    obtain ⟨_, _, _, hs'⟩ := step_withdraw_some _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case redeem shares receiver =>
    obtain ⟨_, _, _, hs'⟩ := step_redeem_some _ _ _ _ _ h_step
    subst hs'
    exfalso
    simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD] at h_dec
  case flexibleRequestUnlock amount =>
    obtain ⟨_, _, hs'⟩ := step_flexibleRequestUnlock_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [createFlexibleUnlock, burnApxUSD] at h_dec
  case flexibleClaimUnlock id =>
    obtain ⟨o, am, rt, ce, _, _, _, _, hs'⟩ := step_flexibleClaimUnlock_some _ _ _ _ h_step
    subst hs'
    exfalso
    simp [mintApxUSD, burnUnlockNFT] at h_dec
  case executeRFQRedemption user amount =>
    obtain ⟨_, _, _, _, hs'⟩ := step_executeRFQRedemption_some _ _ _ _ _ h_step
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

end Tier1
end Apyx
