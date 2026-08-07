import D2fsSpecs.Arithmetic

/-!
# V2-VAULT: ERC-4626 decomposed into vault accounting safety

Proof Map v2 (life#59) V2-G: the big "ERC-4626 compliance" claim is not one
property — it is a family of vault *accounting* guarantees, each of which
deserves its own stable name and manifest row, plus the burn/pending
agreement that ties the vault exit to the unlock ledger. This module names
the conjuncts of the already-proved `req_erc4626_compliance` and adds the
missing member: **the face amount recorded in the pending registry is exactly
the asset amount whose shares were burned**.

None of this claims the deployed contract implements the ERC-4626 ABI, event
surface, or getters — that refinement stays at the implementation hand-off
(`MulDivFidelity.lean`, `model.md` §5). These are vault accounting safety
facts of the model.

Status (proof-map §11): all model-local.
-/

namespace Apyx

/-! ## Named preview/conversion sub-properties (projections of
`req_erc4626_compliance`) -/

/-- `previewDeposit` reports exactly the conversion the deposit performs — it
cannot overstate the shares a deposit mints. -/
theorem vault_previewDeposit_exact (s : State) :
    ∀ assets, previewDeposit s assets = convertToShares s assets :=
  (req_erc4626_compliance s).1

/-- `previewMint` charges the ceiling conversion — it cannot understate the
assets a mint requires. -/
theorem vault_previewMint_ceil (s : State) :
    ∀ shares, previewMint s shares =
      redeemAssetsCeil shares (computeExchangeRate s) :=
  (req_erc4626_compliance s).2.1

/-- `previewWithdraw` charges the ceiling conversion — it cannot understate
the shares a withdrawal burns. -/
theorem vault_previewWithdraw_ceil (s : State) :
    ∀ assets, previewWithdraw s assets =
      withdrawShares assets (computeExchangeRate s) :=
  (req_erc4626_compliance s).2.2.1

/-- `previewRedeem` reports the floor conversion — it cannot overstate the
assets a redemption pays. -/
theorem vault_previewRedeem_exact (s : State) :
    ∀ shares, previewRedeem s shares = convertToAssets s shares :=
  (req_erc4626_compliance s).2.2.2.1

/-- Asset round-trips never credit value to the user. -/
theorem vault_roundtrip_assets_le (s : State) :
    ∀ assets, convertToAssets s (convertToShares s assets) ≤ assets :=
  (req_erc4626_compliance s).2.2.2.2.1

/-- Share round-trips never credit value to the user. -/
theorem vault_roundtrip_shares_le (s : State) :
    ∀ shares, convertToShares s (convertToAssets s shares) ≤ shares :=
  (req_erc4626_compliance s).2.2.2.2.2.1

/-- Withdrawing rounds against the user relative to depositing: an
equal-sized withdrawal never burns fewer shares than the deposit minted. -/
theorem vault_withdraw_rounds_against_user (s : State) :
    ∀ assets, previewDeposit s assets ≤ previewWithdraw s assets :=
  (req_erc4626_compliance s).2.2.2.2.2.2.1

/-- While paused, every `max*` limit is zero — no vault operation is
accepted. -/
theorem vault_paused_max_zero (s : State) (h : s.globalPause = true) :
    ∀ a, maxDeposit s a = 0 ∧ maxMint s a = 0 ∧
      maxWithdraw s a = 0 ∧ maxRedeem s a = 0 :=
  (req_erc4626_compliance s).2.2.2.2.2.2.2.1 h

/-- While live, the `max*` limits are the owner's balance-derived
capacities. -/
theorem vault_live_max_balances (s : State) (h : s.globalPause = false) :
    ∀ a, maxDeposit s a = s.apxUSDBal a ∧
      maxMint s a = convertToShares s (s.apxUSDBal a) ∧
      maxWithdraw s a = convertToAssets s (s.apyUSDBal a) ∧
      maxRedeem s a = s.apyUSDBal a :=
  (req_erc4626_compliance s).2.2.2.2.2.2.2.2 h

/-! ## The burn/pending agreement -/

private theorem pv_nextUnlockId (s : State) :
    (pullVestedYield s).nextUnlockId = s.nextUnlockId := by
  unfold pullVestedYield
  dsimp only
  split <;> rfl

private theorem pv_now (s : State) : (pullVestedYield s).now = s.now := by
  unfold pullVestedYield
  dsimp only
  split <;> rfl

/-- The generic vault-exit post state records the exit's asset amount, owner,
and maturity in the pending registry at the freshly allocated id. -/
private theorem vaultWithdrawPost_records (p : State) (assets shares : Nat)
    (receiver caller : Address) (name : String) (evArgs : List Nat) :
    (emitEvent (updateExchangeRate (createStandardUnlock
      { burnApyUSD p caller shares with
          vaultApxUSDBal := (burnApyUSD p caller shares).vaultApxUSDBal - assets }
      receiver assets)) name evArgs).unlockRequests p.nextUnlockId
      = some (receiver, assets, p.now + cooldownPeriod) := by
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- **Burn matches pending, `withdraw` channel**: a successful withdrawal of
`assets` records exactly `assets` as the face amount of the new pending
position — the shares burned (`withdrawShares` at the pulled rate) purchase
precisely the recorded claim, with the standard cooldown maturity. -/
theorem withdraw_burn_matches_pending (s : State) (assets : Nat)
    (receiver caller : Address) (s' : State)
    (h : step s (Op.withdraw assets receiver) caller = some s') :
    s'.unlockRequests s.nextUnlockId =
      some (receiver, assets, s.now + cooldownPeriod) := by
  obtain ⟨-, -, -, hpost⟩ := withdrawStep_effect s assets receiver caller s' h
  rw [hpost]
  have h1 := vaultWithdrawPost_records (pullVestedYield s) assets
    (withdrawShares assets (computeExchangeRate (pullVestedYield s)))
    receiver caller "Withdraw"
    [caller, receiver, caller, assets,
      withdrawShares assets (computeExchangeRate (pullVestedYield s))]
  rw [pv_nextUnlockId, pv_now] at h1
  exact h1

/-- **Burn matches pending, `redeem` channel**: a successful redemption of
`shares` records exactly the floor-converted asset value of those shares —
`previewRedeem` at the pulled rate — as the face amount of the new pending
position. -/
theorem redeem_burn_matches_pending (s : State) (shares : Nat)
    (receiver caller : Address) (s' : State)
    (h : step s (Op.redeem shares receiver) caller = some s') :
    s'.unlockRequests s.nextUnlockId =
      some (receiver,
        redeemAssets shares (computeExchangeRate (pullVestedYield s)),
        s.now + cooldownPeriod) := by
  obtain ⟨-, -, -, hpost⟩ := redeemStep_effect s shares receiver caller s' h
  rw [hpost]
  have h1 := vaultWithdrawPost_records (pullVestedYield s)
    (redeemAssets shares (computeExchangeRate (pullVestedYield s))) shares
    receiver caller "Withdraw"
    [caller, receiver, caller,
      redeemAssets shares (computeExchangeRate (pullVestedYield s)), shares]
  rw [pv_nextUnlockId, pv_now] at h1
  exact h1

end Apyx
