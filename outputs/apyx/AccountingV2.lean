import D2fsSpecs.InitV2

/-!
# V2-ACC: unified custody/pending/reserve accounting

Proof Map v2 (life#59) V2-C asks for one accounting relation connecting the
circulating apxUSD supply, the pending unlock liabilities, vault custody, the
credited yield stream, and the USDC reserve — and, for the catastrophic
backstop, a conservation statement that does **not** ignore the floor-division
residual (`pro_rata_floor_underpays_witness` in `SpecDefects.lean` proves the
naive equality is false).

Two layers:

* **USDC side** — `backstopPayout`/`backstopResidual` and
  `backstop_reserve_conservation`: over any finite holder support whose
  balances are bounded by the supply, the pro-rata payouts sum to at most the
  reserve, and payouts plus the explicit residual equal the pre-state reserve
  exactly. `catastrophicBackstop_accounting` ties this to the actual
  transition (post-reserve is zero, per-address credits are the modeled
  payouts). The residual is the v2-mandated explicit `RoundingResidual`
  boundary: it is *not* claimed to reach any holder.

* **apxUSD side** — `apxUSDObligations`: vault custody + circulating supply +
  pending unlock face amounts + the credited-but-unpulled yield stream
  (`vestTotal` + `fullyVestedAmount`). The per-operation theorems prove the
  exact conservation ladder of v2 §4:
  requests/claims/lock/vault exits are neutral, the flexible claim sheds
  exactly its fee, `creditYield` adds exactly the credited amount, and the
  vest pull is internal motion (`apxUSDObligations_pullVestedYield`). This is
  the measure under which the vault-exit channel — excluded from
  `SolventOutstanding` because custody was unmeasured — becomes conservation
  rather than exclusion; V2-INV builds the phase-scoped invariant on it.

Status (proof-map §11): all theorems here are model-local exact-delta or
bound facts; none is presented as a reachability theorem. The USDC theorems
take the finite holder support as an explicit parameter, consistent with v2
decision V2-A option 2 (no USDC supply field is added to `State`).
-/

namespace Apyx

/-! ## USDC side: the backstop pays out at most the reserve, with an explicit residual -/

/-- The modeled per-address backstop credit: `reserve * balance / supply`,
floor-divided, exactly as the `catastrophicBackstop` branch writes it. -/
def backstopPayout (s : State) (a : Address) : Nat :=
  s.usdcReserve * s.apxUSDBal a / s.totalSupply_apxUSD

/-- What the floor division leaves behind: the part of the reserve that the
pro-rata distribution does **not** deliver to the given holder support. The
model zeroes the reserve, so this amount is destroyed rather than paid; naming
it is the v2 "explicit rounding residual" rule. -/
def backstopResidual (s : State) (holders : List Address) : Nat :=
  s.usdcReserve - sumOver (backstopPayout s) holders

/-- Sum of floor-divided shares is bounded by the floor-divided sum. -/
private theorem sumOver_div_le (R S : Nat) (f : Address → Nat) :
    (l : List Address) → sumOver (fun a => R * f a / S) l ≤ R * sumOver f l / S
  | [] => by simp
  | a :: rest => by
    have ih := sumOver_div_le R S f rest
    calc R * f a / S + sumOver (fun a => R * f a / S) rest
        ≤ R * f a / S + R * sumOver f rest / S := Nat.add_le_add_left ih _
      _ ≤ (R * f a + R * sumOver f rest) / S := div_add_div_le _ _ _
      _ = R * (f a + sumOver f rest) / S := by rw [Nat.mul_add]

/-- **The pro-rata payouts never exceed the reserve.** Any holder support whose
balances sum to at most the supply receives, in total, at most the pre-state
reserve. The zero-supply corner pays everyone zero (Nat division), so the
bound holds there too — the explicit policy v1 §5.4 asked for. -/
theorem backstopPayout_sum_le_reserve (s : State) (holders : List Address)
    (hsum : sumOver s.apxUSDBal holders ≤ s.totalSupply_apxUSD) :
    sumOver (backstopPayout s) holders ≤ s.usdcReserve := by
  by_cases hS : s.totalSupply_apxUSD = 0
  · have hz : ∀ l : List Address, sumOver (backstopPayout s) l = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons a rest ih => simp [backstopPayout, hS, ih]
    rw [hz holders]
    exact Nat.zero_le _
  · have h1 : sumOver (backstopPayout s) holders
        ≤ s.usdcReserve * sumOver s.apxUSDBal holders / s.totalSupply_apxUSD :=
      sumOver_div_le s.usdcReserve s.totalSupply_apxUSD s.apxUSDBal holders
    calc sumOver (backstopPayout s) holders
        ≤ s.usdcReserve * sumOver s.apxUSDBal holders / s.totalSupply_apxUSD := h1
      _ ≤ s.usdcReserve * s.totalSupply_apxUSD / s.totalSupply_apxUSD :=
          Nat.div_le_div_right (Nat.mul_le_mul_left _ hsum)
      _ = s.usdcReserve := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hS)

/-- **Backstop conservation with the residual explicit**: payouts plus the
named residual equal the pre-state reserve exactly. This is the honest form —
`pro_rata_floor_underpays_witness` proves the residual can be positive, so an
equation without it would be false. -/
theorem backstop_reserve_conservation (s : State) (holders : List Address)
    (hsum : sumOver s.apxUSDBal holders ≤ s.totalSupply_apxUSD) :
    sumOver (backstopPayout s) holders + backstopResidual s holders =
      s.usdcReserve :=
  Nat.add_sub_cancel' (backstopPayout_sum_le_reserve s holders hsum)

/-- The conservation statement tied to the actual transition: a successful
backstop zeroes the reserve, credits every address its modeled payout, and the
payouts over any supply-bounded holder support plus the explicit residual
equal the pre-state reserve. -/
theorem catastrophicBackstop_accounting (s s' : State) (holders : List Address)
    (hsum : sumOver s.apxUSDBal holders ≤ s.totalSupply_apxUSD)
    (h_step : step s Op.catastrophicBackstop s.admin = some s') :
    s'.usdcReserve = 0 ∧
    (∀ a, s'.usdcBal a = s.usdcBal a + backstopPayout s a) ∧
    sumOver (backstopPayout s) holders + backstopResidual s holders =
      s.usdcReserve := by
  obtain ⟨-, -, hbal, hres, -⟩ := req_catastrophic_backstop s s' h_step
  exact ⟨hres, fun a => hbal a, backstop_reserve_conservation s holders hsum⟩

/-- The finite-ledger form: when the pre-state satisfies the finite apxUSD
ledger identity, a supply-complete holder support exists, and the conservation
equation holds over it. -/
theorem catastrophicBackstop_accounting_ledger (s s' : State)
    (hled : ApxUSDLedgerConsistent s)
    (h_step : step s Op.catastrophicBackstop s.admin = some s') :
    ∃ holders : List Address,
      holders.Pairwise (· ≠ ·) ∧
      (∀ a, s.apxUSDBal a ≠ 0 → a ∈ holders) ∧
      s'.usdcReserve = 0 ∧
      sumOver (backstopPayout s) holders + backstopResidual s holders =
        s.usdcReserve := by
  obtain ⟨holders, hnodup, hsupport, hsum⟩ := hled
  obtain ⟨hres, -, hcons⟩ := catastrophicBackstop_accounting s s' holders
    (Nat.le_of_eq hsum) h_step
  exact ⟨holders, hnodup, hsupport, hres, hcons⟩

/-! ## apxUSD side: the unified obligation measure -/

/-- The total modeled apxUSD obligation: vault custody plus circulating supply
plus pending unlock face amounts (`apxUSDFlow`), plus the credited yield that
has not yet been pulled into custody (`vestTotal` still streaming,
`fullyVestedAmount` streamed but unpulled). Under this measure the vest pull
and the vault exits are internal motion, not exclusions. -/
def apxUSDObligations (s : State) : Nat :=
  apxUSDFlow s + s.vestTotal + s.fullyVestedAmount

/-- The streaming release never exceeds the streaming total. Local restatement
of the private `newlyVestedAmount_le_total` in `Apyx.lean`. -/
private theorem nv_le_total (s : State) (n : Nat) :
    newlyVestedAmount s n ≤ s.vestTotal := by
  unfold newlyVestedAmount
  dsimp only
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.le_refl _
    · rename_i hnge
      have hp : 0 < s.vestPeriod := by omega
      calc (n - s.vestStart) * s.vestTotal / s.vestPeriod
          ≤ s.vestPeriod * s.vestTotal / s.vestPeriod :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
        _ = s.vestTotal := Nat.mul_div_cancel_left _ hp

/-- **The vest pull is internal motion.** It moves value from the vest buckets
into custody; the unified obligation is unchanged. -/
theorem apxUSDObligations_pullVestedYield (s : State) :
    apxUSDObligations (pullVestedYield s) = apxUSDObligations s := by
  have hnv : newlyVestedAmount s s.now ≤ s.vestTotal := nv_le_total s s.now
  unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
    standardUnlockTotal flexibleUnlockTotal pullVestedYield
  dsimp only
  split
  · rfl
  · dsimp only
    omega

/-- `tick` only moves the clock; every obligation bucket is framed. -/
theorem apxUSDObligations_tick (s : State) (dt : Nat) (caller : Address)
    (s' : State) (h_step : step s (Op.tick dt) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  simp only [step] at h_step
  cases Option.some.inj h_step
  rfl

/-- **Locking is neutral**: the burned circulating apxUSD reappears as vault
custody, one-for-one. -/
theorem apxUSDObligations_lockApxUSD (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hsupply : amount ≤ s.totalSupply_apxUSD)
    (h_step : step s (Op.lockApxUSD amount) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  simp only [step] at h_step
  (repeat' split at h_step) <;>
    first
      | (cases Option.some.inj h_step
         unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
           standardUnlockTotal flexibleUnlockTotal
         simp only [emitEvent, updateExchangeRate, mintApyUSD, burnApxUSD]
         omega)
      | exact absurd h_step (by simp)

private theorem requestUnlockStep_vestTotal (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).vestTotal = s.vestTotal := by
  unfold requestUnlockStep updateStandardUnlock createStandardUnlock
  (repeat' split) <;> rfl

private theorem requestUnlockStep_fullyVestedAmount (s : State) (caller amount : Nat) :
    (requestUnlockStep s caller amount).fullyVestedAmount = s.fullyVestedAmount := by
  unfold requestUnlockStep updateStandardUnlock createStandardUnlock
  (repeat' split) <;> rfl

/-- **A standard request is neutral**: the burn and the new pending liability
cancel inside `outstandingApxUSD`; custody and the vest buckets are framed. -/
theorem apxUSDObligations_requestUnlock (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hreg : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD)
    (h_step : step s (Op.requestUnlock amount) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  have hout := outstandingApxUSD_requestUnlock s amount caller s' hreg hsupply h_step
  obtain ⟨-, -, hpost⟩ := requestUnlockStep_effect s amount caller s' h_step
  have hv : s'.vaultApxUSDBal = s.vaultApxUSDBal := by
    rw [hpost]; simp
  have hvt : s'.vestTotal = s.vestTotal := by
    rw [hpost]; exact requestUnlockStep_vestTotal s caller amount
  have hfv : s'.fullyVestedAmount = s.fullyVestedAmount := by
    rw [hpost]; exact requestUnlockStep_fullyVestedAmount s caller amount
  unfold apxUSDObligations apxUSDFlow
  rw [hout, hv, hvt, hfv]

/-- **A flexible request is neutral**, same cancellation. -/
theorem apxUSDObligations_flexibleRequestUnlock (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hreg : RegistryWellIndexed s)
    (hsupply : amount ≤ s.totalSupply_apxUSD)
    (h_step : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  have hout := outstandingApxUSD_flexibleRequestUnlock_step s amount caller s'
    hreg hsupply h_step
  obtain ⟨-, -, hpost⟩ := flexibleRequestUnlockStep_effect s amount caller s' h_step
  have hv : s'.vaultApxUSDBal = s.vaultApxUSDBal := by rw [hpost]; rfl
  have hvt : s'.vestTotal = s.vestTotal := by rw [hpost]; rfl
  have hfv : s'.fullyVestedAmount = s.fullyVestedAmount := by rw [hpost]; rfl
  unfold apxUSDObligations apxUSDFlow
  rw [hout, hv, hvt, hfv]

/-- **A standard claim is neutral**: the retired pending liability re-mints as
circulating supply, one-for-one. -/
theorem apxUSDObligations_claimUnlock (s : State) (id : Nat)
    (caller : Address) (s' : State)
    (hreg : RegistryWellIndexed s)
    (h_step : step s (Op.claimUnlock id) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  obtain ⟨owner, amount, cooldownEnd, hreq, -, -, -, hpost⟩ :=
    claimUnlockStep_effect s id caller s' h_step
  have hid : id < s.nextUnlockId := by
    cases Nat.lt_or_ge id s.nextUnlockId with
    | inl h => exact h
    | inr hge => rw [hreg.1.1 id hge] at hreq; simp at hreq
  have hout := outstandingApxUSD_claimUnlock s id owner amount cooldownEnd
    caller s' hid hreq h_step
  have hv : s'.vaultApxUSDBal = s.vaultApxUSDBal := by rw [hpost]; rfl
  have hvt : s'.vestTotal = s.vestTotal := by rw [hpost]; rfl
  have hfv : s'.fullyVestedAmount = s.fullyVestedAmount := by rw [hpost]; rfl
  unfold apxUSDObligations apxUSDFlow
  rw [hout, hv, hvt, hfv]

/-- **A flexible claim sheds exactly its fee**: the obligation falls by the
published early-exit charge and nothing else. -/
theorem apxUSDObligations_flexibleClaimUnlock (s : State) (id : Nat)
    (caller : Address) (s' : State)
    (hreg : RegistryWellIndexed s)
    (h_step : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
      apxUSDObligations s' + amount * flexibleUnlockFee requestTime s.now / 10000 =
        apxUSDObligations s := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, -, -, -, hpost⟩ :=
    flexibleClaimStep_effect s id caller s' h_step
  have hid : id < s.nextUnlockId := by
    cases Nat.lt_or_ge id s.nextUnlockId with
    | inl h => exact h
    | inr hge => rw [hreg.1.2 id hge] at hreq; simp at hreq
  have hout := outstandingApxUSD_flexibleClaimUnlock s id owner amount
    requestTime cooldownEnd caller s' hid hreq h_step
  have hv : s'.vaultApxUSDBal = s.vaultApxUSDBal := by rw [hpost]; rfl
  have hvt : s'.vestTotal = s.vestTotal := by rw [hpost]; rfl
  have hfv : s'.fullyVestedAmount = s.fullyVestedAmount := by rw [hpost]; rfl
  refine ⟨owner, amount, requestTime, cooldownEnd, hreq, ?_⟩
  unfold apxUSDObligations apxUSDFlow
  rw [hv, hvt, hfv]
  omega

/-- Vest-bucket frames of the generic vault-exit post state, mirroring the
`apxUSDFlow_vaultWithdrawPost` boundary. -/
private theorem vaultWithdrawPost_vestTotal (p : State) (assets shares : Nat)
    (receiver caller : Address) (name : String) (evArgs : List Nat) :
    (emitEvent (updateExchangeRate (createStandardUnlock
      { burnApyUSD p caller shares with
          vaultApxUSDBal := (burnApyUSD p caller shares).vaultApxUSDBal - assets }
      receiver assets)) name evArgs).vestTotal = p.vestTotal := by
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

private theorem vaultWithdrawPost_fullyVestedAmount (p : State) (assets shares : Nat)
    (receiver caller : Address) (name : String) (evArgs : List Nat) :
    (emitEvent (updateExchangeRate (createStandardUnlock
      { burnApyUSD p caller shares with
          vaultApxUSDBal := (burnApyUSD p caller shares).vaultApxUSDBal - assets }
      receiver assets)) name evArgs).fullyVestedAmount = p.fullyVestedAmount := by
  simp [emitEvent, updateExchangeRate, createStandardUnlock, burnApyUSD]

/-- **A vault exit (`withdraw`) is neutral**: after the mandatory vest pull —
itself internal motion — custody falls and the new pending liability rises by
the same amount. This is the conservation form of the vault-exit channel that
`SolventOutstanding` had to exclude. -/
theorem apxUSDObligations_withdraw (s : State) (assets : Nat)
    (receiver caller : Address) (s' : State)
    (hreg : RegistryWellIndexed s)
    (h_step : step s (Op.withdraw assets receiver) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  have hflow := apxUSDFlow_withdraw s assets receiver caller s' hreg h_step
  obtain ⟨-, -, -, hpost⟩ := withdrawStep_effect s assets receiver caller s' h_step
  have hvt : s'.vestTotal = (pullVestedYield s).vestTotal := by
    rw [hpost]
    exact vaultWithdrawPost_vestTotal (pullVestedYield s) assets _ receiver caller _ _
  have hfv : s'.fullyVestedAmount = (pullVestedYield s).fullyVestedAmount := by
    rw [hpost]
    exact vaultWithdrawPost_fullyVestedAmount (pullVestedYield s) assets _ receiver caller _ _
  have hpull := apxUSDObligations_pullVestedYield s
  unfold apxUSDObligations at hpull ⊢
  rw [hflow, hvt, hfv]
  exact hpull

/-- **A vault exit (`redeem`) is neutral**, same boundary. -/
theorem apxUSDObligations_redeem (s : State) (shares : Nat)
    (receiver caller : Address) (s' : State)
    (hreg : RegistryWellIndexed s)
    (h_step : step s (Op.redeem shares receiver) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s := by
  have hflow := apxUSDFlow_redeem s shares receiver caller s' hreg h_step
  obtain ⟨-, -, -, hpost⟩ := redeemStep_effect s shares receiver caller s' h_step
  have hvt : s'.vestTotal = (pullVestedYield s).vestTotal := by
    rw [hpost]
    exact vaultWithdrawPost_vestTotal (pullVestedYield s) _ shares receiver caller _ _
  have hfv : s'.fullyVestedAmount = (pullVestedYield s).fullyVestedAmount := by
    rw [hpost]
    exact vaultWithdrawPost_fullyVestedAmount (pullVestedYield s) _ shares receiver caller _ _
  have hpull := apxUSDObligations_pullVestedYield s
  unfold apxUSDObligations at hpull ⊢
  rw [hflow, hvt, hfv]
  exact hpull

/-- **Crediting yield adds exactly the credited amount** — the modeled inflow
of new obligation, explicitly quantified rather than silently excluded. The
accrue-first bookkeeping (realize the streamed portion, then restart the
clock) cancels inside the measure. -/
theorem apxUSDObligations_creditYield (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (h_step : step s (Op.creditYield amount) caller = some s') :
    apxUSDObligations s' = apxUSDObligations s + amount := by
  have hnv : newlyVestedAmount s s.now ≤ s.vestTotal := nv_le_total s s.now
  simp only [step] at h_step
  split at h_step
  · cases Option.some.inj h_step
    unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
      standardUnlockTotal flexibleUnlockTotal
    dsimp only
    omega
  · exact absurd h_step (by simp)

end Apyx
