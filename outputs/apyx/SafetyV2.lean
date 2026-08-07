import D2fsSpecs.PhaseV2

/-!
# V2-ARITH / V2-TRANS / V2-VALUE: arithmetic safety and claim coverage

Proof Map v2 (life#59) P1 layers on top of the P0 invariants:

* **V2-ARITH** — `ArithmeticSafe` packages, per operation, the no-underflow
  facts an *accepted* step guarantees: every `Nat` subtraction the transition
  performs is preceded by the guard that makes it exact.
  `accepted_arithmetic_safe` proves the package for every operation from the
  public effect boundaries. It is a property of the transition (`s`, `op`,
  `caller`), not of one state — v2 explicitly moved it out of `Init`.
  Denominators: `ray` and the vault's `+1`-virtualized share divisor are
  positive (`ray_pos`, `computeExchangeRate`); the backstop's division by a
  zero supply pays zero by Nat semantics — the explicit policy proved in
  `backstopPayout_sum_le_reserve`; `handleStressEvent`'s collateral
  subtraction is deliberately clamped Nat subtraction, stated exactly in
  `StressContract`.

* **V2-TRANS** — `lockApxUSD_guards` closes the one money-moving operation
  that had no public success-inversion boundary. The remaining admin/config
  operations are covered by the frame families in `BlastRadius.lean`
  (`admin_frame`, `admin_cannot_touch_balances`, …); the accepted/reverted
  boundary itself is `StepResult` in `Transition.lean`.

* **V2-VALUE** — `pending_standard_claim_covered` /
  `pending_flexible_claim_covered`: on any state carrying `ProtocolInvV2`
  (hence on every `ReachInit`-reachable state), each individual recorded
  unlock position is covered by collateral plus reserve — the claim-level
  non-depletion corollary, *derived* from the accounting invariant exactly as
  the v2 ladder requires.

Status (proof-map §11): `accepted_arithmetic_safe` and the coverage
corollaries are model-local; the `ReachInit` wrappers are reachable-scoped.
-/

namespace Apyx

/-! ## V2-TRANS gap-fill: the lock guards -/

/-- Success inversion (guard half) for `lockApxUSD`: pause down, caller not
deny-listed, and the burned amount within the caller's balance. -/
theorem lockApxUSD_guards (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h : step s (Op.lockApxUSD amount) caller = some s') :
    s.globalPause = false ∧ s.denylist caller = false ∧
    amount ≤ s.apxUSDBal caller := by
  simp only [step] at h
  (repeat' split at h) <;>
    first
      | (refine ⟨?_, ?_, ?_⟩ <;> simp_all <;> omega)
      | exact absurd h (by simp)

/-! ## V2-ARITH: the per-operation no-underflow package -/

/-- The arithmetic-safety facts an accepted step guarantees: every `Nat`
subtraction performed by the operation is covered by an inequality, so no
implicit truncation occurs on the accepted path. Operations that perform no
guarded subtraction map to `True`; `handleStressEvent`'s clamped collateral
subtraction is intentional model semantics recorded in `StressContract`. -/
def ArithmeticSafe (s : State) (op : Op) (caller : Address) : Prop :=
  match op with
  | Op.lockApxUSD amount => amount ≤ s.apxUSDBal caller
  | Op.requestUnlock amount => amount ≤ s.apxUSDBal caller
  | Op.flexibleRequestUnlock amount => amount ≤ s.apxUSDBal caller
  | Op.redeemApxUSD amount =>
      amount ≤ s.apxUSDBal caller ∧
      amount * s.redemptionValue / ray ≤ s.usdcReserve
  | Op.executeRFQRedemption user amount =>
      amount ≤ s.apxUSDBal user ∧ amount ≤ s.rfqRequests user ∧
      amount * s.redemptionValue / ray ≤ s.usdcReserve
  | Op.poolRedeem amount _ _ =>
      amount * s.redemptionValue / ray ≤ s.usdcReserve
  | Op.withdrawReserve amount _ => amount ≤ s.usdcReserve
  | Op.withdraw assets _ =>
      withdrawShares assets (computeExchangeRate (pullVestedYield s))
        ≤ (pullVestedYield s).apyUSDBal caller ∧
      assets ≤ (pullVestedYield s).vaultApxUSDBal
  | Op.redeem shares _ =>
      shares ≤ (pullVestedYield s).apyUSDBal caller ∧
      redeemAssets shares (computeExchangeRate (pullVestedYield s))
        ≤ (pullVestedYield s).vaultApxUSDBal
  | _ => True

/-- **Every accepted step is arithmetically safe**: the guards enforced by the
transition discharge the whole package, operation by operation. -/
theorem accepted_arithmetic_safe (s : State) (op : Op) (caller : Address)
    (s' : State) (hstep : step s op caller = some s') :
    ArithmeticSafe s op caller := by
  cases op with
  | lockApxUSD amount =>
      exact (lockApxUSD_guards s amount caller s' hstep).2.2
  | requestUnlock amount =>
      exact (requestUnlockStep_effect s amount caller s' hstep).2.1
  | flexibleRequestUnlock amount =>
      exact (flexibleRequestUnlockStep_effect s amount caller s' hstep).2.1
  | redeemApxUSD amount =>
      obtain ⟨-, -, hb, hr, -, -⟩ := redeemApxUSDStep_effect s amount caller s' hstep
      exact ⟨hb, hr⟩
  | executeRFQRedemption user amount =>
      obtain ⟨-, -, -, hreq, hb, hr, -⟩ :=
        executeRFQRedemptionStep_effect s user amount caller s' hstep
      exact ⟨hb, hreq, hr⟩
  | poolRedeem amount receiver minOut =>
      exact (poolRedeemStep_effect s amount receiver minOut caller s' hstep).1
  | withdrawReserve amount receiver =>
      exact (withdrawReserveStep_effect s amount receiver caller s' hstep).2.1
  | withdraw assets receiver =>
      obtain ⟨-, hshares, hassets, -⟩ :=
        withdrawStep_effect s assets receiver caller s' hstep
      exact ⟨hshares, hassets⟩
  | redeem shares receiver =>
      obtain ⟨-, hshares, hassets, -⟩ :=
        redeemStep_effect s shares receiver caller s' hstep
      exact ⟨hshares, hassets⟩
  | _ => exact trivial

/-! ## V2-VALUE: individual claim coverage from the accounting invariant -/

private theorem le_sum_map_of_mem {α : Type} {f : α → Nat} :
    ∀ {l : List α} {i : α}, i ∈ l → f i ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro i h; cases h
  | cons a rest ih =>
      intro i h
      cases h with
      | head =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.le_add_right _ _
      | tail _ hmem =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- A recorded standard position's face amount is bounded by the standard
liability total. -/
theorem standardUnlockTotal_covers (s : State) (id : Nat)
    (owner : Address) (amount cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd)) :
    amount ≤ standardUnlockTotal s := by
  unfold standardUnlockTotal
  have hmem : id ∈ List.range s.nextUnlockId := List.mem_range.mpr hid
  refine Nat.le_trans ?_ (le_sum_map_of_mem hmem)
  simp [hreq]

/-- A recorded flexible position's face amount is bounded by the flexible
liability total. -/
theorem flexibleUnlockTotal_covers (s : State) (id : Nat)
    (owner : Address) (amount requestTime cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd)) :
    amount ≤ flexibleUnlockTotal s := by
  unfold flexibleUnlockTotal
  have hmem : id ∈ List.range s.nextUnlockId := List.mem_range.mpr hid
  refine Nat.le_trans ?_ (le_sum_map_of_mem hmem)
  simp [hreq]

/-- **Claim-level non-depletion, standard channel**: on any state carrying the
v2 invariant, each individual recorded standard unlock is covered by
collateral plus reserve. Derived from `SolventOutstanding` through the
liability totals, exactly the v2 economic ladder. -/
theorem pending_standard_claim_covered (s : State) (hinv : ProtocolInvV2 s)
    (id : Nat) (owner : Address) (amount cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd)) :
    amount ≤ s.totalCollateralValue + s.usdcReserve := by
  have hsol : SolventOutstanding s := hinv.1.2.1
  have h1 := standardUnlockTotal_covers s id owner amount cooldownEnd hid hreq
  unfold SolventOutstanding outstandingApxUSD pendingApxUSD at hsol
  omega

/-- **Claim-level non-depletion, flexible channel.** -/
theorem pending_flexible_claim_covered (s : State) (hinv : ProtocolInvV2 s)
    (id : Nat) (owner : Address) (amount requestTime cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd)) :
    amount ≤ s.totalCollateralValue + s.usdcReserve := by
  have hsol : SolventOutstanding s := hinv.1.2.1
  have h1 := flexibleUnlockTotal_covers s id owner amount requestTime cooldownEnd hid hreq
  unfold SolventOutstanding outstandingApxUSD pendingApxUSD at hsol
  omega

/-- The reachable-state form: every recorded standard claim on a
`ReachInit`-reachable state is covered. -/
theorem pending_standard_claim_covered_reachable (s : State) (h : ReachInit s)
    (id : Nat) (owner : Address) (amount cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.unlockRequests id = some (owner, amount, cooldownEnd)) :
    amount ≤ s.totalCollateralValue + s.usdcReserve :=
  pending_standard_claim_covered s (protocolInvV2_reachable s h)
    id owner amount cooldownEnd hid hreq

/-- The reachable-state form, flexible channel. -/
theorem pending_flexible_claim_covered_reachable (s : State) (h : ReachInit s)
    (id : Nat) (owner : Address) (amount requestTime cooldownEnd : Nat)
    (hid : id < s.nextUnlockId)
    (hreq : s.flexibleUnlockRequests id =
      some (owner, amount, requestTime, cooldownEnd)) :
    amount ≤ s.totalCollateralValue + s.usdcReserve :=
  pending_flexible_claim_covered s (protocolInvV2_reachable s h)
    id owner amount requestTime cooldownEnd hid hreq

end Apyx
