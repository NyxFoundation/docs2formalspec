import D2fsSpecs.Accounting

/-!
# V2-INV: phase structure and the total operation classification

Proof Map v2 (life#59) V2-B demands that no conservation theorem carry its
operation exclusions as *implicit* assumptions: every operation must either
preserve the composite invariant or fall under an explicitly named,
separately proved exception contract. `handleStressEvent` and
`catastrophicBackstop` cannot satisfy a conservation invariant by design —
losing collateral and paying out the whole reserve are their specified
effects — so they get *phase-scoped* rules rather than membership in the
preserving class.

Layers:

* **Phases, derived from the existing state** — `NormalPhase` /
  `StressPhase` read `emergencyFlag`, the model's single phase bit (only
  `handleStressEvent` sets it, nothing clears it). `stressPhase_absorbing`
  proves the phase order Normal → Stress is one-way; `req_catastrophic_backstop`
  already proves the backstop fires only inside `StressPhase`.

* **Exception contracts** — `StressContract` (collateral falls by exactly the
  stress amount, the flag rises, the obligation ledger and reserve are framed,
  and pending-aware solvency degrades by *at most the stress amount*),
  `BackstopContract` (fires only in stress, zeroes the reserve, credits the
  pro-rata payouts, reprices, frames the obligation ledger),
  `ReserveOutflowContract` (admin-only, guarded by the reserve balance, exact
  reserve/receiver deltas, obligation ledger framed).

* **`opCoverage` + `stepContract`** — the totality theorems: every `Op`
  is either `OutstandingScopedOp` (the preserving class of
  `protocolInvFull_step`) or one of the five named exceptions, and one theorem
  delivers the applicable rule for *every* operation with no silent gaps.

Status (proof-map §11): all contracts are model-local; `stepContract` is
the total per-step classification; phase absorption is model-local. The
vault exits appear here through their V2-ACC conservation equations — under
`apxUSDObligations` they are conservation, not exclusion.
-/

namespace Apyx

/-! ## Phases

`NormalPhase` is defined in `Init.lean` (it is a conjunct of `Init`); this
module adds its stress-side counterpart and the phase-order facts. -/

/-- Stress operation: the emergency flag is up. Entered by a successful
`handleStressEvent`; the backstop's guard requires this phase. -/
def StressPhase (s : State) : Prop := s.emergencyFlag = true

/-- **The stress phase is absorbing**: no operation clears the emergency flag.
Once the protocol has entered stress, every successful step stays there. -/
theorem stressPhase_absorbing (s : State) (op : Op) (caller : Address) (s' : State)
    (hstep : step s op caller = some s') (h : StressPhase s) : StressPhase s' := by
  unfold StressPhase at h ⊢
  cases hop : op with
  | handleStressEvent a =>
      subst hop
      simp only [step] at hstep
      split at hstep
      · cases Option.some.inj hstep; rfl
      · exact absurd hstep (by simp)
  | _ =>
      subst hop
      rw [emergencyFlag_frame s _ caller s' hstep (by simp)]
      exact h

/-! ## Exception contracts -/

/-- The stress-phase entry contract: admin-only, the collateral falls by
exactly the exogenous loss, the flag rises, the obligation ledger and the
reserve are framed — and pending-aware solvency degrades by **at most the
stress amount**, the v2 "buffer decrease bounded by the stress amount" rule. -/
def StressContract (s s' : State) (amount : Nat) : Prop :=
  s'.totalCollateralValue = s.totalCollateralValue - amount ∧
  StressPhase s' ∧
  apxUSDObligations s' = apxUSDObligations s ∧
  s'.usdcReserve = s.usdcReserve ∧
  outstandingApxUSD s' = outstandingApxUSD s ∧
  (SolventOutstanding s →
    outstandingApxUSD s' ≤ s'.totalCollateralValue + s'.usdcReserve + amount)

/-- The wind-down contract: fires only inside `StressPhase`, reprices to the
collateral-per-token rate, credits every address its pro-rata payout, zeroes
the reserve and the buffer, and frames the apxUSD obligation ledger. The
payout/residual conservation equation is `catastrophicBackstop_accounting`. -/
def BackstopContract (s s' : State) : Prop :=
  StressPhase s ∧
  s'.redemptionValue = (s.totalCollateralValue * ray) / s.totalSupply_apxUSD ∧
  (∀ a, s'.usdcBal a = s.usdcBal a + backstopPayout s a) ∧
  s'.usdcReserve = 0 ∧
  s'.overcollateralizationBuffer = 0 ∧
  apxUSDObligations s' = apxUSDObligations s

/-- The bare admin reserve outflow: guarded by the reserve balance, with exact
reserve and receiver deltas; the apxUSD obligation ledger is framed. -/
def ReserveOutflowContract (s s' : State) (amount : Nat) (receiver : Address) : Prop :=
  amount ≤ s.usdcReserve ∧
  s'.usdcReserve = s.usdcReserve - amount ∧
  s'.usdcBal receiver = s.usdcBal receiver + amount ∧
  apxUSDObligations s' = apxUSDObligations s

theorem handleStressEvent_contract (s : State) (amount : Nat)
    (caller : Address) (s' : State)
    (hstep : step s (Op.handleStressEvent amount) caller = some s') :
    StressContract s s' amount := by
  simp only [step] at hstep
  split at hstep
  · cases Option.some.inj hstep
    refine ⟨rfl, rfl, ?_, rfl, ?_, ?_⟩
    · unfold apxUSDObligations apxUSDFlow
      rw [outstandingApxUSD_of_projections_eq (s :=
        { s with totalCollateralValue := s.totalCollateralValue - amount,
                 emergencyFlag := true }) (t := s) rfl rfl rfl rfl]
    · exact outstandingApxUSD_of_projections_eq rfl rfl rfl rfl
    · intro hsol
      have h1 : outstandingApxUSD
          { s with totalCollateralValue := s.totalCollateralValue - amount,
                   emergencyFlag := true } = outstandingApxUSD s :=
        outstandingApxUSD_of_projections_eq rfl rfl rfl rfl
      unfold SolventOutstanding at hsol
      rw [h1]
      dsimp only
      omega
  · exact absurd hstep (by simp)

theorem catastrophicBackstop_contract (s : State) (caller : Address) (s' : State)
    (hstep : step s Op.catastrophicBackstop caller = some s') :
    BackstopContract s s' := by
  have hguard : caller = s.admin ∧ s.emergencyFlag = true := by
    simp only [step] at hstep
    split at hstep
    · assumption
    · exact absurd hstep (by simp)
  obtain ⟨hcaller, hflag⟩ := hguard
  subst hcaller
  obtain ⟨-, hprice, hbal, hres, hbuf⟩ := req_catastrophic_backstop s s' hstep
  refine ⟨hflag, hprice, fun a => hbal a, hres, hbuf, ?_⟩
  simp only [step, hflag] at hstep
  split at hstep
  · cases Option.some.inj hstep
    unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
      standardUnlockTotal flexibleUnlockTotal
    dsimp only
  · exact absurd hstep (by simp)

theorem withdrawReserve_contract (s : State) (amount : Nat)
    (receiver caller : Address) (s' : State)
    (hstep : step s (Op.withdrawReserve amount receiver) caller = some s') :
    ReserveOutflowContract s s' amount receiver := by
  simp only [step] at hstep
  split at hstep
  · split at hstep
    · exact absurd hstep (by simp)
    · rename_i hguard
      cases Option.some.inj hstep
      refine ⟨by omega, rfl, by simp, ?_⟩
      unfold apxUSDObligations apxUSDFlow outstandingApxUSD pendingApxUSD
        standardUnlockTotal flexibleUnlockTotal
      dsimp only
  · exact absurd hstep (by simp)

/-! ## Totality: every operation is classified, nothing is silently excluded -/

/-- **Operation coverage**: every `Op` is either in the preserving scope of
`protocolInvFull_step` or is one of the five named exceptions. This is the v2
"no implicit exclusion" declaration, checkable by case analysis. -/
theorem opCoverage (op : Op) :
    OutstandingScopedOp op ∨
    (∃ assets receiver, op = Op.withdraw assets receiver) ∨
    (∃ shares receiver, op = Op.redeem shares receiver) ∨
    (∃ amount, op = Op.handleStressEvent amount) ∨
    op = Op.catastrophicBackstop ∨
    (∃ amount receiver, op = Op.withdrawReserve amount receiver) := by
  cases op <;>
    first
      | (left
         refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ => ?_, ?_, fun _ _ => ?_⟩ <;>
           (simp; done))
      | (right; left; exact ⟨_, _, rfl⟩)
      | (right; right; left; exact ⟨_, _, rfl⟩)
      | (right; right; right; left; exact ⟨_, rfl⟩)
      | (right; right; right; right; left; rfl)
      | (right; right; right; right; right; exact ⟨_, _, rfl⟩)

/-- **The total step contract**: one theorem delivering, for *every* operation
with no exclusions, the rule that governs it — invariant preservation for the
scoped class, conservation for the vault exits, and the named phase/outflow
contracts for the three remaining exceptions. -/
theorem stepContract (s : State) (op : Op) (caller : Address) (s' : State)
    (hstep : step s op caller = some s') :
    (OutstandingScopedOp op → PriceBoundedOp op → ProtocolInvFull s → ProtocolInvFull s') ∧
    (∀ assets receiver, op = Op.withdraw assets receiver → RegistryWellIndexed s →
      apxUSDObligations s' = apxUSDObligations s) ∧
    (∀ shares receiver, op = Op.redeem shares receiver → RegistryWellIndexed s →
      apxUSDObligations s' = apxUSDObligations s) ∧
    (∀ amount, op = Op.handleStressEvent amount → StressContract s s' amount) ∧
    (op = Op.catastrophicBackstop → BackstopContract s s') ∧
    (∀ amount receiver, op = Op.withdrawReserve amount receiver →
      ReserveOutflowContract s s' amount receiver) := by
  refine ⟨fun hscope hprice hinv => protocolInvFull_step s op caller s' hinv hstep hscope hprice,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro assets receiver rfl hreg
    exact apxUSDObligations_withdraw s assets receiver caller s' hreg hstep
  · rintro shares receiver rfl hreg
    exact apxUSDObligations_redeem s shares receiver caller s' hreg hstep
  · rintro amount rfl
    exact handleStressEvent_contract s amount caller s' hstep
  · rintro rfl
    exact catastrophicBackstop_contract s caller s' hstep
  · rintro amount receiver rfl
    exact withdrawReserve_contract s amount receiver caller s' hstep

end Apyx
