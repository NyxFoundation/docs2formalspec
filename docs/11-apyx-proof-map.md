# Apyx Lean Proof Map

This document is a working map for proving the safety of Apyx. It separates the claims that belong in Lean from the claims that require analysis of the deployed implementation, and gives the proof order that keeps the model understandable.

The central idea is simple:

> Prove what one action changes, prove what it cannot change, and then lift those local facts into the accounting and safety properties of the whole protocol.

## 1. What other formalized DeFi systems teach us

The most useful examples do not try to prove every possible property in one formalization. They choose a clear semantic boundary and build a small number of reusable lemmas around it.

| System or approach | Main lesson for Apyx |
| --- | --- |
| [Dexter2](https://arxiv.org/abs/2203.08016) | Separate functional correctness from safety properties of interacting contracts. |
| [DeepSEA AMM](https://drops.dagstuhl.de/storage/01oasics/oasics-vol095-fmbc2021/OASIcs.FMBC.2021/OASIcs.FMBC.2021.pdf) | State an economic property precisely, such as non-depletion or a manipulation-cost bound, and prove it from an explicit invariant. |
| [Maker K-DSS](https://github.com/dapphub/k-dss) | Specify both successful and reverting behavior, then check those claims against executable semantics. |
| [Aave V2 Certora analysis](https://files.safe.de.fi/safe/files/audit/pdf/AaveV2Dec2020.pdf) | Use high-level accounting, health, frame, and relational rules, while documenting rounding and scope assumptions explicitly. |
| [Verity](https://github.com/lfglabs-dev/verity) | Keep the trust boundary visible: a theorem about a design model is different from a theorem that connects the model to generated code or bytecode. |
| [Uniswap Foundation Security Framework](https://github.com/uniswapfoundation/security-framework) | Treat security as a set of risk dimensions and operational checks, not as one monolithic theorem. |

These examples suggest a layered proof plan:

1. define the abstract protocol behavior;
2. prove design-level safety properties;
3. audit the implementation against typed properties;
4. use implementation-oriented tools for the remaining bytecode and arithmetic questions.

## 2. Use precise assurance terms

The following claims should not be mixed together.

### Functional correctness

An accepted action produces the state and events required by the protocol specification. A rejected action preserves the state and returns an allowed reason.

### Safety invariant

A bad state is never reached from an allowed initial state. Examples include negative effective liquidity, broken supply accounting, invalid ownership, or a reserve becoming insufficient for a liability.

### Capability and attack resistance

An attacker or privileged actor cannot obtain a capability that the protocol is meant to prevent, or cannot use an allowed capability to violate a security bound. Examples include draining assets, bypassing a timelock, or exceeding an oracle or pricing limit.

### Liveness and progress

An action that satisfies its preconditions eventually becomes executable, or the protocol eventually reaches a permitted phase. This requires assumptions about time, scheduling, and fairness.

### Implementation assurance

The deployed implementation actually satisfies the modeled behavior. This is a refinement or conformance question, not a consequence of a Lean theorem about an abstract state machine.

A theorem about the model, a theorem about the Solidity or bytecode, and a human-reviewed mapping between them are three different artifacts. The proof map keeps them separate.

## 3. The assurance graph

The project should connect these artifacts with stable property identifiers.

~~~text
natural-language specification
          |
          v
Property manifest
(property ID, source anchor, claim, Lean theorem,
 implementation target, tool, evidence)
          |
          +--> Lean design proof
          |    State -> Action -> StepResult -> Inv -> Reach
          |
          +--> SPECA specification-to-property audit
          |    typed property -> program subgraph -> proof attempt
          |
          +--> implementation checks
               Certora / Halmos / SMT / fuzzing / bytecode analysis
          |
          v
confirmed result, finding, mismatch, or residual gap
~~~

The Lean core should establish the abstract design and its economic invariants. SPECA should audit whether the written specification gives rise to meaningful, reachable, typed properties and whether the relevant implementation paths are covered. Certora, Halmos, SMT-based analyses, fuzzing, and bytecode-level checks should handle implementation-specific behavior.

A full formal simulation or refinement proof can be added later, but it should be treated as a separate project with its own representation relation and trust-boundary argument. It should not be implied by a property table alone.

## 4. Start with an explicit transition result

A transition must represent both success and failure.

~~~lean
inductive StepResult
  | reverted (reason : RevertReason)
  | accepted (state : State) (events : List Event)
~~~

The model should make the following relations available:

- a precondition describing when an action may succeed;
- a postcondition describing the resulting state and events;
- a revert condition describing why an action is rejected;
- a frame condition describing what remains unchanged;
- a relational property comparing two executions or two users.

For each public action, the first proof target is therefore not a large economic theorem. It is a transition contract:

~~~text
precondition
    -> accepted result satisfies postcondition and frame
    -> reverted result preserves state and has an allowed reason
~~~

Success-only proofs can miss an implementation that accepts an invalid action, rejects a valid action, or changes state before reverting.

The current boundary is implemented by `StepResult`, `stepResult`,
`stepResult_total`, `stepResult_reverted_iff`,
`stepResult_accepted_iff`, and `stepResult_state?` in
`lean/D2fsSpecs/Transition.lean`. A
revert is represented by absence of a successor because the underlying
`Apyx.step` returns `Option State`; `RevertReason.modelUnknown` does not claim
to identify the failed guard. Accepted events are the `eventDelta` bookkeeping
projection of the cumulative log. `stepResult_reverted_no_state` records the
strongest revert-state fact available in this model: no successor state exists
to compare with the pre-state. Exact guard reasons, event fidelity, and
partial-state-before-revert behavior therefore remain explicit model gaps,
not silently proved properties.

## 5. Establish representation invariants before economic theorems

Economic properties are only meaningful when the state representation is well formed. The initial invariant should cover at least the following.

### 5.1 Ledger consistency

State what balances, total supply, reserves, and liabilities mean. Then prove the relationships between them.

Typical examples:

- the sum of tracked balances agrees with total supply, modulo explicitly modeled rounding;
- a mint or burn changes supply and balances by matching amounts;
- an outgoing transfer cannot exceed the available balance;
- the reserve and liability ledgers use the same units and asset domains.

The concrete ledger predicate is `ApxUSDLedgerConsistent` in
`lean/D2fsSpecs/Ledger.lean`. Its finite holder-list representation makes the
support and supply identity explicit. `apxUSDLedgerConsistent_default` proves
initialization, `apxUSDLedgerConsistent_step` proves preservation for every
current `Op`, and `apxUSDLedgerConsistent_trace` lifts it over revert-skip
traces. `LedgerCoveredOp`/`ledgerCoveredOp_all` make operation coverage
reviewable. `ledgerGapWitness` and
`wellFormed_solvent_not_imply_ledgerConsistent` intentionally record that the
aggregate predicates alone do not imply this finite identity. The primitive
transfer layer covers both cases: `apxUSDLedgerConsistent_transfer` handles
distinct addresses under the balance bound, while `transferApxUSD_self` and
`apxUSDLedgerConsistent_transfer_self` make self-transfer an explicit no-op.

The analogous apyUSD boundary is `ApyUSDLedgerConsistent` in
`outputs/apyx/HolderValue.lean`. Its default instance is proved by
`apyUSDLedgerConsistent_default`. The primitive writers are covered by
`apyUSDLedgerConsistent_mint` and `apyUSDLedgerConsistent_burn`; the public
step decomposition is made explicit by `ApyLedgerFrameOp`,
`ApyLedgerCoveredOp`, and `apyLedgerCoveredOp_all`. The branch theorems
`apyUSDLedgerConsistent_lock_step`,
`apyUSDLedgerConsistent_withdraw_step`, and
`apyUSDLedgerConsistent_redeem_step`, together with
`apyUSDLedgerConsistent_frame_step`, compose into
`apyUSDLedgerConsistent_step`; `apyUSDLedgerConsistent_trace` lifts it over
revert-skip traces. The relation is therefore a proved reachable-state
invariant from `default`, while arbitrary hand-written `State` values can
still violate it because the state type itself has no finite-support field.
`finitePoolValueAt`, `finitePoolRateDelta`, and
`finitePoolValueAt_rateDelta` provide the finite aggregate needed to sum
holder-level rate revaluations. `apyUSDLedgerConsistent_of_projections_eq`
is the frame composition lemma, and
`apyUSDLedgerConsistent_covered_step` keeps the operation coverage visible
before the universal theorem. Finally, `apyUSDLedgerGapWitness`,
`apyUSDLedgerGapWitness_two_holders_exceed_supply`, and
`apyUSDLedgerGapWitness_not_consistent` record the model boundary: arbitrary
hand-written states can violate the relation even though the default trace
invariant is preserved. For the pool's apyUSD-only conversion, the
floor-rounding layer is explicit: `finiteApyUSDValueAt` and
`finiteApyUSDValueAt_le_redeemAssets_sum` give the aggregate upper bound,
`apyUSDLedgerConsistent_finiteApyUSDValueAt_bound` connects it to the supply
identity, and `finiteApyUSDValueAt_rounding_gap` shows why the bound is not an
equality theorem. `apyUSDValueRoundingGapWitness_consistent` proves that this
strict gap occurs in a state satisfying the finite ledger relation, not only
in an invalid arbitrary state. The exact alternative is the numerator layer:
`finiteApyUSDNumerator`, `finiteApyUSDNumerator_eq_sum_mul`,
`apyUSDLedgerConsistent_finiteApyUSDNumerator`, and
`apyUSDLedgerConsistent_finiteApyUSDValueAt_single_floor` prove that the
holder products can be summed exactly and divided by `ray` once. This is an
explicit rational-style accounting convention, not a claim that the deployed
contract exposes this aggregate numerator.

The pending-apxUSD boundary is a separate, registry-indexed layer rather than
another conjunct of `ProtocolInv`. `standardUnlockTotal` and
`flexibleUnlockTotal` sum the two finite registries by id;
`pendingApxUSD` combines them, and `outstandingApxUSD` adds the circulating
apxUSD supply. Fresh-allocation and in-place update/retirement lemmas make the
arithmetic visible:
`standardUnlockTotal_createStandardUnlock`,
`standardUnlockTotal_updateStandardUnlock`,
`standardUnlockTotal_retireStandardUnlock`,
`flexibleUnlockTotal_createFlexibleUnlock`,
`flexibleUnlockTotal_createStandardUnlock`,
`standardUnlockTotal_createFlexibleUnlock`,
`flexibleUnlockTotal_retireFlexibleUnlock`, and
`flexibleUnlockTotal_retireStandardUnlock`. The request-side wrappers are
`standardUnlockTotal_requestUnlockStep`,
`flexibleUnlockTotal_requestUnlockStep`,
`standardUnlockTotal_flexibleRequestUnlockStep`,
`outstandingApxUSD_requestUnlockStep`,
`outstandingApxUSD_requestUnlock`,
`outstandingApxUSD_flexibleRequestUnlock`, and
`outstandingApxUSD_flexibleRequestUnlock_step`. Standard settlement is closed
by `outstandingApxUSD_claimUnlock`; flexible settlement is deliberately stated
as `outstandingApxUSD_flexibleClaimUnlock`, where the outstanding amount falls
by exactly the modeled early-exit fee. These are boundary theorems, not a
protocol-wide asset-conservation theorem: the current state has neither a fee
wallet balance nor explicit unlock-token custody, so adding them to
`ProtocolInv` would be an unsupported model claim.

The receipt amount is now tied to that liability ledger by
`UnlockTokenLedgerConsistent`. It states, for every allocated id, that the
standard or flexible registry entry, `unlockTokenOwner`, and
`unlockTokenAmount` describe the same owner and face amount, or that an empty
slot has no receipt amount. `unlockTokenLedgerConsistent_default` and the
create/update/retire lemmas prove the lifecycle preservation boundary. The
burn and mint frame lemmas, together with
`unlockTokenLedgerConsistent_requestUnlockStep`,
`unlockTokenLedgerConsistent_requestUnlock`,
`unlockTokenLedgerConsistent_flexibleRequestUnlock`,
`unlockTokenLedgerConsistent_claimUnlock`, and
`unlockTokenLedgerConsistent_flexibleClaimUnlock`, now compose that relation
with all four modeled request/claim public branches, including the standard
top-up branch. It is still kept separate from `ProtocolInv`: these theorems
establish receipt/registry consistency, but do not add receipt custody,
fee-wallet custody, or USDC supply to the current state, and the composite
invariant does not yet cover every state-changing operation under this
accounting boundary.

The missing USDC side is made explicit without adding an unsupported field to
`State`: `UsdcLedgerConsistent s holders totalSupply` takes the finite holder
support and total USDC supply as external accounting parameters. Its default
witness, `usdcLedgerConsistent_debit_to_reserve`,
`usdcLedgerConsistent_reserve_payout`, and `usdcLedgerConsistent_of_frame`
lemmas show the exact arithmetic needed for deposits, reserve payouts, and
unaffected operations. `UsdcLedgerEffect` and
`usdcLedgerConsistent_effect` compose those cases without pretending that the
current dispatcher has supplied the missing finite support or total supply.
The six concrete mappings are closed for `depositUSDC`, `mintApxUSD`,
`redeemApxUSD`, `executeRFQRedemption`, `withdrawReserve`, and `poolRedeem`
by `depositUSDCStep_effect`, `mintApxUSDStep_effect`,
`redeemApxUSDStep_effect`, `executeRFQRedemptionStep_effect`,
`withdrawReserveStep_effect`, `poolRedeemStep_effect` and their
`usdcLedgerEffect_depositUSDC`, `usdcLedgerEffect_mintApxUSD`,
`usdcLedgerEffect_redeemApxUSD`, `usdcLedgerEffect_executeRFQRedemption`,
`usdcLedgerEffect_withdrawReserve`, and `usdcLedgerEffect_poolRedeem`
theorems in `Apyx.lean` and `HolderValue.lean`. `UsdcLedgerFrameOp`,
`UsdcLedgerCoveredOp`, `usdcLedgerCoveredOp_of_not_backstop`,
`usdcLedgerConsistent_covered_step`, `usdcLedgerConsistent_step`, and
`usdcLedgerConsistent_trace` then lift those mappings and all USDC-frame
operations to a conditional successful-step and revert-skip trace boundary.
Every operation in that boundary must be different from
`catastrophicBackstop`. For `depositUSDC` and `mintApxUSD`, the debited caller
must be in the external support list; for redemption and withdrawal paths, the
credited caller, requested user, or named receiver must be in it. These
premises are required for every trace entry, including operations that revert.
Regression §R24 pins the receiver rule, and §R25 pins the trace composition.
The requested user or named receiver, rather than an executing RFQ
counterparty, determines the payout support entry.
`catastrophicBackstop` remains outside this exact effect for two reasons: it
distributes to many addresses, while the effect has a single-receiver payout
arm, and its per-holder Nat division can leave a rounding remainder. Its
conservation statement therefore belongs in a separate deployment/SPECA
model; the zero-supply division corner must be handled there as well. The
fee-wallet treatment and decimal scaling also remain there.

The next internal boundary is `apxUSDFlow`: vault custody plus
`outstandingApxUSD`. Projection lemmas
`standardUnlockTotal_of_projections_eq`,
`flexibleUnlockTotal_of_projections_eq`, and
`outstandingApxUSD_of_projections_eq` keep event emission and rate publication
from obscuring that accounting. `outstandingApxUSD_createStandardUnlock` and
`apxUSDFlow_vaultWithdrawPost` prove the generic vault-exit cancellation;
`apxUSDFlow_withdraw` and `apxUSDFlow_redeem` expose it at the public step
boundary. The request and claim flow forms are
`apxUSDFlow_requestUnlockStep`, `apxUSDFlow_requestUnlock`,
`apxUSDFlow_flexibleRequestUnlock`, `apxUSDFlow_claimUnlock`, and
`apxUSDFlow_flexibleClaimUnlock`. These exit theorems are stated against
`apxUSDFlow (pullVestedYield s)`, not blindly against the pre-state: the live
vest pull is an external custody inflow and remains a separate accounting
boundary. `apxUSDFlow_pullVestedYield` states that this inflow is exactly
`vestedAmount s s.now` while the circulating and pending ledgers are framed.
`withdrawStep_effect` and `redeemStep_effect` in `Apyx.lean` are the
public inversion interfaces used to make that distinction explicit.

The unlock-only aggregate trace is now explicit as well. `ApxUSDFlowStep`
accepts successful standard/flexible requests (carrying registry and supply
premises), successful claims (carrying an in-range recorded position), and
`tick` as a pure frame.
`ApxUSDFlowTrace` composes those steps; `apxUSDFlow_step` proves the local
flow equation, and `apxUSDFlow_trace` lifts it to `execTrace`. Flexible-claim
fees are accumulated separately by `apxUSDFlowStepFee`, because the current
state has no fee-wallet balance. This closes an internal unlock-flow trace,
not the mixed trace containing vault exits, live vesting inflows, or the
unmodeled USDC and fee-wallet ledgers. The model/spec boundary is itself
formalized in `DeploymentFees.lean`: `model_undercharges_withdraw`,
`vault_leak_linear`, `liveCurve_bounds_contradict_the_corpus`, and
`both_fees_bite` show why adding a fee-wallet conservation claim without first
choosing the deployment-faithful fee specification would be unsound.

### 5.2 Registry consistency

For pending requests, positions, or claims, specify:

- ownership;
- amounts;
- timestamps or deadlines;
- status flags;
- links or array indices;
- uniqueness and bounds.

Every action that creates, consumes, or updates a registry entry must preserve these relationships.

The concrete registry layer is `RegistryWellIndexed`, together with
`RegistryBounded` and `OwnerPointerSound`, in
`lean/D2fsSpecs/Registry.lean`. The initialization and step theorems are
`registryWellIndexed_default`, `registryWellIndexed_step`, and
`registryWellIndexed_reachable`; the constructor-specific lemmas cover fresh
allocation, top-ups, claims, and vault exits. Registry reachability is kept
separate from the stricter `ProtocolReach` relation used by the composite
invariant. At the request boundary, `standardUnlockAmount` and
`requestUnlockStep_pending_conservation` make the local liability movement
explicit: under the request's balance guard, the caller's burned balance plus
the amount in its tracked standard position is unchanged. The measure returns
zero for a missing or mismatched pointer, so this theorem does not silently
assume a canonical registry. It does not yet account for all pending positions
or a finite liability ledger. A stronger holder-facing request theorem now
covers both fresh creation and in-place top-up: `requestUnlockStep_effect`
exposes the successful transition, `stdPositions_updateStandardUnlock`
accounts for the one changed finite-sum member, and
`requestUnlock_holderValueAt_neutral` proves value neutrality under
`RegistryBounded`. `OwnerPointerSound` is deliberately not required there:
the top-up branch checks the recorded owner before updating, while
`RegistryBounded` is the condition that prevents an out-of-range record from
being omitted by the finite sum. The claim-side local boundary
is now explicit too: `claimUnlockStep_effect` exposes the exact successful
post-state, `stdPositions_retireStandardUnlock` removes an in-range recorded
amount from the finite position sum, and `claimUnlock_holderValueAt_neutral`
shows that the owner value is unchanged at any fixed rate. These are local
settlement facts, not reachability or global solvency theorems. The flexible
counterpart is fee-aware rather than neutral: `flexibleClaimStep_effect`,
`flexibleClaimFee_le_amount`, `flexPositions_retireFlexibleUnlock`, and
`flexibleClaim_holderValueAt_fee` show that the owner's value falls by exactly
the published fee for an in-range successful flexible claim. The standard
request-to-claim trace is now composed as
`standardUnlock_holderValueAt_trace_neutral` at a fixed rate: it includes
requests, waits, and claims, and carries `RegistryWellIndexed` through the
induction. The live-value variant
`standardUnlock_holderValue_trace_neutral` is intentionally narrower and
excludes waits, because vesting can change the live rate. The fixed-rate
per-holder frames `requestUnlock_holderValueAt_fixedRate_frame`,
`flexibleRequestUnlock_holderValueAt_fixedRate_frame`,
`claimUnlock_holderValueAt_fixedRate_frame`, and
`flexibleClaim_holderValueAt_fixedRate_frame` make operator-mediated actions
explicit rather than silently restricting every caller to the tracked holder.
The combined fixed-rate inequality `unlockLedger_holderValueAt_trace_nonincreasing` now
adds flexible requests and claims: requests are neutral, while flexible
claims are non-increasing by the explicit fee. Its arbitrary-caller form is
`unlockLedger_holderValueAt_trace_nonincreasing_any_callers`. Its witness
`unlockLedger_holderValueAt_trace_witness` exercises a nonzero post-cooldown
fee rather than merely a zero-amount or reverted claim.
There is also a live-rate mixed sublanguage, `StableHolderValueOp`, whose
trace theorem `holderValue_stable_trace_nonincreasing` composes
`depositUSDC`, `redeemApxUSD`, and both unlock channels. It deliberately
excludes vault exits and clock steps because those change the pricing context.
The supporting lemma `holderValueAt_mono_rate` makes that boundary explicit:
the fixed-rate measure is monotone when the pricing rate falls, but a rate rise
is not free conservation and needs an additional economic argument.
The rate-aware definitions `RateAwareHolderValueOp`,
`holderValueExecutionRate`, `RateAwareSideCondition`, and `liveRateSequence`
make that argument stateable. `holderValueAt_rateAware_trace_bound` proves the
fixed-to-live bound under a pairwise non-increasing execution-rate schedule;
`totalAssets_pullVestedYield_of_pos_period` and
`holderValueExecutionRate_eq_live_of_rateAware` derive the initial-rate bridge
when `0 < vestPeriod`, so `holderValue_rateAware_trace_nonincreasing` no longer
needs a separately supplied first-rate inequality. The counterexample
`totalAssets_pullVestedYield_zero_period_counterexample` shows why the positive
period premise is a model condition rather than a proof artifact. The side
condition only carries the no-premium redemption bound through the trace;
operator exclusion is not needed because the trace is holder-signed and the
claim frames used by this theorem are already generic. This is a conditional
vault-trace theorem, not a blanket closure of the live-rate gap. The witnesses
`rateAware_schedule_not_automatic` and
`rateAware_schedule_not_automatic_without_dust` record both a dust-sized
`lockApxUSD` trace and a nonzero `withdraw` trace whose terminal live rate
rises, so the pairwise schedule cannot currently be derived from the model by
merely banning zero-share deposits.
The complementary accounting form uses `holderRateDelta` and
`traceRateAdjustments` instead of hiding those rises behind a schedule premise:
`holderValueAt_rateDelta` and
`holderValueAt_executionRate_step_with_rateDelta` separate the local fixed-rate
bound from signed rate revaluation, and
`holderValue_rateAware_trace_rateAdjusted` sums that revaluation over a whole
trace. This is the current model's honest bridge toward a pool-level ledger;
it does not yet claim that the revaluation sum is protocol-wide conservation.
The optional finite-support boundary is `ApyUSDLedgerConsistent`;
`finitePoolValueAt_rateDelta` shows how the holder-level accounting aggregates
over an explicit list. It is now preserved by every successful `Op` through
`apyUSDLedgerConsistent_step` and by `execTrace` through
`apyUSDLedgerConsistent_trace`; this still does not make every arbitrary value
of the current state representation a valid pool ledger.

### 5.3 Clock consistency

Represent time explicitly when a property depends on it.

The model should distinguish:

- a protocol action executed at time t;
- elapsed time advancing from t to t';
- deadlines and unlock times;
- phase transitions such as Live and WindingDown.

At minimum, prove monotonicity of time and the relationship between timestamps and permission checks.

For the current Apyx model, these obligations are stated directly over the
successful `step` relation in `lean/D2fsSpecs/Apyx.lean`:

- `now_moves_only_by_tick`: every successful non-`tick` operation preserves
  `State.now`;
- `tick_advances_now_exactly`: a successful `Op.tick dt` produces
  `now' = now + dt`;
- `now_nondecreasing`: every successful operation is monotone in `now`.

These are relational lemmas rather than a state-only clock predicate. That is
intentional: the clock is a property of a transition
history, and the state field alone does not say how time was reached. The
remaining time obligations are the deadline-specific permission lemmas and
the trace theorems that use these three facts.

### 5.4 Numeric-domain consistency

Choose the arithmetic domain for every quantity:

- natural numbers for nonnegative counts;
- integers for signed deltas;
- fixed-point integers for on-chain values;
- reals only for a mathematical approximation, with a bridge theorem and an error bound.

Rounding is part of the protocol behavior. A real-valued theorem does not automatically prove a fixed-point implementation.

The current Lean model makes this boundary explicit: `ray_pos` and
`mul_ray_div_ray` state the fixed-point scale and its exact cancellation in
Nat arithmetic. `div_add_div_le`, `redeemAssets_superadd`,
`withdrawShares_covers`, and `redeemAssets_sub_withdraw_le` state the floor and
ceil rounding facts used by the vault holder-value proofs. No real-number
approximation is used, so there is no hidden real-to-Nat bridge to trust.

The backstop allocation has a separate rounding boundary. `req_catastrophic_backstop`
proves the per-address floor-divided credit, while
`pro_rata_floor_underpays_witness` shows that those credits need not sum to the
reserve even when a finite holder list accounts for the entire supply. A future
model that claims "entire reserve" therefore needs an explicit remainder rule,
not only a finite-support summation. The zero-supply case also needs an
explicit policy, because Nat division credits every holder with zero while the
modeled step still sets the reserve to zero.

Decimal scaling is a separate fidelity boundary, not an omitted Nat lemma.
`MulDivFidelity.lean` formalizes the deployment-shaped single-`mulDiv` ray
conversions and the deviation of the current two-stage rate model. The current
Lean state uses normalized Nat units; the USDC-6 to token-18 conversion,
uint256 overflow, and Solidity division-by-zero behavior still belong to the
implementation/SPECA layer. A theorem over the normalized units must not be
read as a proof of those raw-token semantics.

## 6. Define reachability and prove an inductive invariant

A safety theorem should apply to reachable states, not just to arbitrary states that happen to satisfy an invariant.

A minimal shape is:

~~~lean
def ProtocolInv (s : State) : Prop :=
  RegistryWellIndexed s ∧ Solvent s ∧ WellFormed s ∧
  ApxUSDLedgerConsistent s ∧ ApyUSDLedgerConsistent s

inductive ProtocolReach : State → Prop
  | initial : ProtocolReach (default : State)
  | next {s s' : State} {op : Op} {caller : Address} :
      ProtocolReach s ->
      (es : List Event) ->
      stepResult s op caller = .accepted s' es ->
      SolvencyScopedOp op ->
      WellFormed s' ->
      ProtocolReach s'

theorem protocolInv_stepResult_accepted :
  ProtocolInv s ->
  stepResult s op caller = .accepted s' es ->
  SolvencyScopedOp op ->
  WellFormed s' ->
  ProtocolInv s'

theorem protocolInv_reachable :
  ProtocolReach s -> ProtocolInv s
~~~

The exact syntax can change, but the logical obligations must remain visible:

1. the initial state satisfies `ProtocolInv`;
2. every scoped successful transition preserves `ProtocolInv`;
3. `ProtocolReach` carries the same operation restriction and post-state
   `WellFormed` premise used by the preservation theorem.

If a preservation theorem only covers a restricted operation subtype while
reachability permits every `Op`, the final theorem has a gap. Either make the
reachability relation use the same restriction or prove that every reachable
successful action satisfies the required safety condition.

The invariant should be factored into small lemmas. A single giant invariant theorem is difficult to review and tends to hide which accounting relationship actually carries the argument.

In the current source, `ProtocolInv` combines `RegistryWellIndexed`, `Solvent`,
`WellFormed`, and both finite token ledger relations:
`ApxUSDLedgerConsistent` and `ApyUSDLedgerConsistent`. The composite module
imports the apyUSD ledger layer explicitly because that relation is defined in
`HolderValue.lean`, while the apxUSD relation lives in `Ledger.lean`.
`protocolInv_default` proves the base case,
`protocolInv_step` preserves the invariant at the successful `step` boundary,
and `protocolInv_stepResult_accepted` lifts the same proof to the accepted-result
boundary. `ProtocolReach` uses that accepted `StepResult` relation, so
`protocolInv_reachable` is the global theorem
for the explicitly restricted, well-formed solvency-scoped relation. The
restriction and the post-state `WellFormed` premise are part of the relation;
they are not hidden assumptions. Neither ledger identity is derived from
`WellFormed` or `Solvent`; each is a separately initialized and trace-preserved
relation over the current abstract state machine.

Receipt consistency is now composed without changing the meaning of
`ProtocolInv`: `ProtocolInvWithReceiptLedger` adds
`UnlockTokenLedgerConsistent`, `protocolInvWithReceiptLedger_step` preserves it,
and `protocolInvWithReceiptLedger_reachable` lifts the result over the same
restricted reachability relation. The receipt layer has its own exhaustive
`UnlockTokenLedgerCoveredOp` classification: request/claim operations use their
dedicated lifecycle proofs, vault exits use the `createStandardUnlock` chain,
and every other `Op` must provide a receipt/registry frame. This closes the
model-local receipt identity, but it still does not create a USDC total-supply,
fee-wallet, or on-chain NFT-custody field that is absent from `State`.

## 7. Build the economic property ladder

The properties should be proved in dependency order.

~~~text
action postcondition
        |
        v
ledger conservation
        |
        v
price or conversion bound
        |
        v
solvency / non-depletion
        |
        v
holder-value preservation or lower bound
        |
        v
attack-cost or no-drain bound
~~~

For Apyx, useful branches include:

- solvency: every recorded liability is covered by the modeled assets or reserves;
- holder value: a holder does not lose more than the permitted amount under an allowed action;
- rounding: integer arithmetic stays within the specified error bound;
- price: conversion or redemption values stay within the configured bounds;
- non-depletion: protocol assets cannot fall below the protected liability or reserve floor;
- manipulation resistance: an attacker must pay at least the specified cost to move a price or extract value.

A proof about one routine should not be presented as a proof about the whole protocol. For example, if claimUnlock is not modeled, a theorem about the other routines should be labeled as routine-only or phase-restricted. If behavior changes after a shutdown or winding-down phase, the phase must be part of the state and the theorem must state its phase assumptions.

The current economic ladder is distributed across the following source
families: `solvency_step` and `protocolInv_stepResult_accepted` for conditional
solvency/invariant preservation; `holder_value_*` and `netDelta` in
`HolderValue.lean` for per-holder value; the rounding lemmas named in §5.4;
`pro_rata_floor_underpays_witness` in `SpecDefects.lean` for the fact that a
floor-divided pro-rata payout does not automatically conserve a reserve;
`paid_mint_trace_balance_bound` in `BlastRadius.lean` for the narrower trace
slice in which only paid mint operations occur. It bounds a holder's final
apxUSD balance by its initial balance plus attempted USDC input; unlock claims
and their position ledger now have local request and claim boundary facts in
`Apyx.lean` and `HolderValue.lean`, including the fee-bearing flexible claim.
The mixed-operation full-trace liability ledger remains open. The standard
unlock request-to-claim sublanguage is closed at a fixed rate by
`standardUnlock_holderValueAt_trace_neutral`; the arbitrary-caller fixed-rate
form is `unlockLedger_holderValueAt_trace_nonincreasing_any_callers`. The
remaining work is to compose that ledger with vault exits and live-rate changes
without silently treating price movement as transfer conservation; the
flexible channel is now included in both fixed-rate forms.
The live-rate stable sublanguage is separately closed by
`holderValue_stable_trace_nonincreasing`, with
`holderValue_stable_trace_witness` as a nonempty witness. This is a model
boundary, not a claim that vault exits are harmless at the live rate.
`redemptionValue_frame`, `redemption_price_writers`, and
`admin_alone_moves_redemption_price` for price writers; `reserve_outflow_only_via_redemption`
and the buffer theorems for non-depletion boundaries; and
`rate_limit_linear_bound` plus the attack witnesses in `BlastRadius.lean` for
bounded extraction scenarios. The source statements, rather than theorem
counts, determine whether each result is local, reachable, trace-scoped,
conditional, or a witness.

## 8. Compose the protocol components explicitly

Apyx should be modeled as interacting components rather than as one opaque balance map. The composition boundary should identify at least:

- the vault or reserve;
- the unlock token or claim mechanism;
- the commit token or position mechanism;
- the oracle or price input;
- any RFQ or external settlement path;
- external calls and reentrancy assumptions.

For each component, prove its local invariant. Then prove the composition theorem showing that a permitted cross-component action preserves the combined invariant.

External calls need explicit assumptions. For example:

- which balances can change during the call;
- whether control can re-enter the protocol;
- which return values are trusted;
- whether an oracle value is bounded, fresh, and authenticated;
- whether an RFQ counterparty can fail or return an unexpected amount.

If a composition theorem assumes these facts, record them as assumptions rather than burying them in the proof.

The present source boundary is explicit: the core state and transition are in
`outputs/apyx/Apyx.lean`; registry links are proved in `Registry.lean`; the
finite apxUSD ledger is in `Ledger.lean`; aggregate solvency and holder-value
properties are in `Safety.lean` and `HolderValue.lean`; authority and RFQ
blast-radius claims are in `BlastRadius.lean`; and `Invariant.lean` composes
the registry, solvency, well-formedness, and ledger predicates. The current
model has no Solidity external-call semantics or reentrancy transition, so
those bullets are recorded as out-of-model assumptions rather than silently
treated as proved.

## 9. Separate capability from liveness

Capability properties and progress properties use different proof shapes.

A capability theorem usually has the form:

~~~text
reachable state + allowed caller + action
    -> the caller can change only the permitted fields
    -> the resulting state remains within the security bound
~~~

A liveness theorem usually needs a temporal statement:

~~~text
reachable state + precondition + fairness/time assumptions
    -> eventually an enabled action occurs
    -> eventually the protocol reaches an allowed phase
~~~

Do not infer liveness from a safety invariant. A system can remain safe while permanently refusing a valid withdrawal. Conversely, a progress argument does not show that the value released during progress is correct.

The current Lean source keeps the two families separate. Capability and blast-
radius claims live in `outputs/apyx/BlastRadius.lean`, including `admin_frame`,
`admin_cannot_touch_balances`, `no_role_transfers_user_funds`,
`no_role_burns_user_shares`, and their trace-level counterparts. Time- and
progress-dependent examples live in `outputs/apyx/Apyx.lean` and
`outputs/apyx/BlastRadius.lean`, including
`redemption_cycle_closes_after_cooldown`,
`flexible_fee_schedule_is_reachable`, and `timelock_wrapper_is_live`.
These theorem names are deliberately not presented as unconditional deployed
protocol guarantees: their source statements carry the relevant caller,
state, trace, time, and funding assumptions.

## 10. Keep implementation fidelity at the hand-off boundary

Implementation fidelity does not need to be part of the core Lean model.

The Lean model should prove the abstract design claims that are stable and economically meaningful. The implementation assurance pipeline should then check whether the actual Solidity, generated code, or bytecode realizes the relevant properties.

A property manifest is the connection point:

| Field | Purpose |
| --- | --- |
| property_id | Stable identifier shared by documents and tools |
| specification_anchor | Requirement, invariant, or threat-model location |
| lean_theorem | The abstract theorem or definition |
| implementation_target | Contract, function, storage field, or bytecode path |
| implementation_tool | SPECA, Certora, Halmos, SMT, fuzzing, or other tool |
| result | Proved, disproved, bounded, inconclusive, or not run |
| evidence | Query, trace, counterexample, test, or review record |

SPECA is useful for turning natural-language requirements into typed properties such as invariants, preconditions, postconditions, and assumptions, then checking property reachability and the relevant program subgraph. Its output is an audit aid and a source of candidates for proof; a generated finding still requires human validation.

Implementation tools should be explicit about their scope:

- bounded checking does not prove unbounded behavior;
- fuzzing provides witnesses and regression tests, not an inductive proof;
- SMT or rule-based tools may rely on arithmetic or environment assumptions;
- bytecode checks do not automatically establish that the natural-language specification was modeled correctly.

A complete Lean-to-bytecode refinement proof is worthwhile only when the project needs that assurance level. If it is added, define a representation relation Rep and prove a simulation statement such as:

~~~text
Rep abstractState concreteState
    + abstract step
    + concrete execution
    -> Rep nextAbstractState nextConcreteState
~~~

That theorem needs its own scope, assumptions, and trusted computing base.

## 11. Label theorem status precisely

Every theorem should carry a status tag or an equivalent record. Suggested tags are:

- model-local: about one transition or one component;
- reachable: requires the Reach predicate;
- trace: about a sequence of actions;
- approx: uses a real-valued or bounded approximation;
- threat-model: depends on an explicit attacker or privilege assumption;
- audit: supported by an implementation-analysis result;
- refinement: establishes a representation or simulation relation;
- witness: a counterexample or regression case, not a universal theorem;
- regression: preserves a previously discovered behavior.

The status should appear in the source or generated report so that a reader cannot mistake a local model theorem for a deployed-contract guarantee.

## 12. Suggested file organization

The current Apyx material can be organized around proof responsibilities:

~~~text
outputs/apyx/
  Apyx.lean
  README.md
  SPEC.md
  requirements.json
  model.md
  leancheck.json
  review.json

formalization/
  Safety.lean
  HolderValue.lean
  BlastRadius.lean
  Registry.lean
  Accounting.lean
  Time.lean
  Composition.lean

assurance/
  property-manifest.csv
  speca/
  implementation-checks/
  gaps.md
~~~

The exact directory names are not important. The important distinction is between:

- generated requirement-conformance material;
- reusable design invariants;
- economic and threat-model proofs;
- implementation evidence;
- unresolved assumptions and gaps.

## 13. Recommended implementation order

1. Define State, Action, StepResult, and the clock.
2. Define the representation invariants for balances, supply, reserves, liabilities, and registries.
3. Define Reach and prove initialization plus invariant preservation.
4. Prove the postcondition and revert behavior for each public action.
5. Prove ledger conservation and liability coverage.
6. Add holder-value, solvency, rounding, price, non-depletion, and manipulation-cost properties.
7. Add frame and relational lemmas, then prove cross-component composition.
8. Add capability and liveness properties with explicit attacker, scheduler, and time assumptions.
9. Create the property manifest and connect each property to SPECA and implementation-oriented checks.
10. Treat full refinement to Solidity or bytecode as a separately scoped project.

This order makes it possible to find a broken accounting definition before spending time on an economic theorem that depends on it.

## 14. Completion criteria

The proof map is complete only when the following questions have clear answers:

- Which claims are design-level Lean theorems?
- Which claims are implementation-level checks?
- What is the initial state, and what states are reachable?
- Are both accepted and reverted actions modeled?
- Which accounting identities connect balances, supply, reserves, and liabilities?
- Where do time, phases, rounding, and oracle assumptions enter?
- Which properties are local, global, bounded, approximate, or threat-model dependent?
- Which external calls and privileges are in scope?
- Does every important property have a stable property ID?
- Are SPECA results recorded as audit candidates rather than treated as automatic proofs?
- Is a refinement theorem actually proved, or is the model-to-code connection still a review or tool-assisted obligation?

A missing answer is a visible assurance gap. It should be recorded as such instead of being hidden by a successful build.

## 15. Proof focus: from one actor and action to the global invariant

Starting with an individual balance or one action is usually the clearest way to write the proof. It is a proof-engineering technique, not a restriction on the final theorem.

For one action:

1. fix an arbitrary state, caller, recipient, and amount;
2. unfold the transition and identify the fields that can change;
3. prove the exact delta for the caller, recipient, and protocol-owned accounts;
4. prove a frame theorem for every unaffected account and field;
5. combine those local facts into a ledger or liability equation;
6. lift the equation into a global invariant over the transition;
7. lift transition preservation into Reach or trace theorems.

A typical decomposition looks like this:

~~~lean
theorem deposit_caller_delta :
  step s (.deposit caller amount) = .accepted s' events ->
  balance s' caller = balance s caller + amount := by
  ...

theorem deposit_other_holders_frame :
  step s (.deposit caller amount) = .accepted s' events ->
  holder ≠ caller ->
  balance s' holder = balance s holder := by
  ...

theorem deposit_global_accounting :
  Inv s ->
  step s (.deposit caller amount) = .accepted s' events ->
  Inv s' := by
  ...
~~~

The final theorem should still quantify over arbitrary users, states, and permitted actions. The individual accounts are the coordinates that make the proof tractable.

This focus is especially useful for:

- holder-value guarantees;
- free-credit or unauthorized-balance checks;
- receiver payouts;
- caller authorization;
- frame conditions and blast radius;
- passive-holder protection.

The standard redemption request is one concrete instance of this pattern:
`requestUnlock_backs_claim_by_burn_exact` proves the caller's exact balance
delta and splits the registry postcondition into the fresh-position and
top-up cases. The weaker existential theorem
`requestUnlock_backs_claim_by_burn` remains as a compatibility projection,
but the proof-map claim now points to the exact theorem. The local accounting
identity `requestUnlockStep_pending_conservation` is the next layer: it requires
the same balance guard enforced by the transition and covers both fresh and
top-up requests, including malformed pointer states. It stops at the request
boundary. The complete holder-facing request law is
`requestUnlock_holderValueAt_neutral`: it covers both branches under
`RegistryBounded`, with `requestUnlockStep_effect` and
`stdPositions_updateStandardUnlock` providing the transition and ledger
steps. The matching claim-side layer is now `claimUnlock_holderValueAt_neutral`:
given an in-range position and a successful claim, it proves that the owner loses
the position amount while receiving the same apxUSD amount. A complete
request-to-claim trace now has an inductive fixed-rate theorem,
`standardUnlock_holderValueAt_trace_neutral`, over the standard request/claim
language with explicit waits. It starts from `RegistryWellIndexed`, preserves
that invariant over successful prefixes, and skips reverted calls with the
model's `execTrace` semantics. The fixed-rate frame lemmas and
`unlockLedger_holderValueAt_trace_nonincreasing_any_callers` also cover
operator-mediated claims for another holder. The standard-plus-flexible
fixed-rate trace is now covered by `unlockLedger_holderValueAt_trace_nonincreasing`.
The live-rate stable sublanguage is covered by
`holderValue_stable_trace_nonincreasing`, while the mixed trace
that also includes vault exits still needs a ledger composition theorem and a
live-rate treatment. Flexible claims use the corresponding fee law
`flexibleClaim_holderValueAt_fee`; treating
them as neutral would erase the protocol's explicit early-exit charge.

The global layer is where the protocol-level claims belong:

- solvency;
- total supply and reserve consistency;
- liability coverage;
- non-depletion;
- oracle or price bounds;
- manipulation-cost lower bounds.

The reusable pattern is:

~~~text
local delta
   -> unaffected-state frame
   -> accounting identity
   -> global invariant
   -> reachable-state or trace theorem
~~~

If a counterexample is found, keep the concrete actor, action, and balances as a witness or regression test. For universal safety claims, generalize the proof after the witness has clarified which invariant or frame condition was missing.
