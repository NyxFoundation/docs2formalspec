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

## 5. Establish representation invariants before economic theorems

Economic properties are only meaningful when the state representation is well formed. The initial invariant should cover at least the following.

### 5.1 Ledger consistency

State what balances, total supply, reserves, and liabilities mean. Then prove the relationships between them.

Typical examples:

- the sum of tracked balances agrees with total supply, modulo explicitly modeled rounding;
- a mint or burn changes supply and balances by matching amounts;
- an outgoing transfer cannot exceed the available balance;
- the reserve and liability ledgers use the same units and asset domains.

### 5.2 Registry consistency

For pending requests, positions, or claims, specify:

- ownership;
- amounts;
- timestamps or deadlines;
- status flags;
- links or array indices;
- uniqueness and bounds.

Every action that creates, consumes, or updates a registry entry must preserve these relationships.

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

These are relational lemmas rather than a state-only `ClockConsistent`
predicate. That is intentional: the clock is a property of a transition
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

## 6. Define reachability and prove an inductive invariant

A safety theorem should apply to reachable states, not just to arbitrary states that happen to satisfy an invariant.

A minimal shape is:

~~~lean
def Inv (s : State) : Prop :=
  LedgerConsistent s ∧
  RegistryConsistent s ∧
  ClockConsistent s ∧
  NumericBounds s

inductive Reach : State → Prop
  | initial : Reach initialState
  | step :
      Reach s ->
      Allowed action s ->
      step s action = .accepted s' events ->
      Reach s'

theorem inv_step :
  Inv s ->
  Allowed action s ->
  step s action = .accepted s' events ->
  Inv s'

theorem inv_reachable :
  Reach s -> Inv s
~~~

The exact syntax can change, but the logical obligations must remain visible:

1. the initial state satisfies Inv;
2. every allowed successful transition preserves Inv;
3. Reach is built using the same transition restrictions used by the preservation theorem.

If inv_step only covers a SafeAction subtype while Reach permits every Action, the final theorem has a gap. Either make Reach use the same restriction or prove that every reachable successful action satisfies the required safety condition.

The invariant should be factored into small lemmas. A single giant invariant theorem is difficult to review and tends to hide which accounting relationship actually carries the argument.

In the current source, `ProtocolInv` combines `RegistryWellIndexed`, `Solvent`,
`WellFormed`, and `ApxUSDLedgerConsistent`. `protocolInv_default` proves the
base case, `protocolInv_stepResult_accepted` proves preservation at the
accepted-result boundary, and `ProtocolReach` uses that same accepted
`StepResult` relation. `protocolInv_reachable` is therefore the global theorem
for the explicitly restricted, well-formed solvency-scoped relation. The
restriction and the post-state `WellFormed` premise are part of the relation;
they are not hidden assumptions.

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
