# Blast-radius theorem template

A reusable, app-agnostic recipe for producing the **key-compromise blast-radius** theorem family
(T1–T10 of [`docs/05-blast-radius.md`](../../docs/05-blast-radius.md)) for *any* protocol modeled in this
tool's style — a `State` record, a closed `inductive Op`, and a `step : State → Op → Address → Option State`
transition function.

This directory holds the **generic template** only. The instantiated, app-specific proofs live in that
app's output directory (e.g. `outputs/apyx/BlastRadius.lean`), never in `lean/` — the core stays generic.

## Why a template rather than a library

The blast-radius theorems are structurally identical across protocols but reference each protocol's own
field names and operation cases (e.g. `apxUSDBal`, `Op.redeemApxUSD`). Lean's lack of first-class
row-polymorphism over records means a fully generic library would be more obscure than a filled-in copy.
So the reusable asset is a **skeleton + checklist**: [`BlastRadius.template.lean`](BlastRadius.template.lean)
gives the exact structure with `‹PLACEHOLDER›` markers; this README is the fill-in guide. (The Apyx
instantiation at `outputs/apyx/BlastRadius.lean` is the worked reference — read it alongside the skeleton.)

## Step 0 — classify the model (fill in the app profile)

Before writing any theorem, answer these from the app's `State`/`Op`/`step`:

| Question | Apyx answer (example) |
|---|---|
| **Value fields** — which `State` fields represent user-owned value? | `apxUSDBal`, `apyUSDBal`, `usdcBal`, `governanceTokenBal`; pooled: `vaultApxUSDBal`, `usdcReserve`, `vestTotal` |
| **Role addresses** — which `State` fields name privileged callers? | `admin`, `oracle`, `pauseController`, `yieldDistributor`, `governance` |
| **Role-gated ops** — which `Op` cases does `step` gate on `caller = <role>`? | pause/unpause→pauser; creditYield→distributor; whitelist/denylist/rate/vest/stress/backstop→admin; oracle price ops→oracle |
| **Debit sites** — for each value field, which `step` cases *decrease* it, and for whom? | apxUSD debited in lock/requestUnlock/flexRequest/redeem (caller) + executeRFQRedemption (a non-caller victim) |
| **Reserve outflow sites** — which ops decrease the protocol reserve, and at what price? | usdcReserve decreases only in redeemApxUSD/executeRFQRedemption, at `redemptionValue` |
| **Price/param writers** — which ops set redemption/exchange/market-price params, gated on whom? | redemptionValue only via admin `catastrophicBackstop` (no clamp); marketPrice via oracle |
| **Instant vs delayed** — do privileged ops take effect in the same `step`? | yes, all instant (→ base_model_has_no_timelock is provably true; T8 needs a wrapper) |

The debit-sites and reserve-outflow answers are the crux: they determine which theorems are *provably
true of the base model* and which require a defense wrapper.

## Step 1 — infrastructure (copy near-verbatim)

- `execTrace : State → List (Op × Address) → State` — run a trace, revert-skip (`none` leaves state
  unchanged). Identical for every app.
- Role predicates `‹Role›Op (op : Op) : Prop` — one per role, listing that role's gated `Op` cases.
- Local step-inversion lemmas `inv_‹op›` — re-derive per op (the base model's helpers are usually
  `private`; don't un-private them, re-derive in the app's BlastRadius module).

## Step 2 — the theorem checklist (per tier)

**Base-model theorems** (properties of the actual protocol — the valuable ones):

- **T1–T3 per role**: `‹role›_frame` (a successful role-gated op equals the pre-state with only its named
  non-value fields overridden) + `‹role›_trace_blast_radius` (lift by induction: an all-‹role› trace moves
  only those fields). Proof pattern: exhaustive `cases op`, each non-role op is a revert/contradiction.
- **T4 non-custodial**: `no_role_debits_‹valuefield›` for each value field (if `a`'s field decreased in one
  step, `a` was the caller — modulo documented carve-outs like an RFQ victim), then the trace headline
  `user_assets_immune_to_total_key_compromise` (a passive non-signer loses nothing over any trace).
- **T5 no-theft ledger**: define `netHoldings s a := Σ a's value fields`; prove non-decreasing over any
  trace for a victim who never signs and is never a debit-site's non-caller target.
- **T6 role blast radius**: `‹role›_alone_preserves_balances` (the role alone extracts zero). If the model
  has an *uncapped* price/param an op can set, add the honest **no-cap finding**: `‹payout›_formula` +
  `‹payout›_has_no_cap` (exhibit a witness param value making payout exceed any N) — this is the finding
  that motivates the wrappers, not a safety claim.
- **Active no-extraction**: `‹token›_credit_is_backed` — every `step` case that credits a value field is
  backed by an equal payment or the settlement of the recipient's own pre-existing position (no free mint).
- **T9 compartmentalization**: `‹role›_compartmentalized` — projection of the T1–T3 trace theorem showing
  the footprint is confined to one subsystem.
- **T10 coalition**: `single_key_bounds` (recap: no single role extracts principal) + the quantitative
  worst-coalition theorem (`‹coalition›_drains`) exhibiting the concrete total-loss trace, if one exists.
- **base_model_has_no_‹defense›**: if the base model lacks a defense, *prove its absence* (e.g. an admin op
  takes effect in the same step ⇒ no escape window). A negative result is a real finding.

**Design theorems** (what a *missing* defense would guarantee — recommendations, not current properties):

- **T7 rate limit**: define a wrapper `structure RLState where base : State; epoch; spentThisEpoch; cap`
  and `step2`/`execTrace2` charging reserve outflow (gate hook = the reserve-outflow characterization
  lemma), reverting over `cap`. Prove `rate_limit_linear_bound`: cumulative outflow `≤ cap × (epochs+1)`.
- **T8 timelock**: wrapper `structure TLState where base : State; now; pending; delay` with
  queue/tick/execute ops; prove `timelock_escape_guarantee` (a queued op can't take effect until `delay`
  ticks after queuing). Mark clearly as a design theorem — the base model (per Step 0) has no such delay.

## Step 3 — honesty requirements (enforced by the tool's conventions)

- No `sorry`, no vacuous (`: True`) theorems. `#print axioms` on every public theorem must show only
  Lean's trusted axioms (`propext`/`Quot.sound`, and `Classical.choice` is acceptable — all three are
  standard; `sorryAx`/`native_decide` are not).
- Every theorem's docstring states (a) the threat scenario and (b) exactly what is/ isn't claimed, including
  any carve-out (e.g. a non-caller debit site).
- **Crisply separate base-model theorems from design (wrapper) theorems** in both docstrings and the
  app's audit report. Conflating "the protocol guarantees X" with "a wrapper we sketched would guarantee X"
  is the one mistake this template exists to prevent.

## Relation to the requirement-driven pipeline

The main `d2fs` pipeline formalizes what the *docs say* (requirement-traceable theorems). Documentation
never says what an attacker *can't* do under key compromise, so this template is the **second property
source** the memo's §6 describes: threat-model-driven theorems with no requirement of origin. When the
pipeline eventually auto-instantiates this (identifying role fields / debit sites from a generated model),
its output should tag blast-radius theorems distinctly from requirement theorems in `review.json`.
