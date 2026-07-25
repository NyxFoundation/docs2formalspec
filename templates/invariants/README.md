# Design-safety invariant template

A reusable, app-agnostic recipe for the **core design-safety invariants** that catch the majority of
real DeFi design-level losses (see [`docs/08-defi-vuln-patterns.md`](../../docs/08-defi-vuln-patterns.md)
Part B) — for *any* protocol modeled in this tool's style: a `State` record, a closed `inductive Op`, and
`step : State → Op → Address → Option State`.

This directory holds the **generic template** only. Instantiated, app-specific proofs live in that app's
output directory (e.g. `outputs/apyx/Safety.lean`), never in `lean/`.

[`examples/AsyncQueueVault.lean`](examples/AsyncQueueVault.lean) — a *fictional* protocol, not an
analyzed app — is the one file here that compiles, because a reference nobody can check is worth
little. It lives in its **own lake library**, `TemplateExamples`, symlinked from
`lean/TemplateExamples/`, deliberately *not* inside `D2fsSpecs`:

- `lake build D2fsSpecs` → exactly the analyzed systems (what an audit report tells its reader to run)
- `lake build` → those plus this example, so the template keeps a regression test

## Why these invariants, and why this shape

Part A of `docs/08` ranks the loss patterns; four invariants, proved over the **closed `Op` type by
exhaustive case analysis**, cover the bulk of them across Lending / Vault / AMM / Stablecoin protocols:

| Invariant | Catches (docs/08 pattern) | Apyx worked reference |
|---|---|---|
| **I1 Conservation / no-free-value** | D (accounting), A/E (partial) | `no_free_value_trace`, `apxUSD_credit_is_backed` |
| **I2 Solvency** | **E** (missing solvency check — the #1 design flaw), D | `solvency_preserved` |
| **I3 No-dilution / share-value monotone** | **B** (inflation/donation), Vault | `no_dilution` |
| **I4 Rounding favors the protocol** | **C** (rounding leak) | `rounding_favors_protocol`, `withdrawShares_rounds_up` |
| **I5 Donation-immunity** | **B** (the root of inflation attacks) | `donation_free`, `no_inflation_attack` |
| **G Parameter-bound gap-witness** | **G** (unbounded params) | `redeem_payout_has_no_cap`, `admin_rfq_coalition_drains` |

Those five assume an **atomic, single-venue, non-negative-valued** transition system. When the app
breaks that assumption — two-phase (request/settle) operations, a shared bounded queue, value
spread across venues with transfer latency, or a net position that can go negative — a second
family applies (`docs/06` §7, `docs/08` §A.6/§B.2 Tier 1.5). Step 0 below decides which of these
are even stateable for your app:

| Invariant | Catches (docs/08 pattern) | Worked reference |
|---|---|---|
| **I10 Settlement-timing neutrality** | **J** (timing option for the settler) | [`examples/AsyncQueueVault.lean`](examples/AsyncQueueVault.lean) |
| **I11 Queue liveness / capacity griefing** | **K** (starvation, occupancy DoS) | same (gap-witness form) |
| **I12 In-flight conservation** | D, async accounting | same |
| **I13 Cross-venue conservation** | D across venues | *schema only — no worked reference yet* |
| **I14 Intent-vs-realized drift bound** | **L** | *schema only — no worked reference yet* |
| **I15 Signed net value** | E with liabilities; the `Nat` vacuity trap | [`examples/AsyncQueueVault.lean`](examples/AsyncQueueVault.lean) |

**The structural advantage.** Because `step` is total over a *closed* `Op`, proving `Inv s → Inv s'` for
every op is a `cases op` whose branches must *all* discharge before the file compiles. So "no operation
violates the invariant" is a **theorem, not a sample** — this is what structurally eliminates the
single highest-loss pattern (Euler's `donateToReserves`: the invariant held on every path *but one*).
Bytecode fuzzers/symbolic tools *search* for a violating path; here you *prove* none exists.

As with `templates/blast-radius/`, Lean's lack of row-polymorphism over records makes a fully generic
library more obscure than a filled-in copy, so the reusable asset is a **skeleton + checklist**:
[`Invariants.template.lean`](Invariants.template.lean) is the structure with `‹PLACEHOLDER›` markers; this
README is the fill-in guide; `outputs/apyx/Safety.lean` is the worked reference — read it alongside.

## Step 0 — model profile (fill in from the app's `State`/`Op`/`step`)

| Question | Apyx answer (example) |
|---|---|
| **Value fields** — user-owned balances priced in a common unit | `apxUSDBal` (1:1 USD), `apyUSDBal` (×`exchangeRate`), `usdcBal`; measure via `valueAt R s a` |
| **Backing / reserve fields** — what stands behind the claims | `totalCollateralValue`, `usdcReserve`, `vaultApxUSDBal`, `vestedAmount` |
| **Claims aggregate** — the total obligation to bound | `totalSupply_apxUSD` (+ margin), `totalSupply_apyUSD`·rate |
| **Accounted-mint ops** — the *only* ops allowed to raise pooled assets/shares | `lockApxUSD` (share mint), `depositUSDC`; privileged `creditYield` |
| **Raw-transfer primitive?** — is there any op that injects assets *without* a matching share mint? | **none** — the crux for donation-immunity (I5) |
| **Conversion functions** — asset↔share, their rounding direction | `lockShares` (floor), `redeemAssets` (floor), `withdrawShares` (ceil) |
| **Bounded params** — which economic params carry enforced floors/caps in `step` guards | `setYieldRate` bounded by `collateralYieldBase`; **`redemptionValue` has NO lower floor** → gap |

The last two rows decide which invariants are *provably true* (accounted-mint-only ⇒ I5 holds) and which
become **gap-witnesses** (an unbounded param ⇒ prove a bad state is reachable, §Step 2f).

### Step 0b — is this app synchronous? (five questions that gate I10–I15)

Answer these from `Op`/`State` before writing a line of Lean. A single **yes** means the Tier-1
invariants alone will pass while leaving most of the attack surface unexamined.

| Question | If yes | Model extension needed |
|---|---|---|
| **Clock** — does any op advance a block / settlement-round counter? | I10–I12 become stateable at all. If **no**, every trace is same-instant and async properties cannot even be *written* | **E1**: add `Op.tick` |
| **Two-phase ops** — is any user operation split into `request` then `settle`, executed by a different caller? | The settler holds a free timing option ⇒ **I10** | **E2**: `Request` with a price snapshot |
| **In-flight state** — is there state meaning "sent but not yet acknowledged"? | Conservation must count it ⇒ **I12**. Make delivery an *argument*, never hard-wire full delivery | **E1** + explicit `delivered` |
| **Signed value** — can any tracked net position go negative? | A `Nat` ledger makes the solvency claim **vacuously true** ⇒ **I15** | **E3**: `Int` ledger |
| **Shared bounded queue** — do ops compete for a capacity-limited resource? | Starvation / occupancy ⇒ **I11**, gap-witness by default | **E4**: `pending : List Request` + capacity |

> **The `Nat` trap is the one to internalize.** If net value can go negative and the ledger is
> `Nat`, then `0 ≤ netValue` is true *by typing* and proves nothing about the protocol. The worked
> reference makes this concrete: `nat_solvency_is_vacuous` (true for free) alongside
> `insolvency_witness` (a reachable state the unsigned reading reports as solvent). Catch this at
> Step 0 — it is far more expensive to discover after the invariants are written.

## Step 1 — infrastructure (copy near-verbatim)

- `execTrace : State → List (Op × Address) → State` — revert-skip trace executor (identical across apps;
  shared with the blast-radius template).
- A **value measure** `valueAt (R : Nat) (s : State) (a : Address) : Nat` — the sum of `a`'s value fields
  priced at a reference rate `R` (Apyx: `apxUSDBal + redeemAssets(apyUSDBal, R) + usdcBal`).
- A **solvency predicate** `Solvent s : Prop` — `claims s ≤ backing s`.
- A **well-formedness predicate** `WellFormed s : Prop` — the ledger side-conditions the single-step lemma
  needs and the aggregate model can't re-derive (re-supplied per trace-prefix; see I2). Be honest about it.

## Step 2 — the invariant checklist

Each invariant is proved in two stages: **(a)** single-step, *exhaustive over `Op`*; **(b)** trace-level by
induction. Exclude ops honestly (name them) when an invariant legitimately does not apply (e.g. settlement
ops that re-mint against an untracked obligation) — and document why, as `solvency_preserved` does.

**a. I1 Conservation / no-free-value.** No address ends with value it did not pay for.
- Single: define `Penniless a s` (a holds nothing extractable); prove each op preserves it unless the op is
  a *paid* gift to `a`. Trace: induct, giving a no-gift hypothesis on the trace.
- Recipe: `cases op`; the credit ops must show every increase is backed by a burn/payment.

**b. I2 Solvency.** `claims ≤ backing` on every step and every trace.
- Single: `Solvent s → WellFormed s → (op ∉ excluded) → Solvent s'`, by `cases op`.
- Trace: `(∀ n, WellFormed (execTrace s (σ.take n))) → (excluded ∉ σ) → Solvent (execTrace s σ)`.
- **This is the one that closes Euler-class flaws**: the `cases op` forces *every* balance-mutating op to
  re-establish solvency; a path that "forgets" the check cannot compile.

**c. I3 No-dilution / share-value monotone.** No operation lowers a bystander's redeemable per-share value.
- Single: for a holder `a` not transacting, `redeemableValue s' a ≥ redeemableValue s a`.
- The honest scope note: at a *live* (moving) rate this interacts with yield; Apyx proves the single-op and
  fixed-rate trace form (`no_dilution`, `caller_net_nonpositive_trace`) and flags the live-rate closure open.

**d. I4 Rounding favors the protocol.** Every conversion round-trip credits ≤ input; withdrawals round up.
- `convertToAssets (convertToShares a) ≤ a` and the dual; `withdrawShares` rounds up. Pure `Nat` div lemmas.

**e. I5 Donation-immunity.** Pooled assets/shares move only through accounted ops.
- Prove `totalAssets`/`vaultBal` increases are matched 1:1 by a share mint (Apyx `donation_free`), and hence
  the ERC4626 inflation attack is structurally impossible (`no_inflation_attack`). If the app *does* have a
  raw-transfer primitive, this becomes a **finding**, not a theorem.

**f. G Parameter-bound gap-witness.** For each economically-sensitive param with no enforced floor/cap:
- Prove the **absence** as a reachable bad state: `∃ s σ, reachable ∧ BadState (execTrace s σ)`
  (Apyx `redeem_payout_has_no_cap`: no upper bound; `admin_rfq_coalition_drains`: floor 0 ⇒ total loss).
- This turns "we couldn't prove safety" into a **machine-checked vulnerability**, the asymmetric strength of
  this method. Report it with the recommended fix (a floor/cap/rate-limit).

**g. I10 Settlement-timing neutrality.** *(only if Step 0b says two-phase)* The payout of a request
settled at round `n` must not exceed the entitlement at the filing quote **nor** the entitlement at
the settlement-time price — i.e. the rule takes the protocol-favourable side of the two.
- Prove the step-level credit equals `min` of the two readings, then the two `≤` corollaries fall out.
- Also witness the **contrast**: honouring the filing quote alone overpays whenever the price fell.
  That single witness is what makes the `min` a requirement rather than a preference.

**h. I11 Queue liveness / capacity griefing.** *(only if Step 0b says bounded queue)* Default to the
**gap-witness** form; the positive form is rarely true of a real queue. Two distinct mechanisms —
witness both, they need different fixes:
- *Capacity occupancy*: a reachable state where **every** honest enqueue is rejected. Pair it with a
  control clause showing the same enqueue succeeds against a free queue, or the witness does not
  identify capacity as the cause. Then show zero cost: the attacker's cancel-then-refile cycle
  returns him to his starting holdings with the queue just as full — cost-free recyclability is what
  turns a capacity bound into a DoS.
- *Head-of-line starvation*: an unsettleable head freezes everything behind it. The witness is
  strongest when it shows a queued request that the reserve **could** cover and still cannot settle,
  plus a monotonicity lemma (the reserve never grows) proving the block cannot resolve itself.
- If the design *does* guarantee progress, prove `∀ pending r, ∃ τ, Claimed (execTrace s τ) r`.

**i. I12 In-flight conservation.** *(only if Step 0b says in-flight state)*
- `settled + inflight` is preserved by every non-accounted op — `cases op`, exhaustive.
- **Model the delivered amount as an argument to the clock op.** Then conservation holds
  unconditionally and only "in-flight drops to zero" needs the honesty hypothesis. Prove both halves
  and a residue lemma showing the hypothesis is load-bearing. Hard-wiring full delivery into `step`
  assumes the settlement layer's correctness instead of recording it — the single most common way
  an async model quietly lies.

**j. I15 Signed net value.** *(only if Step 0b says signed)* Move the ledger to `Int` **first**, then
either prove `0 ≤ netValue` over traces or witness a reachable negative. Keep the vacuity pair in the
output so a reviewer can see why the unsigned reading was rejected.

**k. I13 / I14** — cross-venue conservation and intent-vs-realized drift are **schema only**: no
worked reference exists yet. I13 needs an explicit in-transit bucket so `Σ(venues) + in-transit` is
preserved by internal moves; I14 follows the pattern-G recipe exactly (bound it, or witness that no
bound exists). Do not report either as covered until instantiated.

## Step 3 — reporting

Tag each theorem by provenance in `review.json` so the audit is traceable:
**requirement-derived** (`model ⊨ requirement`) · **threat-model** (blast-radius) · **design-invariant**
(this template — proved *or* gap-witnessed) · **spec-consistency** ([`docs/07`](../../docs/07-spec-defects.md)).
Always run the **corpus → Solidity source-tracing** of `docs/07` §3.0 so an extraction defect (D6) is never
reported as a protocol design flaw.

## Coverage

This template + the blast-radius template + the `docs/07` spec-consistency layer together address the six
highest-value invariants of `docs/08` §A.5. See the pattern→guarantee matrix in `docs/08` §B.4.

**Honest status of the second family.** I10/I11/I12/I15 are proved in
[`examples/AsyncQueueVault.lean`](examples/AsyncQueueVault.lean) — a *fictional* minimal protocol,
not a real one. That file compiles as part of `lake build` (`sorry`-free, axioms `propext`/`Quot.sound`
only) and doubles as the template's regression test, but it is **not** the same class of evidence as
`outputs/apyx/Safety.lean`: no real protocol has been instantiated against I10–I15 yet, and I13/I14
have no reference at all. Say so in any audit that cites them.
