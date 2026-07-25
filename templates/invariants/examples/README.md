# Worked references for the Tier-1.5 and Tier-1-C invariants

[`AsyncQueueVault.lean`](AsyncQueueVault.lean) is a minimal **async redemption vault**: file a
request against a share balance, wait out a maturity window, have a settler execute it at a price
that may have moved. That is the ERC-7540 shape, and the shape LST unstaking queues,
delayed-redemption stablecoins and queued-withdrawal vaults converge on — the DeFi archetypes
`docs/08` §A.6 collects.

The protocol is **fictional** — no real deployment is modelled. Its job is to give the async /
queue / signed-value invariants of [`../README.md`](../README.md) (Step 0b, checklist items g–k) a
compiled reference the way `outputs/apyx/Safety.lean` serves the Tier-1 family.

It compiles as its own lake library, `TemplateExamples` (`lean/TemplateExamples/AsyncQueueVault.lean`
is a symlink to it), kept out of `D2fsSpecs` so that `lake build D2fsSpecs` still compiles exactly the
analyzed systems. `lake build` builds both, so the schema stays regression-tested.

## What it proves

21 theorems:

| Invariant | Theorems | Form |
|---|---|---|
| **I12** in-flight conservation | `inflight_conservation` (exhaustive over `Op`), `tick_settles_exactly`, `partial_tick_leaves_residue` | proved |
| **I10** settlement-timing neutrality | `settle_credits_protocol_favourable_side`, `settler_timing_cannot_gain`, `settlement_never_overpays_current_value` | proved |
| **I10** why the rule is required | `naive_filing_price_overpays_witness` | witness |
| **I10** end-to-end, with the price actually moving | `settlement_takes_lower_price_after_drop` | witness |
| **I11b** queue capacity griefing | `queue_capacity_griefing_witness` | **gap-witness** |
| **I11** head-of-line starvation | `queue_head_of_line_blocking_witness`, backed by `reserve_non_increasing`, `reserve_non_increasing_trace` | **gap-witness** |
| **I15** the `Nat` vacuity trap | `nat_solvency_is_vacuous`, `insolvency_witness` | proved + witness |
| anti-vacuity guard | `settle_is_reachable` | witness |
| **holder view** — settlement has no deadline | `settlement_has_no_deadline`, `matured_request_can_stay_pending_forever`, `tick_preserves_pending` | **gap-witness** |
| **holder view** — first-mover advantage | `fifo_pays_the_first_filer` | **gap-witness** |
| **holder view** — free re-quoting | `cancel_refile_ratchets_the_quote` | **gap-witness** |
| **I11** progress (positive half) | `settle_succeeds_when_head_is_funded` | proved |

Status: `lake build` green, 0 `sorry`, axioms `propext` / `Quot.sound` only (`naive_filing_price_overpays_witness`
and `nat_solvency_is_vacuous` depend on none).

## How the witnesses avoid proving nothing

A witness theorem is only as good as its ability to fail, and three of these were weaker than they
looked before review:

- **A rejection witness must show the rejection has the cause you claim.** `∀ m, enqueue = none`
  holds just as well of a user with no balance, so the capacity witness leads with a control clause:
  the same user's enqueue *succeeds* against a free queue. Only the pair identifies capacity as the
  cause.
- **"Reachable" belongs in the statement, not the docstring.** `insolvency_witness` quantifies over
  an initial state and a trace, so the bad state is visibly produced by `step` rather than
  hand-written as a `State` literal.
- **A rule about prices should be exercised by a price that moves.** `settlement_takes_lower_price_after_drop`
  runs a trace where the price halves between filing and settlement and pins the credit at `500`,
  against the `1000` a filing-quote-only rule would have paid.

`settle_succeeds_when_head_is_funded` is the positive half of I11, and it earns its place next to
the starvation witness: without it the head-of-line result reads as "settlement never works" rather
than "the queue progresses exactly when its head is funded".

`all_healthy_preserved_is_applicable` is the same guard one level up: an invariant with three
hypotheses proves nothing if no reachable configuration satisfies all of them at once, so the file
exhibits one that does. `settle_is_reachable` guards the rest: every I10/I12 theorem is conditioned on a settlement
succeeding, so without it the whole group could be quietly vacuous. Instantiations should carry the
same guard for each guarded op they reason about — it is cheap, and it is exactly the failure the
round-trip judge cannot see.

## What a large holder reads differently

The safety invariants above are written from the protocol's seat, and two properties that decide a
large holder's behaviour are invisible from there.

**I10 protects the protocol only if settlement happens.** `Op.settle` carries a lower bound on time
— the maturity window — and no upper bound: nothing ever compels a matured request to be executed.
A settler who waits therefore holds an option with no expiry, and since the payout is the *minimum*
of the filing and settlement prices, every round of delay in a falling market is paid for by the
holder. `settlement_has_no_deadline` proves the delay is unbounded; the protective rounding and the
missing deadline are one design decision seen from two sides. Fix: a deadline after which the
request settles at the filing quote, or becomes cancellable.

**The missing bounds point both ways.** `Op.settle` has no deadline, which is an option the settler
holds against the filer. `Op.cancel` has no time constraint either, which is the same omission
mirrored: because the payout is `min(filing quote, settlement price)`, a *higher* filing quote can
only help the filer, so cancel-and-refile lets them ratchet up to the best price seen since they
entered, for free. `cancel_refile_ratchets_the_quote` doubles a payout that way, and the extra comes
straight out of the reserve — that is, out of everyone still queued behind them. A design that
closes only the bound that hurts the protocol has picked a side rather than fixed the asymmetry.

**The reserve is never split.** `fifo_pays_the_first_filer` exhibits two holders filing identical
requests against a reserve covering exactly one: the first is paid in full, the second gets nothing,
and swapping the filing order swaps the outcome. No invariant is violated — which is the point. A
holder reading only the safety proofs would not learn that the rational response to a thin reserve
is to run first. Fix: pro-rata settlement across matured requests, or an explicit statement that
service is first-come-first-served so the incentive is at least disclosed.

## The two transferable lessons

1. **Make delivery an argument to the clock op.** `Op.tick (delivered : Nat)` rather than a `tick`
   that empties the in-flight bucket by fiat. Conservation then holds *unconditionally*
   (`inflight_conservation` covers partial ticks), and only the "in-flight drops to zero" half
   carries the settlement-honesty hypothesis (`tick_settles_exactly`) — with
   `partial_tick_leaves_residue` proving that hypothesis is load-bearing. A model that hard-wires
   full delivery has assumed away the failure it should be exposing.

2. **`Nat` ledgers report insolvency as solvency.** `nat_solvency_is_vacuous` is true by typing;
   `insolvency_witness` exhibits a reachable state where the signed reading is `-999` and the
   unsigned reading is `0`. Decide this at Step 0b, before any invariant is written.

## What it does NOT cover

I13 (cross-venue conservation) and I14 (intent-vs-realized drift) are schema only in
`../Invariants.template.lean` — no worked reference exists. Do not cite them as covered.

Nothing here is evidence about any real protocol. It is evidence that the *schema* is coherent and
that its two subtle points are real.

---

# `CollateralizedDebt.lean` — the per-account solvency family (Tier 1-C)

A minimal **collateralized debt protocol**: positions with collateral and debt, a liquidation
threshold, interest accrual, and a redemption mechanism that buys collateral out of positions in an
advertised priority order. The shape shared by CDP stablecoins and borrow/lend markets, where the
safety property is **per-account** health rather than pooled solvency. Fictional, as above.

It has **no counterparty ledger** — the debt token is not modelled, so a liquidator's repayment and
a redeemer's payment are not represented, only their effect on the position book and the collateral
leaving it. Every theorem here is a statement about the book, and no conservation claim is made.

37 theorems:

| Invariant | Theorems | Form |
|---|---|---|
| **I16** health on every path | `all_healthy_preserved` (book-wide, exhaustive over `Op`), `redeem_preserves_health` | proved |
| — supporting | `healthy_add_coll`, `healthy_sub_debt`, `price_ratio_stable`, `mem_updatePos`, `mem_dropPos`, `mem_insertPos` | proved |
| **I17** liquidation reduces risk | `liquidate_requires_unhealthy`, `liquidation_seizure_bounded` | proved |
| **I17c** liquidation is worth doing | `liquidation_unprofitable_witness` | **gap-witness** |
| **I22** bad debt accounted | `liquidation_accounts_shortfall`, `bad_debt_only_from_liquidation`, `unprofitable_liquidation_books_bad_debt` | proved + witness |
| **I18** priority-order integrity | `sorted_preserved` (book-wide, exhaustive over `Op`), `redeem_hits_head_only`, `insertPos_sorted` | proved |
| — supporting | `sorted_head_le`, `sorted_tail`, `sorted_cons_of_bound`, `sorted_dropPos`, `sorted_updatePos`, `sorted_updateConst`, `sorted_map`, `mem_updateConst`, `lookupPos_mem` | proved |
| **I19** accrual monotone | `index_monotone`, `accrual_never_lowers_debt` | proved |
| **I4** rounding, load-bearing here | `le_ceilDiv_one_mul` | proved |
| **I21** immutable parameter | `min_ratio_immutable`, `penalty_immutable` | proved |
| anti-vacuity | `all_healthy_preserved_is_applicable`, `liquidation_is_reachable`, `redemption_is_reachable`, `healthy_position_cannot_be_liquidated` | witnesses + control |

## The five transferable lessons

1. **State the health invariant book-wide, not per touched position.** A guard lemma proves the op
   you looked at is safe; the Euler defect is always in the op you did not look at.
   `all_healthy_preserved` is `AllHealthy s → AllHealthy s'` by `cases op`, so a debt-increasing
   operation that skipped its check would fail to compile. The price of stating it properly is three
   list-membership lemmas and two monotonicity lemmas — budget for them, they are mechanical.

   Excluding ops is not cheating *if you name them*. `accrue` and `setPrice` are excluded because
   they are supposed to be able to make a position liquidatable, and `accrual_never_lowers_debt`
   proves which direction they move it in.

2. **Give every operation its counterparty side, or the invariant is measuring nothing.** The first
   draft of this file had a redemption that reduced debt and took no collateral — a free write-off.
   Every theorem still compiled, because none of them was false; they were just about an operation
   no protocol would ship. Redemption now exchanges collateral for debt, and that turns
   `redeem_preserves_health` from bookkeeping into the one genuinely interesting case of I16:
   removing backing is safe **only** because the debt reduction rounds up (I4) and the protocol
   over-collateralizes. Round it down and a redeemer walks a healthy position into liquidation.

3. **A lemma about a list helper is not an invariant of the system.** The first version of I18
   proved `insertPos_sorted` and stopped — order-preservation of the *insert function*. Nothing in
   it prevents a different op from scrambling the book, and `Sorted` appeared nowhere else in the
   file: it was never connected to `step` at all. `sorted_preserved` carries it across every op,
   which is what makes "the advertised order is enforced" a claim about the protocol. Same shape as
   lesson 1, same cost: a head-bound lemma plus one preservation lemma per list operation.

4. **Safety invariants do not notice a protocol losing money.** Everything else in this file can
   hold while bad debt piles up, because safety says which operations are forbidden and nothing
   about which ones anyone will perform. Two gaps a DeFi reviewer finds immediately and no
   safety-only invariant catches: a liquidation that recovers less than the debt is never performed
   (`liquidation_unprofitable_witness` — permitted, reachable, and economically irrational), and a
   position dropped from the book takes its uncovered debt with it unless something books the
   shortfall (I22). The first version of this file did exactly that silent write-off and every
   theorem still passed.

5. **Prove immutability, do not assert it.** `min_ratio_immutable` is one tactic block and turns a
   deployment comment into a theorem that a later-added setter would break. This is the dual of the
   pattern-G gap-witness and it is the cheapest useful theorem in the whole template.

## What it does NOT cover

I20 (socialized-loss pool conservation) is schema only, and deliberately so. Note what that costs:
`badDebt` records *how much* was not recovered, and nothing here says **who bears it**. That is the
question a large holder asks first, and this model cannot answer it — the loss has to land on a
backstop, on remaining holders pro-rata, or on a reserve, and none of those exist here. Instantiating
I20 means modelling that party explicitly; until then, do not let a reader infer that a booked
shortfall is a contained one. Concretely: repayment and
liquidation move debt out of the book without a matching counterparty ledger in this model, so any
conservation claim stated here would be about a half-drawn system. A faithful I20 needs the other
side modelled. Do not cite it as covered.
