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

15 theorems:

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

`settle_is_reachable` guards the rest: every I10/I12 theorem is conditioned on a settlement
succeeding, so without it the whole group could be quietly vacuous. Instantiations should carry the
same guard for each guarded op they reason about — it is cheap, and it is exactly the failure the
round-trip judge cannot see.

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
threshold, interest accrual, and a redemption mechanism with an advertised priority order. The shape
shared by CDP stablecoins and borrow/lend markets, where the safety property is **per-account**
health rather than pooled solvency. Fictional, as above.

19 theorems:

| Invariant | Theorems | Form |
|---|---|---|
| **I16** health on every path | `all_healthy_preserved` (book-wide, exhaustive over `Op`), `borrow_requires_health`, `withdraw_requires_health` | proved |
| — its supporting lemmas | `healthy_add_coll`, `healthy_sub_debt`, `price_index_stable`, `mem_updatePos`, `mem_dropPos`, `mem_insertPos` | proved |
| **I17** liquidation reduces risk | `liquidate_requires_unhealthy`, `liquidation_seizure_bounded` | proved |
| **I18** priority-order integrity | `redeem_hits_head_only`, `insertPos_sorted` | proved |
| **I19** accrual monotone | `index_monotone`, `accrual_never_improves_health` | proved |
| **I21** immutable parameter | `min_ratio_immutable`, `penalty_immutable` | proved |
| anti-vacuity | `liquidation_is_reachable`, `healthy_position_cannot_be_liquidated` | witness + control |

## The two transferable lessons

1. **State the health invariant book-wide, not per touched position.** A guard lemma proves the op
   you looked at is safe; the Euler defect is always in the op you did not look at.
   `all_healthy_preserved` is `AllHealthy s → AllHealthy s'` by `cases op`, so a debt-increasing
   operation that skipped its check would fail to compile. The price of stating it properly is three
   list-membership lemmas and two monotonicity lemmas — budget for them, they are mechanical.

   Excluding ops is not cheating *if you name them*. `accrue` and `setPrice` are excluded because
   they are supposed to be able to make a position liquidatable, and
   `accrual_never_improves_health` proves which direction they move it in.

2. **Prove immutability, do not assert it.** `min_ratio_immutable` is one tactic block and turns a
   deployment comment into a theorem that a later-added setter would break. This is the dual of the
   pattern-G gap-witness and it is the cheapest useful theorem in the whole template.

## What it does NOT cover

I20 (socialized-loss pool conservation) is schema only, and deliberately so: repayment and
liquidation move debt out of the book without a matching counterparty ledger in this model, so any
conservation claim stated here would be about a half-drawn system. A faithful I20 needs the other
side modelled. Do not cite it as covered.
