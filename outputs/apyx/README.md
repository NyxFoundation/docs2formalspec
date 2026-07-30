# Apyx Protocol — Formal Verification Report

| | |
|---|---|
| **Subject** | Apyx (apyx.fi) — the apxUSD / apyUSD dividend-backed stablecoin protocol |
| **Contracts** (Ethereum mainnet, per the ingested documentation) | apxUSD [`0x98A8…4665`](https://etherscan.io/address/0x98A878b1Cd98131B271883B390f68D2c90674665) · apyUSD [`0x38EE…8a6A`](https://etherscan.io/address/0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A) · UnlockToken [`0x9377…BF4e6`](https://etherscan.io/address/0x93775E2dFa4e716c361A1f53F212c7AE031BF4e6) |
| **Method** | RFC 2119 specification → Lean 4 state-machine model → machine-checked theorems |
| **Result** | 0 `sorry`, kernel-verified (`lake build D2fsSpecs`, Lean 4.31.0). No internal *contradiction* was found in Apyx's specification. The analysis machine-proved concrete design weaknesses — a single-key (`ADMIN_ROLE`) reserve-drain and unbounded repricing path, and the absence of a redemption-price floor (§4.1, §5, §9.1) — and, in a self-review of this report's own model, found and fixed four defects in the **formalization** (§9.3). |
| **Date** | 2026-07-07, revised 2026-07-30 (§9.3) |
| **Self-review** | This report has been reviewed against its own Lean source; findings and fixes are in [`code_review_lean.md`](code_review_lean.md) and §9.3. Regression tests: [`review_witnesses/`](review_witnesses/). Deployment reads that ground the fixes: [`deployment_ground_truth.md`](deployment_ground_truth.md). |

---

## 1. Summary

Apyx's public protocol documentation was formalized into (a) a normative RFC 2119 specification
([`SPEC.md`](SPEC.md)) and (b) an executable Lean 4 model of the protocol's state machine
([`Apyx.lean`](Apyx.lean)). Against that model we proved **170 theorems**, each re-checked from
source by the Lean kernel, in four groups:

| Group | Question answered | Count | File |
|---|---|---|---|
| **Requirement conformance** | Does the design behave as the documentation specifies? | 82 | [`Apyx.lean`](Apyx.lean) |
| **Key-compromise blast radius** | If a privileged operator key is stolen, how much can be lost? | 56 | [`BlastRadius.lean`](BlastRadius.lean) |
| **Design safety** | Can an ordinary user drain the protocol using only legitimate calls? | 30 | [`Safety.lean`](Safety.lean) |
| **Spec-defect / gap search** | Is the requirement set consistent, and are the economic parameters bounded? | 2 | [`SpecDefects.lean`](SpecDefects.lean) — §9 |

Headline findings for Apyx:

- **No operator key can move a user's balance.** Even with *every* operator key stolen simultaneously, a
  user who signs nothing and is not targeted by an approved RFQ counterparty keeps every unit of their
  recorded `apxUSDBal` / `apyUSDBal` / `usdcBal` (§4.1). Read this as stated: it is a claim about
  **nominal balances**, not about their value. The value claim is false, and the same file proves why —
  see the next point.
- **`ADMIN_ROLE` alone is a total-loss path.** `withdrawReserve` moves the entire USDC reserve to an
  address the admin names, with nothing burned and no claim settled, and `updateRedemptionValue` reprices
  redemptions to any value with no floor and no delay (`admin_alone_drains_reserve`,
  `admin_alone_moves_redemption_price`). A user's balances survive both; their worth does not. The
  two-key admin+RFQ coalition is still proved but is no longer the cheapest route (§4.1, §9.1).
- **The vesting logic is correct.** Formalizing it prompted a close reading of `LinearVestV0.sol`, which
  confirmed the deployed two-accumulator vesting design does not forfeit accrued yield (§4.3).
- **No contradiction in Apyx's own documentation.** A consistency search flagged an apparent conflict
  between two *extracted* requirements, but tracing it to the source docs showed the source is consistent —
  the conflict was an artifact of our automated extraction over-generalizing one requirement (§9.2). No
  change to Apyx's spec is warranted; the fix was in our tooling.
- **Four defects were found in *this report's own model*, and fixed** (§9.3). Three of them had been
  reported here as protocol guarantees: the vault priced off a stale cached rate (so the no-dilution and
  share-price-monotonicity rows were false), `x / 0 = 0` let a share-less address drain the vault, and
  settling an unlock stranded the holder's next request. The fixes are grounded in the deployed contracts'
  verified source and live reads, not in the documentation
  ([`deployment_ground_truth.md`](deployment_ground_truth.md)).
- **The ERC-4626 inflation attack is mitigated, not impossible.** This report previously claimed
  immunity. `ApyUSD._decimalsOffset()` returns `0`, so the vault relies on OpenZeppelin's single virtual
  share; §9.3 quantifies what that leaves open and §5 item 7 is the resulting recommendation.
- **Design recommendations**: a redemption-price floor (§5 item 1) and the ERC-4626 offset decision
  (§5 item 7) are backed by proof. The rate-limit and timelock items are design suggestions whose
  formalized wrappers do not yet establish what their names claim (§5 items 2-3, §9.3).

**Scope.** This verifies a hand-built abstract model of the protocol's *intended design*, not the deployed
Solidity bytecode. It does not check gas, storage layout, upgradeability, reentrancy, or cross-protocol
flash-loan composition — those require an implementation-level audit and are out of scope here (§6). Treat
this report as a rigorous design-level cross-check to sit **alongside** a bytecode audit, not to replace one.

---

## 2. The specification

[`SPEC.md`](SPEC.md) is the normative RFC 2119 requirements document extracted from the source
documentation; [`requirements.json`](requirements.json) is the same content in structured form (each
requirement carries an `id`, `category`, `statement`, `rationale`, and a source quote). The requirements
span nine areas:

- **Access control** — whitelist / denylist gating, pause authority, role-restricted operations.
- **Minting & pricing** — 1:1 issuance, the above-par arbitrage mint pathway.
- **Redemption & the unlock lifecycle** — the request → cooldown → claim asynchronous model, the 20-day
  cooldown, the apxUSD_unlock NFT registry, RFQ redemption.
- **Flexible redemption** — concurrent requests, the 3-day minimum, the early-exit fee schedule.
- **Yield & vesting** — linear vesting, monthly rate cadence, non-decreasing exchange rate.
- **Collateral & solvency** — the overcollateralization invariant and buffer behavior.
- **ERC-4626 vault surface** — conversions, previews, slippage-bounded wrappers.
- **Catastrophic backstop** — redemption-value reset under stress.
- **Events** — the Deposit/Redeem event parameters.

[`model.md`](model.md) is a plain-English walkthrough of the resulting Lean state machine (its actors,
state variables, and operations).

---

## 3. What was proved — requirement conformance (82 theorems)

Every requirement judged expressible as a state-machine property was formalized as a theorem over the
`step` transition function and proved. Grouped by area (theorem names as they appear in
[`Apyx.lean`](Apyx.lean)):

### Access control & authorization
`req_mint_access_whitelist`, `req_redeem_access_whitelist`, `req_deposit_permissionless`,
`req_global_pause_blocks_deposit`, `req_denylist_blocks_deposit`, `req_arbitrage_mint_access`,
`req_arbitrage_redeem_access`, `req_vault_operator_of_unlock_token`, `req_rfq_redemption_allowed`,
`req_governance_deploy_buffer`, `req_yield_distributor_credit`, `req_no_rehypothecation`.

- Mint and redeem are restricted to whitelisted, non-denylisted addresses; deposits revert while paused.
- The arbitrage mint pathway executes only while apxUSD trades **above** $1; the arbitrage redeem pathway
  only while it trades **below** $1 — and only for a whitelisted caller.
- Vault-held apxUSD moves only through the accounting paths in the model (lock / withdraw / redeem):
  proved by exhaustive case analysis over the closed operation type, so **no rehypothecation path exists**.

### Minting & pricing
`req_deposit_mint_apxusd`, `req_mint_price`, `req_issuance_price_one`, `req_mint_price_arbitrage_pathway`,
`req_lock_apxusd`, `req_deposit_immediate`, `req_mint_immediate`.

- Standard minting prices at exactly $1 per unit, unconditionally.
- The vault delivers apyUSD shares synchronously, in the same atomic step as the lock (no deferred settlement).

### Redemption & unlock lifecycle
`req_redemption_async_process`, `req_redemption_cooldown_period`, `req_unlock_cooldown`,
`req_unlock_conversion_after_cooldown`, `req_unlock_token_redeemable_1to1_after_20d`,
`req_unlock_claimable_after_3d`, `req_single_pending_redemption_per_user`,
`req_multiple_unlocks_reset_cooldown`, `req_cooldown_removal`, `req_cooldown_no_yield`,
`req_unlock_token_no_yield`, `req_pay_to_non_cooldown`, `req_synchronous_withdraw_return_token`,
`req_unlock_receipt_nft_mint`, `req_unlock_token_mints_apx_usd_unlock_immediately`,
`req_unlock_token_redeem_after_cooldown`, `req_vault_deposits_apx_usd_into_unlock_token`,
`req_vault_deposits_apx_usd_into_unlock_token_redeem`, `req_vault_pulls_vested_yield_before_withdraw`,
`req_withdrawal_pulls_vested`, `req_vault_burns_apyUSD_shares_immediately_on_withdraw`,
`req_vault_burns_apy_usd_shares_immediately_redeem`, `req_redeem_liquidate_usdc`,
`req_redeem_no_share_transfer`, `req_redemption_value`, `req_redemption_settlement_value`,
`req_redemption_exchange_rate_multiplier`, `req_redemption_value_uniform`, `req_mint_redeem_at_redemption_value`.

- Redemptions follow the three-step request → cooldown → claim model; conversion of the unlock token to
  apxUSD is possible only after the 20-day cooldown.
- A claim requires `caller = owner ∨ caller = the vault operator`; before the deadline, a claim reverts,
  and after it, a claim succeeds.
- **Each user holds at most one pending standard redemption.** A repeat request tops up the caller's
  existing position and resets its cooldown on the aggregated amount, rather than opening a second one —
  enforced by the transition function and proved as a reachable invariant.
- The redemption value applied is uniform across participants.

### Flexible redemption & fees
`req_flexible_redemption_multiple_requests`, `req_flexible_redemption_claim_minimum`,
`req_flexible_redemption_early_fee`, `req_early_unlock_fee_linear_decline`.

- Users may hold multiple concurrent flexible requests; a flexible claim is possible only after 3 days.
- The early-exit fee is bounded in [0.1%, 3.5%], is monotonically non-increasing over time, and reaches
  its 0.1% floor once the full cooldown has elapsed.

### Unlock-token (NFT) integrity
`req_singleton_unlock_token_instance`, `req_unlock_token_nontransferable`, `req_unlock_cannot_be_cancelled`.

- The UnlockToken registry is a genuine singleton with a fixed operator.
- An unlock position's recorded owner can never be reassigned to another address, and a position cannot be
  cancelled once created — both proved by exhaustive case analysis over every operation.

### Yield & vesting
`req_apyusd_value_increase`, `req_new_locked_receives_yield`, `req_linear_vest_implementation`,
`req_continuous_stream`, `req_yield_distribution_period`, `req_configurable_vesting_period`,
`req_credit_preserves_accrued_vest`, `req_yield_rate_dollar_terms`, `req_exchange_rate_non_decreasing`,
`req_token_no_rebase`, `req_total_assets_includes_vault_balance_and_vested`.

- The apyUSD/apxUSD exchange rate is non-decreasing **in time** (`req_exchange_rate_non_decreasing`
  quantifies over `now`, not over operations). Monotonicity across a deposit is the separate
  `exchange_rate_monotone_deposit`; both are now about the live `computeExchangeRate` rather than a
  stored field (§9.3).
- Vesting is linear: nothing releases before the clock anchor, the released amount grows monotonically with
  time, never exceeds the pool, and equals the full pool once a period has elapsed.
- Crediting new yield preserves already-accrued yield (`req_credit_preserves_accrued_vest`); the monthly
  rate is bounded by the recorded prior-month dollar collateral yield.

### Collateral & solvency
`req_overcollateralization_limit`, `req_buffer_non_decreasing`, `req_buffer_preservation`,
`req_buffer_not_consumed`, `req_catastrophic_backstop`.

- The overcollateralization invariant is preserved across operations (under the stated well-formedness
  conditions; the solvency-breaking operations are explicitly excluded and documented). The invariant is
  `totalSupply_apxUSD ≤ totalCollateralValue + usdcReserve`; it no longer carries a "required margin"
  term, which was identically zero on every reachable trace (§9.3).
- Routine redemptions never reduce the overcollateralization buffer.

### ERC-4626 vault surface
`req_erc4626_compliance`, `req_depositforminshares_slippage`, `req_mintformaxassets_slippage`,
`req_withdraw_for_max_shares_revert_if_exceeds_max_shares`,
`req_redeem_for_min_assets_revert_if_below_min_assets`.

- The conversion/preview functions are internally consistent and pause-gated; the slippage wrappers revert
  when the user's bound would be violated.

### Events
`req_deposit_emits_event`, `req_mint_emits_event` — each emits a Deposit event with the exact
`(sender, receiver, owner, assets, shares)` tuple.

> The full statements, each with its source RFC 2119 quote, are the docstrings in
> [`Apyx.lean`](Apyx.lean).

---

## 4. What was proved — adversarial analysis

### 4.1 Key-compromise blast radius (56 theorems, [`BlastRadius.lean`](BlastRadius.lean))

The requirement proofs assume every actor behaves as documented. This group answers the harder question the
documentation never addresses: **if a privileged operator key is stolen, how much can the attacker take?**
The attacker is modeled as holding one or more role keys (`admin`, `oracle`, `pauseController`,
`yieldDistributor`) and submitting arbitrary operation sequences, interleaved with honest traffic.

**No single stolen key can extract principal:**

| Stolen key | Proved blast radius | Theorem |
|---|---|---|
| `pauseController` | Freeze only — touches no balance | `pauser_trace_blast_radius` |
| `yieldDistributor` | Can only donate into the vest pool; debits nothing | `yield_distributor_trace_blast_radius`, `distributor_compartmentalized` |
| `oracle` | No balance movement; publishes the reported market price only. The **redemption** price is an admin capability, not an oracle one (`Roles.assignAdminTargetsFor`) | `oracle_alone_preserves_balances` |
| `admin` | Cannot debit any balance or supply, but **publishes the redemption price with no floor, cap or delay, and can move the reserve to a named address without any redemption** | `admin_cannot_touch_balances`, `admin_alone_moves_redemption_price`, `admin_alone_drains_reserve` |
| **all keys at once** | A passive, non-RFQ-targeted user loses nothing | `user_assets_immune_to_total_key_compromise`, `no_theft_ledger` |

The non-custodial headline (`user_assets_immune_to_total_key_compromise`) is the machine-checked form of
"we cannot move your funds even if we wanted to." Its active complement is also proved: no operation
sequence lets any caller mint apxUSD for free — every credit is backed by an equal USDC payment or the
settlement of the recipient's own pre-existing locked position (`apxUSD_credit_is_backed`).

Supporting theorems include the exact per-role effect frames (`admin_frame`, `oracle_frame`,
`yield_distributor_frame`, and the `step_*_exact` family), the non-custodial lemmas
(`no_role_transfers_user_funds`, `no_role_burns_user_shares`, `no_role_debits_usdc`,
`governance_token_balances_immutable`, `no_role_seizes_unlock_position`), and the extraction-channel
characterizations (`redemption_price_writers`, `reserve_outflow_only_via_redemption`).

**The admin key alone is a total-loss path.** This report used to headline a two-key coalition
(`admin_rfq_coalition_drains`: the admin crashes the redemption value via `catastrophicBackstop`, then an
approved RFQ counterparty settles a victim's request at the crashed price for **0 USDC**). That coalition
is still real and still proved, but it is no longer the cheapest route, and the reason it read as the
cheapest was a gap in the model rather than a property of the protocol. Two operations now carry what the
deployment carries:

- **`admin_alone_drains_reserve`** — `withdrawReserve` moves the reserve to an address the admin names,
  with nothing burned and no claim settled. It mirrors `RedemptionPoolV0.withdraw` / `withdrawTokens`,
  which `Roles.assignAdminTargetsFor` assigns to `ADMIN_ROLE` and the deployment's own
  `RedemptionPool/Access.t.sol` tests as admin-only. No second key, no emergency flag.
- **`admin_alone_moves_redemption_price`** — the *quiet* write to `redemptionValue`: any non-zero value,
  one step, no side effect anywhere else in the state. `catastrophicBackstop` is the loud write; only the
  loud one is visible to a monitor watching protocol state. Both are the same key
  (`redemption_price_writers`).

The payout is exactly `amount × redemptionValue / ray` with no cap on `redemptionValue`
(`redeem_payout_formula`, `redeem_payout_has_no_cap`), so the loss on the pricing route is unbounded. This
sharpens rather than replaces the §5 recommendations: a price floor and a bounded per-update move now
matter against a *single* key, and the reserve wants a rate limit of its own.

**And the counterparty does not need the admin key at all, only the clock.**
`rfq_payout_is_set_by_execution_timing` runs the same user, the same 100-apxUSD request and the same
counterparty twice: settled immediately the user is paid 100, settled after one *honest* price update the
user is paid 50. Both traces are permitted, both consume the request, and the counterparty picks — with no
emergency and no compromised admin.

### 4.2 Design safety — honest-actor attacks (30 theorems, [`Safety.lean`](Safety.lean))

This group assumes every actor is honest and asks whether the *design itself* lets an ordinary attacker
extract value using only legitimate operations.

| Property | Guarantee | Theorem |
|---|---|---|
| No free value | No operation sequence lets any address mint apxUSD from nothing | `no_free_value_trace` |
| Solvency preserved | Minted apxUSD never exceeds the collateral basket plus the USDC reserve across any trace (under stated well-formedness, and excluding the operations listed in §6.2) | `solvency_preserved` |
| Rounding favors the protocol | Conversions never credit the user free value; withdrawals round up in shares | `rounding_favors_protocol`, `withdrawShares_rounds_up` |
| No dilution | A deposit by someone else never lowers an existing holder's redeemable value, measured at the **live** per-share price. Unconditional — no backing or non-zero-supply side condition, so the first depositor is covered too | `no_dilution` |
| No raw donation primitive | Every increase in vault custody is one of the three accounted channels; there is no transfer-into-custody operation | `donation_free`, `no_inflation_attack` |
| Inflation attack: **mitigated, not impossible** | A deposit below the current share price still rounds partly into the pool. The deployment's only structural defence is OpenZeppelin's single virtual share (`_decimalsOffset() = 0`), which the model now carries; §9.3 quantifies the residue | `Regression.lean` §R3 |
| No free extraction | A caller cannot end richer than they started (single-step, at the live rate) | `caller_net_nonpositive`, and the `caller_value_*` family |
| No early yield drain | Vested yield cannot be pulled forward faster than its linear schedule | `vest_no_early_drain` |
| Vesting conservation | Both crediting new yield and reconfiguring the vesting period preserve already-accrued yield | `creditYield_preserves_accrued_vest`, `setVestPeriod_preserves_accrued_vest` |
| No peg-spread round trip | The arbitrage mint (needs price > $1) and arbitrage redeem (needs price < $1) require opposite price regimes, so no single state enables both | `no_same_state_arbitrage_round_trip` |
| Redemption request is backed | A redemption request burns exactly the requested apxUSD and leaves the caller one tracked position — the obligation exactly equals the burn (no free claim) | `requestUnlock_backs_claim_by_burn` |
| No free extraction (trace) | Over arbitrary traces of non-share operations, no address's fixed-rate holdings can increase — no free money through the redemption / RFQ / request channels at any length (the share-op + live-rate closure is left open, see §6.2) | `caller_net_nonpositive_trace` |
| Share-price monotonicity | A new deposit never lowers the **live** per-share price, and crediting yield preserves it (raising it only as yield vests over time) — the ERC-4626 dilution invariant | `exchange_rate_monotone_deposit`, `exchange_rate_monotone_creditYield`, `req_exchange_rate_non_decreasing` |
| Vault pricing is live | Conversions and every `step` branch price off `computeExchangeRate`, never off a stored field — matching the deployment, which has no stored rate | §9.3, `Regression.lean` §R1/R2 |

### 4.3 The vesting cross-check (a positive finding)

Formalizing the vesting logic raised a specific question: does crediting new yield forfeit yield that has
already accrued but not yet been pulled into the vault? Checking the deployed contract answered it:
`LinearVestV0.sol`'s `depositYield` executes `fullyVestedAmount += newlyVestedAmount()` **before** resetting
the vesting clock, so accrued yield is preserved in a second accumulator. The Lean model was aligned to that
two-accumulator design, and the preservation is now proved for both code paths that restart the clock
(`creditYield_preserves_accrued_vest`, `setVestPeriod_preserves_accrued_vest`). **The deployed vesting
design is correct on this point.**

---

### 4.4 The other async-redemption vault (8 theorems, [`CommitToken.lean`](CommitToken.lean))

Added after reading the deployed authority graph, which turned up a second async-redemption vault
holding 250× what the modelled unlock path holds (§6.4 #18). `CommitToken` "CT-apxUSD"
(`0x17122d86…871e`) is the contract `UnlockToken` subclasses; live parameters at the time of
reading are a **14-day** `unlockingDelay`, a `1e26` supply cap, and 1:1 assets↔shares.

**All four live instances are covered by this one model**, because they differ only in the
underlying asset, the cooldown and the supply cap — all three of which are state fields:
`CT-apxUSD` (14 d, 100M cap), `CT-apyUSDapx` (14 d, 20M), `CT-apxUSDUSDC` (14 d, 50M) and
`UnlockToken` (20 d, uncapped), enumerated as `liveDeployments`.
`cycle_closes_at_every_live_deployment` instantiates the liveness half at each.

This is also the first time `docs/06` §7's async family is instantiated against a **real** target
rather than the fictional `AsyncQueueVault` reference, and it needs the clock to say anything at
all.

Three properties hold and are worth having: `cycle_closes_after_the_live_delay` (request, wait the
deployed 14 days, claim — in one trace), `claim_conserves` (a claim burns exactly what it pays),
and `commitment_is_bounded_by_balance` (a holder can never be committed to more than they hold).

Three describe behaviour a holder should know about, none of which violates anything the code
promises:

- **`topup_restarts_the_whole_cooldown`** — `_requestRedeem` does `request.shares += shares;
  request.requestedAt = block.timestamp`, with no tranches. Adding one unit to a request that has
  already served its 14 days makes the **entire** position unclaimable for another 14.
- **`no_partial_claim`** — `redeem` reverts unless the amount equals the request exactly. Composed
  with the above, a position can only be exited whole, so a holder who tops up cannot take out the
  part that had matured.
- **`raising_the_delay_unclaims_pending_requests`** — `_cooldownRemaining` reads `unlockingDelay`
  from storage rather than snapshotting it at request time, so lengthening it pushes out every
  outstanding request, including ones claimable a moment earlier. Bounded by governance rather
  than by the contract: `setUnlockingDelay` is role 24 on-chain, a 3-day scheduled operation
  ([`model.md`](model.md) §6).

`request_does_not_escrow` records the ERC-7540 deviation the contract's own docstring names —
shares stay on the owner's balance between request and claim — and pairs it with the arithmetic
check that makes that safe.

### 4.5 The redemption-price pipeline (8 theorems, [`RedemptionOracle.lean`](RedemptionOracle.lean))

`Apyx.lean` carries one `redemptionValue` field written by privileged operations. On-chain the
price comes from two contracts and **neither has that setter**: `ApyxCollateralRatioOracle`
(`pushRound`, role 22 — a 4-hour scheduled operation) feeds `ApyxRedemptionOracle`, a read-only
aggregator publishing `min(collateral ratio, cap)` with no write functions at all. Live values:
`cap() = 1.00` at 8 decimals, published answer 0.903659.

This module settles the two parameter-bound findings of §9.1 in **opposite** directions, which is
the reason it is worth having as proofs rather than prose:

- **The cap is real.** `published_never_exceeds_par` — along every trace, with the deployed cap,
  the published price is at most 1.00. `cap_immutable` / `cap_immutable_trace` show no operation
  in the pipeline moves the cap (pattern I21 against a live contract; on-chain the contract simply
  has no setter, and changing it needs a UUPS swap under role 24, 3 days). A hostile push is
  clamped rather than rejected (`push_above_cap_is_clamped`).
  This is also where `Safety.lean`'s `h_rv : redemptionValue ≤ ray` stops being a hypothesis: the
  deployment enforces it.
- **The floor is not.** `published_has_no_floor` — one push of `0` publishes `0`. There is no lower
  clamp and no minimum move anywhere in the pipeline, and below the cap the published price is
  exactly what was pushed (`published_tracks_the_push_below_cap`). So `redemption_has_no_floor`
  survives contact with the deployment while `redeem_payout_has_no_cap` does not.

### 4.6 The two operational contracts (9 theorems)

**[`MinterRateLimit.lean`](MinterRateLimit.lean).** `Apyx.lean` mints at $1 with role and list
checks and no volume bound; on-chain, minting goes through `MinterV0` and carries a sliding-window
rate limit — live values **50,000,000 apxUSD per day**, with a 50× tightening to 1,000,000 sitting
in the manager's queue. The guard is modelled and two consequences are stated:
`tightening_does_not_unwind_the_window` (reducing the ceiling does not claw back what the window
already holds, so `available` simply pins at 0 until the window rolls — the mirror image of
`CommitToken.raising_the_delay_unclaims_pending_requests`), and `window_frees_in_one_step` (a
record leaves the window the instant `now` passes it; there is no smoothing, so a full window
restores its entire allowance in one block). The trace-level "damage is linear in time" statement
is not re-proved here — `BlastRadius.rate_limit_linear_bound` already has that shape generically,
and what was missing was the tie to a real contract's guard.

**[`LiquidationBatcher.lean`](LiquidationBatcher.lean).** Role 41 carries no execution delay and is
held by a single EOA, which is what makes it worth modelling; reading the contract is what makes
the answer reassuring. It liquidates on Morpho Blue, not on Apyx state, and two construction-time
pins bound it: `allowlist_immutable` and `destination_immutable` (neither has a setter),
`withdraw_credits_only_the_pinned_destination` (`withdrawTokens` takes no destination argument),
and `unlisted_market_reverts_the_batch` (fail-closed, so an unlisted ticket cannot ride along
inside a large batch). `role41_trace_blast_radius` lifts the two pins to whole traces:
**undelayed, but not unbounded.**

---

## 5. Design recommendations for Apyx

These follow directly from the proofs above. Items 1–3 are the defenses whose *absence* is the reason the
two-key coalition (§4.1) is unbounded; where a defense is formalized, the theorem naming what it would
guarantee is cited.

1. **Add a redemption-price floor.** The single unbounded loss path exists purely because `redemptionValue`
   has no lower clamp; `catastrophicBackstop` can drive it to 0. A floor (or a bounded per-update move)
   removes the total-loss outcome of the admin + RFQ coalition.

2. **Add a withdrawal / redemption rate limit** (ERC-7265-style circuit breaker). Formalized as a wrapper
   over the model and proved to bound cumulative reserve loss to `≤ cap × (epochs elapsed + 1)`
   (`rate_limit_linear_bound`).
   **Read this as a design suggestion, not a quantified guarantee.** The wrapper's `advanceEpoch` is a
   free, permissionless action with no relation to `Op.tick` or `base.now`, so the theorem counts epoch
   markers the attacker put in their own trace rather than elapsed time; and the meter charges
   `usdcReserve` outflow only, so a repricing-to-zero drain passes it unmetered. Both are recorded in
   [`code_review_lean.md`](code_review_lean.md) §1.2 and are unfixed. The *recommendation* stands on its
   own merits — a real ERC-7265 breaker is metered by the chain clock — but this report's theorem does
   not currently establish it.

3. **Add a timelock on privileged admin changes.** The base model is proved to have **no exit window** —
   admin changes take effect in the same block (`base_model_has_no_timelock`,
   `catastrophicBackstop_is_instantaneous`). That negative result is sound.
   The positive half (`timelock_escape_guarantee`) carries the same caveat as item 2: its `tick` is a
   free counter unrelated to the base clock, and the wrapper routes *every* operation through the
   queue — including a user's own exit — so as modelled it does not actually provide the escape window
   its name claims (`code_review_lean.md` §1.2). Unfixed.
   **Largely already met on-chain, and this recommendation was written against a stale
   observation.** The deployed `AccessManager` (`0xe167330E…2824`) runs a graded delay ladder —
   0 for `pause()`, 4h for the price push, 24h for privileged token withdrawal, 3 days for
   `upgradeToAndCall`, 7 days for `setAuthority` — with a 5-day minimum setback on any reduction
   and a 7-day grant delay on `ADMIN_ROLE` itself. What still carries **no** delay is `ADMIN_ROLE`,
   held by a single Safe. See [`model.md`](model.md) §6 for the snapshot and the addresses; the
   residual recommendation is about that one role, not about the scheme.

4. **Minimize trust in the RFQ counterparty set.** With defenses 1–3 in place, user-fund safety against a
   compromised admin still depends on the honesty of approved RFQ counterparties (they are the second key in
   the only total-loss path). Keep this set small, audited, and ideally itself timelocked.

5. **Preserve the two-accumulator vesting pattern** (§4.3). The deployed design is correct; the model
   depends on `fullyVestedAmount` being realized *before* the vesting clock is reset in both `depositYield`
   and `setVestingPeriod`. Any refactor should keep that accrue-first ordering.

6. **Enforce owner-consistency on redemption-request top-ups.** The single-pending-per-user guarantee (§3)
   holds in the model because a top-up only ever modifies a position whose recorded owner is the caller.
   The contract should maintain the same invariant (a user's pending-request pointer references only their
   own position).

7. **Decide on the ERC-4626 inflation-attack posture.** `ApyUSD._decimalsOffset()` returns `0`, so the
   vault's only structural defence against share-price rounding is OpenZeppelin's single virtual share,
   and `deposit()` does not revert on a zero-share result. At 128M outstanding shares this is not
   economically live today, but it is the standard mitigation and it is currently declined. Either raise
   `_decimalsOffset`, seed the vault permanently, or document the reliance on `depositForMinShares` for
   integrators. Quantified in §9.3 and `Regression.lean` §R3.

8. **Commission an implementation-level (bytecode) audit** for the classes this model cannot reach —
   reentrancy, flash-loan composition, gas/storage, and upgrade safety (§6).

---

## 6. Out of scope and not provable against this model

Reported honestly so the boundary of these guarantees is clear.

### 6.0 How to read a theorem count — quantifier scope, and what the model can refute

Two questions decide what a machine-checked theorem is worth, and neither is answered by the
count. **Over what does it quantify?** and **could the model have exhibited its failure?**

**Quantifier scope.** **22 theorems quantify over an arbitrary operation sequence**
(`execTrace`) — 4 in [`Safety.lean`](Safety.lean), 18 in
[`BlastRadius.lean`](BlastRadius.lean). Those are the ones that rule out multi-step attacks.
Every other theorem, **including all 82 requirement-conformance theorems**, is single-step: it
says what one operation does from an arbitrary state satisfying its hypotheses. That is the
right shape for most requirements — "`depositUSDC` mints apxUSD" is a single-step claim — but a
single-step theorem cannot exclude a sequence, and citing one as if it could overstates it.
Anywhere this report says "no operation can …" the statement is exhaustive over `Op` at one
step; anywhere it says "no trace can …", it is the stronger claim.

**Refutability.** A theorem is bounded above by whether its state space can express the failure
it denies. This model has three known blind spots of that kind, all recorded below and in
[`model.md`](model.md) §5:

| The model cannot express | So these say less than they appear to |
|---|---|
| **Negative net value** — every balance is `Nat`, and `x - y` truncates at 0 | Any "never underwater" reading of `solvency_preserved` / `req_overcollateralization_limit`. Insolvency is not false here, it is unrepresentable |
| **Per-holder totals** — the ledger is `Address → Nat` with no `Σ` | §6.2; the aggregate conservation clause of the backstop |
| **A second, independent price** — one `redemptionValue`, where the deployment has a redemption price and a Curve-facing oracle price with nothing tying them together | Divergence between the two. See item #17 in §6.4 |

Two blind spots that **used to be here and no longer are**, recorded because they show the cost
of not asking this question: until `Op.tick` existed no trace advanced `now`, so every
cooldown, vesting and settlement-timing requirement was stated about hand-supplied states; and
until `updateRedemptionValue` wrote anything, `catastrophicBackstop` was the only writer of
`redemptionValue`, which is the sole reason the worst coalition in §4.1 reads as needing two
keys. Neither was a wrong theorem. Both were questions the model could not be asked.

**Reachability is now carried, not assumed.** `flexible_fee_schedule_is_reachable` reaches the
matured states the fee requirements assume — file, wait, claim — and pins the fee actually
charged at 299 bps after 3 days, 180 after 10, 10 after the full cooldown.
`redemption_cycle_closes_after_cooldown` does the same for the standard unlock. Their
counterpart `req_redemption_async_process` proves only that an *immediate* claim reverts; the
positive half is a **liveness** property, and liveness in general stays out of scope — nothing
here forces any party to act (§6.3).

### 6.1 Off-chain or UI behavior (not attempted)
Five requirements describe processes outside on-chain state and were flagged as such at extraction:
treasury capital allocation (`offchain-allocation`), third-party custody attestations (`custody-attestation`),
buffer sizing against historical drawdowns (`liquidity-buffer-size`), qualitative buffer-growth-under-stress
(`buffer-growth-stress`), and frontend jurisdiction blocking (`jurisdiction-restriction-frontend`).

### 6.2 Not expressible in an aggregate-ledger model (partial coverage, documented)
Two clauses need structure the abstract model does not carry; encoding a fictional version would be worse
than an explicit gap:

- **`catastrophic-backstop`, second clause** — "distribute the entire reserve pro-rata to remaining
  holders." The first clause (setting the per-unit redemption value to `totalCollateralValue / totalSupply`,
  matching the deployed `ApxUSDRateOracle`) **is** proved (`req_catastrophic_backstop`), as is the
  *per-address* pro-rata credit itself — every holder `a` is shown to be credited exactly
  `usdcReserve · apxUSDBal(a) / totalSupply` with the reserve and the buffer both driven to zero
  (`req_catastrophic_backstop` clauses (3)–(4), and the buffer-to-zero effect restated in `SpecDefects`).
  What remains unformalized is only the *aggregate conservation* of that split — that `Σ_holder` of the
  credits exactly equals the drained reserve — which needs a `Σ` over the holder set the aggregate
  `Address → Nat` ledger has no summation structure for; the same
  limitation that makes `solvency_preserved` take well-formedness as a hypothesis.
- **`caller_net_nonpositive`, trace-level closure** — the value-weighted no-free-money property is proved
  single-step at a fixed reference rate; extending it to arbitrary traces under a *moving* exchange rate is a
  distinct, genuinely hard arithmetic problem and is flagged as open rather than claimed.

### 6.3 Requires a mechanism the model does not have (declined)
- **`price-may-include-spreads`** — a permissive (MAY) clause; the model prices mints hard-coded 1:1 and has
  no spread parameter to witness it either way.
- **`rebalance-overcollateralization`** — the model tracks only aggregate collateral value, not basket
  composition, and has no active rebalancing operation (only the passive invariant is modeled).

### 6.4 What the design layer cannot check — hand-off to implementation-level tools

This report verifies an **abstract, atomic, hand-built** model. Everything below is invisible to it *by
construction* and must be checked against the **deployed Solidity** with static analysis, SMT/symbolic
execution, and invariant fuzzing. This is the honest boundary — the design-level proofs and this list are
complementary, not redundant. (Tool classes: **Static** = Slither/Aderyn/semgrep; **SMT** = Certora Prover,
Halmos, hevm; **Fuzz** = Echidna, Medusa, Foundry invariant; **Config** = role-graph/delay/storage review.)

| # | Item the design model cannot cover | Why the Lean layer can't see it | Check with |
|---|---|---|---|
| 1 | **Reentrancy** (single-fn, cross-fn, and **read-only** — a view returning mid-update state) | `step` is atomic; there is no notion of an external call re-entering mid-transition | Static + SMT (reentrancy rules) + Fuzz |
| 2 | **Cross-protocol / flash-loan composition** (e.g. manipulating an external pool the protocol reads) | The model has one protocol, one closed `Op`; no external mutable state | SMT with attacker harness + economic sim |
| 3 | **Bytecode ⊨ model** — the model is a *hand-built interpretation* and can diverge from the contract (as the vesting and catastrophic-per-unit cases here showed) | Proofs are about the Lean model, not `ApxUSD`/`ApyUSD`/`RedemptionPoolV0`/`LinearVestV0` bytecode | **SMT (Certora/Halmos) on the actual contracts** — the primary complement |
| 4 | **Fixed-point rounding & decimals** — **partly closed.** The four `previewX` rounding directions were read off the verified source and the model now matches them (`previewMint` was Floor and is now Ceil, §9.3). What remains is the USDC(6)↔apxUSD/apyUSD(18) scaling, which the model still treats as commensurate | Model uses ideal `Nat` division; no `uint256`/decimals semantics | SMT + Static |
| 5 | **Overflow / unchecked / division-by-zero** — Lean `x/0 = 0` masks a Solidity revert; `unchecked{}` blocks | Nat arithmetic never overflows or reverts | Static + SMT |
| 6 | **ERC-20/4626 ledger identity** `Σ balances = totalSupply` — the model *assumes* it (`solvency_preserved`/`req_overcollateralization_limit` take `WellFormed` as a hypothesis) | Balances are bare `Address → Nat` with no summation structure | SMT invariant on the deployed token/vault |
| 7 | ~~**ERC-4626 inflation defense in the real vault**~~ — **answered, and the answer is negative.** `ApyUSD._decimalsOffset()` returns `0`, so the only structural defence is OpenZeppelin's single virtual share, and `deposit()` does not revert on zero shares. The model now carries the same `+1` and reports the residue rather than claiming immunity (§9.3, §4.2). Remaining implementation work is the decision itself: whether to raise `_decimalsOffset` or seed the vault | — | Protocol decision + Fuzz to size the exposure |
| 8 | **Vesting timestamp detail** — `LinearVestV0` separates `lastDepositTimestamp`/`lastTransferTimestamp`; the model collapses to a single `vestStart` (documented simplification), so a pull can shift the vesting end | Model has one clock anchor | SMT/Fuzz on `LinearVestV0` |
| 9 | **Aggregate conservation of the pro-rata split** (catastrophic-backstop 2nd clause) | The *per-address* credit `reserve·balance/totalSupply` is proved (`req_catastrophic_backstop`); only `Σ_holder` of the credits = drained reserve is left, needing a `Σ` the aggregate ledger can't express (§6.2) | Implementation audit + SMT |
| 10 | **Access-control configuration** — the OZ `AccessManager` role graph and the **actual per-function delays** (the 0-second-timelock risk Yearn flagged; the model proves `base_model_has_no_timelock`), plus `MinterV0` rate-limit params | Model abstracts roles to `caller = admin/oracle/…`; it does not carry the deployed authority wiring or delay values | **Config review** + Static |
| 11 | **Signature handling** in `MinterV0` — EIP-712 order signing and ERC-1271 contract signatures: replay, malleability, nonce/expiry, domain separator | The model has no signatures; mint authorization is abstracted away | Static + SMT (signature-replay rules) |
| 12 | **Upgradeability** — the UUPS oracles (`ApxUSDRateOracle`, `ApyUSDRateOracle`): `_authorizeUpgrade` gating, initializer protection, and **ERC-7201 storage-layout** stability across upgrades | Model has no proxies, no storage layout, no upgrade op | Static (upgradeability) + OZ upgrades plugin + storage-layout diff |
| 13 | **Gas / DoS** — e.g. `MinterV0`'s `mintHistory` `DoubleEndedQueue` growth and any unbounded loops | Model has no gas metering or loop cost | Static + gas profiling + Fuzz |
| 14 | **Cross-chain** — `BridgedApyxToken` / `CCIPBridge` in the repo | Out of the single-chain state machine entirely | Separate bridge audit |
| 15 | **Off-chain processes** — USD collection & the mint/redeem **spread** (`price-may-include-spreads`, applied off-chain — §6.3), treasury custody, attestations, and the oracle **price-setting process** feeding `setRate` | Not on-chain state | Operational / process audit |
| 16 | ~~Privileged reserve withdrawal~~ — **now modelled** as `Op.withdrawReserve`; `reserve_outflow_only_via_redemption` carries it as an explicit third exit and `solvency_preserved` names it as an exclusion. What remains out of scope is the **authority behind it**: who actually holds `ADMIN_ROLE` on the deployed `AccessManager`, and with what delay | The model abstracts roles to `caller = admin`; it does not carry the deployed authority wiring | Config review |
| 18 | **The larger async-redemption vault is outside the model.** The modelled unlock path (`UnlockToken`) holds **24,936 apxUSD**; a structurally identical `CommitToken` "CT-apxUSD" (`0x17122d86…871e`), governed by the same authority, holds **6,226,697 — 1.90% of supply, 250× more**. Two further `CommitToken`s wrap the Curve LP tokens | The model was scoped from the documentation, which describes the unlock path; these are separate deployments visible only in the on-chain authority graph | Derive the Step-0 profile from the authority graph as well as the docs, then instantiate the async family (docs/06 §7) against the larger vault — see [`model.md`](model.md) §6 |
| 17 | **Redemption-price source** — `RedemptionPoolV0.exchangeRate` (what a redeemer is paid) and `ApxUSDRateOracle.rate` (what the Curve pool reads) are two independent unbounded values with nothing tying them together | The model carries a single `redemptionValue`; the second price has no consumer inside the modeled system | SMT/Fuzz across the pool boundary + Config review |

**Priority within this list:** #3 (bytecode⊨model) and #7 (real-vault inflation defense) are the highest-value
SMT targets — they directly re-check, at the implementation level, the two guarantees this report proves
abstractly. #10 (delays/roles) directly determines whether the §5 timelock recommendation is already met.

---

## 7. Verifying this report yourself

The Lean project is dependency-free (no mathlib) and compiles in seconds.

```bash
# 1. Install elan (the Lean toolchain manager), if not already present
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell, or: source ~/.elan/env

# 2. Build — elan reads lean-toolchain (Lean 4.31.0) and fetches it automatically
cd lean
lake build D2fsSpecs
```

`D2fsSpecs` is the library of analyzed systems; naming it explicitly compiles exactly the four
Apyx modules below and nothing else. (A bare `lake build` additionally compiles
`TemplateExamples`, a fictional model that regression-tests the reusable proof templates in
`templates/`; it is unrelated to Apyx.)

`lake build` exiting `0` with no `sorry` warnings **is** the proof-checking event: the Lean kernel
re-verifies every theorem from source. Every theorem depends only on Lean's standard `propext` and
`Quot.sound` axioms (one blast-radius theorem additionally uses `Classical.choice`) — all standard, trusted
axioms of Lean's logic; none is an unproved assumption. Compile status is recorded in
[`leancheck.json`](leancheck.json).

---

## 8. Artifact map

| File | Contents |
|---|---|
| [`SPEC.md`](SPEC.md) | The normative RFC 2119 specification (human-readable) |
| [`requirements.json`](requirements.json) | The 82 extracted requirements in structured form |
| [`model.md`](model.md) | Plain-English summary of the Lean state machine |
| [`Apyx.lean`](Apyx.lean) | The formal model (`State`, `Op`, `step`) and the 82 requirement proofs |
| [`BlastRadius.lean`](BlastRadius.lean) | The 56 key-compromise blast-radius proofs and the defense wrappers |
| [`Safety.lean`](Safety.lean) | The 30 design-safety proofs |
| [`SpecDefects.lean`](SpecDefects.lean) | The spec-consistency and parameter-bound gap-witness proofs (§9) |
| [`CommitToken.lean`](CommitToken.lean) | The deployed `CommitToken` async-redemption vaults, all four instances — 9 proofs (§4.4) |
| [`RedemptionOracle.lean`](RedemptionOracle.lean) | The deployed two-stage redemption-price pipeline — 8 proofs (§4.5) |
| [`MinterRateLimit.lean`](MinterRateLimit.lean) | `MinterV0`'s sliding-window mint rate limit — 4 proofs (§4.6) |
| [`LiquidationBatcher.lean`](LiquidationBatcher.lean) | The construction-time bounds on the one undelayed keyed role — 5 proofs (§4.6) |
| [`leancheck.json`](leancheck.json) | Build status: requirement theorems, `sorry` count, vacuous count |
| [`corpus.md`](corpus.md) | The raw ingested source documentation |
| [`code_review_lean.md`](code_review_lean.md) | Self-review of this report's Lean source — every finding, fixed and unfixed (§9.3) |
| [`deployment_ground_truth.md`](deployment_ground_truth.md) | Verified-source and live-read facts the §9.3 fixes are grounded in |
| [`review_witnesses/Regression.lean`](review_witnesses/Regression.lean) | Kernel-checked regression tests pinning each §9.3 fix |

---

## 9. Requirement-consistency and parameter-bound gaps

This group turns the lens on the requirement set itself and on the economic parameters.

### 9.1 A machine-checked parameter gap — the redemption price has no floor or cap

The redemption price (`redemptionValue`) has **no enforced floor and no enforced cap** in the design, and
in the model it is written by the admin — either loudly (`catastrophicBackstop`) or quietly
(`updateRedemptionValue`); see `redemption_price_writers`. Two witnesses prove the consequences:

- **`redemption_has_no_floor`** — there is a reachable state (`redemptionValue = 0`) in which a whitelisted
  holder's `redeemApxUSD` **succeeds** yet pays **0 USDC** for the apxUSD it burns: a total loss the guards do
  not prevent.
- **`BlastRadius.redeem_payout_has_no_cap`** — symmetrically, no upper bound on the payout exists.

> **On-chain the upper bound exists, and the lower one still does not — both are now proved.**
> [`RedemptionOracle.lean`](RedemptionOracle.lean) (§4.5) models the deployed pipeline:
> `published_never_exceeds_par` bounds the price at 1.00 along every trace, so the no-cap finding
> describes the *design* while the deployment supplies a bound outside the modelled state, and
> `Safety.lean`'s `h_rv : redemptionValue ≤ ray` is enforced rather than assumed.
> `published_has_no_floor` shows the floor finding is untouched: one push of `0` publishes `0`.
> `RedemptionPoolV0.setExchangeRate` and `ApxUSDRateOracle.setRate` appear nowhere in the live
> authority table. Addresses and the snapshot: [`model.md`](model.md) §6.

Together with the two-key coalition (§4.1), these are the concrete design weaknesses of the model. **Fix:** a
redemption-price floor/clamp, a withdrawal rate limit, and an admin timelock (§5) — the same three defenses §5
already quantifies. (This matches the two most common industry loss patterns — unbounded parameters and
privileged-key/governance gaps; see [`docs/08-defi-vuln-patterns.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/docs/08-defi-vuln-patterns.md).)

### 9.2 A consistency check on the requirements — an extraction artifact, now fixed

Turning the lens on the extracted requirement set itself: **are the requirements mutually consistent?** The
check flagged one apparent conflict:

- `buffer-non-decreasing` (as first extracted) required, *unconditionally*, that the buffer **MUST NOT
  decrease**.
- `catastrophic-backstop` requires that, on a catastrophic event, the system **distribute the entire buffer**.

A proof confirmed those two *extracted* statements were jointly unsatisfiable. Tracing the requirement back to
the source documentation (`corpus.md`) then showed the **source is consistent**: it states the buffer is "not
consumed during **routine redemptions**" and "preserved through **stress events**," and separately that a
**catastrophic scenario** (a devastating hack or wind-down) distributes the entire buffer — an explicitly
*separate*, terminal mechanism. Our automated extractor had generalized the *stress-events* sentence into an
*unconditional* "MUST NOT decrease," dropping the scope. **This was a defect in our tooling, not in Apyx.**

**Resolution (applied).** We corrected `requirements.json` and `SPEC.md` to restore the routine/stress scope
with the explicit catastrophic exception; the Lean model's `req_buffer_non_decreasing` was already scoped to
routine operations and now matches. The proof is retained, renamed
`req_catastrophic_backstop_distributes_buffer`, as the machine-checked statement of the catastrophic
*exception* — the backstop drives the buffer to zero, which the corrected requirement excludes and
`catastrophic-backstop` mandates (this also partially closes the §6.2 gap on that requirement's second
clause). **No change to Apyx's specification or contracts was warranted.**

The methodology, the source-tracing rule this exemplifies (corpus → Solidity), and four further candidate
checks (all traced to the source and resolved — none a protocol defect) are in
[`docs/07-spec-defects.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/docs/07-spec-defects.md).

### 9.3 A self-review of this report's own model — four formalization defects, found and fixed

The activities above turn the lens on Apyx's documentation. This one turns it on **our own Lean
source**: are the theorems as strong as this report's prose says? Full findings are in
[`code_review_lean.md`](code_review_lean.md); the four that were defects rather than wording are
below. All four were **formalization** defects, not protocol defects — but the first three were
being reported as *protocol guarantees*, which is the more serious kind of error for a report like
this to make.

The fixes are grounded in the deployed contracts rather than in the documentation. `ApyUSD`'s
verified source (impl [`0xfd6165…b112`](https://etherscan.io/address/0xfd616567ecc1607f61073951a1e822f7315bb112),
OpenZeppelin upgradeable 5.5.0) and live reads are recorded in
[`deployment_ground_truth.md`](deployment_ground_truth.md).

**1. The vault priced off a stale cache, and three §4.2 rows were false because of it.**
The model stored `exchangeRate` as a field refreshed only inside vault operations, while
`creditYield`, `tick` and vesting all move the true price without touching it. `lockApxUSD` then
minted at the stale value. A fully honest trace — no compromised key — diluted an existing holder
25% while `no_dilution`'s stale-rate measure reported an *increase*.

The deployment has no stored rate at all: `totalAssets()` is a view returning
`asset.balanceOf(this) + vesting.vestedAmount()`, and every conversion recomputes off it. Read at
block ≈25,642,103, `convertToAssets(1e18)` matches `1e18 * totalAssets / totalSupply` exactly, and
`totalAssets()` exceeds the vault's own apxUSD balance by the 94,044 apxUSD then vesting. So the
cache was an artifact. `computeExchangeRate` is now the live
`((totalAssets + 1) * ray) / (totalSupply_apyUSD + 1)`, every conversion and every `step` branch
prices off it, and the field survives only as a published record. `no_dilution` and
`exchange_rate_monotone_deposit` are now about the live price and are *stronger* — their backing
and non-zero-supply side conditions are gone.

**2. `x / 0 = 0` let an address with no shares drain the vault** — and it took two passes to close.
With `exchangeRate = 0` — the `default` value — `withdrawShares` returned 0, so the share-balance
guard read `0 < 0` and passed. The `+ 1` terms above are OpenZeppelin's virtual share and virtual
asset (`_convertToShares(a,r) = a.mulDiv(totalSupply() + 10**_decimalsOffset(), totalAssets() + 1, r)`
with `_decimalsOffset() = 0`), and carrying them makes the *denominator* structurally non-zero.

**That was not sufficient, and a re-review of this fix caught it.** `computeExchangeRate` itself
still floors to 0 whenever `(totalAssets + 1) * ray < totalSupply_apyUSD + 1`, so with a funded
vault and enough shares outstanding the same drain reappeared. On-chain the real property is
stronger than a non-zero denominator: `previewWithdraw` is
`ceil(assets * (totalSupply + 1) / (totalAssets + 1))`, so for `assets ≥ 1` it is at least 1 — a
positive withdrawal always costs positive shares. `step`'s `withdraw` branch now enforces that
directly, and `Regression.lean` §R4b pins both the corner and the fix. The lesson is recorded
rather than smoothed over: "the denominator can't be zero" is not the same claim as "the quotient
can't be zero", and the first was initially written as if it settled the second.

**3. Settling a standard unlock stranded the next request.** `claimUnlock` burned the receipt but
left `unlockRequests id` and `unlockRequestId owner` set. A later `requestUnlock` topped up the
already-settled entry, and since the claim guard needs `unlockTokenOwner id = some owner` — which
the burn had cleared — the topped-up amount became **permanently unclaimable**. The deployed
`CommitToken.redeem` deletes the request in the same call that burns; the model now does too.

**4. `creditYield` credited the same dollar twice**, to `usdcReserve` *and* the vest pool,
inflating the collateral side of the solvency invariant for free. On-chain
`IVesting.depositYield` moves apxUSD into the vesting contract and touches nothing else; the USDC
redemption reserve is `RedemptionPoolV0`. Removing the double credit *strengthened* three
blast-radius results: a compromised `yieldDistributor` is now proved unable to move the reserve at
all, where before it was only proved unable to lower it.

**What the residue looks like.** The ERC-4626 inflation attack is **mitigated but not eliminated**,
and that is deliberate. `_decimalsOffset()` returns `0` — the deployment's own docstring calls it
"the decimals offset for inflation-attack protection" — and `deposit()` does not revert on zero
shares (`previewDeposit(1 wei) = 0`, read live). Modelling protection the chain does not have would
be the wrong fix, so `Regression.lean` §R3 pins the exposure instead: a victim depositing below the
share price now receives a share rather than none, but still puts in 150 and gets 117 back. The
user-side defence is the real `depositForMinShares`; the protocol-side defence is a non-zero
`_decimalsOffset`. At the vault's current 128M outstanding shares this path is not economically
live; it matters for a fresh vault or a drained one.

**Two claims withdrawn rather than fixed.** `Solvent` and `req_overcollateralization_limit`
carried a "required overcollateralization margin" term that was the `State` *field*
`overcollateralizationBuffer` — written only by `catastrophicBackstop`, and only to `0`. It was
identically zero on every reachable trace, so the margin was rhetorical; both now state exactly
what is proved. And `req_single_pending_redemption_per_user` proves the cooldown-*reset* half of
its requirement, not uniqueness; its docstring says so now, and records that the vault path is
deliberately multi-position because `withdrawForReceipt` mints a fresh receipt NFT per call.

**Still open, and reported as open:** the two defense wrappers in
[`BlastRadius.lean`](BlastRadius.lean) let the attacker supply their own clock —
`rate_limit_linear_bound`'s `advanceEpoch` and `timelock_escape_guarantee`'s `tick` are free,
permissionless counters with no relation to `Op.tick`, so neither theorem currently means "linear
in elapsed time". Until that is repaired, §5 items 2 and 3 should be read as *design suggestions*
rather than as quantified guarantees. The remaining items in
[`code_review_lean.md`](code_review_lean.md) §1.2, §2.3 and §3 are also unfixed.

---

*This report verifies an abstract model of the protocol's intended design, not the deployed Solidity
bytecode; the two can diverge (see §4.3), and it does not inspect the implementation. Questions about
protocol behavior should be verified against the deployed contracts. Generated with
[docs2formalspec](https://github.com/NyxFoundation/docs2formalspec).*
