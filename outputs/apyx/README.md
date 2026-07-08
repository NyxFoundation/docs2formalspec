# Apyx Protocol — Formal Verification Report

| | |
|---|---|
| **Subject** | Apyx (apyx.fi) — the apxUSD / apyUSD dividend-backed stablecoin protocol |
| **Contracts** (Ethereum mainnet, per the ingested documentation) | apxUSD [`0x98A8…4665`](https://etherscan.io/address/0x98A878b1Cd98131B271883B390f68D2c90674665) · apyUSD [`0x38EE…8a6A`](https://etherscan.io/address/0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A) · UnlockToken [`0x9377…BF4e6`](https://etherscan.io/address/0x93775E2dFa4e716c361A1f53F212c7AE031BF4e6) |
| **Method** | RFC 2119 specification → Lean 4 state-machine model → machine-checked theorems |
| **Result** | 167 theorems proved, 0 `sorry`, kernel-verified (`lake build`, Lean 4.31.0). No defect was found in Apyx's protocol or documentation; §9 records one *extraction* artifact in our own tooling. |
| **Date** | 2026-07-07 |

---

## 1. Summary

Apyx's public protocol documentation was formalized into (a) a normative RFC 2119 specification
([`SPEC.md`](SPEC.md)) and (b) an executable Lean 4 model of the protocol's state machine
([`Apyx.lean`](Apyx.lean)). Against that model we proved **167 theorems**, each re-checked from
source by the Lean kernel, in four groups:

| Group | Question answered | Count | File |
|---|---|---|---|
| **Requirement conformance** | Does the design behave as the documentation specifies? | 82 | [`Apyx.lean`](Apyx.lean) |
| **Key-compromise blast radius** | If a privileged operator key is stolen, how much can be lost? | 56 | [`BlastRadius.lean`](BlastRadius.lean) |
| **Design safety** | Can an ordinary user drain the protocol using only legitimate calls? | 28 | [`Safety.lean`](Safety.lean) |
| **Spec-defect search** | Is the requirement set itself internally consistent? | 1 | [`SpecDefects.lean`](SpecDefects.lean) — surfaced an *extraction* artifact only (§9) |

Headline findings for Apyx:

- **Non-custodial guarantee holds.** Even with *every* operator key stolen simultaneously, a user who
  signs nothing and is not targeted by an approved RFQ counterparty cannot lose any balance (§4.2).
- **One structural total-loss path exists** — and it requires **two** roles colluding (admin + an approved
  RFQ counterparty), because the model has no lower bound on the redemption price (§4.2, §5).
- **The vesting logic is correct.** Formalizing it prompted a close reading of `LinearVestV0.sol`, which
  confirmed the deployed two-accumulator vesting design does not forfeit accrued yield (§4.3).
- **No contradiction in Apyx's own documentation.** A consistency search flagged an apparent conflict
  between two *extracted* requirements, but tracing it to the source docs showed the source is consistent —
  the conflict was an artifact of our automated extraction over-generalizing one requirement (§9). No change
  to Apyx's spec is warranted; the fix is in our tooling.
- **Design recommendations** (a redemption-price floor, a withdrawal rate limit, and an admin timelock)
  are backed by proof: §5 shows exactly what each would guarantee.

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

- The apyUSD/apxUSD exchange rate is non-decreasing.
- Vesting is linear: nothing releases before the clock anchor, the released amount grows monotonically with
  time, never exceeds the pool, and equals the full pool once a period has elapsed.
- Crediting new yield preserves already-accrued yield (`req_credit_preserves_accrued_vest`); the monthly
  rate is bounded by the recorded prior-month dollar collateral yield.

### Collateral & solvency
`req_overcollateralization_limit`, `req_buffer_non_decreasing`, `req_buffer_preservation`,
`req_buffer_not_consumed`, `req_catastrophic_backstop`.

- The overcollateralization invariant is preserved across operations (under the stated well-formedness
  conditions; the solvency-breaking operations are explicitly excluded and documented).
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
| `oracle` | No balance movement; can only shift price parameters | `oracle_alone_preserves_balances` |
| `admin` | Cannot move any balance/supply field, only policy parameters | `admin_cannot_touch_balances` |
| **all keys at once** | A passive, non-RFQ-targeted user loses nothing | `user_assets_immune_to_total_key_compromise`, `no_theft_ledger` |

The non-custodial headline (`user_assets_immune_to_total_key_compromise`) is the machine-checked form of
"we cannot move your funds even if we wanted to." Its active complement is also proved: no operation
sequence lets any caller mint apxUSD for free — every credit is backed by an equal USDC payment or the
settlement of the recipient's own pre-existing locked position (`apxUSD_credit_is_backed`).

Supporting theorems include the exact per-role effect frames (`admin_frame`, `oracle_frame`,
`yield_distributor_frame`, and the `step_*_exact` family), the non-custodial lemmas
(`no_role_transfers_user_funds`, `no_role_burns_user_shares`, `no_role_debits_usdc`,
`governance_token_balances_immutable`, `no_role_seizes_unlock_position`), and the extraction-channel
characterizations (`redemption_price_admin_only`, `reserve_outflow_only_via_redemption`).

**The one total-loss path is a two-key coalition** (`admin_rfq_coalition_drains`): the admin drives the
redemption value to 0 via `catastrophicBackstop` (which has no lower bound in the model), after which an
approved RFQ counterparty's `executeRFQRedemption` burns a victim's apxUSD for **0 USDC**. The redemption
payout is exactly `amount × redemptionValue / ray` with no cap on `redemptionValue`
(`redeem_payout_formula`, `redeem_payout_has_no_cap`) — so the loss is unbounded. This directly motivates
the recommendations in §5.

### 4.2 Design safety — honest-actor attacks (24 theorems, [`Safety.lean`](Safety.lean))

This group assumes every actor is honest and asks whether the *design itself* lets an ordinary attacker
extract value using only legitimate operations.

| Property | Guarantee | Theorem |
|---|---|---|
| No free value | No operation sequence lets any address mint apxUSD from nothing | `no_free_value_trace` |
| Solvency preserved | Minted apxUSD never exceeds collateral across any trace (under stated well-formedness) | `solvency_preserved` |
| Rounding favors the protocol | Conversions never credit the user free value; withdrawals round up in shares | `rounding_favors_protocol`, `withdrawShares_rounds_up` |
| No dilution | A deposit by someone else never lowers an existing holder's redeemable value | `no_dilution` |
| Inflation-attack immunity | The ERC-4626 first-depositor / donation attack is structurally impossible — there is no raw donation primitive; every vault-asset increase is matched by a share mint | `donation_free`, `no_inflation_attack` |
| No free extraction | A caller cannot end richer than they started (single-step, fixed reference rate) | `caller_net_nonpositive`, and the `caller_value_*` family |
| No early yield drain | Vested yield cannot be pulled forward faster than its linear schedule | `vest_no_early_drain` |
| Vesting conservation | Both crediting new yield and reconfiguring the vesting period preserve already-accrued yield | `creditYield_preserves_accrued_vest`, `setVestPeriod_preserves_accrued_vest` |
| No peg-spread round trip | The arbitrage mint (needs price > $1) and arbitrage redeem (needs price < $1) require opposite price regimes, so no single state enables both | `no_same_state_arbitrage_round_trip` |
| Redemption request is backed | A redemption request burns exactly the requested apxUSD and leaves the caller one tracked position — the obligation exactly equals the burn (no free claim) | `requestUnlock_backs_claim_by_burn` |
| No free extraction (trace) | Over arbitrary traces of non-share operations, no address's fixed-rate holdings can increase — no free money through the redemption / RFQ / request channels at any length (the share-op + live-rate closure is left open, see §6.2) | `caller_net_nonpositive_trace` |

### 4.3 The vesting cross-check (a positive finding)

Formalizing the vesting logic raised a specific question: does crediting new yield forfeit yield that has
already accrued but not yet been pulled into the vault? Checking the deployed contract answered it:
`LinearVestV0.sol`'s `depositYield` executes `fullyVestedAmount += newlyVestedAmount()` **before** resetting
the vesting clock, so accrued yield is preserved in a second accumulator. The Lean model was aligned to that
two-accumulator design, and the preservation is now proved for both code paths that restart the clock
(`creditYield_preserves_accrued_vest`, `setVestPeriod_preserves_accrued_vest`). **The deployed vesting
design is correct on this point.**

---

## 5. Design recommendations for Apyx

These follow directly from the proofs above. Items 1–3 are the defenses whose *absence* is the reason the
two-key coalition (§4.1) is unbounded; where a defense is formalized, the theorem naming what it would
guarantee is cited.

1. **Add a redemption-price floor.** The single unbounded loss path exists purely because `redemptionValue`
   has no lower clamp; `catastrophicBackstop` can drive it to 0. A floor (or a bounded per-update move)
   removes the total-loss outcome of the admin + RFQ coalition.

2. **Add a withdrawal / redemption rate limit** (ERC-7265-style circuit breaker). Formalized as a wrapper
   over the model and proved to bound cumulative reserve loss to `≤ cap × (epochs elapsed + 1)` — i.e.
   damage becomes at most **linear in time** regardless of how an all-keys attacker sequences operations
   (`rate_limit_linear_bound`).

3. **Add a timelock on privileged admin changes.** The base model is proved to have **no exit window** —
   admin changes take effect in the same block (`base_model_has_no_timelock`,
   `catastrophicBackstop_is_instantaneous`). A delay queue is formalized and proved to give users a
   guaranteed window to exit before any queued change lands (`timelock_escape_guarantee`). (This mirrors the
   external observation that `ApxUSDRateOracle.setRate` currently sits behind a 0-second timelock.)

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

7. **Commission an implementation-level (bytecode) audit** for the classes this model cannot reach —
   reentrancy, flash-loan composition, gas/storage, and upgrade safety (§6).

---

## 6. Out of scope and not provable against this model

Reported honestly so the boundary of these guarantees is clear.

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
  matching the deployed `ApxUSDRateOracle`) **is** proved (`req_catastrophic_backstop`), and the resulting
  buffer-to-zero effect is proved in `SpecDefects`; a genuine *per-holder* pro-rata split requires a
  `Σ_holder reserve · balance/totalSupply` over the holder set, but balances are aggregate `Address → Nat`
  maps with no summation structure — the same
  limitation that makes `solvency_preserved` take well-formedness as a hypothesis.
- **`caller_net_nonpositive`, trace-level closure** — the value-weighted no-free-money property is proved
  single-step at a fixed reference rate; extending it to arbitrary traces under a *moving* exchange rate is a
  distinct, genuinely hard arithmetic problem and is flagged as open rather than claimed.

### 6.3 Requires a mechanism the model does not have (declined)
- **`price-may-include-spreads`** — a permissive (MAY) clause; the model prices mints hard-coded 1:1 and has
  no spread parameter to witness it either way.
- **`rebalance-overcollateralization`** — the model tracks only aggregate collateral value, not basket
  composition, and has no active rebalancing operation (only the passive invariant is modeled).

### 6.4 Outside any state-machine model (bytecode-audit territory)
Reentrancy, cross-protocol flash-loan composition, implementation-level input validation, gas, storage
layout, and upgrade safety cannot be expressed in this atomic transition model. These are the subject of an
implementation-level audit (recommendation §5.7).

---

## 7. Verifying this report yourself

The Lean project is dependency-free (no mathlib) and compiles in seconds.

```bash
# 1. Install elan (the Lean toolchain manager), if not already present
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell, or: source ~/.elan/env

# 2. Build — elan reads lean-toolchain (Lean 4.31.0) and fetches it automatically
cd lean
lake build
```

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
| [`Safety.lean`](Safety.lean) | The 28 design-safety proofs |
| [`SpecDefects.lean`](SpecDefects.lean) | The machine-checked specification-contradiction proof (§9) |
| [`leancheck.json`](leancheck.json) | Build status: requirement theorems, `sorry` count, vacuous count |
| [`corpus.md`](corpus.md) | The raw ingested source documentation |

---

## 9. A consistency check on the requirements — an extraction artifact, now fixed

The three groups above take the specification as the reference. This one turns the lens on the extracted
requirement set itself: **are the requirements mutually consistent?** The check flagged one apparent conflict:

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

The methodology, the source-tracing rule this exemplifies, and four further candidate checks (in progress) are
in [`docs/07-spec-defects.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/docs/07-spec-defects.md).

---

*This report verifies an abstract model of the protocol's intended design, not the deployed Solidity
bytecode; the two can diverge (see §4.3), and it does not inspect the implementation. Questions about
protocol behavior should be verified against the deployed contracts. Generated with
[docs2formalspec](https://github.com/NyxFoundation/docs2formalspec).*
