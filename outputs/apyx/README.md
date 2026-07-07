# Apyx Protocol — Formal Verification Report

| | |
|---|---|
| **Subject system** | Apyx (apyx.fi) — apxUSD / apyUSD dividend-backed stablecoin protocol |
| **Contract addresses** (Ethereum mainnet, per ingested source docs) | apxUSD [`0x98A8…4665`](https://etherscan.io/address/0x98A878b1Cd98131B271883B390f68D2c90674665) · apyUSD [`0x38EE…8a6A`](https://etherscan.io/address/0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A) · UnlockToken [`0x9377…BF4e6`](https://etherscan.io/address/0x93775E2dFa4e716c361A1f53F212c7AE031BF4e6) |
| **Tool** | [docs2formalspec](https://github.com/NyxFoundation/docs2formalspec) (docs → RFC 2119 spec → Lean 4 machine-checked model) |
| **Report date** | 2026-07-07 |

## What this is, and what it is not

This report documents a **model-based formal verification exercise**: Apyx's public documentation was
turned into a normative RFC 2119 specification, then into a Lean 4 state-machine model of the protocol,
against which theorems are mechanically proved by the Lean 4 kernel — the strongest correctness
guarantee available (not testing, not a heuristic checker; each proof is checked by a trusted, tiny proof
kernel). Two complementary bodies of proof were produced:

1. **Requirement conformance** (§4) — 81 theorems showing the model satisfies its documented RFC 2119
   requirements (the "does it do what the docs say" question).
2. **Key-compromise blast-radius** (§6) — 56 additional theorems bounding user-asset loss when a
   privileged operator key is *stolen* (the "what if our multisig / oracle / admin gets phished" question,
   which — per Chainalysis — is the cause of ~44% of real crypto theft, not contract bugs).

**This is not a substitute for a professional smart-contract security audit** (Certora, Quantstamp, Zellic,
Halborn, etc. — Apyx already has several, see `corpus.md`). It verifies a *hand-built abstract model* of
the protocol's intended behavior, not the deployed Solidity bytecode. A property proved against this model
tells you the protocol's *design* is internally consistent on that point; it does **not** tell you the
Solidity implementation actually matches the model, and it does not check gas, storage layout, upgrade
safety, or anything outside the state machine described in [`Apyx.lean`](Apyx.lean). Treat this as a
rigorous design-level cross-check to sit alongside, not replace, an implementation-level audit.

---

## 1. Methodology

1. **Ingest** — pull the protocol's own documentation (`corpus.md`, 9 source pages under docs.apyx.fi).
2. **Extract** — LLM-assisted extraction of 82 discrete RFC 2119 requirements (`requirements.json`), each
   with a source quote, category, and a formalizability flag.
3. **Specify** — render a normative specification document (`SPEC.md`) from the extracted requirements.
4. **Formalize** — build a Lean 4 state-machine model (`Apyx.lean`): a `State` record, an `Op` type
   enumerating every protocol action, a `step : State → Op → Address → Option State` transition function
   (`none` = revert), and one theorem per formalizable requirement.
5. **Verify faithfulness** — an independent LLM judge reads each theorem's *actual formal meaning* (blind
   to its docstring) and rates it against the original requirement text: `full` / `partial` / `mismatch` /
   `unformalizable` / `missing` (`review.json`).

An automated pipeline (local-class LLMs via Ollama Cloud) ran this loop for 15 iterations and plateaued at
53% faithful coverage with 4/55 theorems mechanically proved (documented in the tool repo's
[`docs/03-eval-log.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/docs/03-eval-log.md)).
A subsequent **6-round hand-verification pass** (higher-grade model, direct Lean editing, iteratively
checked against `lake build`) took this to the results below — including finding and fixing two real
model-level gaps described in §3.

---

## 2. Reproducing / checking this report yourself

The Lean project is **mathlib-free** (zero external dependencies — see `lean/lake-manifest.json`), so
setup is minimal and compiles in seconds.

```bash
# 1. Install elan (the Lean version manager), if not already present
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell, or: source ~/.elan/env

# 2. Clone the repo
git clone https://github.com/NyxFoundation/docs2formalspec.git
cd docs2formalspec/lean

# 3. Build — elan reads `lean-toolchain` (Lean 4.31.0) and fetches it automatically on first run
lake build D2fsSpecs.Apyx
```

`lake build D2fsSpecs.Apyx` exiting `0` with no `sorry` warnings is the actual proof-checking event — the
Lean kernel re-verifies all 81 theorems from source. `outputs/apyx/Apyx.lean` (this directory) and
`lean/D2fsSpecs/Apyx.lean` are the same file (the latter is a symlink to the former), so editing/building
either location works.

To re-run the LLM faithfulness judge yourself (requires an `OLLAMA_API_KEY`, see the repo root `README.md`):

```bash
cd docs2formalspec
uv sync
uv run python -c "
import json, sys; sys.path.insert(0, 'src')
from d2fs.config import Config; from d2fs.llm import LLM
from d2fs.extract import Requirement; from d2fs.review import roundtrip_review
cfg = Config(); llm = LLM(cfg)
reqs = [Requirement(**r) for r in json.load(open('outputs/apyx/requirements.json'))]
lean_code = open('lean/D2fsSpecs/Apyx.lean').read()
print(roundtrip_review(llm, cfg, reqs, lean_code)['counts'])
"
```

Note: this judge call is itself an LLM and has observed run-to-run scoring variance of several points on
borderline `full`/`partial`/`mismatch` calls even with **zero code changes** (see §4). The figures in this
report are a **majority vote over 3 independent runs**, not a single sample.

---

## 3. Artifact map

| File | Contents |
|---|---|
| [`corpus.md`](corpus.md) | Raw ingested source documentation (9 pages from docs.apyx.fi) |
| [`requirements.json`](requirements.json) | 82 extracted RFC 2119 requirements, each with `id`, `category`, `statement`, `rationale`, `source_quote`, `formalizable` flag |
| [`SPEC.md`](SPEC.md) | Rendered RFC 2119 specification document (human-readable, organized by category) |
| [`model.md`](model.md) | Plain-English summary of the Lean state machine (actors, state variables, operations, guarantees) |
| [`Apyx.lean`](Apyx.lean) | **The formal model and all 81 requirement proofs** — `State`, `Op`, `step`, and one `theorem req_*` per formalizable requirement, each with an RFC 2119 docstring |
| [`BlastRadius.lean`](../../lean/D2fsSpecs/BlastRadius.lean) | **The 56 key-compromise blast-radius proofs** (§6) — trace executor, per-role damage bounds, and the rate-limit / timelock defense wrappers, all imported from and additive to `Apyx.lean` (which it leaves untouched) |
| [`leancheck.json`](leancheck.json) | Compile status: `81` requirement theorems, `0` sorry, `0` vacuous, `81` mechanically proved |
| [`review.json`](review.json) | Faithfulness verdicts (majority vote over 3 runs) + per-requirement vote records |
| [`review_run1.json`](review_run1.json), [`review_run2.json`](review_run2.json), [`review_run3.json`](review_run3.json) | Raw per-run judge output, kept for reproducibility of the majority vote |
| [`archive/`](archive/) | Prior automated-pipeline runs (Run 2, 9, 11, 12, 13), kept for comparison |

---

## 4. What was formally verified (81 theorems, 0 `sorry`, mechanically checked)

Every theorem in `Apyx.lean` is a **completed, checked proof** — no admitted/skipped steps. Highlights,
by category:

**Access control & custody**
- Mint/redeem restricted to whitelisted, non-denylisted addresses; deposit/mint revert while paused or
  denylisted (`req_mint_access_whitelist`, `req_global_pause_blocks_deposit`, `req_denylist_blocks_deposit`).
- Vault-held apxUSD only ever moves via the accounting paths already in the model (lock/withdraw/redeem) —
  proved by exhaustive case analysis over the closed operation type, i.e. **no rehypothecation/lending path
  exists** in the model (`req_no_rehypothecation`).
- The UnlockToken registry is a genuine singleton with a fixed operator (the vault), which may claim on a
  user's behalf once cooldown has elapsed (`req_singleton_unlock_token_instance`,
  `req_vault_operator_of_unlock_token`).
- `apxUSD_unlock` positions are never transferable or cancellable once created — proved by exhaustive case
  analysis (`req_unlock_token_nontransferable`, `req_unlock_cannot_be_cancelled`).

**Pricing & solvency**
- Standard minting (`depositUSDC`) always prices at exactly $1/unit, unconditionally; the separate
  arbitrage pathway (`mintApxUSD`) also prices at $1 but only executes while apxUSD trades above $1
  (`req_mint_price`, `req_mint_price_arbitrage_pathway`, `req_arbitrage_mint_access`).
- The overcollateralization invariant is preserved across (most) operations, under stated well-formedness
  hypotheses (`req_overcollateralization_limit`).
- The apyUSD/apxUSD exchange rate is non-decreasing; yield vests linearly and completes in exactly the
  configured period (`req_apyusd_value_increase`, `req_linear_vest_implementation`,
  `req_yield_distribution_period`).
- The ERC-4626 vault surface (`convertToShares`/`Assets`, `preview*`, `max*`) is internally consistent and
  correctly gated by the pause flag (`req_erc4626_compliance`).

**Timing**
- Redemption/unlock cooldown enforced at exactly 20 days; flexible-redemption minimum claim at 3 days;
  the early-unlock fee declines linearly from 3.5% to a 0.1% floor (`req_redemption_cooldown_period`,
  `req_flexible_redemption_claim_minimum`, `req_early_unlock_fee_linear_decline`).
- Monthly yield-rate setting can only occur once every 30 days, and the accepted rate is bounded by the
  recorded prior month's collateral-derived yield (`req_monthly_yield_rate_set`) — this required **adding
  a calendar/cadence concept to the model** (`lastRateSetTime`, `collateralYieldBase`), since the original
  model had no notion of monthly timing at all.

**Two real defects were found and fixed as a byproduct of this exercise** (not in the deployed contracts —
in this formal *model's* original construction, then corrected):
- `claimUnlock`/`flexibleClaimUnlock` had **no caller authorization check at all** — any address could
  trigger a claim on behalf of any other address's pending unlock position. Fixed by requiring
  `caller = owner ∨ caller = unlockTokenOperator`, and then proving the vault genuinely can act as
  authorized operator.
- A knock-on edit to `req_mint_price` briefly (in an intermediate, never-released commit) required the
  arbitrage market-price condition for the *standard* $1-pricing guarantee, which would have been an
  under-claim of the standard mint path's guarantee. Caught and fixed before being reported as final.

Full per-requirement detail (docstrings citing the exact RFC 2119 text, alongside each proof) is in
`Apyx.lean`; a build-time compile status is in `leancheck.json`.

---

## 5. What was NOT formally verified

### 5.1 Out of scope by nature (5 requirements, not attempted)

These describe off-chain processes or qualitative/UI behavior that a smart-contract state machine cannot
express, and were flagged as such during requirement extraction rather than during formalization:

| Requirement | Why out of scope |
|---|---|
| `offchain-allocation` — treasury must allocate capital to preferred assets/bonds | Off-chain treasury operations, not on-chain state |
| `custody-attestation` — regular third-party attestations required | Off-chain reporting process |
| `liquidity-buffer-size` — buffer sized against historical TVL drawdowns | Requires external market-data comparison, not a state invariant |
| `buffer-growth-stress` — buffer grows during stress rather than being drained | Duplicate of `overcollateralization-limit`'s intent, expressed qualitatively |
| `jurisdiction-restriction-frontend` — frontend blocks restricted jurisdictions | Frontend/UI behavior, not contract state |

### 5.2 Genuinely unformalizable against this model (2 requirements, attempted and declined)

Both were re-examined after 3 rounds of model extension (which resolved 6 *other* previously-unformalizable
requirements) and are still honestly declined — confirmed unanimous across all 3 independent judge runs:

- **`price-may-include-spreads`** — "The protocol MAY reflect spreads and offchain execution expenses in
  the price during minting and redemption." The model prices all mints hard-coded 1:1; there is no spread
  parameter to witness this permissive (MAY) clause either way.
- **`rebalance-overcollateralization`** — "The system SHALL rebalance the collateral basket so that apxUSD
  remains over-collateralized." The model tracks only an aggregate `totalCollateralValue`, not basket
  composition, and has no active rebalancing operation — only the *passive* invariant
  (`overcollateralization-limit`) is modeled.

### 5.3 Formalized but judged not fully faithful (2 requirements)

Both compile and are proved — they are not `sorry` or vacuous — but an independent reading of the theorem's
actual formal content was judged to assert something narrower or different from the source requirement:

- **`token-no-rebase`** — "apyUSD MUST NOT rebase; balances change only via transfers, minting, or
  burning." The current theorem restricts balance changes to the three ops that mint/burn apyUSD in this
  model (`lockApxUSD`, `withdraw`, `redeem`) but the model has no explicit peer-to-peer apyUSD *transfer*
  operation to include in that list, which a strict reading of the requirement expects.
- **`pay-to-non-cooldown`** — "Yield MUST be paid to all apyUSD tokens not currently undergoing cooldown."
  The current theorem proves every current apyUSD holder's redeemable value strictly increases on
  `creditYield`, without separately quantifying over an explicit "not in cooldown" set (holders who *are*
  in cooldown have, in this model, already exited `apyUSDBal` into the unlock registry, so the claim is
  true by construction — but the judge wants the cooldown condition stated explicitly rather than implied).

### 5.4 Faithful-but-partial coverage (49 of 77 formalizable requirements)

The majority of formalized requirements (`partial` verdict) capture the *core* normative behavior but not
every clause of the source text — e.g. a theorem proving a redemption's dollar-value calculation without
also asserting the emitted event's exact parameter list. See `review.json` → `results[].note` for the
specific gap on any individual requirement.

---

## 6. Key-compromise blast-radius analysis (56 theorems, 0 `sorry`)

The §4 requirement proofs assume every actor behaves as documented. This section answers a different,
harder question that documentation never addresses: **if a privileged operator key is stolen — the
social-engineering / infrastructure-compromise threat that caused the Bybit $1.5B loss and ~44% of 2024
crypto theft — how much can the attacker take?** All proofs are in
[`BlastRadius.lean`](../../lean/D2fsSpecs/BlastRadius.lean), machine-checked, additive to and leaving
`Apyx.lean` untouched.

The threat model: the attacker holds the private key of one or more role addresses (`admin`, `oracle`,
`pauseController`, `yieldDistributor`) and may submit an arbitrary sequence of operations from those
addresses, interleaved with honest traffic (modeled by `execTrace`, with reverted operations skipped).

### 6.1 Results about the current protocol model

**No single stolen key can extract principal.** Proved for each role, over arbitrary-length attack traces:

| Stolen key | Proved blast radius | Theorem |
|---|---|---|
| `pauseController` | Liveness only (can freeze the protocol; touches no balance) | `pauser_trace_blast_radius` |
| `yieldDistributor` | Can only *donate* into the vest pool; never debits any holding | `yield_distributor_trace_blast_radius`, `distributor_compartmentalized` |
| `oracle` | Zero balance movement — can only shift price *parameters* | `oracle_alone_preserves_balances` |
| `admin` | Cannot move any balance/supply field (only policy parameters) | `admin_cannot_touch_balances` |
| **any / all of the above** | A user who signs nothing and isn't RFQ-targeted loses **nothing** | `user_assets_immune_to_total_key_compromise`, `no_theft_ledger` |

The headline: **even with every operator key stolen at once, a passive user's four balances cannot
decrease** (`user_assets_immune_to_total_key_compromise`). This is the formal, machine-checked version of
"non-custodial: we cannot move your funds even if we wanted to." Its active complement is also proved —
there is no operation sequence by which *any* caller mints apxUSD for free; every credit is backed by an
equal USDC payment or the settlement of the recipient's own pre-existing locked position
(`apxUSD_credit_is_backed`).

**The one total-loss path — a two-key coalition.** The proofs isolate exactly one way user principal can be
drained, and it requires **two** compromised roles acting together: `admin` **+** an approved RFQ
counterparty (`admin_rfq_coalition_drains`). The admin drives `redemptionValue` to 0 (via
`catastrophicBackstop`, which has no lower bound / clamp in the model), after which the RFQ counterparty's
`executeRFQRedemption` burns a victim's apxUSD for **exactly 0 USDC**. The proofs pin this to precisely two
channels (`redemption_price_admin_only`, `reserve_outflow_only_via_redemption`), and show it is *unbounded*:
redemption payout is exactly `amount × redemptionValue / ray` with no in-model cap on `redemptionValue`
(`redeem_payout_formula`, `redeem_payout_has_no_cap`).

**Actionable conclusion for Apyx:** user funds' safety against a compromised admin rests entirely on (a)
the trustworthiness of the approved RFQ counterparty set, and (b) the *absence* of three defenses the
current model lacks — a redemption-price floor, a withdrawal rate limit, and a timelock on admin changes.
(This mirrors Yearn's real-world finding that Apyx's `ApxUSDRateOracle.setRate` sits behind a 0-second
timelock.)

### 6.2 Design theorems — what the missing defenses would guarantee

To quantify the value of the defenses (a)–(b), two are formalized as *wrappers* over the base model and
proved to deliver hard guarantees. **These describe mechanisms the current protocol does not have** — they
are recommendations backed by proof, not properties of the deployed system:

- **Rate limit** (`rate_limit_linear_bound`): with a per-epoch outflow cap, cumulative reserve loss is
  provably `≤ cap × (epochs elapsed + 1)` — i.e. **damage is at most linear in time**, no matter how an
  all-keys attacker sequences operations. (ERC-7265-style circuit breaker.)
- **Timelock / escape hatch** (`timelock_escape_guarantee`): with a delay queue on privileged operations, a
  queued admin change provably cannot take effect until `delay` ticks after it was queued — a **guaranteed
  window for users to exit** before any change lands. The base model is separately proved to have *no* such
  window (`base_model_has_no_timelock`: admin changes take effect in the same step, instantly).

### 6.3 Scope and honesty caveats

Same model-level caveat as §"What this is not": these are properties of the abstract Lean model, not the
deployed Solidity. The §6.2 wrapper theorems are explicitly about *hypothetical* defenses. Of the 56
theorems, 55 depend only on Lean's standard `propext`/`Quot.sound` axioms and one
(`admin_rfq_coalition_drains`) additionally on `Classical.choice` — all three are the standard trusted
axioms of Lean's logic; none is `sorry` or an unproved assumption. Full method and the T1–T10 theorem
roadmap: [`docs/05-blast-radius.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/docs/05-blast-radius.md).

---

## 7. Coverage summary

| Metric | Value |
|---|---|
| Requirements extracted | 82 (77 formalizable, 5 out of scope — §5.1) |
| Lean 4 compilation | Passes (`lake build D2fsSpecs`, zero errors/warnings) |
| Requirement theorems proved (§4) | **81 / 81 (100%, zero `sorry`, zero vacuous)** |
| Blast-radius theorems proved (§6) | **56 (zero `sorry`, zero vacuous)** |
| Faithful coverage (full + partial, majority of 3 judge runs) | **73 / 77 = 94.8%** |
| — of which fully faithful (`full`) | 24 |
| — of which partially faithful (`partial`) | 49 |
| Judged not fully faithful (`mismatch`) | 2 (§5.3) |
| Genuinely unformalizable against this model (`unformalizable`) | 2 (§5.2) |

**Methodology caveat**: the faithfulness judge is itself an LLM. Re-running it against the *identical,
unchanged* Lean code produced 92.2%, 96.1%, and 94.8% full+partial coverage across 3 independent runs —
a real measurement variance, not a code regression. The 94.8% figure above is the per-requirement
**majority vote** across those 3 runs, which is more reliable than any single run but should still be read
as "approximately mid-90s%," not an exact figure.

---

*This report and all underlying artifacts are generated by [docs2formalspec](https://github.com/NyxFoundation/docs2formalspec),
an open-source tool, and are provided as-is for Apyx's own review. Questions about the tool or methodology:
see the tool repository. Questions about protocol behavior itself should be directed to the Apyx team and
verified against the deployed contracts, which this report does not inspect.*
