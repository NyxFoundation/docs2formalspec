**Apyx Protocol – Formal State‑Transition Model**  
*(Lean-synchronized public model, 2026-08-11)*

This document describes the current `State`, `Op`, and `step` definitions in [`Apyx.lean`](Apyx.lean).
The model is an abstract design model, not a Solidity refinement proof. Successful steps return
`some State`; reverted steps return `none` and are skipped by `execTrace`. The companion modules add
ledger, registry, pending-liability, holder-value, and deployment-derived boundaries.

The current assurance boundaries are implemented inside this existing model. `Apyx.lean` projects the concrete state into
`LedgerState`, `VaultState`, `RedemptionState`, `ReserveState`, `AuthorityState`, `OracleState`,
`TimeState`, and `ExternalState`; `AuthorityState.roleGraph` names the four model-level caller
capabilities; `Phase.lean` classifies every operation into a security family and an exhaustive
`AccountingEffect`; and `BlastRadius.lean` states the passive-holder trace and total-key threat
assumptions used by the nominal-balance theorem. `Phase.lean` also exposes an operation-contract
coverage entry for every `Op`, with separate precondition, postcondition, revert, frame, and
relational statuses. Those entries are an honest coverage index: many are still `incomplete`,
`notModeled`, or `handoff`, and therefore are not proofs. These are views over the single transition
model, not a second unconnected model. The user-facing distinction remains important: nominal balance
preservation is not economic-value preservation, and model theorems are not bytecode-refinement
theorems.

The projections are connected back to the existing proofs rather than being documentation-only:
`Invariant.lean` defines `ProtocolViewInvariant` and derives it from
`ProtocolInvOutstanding`, while `Init.lean` lifts the reachable `ProtocolInvFull` theorem to
`protocolInvFull_reachable_view`. The total-key isolation theorem consumes both the explicit
`AttackerTrace` capability premise and the passive-holder/victim restriction.

The attack-pattern index in `BlastRadius.lean` has the same discipline. Each of the nine normalized
patterns carries a source PoC/corpus link, root cause, attacker capability, preconditions, trace
skeleton, target assets, loss metric, Apyx mapping, model status, implementation status, and human-review
status. `attackPatternCatalog_records_are_complete` checks that the required record fields are present;
it does not claim that the corresponding implementation is resistant.

---

### 1. Actors  

| Actor | Role |
|-------|------|
| **User** | Holds USDC, apxUSD, apyUSD; initiates deposit, mint, lock, unlock, redeem. |
| **Off‑chain Treasury** | Custodies the collateral basket; provides attestations. |
| **apyUSD Vault (ERC‑4626)** | Accepts apxUSD, mints apyUSD, streams yield, coordinates unlocks. |
| **UnlockToken** | Issues non‑transferable `apxUSD_unlock` NFTs; enforces 20‑day cooldown. |
| **YieldDistributor** | Credits converted USDC to the vault each month. |
| **LinearVestV0** | Holds vested yield; releases it linearly over a configurable period. |
| **Governance** | Votes on buffer deployment, pause, list management. |
| **Pause Controller** | Toggles the global‑pause flag. |
| **Whitelist / Deny‑list Manager** | Maintains address‑based access control. |
| **RFQ Counterparty** | Executes approved redemption requests. |

---

### 2. State Variables  

| Variable | Type | Meaning |
|----------|------|---------|
| `totalSupply_apxUSD` | `uint256` | Total minted apxUSD (1 apxUSD ≈ $1). |
| `totalSupply_apyUSD` | `uint256` | Total minted apyUSD shares. |
| `redemptionValue` | `uint256` (ray, 1e27) | Per-apxUSD redemption price in USDC (`1e27` = $1.00); redeeming `amount` apxUSD pays `amount·redemptionValue/1e27` USDC. Corresponds to **`RedemptionPoolV0.exchangeRate`** — the value that actually prices a redemption (`previewRedeem = assetsAmount·exchangeRate/1e18/10^|assetDec−reserveDec|`). **Scale differs**: the contract is `1e18`, the model is `ray = 1e27`; only the dimension (per-unit, not aggregate) is shared. Not `ApxUSDRateOracle.rate` — see §5. |
| `totalCollateralValue` | `uint256` | Full value of the reserve (collateral basket + buffer). |
| `overcollateralizationBuffer` (derived) | `uint256` | `max(0, totalCollateralValue − totalSupply_apxUSD·redemptionValue/1e27)` — the excess of collateral over the outstanding redemption obligation. |
| `overcollateralizationBuffer` (**field**) | `uint256` | A *different object* from the derived function above, and never synchronised with it. Written by exactly one operation — `catastrophicBackstop`, which sets it to `0` — and `0` in the default state, so it is identically zero on every reachable trace. It is not used as a required-margin term in the solvency invariant (`README` §9.3). |
| `exchangeRate` | `uint256` (ray, 1e27) | **A published record, not a pricing input.** The deployed `ApyUSD` stores no rate: `totalAssets()` is a `view` returning `asset.balanceOf(this) + vesting.vestedAmount()` and every conversion recomputes off it. So the model prices everything off the derived `computeExchangeRate s = ((totalAssets s + 1) * ray) / (totalSupply_apyUSD + 1)`, and this field only records the last published value. The `+1` terms are OpenZeppelin's virtual share and virtual asset (`_decimalsOffset() = 0`); they also make the denominator structurally non-zero. See §5 and `README` §9.3. |
| `cooldownEnd[user][requestId]` | `uint256` (timestamp) | Time after which the unlock token may be redeemed. |
| `whitelist[address]` | `bool` | `true` ⇒ address may mint/redeem. |
| `denylist[address]` | `bool` | `true` ⇒ address blocked from deposit/mint. |
| `globalPause` | `bool` | `true` ⇒ all deposit/mint ops revert. |
| `yieldRateMonth` | `uint256` (basis points) | Monthly yield applied to the vault’s assets. |
| `vestPeriod` | `uint256` (seconds) | Linear vesting period for `LinearVestV0`. |
| `vestTotal` (contract: `vestingAmount`) | `uint256` | The unvested yield pool, vesting linearly from `vestStart` over `vestPeriod`. |
| `fullyVestedAmount` | `uint256` | Yield that has already vested but not yet been pulled into the vault. Preserved across deposits/period-changes (`vestedAmount = fullyVestedAmount + newlyVested`). |
| `unlockTokenId → (owner, amount, requestTime)` | `struct` | NFT representing a pending unlock. |
| `unlockTokenAddress` | `address` (constant) | Identifies the single UnlockToken contract instance holding the unlock registry. |
| `unlockTokenOperator` | `address` | Address authorized to initiate a claim on behalf of a recorded unlock-position owner (the apyUSD vault). |
| `apxUSDMarketPrice` | `uint256` (ray, 1e27) | Current secondary-market trading price of apxUSD, reported by the price oracle; the arbitrage mint pathway is only open while this exceeds 1e27 ($1.00). |
| `lastRateSetTime` | `uint256` (timestamp) | Cadence anchor for `setYieldRate`: the next setting only succeeds once `monthPeriod` (30 days) has elapsed since this. |
| `collateralYieldBase` | `uint256` (USD‑cents) | Prior month's collateral-base yield figure; the next month's rate must be bounded by this. |

---

### 3. Operations  

| Operation | Inputs | Preconditions (must hold) | Effects (state updates & external calls) |
|-----------|--------|---------------------------|------------------------------------------|
| **depositUSDC** *(standard mint pathway)* | `amount` (USDC) | `!globalPause` ∧ `whitelist[msg.sender]` ∧ `!denylist[msg.sender]` ∧ `amount ≤ balanceUSDC(msg.sender)` | Off‑chain Treasury receives `amount`; `totalSupply_apxUSD += amount`; ERC‑20 `apxUSD.mint(msg.sender, amount)` at $1/unit, unconditionally (the abstract dispatcher permits the zero amount). |
| **mintApxUSD** *(arbitrage pathway)* | `to`, `amount` | `!globalPause` ∧ `whitelist[msg.sender]` ∧ `!denylist[msg.sender]` ∧ `!denylist[to]` ∧ **`apxUSDMarketPrice > 1e27`** (apxUSD trading above $1) ∧ `amount ≤ balanceUSDC(msg.sender)` | Transfer USDC to Treasury; `totalSupply_apxUSD += amount`; ERC‑20 `apxUSD.mint(to, amount)` at $1/unit. |
| **lockApxUSD** | `amount` | `!globalPause` ∧ `!denylist[msg.sender]` ∧ `balanceOf_apxUSD(msg.sender) ≥ amount`; a positive amount is rejected only when the live model rate floors to zero | `apxUSD.transferFrom(msg.sender, vault, amount)`; `shares = amount * 1e27 / computeExchangeRate(s)` — the **live** rate; `totalSupply_apyUSD += shares`; `apyUSD.mint(msg.sender, shares)`. Floor rounding means a deposit below the current share price can mint zero shares, matching `previewDeposit(1 wei) = 0` read on-chain. |
| **requestUnlock** *(standard redemption request)* | `amount` | `!globalPause` ∧ `!denylist[msg.sender]` ∧ `balanceOf_apxUSD(msg.sender) ≥ amount` | Burn `amount` **apxUSD** from `msg.sender`; in this request registry, a repeat request tops up the same pointed-to position and resets its cooldown. Vault receipts are a separate fresh-position path. |
| **claimUnlock** | `requestId` | Recorded request/receipt; `!globalPause` ∧ `!denylist[owner]` ∧ `(msg.sender == owner ∨ msg.sender == unlockTokenOperator)` ∧ `block.timestamp ≥ cooldownEnd[requestId]` | Burn NFT; `apxUSD.mint(owner(requestId), amount)`; **retire the position** — clear `unlockRequests[requestId]` *and* the owner's `unlockRequestId` pointer (`retireStandardUnlock`). |
| **redeemApxUSD** *(arbitrage redemption pathway)* | `amount` | `!globalPause` ∧ `!denylist[msg.sender]` ∧ `whitelist[msg.sender]` ∧ **`apxUSDMarketPrice < 1e27`** ∧ `balanceOf_apxUSD(msg.sender) ≥ amount` ∧ reserve suffices ∧ the step does not decrease the derived buffer | Burn `amount` apxUSD; `usdcReserve -= amount·redemptionValue/1e27`; `USDC.transfer(msg.sender, amount·redemptionValue/1e27)`. |
| **withdraw** | `assets`, `receiver` | `!globalPause` ∧ both caller/receiver are not deny-listed ∧ `receiver = msg.sender` ∧ positive assets require a positive `withdrawShares(assets, computeExchangeRate(pullVestedYield(s)))` quote ∧ caller has the shares ∧ vault has the assets | Pull vested yield; compute the live rate; burn the ceil-rounded share amount; deposit `assets` into `UnlockToken` as a fresh position with a 20-day cooldown. |
| **redeem** | `shares`, `receiver` | `!globalPause` ∧ `balanceOf_apyUSD(msg.sender) ≥ shares` ∧ vault holds enough apxUSD after pulling vested yield | Pull vested yield **first**, then price: `assets = shares·computeExchangeRate(pullVestedYield s)/1e27`. The deployment does the same, with the comment "Pull vested yield so liquid assets match `totalAssets()`". Burn `shares` apyUSD; `vaultApxUSDBal -= assets`; open a standard unlock position for `receiver` (`assets`, 20-day cooldown) — a **fresh** position per call, matching `redeemForReceipt`, which mints a new `UnlockReceipt` and returns its own `tokenId`. |
| **flexibleRequestUnlock** | `amount` | `!globalPause` ∧ `!denylist[msg.sender]` ∧ `balanceOf_apxUSD(msg.sender) ≥ amount` | Burn `amount` apxUSD; open a *flexible* unlock position (records `requestTime`); multiple concurrent flexible requests are allowed. |
| **flexibleClaimUnlock** | `requestId` | `!globalPause` ∧ `!denylist[owner]` ∧ (owner ∨ operator) ∧ `now ≥ requestTime + 3 days` | Burn the flexible NFT; `apxUSD.mint(owner, amount − fee)`. The documentation-derived model uses the 3.5%→0.1% schedule; deployment fidelity is separately formalized in `DeploymentFees.lean`. |
| **pause / unpause** | – | `msg.sender` has `PAUSE_ROLE` | Set `globalPause = true / false`. |
| **addToWhitelist / removeFromWhitelist** | `addr` | `msg.sender` has `ADMIN_ROLE` | `whitelist[addr] = true / false`. |
| **addToDenylist / removeFromDenylist** | `addr` | `msg.sender` has `ADMIN_ROLE` | `denylist[addr] = true / false`. |
| **setYieldRate** | `bps` | `msg.sender == admin` ∧ `now ≥ lastRateSetTime + 30 days` (monthly cadence) ∧ `bps ≤ collateralYieldBase` (bounded by the prior month's collateral-derived yield) | `yieldRateMonth = bps`; `lastRateSetTime = now`; `collateralYieldBase` refreshed from the current collateral state (becomes next month's basis). |
| **creditYield** | `amount` (apxUSD) | `msg.sender` == `YieldDistributor` | Accrue the already-vested portion first (`fullyVestedAmount += newlyVested`), then rebase the pool (`vestTotal := unvested + amount`) and reset `vestStart := now` — so previously accrued yield is **preserved**, not forfeited (REQ-credit-preserves-accrued-vest). **Does not touch `usdcReserve`**: `IVesting.depositYield` moves apxUSD into the vesting contract and nothing else, and the USDC redemption reserve is `RedemptionPoolV0`, a different contract. Crediting both inflated the collateral side of the solvency invariant for free (`README` §9.3). |
| **setApxUSDMarketPrice** | `price` | `msg.sender == oracle` | `apxUSDMarketPrice = price`. Gates the `mintApxUSD` arbitrage pathway. |
| **setVestPeriod** | `p` | `msg.sender == admin` | Accrue already-vested first (`fullyVestedAmount += newlyVested`), rebase `vestTotal := unvested`, reset `vestStart := now`, then `vestPeriod = p` — same preservation as creditYield (REQ‑credit‑preserves‑accrued‑vest). |
| **voteBufferDeployment** | – | `governanceTokenBal(msg.sender) ≠ 0` | Sets `bufferDeployed := bufferDeployed ∨ (governanceTokenBal(msg.sender) ≥ governanceThreshold)`. **No vote aggregation is modelled** — a single caller whose own balance meets the threshold deploys the buffer, and with `governanceThreshold = 0` any holder does so unilaterally. `bufferDeployed` is written but never read by any other operation. |
| **executeRFQRedemption** | `user`, `amount` | `!globalPause` ∧ `msg.sender` ∈ approved RFQ counterparties ∧ `balanceOf_apxUSD(user) ≥ amount` ∧ `usdcReserve ≥ amount·redemptionValue/1e27` | Burn `amount` apxUSD from `user`; `usdcReserve -= amount·redemptionValue/1e27`; transfer that USDC to `user`. |
| **updateRedemptionValue** | `newValue` | `msg.sender == admin` ∧ `newValue ≠ 0` | `redemptionValue = newValue`. Corresponds to **`RedemptionPoolV0.setExchangeRate`**, whose only guard is `newRate != 0` — no cap, no floor, no bounded per-update move, no cadence, no side effect on any other field. Gated on the admin role, matching `Roles.assignAdminTargetsFor`. See §5. |
| **handleStressEvent** | `amount` | `msg.sender == admin` | Models an exogenous collateral loss: `totalCollateralValue -= amount`; set `emergencyFlag = true`. (The buffer is the shock absorber, so this can reduce it — distinct from routine redemptions, which never consume the buffer.) |
| **catastrophicBackstop** | – | `msg.sender == admin` ∧ `emergencyFlag == true` (the governance emergency flag must already be up — raised by the stress pathway `handleStressEvent`; the backstop does not raise it for itself) | `redemptionValue = totalCollateralValue·1e27 / totalSupply_apxUSD` (**per-unit**, matching `ApxUSDRateOracle`, so redeeming the whole supply distributes the full reserve — buffer included — pro-rata to holders, crediting each `a` with `usdcReserve·apxUSDBal(a)/totalSupply_apxUSD`); `usdcReserve = 0`. Drives `overcollateralizationBuffer` to 0. |

---

### 4. Key Quantitative Guarantees  

* **Mint price** = $1 = 1 apxUSD (exact) on-chain via `depositUSDC`; the `mintApxUSD` arbitrage pathway also prices at $1 but only while `apxUSDMarketPrice > 1e27`. (Any spreads/execution costs are applied **off-chain** at USD collection — `MinterV0` mints 1:1 on-chain — so they are out of on-chain scope.)
* **ExchangeRate (apyUSD→apxUSD)** is computed live by `computeExchangeRate`, not read from the `exchangeRate` field. The model proves time/deposit monotonicity only under the premises of the named theorems; mixed traces require the rate-aware theorems in `HolderValue.lean`. It is **not bounded below by `1e27`** — `Regression.lean` §R4b exhibits a state where the live rate floors to 0. The deployment read of 1.4036 is an observation, not an invariant.
* **Cooldown** = 20 days (claimable after) with early‑claim fee = `3.5 % – (t/20d)*(3.4 %)` (minimum 0.1 %).  
* **Flexible redemption** minimum claim after 3 days, same fee schedule.  
  These two lines preserve the documentation-corpus model. They are not deployment-fidelity claims: `DeploymentFees.lean` records the verified live receipt curve as 3.4% down to 0%, its mutable admin ceiling, and the separate 10 bps vault-side `unlockingFee` omitted from this model.
* **Over-collateralization**: the derived buffer is `max(0, totalCollateralValue − totalSupply_apxUSD·redemptionValue/ray)`. It **MUST NOT decrease during the modeled routine-redemption slice** (machine-checked: `req_buffer_non_decreasing` over `redeemApxUSD` / `requestUnlock` / `flexibleRequestUnlock` / `executeRFQRedemption`). Stress loss, catastrophic backstop, and admin reserve withdrawal are explicit exceptions in the transition model. The separate `overcollateralizationBuffer` field is a legacy state field written only by the backstop and is not used as a hidden margin term.
* **Yield vesting** linear over `vestPeriod` (default 20 days); `vestedAmount = fullyVestedAmount + newlyVested`, and deposits/period-changes accrue the newly-vested portion into `fullyVestedAmount` before resetting the clock, so accrued yield is never forfeited (REQ‑credit‑preserves‑accrued‑vest). *(Model simplification vs contract: the contract separates `lastDepositTimestamp` from `lastTransferTimestamp` so pulls don't extend the vesting end; the model uses a single `vestStart`, so a pull restarts the remaining pool's clock — a documented remaining approximation.)*  
* **UnlockToken singleton/operator**: exactly one `unlockTokenAddress` exists and is never reassigned; `unlockTokenOperator` (the vault) never changes and may claim on behalf of any recorded owner once cooldown has elapsed.  
* **Monthly yield-rate cadence**: `setYieldRate` succeeds at most once per 30-day period, and the accepted rate is bounded by the previous period's recorded collateral-base yield.  

### 4.1 Lean proof layers

The current proof surface is organized as follows:

| Layer | Current declarations | Scope |
|---|---|---|
| Token ledgers | `apxUSDLedgerConsistent_trace`, `apyUSDLedgerConsistent_trace` | Finite-support balance/supply identities across revert-skip traces. |
| Registry and receipts | `RegistryBounded`, `OwnerPointerSound`, `unlockTokenLedgerConsistent_trace` | Allocation, owner-pointer, and receipt face-value consistency. |
| Composite invariants | `ProtocolInv`, `ProtocolInvWithReceiptLedger`, `ProtocolInvOutstanding` | Conditional composition of registry, solvency, well-formedness, token ledgers, receipts, and pending obligations. |
| Holder value | `holderValue`, `holderValueAt_rateAware_trace_rateAdjusted`, `apxUSDFlow_trace` | Complete per-holder value including pending positions, explicit signed rate revaluation, and internal custody flow. |
| External USDC | `UsdcLedgerConsistent`, `usdcLedgerConsistent_trace` | Parameterized boundary with supplied holder support and total supply; not a field-level invariant of `State`. |

The strongest statements are conditional by design. In particular, a theorem about `ProtocolInv` or
`SolventOutstanding` is not an unconditional guarantee for arbitrary hand-written `State` values, and
none of these theorems proves that deployed bytecode refines this model. See [`SPEC.md`](SPEC.md) §10b
and [`property-manifest.csv`](property-manifest.csv) for requirement-level status.

---  

---

### 5. Implementation correspondence — where this model and `apyx-labs/evm-contracts` differ

Recorded after re-reading the Solidity. Everything here is a **mapping fact**, not a finding;
the findings that follow from it live in `README.md` §9 and in `docs/00`'s TODO.

**Two independent, unbounded prices exist on-chain; this model carries one.**

| On-chain | Scale | Setter / guard | Who reads it |
|---|---|---|---|
| `RedemptionPoolV0.exchangeRate` | `1e18` | `setExchangeRate`, guard `newRate != 0`, `ADMIN_ROLE` | `previewRedeem` / `redeem` — this is what a redeemer is paid |
| `ApxUSDRateOracle.rate` | `1e18` | `setRate`, guard `newRate != 0`, `restricted` | The Curve Stableswap-NG pool, via `staticcall rate()`. **No consumer under `src/`** |

The model's `redemptionValue` is the first. The second is out of scope: nothing in the modeled
system reads it, so adding an inert second field would not buy a theorem. What *is* unmodelled
is the **divergence** between the two — a redemption price and a pool price that no invariant
ties together — and that surface belongs to the Curve pool, outside this state machine.

**The ERC-4626 vault, read from verified source (2026-07-30).** `ApyUSD` is a UUPS proxy
(`0x38EE…8a6A`) over implementation `0xfd616567…b112`, built on OpenZeppelin upgradeable **5.5.0**.
Four facts here changed the model rather than merely annotating it; see `README` §9.3 and
`archive/audit-evidence/deployment_ground_truth.md`.

| On-chain | Model |
|---|---|
| `totalAssets()` is a `view`: `asset.balanceOf(this) + vesting.vestedAmount()`. There is **no stored exchange rate** — every conversion recomputes. `convertToAssets(1e18)` was checked to equal `1e18 * totalAssets / totalSupply` exactly | `totalAssets` has the same shape, and pricing now reads the derived `computeExchangeRate` at every site. The `exchangeRate` field is a published record only |
| `_convertToShares(a,r) = a.mulDiv(totalSupply() + 10**_decimalsOffset(), totalAssets() + 1, r)`, with `_decimalsOffset() = 0` | `computeExchangeRate` carries the same `+1` virtual share and virtual asset, so its denominator is never 0. The *quotient* can still floor to 0 in extreme states, so `withdraw` additionally enforces the deployment's stronger property — `previewWithdraw ≥ 1` for `assets ≥ 1` — as an explicit guard (`README` §9.3 item 2, `Regression.lean` §R4b) |
| `previewDeposit` Floor, `previewMint` **Ceil**, `previewWithdraw` Ceil, `previewRedeem` Floor | Matched. `previewMint` was Floor and under-charged the minter; `redeemAssetsCeil` fixes it |
| `withdraw`/`redeem` call `vesting.pullVestedYield()` **before** pricing ("so liquid assets match `totalAssets()`") | Matched — both branches price off `computeExchangeRate (pullVestedYield s)` |

Two further facts are recorded but **not** modelled:

- **`_decimalsOffset() = 0`**, and `deposit()` does not revert on a zero-share result. So the vault's
  only structural inflation-attack defence is OpenZeppelin's single virtual share. The model carries
  exactly that and no more, which is why `README` §4.2 reports the attack as *mitigated* rather than
  impossible. `depositForMinShares` / `mintForMaxAssets` / `withdrawForMaxShares` /
  `redeemForMinAssets` all exist as the user-side slippage guards.
- **A vault-side `unlockingFee`** is charged upfront inside `_withdraw`, live value `1e15` = **10 bps**,
  which is the production target named in the contract's own docstring. The model has no counterpart:
  its only unlock fee is the flexible-redemption schedule, which belongs to the receipt. Any
  fee-related theorem here is therefore about the receipt fee, not the vault fee.

**Receipts are per-withdrawal, and the model matches.** `withdrawForReceipt` / `redeemForReceipt`
return a fresh `tokenId` per call, so the vault path deliberately opens a *new* position each time.
The single-pending-request rule belongs to the `CommitToken`/`UnlockToken` registry, whose
`_requestRedeem` does `request.shares += shares`. `Apyx.lean` routes both mechanisms through one
registry, so `req_single_pending_redemption_per_user` is scoped to the `requestUnlock` path and does
not claim uniqueness — see its docstring.

**Other differences, all in the direction of the model being narrower than the implementation:**

- **Redemption is permissioned on-chain, and not even the admin may call it.**
  `RedemptionPoolV0.redeem` carries `ROLE_REDEEMER` (`Roles.assignRedeemerTargetsFor`), and
  `Access.t.sol::test_RevertWhen_RedeemNotRedeemer` asserts the revert for an ordinary holder
  *and* for the admin. `Op.redeemApxUSD` is gated on whitelist membership instead, so the model's
  self-service redemption path is more permissive than the deployment's. Further, on-chain `redeem`
  does `burnFrom(msg.sender)` — it burns the *redeemer's* tokens and pays a named `receiver`, so a
  holder must part with their apxUSD first. `Op.executeRFQRedemption` instead burns the *user's*
  balance against their own recorded request, which is a stronger capability than the chain grants
  in one direction and, per `rfq_payout_is_set_by_execution_timing`, a weaker model of the timing
  exposure in the other. **Both legs are now carried**: `Op.executeRFQRedemption` models the
  documented process (settlement against a user's own recorded request), `Op.poolRedeem` models
  the on-chain contract (counterparty-gated, `burnFrom(msg.sender)`, named `receiver`, and the
  `minReserveAssetOut` floor). The request registry has no on-chain counterpart — the user's
  consent and handover happen outside this state machine.
- **The slippage floor is now modelled, and it belongs to the redeemer.** `redeem` takes
  `minReserveAssetOut` and reverts on `SlippageExceeded`. Because the same function is
  `ROLE_REDEEMER`-gated and burns `msg.sender`, the party who sets the floor is the redeemer,
  not the holder whose apxUSD is being converted — `pool_redeem_floor_is_the_redeemers` runs
  both sides of that. So `redemption_has_no_floor` remains accurate for the holder's exposure;
  what the deployment adds is protection for the counterparty.
- ~~**The reserve has an admin exit the model does not carry.**~~ **Now carried**, as
  `Op.withdrawReserve`, after `RedemptionPool/Access.t.sol` showed `withdraw` / `withdrawTokens`
  are deliberately tested admin-only capabilities rather than an oversight. Consequences, all of
  them the honest ones: `reserve_outflow_only_via_redemption` gains a third disjunct that is not
  a redemption at all; `solvency_preserved` has to name it as an exclusion alongside the stress
  loss and the backstop; and `no_free_value_trace` has to name it as a *gift* channel, because it
  credits an address the admin picks with USDC that address never paid for.
- **The redemption-price setter is admin-gated, and the model now agrees.**
  `Roles.assignAdminTargetsFor` assigns `RedemptionPoolV0.setExchangeRate` to `ADMIN_ROLE`, and
  `RedemptionPool/Access.t.sol::test_RevertWhen_SetExchangeRateNotAdmin` pins it. `Op.updateRedemptionValue`
  was oracle-gated; it is not any more. The oracle role publishes the reported market price and
  nothing else.
- **No decimal scaling.** `previewRedeem` divides by `10^|assetDecimals − reserveDecimals|`;
  the model treats apxUSD and USDC as commensurate.
- **`ApxUSDRateOracle` is UUPS.** `_authorizeUpgrade` is `restricted`, so implementation
  replacement is a strictly stronger authority than `setRate`. Out of scope per `README.md` §12.

**Not verified.** Whether `RedemptionPoolV0` is deployed and is the live redemption path (the
addresses published in `README.md` are apxUSD / apyUSD / UnlockToken only), and what the live
`AccessManager` grants actually are — `Roles.sol` is the setup library, not a snapshot of chain
state. Both are open questions for the implementation side.

---

---

### 6. On-chain snapshot — the deployed authority and price pipeline

Read from Ethereum mainnet on 2026-07-30 (≈ block 25,641,600). This is a **snapshot of
configuration, not of code**: it can be changed by the holders named below, subject to the delays
named below. Everything in §5 is about the repository; this section is about what is actually
wired up, and on three points the two differ enough to change findings in
[`README.md`](README.md).

**Authority.** `apxUSD`, `apyUSD` and `UnlockToken` all report
`authority() = 0xe167330E2Eac88666de253e9607C6d9ae0cA2824`, an OpenZeppelin `AccessManager`.

| Role | Holder | Execution delay |
|---|---|---|
| **0 — ADMIN** | Safe `0xABdd8c8e…65e96` **only** (the deployer EOA and the ops Safe were both granted role 0 and later revoked — `hasRole` is now false for both) | **0** |
| 21 | ops Safe `0xf9862EfC…63cE2` | 0 (this is the `pause()` tier) |
| 22 | ops Safe | **4 hours** (`unpause`, and the price push) |
| 23 | ops Safe | **24 hours** |
| 24 | ops Safe | **3 days** (`upgradeToAndCall`) |
| 25 | ops Safe | **7 days** (`setAuthority`) |
| 31, 41 | assorted EOAs | 0 |

Granting role 0 to a new account carries `getRoleGrantDelay(0) = 7 days`, and every delay
*reduction* carries `minSetback() = 5 days`. `getTargetAdminDelay` is 0 for the manager itself but
**3 days** for the collateral oracle, so re-pointing that contract's function-role mapping is
itself a 3-day scheduled operation.

**The redemption price pipeline is not what either the repo or this model describes.**

- `ApyxRedemptionOracle` — proxy `0x2037a5eb…23b4`, implementation `0xbcc4a174…d682`. A read-only
  Chainlink-shaped aggregator: `latestRoundData` / `getRoundData` / `decimals() = 8`, description
  **"Apyx Capped Collateralization Ratio"**. It has **no setter of any kind**. It reads
  `collateralOracle()` and applies `cap()`.
- `cap() = 1e8`, i.e. **1.00 at 8 decimals**. The published redemption ratio is
  `min(collateral ratio, 1.0)`. Latest answer at the time of reading: `90365900` = **0.903659**.
- `ApyxCollateralRatioOracle` — proxy `0x823210Eb…D305`. `pushRound(int256)` (selector
  `0xc01096f0`) is assigned to **role 22**, so a price push is a **4-hour scheduled operation**,
  not an immediate write.
- **`RedemptionPoolV0` is not deployed under this authority.** `setExchangeRate(uint256)`
  (`0xdb068e0e`) and `redeem(uint256,address,uint256)` (`0xd8780161`) appear nowhere in the
  manager's function-role table, and neither does `ApxUSDRateOracle.setRate(uint256)`
  (`0x34fcf437`). The contracts governed are `apxUSD`, `apyUSD`, three `CommitToken`s,
  `UnlockToken`, `MinterV0`, `LinearVestV0`, `YieldDistributor`, `AddressList`, `OrderDelegate`,
  `LiquidationBatcher` and the two oracles.
- The live analogue of `Op.withdrawReserve` is `YieldDistributor.withdrawTokens(address,uint256,address)`
  (`0x9bc5c509`), assigned to **role 23 — a 24-hour scheduled operation**.

**What this changes.** Three of this report's findings are statements about the model that do not
carry to the deployment as configured:

1. **"The redemption price has no cap."** On-chain it is capped at par by construction, and the
   capping contract cannot be written to at all. `redeem_payout_has_no_cap` remains a true and
   useful statement about the model — it says the *design* imposes no bound — but the deployment
   imposes one.
2. **`redemptionValue ≤ ray`.** `Safety.lean` carries this as the hypothesis `h_rv`, re-supplied
   along the trace. The `cap()` makes it a **deployment invariant**, which is the strongest
   possible discharge of a hypothesis: not assumed, enforced.
3. **"Admin changes take effect in the same block."** `base_model_has_no_timelock` and
   the model’s instantaneous backstop behavior are true of the model, and §5's recommendation 3 cited
   an external observation of a 0-second timelock. The deployed manager has a graded delay ladder
   — 0 / 4h / 24h / 3d / 7d — with 5-day minimum setback on reductions. What remains without delay
   is **ADMIN_ROLE itself**, held by one Safe.

**The Safes, and whether the ladder can be stepped around.** Both Safes are v1.4.1 and carry the
**same six owners**; the admin Safe `0xABdd8c8e…65e96` is **4-of-6**, the ops Safe
`0xf9862EfC…63cE2` is **3-of-6**. So the separation between the undelayed admin tier and the
delayed operational tiers is a *threshold* separation, not a signer separation — the same people
sign both, one more of them for the admin path.

That makes the bypass question the important one, and the configuration answers it:
`getRoleGrantDelay` is **7 days for every operational role** (0, 21, 22, 23, 24, 25), so the admin
cannot mint a fresh zero-delay holder of the price-push role and act. The remaining routes are
also slow: re-pointing a selector to the zero-delay role 21 is `setTargetFunctionRole` against the
collateral oracle, whose `getTargetAdminDelay` is **3 days**; and shortening any delay is subject
to `minSetback() = 5 days`. **So the shortest on-chain path to an undelayed price write is about
three days of public notice** — which is the *shape* of the window `timelock_escape_guarantee` formalizes. That theorem's clock is
attacker-supplied, so the deployment fact rests on the `AccessManager` reads recorded here, not on the theorem (`README` §9.3).

Current write-side roles on `ApyxCollateralRatioOracle`: `pushRound(int256)` → 22 (4h),
`upgradeToAndCall` → 24 (3d), while `pushRound(int256,uint80)`, `setUpstreamOracle` and
`clearOverride` are still **role 0** (admin, undelayed).

**Queue.** `expiration() = 7 days`. Of 896 operations ever scheduled, 169 executed and 5 cancelled;
almost all the rest expired. Four are live at the time of reading, and all four are housekeeping:
two `setTargetFunctionRole` calls that would move `pushRound(int256,uint80)` onto role 22 and
`setUpstreamOracle` onto role 24 — i.e. bring the two remaining admin-only price functions into the
ladder — plus a `MinterV0.setRateLimit(1e24, 86400)` and an `upgradeToAndCall` on the collateral
oracle whose target implementation is **already** the live one.

**Individual EOAs hold two undelayed powers.** Role 31 (`getRoleGrantDelay` 0, execution delay 0)
is granted to **five of the six Safe owners individually**, plus the deployer EOA — not to a Safe.
It covers `MinterV0.cancelMint(bytes32)` (a guardian stop, reasonable to leave instant) and
`OrderDelegate.transferToken(address,uint256)` / `transfer(uint256)` on `OrderDelegate` and on an
**unverified contract** `0xdbef8322…20ef`. Both of those hold no tokens at the time of reading, so
the current exposure is zero, but the capability is unilateral, undelayed and outside the Safe
threshold. Role 41 (`LiquidationBatcher.batchLiquidate`) is likewise an undelayed single-EOA
keeper role, rotated once on 2026-07-28.

**Modelled surface vs governed surface.** The authority governs fourteen contracts. This model
covers apxUSD, apyUSD, the unlock registry, vesting and yield distribution, and the deny list.
It does **not** cover:

| Governed, not modelled | What it is | Weight |
|---|---|---|
| **`CommitToken` "CT-apxUSD"** `0x17122d86…871e` | An async-redeem vault over apxUSD — the same shape as the modelled `UnlockToken`, a separate deployment | **holds 6,226,697 apxUSD, 1.90% of supply** |
| `CommitToken` "CT-apyUSDapx" `0x55095f69…4a60`, "CT-apxUSDUSDC" `0xdfc3cf7e…9375` | Async-redeem vaults over the two Curve LP tokens | 18.4 and 5,046 units |
| `LiquidationBatcher` `0x4dB4D934…b732` | Batched liquidations **on Morpho Blue** (`0xBBBB…FFCb`) — an external-protocol operation, not an Apyx-internal mechanism | proceeds pinned to the ops Safe |
| `OrderDelegate` `0xcCa1AF4d…f7b8` and `0xdbEF8322…20ef` | Delegated signing / settlement helpers, holding the role-31 transfer powers above. The second is unverified | 0 tokens held |
| `MinterV0` `0x2c36e1aD…a76e` | EIP-712 signed minting with a rate limit. The model abstracts mint authorization away (README §6.4 #11) | |
| `ApyxCollateralRatioOracle` / `ApyxRedemptionOracle` | The two-stage price pipeline; the model carries a single `redemptionValue` field | |

**The first row is the finding.** The modelled unlock path (`UnlockToken`) holds **24,936 apxUSD**.
`CT-apxUSD` holds **6,226,697** — **250× more**, and it is the same async request/cooldown/claim
shape. So the report's async-redemption reasoning, including everything the clock work above
unlocked, is aimed at the smaller of the two instances by two and a half orders of magnitude. That
is a Step-0 scoping error, not a proof error: nothing proved here is wrong, it is pointed at 0.008%
of supply when a structurally identical 1.90% sits beside it.

**`LiquidationBatcher` is not the gap it first looked like, and the earlier note here overstated
it.** Reading the source: it liquidates on **Morpho Blue**, not on Apyx state — Apyx has no
per-account collateral positions, so there is no internal liquidation mechanism to be missing. Its
market allowlist is fixed in the constructor with no setter, `withdrawTokens` takes no destination
and always pays the immutable `WITHDRAW_DESTINATION` (the ops Safe), and it is neither pausable nor
upgradeable. The undelayed role-41 keeper is therefore bounded by construction to *which* markets
it may liquidate and *where* proceeds may go. It belongs under README §6.4 #2 (cross-protocol
composition), and as configured it is tight.

**Still unread.** Who the six owner EOAs are — all six are plain externally-owned accounts with no
ENS name or public label, so the chain says nothing further. None is itself a multisig.

---

### 7. The two modules built from the deployment

§6 is a snapshot of configuration. These two Lean modules are the parts of it that carry theorems,
and they sit alongside `Apyx.lean` rather than inside it, because each models a contract the
original documentation-derived scope did not include.

**[`CommitToken.lean`](CommitToken.lean)** — the async-redemption vault. One model, four live
instances (`liveDeployments`), differing only in asset, cooldown and supply cap:

| Instance | Cooldown | Supply cap | Held |
|---|---|---|---|
| `CT-apxUSD` `0x17122d86…871e` | 14 days | 100M | 6,226,697 apxUSD |
| `CT-apyUSDapx` `0x55095f69…4a60` | 14 days | 20M | 18.4 |
| `CT-apxUSDUSDC` `0xdfc3cf7e…9375` | 14 days | 50M | 5,046 |
| `UnlockToken` `0x93775E2d…F4e6` | 20 days | uncapped | 24,936 apxUSD |

The last row is the one `Apyx.lean` already models as `requestUnlock`/`claimUnlock`, and its
20-day cooldown is `Apyx.cooldownPeriod`. The first row holds 250× as much.

**[`RedemptionOracle.lean`](RedemptionOracle.lean)** — the two-stage price pipeline. Models
`ApyxCollateralRatioOracle.pushRound` (role 22, 4-hour scheduled) feeding
`ApyxRedemptionOracle`'s `min(collateral ratio, cap)`. The point of modelling it is that it
resolves §6's three corrections into proofs rather than prose: the cap holds along every trace and
no operation moves it, so `h_rv` is enforced; and the floor genuinely does not exist, so
`redemption_has_no_floor` stands.

**[`MinterRateLimit.lean`](MinterRateLimit.lean)** — `MinterV0`'s sliding-window mint limit
(live: 50,000,000 apxUSD/day; a 50× tightening to 1,000,000 is queued). Models the guard and the
two ways it is weaker than it reads: a reduction does not unwind the window, and the window frees
its whole allowance in one step rather than smoothly.

**[`LiquidationBatcher.lean`](LiquidationBatcher.lean)** — the construction-time bounds on role 41,
the one undelayed keyed role. Immutable market allowlist, immutable withdrawal destination,
fail-closed batching. Undelayed, but not unbounded.

**Still not modelled, deliberately.** `OrderDelegate` (`0xcCa1AF4d…f7b8`) and `0xdbEF8322…20ef`:
the first is a delegated-signing helper holding no tokens, the second is **unverified**, so there
is no source to be faithful to. Both carry role-31 transfer powers, recorded in §6.

None of these four modules changes anything in `Apyx.lean`, `Safety.lean` or `BlastRadius.lean`.
The 82 requirement theorems and the blast-radius analysis are about the contracts they were always
about.

*All state transitions are atomic and protected by the Checks‑Effects‑Interactions pattern; re‑entrancy guards are applied to every external call.*
