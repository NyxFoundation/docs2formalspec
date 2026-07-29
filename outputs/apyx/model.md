**Apyx Protocol – Formal State‑Transition Model**  
*(Version 1.0 Draft – quantitative view)*  

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
| `exchangeRate` | `uint256` (ray, 1e27) | apyUSD → apxUSD conversion factor (≥ 1e27). |
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
| **depositUSDC** *(standard mint pathway)* | `amount` (USDC) | `!globalPause` ∧ `whitelist[msg.sender]` ∧ `!denylist[msg.sender]` ∧ `amount > 0` | Off‑chain Treasury receives `amount`; `totalSupply_apxUSD += amount`; ERC‑20 `apxUSD.mint(msg.sender, amount)` at $1/unit, unconditionally (no market-price gate — see `mintApxUSD` for the separate arbitrage pathway). |
| **mintApxUSD** *(arbitrage pathway)* | `to`, `amount` | `!globalPause` ∧ `whitelist[msg.sender]` ∧ `!denylist[msg.sender]` ∧ `!denylist[to]` ∧ **`apxUSDMarketPrice > 1e27`** (apxUSD trading above $1) ∧ `amount ≤ balanceUSDC(msg.sender)` | Transfer USDC to Treasury; `totalSupply_apxUSD += amount`; ERC‑20 `apxUSD.mint(to, amount)` at $1/unit. |
| **lockApxUSD** | `amount` | `balanceOf_apxUSD(msg.sender) ≥ amount` ∧ `amount > 0` | `apxUSD.transferFrom(msg.sender, vault, amount)`; `shares = amount * 1e27 / exchangeRate`; `totalSupply_apyUSD += shares`; `apyUSD.mint(msg.sender, shares)`. |
| **requestUnlock** *(standard redemption request)* | `amount` | `!globalPause` ∧ `balanceOf_apxUSD(msg.sender) ≥ amount` | Burn `amount` **apxUSD** from `msg.sender`; enforce **at most one pending standard request per user** — if the caller already has a pending standard position, top it up (`amount` added, cooldown reset); else open a fresh one. Cooldown `= now + 20 days`; mint/refresh the caller's `apxUSD_unlock` NFT. |
| **claimUnlock** | `requestId` | `(msg.sender == owner(requestId)` **∨ `msg.sender == unlockTokenOperator`**`)` ∧ `block.timestamp ≥ cooldownEnd[requestId]` | Burn NFT; `apxUSD.mint(owner(requestId), amount)`; delete `requestId` entry. The vault (as configured operator) may trigger this on behalf of the owner. |
| **redeemApxUSD** *(arbitrage redemption pathway)* | `amount` | `!globalPause` ∧ `whitelist[msg.sender]` ∧ **`apxUSDMarketPrice < 1e27`** (apxUSD trading below $1) ∧ `balanceOf_apxUSD(msg.sender) ≥ amount` ∧ `usdcReserve ≥ amount·redemptionValue/1e27` ∧ the step does not decrease the buffer | Burn `amount` apxUSD; `usdcReserve -= amount·redemptionValue/1e27`; `USDC.transfer(msg.sender, amount·redemptionValue/1e27)`; `totalSupply_apxUSD -= amount`. |
| **withdraw** | `assets`, `receiver` | `balanceOf_apyUSD(msg.sender) ≥ assets / exchangeRate` | Pull vested yield from `LinearVestV0`; burn corresponding apyUSD shares; deposit `assets` into `UnlockToken` (creates unlock NFT with 20‑day cooldown). |
| **redeem** | `shares`, `receiver` | `!globalPause` ∧ `balanceOf_apyUSD(msg.sender) ≥ shares` ∧ vault holds enough apxUSD after pulling vested yield | Pull vested yield; `assets = shares·exchangeRate/1e27`; burn `shares` apyUSD; `vaultApxUSDBal -= assets`; open a standard unlock position for `receiver` (`assets`, 20-day cooldown); recompute `exchangeRate`. |
| **flexibleRequestUnlock** | `amount` | `!globalPause` ∧ `balanceOf_apxUSD(msg.sender) ≥ amount` | Burn `amount` apxUSD; open a *flexible* unlock position (records `requestTime`); multiple concurrent flexible requests are allowed. |
| **flexibleClaimUnlock** | `requestId` | (owner ∨ operator) ∧ `now ≥ requestTime + 3 days` | Burn the flexible NFT; `apxUSD.mint(owner, amount − fee)`, `fee = amount·feeBps/10000` with `feeBps` declining linearly from 3.5% to a 0.1% floor. |
| **pause / unpause** | – | `msg.sender` has `PAUSE_ROLE` | Set `globalPause = true / false`. |
| **addToWhitelist / removeFromWhitelist** | `addr` | `msg.sender` has `ADMIN_ROLE` | `whitelist[addr] = true / false`. |
| **addToDenylist / removeFromDenylist** | `addr` | `msg.sender` has `ADMIN_ROLE` | `denylist[addr] = true / false`. |
| **setYieldRate** | `bps` | `msg.sender == admin` ∧ `now ≥ lastRateSetTime + 30 days` (monthly cadence) ∧ `bps ≤ collateralYieldBase` (bounded by the prior month's collateral-derived yield) | `yieldRateMonth = bps`; `lastRateSetTime = now`; `collateralYieldBase` refreshed from the current collateral state (becomes next month's basis). |
| **creditYield** | `amount` (USDC) | `msg.sender` == `YieldDistributor` | Accrue the already-vested portion first (`fullyVestedAmount += newlyVested`), then rebase the pool (`vestTotal := unvested + amount`) and reset `vestStart := now` — so previously accrued yield is **preserved**, not forfeited (REQ‑credit‑preserves‑accrued‑vest). Also `usdcReserve += amount`. |
| **setApxUSDMarketPrice** | `price` | `msg.sender == oracle` | `apxUSDMarketPrice = price`. Gates the `mintApxUSD` arbitrage pathway. |
| **setVestPeriod** | `p` | `msg.sender == admin` | Accrue already-vested first (`fullyVestedAmount += newlyVested`), rebase `vestTotal := unvested`, reset `vestStart := now`, then `vestPeriod = p` — same preservation as creditYield (REQ‑credit‑preserves‑accrued‑vest). |
| **voteBufferDeployment** | – | `msg.sender` holds governance tokens ≥ threshold | If the vote reaches the threshold, set `bufferDeployed = true` (governs intermediate-risk buffer deployment). |
| **executeRFQRedemption** | `user`, `amount` | `!globalPause` ∧ `msg.sender` ∈ approved RFQ counterparties ∧ `balanceOf_apxUSD(user) ≥ amount` ∧ `usdcReserve ≥ amount·redemptionValue/1e27` | Burn `amount` apxUSD from `user`; `usdcReserve -= amount·redemptionValue/1e27`; transfer that USDC to `user`. |
| **updateRedemptionValue** | `newValue` | `msg.sender == admin` ∧ `newValue ≠ 0` | `redemptionValue = newValue`. Corresponds to **`RedemptionPoolV0.setExchangeRate`**, whose only guard is `newRate != 0` — no cap, no floor, no bounded per-update move, no cadence, no side effect on any other field. Gated on the admin role, matching `Roles.assignAdminTargetsFor`. See §5. |
| **handleStressEvent** | `amount` | `msg.sender == admin` | Models an exogenous collateral loss: `totalCollateralValue -= amount`; set `emergencyFlag = true`. (The buffer is the shock absorber, so this can reduce it — distinct from routine redemptions, which never consume the buffer.) |
| **catastrophicBackstop** | – | `msg.sender == admin` ∧ `emergencyFlag == true` (the governance emergency flag must already be up — raised by the stress pathway `handleStressEvent`; the backstop does not raise it for itself) | `redemptionValue = totalCollateralValue·1e27 / totalSupply_apxUSD` (**per-unit**, matching `ApxUSDRateOracle`, so redeeming the whole supply distributes the full reserve — buffer included — pro-rata to holders, crediting each `a` with `usdcReserve·apxUSDBal(a)/totalSupply_apxUSD`); `usdcReserve = 0`. Drives `overcollateralizationBuffer` to 0. |

---

### 4. Key Quantitative Guarantees  

* **Mint price** = $1 = 1 apxUSD (exact) on-chain via `depositUSDC`; the `mintApxUSD` arbitrage pathway also prices at $1 but only while `apxUSDMarketPrice > 1e27`. (Any spreads/execution costs are applied **off-chain** at USD collection — `MinterV0` mints 1:1 on-chain — so they are out of on-chain scope.)
* **ExchangeRate (apyUSD→apxUSD)** `≥ 1e27`, **non-decreasing**. It is denominated in apxUSD (the vault's ERC-4626 `convertToAssets`), so it rises only with yield and is **structurally insulated from apxUSD-collateral stress**: a collateral loss reduces apxUSD's USD `redemptionValue`, not the apxUSD count backing apyUSD.
* **Cooldown** = 20 days (claimable after) with early‑claim fee = `3.5 % – (t/20d)*(3.4 %)` (minimum 0.1 %).  
* **Flexible redemption** minimum claim after 3 days, same fee schedule.  
* **Over-collateralization**: `overcollateralizationBuffer ≥ 0`. It **MUST NOT decrease during routine redemptions** (machine-checked: `req_buffer_non_decreasing` over `redeemApxUSD` / `requestUnlock` / `flexibleRequestUnlock` / `executeRFQRedemption`) and may grow via yield spreads and collateral appreciation. Two operations are the documented exceptions: a modeled stress **loss** (`handleStressEvent`) can reduce it — the buffer absorbing the shock — and a **catastrophic backstop** distributes it entirely, driving it to 0. (Matches `corpus.md`, which scopes 'not consumed during routine redemptions'; the earlier unconditional 'may only increase' wording was an over-generalized extraction, corrected 2026-07-08.)
* **Yield vesting** linear over `vestPeriod` (default 20 days); `vestedAmount = fullyVestedAmount + newlyVested`, and deposits/period-changes accrue the newly-vested portion into `fullyVestedAmount` before resetting the clock, so accrued yield is never forfeited (REQ‑credit‑preserves‑accrued‑vest). *(Model simplification vs contract: the contract separates `lastDepositTimestamp` from `lastTransferTimestamp` so pulls don't extend the vesting end; the model uses a single `vestStart`, so a pull restarts the remaining pool's clock — a documented remaining approximation.)*  
* **UnlockToken singleton/operator**: exactly one `unlockTokenAddress` exists and is never reassigned; `unlockTokenOperator` (the vault) never changes and may claim on behalf of any recorded owner once cooldown has elapsed.  
* **Monthly yield-rate cadence**: `setYieldRate` succeeds at most once per 30-day period, and the accepted rate is bounded by the previous period's recorded collateral-base yield.  

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

*All state transitions are atomic and protected by the Checks‑Effects‑Interactions pattern; re‑entrancy guards are applied to every external call.*