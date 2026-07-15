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
| `redemptionValue` | `uint256` (ray, 1e27) | Per-apxUSD redemption price in USDC (`1e27` = $1.00); redeeming `amount` apxUSD pays `amount·redemptionValue/1e27` USDC. Matches the deployed `ApxUSDRateOracle.rate` (per-unit, with a `>0` guard on-chain). |
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
| **updateRedemptionValue** | – | `msg.sender == oracle` | Placeholder in the model (a no-op re-read of the oracle). On-chain the redemption price is the `ApxUSDRateOracle.rate`, set by admin `setRate` (guarded `newRate > 0`). |
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

*All state transitions are atomic and protected by the Checks‑Effects‑Interactions pattern; re‑entrancy guards are applied to every external call.*