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
| `RedemptionValue` | `uint256` (USD‑cents) | Dollar value of 1 apxUSD = collateral value / `totalSupply_apxUSD`. |
| `OvercollateralizationBuffer` | `int256` (USD‑cents) | `RedemptionValue·totalSupply_apxUSD – TotalCollateralValue`. |
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
| **requestUnlock** | `amount` | `balanceOf_apyUSD(msg.sender) ≥ amount` ∧ `amount > 0` | Burn `amount` apyUSD shares; compute `requestId`; `cooldownEnd[msg.sender][requestId] = block.timestamp + 20 days`; mint `apxUSD_unlock` NFT (`requestId`, `owner=msg.sender`, `amount`) at `unlockTokenAddress`. |
| **claimUnlock** | `requestId` | `(msg.sender == owner(requestId)` **∨ `msg.sender == unlockTokenOperator`**`)` ∧ `block.timestamp ≥ cooldownEnd[requestId]` | Burn NFT; `apxUSD.mint(owner(requestId), amount)`; delete `requestId` entry. The vault (as configured operator) may trigger this on behalf of the owner. |
| **redeemApxUSD** | `amount` | `balanceOf_apxUSD(msg.sender) ≥ amount` ∧ `amount > 0` | Burn `amount` apxUSD; `USDC.transfer(msg.sender, amount * RedemptionValue / 1e2)`; `totalSupply_apxUSD -= amount`. |
| **withdraw** | `assets`, `receiver` | `balanceOf_apyUSD(msg.sender) ≥ assets / exchangeRate` | Pull vested yield from `LinearVestV0`; burn corresponding apyUSD shares; deposit `assets` into `UnlockToken` (creates unlock NFT with 20‑day cooldown). |
| **pause / unpause** | – | `msg.sender` has `PAUSE_ROLE` | Set `globalPause = true / false`. |
| **addToWhitelist / removeFromWhitelist** | `addr` | `msg.sender` has `ADMIN_ROLE` | `whitelist[addr] = true / false`. |
| **addToDenylist / removeFromDenylist** | `addr` | `msg.sender` has `ADMIN_ROLE` | `denylist[addr] = true / false`. |
| **setYieldRate** | `bps` | `msg.sender == admin` ∧ `now ≥ lastRateSetTime + 30 days` (monthly cadence) ∧ `bps ≤ collateralYieldBase` (bounded by the prior month's collateral-derived yield) | `yieldRateMonth = bps`; `lastRateSetTime = now`; `collateralYieldBase` refreshed from the current collateral state (becomes next month's basis). |
| **creditYield** | `amount` (USDC) | `msg.sender` == `YieldDistributor` | Accrue the already-vested portion first (`fullyVestedAmount += newlyVested`), then rebase the pool (`vestTotal := unvested + amount`) and reset `vestStart := now` — so previously accrued yield is **preserved**, not forfeited (REQ‑credit‑preserves‑accrued‑vest). Also `usdcReserve += amount`. |
| **setApxUSDMarketPrice** | `price` | `msg.sender == oracle` | `apxUSDMarketPrice = price`. Gates the `mintApxUSD` arbitrage pathway. |
| **setVestPeriod** | `p` | `msg.sender == admin` | Accrue already-vested first (`fullyVestedAmount += newlyVested`), rebase `vestTotal := unvested`, reset `vestStart := now`, then `vestPeriod = p` — same preservation as creditYield (REQ‑credit‑preserves‑accrued‑vest). |
| **voteBufferDeployment** | – | `msg.sender` holds governance tokens ≥ threshold | If proposal passes, `OvercollateralizationBuffer` may be allocated per vote outcome. |
| **executeRFQRedemption** | `user`, `amount` | `msg.sender` ∈ approved RFQ counterparties ∧ `whitelist[user]` | Burn `amount` apxUSD from `user`; transfer USDC = `amount * RedemptionValue / 1e2`. |
| **updateRedemptionValue** | – | Called by oracle/treasury after collateral re‑valuation | `RedemptionValue = TotalCollateralValue / totalSupply_apxUSD`; recompute `OvercollateralizationBuffer`. |
| **handleStressEvent** | – | Triggered when market price deviates > 5 % | Increase `OvercollateralizationBuffer` by allocating excess yield; do **not** reduce buffer. |
| **catastrophicBackstop** | – | Governance emergency flag set | `RedemptionValue = TotalCollateralValue / totalSupply_apxUSD`; distribute entire reserve pro‑rata to all `apxUSD` holders; set `OvercollateralizationBuffer = 0`. |

---

### 4. Key Quantitative Guarantees  

* **Mint price** = $1 = 1 apxUSD (exact), unconditionally via `depositUSDC`; the separate `mintApxUSD` arbitrage pathway also prices at $1 but only executes while `apxUSDMarketPrice > 1e27`.
* **ExchangeRate** `≥ 1e27` (non‑decreasing).  
* **Cooldown** = 20 days (claimable after) with early‑claim fee = `3.5 % – (t/20d)*(3.4 %)` (minimum 0.1 %).  
* **Flexible redemption** minimum claim after 3 days, same fee schedule.  
* **Over‑collateralization**: `OvercollateralizationBuffer ≥ 0` at all times; may only increase on yield or asset appreciation.  
* **Yield vesting** linear over `vestPeriod` (default 20 days); `vestedAmount = fullyVestedAmount + newlyVested`, and deposits/period-changes accrue the newly-vested portion into `fullyVestedAmount` before resetting the clock, so accrued yield is never forfeited (REQ‑credit‑preserves‑accrued‑vest). *(Model simplification vs contract: the contract separates `lastDepositTimestamp` from `lastTransferTimestamp` so pulls don't extend the vesting end; the model uses a single `vestStart`, so a pull restarts the remaining pool's clock — a documented remaining approximation.)*  
* **UnlockToken singleton/operator**: exactly one `unlockTokenAddress` exists and is never reassigned; `unlockTokenOperator` (the vault) never changes and may claim on behalf of any recorded owner once cooldown has elapsed.  
* **Monthly yield-rate cadence**: `setYieldRate` succeeds at most once per 30-day period, and the accepted rate is bounded by the previous period's recorded collateral-base yield.  

---  

*All state transitions are atomic and protected by the Checks‑Effects‑Interactions pattern; re‑entrancy guards are applied to every external call.*