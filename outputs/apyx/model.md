**Apyx Protocol – Formal State‑Transition Model**  

---

### 1. State Variables  

| Variable | Type | Meaning (quantitative) |
|----------|------|------------------------|
| `totalCollateralValue` | `uint256` (USD‑scaled, 18 dec) | Market value of **all** collateral assets **including** the over‑collateralization buffer. |
| `totalMintedApxUSD` | `uint256` (18 dec) | Number of apxUSD tokens currently issued. |
| `redemptionValue` | `uint256` (18 dec) | Current per‑token redemption price (USD). |
| `bufferAmount` | `uint256` (18 dec) | `totalCollateralValue – (totalMintedApxUSD × redemptionValue)`. |
| `totalApyUSDshares` | `uint256` (18 dec) | Total supply of apyUSD (ERC‑4626 shares). |
| `totalApyAssets` | `uint256` (18 dec) | `totalApyUSDshares × exchangeRate`; includes streamed yield from `LinearVestV0`. |
| `exchangeRate` | `uint256` (18 dec) | `totalApyAssets / totalApyUSDshares`; grows with accrued yield. |
| `paused` | `bool` | Global emergency stop flag. |
| `denyList` | `mapping(address ⇒ bool)` | Addresses prohibited from any interaction. |
| `whitelist` | `mapping(address ⇒ bool)` | Addresses allowed to use privileged mint/redeem paths. |
| `authorizedCounterparties` | `mapping(address ⇒ bool)` | RFQ executors. |
| `unlockRequests[addr]` | `struct { uint256 amount; uint256 start; bool claimed; }` | One active flexible‑redemption request per user (NFT‑backed). |
| `governanceVotes` | `mapping(uint256 ⇒ Vote)` | Ongoing buffer‑deployment proposals. |

---

### 2. Actors  

| Actor | Role |
|-------|------|
| **User** | Deposits USDC, mints/redeems apxUSD, locks apxUSD → apyUSD, initiates unlocks. |
| **Whitelisted Participant** | Calls `arbitrageMint` / `arbitrageRedeem`. |
| **Governance Token Holder** | Votes on buffer deployment, upgrades, back‑stop. |
| **Authorized Counterparty** | Executes `rfqExecute`. |
| **Protocol Contracts** | `Vault`, `LinearVestV0`, `UnlockReceiptNFT`, `PauseController`. |
| **Oracle** | Supplies `priceUSDC`, `priceRedemptionBasket`. |

---

### 3. Operations  

| Operation | Inputs | Preconditions (must hold) | Effects (state changes) |
|----------|--------|--------------------------|--------------------------|
| `depositForMinShares(user, usdcAmt, minApx)` | `usdcAmt:uint256`, `minApx:uint256` | `!paused`, `!denyList[user]`, `usdcAmt ≥ minApx` | Transfer USDC from `user`; `totalMintedApxUSD += minApx`; `totalCollateralValue += usdcAmt`; mint `minApx` apxUSD to `user`. |
| `mintForMaxAssets(user, apxAmt, maxUSDC)` | `apxAmt:uint256`, `maxUSDC:uint256` | `!paused`, `!denyList[user]`, `maxUSDC ≥ apxAmt` | Pull `apxAmt` USDC; update `totalMintedApxUSD`, `totalCollateralValue`; mint `apxAmt` apxUSD. |
| `redeemForMinAssets(user, apxAmt, minUSDC)` | `apxAmt:uint256`, `minUSDC:uint256` | `!paused`, `!denyList[user]`, `apxAmt ≤ totalMintedApxUSD`, `redemptionValue × apxAmt ≥ minUSDC` | Burn `apxAmt` apxUSD; `totalMintedApxUSD -= apxAmt`; `totalCollateralValue -= redemptionValue × apxAmt`; transfer USDC ≥ `minUSDC` to `user`. |
| `lock(user, apxAmt)` | `apxAmt:uint256` | `apxAmt ≤ balanceApxUSD(user)`, `!paused` | Burn `apxAmt` apxUSD; `totalApyUSDshares += shares = apxAmt / exchangeRate`; `totalApyAssets += apxAmt`; mint `shares` apyUSD to `user`. |
| `unlock(user, apxAmt)` | `apxAmt:uint256` | `apxAmt ≤ balanceApxUSD(user)`, **no active request** | Burn `apxAmt` apxUSD; create `UnlockReceiptNFT` with `amount=apxAmt`, `start=block.timestamp`; store in `unlockRequests[user]`. |
| `claimUnlock(user)` | – | `request exists && block.timestamp ≥ start + 3 days` | Transfer `amount` USDC (minus early‑fee if <20 days); delete request; `totalCollateralValue -= amount`. |
| `pause()` / `unpause()` | – | `caller ∈ governance` | Set `paused = true/false`. |
| `voteDeployBuffer(proposalId, amount)` | `proposalId:uint256`, `amount:uint256` | `caller ∈ governance`, `amount ≤ bufferAmount` | On successful quorum, `totalCollateralValue -= amount`; `bufferAmount -= amount`; funds sent to designated risk‑module. |
| `rfqSubmit(user, apxAmt, quote)` | `apxAmt:uint256`, `quote:uint256` | `!paused`, `apxAmt ≤ balanceApxUSD(user)` | Record RFQ entry `pending[user] = {apxAmt, quote}`. |
| `rfqExecute(counterparty, user)` | – | `authorizedCounterparties[counterparty]`, `pending[user] exists` | Burn `apxAmt`; transfer `quote` USDC to `user`; delete pending entry. |
| `arbitrageMint(arbitrageur, usdcAmt)` | `usdcAmt:uint256` | `whitelist[arbitrageur]`, `apxUSD price > $1` | Transfer `usdcAmt` to buffer; mint `usdcAmt` apxUSD at $1 peg; `totalMintedApxUSD += usdcAmt`; `totalCollateralValue += usdcAmt`. |
| `arbitrageRedeem(arbitrageur, apxAmt)` | `apxAmt:uint256` | `whitelist[arbitrageur]`, `apxUSD price < $1` | Burn `apxAmt`; transfer `apxAmt × redemptionValue` USDC from buffer; `totalMintedApxUSD -= apxAmt`; `totalCollateralValue -= apxAmt × redemptionValue`. |
| `streamYield(amount, period)` *(LinearVestV0)* | `amount:uint256`, `period:uint256` | `caller = Vault` | `totalApyAssets += amount`; vest linearly over `period`; only non‑cooldown apyUSD holders accrue. |
| `activateBackstop()` | – | `governance vote passes`, catastrophic condition | `redemptionValue = totalCollateralValue / totalMintedApxUSD`; distribute all assets pro‑rata to apxUSD holders; `bufferAmount = 0`. |

*All mutating functions are protected by `nonReentrant` and emit appropriate events.*  

---  

**Key Quantitative Guarantees**  

- **Peg:** `apxUSD` minted at exactly **$1** (1 USDC = 1 apxUSD).  
- **Over‑collateralization:** `bufferAmount ≥ 0` at all times; must cover the largest historical TVL draw‑down of comparable stablecoins.  
- **Yield:** `exchangeRate` is monotonic non‑decreasing; no rebasing of apyUSD balances.  
- **Cooldown:** Flexible unlocks lock assets for **≥ 3 days**; early claim fee = `3.5% – (elapsed/20days)×(3.4%)`, floor **0.1%**.  

*All state transitions are atomic and deterministic, enabling formal verification of safety properties.*  