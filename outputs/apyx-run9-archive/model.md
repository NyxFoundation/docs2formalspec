**Apyx Protocol – Formal State‑Transition Model**  

---

### 1. State Variables  

| Name | Type | Meaning (quantitative) |
|------|------|------------------------|
| `TCV` | `uint256` (USD‑scaled 1e18) | Market value of **all** collateral (Prefs + bonds + over‑collateralisation buffer). |
| `RV` | `uint256` (USD‑scaled) | Redemption value – price at which each `apxUSD` can be redeemed; tracks the basket. |
| `liquidityBuffer` | `uint256` (USD‑scaled) | Portion of `TCV` reserved against historic TVL draw‑downs; never used in routine redemptions. |
| `exchangeRate` | `uint256` (ratio × 1e18) | Conversion factor `apxUSD = apyUSD × exchangeRate`; must satisfy `exchangeRate ≥ 1e18`. |
| `cooldownEnd[user]` | `mapping(address ⇒ uint256)` | Unix timestamp after which the user’s pending unlock may be claimed. |
| `unlockReceiptId` | `uint256` (auto‑increment) | Identifier of the non‑transferable Unlock Receipt NFT for a redemption request. |
| `paused` | `bool` | Global emergency pause flag. |
| `denyList[address]` | `mapping(address ⇒ bool)` | `true` ⇒ address blocked from `deposit`/`mint`. |
| `vestedYield` | `uint256` (USD‑scaled) | Yield that has been vested and is available for distribution. |
| `totalShares` | `uint256` | Total `apyUSD` shares outstanding (ERC‑4626). |
| `totalAssets` | `uint256` | `TCV` − `liquidityBuffer` + `vestedYield` (value held by the vault). |

---

### 2. Actors  

| Actor | Permissions / Role |
|-------|--------------------|
| **Whitelisted User** | May call `mint`/`redeem` when price deviates (> $1 or < $1). |
| **Permissionless User** | May call `deposit`, `withdraw`, `requestUnlock`. |
| **Approved Counterparty** | May fulfil an RFQ redemption after `requestUnlock`. |
| **Governance** | Can vote to deploy part of the buffer, pause/unpause, upgrade contracts. |
| **AccessManager** | Enforces `paused`, `denyList`, upgradeability. |
| **YieldDistributor** | Pulls yield from off‑chain treasury and credits the vault. |
| **LinearVestV0** | Holds vested yield and streams it linearly. |
| **UnlockToken (NFT)** | Minted on each `requestUnlock`; non‑transferable. |

---

### 3. Operations  

| Operation | Inputs | Preconditions (must hold) | Effects (state updates & external calls) |
|-----------|--------|---------------------------|------------------------------------------|
| **deposit(assets, receiver)** | `assets` `uint256` (USDC‑scaled), `receiver` `address` | `!paused`, `!denyList[msg.sender]`, `!denyList[receiver]` | `totalAssets += assets`; `mintShares = assets / exchangeRate`; `totalShares += mintShares`; emit `Deposit`. |
| **mint(shares, receiver)** | `shares` `uint256`, `receiver` `address` | `!paused`, `!denyList[msg.sender]`, `!denyList[receiver]`, `requiredAssets = shares * exchangeRate ≤ TCV‑liquidityBuffer` | `totalAssets += requiredAssets`; `totalShares += shares`; emit `Mint`. |
| **withdraw(assets, receiver)** | `assets` `uint256`, `receiver` `address` | `assets ≤ totalAssets`; caller holds enough `apyUSD` shares; not in cooldown | Pull `vestedYield` from `LinearVestV0`; `totalAssets -= assets`; `totalShares -= sharesNeeded`; mint `UnlockReceipt NFT` (`unlockReceiptId++`); set `cooldownEnd[msg.sender] = now + COOLDOWN`; emit `Withdraw`. |
| **redeem(shares, receiver)** | `shares` `uint256`, `receiver` `address` | `shares ≤ totalShares`; `exchangeRate ≥ 1e18` | `assetsOut = shares * exchangeRate`; `totalAssets -= assetsOut`; `totalShares -= shares`; mint `UnlockReceipt NFT`; set cooldown; emit `Redeem`. |
| **requestUnlock(amount)** | `amount` `uint256` (apxUSD) | `amount ≤ userLockedBalance`; not already in cooldown | Mint `UnlockReceipt NFT`; `cooldownEnd[msg.sender] = now + COOLDOWN`; emit `UnlockRequested`. |
| **claimUnlock(tokenId)** | `tokenId` `uint256` | `ownerOf(tokenId) == msg.sender`; `now ≥ cooldownEnd[msg.sender]` | Burn `UnlockReceipt NFT`; transfer `amount` of `apxUSD` to caller; update `totalAssets`; emit `UnlockClaimed`. |
| **submitRFQ(request)** | `request` struct (amount, price, expiry) | `msg.sender` ∈ `approvedCounterparties` | Record RFQ; counterparties may call `fulfilRFQ`. |
| **fulfilRFQ(requestId)** | `requestId` `uint256` | `msg.sender` ∈ `approvedCounterparties`; request not expired | Transfer `apxUSD` to requester; burn corresponding `UnlockReceipt`; update `totalAssets`. |
| **pause() / unpause()** | – | `msg.sender` authorized by `AccessManager` | Set `paused = true/false`. |
| **addToDenyList(addr) / removeFromDenyList(addr)** | `addr` `address` | `msg.sender` authorized | Update `denyList[addr]`. |
| **upgradeTo(newImpl)** | `newImpl` `address` | `msg.sender` authorized governance | Proxy points to `newImpl`. |
| **distributeYield(amount)** | `amount` `uint256` | `amount ≤ vestedYield` | Call `LinearVestV0.lock(amount)`; `vestedYield -= amount`; `totalAssets += amount`; emit `YieldDistributed`. |

*All arithmetic uses 18‑decimal fixed‑point (1 = 1 × 10¹⁸).*  

*Early‑unlock fee*: when `claimUnlock` is called before `COOLDOWN`, the transferred amount is reduced by `fee = 3.5% − ( (elapsed / COOLDOWN) × (3.5% − 0.1%) )`.  

*Over‑collateralisation invariant*: `TCV ≥ totalAssets + liquidityBuffer`.  

*Buffer visibility*: `TCV`, `RV`, and `liquidityBuffer` are emitted in a public `MetricsUpdated` event after every state‑changing operation.  