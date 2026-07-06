**Apyx Protocol – Formal State‑Transition Model**  
*(Version 1.0 Draft – ≤ 60 lines)*  

---  

## 1. State Variables  

| Name | Type | Meaning / Invariant |
|------|------|---------------------|
| `totalCollateralValue` | `uint256` (USD‑scaled × 1e18) | Value of Prefs + bonds held off‑chain. |
| `redemptionValue` | `uint256` (USD‑scaled) | Dollar price used for all apxUSD redemptions (≥ 1 USD). |
| `liquidityBuffer` | `uint256` (USD‑scaled) | Over‑collateralisation; must be **≥ maxHistoricalTVLDrawdown** and never decrease under stress. |
| `exchangeRate` | `uint256` (ray = 1e27) | apxUSD / apyUSD multiplier; **≥ 1** and **non‑decreasing**. |
| `globalPause` | `bool` | When `true` all `deposit`/`mint` revert. |
| `denyList` | `mapping(address ⇒ bool)` | `true` ⇒ address blocked from deposit/mint. |
| `cooldownEnd[bytes32]` | `mapping(bytes32 ⇒ uint256)` | Timestamp when a specific `apxUSD_unlock` NFT becomes claimable. |
| `unlockFeeSlope` | `uint256` (basis‑points per second) | Linear fee slope = `(3500‑10) bps / 20 days`. |
| `unlockReceiptId` | `uint256` (counter) | Auto‑incremented ID for each Unlock Receipt NFT. |
| `vaultShares` | `mapping(address ⇒ uint256)` | apyUSD ERC‑4626 share balance (non‑rebasing). |
| `vestedYield` | `uint256` (USD‑scaled) | Amount already streamed to the vault (from `LinearVestV0`). |
| `rfqActive` | `bool` | `true` while an RFQ redemption request is open. |
| `bufferDeployVotes[address]` | `mapping(address ⇒ uint256)` | Governance‑token‑weighted votes for buffer deployment. |

---  

## 2. Actors  

| Actor | Authority / Role |
|-------|------------------|
| **WhitelistedUser** | Can call `mint` / `redeem` (must be on‑chain whitelist). |
| **AnyUser** | Permissionless `deposit`, `lock`, `unlock`, `claim`. |
| **GovernanceHolder** | Calls `voteBufferDeployment`. |
| **OffchainTreasury** | Receives USDC, buys Prefs + bonds, reports `totalCollateralValue`. |
| **YieldDistributor** | Calls `pushYield(uint256 amount)` to credit the vault. |
| **ApprovedCounterparty** | Executes RFQ redemption at competitive price. |
| **Admin** | Calls `pause`, `unpause`, `addToDenyList`, `removeFromDenyList`. |

---  

## 3. Operations  

| Operation | Inputs | Preconditions (must hold) | Effects (state change) |
|-----------|--------|--------------------------|--------------------------|
| `deposit(uint256 assets, address receiver)` | `assets` apxUSD, `receiver` | `!globalPause` ∧ `!denyList[msg.sender]` ∧ `!denyList[receiver]` ∧ `assets > 0` | `transferFrom(msg.sender, vault, assets)`<br>`shares = assets * 1e27 / exchangeRate`<br>`vaultShares[receiver] += shares` |
| `mint(uint256 shares, address receiver)` | `shares` apyUSD, `receiver` | Same as `deposit` + `shares > 0` | `required = shares * exchangeRate / 1e27`<br>`transferFrom(msg.sender, vault, required)`<br>`vaultShares[receiver] += shares` |
| `lock(uint256 amount)` | `amount` apxUSD | `amount > 0` | `transferFrom(msg.sender, vault, amount)`<br>`shares = amount * 1e27 / exchangeRate`<br>`vaultShares[msg.sender] += shares` |
| `unlock(uint256 amount)` | `amount` apxUSD (requested) | `amount > 0` ∧ `vaultShares[msg.sender] ≥ amount * exchangeRate / 1e27` | Burn corresponding `shares`.<br>`unlockId = ++unlockReceiptId`<br>`cooldownEnd[unlockId] = block.timestamp + 20 days`<br`mint UnlockReceiptNFT(unlockId, amount, msg.sender)` |
| `claim(uint256 unlockId)` | `unlockId` | `block.timestamp ≥ cooldownEnd[unlockId]` ∧ `ownerOf(unlockId) == msg.sender` | Burn UnlockReceiptNFT.<br>`transfer(apxUSD, msg.sender, amount)` |
| `redeem(uint256 shares, address receiver)` | `shares` apyUSD | `shares > 0` ∧ `vaultShares[msg.sender] ≥ shares` | Burn `shares`.<br>`amount = shares * exchangeRate / 1e27`<br>`unlockId = ++unlockReceiptId`<br>`cooldownEnd[unlockId] = block.timestamp + 20 days`<br>`mint UnlockReceiptNFT(unlockId, amount, receiver)` |
| `submitRFQ(RFQRequest req)` | `req.amount` apxUSD | `!rfqActive` ∧ `req.amount ≤ vaultBalance` | `rfqActive = true`<br>`store req` |
| `executeRFQ(address counterparty, uint256 priceBps)` | `counterparty`, `priceBps` | `rfqActive` ∧ `counterparty ∈ ApprovedCounterparties` | Transfer `req.amount` apxUSD to `counterparty` at `priceBps` discount/premium.<br>`rfqActive = false` |
| `pushYield(uint256 amount)` | `amount` apxUSD | `amount > 0` | `vestedYield += amount`<br>`LinearVestV0.startVesting(amount, 20 days)` |
| `voteBufferDeployment(uint256 amount)` | `amount` USD‑scaled | `msg.sender` holds governance tokens ≥ `amount` | `bufferDeployVotes[msg.sender] += amount` |
| `pause()` / `unpause()` | – | `msg.sender == admin` | `globalPause = true/false` |
| `addToDenyList(address a)` / `removeFromDenyList(address a)` | `a` | `msg.sender == admin` | `denyList[a] = true/false` |

**Notes on Quantitative Rules**  

* **Cooldown** = 20 days (≈ 1 728 000 seconds).  
* **Early‑unlock fee** = `3.5% – ( (block.timestamp‑start) * unlockFeeSlope )`, floor = 0.1 %.  
* **ExchangeRate** never drops below `1e27` (i.e., 1.0) and is updated only upward after each yield vesting tranche.  
* **Liquidity Buffer** must satisfy `liquidityBuffer ≥ maxHistoricalTVLDrawdown` (e.g., ≥ 30 % of peak TVL).  
* **Yield streaming**: linear over 20 days from `pushYield` → `LinearVestV0`.  
* **Unlock Receipt NFT** is non‑transferable: `transfer`/`transferFrom` always revert.  

---  

*All operations are atomic; state updates occur before any external call to prevent re‑entrancy.*  