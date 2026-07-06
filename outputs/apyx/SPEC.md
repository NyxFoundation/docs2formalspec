# Apyx Protocol Specification  
**Version:** 1.0 – Draft  
**Status:** Working Draft (intended for discussion and review)  

---

## 1. Introduction  

The **Apyx** system is a hybrid on‑chain/off‑chain stable‑coin platform that issues **apxUSD** (a USD‑pegged stablecoin) and **apyUSD** (a yield‑bearing token representing locked apxUSD). The protocol provides a regulated, whitelisted mint‑and‑redeem pathway for apxUSD, a permissionless vault for locking apxUSD to receive apyUSD, and a yield‑distribution mechanism that streams off‑chain dividend income to apyUSD holders.  

The purpose of this document is to capture, in a single normative reference, the functional and non‑functional requirements that govern the behavior of the Apyx protocol. All requirements are derived from the official Apyx documentation (see **References**).  

The scope includes:  

* Access‑control rules for minting, redemption, and vault interactions.  
* Economic pricing and profit‑limit constraints.  
* Arithmetic invariants for pricing, exchange rates, and buffer sizing.  
* State‑transition rules for the off‑chain treasury, on‑chain vault, and unlock‑token contracts.  
* Temporal constraints such as cooldown periods and yield‑streaming schedules.  
* Failure‑mode handling (reverts, denial, cancellation).  

Implementation‑specific details (e.g., contract addresses, gas optimisation) are outside the scope of this specification.  

---

## 2. Terminology  

The following terms have the meanings defined below.  

### 2.1 RFC 2119 Keywords  

The key words **MUST**, **MUST NOT**, **SHALL**, **SHALL NOT**, **REQUIRED**, **SHOULD**, **SHOULD NOT**, **RECOMMENDED**, **MAY**, and **OPTIONAL** in this document are to be interpreted as described in **RFC 2119**[^1].  

### 2.2 Domain‑Specific Terms  

| Term | Definition |
|------|------------|
| **apxUSD** | The on‑chain stablecoin issued by Apyx, priced at $1 per unit. |
| **apyUSD** | A non‑rebasing ERC‑4626 vault share that represents locked apxUSD and accrues yield. |
| **Offchain Treasury** | The off‑chain entity that receives USDC deposits, purchases a basket of preferred assets (“Prefs”) and short‑term treasury bonds, and reports custody. |
| **Onchain Vault** | The ERC‑4626 vault that holds locked apxUSD, mints apyUSD, and distributes yield. |
| **YieldDistributor** | The contract that credits converted off‑chain dividend proceeds to the vault. |
| **Unlock Receipt NFT** | An on‑chain non‑transferable token representing a pending claim to convert `apxUSD_unlock` back to apxUSD after a cooldown. |
| **Redemption Value** | The dollar‑equivalent value of the underlying basket used to price redemptions. |
| **Liquidity Buffer** | The over‑collateralisation buffer that protects against stress events. |
| **RFQ** | “Request for Quote” process used for structured redemption execution. |
| **DENY LIST** | An address list that blocks participation in deposit/mint operations. |
| **GLOBAL PAUSE** | A protocol‑wide flag that halts deposits and mints when active. |
| **STRC** | A synthetic reference token whose price is guided by dividend policy rather than a hard peg. |
| **LinearVestV0** | The contract that implements linear vesting of yield for the vault. |

---

## 3. System Model  

### 3.1 Actors  

| Actor | Role |
|-------|------|
| **Whitelisted User** | Allowed to mint/redeem apxUSD (subject to jurisdiction). |
| **Institutional Market Maker** | Whitelisted participant that may mint/redeem at premium/discount. |
| **Governance Token Holder** | May vote on buffer deployment in intermediate‑risk scenarios. |
| **Offchain Treasury** | Receives USDC, purchases Prefs & bonds, holds assets in custody, reports attestations. |
| **Onchain Vault** | ERC‑4626 vault that locks apxUSD, mints apyUSD, streams yield, and issues unlock tokens. |
| **YieldDistributor** | Credits converted dividend proceeds to the vault. |
| **Approved Counterparty** | Executes RFQ redemption requests competitively. |
| **Frontend** | UI that enforces jurisdiction restrictions. |
| **AddressList (Deny List)** | Smart‑contract list used to block prohibited addresses. |

### 3.2 State Variables (selected)  

* `totalCollateralValue` – USD value of Prefs + treasury bonds held by the Offchain Treasury.  
* `redemptionValue` – Current dollar value used to price apxUSD redemptions (tracks basket).  
* `liquidityBuffer` – Over‑collateralisation amount (must be ≥ historical TVL drawdown).  
* `exchangeRate (t)` – apxUSD/apyUSD exchange multiplier (≥ 1, non‑decreasing).  
* `cooldownEnd[unlockId]` – Timestamp when a specific `apxUSD_unlock` becomes redeemable.  
* `globalPause` – Boolean flag controlling deposit/mint operations.  

### 3.3 Operations  

| Operation | Description |
|-----------|-------------|
| `deposit(assets, receiver)` | Transfers `assets` apxUSD from caller to vault, mints apyUSD shares to `receiver`. |
| `mint(shares, receiver)` | Caller provides required apxUSD, receives exact `shares` of apyUSD. |
| `lock(apxUSD)` | Synchronous lock of apxUSD, immediate mint of apyUSD. |
| `unlock(apxUSD_unlock)` | After cooldown, converts unlock token 1:1 to apxUSD. |
| `redeem(...)` / `withdraw(...)` | Synchronous burn of apyUSD, issuance of `apxUSD_unlock`. |
| `submitRFQ(request)` | User submits redemption request via RFQ. |
| `voteBufferDeployment(amount)` | Governance token holder votes to deploy part of the buffer. |
| `pause()` / `unpause()` | Sets `globalPause`. |
| `addToDenyList(address)` / `removeFromDenyList(address)` | Manage deny list. |

All operations must respect the normative requirements listed in the following sections.  

---

## 4. Access‑Control Requirements  

| ID | Requirement |
|----|-------------|
| **REQ-whitelist-deposit-mint** | **“Only whitelisted users may deposit USDC and receive newly minted apxUSD.”**<br>Only addresses that have been added to the whitelist are permitted to call the minting pathway that accepts USDC and mints apxUSD. |
| **REQ-access-whitelist-permitted-jurisdictions** | **“Only participants who are whitelisted and located in permitted jurisdictions MAY mint or redeem apxUSD through the protocol's designated issuance and redemption pathways.”**<br>Both whitelist status and jurisdiction compliance are required for any mint or redemption transaction. |
| **REQ-lock-apxusd** | **“The system MUST allow users to lock apxUSD in the vault to receive apyUSD.”**<br>Any user (permissionless) can call the lock function to receive apyUSD shares. |
| **REQ-no-rehypothecation** | **“The protocol MUST NOT rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose.”**<br>Deposited apxUSD remains locked and is never used for external lending or other purposes. |
| **REQ-permissionless-deposit** | **“The vault MUST allow any user to deposit apxUSD and receive apyUSD without requiring KYB/KYC.”**<br>Deposit and mint functions are open to all callers, subject only to the global pause and deny‑list checks. |
| **REQ-rfq-redemption-requests** | **“Users MAY submit redemption requests through the Request for Quote (RFQ) process.”**<br>Submission of redemption requests via RFQ is optional and permitted. |
| **REQ-rfq-approved-counterparties** | **“Approved counterparties MUST provide competitive execution against the underlying reserve for RFQ redemption requests.”**<br>When an RFQ is active, the counterparties designated by the protocol must execute at competitive rates. |
| **REQ-governance-deploy-buffer** | **“Governance token holders MAY vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios to support the Redemption Value.”**<br>Buffer deployment is optional and governed by token‑holder votes. |
| **REQ-jurisdiction-restriction** | **“The frontend MUST prevent users located in restricted jurisdictions from accessing the Apyx application.”**<br>UI layer must enforce jurisdictional blocks before any contract interaction. |
| **REQ-global-pause-blocks-deposits** | **“If the global pause is active, the vault MUST reject (revert) all deposit and mint operations.”**<br>When `globalPause == true`, any call to `deposit` or `mint` must revert. |
| **REQ-denylist-blocks-deposits** | **“For any deposit or mint call, the vault MUST check the AddressList deny list for both the caller and the receiver and MUST revert the transaction if either address is denylisted.”**<br>Both `msg.sender` and `receiver` are validated against the deny list. |
| **REQ-unlock-token-nontransferable** | **“The apxUSD_unlock token MUST be non‑transferable.”**<br>The unlock token contract enforces `transfer`/`transferFrom` reverts. |
| **REQ-single-unlocktoken-instance** | **“There MUST be exactly one UnlockToken contract instance, and only the apyUSD vault MAY interact with it.”**<br>Singleton pattern enforced; only the vault has the operator role. |
| **REQ-vault-operator-of-unlocktoken** | **“The apyUSD vault MUST be set as the operator of the UnlockToken contract, enabling it to initiate redeem requests on behalf of users.”**<br>Operator role is granted exclusively to the vault. |
| **REQ-multiple-unlock-requests** | **“The system MAY allow users to queue multiple unlock requests simultaneously, each represented by a distinct Unlock Receipt NFT.”**<br>Multiple concurrent unlocks are permitted but optional. |
| **REQ-single-pending-request** | **“Each user MUST have at most one pending standard redemption request at any time.”**<br>Enforced by the RFQ subsystem. |
| **REQ-reset-cooldown-on-update** | **“If a user adds assets to an existing redemption request, the system MUST reset the cooldown period starting from the time of the update.”**<br>Cooldown timer restarts on request amendment. |
| **REQ-multiple-unlocks-reset-cooldown** | **“When a user initiates an additional unlock while a previous unlock is pending, the cooldown period for the total pending amount MUST be reset to the full cooldown period.”**<br>Combined unlock amount inherits a fresh 20‑day timer. |
| **REQ-unlock-cannot-be-cancelled** | **“The system MUST NOT allow a user to cancel an unlock request after it has been initiated.”**<br>Unlock requests are irrevocable once submitted. |
| **REQ-conversion-after-cooldown-only** | **“The system MUST only allow conversion of apxUSD_unlock to apxUSD after the cooldown period has elapsed.”**<br>Conversion function checks `block.timestamp >= cooldownEnd`. |
| **REQ-early-unlock-fee** | **“The early unlock fee MUST decline linearly from 3.5 % at the earliest claim to 0.1 % at the end of the 20‑day cooldown period.”**<br>Fee schedule is deterministic and linear over time. |
| **REQ-flexible-claim-3days** | **“A flexible redemption becomes claimable after 3 days from initiation.”**<br>After three days, the unlock receipt can be claimed (subject to fee). |
| **REQ-apxusd-unlock-cooldown-20d** | **“The cooldown period for apxUSD_unlock tokens MUST be 20 days.”**<br>Fixed cooldown duration for the unlock token. |
| **REQ-apxusd-unlock-redeemable-1to1** | **“Each apxUSD_unlock token MUST be redeemable 1:1 for one apxUSD after the cooldown period.”**<br>Redemption ratio is exactly one‑to‑one post‑cooldown. |
| **REQ-apxusd-unlock-no-yield** | **“The apxUSD_unlock token MUST NOT earn any yield.”**<br>Unlock tokens are excluded from the yield‑distribution pool. |
| **REQ-unlock-receipt-nft** | **“When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.”**<br>Each unlock request creates a unique NFT. |

---

## 5. Economic Requirements  

| ID | Requirement |
|----|-------------|
| **REQ-mint-price** | **“New apxUSD issuance MUST be priced at $1 per unit.”**<br>All mint transactions price the stablecoin at parity with USD. |
| **REQ-redemption-value-price** | **“All redemptions MUST be priced at the current Redemption Value (subject to a small spread for liquidity and slippage) and this value applies identically across calm and stressed conditions and to all participants.”**<br>Redemption pricing is uniform and may include a modest spread. |
| **REQ-price-spreads-may** | **“The system MAY reflect spreads and off‑chain execution expenses in the price during minting and redemption.”**<br>Optional inclusion of operational costs in pricing. |
| **REQ-profit-limit** | **“The protocol MUST limit profit from minting and redemption to minimal amounts necessary to operate the protocol and prevent attacks.”**<br>Profit margins are constrained to cover only essential costs. |
| **REQ-premium-mint-whitelist** | **“Eligible whitelist participants MUST be allowed to mint apxUSD under predefined terms when the market price of apxUSD exceeds $1.00.”**<br>Whitelist can mint at a premium when market price > $1. |
| **REQ-discount-redeem-whitelist** | **“Eligible whitelist participants MUST be allowed to redeem apxUSD for dollar‑equivalent value when the market price of apxUSD is below $1.00.”**<br>Whitelist can redeem at a discount when market price < $1. |
| **REQ-treasury-allocation** | **“The Offchain Treasury MUST allocate incoming USDC to acquire a basket of preferred assets and short‑term treasury bonds.”**<br>All received USDC is invested per the allocation policy. |
| **REQ-treasury-custody** | **“The Offchain Treasury MUST hold acquired preferred assets in designated custody accounts.”**<br>Custody accounts are used for all Pref holdings. |
| **REQ-treasury-reporting** | **“The Offchain Treasury MUST provide regular third‑party accounting attestations and transparent reporting on custody and collateral composition.”**<br>Periodic attestations are required (non‑formalizable). |
| **REQ-vault-receive-yield** | **“The Onchain Vault MUST receive yield converted into apxUSD from the Offchain Treasury.”**<br>Yield is transferred to the vault in apxUSD form. |
| **REQ-vault-distribute-yield** | **“The Onchain Vault MUST distribute received yield to apyUSD holders in a stream over a 20‑day period.”**<br>Yield is streamed, not lump‑sum. |
| **REQ-buffer-growth-stress** | **“The system MUST increase the overcollateralization buffer during stress events and MUST NOT decrease it as a result of those events.”**<br>Buffer size is monotonic non‑decreasing under stress. |
| **REQ-buffer-availability-all-times** | **“The liquidity buffer MUST remain available at all times, including outside traditional trading hours and on weekends.”**<br>Buffer liquidity is continuously accessible. |
| **REQ-liquidity-buffer-sizing** | **“The system MUST maintain a liquidity buffer that is at least as large as the largest historical TVL drawdown observed in comparable stablecoins.”**<br>Buffer size meets the historical‑drawdown benchmark. |
| **REQ-buffer-not-consumed** | **“The over‑collateralization buffer MUST NOT be consumed during routine redemptions and must be preserved during stress events, growing through stress events.”**<br>Routine redemptions do not draw down the buffer. |
| **REQ-buffer-visibility** | **“The buffer (the gap between Redemption Value and Total Collateral Value) MUST be visible to everyone at all times.”**<br>Transparency of buffer metrics is required (non‑formalizable). |
| **REQ-catastrophic-backstop** | **“In a catastrophic scenario, Total Collateral Value MUST become the Redemption Value and the entire reserve, including the buffer, MUST be distributed pro‑rata to remaining holders.”**<br>Final liquidation rule for catastrophic failure. |
| **REQ-strc-no-hard-peg** | **“The system MUST NOT enforce a hard peg for STRC; instead it SHALL rely on dividend policy as a market‑based lever to guide trading toward the $100 reference price range.”**<br>STRC price is market‑driven via dividends. |
| **REQ-strc-dividend-adjustment** | **“Strategy MUST review and may adjust the STRC dividend rate each month with the objective of keeping STRC trading near its $100 reference value.”**<br>Monthly discretionary dividend adjustments are permitted (non‑formalizable). |
| **REQ-price-spreads-may** (re‑listed) | **“The system MAY reflect spreads and off‑chain execution expenses in the price during minting and redemption.”**<br>Optional cost pass‑through. |

---

## 6. Arithmetic Requirements  

| ID | Requirement |
|----|-------------|
| **REQ-redemption-value-price** (re‑listed) | **“All redemptions MUST be priced at the current Redemption Value (subject to a small spread for liquidity and slippage) …”**<br>Ensures a deterministic redemption price function. |
| **REQ-exchange-rate-non-decreasing** | **“The apxUSD/apyUSD exchange rate MUST be greater than or equal to 1 at all times and MUST never decrease.”**<br>Exchange multiplier `t` satisfies `t ≥ 1` and is monotonic non‑decreasing. |
| **REQ-fixed-rate-during-cooldown** | **“During the cooldown period, the apxUSD/apyUSD exchange rate MUST remain fixed.”**<br>Rate is frozen for the duration of a lock‑up. |
| **REQ-totalAssets-includes-vested** | **“totalAssets() MUST return the sum of the vault's direct apxUSD balance and the vestedAmount() from the LinearVestV0 contract.”**<br>`totalAssets` aggregates on‑chain balance + vested yield. |
| **REQ-yield-rate-dollar-terms** | **“The yield rate MUST be expressed in dollar terms for the month (e.g., $1 M of yield will be paid).”**<br>Yield rate is quoted in absolute USD. |
| **REQ-yield-paid-to-non-cooldown** | **“Yield MUST be paid only to apyUSD tokens that are not currently undergoing cooldown.”**<br>Cooldowned tokens are excluded from the yield pool. |
| **REQ-new-locked-receives-yield-immediately** | **“When apyUSD is locked, the system MUST include it immediately in the set of tokens receiving yield.”**<br>Newly minted apyUSD participates in the current yield stream. |
| **REQ-cooldown-removes-from-pool** | **“When apyUSD enters cooldown, the system MUST remove it immediately from the pool that receives yield.”**<br>Cooldowned tokens stop accruing yield instantly. |
| **REQ-track-basket** | **“The system MUST track the underlying basket to determine the Redemption Value for redemptions.”**<br>Basket composition is maintained for pricing. |
| **REQ-linear-vesting-implementation** | **“The LinearVestV0 contract MUST implement a linear vesting mechanism for yield credited to the apyUSD vault.”**<br>Yield vests linearly over the configured period. |
| **REQ-continuous-streaming** | **“Yield MUST be streamed continuously over a configurable period rather than distributed as a single lump‑sum.”**<br>Yield distribution is a continuous flow. |
| **REQ-monthly-yield-rate-setting** | **“The system MUST set the yield rate each month for the following month based on the yield generated by the collateral base in the prior month.”**<br>Monthly forward‑looking rate calculation. |

---

## 7. State Requirements  

| ID | Requirement |
|----|-------------|
| **REQ-treasury-allocation** (re‑listed) | **“The Offchain Treasury MUST allocate incoming USDC to acquire a basket of preferred assets and short‑term treasury bonds.”** |
| **REQ-treasury-custody** (re‑listed) | **“The Offchain Treasury MUST hold acquired preferred assets in designated custody accounts.”** |
| **REQ-treasury-reporting** (re‑listed) | **“The Offchain Treasury MUST provide regular third‑party accounting attestations and transparent reporting on custody and collateral composition.”** |
| **REQ-vault-receive-yield** (re‑listed) | **“The Onchain Vault MUST receive yield converted into apxUSD from the Offchain Treasury.”** |
| **REQ-vault-distribute-yield** (re‑listed) | **“The Onchain Vault MUST distribute received yield to apyUSD holders in a stream over a 20‑day period.”** |
| **REQ-apyusd-value-increase** | **“The apyUSD token MUST increase in redeemable value over time as yield is distributed to the vault.”** |
| **REQ-yield-source-offchain** | **“Yield for apyUSD MUST be sourced from off‑chain preferred‑share dividends, converted into apxUSD and credited to the apyUSD vault via the YieldDistributor.”** |
| **REQ-rebalance-overcollateralization** | **“The system MUST rebalance the collateral basket to maintain apxUSD overcollateralization.”** |
| **REQ-redemption-settlement-usdc** | **“The system MUST settle all redemption requests in USDC and MUST NOT transfer preferred shares to redeeming participants.”** |
| **REQ-erc4626-compliance** | **“The vault MUST implement the ERC‑4626 standard.”** |
| **REQ-non-rebasing-balances** | **“The apyUSD token balances MUST NOT rebase.”** |
| **REQ-unlock-token-nontransferable** (re‑listed) | **“The apxUSD_unlock token MUST be non‑transferable.”** |
| **REQ-totalAssets-includes-vested** (re‑listed) | **“totalAssets() MUST return the sum of the vault's direct apxUSD balance and the vestedAmount() from the LinearVestV0 contract.”** |
| **REQ-linear-vesting-implementation** (re‑listed) | **“The LinearVestV0 contract MUST implement a linear vesting mechanism for yield credited to the apyUSD vault.”** |
| **REQ-unlock-receipt-nft** (re‑listed) | **“When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.”** |
| **REQ-withdraw-redeem-immediate** | **“The apyUSD vault MUST execute withdrawals and redeems synchronously, burning apyUSD shares and minting apxUSD_unlock tokens within the same transaction.”** |
| **REQ-withdrawal-returns-unlock-token** | **“When a withdrawal is performed, the vault MUST return an apxUSD_unlock token instead of apxUSD.”** |
| **REQ-withdrawal-pulls-vested-yield** | **“When a withdrawal is processed, the vault MUST pull all vested yield from the LinearVestV0 contract before completing the withdrawal.”** |
| **REQ-deposit-function-behavior** | **“The deposit(assets, receiver) function MUST transfer the specified amount of apxUSD from the caller to the vault and MUST mint the calculated number of apyUSD shares to the receiver immediately.”** |
| **REQ-mint-function-behavior** | **“The mint(shares, receiver) function MUST transfer the calculated amount of apxUSD from the caller to the vault and MUST mint the exact number of apyUSD shares to the receiver immediately.”** |
| **REQ-deposit-failure-denylist-revert** | **“deposit must revert with a Denied error when either the caller or the receiver address is present in the deny list.”** |
| **REQ-global-pause-blocks-deposits** (re‑listed) | **“If the global pause is active, the vault MUST reject (revert) all deposit and mint operations.”** |
| **REQ-denylist-blocks-deposits** (re‑listed) | **“For any deposit or mint call, the vault MUST check the AddressList deny list for both the caller and the receiver and MUST revert the transaction if either address is denylisted.”** |
| **REQ-unlock-token-nontransferable** (re‑listed) | **“The apxUSD_unlock token MUST be non‑transferable.”** |
| **REQ-single-unlocktoken-instance** (re‑listed) | **“There MUST be exactly one UnlockToken contract instance, and only the apyUSD vault MAY interact with it.”** |
| **REQ-vault-operator-of-unlocktoken** (re‑listed) | **“The apyUSD vault MUST be set as the operator of the UnlockToken contract, enabling it to initiate redeem requests on behalf of users.”** |

---

## 8. Temporal Requirements  

| ID | Requirement |
|----|-------------|
| **REQ-vault-distribute-yield** (re‑listed) | **“The Onchain Vault MUST distribute received yield to apyUSD holders in a stream over a 20‑day period.”** |
| **REQ-cooldown-period** | **“After a redemption request, the system SHALL enforce a cooldown period of approximately 20 days before a claim can be submitted.”** |
| **REQ-locking-immediate** | **“The apyUSD vault MUST lock apxUSD tokens synchronously and mint apyUSD shares to the receiver immediately.”** |
| **REQ-reset-cooldown-on-update** (re‑listed) | **“If a user adds assets to an existing redemption request, the system MUST reset the cooldown period starting from the time of the update.”** |
| **REQ-multiple-unlocks-reset-cooldown** (re‑listed) | **“When a user initiates an additional unlock while a previous unlock is pending, the cooldown period for the total pending amount MUST be reset to the full cooldown period.”** |
| **REQ-flexible-claim-3days** (re‑listed) | **“A flexible redemption becomes claimable after 3 days from initiation.”** |
| **REQ-early-unlock-fee** (re‑listed) | **“The early unlock fee MUST decline linearly from 3.5 % at the earliest claim to 0.1 % at the end of the 20‑day cooldown period.”** |
| **REQ-apxusd-unlock-cooldown-20d** (re‑listed) | **“The cooldown period for apxUSD_unlock tokens MUST be 20 days.”** |
| **REQ-apxusd-unlock-redeemable-1to1** (re‑listed) | **“Each apxUSD_unlock token MUST be redeemable 1:1 for one apxUSD after the cooldown period.”** |
| **REQ-continuous-streaming** (re‑listed) | **“Yield MUST be streamed continuously over a configurable period rather than distributed as a single lump‑sum.”** |
| **REQ-monthly-yield-rate-setting** (re‑listed) | **“The system MUST set the yield rate each month for the following month based on the yield generated by the collateral base in the prior month.”** |

---

## 9. Failure‑Mode Requirements  

| ID | Requirement |
|----|-------------|
| **REQ-deposit-failure-slippage-revert** | **“depositForMinShares must revert with a SlippageExceeded error when the previewed share amount is lower than the specified minShares.”** |
| **REQ-deposit-failure-denylist-revert** (re‑listed) | **“deposit must revert with a Denied error when either the caller or the receiver address is present in the deny list.”** |
| **REQ-mint-for-max-assets-slippage** | **“mintForMaxAssets(shares, maxAssets, receiver) MUST revert if the amount of apxUSD required to mint the shares exceeds maxAssets.”** |
| **REQ-withdrawForMaxShares-slippage-revert** | **“withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of shares required to withdraw the specified assets exceeds maxShares.”** |
| **REQ-redeemForMinAssets-slippage-revert** | **“redeemForMinAssets(uint256 shares, uint256 minAssets, address receiver) MUST revert if the assets received for the specified shares are less than minAssets.”** |
| **REQ-unlock-cannot-be-cancelled** (re‑listed) | **“The system MUST NOT allow a user to cancel an unlock request after it has been initiated.”** |
| **REQ-conversion-after-cooldown-only** (re‑listed) | **“The system MUST only allow conversion of apxUSD_unlock to apxUSD after the cooldown period has elapsed.”** |
| **REQ-catastrophic-backstop** (re‑listed) | **“In a catastrophic scenario, Total Collateral Value MUST become the Redemption Value and the entire reserve, including the buffer, MUST be distributed pro‑rata to remaining holders.”** |

---

## 10. Security Considerations  

* **Access Control** – Whitelisting, jurisdiction checks, deny‑list enforcement, and global pause are critical to prevent unauthorized minting or redemption.  
* **Re‑entrancy & Atomicity** – Deposit, mint, withdraw, and unlock operations must be atomic; any external call (e.g., to the treasury or YieldDistributor) must be performed after state updates to avoid re‑entrancy attacks.  
* **Buffer Integrity** – The over‑collateralisation buffer must never be consumed during normal operation; its growth under stress must be verified by third‑party attestations.  
* **Yield Distribution** – Yield streaming must be implemented using a trusted linear vesting contract; any deviation could lead to under‑payment of apyUSD holders.  
* **Unlock Token Non‑Transferability** – Enforced at the contract level to prevent secondary market abuse of unlock receipts.  
* **Front‑end Jurisdiction Enforcement** – While UI‑level checks are required, on‑chain verification (e.g., via oracle‑provided jurisdiction data) should be considered for stronger guarantees.  
* **Denial‑of‑Service** – The RFQ process and buffer deployment voting must be designed to avoid blocking legitimate redemption requests.  

---

## 11. References  

* Apyx Overview – How Apyx Works: <https://docs.apyx.fi/apyx-overview/how-apyx-works.md>  
* APXUSD Overview: <https://docs.apyx.fi/product-overview/apxusd-overview.md>  
* APYUSD Overview: <https://docs.apyx.fi/product-overview/apyusd-overview.md>  
* Peg Stability Model: <https://docs.apyx.fi/solution-overview/peg-stability-model.md>  
* APYUSD Yield Distribution: <https://docs.apyx.fi/solution-overview/apyusd-yield-distribution.md>  
* Capitalization Framework: <https://docs.apyx.fi/solution-overview/capitalization-framework.md>  
* Protocol Contracts Overview: <https://docs.apyx.fi/technical-overview/protocol-contracts-overview.md>  
* Locking Specification: <https://docs.apyx.fi/technical-overview/locking.md>  
* Unlocking Specification: <https://docs.apyx.fi/technical-overview/unlocking.md>  

---

[^1]: *RFC 2119 – Key words for use in RFCs to Indicate Requirement Levels*, https://www.rfc-editor.org/rfc/rfc2119.txt.