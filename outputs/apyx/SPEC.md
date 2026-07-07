# Apyx Protocol Specification  
**Version:** 1.0 – Draft  
**Status:** Working Draft (intended for discussion and review)  

---

## 1. Introduction  

The **Apyx** protocol is a hybrid on‑chain/off‑chain stable‑coin system that issues **apxUSD** (a dollar‑pegged token) and **apyUSD** (a yield‑bearing vault token). Users deposit USDC to mint apxUSD, lock apxUSD to receive apyUSD, and later redeem apxUSD or apyUSD according to defined economic and operational rules. The protocol combines an off‑chain treasury that holds a diversified basket of preferred‑share assets and short‑term treasury bonds with an on‑chain vault that streams yield to apyUSD holders.  

The purpose of this document is to capture, in a single normative reference, all **RFC‑2119**‑style requirements that govern the behavior of the Apyx system. The scope includes:  

* Minting and redemption of apxUSD.  
* Locking of apxUSD to obtain apyUSD and the associated yield‑distribution mechanics.  
* Access‑control and jurisdictional restrictions.  
* Collateral management, over‑collateralization buffers, and stress‑event handling.  
* All on‑chain contract interactions (ERC‑4626 vault, UnlockToken, YieldDistributor, LinearVestV0, etc.).  

---

## 2. Terminology  

The following terms have the meanings defined below. The definitions use the key words **MUST**, **MUST NOT**, **SHALL**, **SHALL NOT**, **SHOULD**, **SHOULD NOT**, **MAY**, and **OPTIONAL** as described in **RFC 2119**[^1].

| Term | Definition |
|------|------------|
| **apxUSD** | On‑chain stable‑coin token representing a dollar‑pegged claim on the off‑chain collateral basket. |
| **apyUSD** | ERC‑4626 vault token received when a user locks apxUSD; it accrues yield over time. |
| **UnlockToken** | Contract that issues non‑transferable `apxUSD_unlock` tokens representing pending redemption claims. |
| **YieldDistributor** | Contract that credits converted apxUSD proceeds to the apyUSD vault. |
| **LinearVestV0** | Contract that implements a linear vesting mechanism for streamed yield. |
| **Redemption Value** | The dollar‑denominated value per apxUSD that reflects the underlying collateral basket and any applicable spreads. |
| **Over‑collateralization Buffer** | The excess of Redemption Value over the market value of the collateral, which must be preserved (or may grow) under normal operation. |
| **Whitelist** | List of participants approved to mint or redeem apxUSD (or to perform arbitrage) based on eligibility and jurisdiction. |
| **Global Pause** | Protocol‑wide flag that, when active, blocks all deposit and mint operations. |
| **Deny List** | List of addresses that are prohibited from depositing or minting. |
| **RFQ** | Request‑for‑Quote process that allows approved counterparties to execute redemption requests. |
| **Cooldown** | Fixed waiting period after a redemption or unlock request before the user may claim underlying assets. |
| **Flexible Redemption** | Redemption path that allows early claim after a minimum of three days, subject to a declining fee. |
| **Arbitrage Mint / Redeem** | Special mint or redeem pathways that are only available to whitelisted participants when apxUSD trades above or below $1.00 respectively. |

[^1]: *RFC 2119, “Key words for use in RFCs to Indicate Requirement Levels”, https://www.rfc-editor.org/rfc/rfc2119.*

---

## 3. System Model  

### 3.1 Actors  

| Actor | Role |
|-------|------|
| **User** | Deposits USDC, mints apxUSD, locks apxUSD for apyUSD, initiates redemption or unlock requests. |
| **Offchain Treasury** | Holds the collateral basket (preferred‑share assets and short‑term treasury bonds), performs allocation, liquidation, and provides third‑party attestations. |
| **Onchain Vault (apyUSD Vault)** | ERC‑4626 compliant contract that accepts apxUSD deposits, mints apyUSD, streams yield, and coordinates withdrawals/unlocks. |
| **UnlockToken Contract** | Issues `apxUSD_unlock` tokens representing pending redemption claims; enforces cooldown and non‑transferability. |
| **YieldDistributor** | Credits converted apxUSD proceeds to the vault for yield distribution. |
| **LinearVestV0** | Holds vested yield and releases it linearly over a configurable period. |
| **Governance Token Holders** | May vote on buffer deployment and other governance actions. |
| **Approved Counterparties** | Execute RFQ redemption requests. |
| **Global Pause Controller** | Can activate/deactivate the global pause flag. |
| **Deny List / Whitelist Manager** | Maintains address lists for access control. |

### 3.2 State Variables (selected)  

* `totalSupply_apxUSD` – total minted apxUSD.  
* `totalSupply_apyUSD` – total minted apyUSD shares.  
* `RedemptionValue` – current dollar value per apxUSD (tracks basket).  
* `OvercollateralizationBuffer` – RedemptionValue – TotalCollateralValue.  
* `exchangeRate` – apxUSD per apyUSD (≥ 1, non‑decreasing).  
* `cooldownEndTimestamp[user][requestId]` – timestamp after which unlock can be claimed.  
* `whitelist[address]`, `denylist[address]` – access‑control mappings.  
* `globalPause` – boolean flag.  

### 3.3 Operations  

| Operation | Description |
|-----------|-------------|
| `depositUSDC(uint256 amount)` | User sends USDC to the Offchain Treasury; protocol mints apxUSD (REQ‑deposit‑mint‑apxusd). |
| `mintApXUSD(address to, uint256 amount)` | Mints apxUSD at $1 per unit (REQ‑mint‑price, REQ‑issuance‑price‑one). |
| `lockApXUSD(uint256 amount)` | Locks apxUSD in the vault, mints apyUSD (REQ‑lock‑apxusd). |
| `redeemApXUSD(uint256 amount)` | Burns apxUSD and returns USDC at Redemption Value (REQ‑redemption‑value, REQ‑redemption‑value‑uniform, REQ‑mint‑redeem‑at‑redemption‑value). |
| `requestUnlock(uint256 amount)` | Initiates unlock, mints `apxUSD_unlock` NFT (REQ‑unlock‑receipt‑nft‑mint). |
| `claimUnlock(uint256 requestId)` | After cooldown, redeems `apxUSD_unlock` for apxUSD (REQ‑unlock‑token‑redeemable‑1to1‑after‑20d). |
| `withdraw(uint256 assets, address receiver)` | Synchronous withdrawal of apxUSD (REQ‑synchronous‑withdraw‑return‑token). |
| `depositForMinShares(...)`, `mintForMaxAssets(...)`, `withdrawForMaxShares(...)`, `redeemForMinAssets(...)` | Functions that revert on slippage (REQ‑depositforminshares‑slippage, REQ‑mintformaxassets‑slippage, REQ‑withdrawal‑pulls‑vested, REQ‑redeemForMinAssets‑revert‑if‑below‑minAssets). |
| `pause()` / `unpause()` | Activate or deactivate global pause (REQ‑global‑pause‑blocks‑deposit). |
| `addToDenyList(address)` / `removeFromDenyList(address)` | Manage deny list (REQ‑denylist‑blocks‑deposit). |
| `setYieldRate(uint256 amount)` | Monthly yield rate setting (REQ‑monthly‑yield‑rate‑set). |
| `creditYield(uint256 amount)` | YieldDistributor credits vault (REQ‑yield‑distributor‑credit). |
| `voteBufferDeployment()` | Governance token holders vote on buffer deployment (REQ‑governance‑deploy‑buffer). |

---

## 4. State Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑deposit‑mint‑apxusd** | **The protocol MUST mint apxUSD to a user when the user deposits USDC.** Users obtain apxUSD by depositing USDC. |
| **REQ‑mint‑price** | **The protocol MUST price newly minted apxUSD at $1 per unit.** New issuance is explicitly priced at $1. |
| **REQ‑redemption‑value** | **The protocol MUST allow redemption of apxUSD at the current Redemption Value.** All redemption activity occurs at Redemption Value. |
| **REQ‑token‑no‑rebase** | **The apyUSD token MUST NOT rebase its balances; balances may change only via transfers, minting, or burning.** Token balances do not rebase. |
| **REQ‑offchain‑allocation** | **The Offchain Treasury MUST allocate incoming capital to acquire a basket of preferred assets and short‑term treasury bonds.** |
| **REQ‑custody‑attestation** | **The Offchain Treasury MUST provide regular third‑party accounting attestations and transparent reporting on custody and collateral composition.** |
| **REQ‑no‑rehypothecation** | **The protocol MUST NOT rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose.** |
| **REQ‑lock‑apxusd** | **The protocol MUST allow a user to lock apxUSD in the vault and receive apyUSD.** |
| **REQ‑rebalance‑overcollateralization** | **The system SHALL rebalance the collateral basket so that apxUSD remains over‑collateralized.** |
| **REQ‑redeem‑liquidate‑usdc** | **The system SHALL liquidate preferred‑share collateral to USDC in order to settle any redemption request.** |
| **REQ‑redeem‑no‑share‑transfer** | **The system MUST NOT transfer preferred shares directly to a participant who redeems apxUSD.** |
| **REQ‑redemption‑settlement‑value** | **Redemptions SHALL be settled at the Redemption Value, which tracks the underlying basket.** |
| **REQ‑mint‑access‑whitelist** | **Only participants who are eligible, located in permitted jurisdictions, and whitelisted SHALL be allowed to mint apxUSD.** |
| **REQ‑redeem‑access‑whitelist** | **Only participants who are eligible, located in permitted jurisdictions, and whitelisted SHALL be allowed to redeem apxUSD.** |
| **REQ‑issuance‑price‑one** | **New apxUSD issuance SHALL be priced at exactly $1 per token.** |
| **REQ‑buffer‑growth‑stress** | **The over‑collateralization buffer SHALL grow during stress events rather than be drained by them.** |
| **REQ‑buffer‑preservation** | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑mint‑redeem‑at‑redemption‑value** | **All minting and redemption transactions MUST be executed at the Redemption Value, which reflects the underlying basket of preferred shares and cash.** |
| **REQ‑buffer‑non‑decreasing** | **The overcollateralization buffer, defined as the difference between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over time due to yield spreads and collateral appreciation.** |
| **REQ‑arbitrage‑mint‑access** | **Only eligible whitelist participants SHALL be permitted to invoke the minting pathway for arbitrage when apxUSD trades above $1.00.** |
| **REQ‑arbitrage‑redeem‑access** | **Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00.** |
| **REQ‑catastrophic‑backstop** | **Upon detection of a catastrophic scenario, the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, including the buffer, pro‑rata to remaining holders.** |
| **REQ‑governance‑deploy‑buffer** | **The system MUST restrict voting on buffer deployment to holders of the governance token.** |
| **REQ‑rfq‑redemption‑allowed** | **The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute those requests.** |
| **REQ‑unlock‑receipt‑nft‑mint** | **When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |
| **REQ‑unlock‑token‑nontransferable** | **apxUSD_unlock tokens MUST NOT be transferable.** |
| **REQ‑unlock‑token‑no‑yield** | **apxUSD_unlock tokens MUST NOT earn yield.** |
| **REQ‑unlock‑token‑mint‑immediately** | **The UnlockToken contract MUST mint apxUSD_unlock tokens to the user immediately after the deposit — where "the deposit" is the vault depositing the corresponding apxUSD into the UnlockToken contract (as part of a `withdraw`/`redeem`/unlock-request operation), not the user's initial USDC/apxUSD deposit into the vault.** |
| **REQ‑unlock‑token‑redeem‑after‑cooldown** | **The UnlockToken contract MUST allow a user to call redeem() after the cooldown period to receive the underlying apxUSD.** |
| **REQ‑singleton‑unlockToken‑instance** | **There MUST be exactly one instance of UnlockToken and it MUST be used exclusively by the apyUSD vault.** |
| **REQ‑vault‑operator‑of‑UnlockToken** | **The apyUSD vault MUST be configured as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately.** |
| **REQ‑unlock‑cannot‑be‑cancelled** | **The system MUST NOT allow an unlocking request to be cancelled once it has been initiated.** |
| **REQ‑multiple‑unlocks‑reset‑cooldown** | **If a user initiates multiple unlocks, the system MUST reset the cooldown period for the total locked amount.** |
| **REQ‑unlock‑conversion‑after‑cooldown** | **Conversion of apxUSD_unlock to apxUSD MUST only be possible after the cooldown period has elapsed.** |
| **REQ‑unlock‑claimable‑after‑3d** | **Unlocks MUST become claimable after three days.** |
| **REQ‑early‑unlock‑fee‑linear‑decline** | **The early unlock fee MUST decline linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑flexible‑redemption‑multiple‑requests** | **The system MUST allow a user to have multiple concurrent flexible redemption unlock requests.** |
| **REQ‑flexible‑redemption‑claim‑minimum** | **A flexible redemption claim MUST be executable only after a minimum of 3 days have elapsed since the request.** |
| **REQ‑flexible‑redemption‑early‑fee** | **The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %.** |
| **REQ‑single‑pending‑redemption‑per‑user** | **Each user MUST have at most one pending redemption request; if the user adds assets to an existing request, the cooldown timer MUST reset to the time of the update.** |
| **REQ‑redemption‑async‑process** | **Redemption requests MUST follow the three‑step asynchronous process of request, cooldown, and claim.** |
| **REQ‑redemption‑cooldown‑period** | **After a redemption request is submitted, the system MUST enforce a cooldown period of approximately 20 days before a claim can be executed.** |
| **REQ‑pay‑to‑non‑cooldown** | **Yield MUST be paid to all apyUSD tokens that are not currently undergoing cooldown.** |
| **REQ‑new‑locked‑receives‑yield** | **When new apyUSD is locked, it MUST immediately begin receiving yield, which reduces the overall percentage yield for existing holders.** |
| **REQ‑cooldown‑removal** | **When apyUSD enters the cooldown phase, it MUST be removed from the yield pool, causing remaining apyUSD to receive a higher percentage yield.** |
| **REQ‑buffer‑not‑consumed** | **The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations.** |
| **REQ‑redemption‑value‑uniform** | **The system MUST apply the same Redemption Value to all participants regardless of market conditions.** |
| **REQ‑overcollateralization‑limit** | **The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin.** |
| **REQ‑buffer‑preservation** | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** *(duplicate – same as above)* | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |
| **REQ‑unlock‑token‑nontransferable** *(duplicate – same as above)* | **apxUSD_unlock tokens MUST NOT be transferable.** |
| **REQ‑unlock‑token‑no‑yield** *(duplicate – same as above)* | **apxUSD_unlock tokens MUST NOT earn yield.** |
| **REQ‑unlock‑receipt‑nft‑mint** *(duplicate – same as above)* | **When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑unlock‑claimable‑after‑3d** *(duplicate – same as above)* | **Unlocks MUST become claimable after three days.** |
| **REQ‑early‑unlock‑fee‑linear‑decline** *(duplicate – same as above)* | **The early unlock fee MUST decline linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑unlock‑cannot‑be‑cancelled** *(duplicate – same as above)* | **The system MUST NOT allow an unlocking request to be cancelled once it has been initiated.** |
| **REQ‑multiple‑unlocks‑reset‑cooldown** *(duplicate – same as above)* | **If a user initiates multiple unlocks, the system MUST reset the cooldown period for the total locked amount.** |
| **REQ‑unlock‑conversion‑after‑cooldown** *(duplicate – same as above)* | **Conversion of apxUSD_unlock to apxUSD MUST only be possible after the cooldown period has elapsed.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** *(duplicate – same as above)* | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |

> **Note:** Duplicate entries are retained for traceability to their original source statements.

---

## 5. Economic Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑price‑may‑include‑spreads** | **The protocol MAY reflect spreads and offchain execution expenses in the price during minting and redemption.** |
| **REQ‑apyusd‑value‑increase** | **The redeemable value of apyUSD MUST increase over time as yield is distributed to the vault.** |
| **REQ‑liquidity‑buffer‑size** | **The system SHALL maintain a liquidity buffer sized against the largest historical TVL drawdowns observed in comparable stablecoins.** |
| **REQ‑buffer‑growth‑stress** *(already listed in State)* | **The over‑collateralization buffer SHALL grow during stress events rather than be drained by them.** |
| **REQ‑exchange‑rate‑non‑decreasing** | **The exchange rate between apyUSD and apxUSD MUST be non‑decreasing over time.** |
| **REQ‑redemption‑exchange‑rate‑multiplier** | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |
| **REQ‑yield‑distributor‑credit** | **The YieldDistributor MUST credit converted apxUSD proceeds to the apyUSD vault.** |
| **REQ‑linear‑vest‑implementation** | **The LinearVestV0 contract MUST implement a linear vesting mechanism for yield credited to the apyUSD vault.** |
| **REQ‑continuous‑stream** | **Yield MUST be streamed continuously over a configurable period rather than as a lump‑sum distribution.** |
| **REQ‑monthly‑yield‑rate‑set** | **Each month, the system MUST set the yield rate for the following month based on the prior month’s collateral‑base yield.** |
| **REQ‑yield‑rate‑dollar‑terms** | **The yield rate MUST be expressed in dollar terms for the month.** |
| **REQ‑pay‑to‑non‑cooldown** *(already listed in State)* | **Yield MUST be paid to all apyUSD tokens that are not currently undergoing cooldown.** |
| **REQ‑new‑locked‑receives‑yield** *(already listed in State)* | **When new apyUSD is locked, it MUST immediately begin receiving yield, which reduces the overall percentage yield for existing holders.** |
| **REQ‑cooldown‑removal** *(already listed in State)* | **When apyUSD enters the cooldown phase, it MUST be removed from the yield pool, causing remaining apyUSD to receive a higher percentage yield.** |
| **REQ‑early‑unlock‑fee‑linear‑decline** *(already listed in State)* | **The early unlock fee MUST decline linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑flexible‑redemption‑early‑fee** *(already listed in State)* | **The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %.** |
| **REQ‑unlock‑token‑no‑yield** *(already listed in State)* | **apxUSD_unlock tokens MUST NOT earn yield.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** *(already listed in State)* | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |
| **REQ‑unlock‑token‑nontransferable** *(already listed in State)* | **apxUSD_unlock tokens MUST NOT be transferable.** |
| **REQ‑unlock‑token‑mint‑immediately** *(already listed in State)* | **The UnlockToken contract MUST mint apxUSD_unlock tokens to the user immediately after the deposit — where "the deposit" is the vault depositing the corresponding apxUSD into the UnlockToken contract (as part of a `withdraw`/`redeem`/unlock-request operation), not the user's initial USDC/apxUSD deposit into the vault.** |
| **REQ‑unlock‑token‑redeem‑after‑cooldown** *(already listed in State)* | **The UnlockToken contract MUST allow a user to call redeem() after the cooldown period to receive the underlying apxUSD.** |
| **REQ‑unlock‑receipt‑nft‑mint** *(already listed in State)* | **When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑unlock‑claimable‑after‑3d** *(already listed in State)* | **Unlocks MUST become claimable after three days.** |
| **REQ‑flexible‑redemption‑claim‑minimum** *(already listed in State)* | **A flexible redemption claim MUST be executable only after a minimum of 3 days have elapsed since the request.** |
| **REQ‑flexible‑redemption‑multiple‑requests** *(already listed in State)* | **The system MUST allow a user to have multiple concurrent flexible redemption unlock requests.** |
| **REQ‑flexible‑redemption‑early‑fee** *(already listed in State)* | **The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %.** |
| **REQ‑buffer‑not‑consumed** *(already listed in State)* | **The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations.** |
| **REQ‑buffer‑preservation** *(duplicate – already listed)* | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑buffer‑growth‑stress** *(duplicate – already listed)* | **The over‑collateralization buffer SHALL grow during stress events rather than be drained by them.** |
| **REQ‑buffer‑non‑decreasing** *(already listed in State)* | **The overcollateralization buffer, defined as the difference between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over time due to yield spreads and collateral appreciation.** |
| **REQ‑catastrophic‑backstop** *(already listed in State)* | **Upon detection of a catastrophic scenario, the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, including the buffer, pro‑rata to remaining holders.** |
| **REQ‑governance‑deploy‑buffer** *(already listed in State)* | **The system MUST restrict voting on buffer deployment to holders of the governance token.** |
| **REQ‑rfq‑redemption‑allowed** *(already listed in State)* | **The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute those requests.** |

---

## 6. Access‑Control Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑mint‑access‑whitelist** *(already listed in State)* | **Only participants who are eligible, located in permitted jurisdictions, and whitelisted SHALL be allowed to mint apxUSD.** |
| **REQ‑redeem‑access‑whitelist** *(already listed in State)* | **Only participants who are eligible, located in permitted jurisdictions, and whitelisted SHALL be allowed to redeem apxUSD.** |
| **REQ‑deposit‑permissionless** | **The vault MUST allow any address to deposit apxUSD and receive apyUSD without requiring KYB/KYC.** |
| **REQ‑jurisdiction‑restriction‑frontend** | **The frontend MUST prevent users located in restricted jurisdictions from accessing the Apyx application.** |
| **REQ‑unlock‑token‑nontransferable** *(already listed in State)* | **apxUSD_unlock tokens MUST NOT be transferable.** |
| **REQ‑global‑pause‑blocks‑deposit** | **If the global pause is active, any deposit or mint transaction MUST revert.** |
| **REQ‑denylist‑blocks‑deposit** | **If the caller or the receiver address is present in the deny list, deposit and mint operations MUST revert.** |
| **REQ‑unlock‑cannot‑be‑cancelled** *(already listed in State)* | **The system MUST NOT allow an unlocking request to be cancelled once it has been initiated.** |
| **REQ‑vault‑operator‑of‑UnlockToken** *(already listed in State)* | **The apyUSD vault MUST be configured as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately.** |
| **REQ‑arbitrage‑mint‑access** *(already listed in State)* | **Only eligible whitelist participants SHALL be permitted to invoke the minting pathway for arbitrage when apxUSD trades above $1.00.** |
| **REQ‑arbitrage‑redeem‑access** *(already listed in State)* | **Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00.** |
| **REQ‑rfq‑redemption‑allowed** *(already listed in State)* | **The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute those requests.** |
| **REQ‑governance‑deploy‑buffer** *(already listed in State)* | **The system MUST restrict voting on buffer deployment to holders of the governance token.** |

---

## 7. Temporal Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑yield‑distribution‑period** | **The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period.** |
| **REQ‑deposit‑immediate** | **The apyUSD vault MUST complete deposit operations synchronously and deliver apyUSD shares to the receiver without any delay.** |
| **REQ‑mint‑immediate** | **The apyUSD vault MUST complete mint operations synchronously and deliver apyUSD shares to the receiver without any delay.** |
| **REQ‑synchronous‑withdraw‑return‑token** | **The apyUSD vault MUST execute withdrawals and redeems synchronously and MUST return apxUSD_unlock tokens immediately.** |
| **REQ‑unlock‑cooldown** | **The apxUSD_unlock token MAY be redeemed for apxUSD only after a cooldown period has elapsed.** |
| **REQ‑redemption‑async‑process** *(already listed in State)* | **Redemption requests MUST follow the three‑step asynchronous process of request, cooldown, and claim.** |
| **REQ‑redemption‑cooldown‑period** *(already listed in State)* | **After a redemption request is submitted, the system MUST enforce a cooldown period of approximately 20 days before a claim can be executed.** |
| **REQ‑flexible‑redemption‑claim‑minimum** *(already listed in State)* | **A flexible redemption claim MUST be executable only after a minimum of 3 days have elapsed since the request.** |
| **REQ‑unlock‑claimable‑after‑3d** *(already listed in State)* | **Unlocks MUST become claimable after three days.** |
| **REQ‑multiple‑unlocks‑reset‑cooldown** *(already listed in State)* | **If a user initiates multiple unlocks, the system MUST reset the cooldown period for the total locked amount.** |
| **REQ‑configurable‑vesting‑period** | **The vesting period for linear yield distribution MUST be configurable.** |
| **REQ‑monthly‑yield‑rate‑set** *(already listed in Economic)* | **Each month, the system MUST set the yield rate for the following month based on the prior month’s collateral‑base yield.** |
| **REQ‑unlock‑conversion‑after‑cooldown** *(already listed in State)* | **Conversion of apxUSD_unlock to apxUSD MUST only be possible after the cooldown period has elapsed.** |
| **REQ‑unlock‑receipt‑nft‑mint** *(already listed in State)* | **When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑unlock‑token‑redeem‑after‑cooldown** *(already listed in State)* | **The UnlockToken contract MUST allow a user to call redeem() after the cooldown period to receive the underlying apxUSD.** |
| **REQ‑unlock‑token‑mint‑immediately** *(already listed in State)* | **The UnlockToken contract MUST mint apxUSD_unlock tokens to the user immediately after the deposit — where "the deposit" is the vault depositing the corresponding apxUSD into the UnlockToken contract (as part of a `withdraw`/`redeem`/unlock-request operation), not the user's initial USDC/apxUSD deposit into the vault.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** *(already listed in State)* | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |
| **REQ‑unlock‑receipt‑nft‑mint** *(duplicate – already listed)* | **When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑unlock‑claimable‑after‑3d** *(duplicate – already listed)* | **Unlocks MUST become claimable after three days.** |
| **REQ‑early‑unlock‑fee‑linear‑decline** *(duplicate – already listed)* | **The early unlock fee MUST decline linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑flexible‑redemption‑early‑fee** *(duplicate – already listed)* | **The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** *(duplicate – already listed)* | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |

---

## 8. Arithmetic Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑apyusd‑value‑increase** *(already listed in State)* | **The redeemable value of apyUSD MUST increase over time as yield is distributed to the vault.** |
| **REQ‑exchange‑rate‑non‑decreasing** *(already listed in Economic)* | **The exchange rate between apyUSD and apxUSD MUST be non‑decreasing over time.** |
| **REQ‑redemption‑exchange‑rate‑multiplier** *(already listed in Economic)* | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |
| **REQ‑cooldown‑no‑yield** | **During a redemption cooldown, the exchange rate for the locked apyUSD MUST remain fixed and the user MUST NOT accrue additional yield on those tokens.** During the cooldown period, users will not receive yield on their apyUSD, with the apxUSD/apyUSD exchange rate being fixed. |
| **REQ‑overcollateralization‑limit** *(already listed in State)* | **The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin.** |
| **REQ‑totalAssets‑includes‑vault‑balance‑and‑vested** | **The vault's totalAssets() function MUST include both the vault's apxUSD balance and the vestedAmount() reported by the LinearVestV0 contract.** |
| **REQ‑buffer‑non‑decreasing** *(already listed in State)* | **The overcollateralization buffer, defined as the difference between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over time due to yield spreads and collateral appreciation.** |
| **REQ‑redemption‑exchange‑rate‑multiplier** *(duplicate – already listed)* | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |
| **REQ‑exchange‑rate‑non‑decreasing** *(duplicate – already listed)* | **The exchange rate between apyUSD and apxUSD MUST be non‑decreasing over time.** |
| **REQ‑redemption‑value‑uniform** *(already listed in State)* | **The system MUST apply the same Redemption Value to all participants regardless of market conditions.** |
| **REQ‑buffer‑preservation** *(duplicate – already listed)* | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑buffer‑growth‑stress** *(duplicate – already listed)* | **The over‑collateralization buffer SHALL grow during stress events rather than be drained by them.** |
| **REQ‑buffer‑not‑consumed** *(duplicate – already listed)* | **The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations.** |
| **REQ‑redemption‑value‑uniform** *(duplicate – already listed)* | **The system MUST apply the same Redemption Value to all participants regardless of market conditions.** |
| **REQ‑buffer‑non‑decreasing** *(duplicate – already listed)* | **The overcollateralization buffer, defined as the difference between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over time due to yield spreads and collateral appreciation.** |
| **REQ‑redemption‑exchange‑rate‑multiplier** *(duplicate – already listed)* | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |
| **REQ‑overcollateralization‑limit** *(duplicate – already listed)* | **The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin.** |
| **REQ‑buffer‑preservation** *(duplicate – already listed)* | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑buffer‑non‑decreasing** *(duplicate – already listed)* | **The overcollateralization buffer, defined as the difference between Redemption Value and Total Collateral Value, MUST NOT decrease; it MAY increase over time due to yield spreads and collateral appreciation.** |
| **REQ‑redemption‑exchange‑rate‑multiplier** *(duplicate – already listed)* | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |

---

## 9. Failure‑Handling Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑depositforminshares‑slippage** | **depositForMinShares(uint256 assets, uint256 minShares, address receiver) MUST revert if the number of shares that would be minted is less than minShares.** |
| **REQ‑mintformaxassets‑slippage** | **mintForMaxAssets(uint256 shares, uint256 maxAssets, address receiver) MUST revert if the amount of assets required to mint the requested shares exceeds maxAssets.** |
| **REQ‑withdrawal‑pulls‑vested** | **When processing a withdrawal, the apyUSD vault MUST pull all vested yield from the LinearVestV0 contract before completing the withdrawal.** |
| **REQ‑redeemForMinAssets‑revert‑if‑below‑minAssets** | **redeemForMinAssets(uint256 shares, uint256 minAssets, address receiver) MUST revert if the amount of apxUSD assets to be received is less than minAssets.** |
| **REQ‑withdrawForMaxShares‑revert‑if‑exceeds‑maxShares** | **withdrawForMaxShares(uint256 assets, uint256 maxShares, address receiver) MUST revert if the number of apyUSD shares required to withdraw the assets exceeds maxShares.** |
| **REQ‑global‑pause‑blocks‑deposit** *(already listed in Access‑Control)* | **If the global pause is active, any deposit or mint transaction MUST revert.** |
| **REQ‑denylist‑blocks‑deposit** *(already listed in Access‑Control)* | **If the caller or the receiver address is present in the deny list, deposit and mint operations MUST revert.** |
| **REQ‑deposit‑emits‑event** | **The deposit(assets, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution.** |
| **REQ‑mint‑emits‑event** | **The mint(shares, receiver) function MUST emit a Deposit event with parameters (sender, receiver, owner, assets, shares) upon successful execution.** |
| **REQ‑erc4626‑compliance** | **The apyUSD vault contract MUST implement the ERC‑4626 tokenized vault interface.** |
| **REQ‑vault‑burns‑apyUSD‑shares‑immediately** | **The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call.** |
| **REQ‑vault‑deposits‑apxUSD‑into‑UnlockToken** | **The vault MUST deposit the corresponding apxUSD amount into the UnlockToken contract during a withdraw or redeem operation.** |
| **REQ‑unlockToken‑mints‑apxUSD_unlock‑immediately** | **The UnlockToken contract MUST mint apxUSD_unlock tokens to the user immediately after the deposit — where "the deposit" is the vault depositing the corresponding apxUSD into the UnlockToken contract (as part of a `withdraw`/`redeem`/unlock-request operation), not the user's initial USDC/apxUSD deposit into the vault.** |
| **REQ‑unlockToken‑redeem‑after‑cooldown** *(already listed in State)* | **The UnlockToken contract MUST allow a user to call redeem() after the cooldown period to receive the underlying apxUSD.** |
| **REQ‑vault‑pulls‑vested‑yield‑before‑withdraw** *(duplicate – already listed)* | **When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal.** |
| **REQ‑vault‑burns‑apyUSD‑shares‑immediately** *(duplicate – already listed)* | **The vault MUST burn the appropriate amount of apyUSD shares immediately upon a withdraw or redeem call.** |
| **REQ‑vault‑deposits‑apxUSD‑into‑UnlockToken** *(duplicate – already listed)* | **The vault MUST deposit the corresponding apxUSD amount into the UnlockToken contract during a withdraw or redeem operation.** |
| **REQ‑unlockToken‑mints‑apxUSD_unlock‑immediately** *(duplicate – already listed)* | **The UnlockToken contract MUST mint apxUSD_unlock tokens to the user immediately after the deposit — where "the deposit" is the vault depositing the corresponding apxUSD into the UnlockToken contract (as part of a `withdraw`/`redeem`/unlock-request operation), not the user's initial USDC/apxUSD deposit into the vault.** |
| **REQ‑unlockToken‑redeem‑after‑cooldown** *(duplicate – already listed)* | **The UnlockToken contract MUST allow a user to call redeem() after the cooldown period to receive the underlying apxUSD.** |
| **REQ‑singleton‑unlockToken‑instance** *(already listed in State)* | **There MUST be exactly one instance of UnlockToken and it MUST be used exclusively by the apyUSD vault.** |
| **REQ‑vault‑operator‑of‑UnlockToken** *(already listed in Access‑Control)* | **The apyUSD vault MUST be configured as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately.** |
| **REQ‑unlock‑cannot‑be‑cancelled** *(duplicate – already listed)* | **The system MUST NOT allow an unlocking request to be cancelled once it has been initiated.** |
| **REQ‑multiple‑unlocks‑reset‑cooldown** *(duplicate – already listed)* | **If a user initiates multiple unlocks, the system MUST reset the cooldown period for the total locked amount.** |
| **REQ‑unlock‑conversion‑after‑cooldown** *(duplicate – already listed)* | **Conversion of apxUSD_unlock to apxUSD MUST only be possible after the cooldown period has elapsed.** |
| **REQ‑unlock‑token‑redeemable‑1to1‑after‑20d** *(duplicate – already listed)* | **apxUSD_unlock tokens MUST be redeemable 1:1 for apxUSD after a 20‑day cooldown period.** |
| **REQ‑unlock‑token‑nontransferable** *(duplicate – already listed)* | **apxUSD_unlock tokens MUST NOT be transferable.** |
| **REQ‑unlock‑token‑no‑yield** *(duplicate – already listed)* | **apxUSD_unlock tokens MUST NOT earn yield.** |
| **REQ‑unlock‑receipt‑nft‑mint** *(duplicate – already listed)* | **When a user initiates a new unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑unlock‑claimable‑after‑3d** *(duplicate – already listed)* | **Unlocks MUST become claimable after three days.** |
| **REQ‑early‑unlock‑fee‑linear‑decline** *(duplicate – already listed)* | **The early unlock fee MUST decline linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑flexible‑redemption‑early‑fee** *(duplicate – already listed)* | **The early redemption fee applied to a flexible redemption claim MUST start at 3.5 % and decline linearly over time to a minimum of 0.1 %.** |

---

## 10. Security Considerations  

1. **Access‑Control Enforcement** – Whitelisting, deny‑listing, and jurisdictional front‑end checks must be immutable or governed only by trusted multisig or DAO mechanisms to prevent unauthorized minting or redemption.  

2. **Re‑entrancy & Atomicity** – All synchronous operations (deposit, mint, withdraw, redeem) must be protected against re‑entrancy (e.g., using the Checks‑Effects‑Interactions pattern) because they involve external token transfers and calls to the UnlockToken contract.  

3. **Pause Mechanism** – The global pause must be callable only by a designated admin role; when active, it must reliably revert all state‑changing entry points to prevent partial state updates.  

4. **Buffer Integrity** – The over‑collateralization buffer must be stored in a read‑only view that can only be increased by protocol‑defined yield or collateral appreciation; any accidental reduction would constitute a critical vulnerability.  

5. **Yield Distribution** – Since yield is streamed continuously, the LinearVestV0 contract must enforce the configured vesting period and prevent premature withdrawals that could lead to under‑payment of vault participants.  

6. **UnlockToken Non‑Transferability** – The `apxUSD_unlock` token must reject any ERC‑20 `transfer` or `transferFrom` calls to guarantee that the cooldown semantics cannot be bypassed.  

7. **RFQ Redemption** – Counterparties executing RFQ redemptions must be authenticated and authorized; misuse could allow draining of the reserve.  

8. **Oracle & Pricing** – Although the protocol aims to keep mint/redeem price at $1, any off‑chain price feed used for arbitrage pathways must be secured against manipulation.  

9. **Catastrophic Backstop** – The transition to a catastrophic scenario must be an atomic state change to avoid race conditions that could leave some participants with outdated Redemption Values.  

---

## 11. References  

| # | URL |
|---|-----|
| 1 | <https://docs.apyx.fi/apyx-overview/how-apyx-works.md> |
| 2 | <https://docs.apyx.fi/product-overview/apxusd-overview.md> |
| 3 | <https://docs.apyx.fi/product-overview/apyusd-overview.md> |
| 4 | <https://docs.apyx.fi/solution-overview/peg-stability-model.md> |
| 5 | <https://docs.apyx.fi/solution-overview/apyusd-yield-distribution.md> |
| 6 | <https://docs.apyx.fi/solution-overview/capitalization-framework.md> |
| 7 | <https://docs.apyx.fi/technical-overview/protocol-contracts-overview.md> |
| 8 | <https://docs.apyx.fi/technical-overview/locking.md> |
| 9 | <https://docs.apyx.fi/technical-overview/unlocking.md> |
| 10 | RFC 2119 – *Key words for use in RFCs to Indicate Requirement Levels* – <https://www.rfc-editor.org/rfc/rfc2119> |

--- 

*End of Specification*