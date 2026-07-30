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
| **REQ‑buffer‑non‑decreasing** | **Outside of a catastrophic backstop, the overcollateralization buffer — the gap between Total Collateral Value and Redemption Value — MUST NOT decrease during routine redemptions or stress events (and MAY grow via yield spreads and collateral appreciation). A catastrophic backstop is the sole exception and distributes the entire buffer (see REQ‑catastrophic‑backstop).** *(Only the routine-redemption half is formalised — `req_buffer_non_decreasing` covers `redeemApxUSD`, `requestUnlock`, `flexibleRequestUnlock` and `executeRFQRedemption`. The stress-event half is **not** proved: the model's `handleStressEvent` is an exogenous loss the buffer absorbs, and `buffer-growth-stress` is listed as not attempted in `README` §6.1.)* |
| **REQ‑arbitrage‑mint‑access** | **Only eligible whitelist participants SHALL be permitted to invoke the minting pathway for arbitrage when apxUSD trades above $1.00.** |
| **REQ‑arbitrage‑redeem‑access** | **Only eligible whitelist participants SHALL be permitted to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.00.** |
| **REQ‑catastrophic‑backstop** | **Upon detection of a catastrophic scenario, the system MUST set the per‑apxUSD Redemption Value to Total Collateral Value ÷ total apxUSD supply (a per‑unit apxUSD→USDC price, matching the deployed ApxUSDRateOracle rate), so that redeeming the entire supply distributes the full reserve, including the buffer, pro‑rata to remaining holders.** |
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
| **REQ‑single‑pending‑redemption‑per‑user** | **Each user MUST have at most one pending redemption request; if the user adds assets to an existing request, the cooldown timer MUST reset to the time of the update.** *(Scope, per DR‑23: this governs the unlock **request registry**, where a repeat request tops up the existing position. Vault `withdraw`/`redeem` mint a separate receipt per call and are outside it.)* |
| **REQ‑redemption‑async‑process** | **Redemption requests MUST follow the three‑step asynchronous process of request, cooldown, and claim.** |
| **REQ‑redemption‑cooldown‑period** | **After a redemption request is submitted, the system MUST enforce a cooldown period of approximately 20 days before a claim can be executed.** |
| **REQ‑pay‑to‑non‑cooldown** | **Yield MUST be paid to all apyUSD tokens that are not currently undergoing cooldown.** |
| **REQ‑new‑locked‑receives‑yield** | **When new apyUSD is locked, it MUST immediately begin receiving yield, which reduces the overall percentage yield for existing holders.** |
| **REQ‑cooldown‑removal** | **When apyUSD enters the cooldown phase, it MUST be removed from the yield pool, causing remaining apyUSD to receive a higher percentage yield.** |
| **REQ‑buffer‑not‑consumed** | **The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations.** |
| **REQ‑redemption‑value‑uniform** | **The system MUST apply the same Redemption Value to all participants regardless of market conditions.** |
| **REQ‑overcollateralization‑limit** | **The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin.** *(The sources do not quantify the "required overcollateralization margin", so the Lean invariant is the unmargined `totalSupply_apxUSD ≤ totalCollateralValue + usdcReserve`. A margin term that was identically zero on every reachable trace was removed rather than left in place — `README` §9.3.)* |
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
| **REQ‑credit‑preserves‑accrued‑vest** | **When new yield is deposited or the vesting period is changed, the LinearVestV0 contract MUST accrue the already‑vested‑but‑not‑yet‑transferred amount into a separate fully‑vested accumulator BEFORE resetting the vesting clock, so previously accrued yield is preserved (not forfeited) across the reset.** |
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
| **REQ‑buffer‑non‑decreasing** *(already listed in State)* | **Outside of a catastrophic backstop, the overcollateralization buffer — the gap between Total Collateral Value and Redemption Value — MUST NOT decrease during routine redemptions or stress events (and MAY grow via yield spreads and collateral appreciation). A catastrophic backstop is the sole exception and distributes the entire buffer (see REQ‑catastrophic‑backstop).** *(Only the routine-redemption half is formalised — `req_buffer_non_decreasing` covers `redeemApxUSD`, `requestUnlock`, `flexibleRequestUnlock` and `executeRFQRedemption`. The stress-event half is **not** proved: the model's `handleStressEvent` is an exogenous loss the buffer absorbs, and `buffer-growth-stress` is listed as not attempted in `README` §6.1.)* |
| **REQ‑catastrophic‑backstop** *(already listed in State)* | **Upon detection of a catastrophic scenario, the system MUST set the per‑apxUSD Redemption Value to Total Collateral Value ÷ total apxUSD supply (a per‑unit apxUSD→USDC price, matching the deployed ApxUSDRateOracle rate), so that redeeming the entire supply distributes the full reserve, including the buffer, pro‑rata to remaining holders.** |
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
| **REQ‑overcollateralization‑limit** *(already listed in State)* | **The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin.** *(The sources do not quantify the "required overcollateralization margin", so the Lean invariant is the unmargined `totalSupply_apxUSD ≤ totalCollateralValue + usdcReserve`. A margin term that was identically zero on every reachable trace was removed rather than left in place — `README` §9.3.)* |
| **REQ‑totalAssets‑includes‑vault‑balance‑and‑vested** | **The vault's totalAssets() function MUST include both the vault's apxUSD balance and the vestedAmount() reported by the LinearVestV0 contract.** |
| **REQ‑buffer‑non‑decreasing** *(already listed in State)* | **Outside of a catastrophic backstop, the overcollateralization buffer — the gap between Total Collateral Value and Redemption Value — MUST NOT decrease during routine redemptions or stress events (and MAY grow via yield spreads and collateral appreciation). A catastrophic backstop is the sole exception and distributes the entire buffer (see REQ‑catastrophic‑backstop).** *(Only the routine-redemption half is formalised — `req_buffer_non_decreasing` covers `redeemApxUSD`, `requestUnlock`, `flexibleRequestUnlock` and `executeRFQRedemption`. The stress-event half is **not** proved: the model's `handleStressEvent` is an exogenous loss the buffer absorbs, and `buffer-growth-stress` is listed as not attempted in `README` §6.1.)* |
| **REQ‑redemption‑exchange‑rate‑multiplier** *(duplicate – already listed)* | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |
| **REQ‑exchange‑rate‑non‑decreasing** *(duplicate – already listed)* | **The exchange rate between apyUSD and apxUSD MUST be non‑decreasing over time.** |
| **REQ‑redemption‑value‑uniform** *(already listed in State)* | **The system MUST apply the same Redemption Value to all participants regardless of market conditions.** |
| **REQ‑buffer‑preservation** *(duplicate – already listed)* | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑buffer‑growth‑stress** *(duplicate – already listed)* | **The over‑collateralization buffer SHALL grow during stress events rather than be drained by them.** |
| **REQ‑buffer‑not‑consumed** *(duplicate – already listed)* | **The system MUST NOT reduce the overcollateralization buffer as a result of routine redemption operations.** |
| **REQ‑redemption‑value‑uniform** *(duplicate – already listed)* | **The system MUST apply the same Redemption Value to all participants regardless of market conditions.** |
| **REQ‑buffer‑non‑decreasing** *(duplicate – already listed)* | **Outside of a catastrophic backstop, the overcollateralization buffer — the gap between Total Collateral Value and Redemption Value — MUST NOT decrease during routine redemptions or stress events (and MAY grow via yield spreads and collateral appreciation). A catastrophic backstop is the sole exception and distributes the entire buffer (see REQ‑catastrophic‑backstop).** *(Only the routine-redemption half is formalised — `req_buffer_non_decreasing` covers `redeemApxUSD`, `requestUnlock`, `flexibleRequestUnlock` and `executeRFQRedemption`. The stress-event half is **not** proved: the model's `handleStressEvent` is an exogenous loss the buffer absorbs, and `buffer-growth-stress` is listed as not attempted in `README` §6.1.)* |
| **REQ‑redemption‑exchange‑rate‑multiplier** *(duplicate – already listed)* | **When a user redeems apyUSD, the system MUST transfer an amount of apxUSD equal to the number of apyUSD redeemed multiplied by the current exchange rate, which MUST be greater than or equal to 1.** |
| **REQ‑overcollateralization‑limit** *(duplicate – already listed)* | **The system MUST ensure that the total amount of apxUSD minted never exceeds the market value of the collateral minus the required overcollateralization margin.** *(The sources do not quantify the "required overcollateralization margin", so the Lean invariant is the unmargined `totalSupply_apxUSD ≤ totalCollateralValue + usdcReserve`. A margin term that was identically zero on every reachable trace was removed rather than left in place — `README` §9.3.)* |
| **REQ‑buffer‑preservation** *(duplicate – already listed)* | **The system MUST preserve the overcollateralization buffer during routine redemption operations; the buffer MUST NOT be consumed.** |
| **REQ‑buffer‑non‑decreasing** *(duplicate – already listed)* | **Outside of a catastrophic backstop, the overcollateralization buffer — the gap between Total Collateral Value and Redemption Value — MUST NOT decrease during routine redemptions or stress events (and MAY grow via yield spreads and collateral appreciation). A catastrophic backstop is the sole exception and distributes the entire buffer (see REQ‑catastrophic‑backstop).** *(Only the routine-redemption half is formalised — `req_buffer_non_decreasing` covers `redeemApxUSD`, `requestUnlock`, `flexibleRequestUnlock` and `executeRFQRedemption`. The stress-event half is **not** proved: the model's `handleStressEvent` is an exogenous loss the buffer absorbs, and `buffer-growth-stress` is listed as not attempted in `README` §6.1.)* |
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

## 10a. Deployment‑Derived Requirements (provenance: on‑chain, not documentation)

Sections 1–10 are extracted from the sources in §11. This section is not: every requirement below
was read from the **deployed contracts and their `AccessManager` configuration** at ≈ block
25,641,600 on 2026‑07‑30, and each is realised in Lean by the module named against it. They are
kept separate because the rest of this document is traceable to a `source_quote` and these are
traceable to chain state, which can change — see `model.md` §6 for the snapshot and §7 for the
modules.

### 10a.1 Asynchronous redemption vaults (`CommitToken.lean`)

Four live instances of one contract; `apxUSD_unlock` is the subclass §7 already specifies.

| # | Requirement | Level |
|---|---|---|
| DR‑1 | A redeem request SHALL become claimable once `unlockingDelay` has elapsed since it was filed, and a trace SHALL exist that files, waits and claims. | MUST |
| DR‑2 | A claim SHALL burn exactly the recorded share amount and credit the receiver exactly that amount (assets and shares convert 1:1). | MUST |
| DR‑3 | A holder SHALL NOT be committed to more shares than they hold. | MUST |
| DR‑4 | Adding to an existing request SHALL reset the cooldown for the **entire** position; the contract keeps no tranches. | Documented behaviour |
| DR‑5 | A claim SHALL be rejected unless its amount equals the recorded request exactly; partial claims are not supported. | Documented behaviour |
| DR‑6 | Claimability SHALL be evaluated against the current `unlockingDelay`, so raising it applies to requests already pending. Governed by role 24, a 3‑day scheduled operation. | Documented behaviour |
| DR‑7 | A request SHALL NOT escrow the shares; they remain on the owner's balance until the claim. (An explicit ERC‑7540 deviation, noted in the contract.) | Documented behaviour |

DR‑4 to DR‑7 are recorded as behaviour rather than as guarantees: they are consequences of the
book‑keeping, not promises the contract makes, and each is a theorem in `CommitToken.lean` rather
than a defect.

### 10a.2 Redemption‑price pipeline (`RedemptionOracle.lean`)

| # | Requirement | Level |
|---|---|---|
| DR‑8 | The published redemption ratio SHALL be `min(collateral ratio, cap)` and SHALL NOT exceed `cap` on any trace. | MUST |
| DR‑9 | No operation of the pipeline SHALL modify `cap`; moving it requires replacing the implementation (role 24, 3‑day scheduled). | MUST |
| DR‑10 | A push above the cap SHALL be clamped rather than rejected. | MUST |
| DR‑11 | Below the cap the published ratio SHALL equal the pushed value; **no lower bound is enforced**, and a push of `0` publishes `0`. | Documented gap |

DR‑8 supersedes, for the deployment, the §8 assumption that the redemption value is merely
"tracked": it is bounded above at par. DR‑11 is the surviving half of §9.1's parameter‑bound
finding — `redemption_has_no_floor` still holds on‑chain.

### 10a.3 Mint rate limit (`MinterRateLimit.lean`)

| # | Requirement | Level |
|---|---|---|
| DR‑12 | A mint request SHALL be rejected when it exceeds `rateLimitAmount` minus the volume already recorded inside `rateLimitPeriod`. | MUST |
| DR‑13 | A successful mint SHALL record its amount at the current timestamp. | MUST |
| DR‑14 | Reducing `rateLimitAmount` SHALL NOT unwind volume already inside the window; available capacity pins at zero until the window rolls. | Documented behaviour |
| DR‑15 | A record SHALL leave the window the moment `rateLimitPeriod` has elapsed since it was made; capacity is restored in one step, not smoothly. | Documented behaviour |

### 10a.4 Liquidation batcher (`LiquidationBatcher.lean`)

| # | Requirement | Level |
|---|---|---|
| DR‑16 | The market allowlist SHALL be fixed at construction; no operation may widen it. | MUST |
| DR‑17 | Withdrawals SHALL transfer only to the immutable construction‑time destination; the caller SHALL NOT choose a recipient. | MUST |
| DR‑18 | A batch naming any market outside the allowlist SHALL revert in full. | MUST |

DR‑16 to DR‑18 are what make role 41 — which carries no execution delay — bounded rather than
open: it can choose neither which markets it touches nor where proceeds go.

### 10a.5 ERC‑4626 vault mechanics (`Apyx.lean`)

Read from `ApyUSD`'s verified source — proxy `0x38EE…8a6A` over implementation
`0xfd616567…b112`, OpenZeppelin upgradeable 5.5.0 — plus live reads at ≈ block 25,642,103. These
supersede the model's earlier assumptions; see `README` §9.3 and `deployment_ground_truth.md`.

| # | Requirement | Level |
|---|---|---|
| DR‑19 | The vault SHALL hold **no stored exchange rate**. `totalAssets()` SHALL be computed on read as `asset.balanceOf(vault) + vesting.vestedAmount()`, and every share/asset conversion SHALL be derived from it, so the per‑share price moves continuously as yield vests. | MUST |
| DR‑20 | Conversions SHALL use OpenZeppelin's virtual share and virtual asset: `shares = assets · (totalSupply + 10^offset) / (totalAssets + 1)` and its inverse, with `offset = _decimalsOffset()`. Consequently every conversion denominator SHALL be at least 1. | MUST |
| DR‑21 | Rounding SHALL favour the vault in all four directions: `previewDeposit` down, `previewMint` **up**, `previewWithdraw` up, `previewRedeem` down. | MUST |
| DR‑22 | `withdraw` and `redeem` SHALL realise vested yield **before** pricing, so that liquid assets match `totalAssets()` at the moment of conversion. | MUST |
| DR‑23 | Each `withdraw`/`redeem` SHALL open a **new** unlock receipt with its own token id. The one‑pending‑request rule of REQ‑single‑pending‑redemption‑per‑user applies to the `CommitToken`/`UnlockToken` request registry, **not** to vault receipts. | MUST |
| DR‑24 | A settled unlock SHALL be retired in the same call that pays it out — the request entry and the owner's pending‑request pointer SHALL both be cleared, not only the receipt. | MUST |
| DR‑25 | Crediting yield SHALL affect only the vesting contract. It SHALL NOT credit the USDC redemption reserve, which is held by a separate contract. | MUST |

**Two deployment facts recorded as gaps rather than requirements.** Neither is derivable from the
documentation, and the model deliberately does not assert a stronger property than the chain
provides:

- `_decimalsOffset()` returns **0**, and `deposit()` does not revert when the share result rounds to
  zero (`previewDeposit(1 wei) = 0`, read live). The vault therefore relies on a single virtual share
  for inflation‑attack resistance, and on callers using `depositForMinShares`. `README` §4.2 reports
  the attack as *mitigated*, not impossible, and §5 item 7 is the resulting recommendation.
- A vault‑side `unlockingFee` is charged upfront inside `_withdraw`; live value `1e15` = **10 bps**.
  §7's early‑unlock fee schedule is the *receipt* fee and is a different charge. No requirement in
  §1–10 covers the vault fee, and the model has no counterpart for it.

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