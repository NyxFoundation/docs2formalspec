# Apyx Protocol Specification  
**Version:** 1.0.0‑draft  
**Status:** Draft (intended for discussion and review)  

---

## 1. Introduction  

### 1.1 Purpose  
This document defines the functional and non‑functional requirements of the **Apyx** protocol, a multi‑asset stable‑coin system comprising the **apxUSD** (collateral‑backed stablecoin) and **apyUSD** (yield‑bearing token). The specification is written in a style compatible with RFC 2119, enabling precise implementation and verification.

### 1.2 Scope  
The specification covers:

* Access‑control rules for minting, redemption and protocol interaction.  
* Economic and arithmetic invariants that preserve the peg and over‑collateralisation.  
* State‑transition rules for the on‑chain vault, off‑chain treasury, and auxiliary contracts.  
* Temporal constraints such as cooldown periods, yield‑streaming windows and fee schedules.  
* Failure‑mode handling (e.g., slippage reverts, prohibition of rehypothecation).  

All requirements are derived from the source documentation listed in **Appendix A**; no additional requirements are introduced.

---

## 2. Terminology  

The following terms have the meanings defined below. The definitions use the RFC 2119 keywords **MUST**, **MUST NOT**, **SHALL**, **SHOULD**, **MAY**, and **OPTIONAL** as defined in [RFC 2119] (https://datatracker.ietf.org/doc/html/rfc2119).

| Term | Definition |
|------|--------------|
| **apxUSD** | The primary stablecoin issued by the protocol, backed by a basket of preferred assets (“Prefs”) and short‑term treasury bonds. |
| **apyUSD** | A tokenised vault share that represents a claim on locked apxUSD and accrues yield distributed by the protocol. |
| **Offchain Treasury** | The off‑chain entity that receives deposited USDC, acquires the collateral basket, and manages custody. |
| **Preferred Assets (Prefs)** | The basket of high‑quality securities held as collateral for apxUSD. |
| **Redemption Value (RV)** | The price at which apxUSD can be redeemed, tracking the market value of the underlying basket. |
| **Total Collateral Value (TCV)** | The full market value of the reserve, including the over‑collateralisation buffer. |
| **Liquidity Buffer** | An extra reserve sized against historic TVL drawdowns to protect against stress events. |
| **Unlock Receipt NFT** | An on‑chain non‑transferable NFT representing a pending redemption (unlock) request. |
| **Cooldown** | The mandatory waiting period after a redemption request before the claim can be executed. |
| **YieldDistributor** | The contract that credits converted apxUSD proceeds to the apyUSD vault. |
| **LinearVestV0** | The contract implementing linear vesting of yield over a configurable period. |
| **AccessManager** | The on‑chain access‑control component governing privileged operations (e.g., upgrades, pauses). |
| **RFQ** | “Request‑for‑Quote” process allowing approved counterparties to execute redemption requests. |
| **Global Pause** | A protocol‑wide emergency switch that halts deposits and mints. |
| **Deny List** | A registry of addresses prohibited from interacting with the vault. |
| **KYC / KYB** | Know‑Your‑Customer / Know‑Your‑Business verification procedures. |
| **ERC‑4626** | Standardised tokenised vault interface. |
| **UUPS** | Upgradeable proxy pattern. |

---

## 3. System Model  

### 3.1 Actors  

| Actor | Role |
|-------|------|
| **Whitelisted User** | Eligible participant (institutional market maker) allowed to mint/redeem apxUSD under certain market conditions. |
| **Permissionless User** | Any address that may deposit apxUSD and receive apyUSD without KYC. |
| **Governance Token Holder** | May vote to deploy part of the over‑collateralisation buffer in intermediate‑risk scenarios. |
| **Approved Counterparty** | Executes redemption requests submitted via the RFQ process. |
| **Offchain Treasury** | Receives USDC deposits, purchases Prefs and treasury bonds, holds assets in designated custody accounts. |
| **YieldDistributor** | Converts proceeds from collateral yields into apxUSD and credits the apyUSD vault. |
| **Vault (apyUSD contract)** | Implements ERC‑4626, manages deposits, mints, withdrawals, and unlock tokens. |
| **UnlockToken contract** | Issues non‑transferable Unlock Receipt NFTs. |
| **AccessManager** | Enforces global pause, deny‑list, and upgradeability controls. |

### 3.2 State Variables  

| Variable | Description |
|----------|-------------|
| `totalCollateralValue` (TCV) | Market value of all Prefs, treasury bonds, and the over‑collateralisation buffer. |
| `redemptionValue` (RV) | Price at which apxUSD can be redeemed; tracks the underlying basket. |
| `liquidityBuffer` | Portion of TCV reserved against historic drawdowns; never consumed in routine redemptions. |
| `exchangeRate` | Ratio used to convert apyUSD ↔ apxUSD during redemption; must be ≥ 1. |
| `cooldownEnd[user]` | Timestamp after which a user’s pending unlock request may be claimed. |
| `unlockReceiptId` | Identifier of the Unlock Receipt NFT associated with a redemption request. |
| `paused` | Boolean flag indicating whether the global pause is active. |
| `denyList[address]` | Mapping indicating whether an address is blocked from deposit/mint. |
| `vestedYield` | Amount of yield that has been vested and is available for distribution. |

### 3.3 Operations  

| Operation | Synopsis |
|-----------|----------|
| `deposit(assets, receiver)` | Synchronously lock USDC‑equivalent apxUSD and mint apyUSD shares to `receiver`. |
| `mint(shares, receiver)` | Synchronously mint `shares` of apyUSD by depositing the required apxUSD. |
| `withdraw(assets, receiver)` | Pull vested yield, then withdraw `assets` of apxUSD, returning an `apxUSD_unlock` token. |
| `redeem(shares, receiver)` | Convert `shares` of apyUSD into apxUSD at the current `exchangeRate`. |
| `requestUnlock(amount)` | Create an Unlock Receipt NFT and start a cooldown timer. |
| `claimUnlock(tokenId)` | After cooldown, redeem the Unlock Receipt for apxUSD. |
| `submitRFQ(redemptionRequest)` | Submit a structured redemption request; only approved counterparties may fulfil it. |
| `pause()` / `unpause()` | Global pause control (AccessManager). |
| `addToDenyList(address)` / `removeFromDenyList(address)` | Manage deny‑list entries (AccessManager). |
| `upgradeTo(newImplementation)` | Upgrade the vault contract via UUPS (AccessManager). |

All operations must respect the requirements enumerated in the following sections.

---

## 4. Access‑Control Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑whitelist‑mint‑access** | **The protocol MUST only allow whitelisted users to deposit USDC for minting apxUSD.**<br>Only addresses on the eligible whitelist may invoke the minting pathway that creates new apxUSD. |
| **REQ‑whitelist‑mint‑redeem** | **Only participants who are eligible, located in permitted jurisdictions, and whitelisted MAY mint or redeem apxUSD through the protocol's designated pathways.**<br>Eligibility and jurisdiction checks are performed off‑chain before the on‑chain call is accepted. |
| **REQ‑deposit‑permissionless** | **The vault MUST allow any address to deposit apxUSD and receive apyUSD without requiring KYC.**<br>Deposits are permissionless; no identity verification is required. |
| **REQ‑jurisdiction‑restriction‑frontend** | **The frontend MUST prevent users located in restricted jurisdictions from accessing the Apyx application.**<br>Geolocation checks are enforced at the UI layer. |
| **REQ‑kyc‑not‑required** | **The smart‑contract system MUST NOT require any KYB/KYC verification for any operation.**<br>All on‑chain functions are open to any address. |
| **REQ‑rfq‑redemption** | **The system MUST allow users to submit redemption requests via a structured RFQ process and MUST permit only approved counterparties to execute those requests.** |
| **REQ‑global‑pause‑blocks‑deposit‑mint** | **If the global pause is active, the vault MUST reject any `deposit` or `mint` transaction.** |
| **REQ‑denylist‑blocks‑deposit‑mint** | **The vault MUST revert any `deposit` or `mint` transaction if the caller or the receiver address is present in the deny list.** |
| **REQ‑unlock‑nontransferable** | **The apxUSD_unlock token MUST NOT be transferable.** |
| **REQ‑single‑unlocktoken‑instance** | **There MUST be only one instance of the UnlockToken contract, and it MUST be used exclusively by the apyUSD vault.** |
| **REQ‑vault‑operator‑unlocktoken** | **The apyUSD vault MUST be set as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately.** |
| **REQ‑governance‑deploy‑buffer** | **Governance token holders MUST be able to vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios.** |
| **REQ‑whitelist‑mint‑premium** | **Only participants on the eligible whitelist MAY mint apxUSD via the arbitrage pathway when apxUSD trades above $1.** |
| **REQ‑whitelist‑redeem‑discount** | **Only participants on the eligible whitelist MAY redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.** |

---

## 5. Arithmetic Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑issuance‑price‑one** | **The protocol MUST price new issuance of apxUSD at $1 per unit.** |
| **REQ‑redemption‑value‑tracks‑basket** | **Redemption Value MUST track the value of the underlying basket of preferred shares.** |
| **REQ‑exchange‑rate‑monotonic** | **The exchangeRate used for redemption MUST be greater than or equal to 1 at all times.** |
| **REQ‑redemption‑calculation** | **When a user redeems apyUSD, the system MUST transfer apxUSD equal to the redeemed apyUSD amount multiplied by the current exchangeRate.** |
| **REQ‑overcollateralization‑margin** | **The system MUST ensure that the total amount of apxUSD minted does not exceed the market value of the collateral minus the required overcollateralization margin.** |
| **REQ‑rate‑dollar‑terms** | **The yield rate MUST be expressed in dollar terms.** |
| **REQ‑constant‑rate‑vesting** | **The linear vesting mechanism MUST distribute yield at a constant rate over the vesting period.** |
| **REQ‑total‑collateral‑definition** | **Total Collateral Value MUST be calculated as the full value of the reserve, including the overcollateralization buffer.** |
| **REQ‑price‑may‑reflect‑spreads** *(Economic category, but arithmetic‑related)* | **The system MAY reflect spreads and offchain execution expenses in the price during minting and redemption.** |
| **REQ‑price‑floor** *(Economic)* | **Redemption Value MUST act as a hard floor for the market price of apxUSD.** |
| **REQ‑buffer‑visibility** | **The buffer (gap between Redemption Value and Total Collateral Value) MUST be visible to everyone at all times.** |
| **REQ‑redemption‑value‑price** | **The system MUST use Redemption Value as the price for all redemption transactions.** |
| **REQ‑redemption‑value‑uniform** | **Redemption Value MUST apply identically to all participants under both calm and stressed conditions.** |
| **REQ‑hard‑floor‑redemption‑value** | **apxUSD MUST not trade below Redemption Value, which serves as a hard floor.** |
| **REQ‑buffer‑growth‑stress** | **The overcollateralization buffer MUST increase during stress events and MUST NOT be reduced by them.** |
| **REQ‑buffer‑not‑consumed** | **The overcollateralization buffer MUST NOT be consumed during routine redemption operations.** |
| **REQ‑buffer‑preserved‑stress** | **The system MUST preserve the buffer (the difference between Redemption Value and Total Collateral Value) during stress events.** |
| **REQ‑liquidity‑buffer‑size** | **The protocol MUST maintain a liquidity buffer sized against the largest historical TVL drawdowns observed in comparable stablecoins.** |
| **REQ‑catastrophic‑redemption** | **In a catastrophic scenario the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, buffer included, pro‑rata to remaining holders.** |
| **REQ‑mint‑redeem‑at‑redemption‑value** | **The system MUST price all mint and redemption transactions at the Redemption Value, which tracks the underlying basket of preferred shares and cash.** |
| **REQ‑apyusd‑value‑increases‑with‑yield** | **The redemption value of apyUSD SHALL increase over time as yield is distributed.** |

---

## 6. Economic Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑redemption‑at‑redemption‑value** | **The protocol MUST redeem apxUSD at the Redemption Value that tracks the underlying basket.** |
| **REQ‑price‑may‑reflect‑spreads** | **The system MAY reflect spreads and offchain execution expenses in the price during minting and redemption.** |
| **REQ‑liquidity‑buffer‑size** | **The protocol MUST maintain a liquidity buffer sized against the largest historical TVL drawdowns observed in comparable stablecoins.** |
| **REQ‑buffer‑growth‑stress** | **The overcollateralization buffer MUST increase during stress events and MUST NOT be reduced by them.** |
| **REQ‑price‑floor** | **Redemption Value MUST act as a hard floor for the market price of apxUSD.** |
| **REQ‑catastrophic‑redemption** | **In a catastrophic scenario the system MUST set Redemption Value equal to Total Collateral Value and MUST distribute the entire reserve, buffer included, pro‑rata to remaining holders.** |
| **REQ‑mint‑redeem‑at‑redemption‑value** | **The system MUST price all mint and redemption transactions at the Redemption Value, which tracks the underlying basket of preferred shares and cash.** |
| **REQ‑early‑redemption‑fee‑schedule** | **The system MUST calculate an early redemption fee that starts at 3.5 % at request time and declines linearly to 0.1 % by the end of the 3‑day claim window.** |
| **REQ‑early‑unlock‑fee‑linear** | **If a user claims an unlock before the end of the cooldown period, the system MUST apply an early unlock fee that declines linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑yield‑eligible‑cooldown** | **Yield MUST be paid only to apyUSD tokens that are not currently undergoing cooldown.** |
| **REQ‑cooldown‑exclusion** | **When an apyUSD token enters the cooldown phase, it MUST be removed from the pool that receives yield.** |
| **REQ‑immediate‑yield‑on‑lock** | **Newly locked apyUSD MUST begin receiving yield immediately.** |
| **REQ‑credit‑yield** | **The system MUST credit converted apxUSD proceeds to the apyUSD vault via the YieldDistributor.** |
| **REQ‑linear‑vesting‑implementation** | **Yield distribution MUST use a linear vesting mechanism implemented by the LinearVestV0 contract.** |
| **REQ‑continuous‑streaming** | **Yield MUST be streamed continuously over a configurable period rather than as a single lump‑sum distribution.** |
| **REQ‑monthly‑rate‑setting** | **Each month, the system MUST set the yield rate for the following month based on the yield generated by the collateral base in the prior month.** |
| **REQ‑configurable‑period** | **The vesting period over which yield is streamed MUST be configurable by the protocol.** |

---

## 7. Failure‑Mode Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑no‑rehypothecation** | **The protocol MUST NOT rehypothecate or lend deposited apxUSD.** |
| **REQ‑depositforminshares‑slippage** | **The `depositForMinShares` function MUST revert with a slippage error if the previewed share amount is less than `minShares`.** |
| **REQ‑mintformaxassets‑slippage** | **The `mintForMaxAssets` function MUST revert with a slippage error if the required asset amount exceeds `maxAssets`.** |
| **REQ‑withdrawformaxshares‑revert‑on‑slippage** | **The `withdrawForMaxShares` function MUST revert if the number of shares required to withdraw the specified assets exceeds `maxShares`.** |
| **REQ‑redeemforminassets‑revert‑on‑slippage** | **The `redeemForMinAssets` function MUST revert if the amount of assets received for the specified shares is less than `minAssets`.** |
| **REQ‑unlock‑cannot‑cancel** | **The system MUST NOT allow a user to cancel an unlock once it has been initiated.** |
| **REQ‑unlocktoken‑redeem‑after‑cooldown** | **The UnlockToken.redeem function MUST only be callable after the cooldown period for the corresponding apxUSD_unlock tokens has elapsed.** |

---

## 8. State Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑treasury‑allocates‑capital** | **The Offchain Treasury MUST allocate incoming USDC to acquire a basket of preferred assets and short‑term treasury bonds.** |
| **REQ‑custody‑designated‑accounts** | **Acquired preferred assets MUST be held in custody in designated accounts.** |
| **REQ‑redemption‑settlement‑usdc** | **All redemption settlements MUST be made in USDC.** |
| **REQ‑redemption‑liquidate‑usdc** | **When a redemption is processed, the protocol MUST liquidate preferred shares into USDC and MUST NOT transfer preferred shares directly to the redeemer.** |
| **REQ‑hard‑floor‑redemption‑value** | **apxUSD MUST not trade below Redemption Value, which serves as a hard floor.** |
| **REQ‑publish‑total‑collateral** | **The protocol MUST publish the Total Collateral Value, including the overcollateralization buffer, on the dashboard.** |
| **REQ‑buffer‑not‑consumed** | **The overcollateralization buffer MUST NOT be consumed during routine redemption operations.** |
| **REQ‑buffer‑preserved‑stress** | **The system MUST preserve the buffer (the difference between Redemption Value and Total Collateral Value) during stress events.** |
| **REQ‑buffer‑visibility** | **The buffer (gap between Redemption Value and Total Collateral Value) MUST be visible to everyone at all times.** |
| **REQ‑publish‑metrics** | **The system MUST publish Redemption Value and Total Collateral Value on the transparency dashboard.** |
| **REQ‑lock‑apxusd‑for‑apyusd** | **The system SHALL allow users to lock apxUSD in the vault to receive apyUSD.** |
| **REQ‑non‑rebasing‑balance** | **The apyUSD token balances MUST NOT be rebased; balances may only change via minting or burning.** |
| **REQ‑erc4626‑compliance** | **The apyUSD contract MUST implement the ERC‑4626 tokenized vault interface.** |
| **REQ‑upgradeable‑uups** | **The apyUSD contract MUST be upgradeable via the UUPS proxy pattern and governed by AccessManager.** |
| **REQ‑sync‑withdraw‑redeem** | **The apyUSD vault MUST execute withdraw and redeem operations synchronously and return apxUSD_unlock tokens.** |
| **REQ‑unlock‑receipt‑nft‑mint** | **When a user initiates a new redemption/unlock, the system MUST mint an on‑chain Unlock Receipt NFT representing the pending claim.** |
| **REQ‑withdrawal‑pulls‑vested** | **When a withdrawal is requested, the vault MUST automatically pull all vested yield from the LinearVestV0 contract before processing the withdrawal.** |
| **REQ‑totalassets‑includes‑vested** | **The `totalAssets()` function MUST return the sum of the vault's direct apxUSD balance and the vested amount from the LinearVestV0 contract.** |
| **REQ‑deposit‑immediate** | **The vault MUST mint apyUSD shares to the receiver immediately upon successful execution of `deposit(assets, receiver)`.** |
| **REQ‑mint‑immediate** | **The vault MUST mint the requested apyUSD shares to the receiver immediately upon successful execution of `mint(shares, receiver)`.** |
| **REQ‑withdrawal‑returns‑unlock‑token** | **Upon a successful withdrawal, the vault MUST mint a non‑transferable `apxUSD_unlock` token that MAY be redeemed for apxUSD only after a cooldown period.** |
| **REQ‑unlock‑nontransferable** | **The apxUSD_unlock token MUST NOT be transferable.** |
| **REQ‑unlock‑token‑single‑instance** | **There MUST be only one instance of the UnlockToken contract, and it MUST be used exclusively by the apyUSD vault.** |
| **REQ‑vault‑operator‑unlocktoken** | **The apyUSD vault MUST be set as the operator of the UnlockToken contract, allowing it to initiate redeem requests on behalf of users immediately.** |
| **REQ‑unlock‑token‑no‑yield** | **The apxUSD_unlock token MUST NOT earn any yield during the cooldown period.** |

---

## 9. Temporal Requirements  

| ID | Requirement |
|----|-------------|
| **REQ‑vault‑yield‑distribution‑20d** | **The Onchain Vault MUST distribute received yield to apyUSD holders over a 20‑day period.** |
| **REQ‑cooldown‑duration** | **The system MUST enforce a cooldown period of approximately 20 days between a redemption request and the earliest possible claim.** |
| **REQ‑flexible‑claim‑available‑after‑3d** | **The system MUST allow a flexible redemption/unlock claim to be submitted no earlier than 3 days after the request.** |
| **REQ‑add‑assets‑resets‑cooldown** | **If a user adds assets to an existing pending redemption request, the system MUST reset the cooldown period starting from the time of the update.** |
| **REQ‑multiple‑unlock‑requests‑allowed** | **The system MAY allow a user to have multiple concurrent Unlock Receipt NFTs for separate redemption requests.** |
| **REQ‑multiple‑unlocks‑reset‑cooldown** | **When a user initiates a new unlock while a previous unlock is pending, the system MUST reset the cooldown period for the entire pending amount.** |
| **REQ‑unlock‑convert‑after‑cooldown** | **The system MUST only allow conversion of apxUSD_unlock to apxUSD after the cooldown period has elapsed.** |
| **REQ‑early‑redemption‑fee‑schedule** | **The system MUST calculate an early redemption fee that starts at 3.5 % at request time and declines linearly to 0.1 % by the end of the 3‑day claim window.** |
| **REQ‑early‑unlock‑fee‑linear** | **If a user claims an unlock before the end of the cooldown period, the system MUST apply an early unlock fee that declines linearly over time from 3.5 % down to 0.1 %.** |
| **REQ‑continuous‑streaming** | **Yield MUST be streamed continuously over a configurable period rather than as a single lump‑sum distribution.** |
| **REQ‑monthly‑rate‑setting** | **Each month, the system MUST set the yield rate for the following month based on the yield generated by the collateral base in the prior month.** |
| **REQ‑configurable‑period** | **The vesting period over which yield is streamed MUST be configurable by the protocol.** |

---

## 10. Security Considerations  

* **Access Controls** – Whitelisting, jurisdiction checks, deny‑list, and global pause must be enforced on‑chain to prevent unauthorized minting or redemption.  
* **Re‑entrancy** – All external calls (e.g., to the YieldDistributor or treasury) must be performed after state updates to avoid re‑entrancy attacks.  
* **Upgrade Safety** – The UUPS proxy pattern must be combined with AccessManager‑controlled upgrades; only authorized governance may change implementations.  
* **Denial‑of‑Service** – The liquidity buffer and over‑collateralisation buffer protect against mass redemption attacks; buffers are never consumed in routine redemptions.  
* **Front‑end Jurisdiction Enforcement** – While UI checks are not a security boundary, they reduce regulatory risk; on‑chain checks (whitelisting) provide the definitive enforcement.  
* **NFT Minting** – Unlock Receipt NFTs must be non‑transferable to prevent secondary market abuse.  
* **Yield Distribution** – Tokens in cooldown are excluded from the yield pool, preventing double‑counting of yield.  

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

---  

*End of Specification*