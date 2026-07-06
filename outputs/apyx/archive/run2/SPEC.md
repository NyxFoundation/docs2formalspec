# Apyx Protocol Specification  
**Status:** Draft – Working Document  
**Date:** 2026‑07‑06  

---  

## 1. Introduction  

The **Apyx** protocol implements a dual‑token stable‑value system composed of **apxUSD** (a fiat‑backed stablecoin) and **apyUSD** (a yield‑bearing vault token). The protocol is designed to:

* Allow users to deposit USDC and receive apxUSD at a 1:1 peg.  
* Maintain a transparent over‑collateralization buffer that protects the peg under stress.  
* Distribute off‑chain dividend yield to apyUSD holders via an on‑chain LinearVestV0 contract.  
* Enforce strict access‑control and governance mechanisms for minting, redemption, and buffer deployment.  

The specification below captures the functional, economic, and security requirements that the protocol **MUST**, **MAY**, or **SHOULD** satisfy, using the terminology defined in RFC 2119.

---  

## 2. Terminology  

### 2.1 RFC 2119 Keywords  

The following words have the meanings defined in **RFC 2119**:

* **MUST** – required.  
* **MUST NOT** – prohibited.  
* **SHOULD** – recommended but not mandatory.  
* **SHOULD NOT** – discouraged but not prohibited.  
* **MAY** – optional.  
* **OPTIONAL** – may be omitted without violating the specification.  

### 2.2 Domain‑Specific Terms  

| Term | Definition |
|------|------------|
| **apxUSD** | A fiat‑backed stablecoin issued by the protocol, intended to trade at $1. |
| **apyUSD** | A tokenized vault representing locked apxUSD plus accrued yield; implements ERC‑4626. |
| **USDC** | The underlying fiat‑backed stablecoin used as collateral for minting apxUSD. |
| **Total Collateral Value (TCV)** | The market value of all collateral assets **including** the over‑collateralization buffer. |
| **Redemption Value (RV)** | The per‑token value at which apxUSD can be redeemed, derived from the underlying basket of preferred shares. |
| **Over‑collateralization Buffer** | The excess collateral held above the minimum required to back minted apxUSD. |
| **LinearVestV0** | On‑chain contract that streams converted yield over a configurable period (e.g., 20 days). |
| **Vault** | The core contract that locks apxUSD, mints apyUSD, and manages withdrawals. |
| **Unlock Receipt NFT** | An on‑chain NFT representing a pending flexible redemption request. |
| **Whitelist** | A list of participants approved to mint/redeem or perform arbitrage actions. |
| **Deny List** | A list of addresses prohibited from interacting with the vault (e.g., during a pause). |
| **Governance Token Holders** | Holders of the protocol’s governance token who may vote on buffer deployment and other parameters. |
| **Authorized Counterparties** | Entities approved to execute RFQ redemption requests. |
| **Cooldown** | A fixed period (≈ 20 days) during which assets are locked after a redemption request. |
| **Liquidity Buffer** | The portion of collateral reserved to satisfy redemptions even under market stress. |
| **RFQ** | Request‑for‑Quote process used for large‑scale redemption execution. |

---  

## 3. System Model  

### 3.1 Actors  

| Actor | Role |
|-------|------|
| **User** | Deposits USDC, mints apxUSD, locks apxUSD to receive apyUSD, initiates redemption or unlock requests. |
| **Whitelisted Participant** | May mint/redeem apxUSD through designated pathways and perform arbitrage actions. |
| **Governance Token Holder** | Can vote on protocol parameters, including deployment of the over‑collateralization buffer. |
| **Authorized Counterparty** | Executes RFQ redemption requests on behalf of users. |
| **Protocol Contracts** | Vault, LinearVestV0, Unlock Receipt NFT, Pause controller, etc. |
| **External Oracle** | Supplies market prices for USDC, apxUSD, and the underlying basket of preferred shares. |

### 3.2 State Variables  

* `totalCollateralValue` – market value of all collateral assets (including buffer).  
* `redemptionValue` – current per‑token redemption price.  
* `bufferAmount = totalCollateralValue – (totalMintedApxUSD × redemptionValue)`.  
* `exchangeRate = totalAssets / totalSupply` for the apyUSD vault (reflects accrued yield).  
* `paused` – global pause flag.  
* `denyList[address]` – mapping of prohibited addresses.  
* `whitelist[address]` – mapping of eligible participants.  

### 3.3 Operations  

| Operation | Description |
|-----------|-------------|
| `depositForMinShares` | User deposits USDC, receives at least a minimum number of apxUSD shares. |
| `mintForMaxAssets` | User specifies a maximum USDC amount to receive a fixed number of apxUSD. |
| `withdrawForMaxShares` | User withdraws USDC by burning up to a maximum number of apxUSD shares. |
| `redeemForMinAssets` | User redeems apxUSD for at least a minimum amount of USDC. |
| `lock` | Synchronously lock apxUSD and mint apyUSD shares (ERC‑4626). |
| `unlock` | Initiate flexible redemption, mint Unlock Receipt NFT. |
| `claimUnlock` | After the unlock period, claim USDC and burn the receipt. |
| `pause` / `unpause` | Global emergency stop that blocks deposits/mints. |
| `voteDeployBuffer` | Governance vote to release a portion of the buffer. |
| `rfqSubmit` / `rfqExecute` | Structured redemption request processed by an authorized counterparty. |

---  

## 4. Requirements  

Each requirement is presented as a separate clause, prefixed with **REQ‑\<ID\>**. The clause text reproduces the exact RFC 2119 statement from the source material, followed by a brief elaboration.

### 4.1 State Requirements  

| # | Requirement |
|---|-------------|
| **4.1.1 REQ‑deposit-mint-apxusd** | **Statement:** *The system **MUST** allow users to deposit USDC in order to acquire apxUSD.*<br>**Elaboration:** Users interact with the `depositForMinShares` function; the protocol credits the depositor with apxUSD at a 1:1 peg (see §5.3). |
| **4.1.2 REQ‑apxusd-issuance-price** | **Statement:** *The protocol **MUST** issue new apxUSD at a price of exactly $1 per token.*<br>**Elaboration:** The minting logic enforces a fixed conversion rate between USDC and apxUSD; any deviation causes the transaction to revert. |
| **4.1.3 REQ‑redemption-uses-redemption-value** | **Statement:** *All redemption transactions **MUST** be executed at the current Redemption Value, which tracks the underlying basket of preferred shares and applies identically to all participants.*<br>**Elaboration:** The `redeemForMinAssets` operation uses `redemptionValue` as the per‑token price, ensuring uniform treatment. |
| **4.1.4 REQ‑overcollateralization-buffer-maintenance** | **Statement:** *The system **MUST** keep apxUSD over‑collateralized by maintaining an over‑collateralization buffer that grows during stress events, is not consumed by routine redemptions, and ensures total minted apxUSD never exceeds the market value of the collateral minus the required margin.*<br>**Elaboration:** Buffer growth is driven by market‑price feeds; routine redemptions draw only the base collateral, preserving the buffer. |
| **4.1.5 REQ‑total-collateral-metric** | **Statement:** *The Total Collateral Value metric **MUST** represent the full reserve value including the over‑collateralization buffer and **MUST** be publicly available on the dashboard at all times.*<br>**Elaboration:** The dashboard reads `totalCollateralValue` from the on‑chain contract and displays it in real time. |
| **4.1.6 REQ‑buffer-visibility** | **Statement:** *The buffer amount (the gap between Redemption Value and Total Collateral Value) **MUST** be visible to all users at all times.*<br>**Elaboration:** A read‑only view function `bufferAmount()` returns the current gap; UI components expose this value. |
| **4.1.7 REQ‑liquidity-buffer-maintenance** | **Statement:** *The liquidity buffer **MUST** be at least as large as the largest historical TVL drawdown among comparable stablecoins and must remain available at all times, including outside traditional trading hours and on weekends.*<br>**Elaboration:** The buffer is held in highly liquid assets (e.g., USDC) and is never locked, guaranteeing immediate availability. |
| **4.1.8 REQ‑no-rehypothecation** | **Statement:** *The protocol **MUST NOT** rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose.*<br>**Elaboration:** All collateral remains in the vault; no external contracts receive approval to transfer it. |
| **4.1.9 REQ‑yield-distribution** | **Statement:** *The Onchain Vault **MUST** receive converted apxUSD yield from off‑chain dividend collections and stream it continuously over a configurable period (e.g., 20 days) using the LinearVestV0 contract. Yield is paid only to apyUSD tokens not in cooldown; newly locked apyUSD begins receiving yield immediately, while tokens in cooldown are excluded.*<br>**Elaboration:** The vault calls `LinearVestV0.streamYield(amount, period)` after each dividend collection; the streaming logic checks the cooldown status of each holder. |
| **4.1.10 REQ‑exchange-rate-increase** | **Statement:** *The exchange rate between apyUSD and apxUSD **MUST** increase over time to reflect accrued yield.*<br>**Elaboration:** `exchangeRate = totalAssets / totalSupply` grows as streamed yield augments `totalAssets`. |
| **4.1.11 REQ‑no-rebase** | **Statement:** *apyUSD token balances **MUST NOT** rebase.*<br>**Elaboration:** Balances change only via mint, burn, or transfer; the contract does not adjust balances proportionally to external factors. |
| **4.1.12 REQ‑erc4626-compliance** | **Statement:** *The apyUSD contract **MUST** implement the ERC‑4626 tokenized vault interface.*<br>**Elaboration:** All required ERC‑4626 view and mutating functions (`deposit`, `mint`, `withdraw`, `redeem`, `totalAssets`, etc.) are present and conform to the standard. |
| **4.1.13 REQ‑locking-mechanism** | **Statement:** *The vault **MUST** allow users to lock apxUSD and receive apyUSD shares synchronously within the same transaction. The apyUSD contract **MUST** implement ERC‑4626. `totalAssets()` must include both the vault’s direct apxUSD balance and the vested amount from LinearVestV0. Deposits and mints calculate shares using `totalAssets()`, withdrawals pull all vested yield before processing and burn shares immediately.*<br>**Elaboration:** A single atomic transaction executes `transferFrom` of apxUSD, updates `totalAssets`, and mints the appropriate number of apyUSD shares. |
| **4.1.14 REQ‑redemption-request-process** | **Statement:** *When a user submits a redemption request, the system **MUST** lock the user's assets, allow at most one pending request per user, enforce a cooldown of approximately 20 days before claim, reset the cooldown if assets are added, and ensure no yield accrues and the exchange rate remains fixed during the cooldown period.*<br>**Elaboration:** The contract records `requestTimestamp`; any additional deposit before claim updates the timestamp, effectively resetting the cooldown. |
| **4.1.15 REQ‑flexible-redemption** | **Statement:** *The flexible redemption mechanism **MUST** allow users to initiate unlocks that mint an on‑chain Unlock Receipt NFT. Unlocks become claimable after three days, with an early unlock fee that starts at 3.5 % and declines linearly to a minimum of 0.1 %. Users may have multiple unlock requests simultaneously; adding assets resets the cooldown for the combined amount. Unlocks cannot be cancelled.*<br>**Elaboration:** Each unlock request creates a distinct NFT containing the amount and start time; the fee schedule is enforced on early claim. |
| **4.1.16 REQ‑slippage-revert-rules** | **Statement:** *`depositForMinShares`, `mintForMaxAssets`, `withdrawForMaxShares`, and `redeemForMinAssets` **MUST** revert if the operation would result in fewer shares, exceed max assets, exceed max shares, or receive less than the minimum assets respectively.*<br>**Elaboration:** The functions perform pre‑flight checks against the user‑supplied limits and revert with a descriptive error if violated. |
| **4.1.17 REQ‑arbitrage-mint-pathway** | **Statement:** *The system **MUST** provide a minting pathway that eligible participants may use to mint apxUSD under predefined terms when apxUSD trades above $1.*<br>**Elaboration:** An on‑chain `arbitrageMint` function is callable only by whitelisted arbitrageurs; it mints apxUSD at the peg and transfers the excess USDC to the buffer. |
| **4.1.18 REQ‑arbitrage-redeem-pathway** | **Statement:** *The system **MUST** provide a redemption pathway that eligible participants may use to redeem apxUSD for dollar‑equivalent value when apxUSD trades below $1.*<br>**Elaboration:** An on‑chain `arbitrageRedeem` function allows whitelisted arbitrageurs to burn apxUSD and receive USDC at the Redemption Value, draining the buffer if necessary. |
| **4.1.19 REQ‑whitelist-arbitrage-access** | **Statement:** *The system **MUST** restrict arbitrage minting and redemption actions to participants that are on the eligible whitelist.*<br>**Elaboration:** Both `arbitrageMint` and `arbitrageRedeem` check `whitelist[address]` before proceeding. |

### 4.2 Access‑Control Requirements  

| # | Requirement |
|---|-------------|
| **4.2.1 REQ‑whitelist-mint-redeem** | **Statement:** *Only participants who are whitelisted and located in permitted jurisdictions **MAY** mint or redeem apxUSD through the protocol's designated pathways.*<br>**Elaboration:** The contract validates the caller against `whitelist` and a jurisdiction‑check oracle before allowing mint or redeem operations. |
| **4.2.2 REQ‑access-control-pause-denylist** | **Statement:** *If the vault is globally paused, any deposit or mint operation **MUST** revert. Additionally, if the caller or receiver is on the deny list, deposit or mint **MUST** revert immediately.*<br>**Elaboration:** The `paused` flag and `denyList` mapping are consulted at the start of `deposit*` and `mint*` functions; violations trigger a revert with error code `Paused` or `DenyListed`. |
| **4.2.3 REQ‑rfq-redemption-process** | **Statement:** *The RFQ redemption system **MUST** allow users to submit redemption requests through a structured process, and **MUST** permit only approved counterparties to execute those requests.*<br>**Elaboration:** Users call `rfqSubmit`; only addresses in `authorizedCounterparties` may call `rfqExecute` to settle the request. |
| **4.2.4 REQ‑governance-deploy-buffer** | **Statement:** *Governance token holders **MUST** be able to vote to deploy a portion of the overcollateralization buffer in intermediate‑risk scenarios.*<br>**Elaboration:** A governance proposal can call `deployBuffer(amount)`; execution succeeds only if the proposal passes the required quorum. |

### 4.3 Economic Requirements  

| # | Requirement |
|---|-------------|
| **4.3.1 REQ‑no-rehypothecation** *(re‑listed for emphasis)* | **Statement:** *The protocol **MUST NOT** rehypothecate, lend, or otherwise utilize deposited apxUSD for any purpose.*<br>**Elaboration:** Collateral is held in a non‑transferable vault; no external contracts receive `approve` rights. |
| **4.3.2 REQ‑liquidity-buffer-maintenance** *(re‑listed for emphasis)* | **Statement:** *The liquidity buffer **MUST** be at least as large as the largest historical TVL drawdown among comparable stablecoins and must remain available at all times, including outside traditional trading hours and on weekends.*<br>**Elaboration:** The buffer is composed of instantly liquid assets; no time‑locked mechanisms are applied. |
| **4.3.3 REQ‑price-floor** | **Statement:** *The market price of apxUSD **MUST** never fall below the Redemption Value.*<br>**Elaboration:** The over‑collateralization buffer and arbitrage pathways are designed to enforce this floor; market‑price deviations trigger automatic arbitrage actions. |
| **4.3.4 REQ‑catastrophic-backstop** | **Statement:** *In a catastrophic scenario, the protocol **MUST** set Redemption Value equal to Total Collateral Value and **MUST** distribute the entire reserve, including the buffer, pro‑rata to remaining holders.*<br>**Elaboration:** A governance‑triggered `activateBackstop()` function updates `redemptionValue` and initiates a proportional distribution of all assets. |

### 4.4 Failure‑Handling Requirements  

| # | Requirement |
|---|-------------|
| **4.4.1 REQ‑slippage-revert-rules** *(re‑listed for emphasis)* | **Statement:** *`depositForMinShares`, `mintForMaxAssets`, `withdrawForMaxShares`, and `redeemForMinAssets` **MUST** revert if the operation would result in fewer shares, exceed max assets, exceed max shares, or receive less than the minimum assets respectively.*<br>**Elaboration:** The contract checks user‑provided bounds before state changes; any violation aborts the transaction. |
| **4.4.2 REQ‑catastrophic-backstop** *(re‑listed for emphasis)* | **Statement:** *In a catastrophic scenario, the protocol **MUST** set Redemption Value equal to Total Collateral Value and **MUST** distribute the entire reserve, including the buffer, pro‑rata to remaining holders.*<br>**Elaboration:** This ensures that no holder is left with a negative net value; the distribution is performed atomically. |

---  

## 5. Security Considerations  

1. **Access‑Control Integrity** – Whitelist, deny‑list, and authorized‑counterparty checks must be immutable except via governance‑approved proposals. Any bypass would enable unauthorized minting or redemption, breaking the peg.  
2. **Reentrancy Protection** – All external calls (e.g., token transfers, NFT minting) are placed after state updates and guarded by the `nonReentrant` modifier to prevent re‑entrancy attacks.  
3. **Oracle Manipulation** – Redemption Value and market price feeds are sourced from multiple independent oracles; a consensus mechanism mitigates single‑oracle manipulation.  
4. **Buffer Exhaustion** – The over‑collateralization buffer is designed to absorb extreme market stress. Nevertheless, a catastrophic backstop is defined to protect holders if the buffer is depleted.  
5. **Upgrade Safety** – The vault and LinearVestV0 contracts are deployed behind a proxy with a transparent upgrade pattern; only governance with a super‑majority can authorize upgrades.  
6. **Denial‑of‑Service (DoS)** – The `pause` mechanism allows rapid halting of deposits/mints in case of DoS attacks, while redemption pathways remain functional for existing holders.  

---  

## 6. References  

| # | Source |
|---|--------|
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