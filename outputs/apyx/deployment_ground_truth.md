# 実デプロイのグラウンドトゥルース (2026-07-30 読み取り)

`code_review_lean.md` の指摘を修正する際の根拠。RPC は `https://ethereum-rpc.publicnode.com`
(block `0x1874477` = 25,642,103)、ソースは **sourcify v2** から取得
(`https://sourcify.dev/server/v2/contract/1/<impl>?fields=sources`)。

## apyUSD — ERC-4626 vault

- プロキシ `0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A` (ERC-1967)
- 実装 `0xfd616567ecc1607f61073951a1e822f7315bb112` → `src/ApyUSD.sol` (solidity 0.8.30,
  OpenZeppelin upgradeable **5.5.0**)、検証済みソース73ファイル

### 読み取った実測値

| 呼び出し | 値 |
|---|---|
| `decimals()` | 18 |
| `totalSupply()` | 128,282,547.748284580697224788 |
| `totalAssets()` | 180,056,554.469551067918902045 |
| `asset()` | `0x98a878b1cd98131b271883b390f68d2c90674665` (= apxUSD) |
| `apxUSD.balanceOf(apyUSD)` | 179,962,509.922863992091448078 |
| **差 (= vesting 中の yield)** | **94,044.546687075827453967 apxUSD** |
| `convertToShares(1e18)` | 0.712456972900579049 |
| `convertToAssets(1e18)` | 1.403593533415451045 |
| `previewDeposit(1 wei)` | **0** |
| `previewRedeem(1 wei)` | **0** |

`convertToAssets(1e18)` は `10^18 * totalAssets / totalSupply` の floor と**整数レベルで厳密一致**
(検算済み)。つまり株価はキャッシュされておらず、毎回ライブに計算されます。

### ソースから確定した事実

1. **`totalAssets()` はライブ view**:
   ```solidity
   function totalAssets() public view override returns (uint256) {
       uint256 vaultBalance = IERC20(asset()).balanceOf(address(this));
       uint256 vestedYield = 0;
       if (address($.vesting) != address(0)) vestedYield = $.vesting.vestedAmount();
       return vaultBalance + vestedYield;
   }
   ```
   → **モデルの `totalAssets = vaultApxUSDBal + vestedAmount` は形として忠実**。
   ただし実装は**格納レートを一切持たない**ので、`State.exchangeRate` フィールドは
   モデルの人工物。時間経過で `vestedAmount()` が増えるだけで株価が動きます。

2. **`_decimalsOffset() = 0`** — docstring は
   「Returns the decimals offset for **inflation-attack protection**」と書きながら 0 を返す。
   → 仮想株による inflation 保護は **OZ のベースライン (+1) のみ**。

3. **変換式は OZ 5.5.0 の標準形** (`ERC4626Upgradeable`):
   ```solidity
   _convertToShares(assets, r) = assets.mulDiv(totalSupply() + 10**_decimalsOffset(), totalAssets() + 1, r)
   _convertToAssets(shares, r) = shares.mulDiv(totalAssets() + 1, totalSupply() + 10**_decimalsOffset(), r)
   ```
   `_decimalsOffset() = 0` なので `10**0 = 1`。
   → **分母は常に ≥ 1 で、ゼロ除算が構造的に起こり得ません。**
   `previewDeposit = _convertToShares(·, Floor)`、`previewWithdraw = _convertToShares(·, Ceil)`、
   `previewMint = _convertToAssets(·, Ceil)`、`previewRedeem = _convertToAssets(·, Floor)`。

4. **`deposit()` は 0 株でも revert しません** (OZ 既定):
   `shares = previewDeposit(assets); _deposit(...)`。株価未満の dust は 0 株になります
   (`previewDeposit(1 wei) = 0` で実測)。ユーザー側の緩和は `depositForMinShares`。
   なお `burnWithAssets` 系は `if (shares == 0) revert InvalidAmount("shares", 0);` を持ちます。

5. **`withdraw` / `redeem` は価格決定の前に vested yield を実現します**:
   `$.vesting.pullVestedYield();` を `super._withdraw` の前に呼び、コメントは
   「Pull vested yield so liquid assets match totalAssets().」。
   → モデルの `pullVestedYield` を `withdraw`/`redeem` の先頭で呼ぶ設計は忠実。

6. **vault 側 `unlockingFee`** が `_withdraw` で前払い徴収されます (production target 10 bps)。
   モデルの flexible 早期解除手数料とは**別物**で、現モデルには対応物がありません。

7. スリッページラッパー4本 (`depositForMinShares`, `mintForMaxAssets`,
   `withdrawForMaxShares`, `redeemForMinAssets`) は実在します。

## Lean 修正への含意

| レビュー指摘 | 実装での事実 | 修正方針 |
|---|---|---|
| §1.0-a レート古さによる希釈 (W1/W2) | 実装は**ライブ計算、格納レートなし** | **モデルの人工物**。価格決定を `computeExchangeRate` に切り替える。これで W1/W2 は再現しなくなる |
| §1.0-c `x/0 = 0` で vault 全額流出 (W4) | 実装の分母は `totalAssets + 1` / `totalSupply + 1` で**常に ≥ 1** | 分母に `+1` を入れて忠実化。ゼロ除算が構造的に消え W4 も消える |
| §1.0-b inflation attack (W3/W5) | `_decimalsOffset = 0`、`deposit` は 0 株を revert しない | **実装に忠実な弱点**。`+1` 仮想株を入れた上で「dust は株価未満で 0 株」を境界付き定理として残し、`depositForMinShares` を推奨に格上げ |
| §2.5 `mintForMaxAssets` が株数不足 | 実装は `previewMint` (Ceil) で資産を計算し `shares` を厳密に発行 | モデルを `mint(shares)` が厳密に `shares` を渡す形に直す |
| §2.3 手数料の起点 | vault 側 `unlockingFee` は別物、flexible 手数料は receipt 側 | 起点の扱いは docs 側と突き合わせて再確認が必要 |

**未取得**: `LinearVestV0` のアドレス (apyUSD の `vesting()` getter から取得可能)、
`RedemptionPoolV0` が実際にデプロイされ稼働中かどうか (model.md §5「Not verified」のまま)。
