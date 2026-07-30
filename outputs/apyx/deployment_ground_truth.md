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
| §1.0-c `x/0 = 0` で vault 全額流出 (W4) | 実装の分母は `totalAssets + 1` / `totalSupply + 1` で**常に ≥ 1**。さらに `previewWithdraw = ceil(assets·(TS+1)/(TA+1))` なので `assets ≥ 1` なら結果は必ず ≥ 1 | **2段階必要だった。** `+1` は分母のゼロを消すだけで、商が 0 に floor する余地は残り W4 は再現した。`previewWithdraw ≥ 1` を `withdraw` のガードとして明示的に入れて初めて閉じた (`README` §9.3 項2、`Regression.lean` §R4b) |
| §1.0-b inflation attack (W3/W5) | `_decimalsOffset = 0`、`deposit` は 0 株を revert しない | **実装に忠実な弱点**。`+1` 仮想株を入れた上で「dust は株価未満で 0 株」を境界付き定理として残し、`depositForMinShares` を推奨に格上げ |
| §2.5 `mintForMaxAssets` が株数不足 | 実装は `previewMint` (Ceil) で資産を計算し `shares` を厳密に発行 | **見送った。** `previewMint` の Ceil 化は実施したが、株数厳密化には share 単位の `Op` コンストラクタが必要で、追加すると全網羅証明が kernel の深い再帰で壊れた。定義に逸脱を明記して境界付きで残している |
| §2.3 手数料の起点 | vault 側 `unlockingFee` は別物、flexible 手数料は receipt 側 | 起点の扱いは docs 側と突き合わせて再確認が必要 |

## 追加で再取得できた値 (本セッション)

| 呼び出し | 値 |
|---|---|
| `apyUSD.vesting()` | `0x0d62b4cc02b4b51ed19ddf41d7a7979cf394c99f` (LinearVest) |
| `apyUSD.unlockingFee()` | `1000000000000000` = 1e15 = **10 bps** (コントラクトの docstring が言う production target と一致) |
| `apxUSD.balanceOf(UnlockToken 0x93775E2d…BF4e6)` | 24,936.065068259672231340 apxUSD — `README` §4.4 の「24,936 apxUSD」と一致 |
| `apxUSD.totalSupply()` | 327,073,514.822856436999740169 |

## このファイルの範囲

**ここに記録されているのは apyUSD / ERC-4626 周りと上表の読み取りだけです。** `README` §4.4-§4.6 と
`model.md` §6-§7 が引用している残りの live 値 — `CommitToken` の
6,226,697 apxUSD (供給の 1.90%)、`ApyxRedemptionOracle` の `cap() = 1e8` と published answer
`90365900`、`AccessManager` のロール/遅延ラダー、`expiration() = 7 days`、スケジュール済み操作の
896/169/5、Safe の 4-of-6 / 3-of-6、`MinterV0` の 50M/day — は**このファイルには記録されていません**。
それらは以前のセッションでの読み取りで、artifact が残っていません。Lean 側の定数
(`liveDeployments`, `liveAmount`, `queuedAmount`, `par`) は prose と一致していますが、
チェーンからの再取得はされていません。docs 内のアドレスが省略形 (`0x17122d86…871e` など) で
記載されているため本セッションでは呼び出せませんでした。「未記録の live read」として扱ってください。
完全なアドレスを補えば同じ手順 (`eth_call` + sourcify v2) で再検証できます。

`vesting()` = `0x0d62b4cc02b4b51ed19ddf41d7a7979cf394c99f` (LinearVest) は本セッションで取得済み。
`RedemptionPoolV0` が実際にデプロイされ稼働中かどうかは未確認 (model.md §5「Not verified」のまま)。

---

## 追加取得 (2026-07-30、第2セッション) — モデルに無い手数料機構

sourcify から `src/ApyUSD.sol` / `src/FeeCurve.sol` を再取得し、プロキシ
`0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A` に対してライブ読み取りを実施。

| 呼び出し | 値 | 含意 |
|---|---|---|
| `unlockingFee()` | `1e15` = **10 bps** | 稼働中。モデルには対応する項が無い |
| `feeWallet()` | `0x6f93635f2a1c19b4f7f1bd9ba655f6a073c629dc` | ゼロでもvault自身でもないので、手数料は**vault外へ出る** |
| `unlockToken()` | `0x93775e2dfa4e716c361a1f53f212c7ae031bf4e6` | |
| `receipt()` | `0x9bf51f33955ec70f87c4b5c49441815589043237` | |
| `totalSupply()` | 128,449,132.273516284371364816 | |
| `totalAssets()` | 180,310,584.281533099520335160 | |

### 1. vault側 `unlockingFee` — モデルに存在しない

`ApyUSD._withdraw` は毎回の `withdraw`/`redeem` で手数料を徴収する:

```solidity
uint256 fee = _feeOnRaw(assets, $.unlockingFee);
super._withdraw(caller, address(this), owner, assets + fee, shares);  // GROSS で株を焼く
if (fee > 0 && feeRecipient != address(0) && feeRecipient != address(this))
    IERC20(asset()).safeTransfer(feeRecipient, fee);                  // 手数料は vault を出る
IERC20(asset()).approve(address($.unlockReceipt), assets);
$.unlockReceipt.mint(receiver, SafeCast.toUint208(assets));           // receipt は NET を預かる
```

`_feeOnRaw` / `_feeOnTotal` はいずれも `Math.Rounding.Ceil`(1 wei 未満に丸め消えない)。
`setUnlockingFee` は `fee <= MAX_FEE`(5%)のみを課す。

→ モデルの `Op.withdraw` は `assets` 分だけ株を焼き `assets` を position に入れる。
実装は `assets + fee` 分焼き、`fee` は系外へ出る。**モデルは出金者を過小請求し、vault を過大計上**する。

### 2. `receiver == owner` ガード — モデルに存在しない

`_withdraw` は `if (receiver != owner) revert InvalidCaller();` を持つ。モデルの
`Op.withdraw assets receiver` の4ガードは receiver に一切言及しない(`withdraw_receiver_unconstrained`)。

### 3. `FeeCurve` — モデルの形が違う

`src/FeeCurve.sol` の `fee()` はクランプ付きパラメータ曲線
(`minFee`, `maxFee`, `minDuration`, `maxDuration`, `curvature`)。定数境界は
`MAX_FEE = 0.05e18`、`MAX_DURATION = 90 days`、`curvature ∈ [0.1e18, 10e18]`。

**重要**: docstring が明示するとおり `minDuration` は**ロック期間と曲線のゼロ点を兼ねる**。
`fee()` は `elapsed <= minDuration` で `maxFee` を返すので、**最初に請求可能になる瞬間の
手数料はちょうど `maxFee`**。モデルは `minFlexibleClaim = 3 day` と `cooldownPeriod = 20 day`
に役割を分離しているため 2.99% までしか届かず、README §2.3 の「3.5% は到達不能」は
**モデル由来の人工物**だった(`feeRate_at_first_claim` で訂正)。

以上は [`DeploymentFees.lean`](DeploymentFees.lean) に形式化済み(12定理、公理は
`propext` / `Quot.sound` のみ)。
