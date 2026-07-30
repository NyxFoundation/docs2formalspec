# 回帰テスト — ERC-4626 価格決定の修正

`code_review_lean.md` §1.0 で報告した5つの反例を、**修正後の**モデルに向け直したものです。
修正前はこれらが README §4.2 の見出し主張の**違反を証明**していました。現在は
`Regression.lean` が修正後の正しい挙動を固定しており、穴が黙って再発しないようにしています。

すべて `by decide` / `rfl` のみで、`native_decide` は使っていません。

## 実行方法

```bash
cd lean
lake build D2fsSpecs
lake env lean ../outputs/apyx/review_witnesses/Regression.lean
```

エラー出力がなければ全アサーションが kernel で通ったということです。

## 何を修正したか

根拠は [`../deployment_ground_truth.md`](../deployment_ground_truth.md)(検証済みソースと
mainnet の実測値)。

1. **`computeExchangeRate` をライブ価格にした。**
   `((totalAssets s + 1) * ray) / (totalSupply_apyUSD + 1)`。
   デプロイ済み `ApyUSD` は**格納レートを持ちません** — `totalAssets()` は
   `asset.balanceOf(this) + vesting.vestedAmount()` を返す `view` で、変換は毎回そこから
   計算されます(`convertToAssets(1e18)` が `1e18 * totalAssets / totalSupply` に整数レベルで
   一致することを実測で確認)。
   `+1` は OpenZeppelin 5.5.0 の仮想株・仮想資産(`_decimalsOffset() = 0` なので `10**0 = 1`)。

2. **すべての変換と `step` の全分岐がそれを参照する。**
   `exchangeRate` **フィールド**は「公表された記録」になり、価格決定の入力ではなくなりました。

## 各セクションが守るもの

| セクション | 旧ファイル | 反証していた README §4.2 の主張 | 現在の状態 |
|---|---|---|---|
| **R1/R2** | `W1_stale_rate_dilution` / `W2_honest_lifecycle_dilution` | 「No dilution」「Share-price monotonicity」 | **解消。** 預入者は公正な 50 株を受け取り(旧: 100 株)、既存ホルダーの償還価値は 199 のまま(旧: 200→150)、`computeExchangeRate w3 ≤ computeExchangeRate w4` が成立 |
| **R3** | `W3_inflation_attack` | 「Inflation-attack immunity — structurally impossible」 | **緩和されたが解消はしていない(意図的)。** 被害者は 0 株ではなく 1 株を受け取る。ただし 150 入れて 117 しか戻らず、攻撃者は 100→117 を得る |
| **R4** | `W4_zero_rate_drain` | 「No free extraction」 | **構造的に解消。** 分母が `totalSupply_apyUSD + 1` で常に正になり、`x / 0 = 0` の穴が到達不能に。0 株のアドレスの `withdraw` は revert |
| **R5** | `W5_first_depositor_steal` | 同上 (first-depositor 版) | **解消。** 最初の預入者は 100 apxUSD に対して 100 株を受け取る(旧: 0 株) |

## R3 を閉じきっていない理由

デプロイ済みコントラクトの `_decimalsOffset()` が **`0`** を返します
(docstring 自身が「Returns the decimals offset for **inflation-attack protection**」と
書いているにもかかわらず)。したがって構造的防御は OpenZeppelin の仮想株1つだけで、
`deposit()` は 0 株でも revert しません(`previewDeposit(1 wei) = 0` を実測)。

**チェーンが持っていない保護をモデルに入れるのは誤った修正**なので、R3 は
「忠実な残存弱点」として境界付きで残しています。対策は2方向:

- ユーザー側: `depositForMinShares`(実在するスリッページラッパー)を使う
- プロトコル側: `_decimalsOffset()` を非ゼロにする

現行デプロイでは apyUSD の発行済株数が 1.28億株あるため、この経路の実害は現時点では
無視できる水準です。危険なのは新規 vault や供給が枯れた状態です。
