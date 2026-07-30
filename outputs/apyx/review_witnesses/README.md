# 反例 witness — `code_review_lean.md` の裏付け

`code_review_lean.md` §1.0 / §1.4 で報告した過大主張を、**Lean kernel で検証可能な具体反例**として
固定したものです。すべて `by decide` / `rfl` のみで、`native_decide` は使っていません。

## 実行方法

```bash
cd lean
lake build D2fsSpecs                     # 先にライブラリをビルド
lake env lean ../outputs/apyx/review_witnesses/W1_stale_rate_dilution.lean
```

エラー出力がなければ、そのファイル中の全 `example` が kernel で通ったということです
(5ファイルすべて 2026-07-30 時点で通過を確認済み)。

## 各ファイルの内容

| ファイル | 反証する README の主張 | 内容 |
|---|---|---|
| `W1_stale_rate_dilution.lean` | §4.2「No dilution — A deposit by someone else never lowers an existing holder's redeemable value」 | 手作り状態から。`no_dilution` の仮説 `hTS` / `hbacked` は**両方成立**するのに、A の真の償還価値は 200 → 150 に下落。定理の結論はキャッシュレートで測るため「100 → 150 に増加」と報告する |
| `W2_honest_lifecycle_dilution.lean` | 同上 +「Share-price monotonicity」 | **最重要。** レート整合な初期状態から、正直なロールだけの操作列 `[lockApxUSD A, creditYield(本物の distributor), tick, lockApxUSD B]` で `computeExchangeRate w4 < computeExchangeRate w3` — **真の株価が下落**。A は 25% 希釈 (200→150)、B は 100 apxUSD が 150 になる |
| `W3_inflation_attack.lean` | §4.2「Inflation-attack immunity — structurally impossible」 | レート整合・非退化状態 (攻撃者が1株、vault に 200 資産、株価 200·ray)。被害者が 150 apxUSD を lock → **0 株**、150 全額喪失。攻撃者の1株は 200 → 350 に。`no_dilution` の結論は**攻撃者について**成立する |
| `W4_zero_rate_drain.lean` | §4.2「No free extraction」/ vest の「no early drain」 | (a) `exchangeRate = 0` (= `default` 値) で `withdrawShares 100 0 = 0` となりガード `apyUSDBal < 0` が偽になるため、**0 株しか持たないアドレスが vault を全額**自分の unlock ポジションに移す (株の焼却なし)。(b) `setVestPeriod 0` が vest ストリーム 1000 全額を1ステップで即時実現 |
| `W5_first_depositor_steal.lean` | 同上 (first-depositor 版) | `default` 由来状態で最初の預入者が 100 apxUSD → 0 株、その後攻撃者が 1 apxUSD で 1 株を得て vault 全額 101 を `redeem` で奪う |

## 共通の根本原因

1. **`exchangeRate` がキャッシュで、レート整合の不変量がどこにも無い。**
   `Op.lockApxUSD` は**格納された古いレート**で株を発行し (`Apyx.lean:594`)、
   `updateExchangeRate` はその**後**に呼ばれます。`creditYield` / `tick` / vesting は
   キャッシュを更新しないので、vault 操作の合間はキャッシュが真の価格より必ず低くなります。
   `s.exchangeRate = computeExchangeRate s` を述べた定義・定理は両ファイルに存在しません。

2. **`lockShares = amount * ray / exchangeRate` に下限チェックが無い。**
   `amount · ray < exchangeRate` のとき floor して 0 になり、これが「存在しない」とされた
   raw donation primitive です。`depositForMinShares` (`Apyx.lean:838`) は存在しますが、
   どの安全性定理もそれを使っていません。

## 実装側への含意

1 は**モデルの人工物ではなく実装に持ち帰るべき指摘**です。`lockApxUSD` が価格決定の**前**に
`pullVestedYield` / `updateExchangeRate` を呼ぶか、レート整合を帰納的不変量として証明する必要が
あります。2 は ERC-4626 の標準的な緩和策 (virtual shares / offset、または最小株数チェック) の
有無を deployed contract 側で確認すべき項目です。
