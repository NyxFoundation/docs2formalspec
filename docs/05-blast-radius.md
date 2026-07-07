# スコープ外攻撃に対する被害上限(blast radius)の形式証明 — DeFi版 設計メモ

(調査日 2026-07-07。docs2formalspec の次期テーマ: 「モデル内の要件証明」から「モデル外の攻撃に対する被害上限証明」への拡張)

## 実装ステータス(2026-07-07)

`lean/D2fsSpecs/BlastRadius.lean`(単一モジュール、namespace `Apyx`、公開定理35本、sorry 0・vacuous 0、全て `propext`/`Quot.sound` のみに依存)。`Apyx.lean`(81要件定理)は無傷 — blast-radius層は完全に追加的。

- **Tier 1(T1-T4)完了**: pauser/yieldDistributor/admin の各ロール侵害が残高・供給量フィールドに触れないこと(単発+トレースレベル)。T4ヘッドライン `user_assets_immune_to_total_key_compromise` = 全鍵漏洩でも「署名せずRFQ標的でない傍観者」は残高を失わない。
- **Tier 2(T5-T6)完了**: `no_theft_ledger`(傍観者の transferable 残高がトレース全体で非減少)、`oracle_alone_preserves_balances`(oracle鍵単独では抽出ゼロ)、`redeem_payout_formula` + `redeem_payout_has_no_cap`(払戻額 = `amount × redemptionValue / ray`、`redemptionValue` にクランプが無いため払戻額に上限が存在しないことを witness 付きで証明 — Tier 3 の動機)。
- **未了**: 能動的no-extraction(caller双対台帳、in-scope安全性の能動的半分)、Tier 3(T7 rate-limit線形上限 / T8 timelock退出保証 / T9 区画化 / T10 結託表 — いずれも base `step` をラップした `step2` が必要)。

インフラ: `execTrace`(revert-skip意味論のトレース実行器)、ロール述語 `PauserOp`/`DistributorOp`/`AdminOp`/`OracleOp`、各opの exact-effect frame lemma、`reserve_outflow_only_via_redemption`(reserve減少はredemption経由のみ = T5/T9/T10 の帰納ステップ)、`redemption_price_admin_only`(redemption価格はadmin `catastrophicBackstop` 専有)。

## 1. 動機: エクスプロイトの主戦場はもうコードバグではない

- Chainalysis 2025年報告: 盗難額の **43.8% が秘密鍵の漏洩**由来(2024年)。個人ウォレット侵害は2022年の7.3%から2024年には盗難総額の44%へ。
- 2025年は総額$3.4B、うち**Bybit単独で$1.5B**(Safe multisig署名UIの侵害 = ソーシャルエンジニアリング/インフラ攻撃であり、コントラクトのバグではない)。
- つまり「コードは形式検証済みでも、**運営の鍵が抜かれたら終わり**」が現実の支配的リスク。

従来の形式検証(本リポジトリの81定理も含む)は「正しい呼び出し元が正しく振る舞う」世界の性質を証明する。ここで提案するのは逆向きの問い:

> **「役割Xの鍵が完全に攻撃者の手に落ちたとき、ユーザー資産の喪失は最大いくらに収まるか」を定理として証明する。**

証明された被害上限は、保険の引受(underwriting)可能なリスク定量になる。「監査済み」というバイナリな主張より、「オラクル鍵漏洩時の最大損失 ≤ USDCリザーブの x%」という機械検証済みの数値のほうが、保険料算定・プロトコル設計・ユーザー開示のすべてに使える。

## 2. 脅威モデルの形式化

既存の`State`/`Op`/`step`モデル(lean/D2fsSpecs/Apyx.lean)がそのまま土台になる。追加するのは攻撃者の定義だけ:

```
攻撃者 = 侵害された役割の集合 R ⊆ {admin, oracle, pauseController, yieldDistributor, governance}
能力   = caller ∈ R となる任意の操作列(正規ユーザーの操作を任意に交互挟込み可)
測度   = userLoss(σ) := ユーザー資産の正味減少(操作列σの実行前後の差)
```

証明目標の一般形:

```
theorem blast_radius (R : Set Address) (σ : List (Op × Address)) :
    (∀ (op, c) ∈ σ, c ∈ R ∨ isHonest c) →
    userLoss (execSeq s₀ σ) ≤ B R s₀
```

`B R s₀` が役割集合ごとの**被害上限関数**。これは1回のstepの性質ではなく**任意長の操作列に対する帰納法**なので、既存の保存則型定理(`req_overcollateralization_limit`等)を帰納法の1ステップとして再利用する形になる。

## 3. 証明したい定理リスト(DeFi版、Apyxモデルでの実装難度付き)

### Tier 1: 現行モデルで今すぐ証明可能(全ケース分析の流用)

| # | 定理 | 主張 | 難度 |
|---|---|---|---|
| T1 | `pauser_cannot_extract` | pauseController侵害の被害 = 凍結(liveness喪失)のみ。全opの網羅分析で「pauserにできるのはglobalPauseの反転だけで、いかなる残高・供給量フィールドも変化させられない」 | 低(既存パターン) |
| T2 | `yield_distributor_cannot_extract` | yieldDistributor侵害では資産を抜けない: `creditYield`は入金(vestTotal/usdcReserve増)しかできず、いかなるユーザー残高も減らせない | 低 |
| T3 | `admin_cannot_touch_balances` | admin侵害でも既存ユーザーの`apxUSDBal`/`apyUSDBal`を**直接**は動かせない(whitelist/denylist/レート設定のみ)。ただし将来の操作をブロックできる(liveness影響は別掲) | 低〜中 |
| T4 | `no_role_transfers_user_funds` | 非保管性(non-custodial invariant): ユーザー残高が減る遷移は、そのユーザー自身がcallerである操作に限る。**ソーシャルエンジニアリングで運営が全滅してもユーザーの既存残高は動かない**ことの直接証明 | 中(全opの網羅+caller条件の抽出) |

### Tier 2: 台帳フィールドの追加が必要(中規模のモデル拡張)

| # | 定理 | 主張 | 前提となる拡張 |
|---|---|---|---|
| T5 | `no_theft_ledger` | 任意の操作列で、任意のアドレスの「正味引出額 ≤ 正味入金額」。第一原理のno-theft定理であり、T1-T4の統合版 | `State`に累積入金/引出の台帳フィールド(または`eventLog`からの導出関数)を追加し、全opで保存則を証明 |
| T6 | `oracle_blast_radius` | oracle侵害時の最大抽出額の明示: 攻撃者が`redemptionValue`/`apxUSDMarketPrice`を任意値に設定できても、抽出可能額 ≤ f(usdcReserve, 設定可能レンジ)。**逸脱クランプが無い現行モデルでは f = usdcReserve 全額**、という証明自体が発見になる(Yearnリスク評価がApyx実機の`ApxUSDRateOracle.setRate`のタイムロック0秒を最大リスクと指摘済み — モデルがこれを正確に映している) | 台帳(T5)+ oracleが影響する経路の分析 |

### Tier 3: 防御機構そのもののモデル化が必要(大規模拡張、ただし価値最大)

| # | 定理 | 主張 | 前提となる拡張 |
|---|---|---|---|
| T7 | `rate_limit_linear_bound` | 期間あたりの引出上限(rate limit)を導入した場合: `userLoss(t) ≤ cap × ⌈t/epoch⌉`。**「被害は時間に対して高々線形」**という、ユーザーが口頭で述べた性質の正確な形式化。ERC-7265(circuit breaker標準)の設計をモデルに映す | `State`にepochあたり流出量トラッカーと上限、`step`にゲート追加 |
| T8 | `timelock_escape_guarantee` | 特権操作にタイムロックTを導入した場合: 「adminが悪性の変更をqueueしてから発効するまでの間、**任意のユーザーは高々ε損失で退出できる**」(escape hatch定理、Eyal & Sirer提案の形式化)。安全性でなく**敵対的環境下のliveness** | タイムロックqueue(pending操作+発効時刻)のモデル化。現行モデルのadmin操作は全て即時発効なので、この定理は現行モデルでは**偽**— それ自体が設計指摘になる |
| T9 | `compartmentalization` | 役割Rの侵害の影響が部分システムS(R)に閉じる: 例「yieldDistributor侵害はvestプール(未分配利回り)にのみ影響し、元本(vaultApxUSDBal)には波及しない」 | T5の台帳を部分システムごとに分割 |
| T10 | `coalition_bound` | 役割の結託に対する上限表: B({oracle})、B({admin, oracle})、… の**単調な表を証明付きで出す**。「何個の鍵が同時に漏れたら全損か」の定量化(m-of-n multisigの価値の形式的裏付け) | T5-T9の合成 |

## 4. 既存研究とのギャップ(= この方向の新規性)

Web調査(2026-07-07)の結論: **「役割侵害を仮定した被害上限の機械検証済み定理」というジャンルは確立されていない。**

近いものは:
- **Eyal & Sirer の Decentralized Escape Hatch**(出金の24hバッファ+プログラム的不変条件で流出を制限する提案)— アイデアはT7/T8の原型だが、形式証明はない
- **ERC-7265 Circuit Breaker**(資産ごとのrate limitパラメータ)— 実装標準であり、性質の証明はない
- **SoK: Attacks on DAOs (arXiv:2406.15071)** — escape hatch/timelockを緩和策として整理するが、被害上限の定理化はしていない
- **PropertyGPT / Certora系**(docs/01-related-work.md)— 検証対象は「正しい呼び出し元」の世界の不変条件で、役割侵害モデルではない
- **Clockwork Finance (KEVM)** — 経済的安全性の検証だが、鍵漏洩シナリオの上限定量ではない

つまり: 各部品(タイムロック、rate limit、escape hatch)は実務側に存在するが、**「それらが入っていれば被害はこの式で抑えられる」という定理+機械証明のセット**は空白地帯。docs2formalspecのモデル(閉じたOp型+全ケース分析ができる小さなstate machine)はこの証明に最適な粒度を既に持っている。

## 5. ロードマップ(推奨順)

1. **T1, T2**(pauser/yieldDistributor無害性)— 既存の網羅分析パターンの流用で即着手可能。「運営鍵の一部漏洩は資産に触れない」という最初の保険的言明が数日で出る
2. **T4**(非保管性)— ソーシャルエンジニアリング物語に対する最重要の反論定理。「チームが全員フィッシングされてもあなたの残高は動かない」
3. **T5**(台帳+no-theft帰納法)— 以降すべての土台
4. **T6**(oracle被害上限)— Yearnが実プロトコルで指摘済みのリスクをモデルで定量化。「証明できない(上限=リザーブ全額)」という結果が出た場合、それはクランプ/タイムロック追加の設計提言として最も説得力のある形になる
5. **T7, T8**(rate limit / timelockのモデル化と線形上限・退出保証)— 防御機構の価値を定理で示す。ここまで来ると「この機構を入れればこの上限式が成り立つ」というテンプレート集として他プロトコルへ汎用化できる
6. **T10**(結託表)— 最終成果物。保険引受・監査レポートにそのまま載せられる形

## 6. docs2formalspecへの組み込み方(将来)

要件駆動パイプラインの死角(ドキュメントは「攻撃者に何ができないか」を書かない)を埋める第2の性質供給源として、`templates/`にT1-T10のパラメータ化Leanスキーマを置き、`gen_lean`が生成した`State`/`Op`に対して役割フィールド(admin/oracle等)を自動同定してインスタンス化する構想。要件由来の定理(トレーサビリティ付き)とテンプレート由来の定理(脅威モデル付き)を`review.json`で区別して報告する。

## 参考リンク

- Chainalysis 2025 crime report / 2026 update: 盗難統計・鍵漏洩シェア
- Bybit事件(2025-02, $1.5B, Safe署名UI侵害)
- SoK: Attacks on DAOs — https://arxiv.org/abs/2406.15071
- ERC-7265 Circuit Breaker 提案
- Eyal & Sirer, Decentralized Escape Hatch(SoK内で参照)
- Yearn risk-score: Apyx apxUSD 評価(rate oracleのタイムロック0秒を最大リスクと指摘)— T6の実世界対応物
