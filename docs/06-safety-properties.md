# プロトコル設計自体の安全性(in-scope safety)の形式証明 — DeFi版 設計メモ

(調査日 2026-07-07。docs2formalspec 第3の柱。第1=要件適合[81定理, Apyx.lean]、第2=鍵漏洩時の被害上限[56定理, BlastRadius.lean]、本メモ=**正規の攻撃者(全ロール正直)でも設計に欠陥がないか**)

## 0. スコープ: 3つの柱の違い

| 柱 | 敵対者 | 問い | 成果物 |
|---|---|---|---|
| 要件適合 | なし | ドキュメント通りに動くか | `Apyx.lean`(81定理) |
| 被害上限 | 特権鍵が漏洩 | 鍵が盗まれたら最大いくら失うか | `BlastRadius.lean`(56定理) |
| **本メモ: in-scope安全性** | **正規の攻撃者(署名・入金・操作を正規に行うが悪意ある)** | **設計自体に、正規操作の組合せで資産を不当に奪える穴があるか** | `outputs/apyx/Safety.lean`(予定) |

第3の柱は「盗む」タイプではなく「**設計の穴を突く**」タイプ。全ロールが正直でも、攻撃者が正規の`deposit`/`lock`/`redeem`等を巧妙な順序・金額・タイミングで組み合わせて、他ユーザーの価値を吸い上げたり、無から価値を作れてしまう設計欠陥がないかを問う。DeFiの大型被害の多く(2024年のロジック誤り・価格操作・丸め)はこの種の設計欠陥。

## 1. 生成方式: トップダウン + ボトムアップ混合

### 1a. トップダウン: 正典的DeFi安全性invariant族

産業標準の性質集(Trail of Bits [`crytic/properties`](https://github.com/crytic/properties/blob/main/PROPERTIES.md) の37 ERC4626性質、a16z erc4626-tests、OpenZeppelin ERC4626)+学術のDeFi形式化(AMM-in-Lean4 論文、Clockwork Finance)から抽出した、プロトコル横断で繰り返し現れる安全性の「型」:

- **保存則(conservation)**: 価値は無から生まれない。全操作列で「発行された請求権の総和 ≤ 裏付け資産の総和」。
- **支払能力(solvency)**: `Σ 償還可能額 ≤ Σ 担保価値`。要件 `req_overcollateralization_limit` が単発版で存在。
- **no-free-money**: 任意のcallerが任意の操作列で、正味利得 ≤ 0(入れた以上は引き出せない)。
- **丸め方向(rounding favors protocol)**: 発行share/引出assetの丸めは常にプロトコル有利、ユーザーに一切クレジットしない(ERC4626の中核安全性)。
- **share価格単調性・非希釈**: 新規lock/mintが既存holderの per-share 請求権を下げない(`exchangeRate` 非減少)。
- **インフレ攻撃耐性(first-depositor / donation)**: 初回入金者が1weiをmintしてから直接donateで`totalAssets`を膨らませ、後続入金者のshareを丸め損で奪う攻撃が成立しないこと。
- **アクセス制御健全性**: 特権操作は認可されたcallerのみ(第1・第2の柱で相当分カバー済み)。
- **原子性・再入不可**: 外部呼び出しの途中に状態が再入されない(下記 §4 参照 — 本モデルでは原理的に扱えない)。

### 1b. ボトムアップ: 実被害の根本原因タクソノミー → invariant逆写像

「脆弱性 = ある性質違反の実例(witness)」なので、実被害を根本原因でクラスタリングし、各クラスが**どの invariant の違反か**を逆算する。2024年DeFi被害の分布(Three Sigma / Hacken / Halborn 集計):

| 実被害クラス(2024-25) | 規模の目安 | 違反している invariant | 本モデルで検証可能か |
|---|---|---|---|
| ロジック誤り・入力検証不備 | 最多(20件) | 操作固有の事後条件(ケースごと) | △ 一部(型付き入力で入力検証は範囲外、ロジックは可) |
| 価格/オラクル操作(flash loan) | $52M+ / 37件, flash loan $380M | 価格ソースの健全性・solvency | ○ solvency側で。価格操作自体は第2の柱で `redeem_payout_has_no_cap` として顕在化済み |
| アクセス制御 | 17件 | 認可健全性 | ○ 第1・第2の柱で相当分 |
| **再入(reentrancy)** | $47M / 12件 | 原子性 | **✗ 本モデルでは原理的に不可**(§4) |
| 丸め・精度 | 恒常的 | 丸め方向 | ○ ERC4626 rounding(一部 `req_erc4626_compliance`) |
| **インフレ/donation攻撃** | ERC4626金庫の定番 | share価格操作耐性 | ○ **最重要の設計欠陥チェック候補** |

**注意**: 手持ちの `~/workspace/ethereum-vuln-dataset` は Ethereum **クライアント**(実行層・合意層)の脆弱性コーパスであり、DeFiコントラクトの被害集ではない。したがって本DeFiメモのボトムアップ入力には**不適**(上表は公開DeFi被害集計から手動抽出)。当該データセットは将来「**合意プロトコルの安全性メモ**」(agreement / accountable-safety / liveness をトップダウン、クライアントバグをボトムアップ)のボトムアップ入力として最適。

## 2. 証明したい定理リスト(Apyxモデル、既存カバレッジ付き)

### Tier A: 現行モデルで証明可能・設計欠陥検出価値が高い

| # | 定理 | 主張 | 既存カバレッジ / 追加作業 |
|---|---|---|---|
| S1 | `no_free_value_trace` | 任意の操作列で、任意アドレスの「受領apxUSD総和 ≤ 支払総和 + 初期残高」。無からの価値創出が不可能 | 単発版 `apxUSD_credit_is_backed`(BlastRadius.lean)済 → トレース総和へ帰納で拡張 |
| S2 | `solvency_preserved` | 全操作列で `totalSupply_apxUSD ≤ totalCollateralValue`(発行総額が担保を超えない)が保存 | 単発版 `req_overcollateralization_limit` 済 → 全op保存則として帰納 |
| S3 | `rounding_favors_protocol` | `lockShares`/`redeemAssets`/`withdrawShares` の丸めが常にプロトコル有利: 往復変換がユーザーに価値をクレジットしない(`convertToAssets (convertToShares a) ≤ a`) | `req_erc4626_compliance` に一部 → 全変換方向で明示 |
| S4 | `no_dilution` | 新規 `lockApxUSD`(share mint)が既存holderの per-share 償還価値を下げない | `req_exchange_rate_non_decreasing` 済 → 「他者のmintで自分の`redeemAssets`が減らない」形へ精緻化 |
| S5 | `no_inflation_attack` | **最重要**: 初回入金者が小額mint→donateで`totalAssets`を膨らませ、後続入金者のshareを丸めで0にする攻撃列が存在しない。**調査で確定(2026-07-07)**: `Op`型の全26操作+`vaultApxUSDBal`全書き込み経路を手動確認した結果、mintApyUSDを迂回して金庫にapxUSDを注入する「生transfer」原始操作は**存在しない**。`vaultApxUSDBal`増加は全て(a)share mint(lock)と対、(b)vest pool(特権`creditYield`のみ)。→ **一般攻撃者によるdonationインフレ攻撃は構造的に不可能**を肯定的に証明する(「金庫資産の非特権増加は必ずshare mintを伴う」)。唯一の疑似donationは特権`creditYield`で、これは第2の柱(脅威モデル)の管轄 | 新規。donation経路の不在は確認済み、あとは構造的免疫を全op網羅で証明 |

### Tier B: 中規模のモデル作業が必要

| # | 定理 | 主張 | 前提 |
|---|---|---|---|
| S6 | `caller_net_nonpositive` | callerの正味価値収支(全価値フィールドをUSDC建てで合算)がトレール全体で ≤ 初期値。S1のUSDC込み一般化=完全な no-free-money | 複数価値フィールドをredemptionValue建てで合算する台帳(`netHoldings` の価値加重版)。Nat減算の扱いに注意 |
| S7 | `vest_no_early_drain` | vestプールの未確定利回りを、確定前に引き出せない(`vestedAmount` の時間単調性を悪用した先取りが不可) | `vestedAmount`/`pullVestedYield` の相互作用の帰納 |

### Tier C: 本モデルでは原理的に検証不能(§4で詳述、正直に除外)

- 再入(reentrancy)、フラッシュローンのクロスプロトコル合成、実装レベルの入力検証、ガス・ストレージレイアウト。

## 3. 既に証明済みで再利用できるもの

`Apyx.lean`: `req_overcollateralization_limit`(→S2)、`req_exchange_rate_non_decreasing`(→S4)、`req_erc4626_compliance`(→S3)、`req_buffer_non_decreasing`/`req_buffer_preservation`、`req_apyusd_value_increase`。`BlastRadius.lean`: `apxUSD_credit_is_backed`(→S1)、`reserve_outflow_only_via_redemption`、`no_theft_ledger`。第3の柱は多くがこれらの**トレースレベル一般化**であり、ゼロからではない。

## 4. 本モデルでは原理的に扱えない安全性(正直な限界)

第3の柱の最大の落とし穴は**再入(reentrancy)**。本モデルの `step : State → Op → Address → Option State` は**原子的**で、1つの操作は不可分に完了する。外部コントラクト呼び出しの「途中で」別の操作が状態に割り込む、という実行のインターリーブが表現できない。再入攻撃はまさにこのインターリーブを突くので、**このモデルでは再入バグを見つけることも、無いことを証明することもできない**。同様に、フラッシュローンによる複数プロトコル横断の価格操作、実装レベルの入力検証(型付きモデルなので範囲外)、ガス/ストレージ/upgrade安全性も範囲外。

これは Certora/Halmos 等の**バイトコードレベル検証**が担う領域であり、第3の柱の抽象モデル証明はそれらを代替しない。「設計レベルの経済的欠陥(保存則・solvency・丸め・希釈・インフレ攻撃)」を検証する道具であって、「実装レベルの実行順序バグ」は対象外、と監査レポートに明記する必要がある。

## 4b. 進捗と証明中に判明した設計上の発見(2026-07-07)

**S1-S7 すべて証明完了**。`outputs/apyx/Safety.lean`(namespace `Apyx`、公開定理23本、sorry 0、全て `propext`/`Quot.sound` のみ、`Apyx.lean`/`BlastRadius.lean` 無傷)。

| # | 定理 | 状態 |
|---|---|---|
| S1 | `no_free_value_trace` | 完全 |
| S2 | `solvency_preserved` | 完全(WellFormed仮説をトレール各点で再供給する正直形。claimUnlock/handleStressEventはop単位で除外・文書化) |
| S3 | `rounding_favors_protocol` + `withdrawShares_rounds_up` | 完全(3方向) |
| S4 | `no_dilution` | 完全 |
| S5 | `donation_free` + `no_inflation_attack` | 完全(生donation経路の構造的不在) |
| S6 | `caller_net_nonpositive` | 固定参照レート下の単発版(正直にスコープ限定)。**残る開放問題**: live-rate/トレースレベルの閉包(単一`updateExchangeRate`のレート移動量の限界+トレール合成)は別種の難しい算術問題として明示的に未着手 |
| S7 | `vest_no_early_drain` | 完全(単調性・上限・pull正確性) |

**証明作業が炙り出した実設計欠陥2件**(いずれも特権ロールの会計問題であって一般攻撃者exploitではない):

1. **S5訂正**: `creditYield` は `vaultApxUSDBal` を動かさない(当初仮説の誤り)。`withdraw`/`redeem` が `pullVestedYield` 経由で金庫を増やしうるが `vestedAmount` 上限内で、donationではない。結論(生donationインフレ攻撃の構造的不可能性)は不変。

2. **`creditYield_forfeits_pending_vest` → 実コントラクト照合で決着(2026-07-07): モデルの不忠実、コントラクトは正しい**。
   - **モデルでの証明内容**: `Op.creditYield` は `vestStart := now` をリセットするが成熟済み分 `vestedAmount s s.now` を先に確定しない。証明で確定: creditYield直後 `vestedAmount s' s'.now = 0`、事前に未実現vestが正なら `totalAssets s' < totalAssets s`(実現可能価値が瞬間的に下がる)。
   - **実コントラクト照合**(`apyx-labs/evm-contracts` の `src/LinearVestV0.sol`): `depositYield`(=creditYield相当)の168行目が `fullyVestedAmount += newlyVestedAmount();` を**タイムスタンプ・リセットの前に**実行しており、成熟済み分を別アキュムレータ `fullyVestedAmount` に退避している。→ **実コントラクトは取りこぼさない。正しい。** `setVestingPeriod` も同じ正しいパターン。
   - **根本原因**: モデルは実装の2アキュムレータ設計(`vestingAmount` 未成熟プール + `fullyVestedAmount` 成熟済み・未pull、および2タイムスタンプ `lastDepositTimestamp`/`lastTransferTimestamp`)を単一の `vestTotal`/`vestStart` に**畳み込んで単純化**し、その過程で168行目相当の退避ステップを落とした。**プロトコル欠陥ではなくモデル忠実性ギャップ**。
   - **意義**: 形式証明が「ここは確認すべき」という具体的な問いを生み、実コード照合で決着した好例。同時に「モデルレベル証明は実装と乖離しうる」という本ツールの根本的限界の具体化でもある。**モデル修正案**: `State` に `fullyVestedAmount` フィールドを追加し `creditYield`/`setVestPeriod` に退避ステップを入れれば忠実になり、forfeit定理は保存定理に置き換わる(`setVestPeriod` の単純化も同様に要修正)。

**S5証明中の設計仮説の訂正**(memoの当初仮説 vs 実際のモデル):
- `creditYield` は `vaultApxUSDBal` を**動かさない**(`usdcReserve`/`vestTotal`/`vestStart` のみ)。当初「lockとcreditYieldが金庫を増やす」としたが誤り。
- 代わりに `withdraw`/`redeem` が内部の `pullVestedYield` 経由で金庫を増やしうる。ただし増加は `vestedAmount s s.now` で上限され、この量を増やせるのは特権 `creditYield` のみ。donation ではない(`totalAssets` は `pullVestedYield` で保存)。
- 結論は不変: **一般攻撃者による生donationインフレ攻撃は構造的に不可能**(`donation_free`/`no_inflation_attack` で `lockApxUSD` の金庫増加が caller 自身の入金と1:1であることを証明済み)。

**⚠ 潜在的な設計上の懸念(要調査、S7の前段)**: `Op.creditYield` は `vestStart := now` をリセットする際、既存vestストリームの `vestedAmount s s.now`(部分的に成熟済みだが未だ `pullVestedYield` で実現されていない分)を**先に確定しない**。もし旧ストリームが部分成熟済みで未実現なら、その分が黙って失われうる。これは「利回りの取りこぼし」型の実際の設計欠陥候補であり、S7(vest先取り不可)の証明前に専用調査が必要 — **証明作業が実コードの懸念点を炙り出した好例**。

## 5. ロードマップ(推奨順)

1. **S1 → S2**(no-free-value と solvency の帰納): 既存単発版のトレース化。設計健全性の最初の言明が最速で出る。
2. **S5 インフレ攻撃**: 最も価値の高い設計欠陥チェック。前段でモデルに donation 経路が在るかを調査 — 無ければ「構造的に不可能」を全op網羅で証明、在れば丸め下限で防御が効くかを検証(効かなければ**実際の設計欠陥の発見**)。
3. **S3, S4**(丸め方向・非希釈): ERC4626中核安全性の明示化。
4. **S6**(完全 no-free-money): 価値加重台帳。第3の柱のヘッドライン。
5. **S7**(vest先取り不可)。

## 6. docs2formalspecへの組み込み

第2の柱と同様、`templates/safety/` に Tier A の性質族(保存則・solvency・丸め方向・非希釈・インフレ耐性)のパラメータ化スキーマを置く(将来)。ボトムアップ入力は**ドメイン別**: DeFi は公開被害集計、合意プロトコルは `ethereum-vuln-dataset`。生成定理は要件由来 / 脅威モデル由来 / **設計不変条件由来** の3種を `review.json` で区別報告。

## 参考リンク

- crytic/properties (Trail of Bits) — ERC4626の37安全性性質: https://github.com/crytic/properties/blob/main/PROPERTIES.md
- a16z erc4626-tests / ERC4626 inflation attack (OZ, Zellic Perennial finding)
- 2024 DeFi exploit taxonomy: Three Sigma, Hacken Top-10 2025, Halborn Top-100 DeFi Hacks 2025
- AMM-in-Lean4 (arXiv:2402.06064), Clockwork Finance(経済的安全性の形式化) — docs/01-related-work.md
- ethereum-vuln-dataset(`~/workspace/ethereum-vuln-dataset`)— 合意プロトコル安全性メモ用のボトムアップ入力(DeFi用ではない)
