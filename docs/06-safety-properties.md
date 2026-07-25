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

**まず区別すべき2種類の「非原子性」**。本モデルの `step` が原子的であることが閉ざすのは、

- **(i) 1操作の実行途中への割り込み(再入)** — 扱えない。`step` の不可分性が構造的前提。
- **(ii) 1つのユーザー操作が request と settle の2相に分かれ、その間に時間が進む(非同期決済)** — **扱える**。`Op` に時計を入れれば表現でき、§7 でこの拡張と定理族を扱う。

の (i) だけであって (ii) ではない。両者を同じ「原理的に扱えない」箱に入れるのはスコープ記述として不正確なので、以下では (i) のみを限界として述べる。

第3の柱の最大の落とし穴は**再入(reentrancy)**。本モデルの `step : State → Op → Address → Option State` は**原子的**で、1つの操作は不可分に完了する。外部コントラクト呼び出しの「途中で」別の操作が状態に割り込む、という実行のインターリーブが表現できない。再入攻撃はまさにこのインターリーブを突くので、**このモデルでは再入バグを見つけることも、無いことを証明することもできない**。同様に、フラッシュローンによる複数プロトコル横断の価格操作、実装レベルの入力検証(型付きモデルなので範囲外)、ガス/ストレージ/upgrade安全性も範囲外。

これは Certora/Halmos 等の**バイトコードレベル検証**が担う領域であり、第3の柱の抽象モデル証明はそれらを代替しない。「設計レベルの経済的欠陥(保存則・solvency・丸め・希釈・インフレ攻撃)」を検証する道具であって、「実装レベルの実行順序バグ」は対象外、と監査レポートに明記する必要がある。

## 4b. 進捗と証明中に判明した設計上の発見(2026-07-07)

**S1-S7 すべて証明完了、S8-S9 追加**。`outputs/apyx/Safety.lean`(namespace `Apyx`、公開定理28本、sorry 0、全て `propext`/`Quot.sound` のみ、`Apyx.lean`/`BlastRadius.lean` 無傷)。

| # | 定理 | 状態 |
|---|---|---|
| S1 | `no_free_value_trace` | 完全 |
| S2 | `solvency_preserved` | 完全(WellFormed仮説をトレール各点で再供給する正直形。claimUnlock/handleStressEventはop単位で除外・文書化) |
| S3 | `rounding_favors_protocol` + `withdrawShares_rounds_up` | 完全(3方向) |
| S4 | `no_dilution` | 完全 |
| S5 | `donation_free` + `no_inflation_attack` | 完全(生donation経路の構造的不在) |
| S6 | `caller_net_nonpositive` | 固定参照レート下の単発版(正直にスコープ限定)。**トレース閉包は S9 で部分達成**(下記)。**残る開放問題**: share-op(lock/withdraw/redeem)を含む live-rate 閉包(単一`updateExchangeRate`のレート移動量の限界+トレール合成)は別種の難しい算術問題として明示的に未着手 |
| S7 | `vest_no_early_drain` | 完全(単調性・上限・pull正確性)。線形スケジュール自体は `Apyx.lean` の `req_linear_vest_implementation` で証明済 |
| S8 | `no_same_state_arbitrage_round_trip` / `requestUnlock_backs_claim_by_burn` | 完全(強化モデルの帰結。arbitrage mint/redeem は逆の価格レジームを要し同一 state で両立不可=peg スプレッド round-trip 不能。requestUnlock は焼却分ちょうどで claim を裏付け=無償 claim 不能) |
| S9 | `caller_net_nonpositive_trace` + `valueAt_step_le` | S6 のトレース化を **value-preserving op 断片**で達成(share-op / unlock 決済 / gift mint を除く全 op のトレースで、任意固定レート `R` での保有価値は非増加。`redemptionValue ≤ ray` を各 prefix で再供給、`solvency_preserved` と同じ正直形)。redemption/RFQ/request の抽出経路を任意長トレースでカバー。**share-op + live-rate 閉包は S6 の開放問題として残置** |

**証明作業が炙り出した実設計欠陥2件**(いずれも特権ロールの会計問題であって一般攻撃者exploitではない):

1. **S5訂正**: `creditYield` は `vaultApxUSDBal` を動かさない(当初仮説の誤り)。`withdraw`/`redeem` が `pullVestedYield` 経由で金庫を増やしうるが `vestedAmount` 上限内で、donationではない。結論(生donationインフレ攻撃の構造的不可能性)は不変。

2. **`creditYield_forfeits_pending_vest` → 実コントラクト照合で決着(2026-07-07): モデルの不忠実、コントラクトは正しい**。
   - **モデルでの証明内容**: `Op.creditYield` は `vestStart := now` をリセットするが成熟済み分 `vestedAmount s s.now` を先に確定しない。証明で確定: creditYield直後 `vestedAmount s' s'.now = 0`、事前に未実現vestが正なら `totalAssets s' < totalAssets s`(実現可能価値が瞬間的に下がる)。
   - **実コントラクト照合**(`apyx-labs/evm-contracts` の `src/LinearVestV0.sol`): `depositYield`(=creditYield相当)の168行目が `fullyVestedAmount += newlyVestedAmount();` を**タイムスタンプ・リセットの前に**実行しており、成熟済み分を別アキュムレータ `fullyVestedAmount` に退避している。→ **実コントラクトは取りこぼさない。正しい。** `setVestingPeriod` も同じ正しいパターン。
   - **根本原因**: モデルは実装の2アキュムレータ設計(`vestingAmount` 未成熟プール + `fullyVestedAmount` 成熟済み・未pull、および2タイムスタンプ `lastDepositTimestamp`/`lastTransferTimestamp`)を単一の `vestTotal`/`vestStart` に**畳み込んで単純化**し、その過程で168行目相当の退避ステップを落とした。**プロトコル欠陥ではなくモデル忠実性ギャップ**。
   - **意義**: 形式証明が「ここは確認すべき」という具体的な問いを生み、実コード照合で決着した好例。同時に「モデルレベル証明は実装と乖離しうる」という本ツールの根本的限界の具体化でもある。
   - **修正完了(2026-07-07、4段階)**: 実装に合わせて仕様・モデル・証明を全面修正した。**Stage 1** 仕様(SPEC.md/model.md/requirements.json)に新要件 `credit-preserves-accrued-vest` 追加。**Stage 2** `Apyx.lean` の `State` に `fullyVestedAmount` を追加、`vestedAmount = fullyVestedAmount + newlyVestedAmount`、`creditYield`/`setVestPeriod` を accrue-first に修正、新定理 `req_credit_preserves_accrued_vest`(vested総額の保存)を追加、影響した約10の要件定理を忠実に更新(要件定理 81→82本)。**Stage 3** `BlastRadius.lean` を修復(偽になった `vestTotal` 単調性を `fullyVestedAmount + vestTotal` 保存に restate、「yieldDistributor侵害は donate のみ」の意図を維持)。**Stage 4** `Safety.lean` を修復し、**`creditYield_forfeits_pending_vest`(forfeit定理)を `creditYield_preserves_accrued_vest`(保存定理: `vestedAmount s' s'.now = vestedAmount s s.now ∧ totalAssets s' = totalAssets s`)に置換**。全3モジュール `lake build D2fsSpecs` 緑・sorry 0・公理クリーンを独立検証。**残る単純化**(単一 `vestStart` vs 実装の2タイムスタンプ = pullでvesting終了が延びる)はコア修正の対象外として明示的に文書化(ユーザー判断で「コア修正=2アキュムレータ」を選択)。

**S5証明中の設計仮説の訂正**(memoの当初仮説 vs 実際のモデル):
- `creditYield` は `vaultApxUSDBal` を**動かさない**(`usdcReserve`/`vestTotal`/`vestStart` のみ)。当初「lockとcreditYieldが金庫を増やす」としたが誤り。
- 代わりに `withdraw`/`redeem` が内部の `pullVestedYield` 経由で金庫を増やしうる。ただし増加は `vestedAmount s s.now` で上限され、この量を増やせるのは特権 `creditYield` のみ。donation ではない(`totalAssets` は `pullVestedYield` で保存)。
- 結論は不変: **一般攻撃者による生donationインフレ攻撃は構造的に不可能**(`donation_free`/`no_inflation_attack` で `lockApxUSD` の金庫増加が caller 自身の入金と1:1であることを証明済み)。

**⚠ 潜在的な設計上の懸念(要調査、S7の前段)**: `Op.creditYield` は `vestStart := now` をリセットする際、既存vestストリームの `vestedAmount s s.now`(部分的に成熟済みだが未だ `pullVestedYield` で実現されていない分)を**先に確定しない**。もし旧ストリームが部分成熟済みで未実現なら、その分が黙って失われうる。これは「利回りの取りこぼし」型の実際の設計欠陥候補であり、S7(vest先取り不可)の証明前に専用調査が必要 — **証明作業が実コードの懸念点を炙り出した好例**。

## 4c. レビュー後の追加強化(2026-07-07、独立レビュー由来)

3本の Lean ファイルの独立レビューで炙り出した弱点を、`lake build` 緑・sorry 0・公理 `propext`/`Quot.sound` のみを維持したまま順次修正した:

- **`setVestPeriod_preserves_accrued_vest` 追加**(Safety、公開定理 23→24本): `creditYield_preserves_accrued_vest` の双子。accrue-first の `setVestPeriod` 経路は散文でのみ「取りこぼさない」と主張され定理が無かった弱点を解消(`vestedAmount`/`totalAssets` 保存を証明)。
- **弱い/誤解を招く要件定理の強化**(Apyx、要件定理数は不変=書き換え): `req_yield_rate_dollar_terms`(`∃x,y=x` の空虚→`setYieldRate` が dollar `collateralYieldBase` で上界する実質へ)、`req_linear_vest_implementation`(`⟨rfl,rfl⟩`→前アンカー0・時間単調・プール上界・満期100%・2アキュムレータ和)、`req_deposit_immediate`/`req_mint_immediate`(`apyUSDBal to ≥ apyUSDBal to` の自明→ vault の同期 mint 経路 `Op.lockApxUSD` の厳密な同一step share 交付)、`*_emits_event`(5引数存在→厳密タプル固定)。
- **`single-pending-redemption-per-user` を遷移系に忠実実装**(モデル変更): `Op.requestUnlock` を `requestUnlockStep` 経由にし、既存の標準ポジションを**追加更新(top-up、cooldown リセット)**して2つ目を作らないよう変更。要件「ユーザーあたり pending 1件」が単発の per-user `unlockRequestId` ポインタで遷移系自体に強制される。top-up 分岐は**自己検証的**(記録上の所有者が caller のポジションのみ更新)なので、`Penniless`(`no_free_value_trace`)等の unlockRequests 系不変条件をレジストリ整合性仮説なしで維持。影響したレジストリ定理(`req_redemption_async_process`/`req_redemption_cooldown_period` は caller のトラッキングポジションでの branch-agnostic 形に、`req_unlock_token_nontransferable`/`unlock_position_created_only_by_vault_ops`/`req_unlock_cannot_be_cancelled` は branch-aware 証明に、`no_role_seizes_unlock_position` はレジストリ well-formedness 仮説付き)を全て修復。`req_single_pending_redemption_per_user`/`req_multiple_unlocks_reset_cooldown` を helper テストから**到達可能な step レベル不変条件**へ格上げ。

## 5. ロードマップ(推奨順)

1. **S1 → S2**(no-free-value と solvency の帰納): 既存単発版のトレース化。設計健全性の最初の言明が最速で出る。
2. **S5 インフレ攻撃**: 最も価値の高い設計欠陥チェック。前段でモデルに donation 経路が在るかを調査 — 無ければ「構造的に不可能」を全op網羅で証明、在れば丸め下限で防御が効くかを検証(効かなければ**実際の設計欠陥の発見**)。
3. **S3, S4**(丸め方向・非希釈): ERC4626中核安全性の明示化。
4. **S6**(完全 no-free-money): 価値加重台帳。第3の柱のヘッドライン。
5. **S7**(vest先取り不可)。

## 6. docs2formalspecへの組み込み

第2の柱と同様、Tier A の性質族(保存則・solvency・丸め方向・非希釈・インフレ耐性)のパラメータ化スキーマを **[`templates/invariants/`](../templates/invariants/) に実装済み**(README = 記入ガイド、`Invariants.template.lean` = `‹PLACEHOLDER›` 付き骨格、`outputs/apyx/Safety.lean` = worked reference)。設計方針と業界脆弱性パターンとの対応は [`docs/08-defi-vuln-patterns.md`](08-defi-vuln-patterns.md)。ボトムアップ入力は**ドメイン別**: DeFi は公開被害集計、合意プロトコルは `ethereum-vuln-dataset`。生成定理は要件由来 / 脅威モデル由来 / **設計不変条件由来** / spec-consistency 由来 の4種を `review.json` で区別報告。

## 7. 第4の状態族 — 非同期・多拠点・符号付き価値(S10–S16、枝番含む)

> **ステータス(正直な明示)**: S1–S9 は `outputs/apyx/Safety.lean` で**実プロトコル**に対して証明済み。
> 本節の S10–S16 に**実プロトコルの worked reference は一つも無い**。内訳は下記のとおりで、
> 監査でこれらを引用する際は必ずこの区別を明記すること。
>
> | | 状態 |
> |---|---|
> | **S10 / S10c / S10d / S10e / S11(witness形) / S11b / S11c / S11d / S12 / S15** | ERC-7540 型の非同期償還 vault の最小形 [`templates/invariants/examples/AsyncQueueVault.lean`](../templates/invariants/examples/AsyncQueueVault.lean) で**証明済み**(22定理・`lake build` 緑・sorry 0・公理 `propext`/`Quot.sound` のみ)。ただしこれは**架空のプロトコル**であり、**スキーマが整合していることの証拠**であって実プロトコルについての証拠では一切ない |
> | **S10b / S13 / S14 / S16** | **スキーマのみ**。実証も worked reference も無い |
> | **S11 の肯定形** | **部分的**。「資金が足りた成熟済み先頭は必ず決済される」(S11d)は証明済みだが、**任意位置の請求がいずれ必ず serve される**という完全形(`queue_no_starvation`)は未証明。監査で「飢餓しない」と書けるのは前者までである |
>
> テンプレートは [`templates/invariants/`](../templates/invariants/)(Step 0b と checklist g–k)。

### 7.1 対象 — 償還が非同期な DeFi プロトコル

**この節は Apyx には適用されない**。Apyx は入金も償還も原子的に完結する同期型なので、S1–S9 で
設計安全性は尽きている。S10–S16 は**次に監査する対象が以下のいずれかだったときに追加で証明すべき
定理群**であり、そうでなければ 1本も足す必要はない(判定は Step 0b の5問で機械的に済む —
[`templates/invariants/`](../templates/invariants/))。

- 非同期 vault / RWA ファンド(ERC-7540 型の request → claim)
- LST / LRT の unstaking キュー、出金キュー付き vault、遅延償還ステーブル
- 複数の会計拠点にまたがり移送に遅延がある運用(デルタニュートラル等)
- 負債・建て玉を持ち、純資産が負になりうる設計

損失アーキタイプとの対応は [`docs/08`](08-defi-vuln-patterns.md) §A.6。

### 7.2 なぜ S1–S9 だけでは足りないか

S1–S9 は、明示されてはいないが次の5つのモデル前提の上に成立している:

| # | 前提 | 本リポジトリでの根拠 |
|---|---|---|
| P1 | **トレース中に時間が進まない** | `execTrace` は `step` を畳むだけで、コア `Op` に時計を進める操作が無い(`Apyx.lean` の `State.now` を動かす op は存在しない) |
| P2 | **step は原子的かつ即時決済** | `step : State → Op → Address → Option State` |
| P3 | **価値は非負(`Nat`)** | `valueAt : Nat → State → Address → Nat` |
| P4 | **台帳は `Address → Nat` の集約** | `Σ over holders` が書けないことは §6.2 相当の限界として既知 |
| P5 | **価格ソースは単一・常に新鮮** | `redemptionValue` / `apxUSDMarketPrice` は state の単一フィールド |

次の4条件のいずれかを満たすプロトコルでは、この前提の**外側**に攻撃面の大半が落ちる:

1. 入出金が request → settle の2相で、その間に時間が進む(ERC-7540 型の非同期 vault、
   出金キュー、遅延償還)
2. 資産が複数の会計拠点にまたがり、拠点間の移送に遅延がある
3. 保有価値が符号付きになりうる(負債を差し引いた純資産)
4. 操作が有限容量の共有キューを奪い合う

S1–S9 をこの種のプロトコルにそのまま当てると、**証明は通るが攻撃面をほとんど覆っていない**という
最悪の結果(空虚に近い安全性主張)になりうる。特に P3 は危険で、`Nat` 台帳では債務超過が
そもそも表現できないため、支払能力の定理が**空虚に真**になる。これは本ツールが `review.json` の
`vacuous` 判定で常に警戒している失敗様式の、型レベル版である。

### 7.3 必要なモデル拡張(E1–E4)

| # | 拡張 | 内容 | 開く定理 |
|---|---|---|---|
| **E1** | **時計** | `Op` に `tick`(1決済ラウンドの経過)を追加し、`execTrace` が時間を進められるようにする | S10, S11, S12 |
| **E2** | **二相操作と決済仮説** | `Request`(owner / amount / filedAt / 価格スナップショット)と `settle` op。**決済層が約束どおり処理することは定理ではなく明示された仮説** `SettlementHonored` として置く | S10, S12, S13 |
| **E3** | **符号付き台帳** | `netValue : State → Address → Int`。`Nat` のままでは S15 が空虚に真 | S14, S15 |
| **E4** | **明示キュー** | `State` に `pending : List Request` と容量パラメータ | S11 |

E1 には**既に前例がある** — `BlastRadius.lean` の rate-limit ラッパ(`RLOp.advanceEpoch` /
`execTrace2` / `countEpochs`)と timelock ラッパ(`TLOp.tick` / `execTraceTL` / `countTicks`)は
既に時計付きの遷移系である。コアモデルへ昇格していないだけで、手法とその証明作法は確立済み。

### 7.4 定理リスト

| # | 定理 | 主張 | 効く DeFi アーキタイプ | 形 | 要る拡張 |
|---|---|---|---|---|---|
| **S10** | `settlement_price_no_timing_gain` | request と settle の間に価格が動いても、**決済タイミングの選択**が実行者に利得を与えない(払出は request 時と settle 時のプロトコル有利側で評価) | 非同期 vault / 遅延償還 | 定理(S3 丸めの価格版) | E1, E2 |
| **S10b** | `price_source_choice_no_gain` | 複数の価格ソースを読めるとき、どれを読むかの選択が caller に利得を与えない | 多重オラクル | 定理 or witness | P5 の解消(価格を複数フィールド化) |
| **S10c** | `settlement_has_no_deadline` | 成熟後の決済を強制する仕組みが無く、**決済者のオプションに期限が無い**。S10 の `min` 規則と合わせると遅延コストは請求者が負担 | **gap-witness** | E1, E2 |
| **S10d** | `cancel_refile_ratchets_the_quote` | `cancel` にも時間制約が無く、申請者は**取消・再申請で申請価格を無償で吊り上げられる**。増えた支払いは準備金=後続者の原資から出る | **gap-witness** | E1, E2, E4 |
| **S10e** | `enqueue_then_settle_needs_a_round` | 成熟窓が非ゼロなら**申請と決済が同一ラウンドで成立しない**。フラッシュローンで資本を無限にしても往復できない=構造的免疫 | 定理 | E1, E2 |
| **S11** | `queue_no_starvation` / `queue_head_of_line_blocking_witness` | 正直ユーザーの pending は有限トレースで必ず claim 可能。成り立たないなら**飢餓トレースを witness として証明する**(先頭が決済不能なら後続は支払可能でも凍る) | LST unstaking / 出金キュー | 定理 or **gap-witness** | E1, E4 |
| **S11b** | `queue_capacity_griefing_witness` | 有界コストの攻撃者トレース後、正直ユーザーの enqueue が全て拒否される状態が到達可能 | pending 上限を持つ入出金 | **gap-witness** | E1, E4 |
| **S11c** | `fifo_pays_the_first_filer` | 準備金が不足するとき**按分されず先着順**。同サイズの2件で、支払われるかどうかが申請順だけで決まる=取り付けの誘因 | **gap-witness** | E1, E4 |
| **S11d** | `settle_succeeds_when_head_is_funded` | 資金が足りた成熟済み先頭は必ず決済される。S11 の**肯定側**で、飢餓 witness を「決済は動かない」と誤読させないための対 | 定理 | E1, E4 |
| **S12** | `inflight_conservation` + `tick_settles_exactly` | 未決済分と決済済み分の総和が全 op で保存。時計が進むと未決済分は**ちょうど**決済済みへ移る(`SettlementHonored` 下) | 決済が別ラウンドに落ちる会計 | 定理(仮説付き) | E1, E2 |
| **S13** | `venue_conservation` + `in_transit_lands` | Σ(拠点A + 拠点B + 移送中)が内部移送 op で保存。移送中資産が恒久滞留しない | 多拠点運用 | 定理 / witness | E2 |
| **S14** | `drift_bounded` / `drift_unbounded_witness` | 「意図した状態」と「実現した状態」の乖離に上界がある。無ければ**上界の不在を証明する** | 帳簿先行・執行後追いの設計 | 上界定理 or **gap-witness** | E3 |
| **S15** | `net_value_nonneg` / `insolvency_witness` | 純資産が負になるトレースが存在しない / する | 負債・建て玉を持つ vault | 定理 or **gap-witness** | E3 |
| **S16** | `round_trip_nonprofitable` | 同一状態での往復操作が手数料分だけ必ず損 | スワップ / 償還の往復 | 定理 | — |

**S10c / S11c は「保有者の座席から見る」と出てくる**。S10–S16 はプロトコルの座席から書かれており、
大口保有者の行動を決める2つの性質がそこからは見えない。決済に上限時刻が無いこと(S10c)と、
不足時に按分されないこと(S11c)である。どちらも**どの安全性不変条件にも違反しない**まま成立する。
安全性の証明だけを読んだ保有者は「準備金が薄いときの合理的な行動は先に走ること」を学べない。

**そして欠けている境界は両方向を向いている**。`settle` に期限が無いのは決済者が申請者に対して持つ
オプションだが、`cancel` にも時間制約が無く、これは同じ欠落の鏡像である。払出が
`min(申請価格, 決済価格)` である以上、申請価格は**高いほど申請者に有利**なので、取消・再申請を
繰り返せば入場以降の最高値を無償で握れる(S10d)。しかも増えた支払いは準備金から出る = **後ろに
並んでいる全員の原資**である。プロトコルに不利な側の境界だけを塞ぐ設計は、非対称性を直したのではなく
どちらの側に立つかを選んだだけになる。

**根拠の種類は一様ではない**。S10(パターン J)と S11(パターン K)は ERC-7540 の
Security Considerations と本番設計の防御策という**一次文献**で裏が取れている。S14(パターン L)は
分散システムの **dual-write problem** という既知の失敗様式に構造アンカーを持つが、
**DeFi 固有の公開インシデントは見つかっていない**。詳細と、それでも3つとも A.1 に
昇格させない理由は [`docs/08`](08-defi-vuln-patterns.md) §A.6 を参照。

いずれも**ゼロからではない**: S16 は S8 `no_same_state_arbitrage_round_trip` の一般化、
S14 と S11b は S4b の `redeem_payout_has_no_cap`(上界の不在を witness で確定させる型)の
再利用、S12 は S2 `solvency_preserved` と同じ「仮説をトレール各点で再供給する正直形」である。

### 7.5 副産物: S6 の開放問題

S6(`caller_net_nonpositive`)のトレース閉包が §4b で開放問題として残っているのは、
「レートが動くトレース」を書く手段がモデルに無いことが一因である。E1 の時計を入れると、
レート移動を `tick` の回数で量化した形(`|R' − R| ≤ maxMovePerTick × ticks`)で初めて
**定式化が可能になる**。証明が済むという意味ではないが、書けない問題から書ける問題に変わる。

### 7.6 拡張しても残る限界

E1–E4 を入れても閉じないもの:

- **再入** — §4 (i) のまま。
- **フラッシュローンのクロスプロトコル合成**、実装レベルの入力検証、gas/storage/upgrade。
- **決済層自体の生存性** — `SettlementHonored` は**仮説であって定理ではない**。仮説が破れた場合の
  帰結(S12 の対偶)は書けるが、破れないことは本モデルの外側にある。監査レポートには
  「非同期決済の安全性は決済層の履行を仮定した条件付き保証である」と明記する必要がある。

## 8. アーキタイプ族 — 担保付き債務ポジション(S17–S24、枝番含む)

> **ステータス**: S17 / S17b / S18 / S18b / S19 / S20 / S22 / S23 / S24 は架空の最小モデル
> [`templates/invariants/examples/CollateralizedDebt.lean`](../templates/invariants/examples/CollateralizedDebt.lean)
> で**証明済み**(39定理・`lake build` 緑・sorry 0・公理 `propext`/`Quot.sound` のみ)。**S21 のみスキーマ**(社会化損失プールの保存 —
> 相手方台帳が無いモデルで述べると半分しか描いていない系についての主張になるため)。§7 と同じく、
> **実プロトコルの worked reference は一つも無い**。なお S18b と S24 は **gap-witness**、
> すなわち「安全性が証明できなかった」ではなく「悪状態が到達可能であることを証明した」側である。

### 8.1 対象 — 口座単位の支払能力が本体になる設計

§7 が「償還が非同期か」で分岐したのに対し、こちらは「**支払能力がプール単位か口座単位か**」で分岐する。

S1–S9 の S2(`solvency_preserved`)は `Σ 請求 ≤ Σ 裏付け` という**プール単位**の主張である。
CDP・借貸市場・担保付き債務を扱う設計では、プール合計が健全でも**個々のポジションが水没していれば
不良債権**になるので、口座単位の健全性が安全性の本体になる。次のいずれかを持つなら本節が要る:

- ユーザーごとの担保・負債ポジションと清算閾値がある(CDP ステーブル、借貸市場)
- 清算・償還に**優先順序**を約束している(worst-first、レート順、FIFO)
- 利息 index などの accrual がポジションの健全性を時間で悪化させる
- デプロイ時固定と宣言しているリスクパラメータがある

Apyx は集約台帳でポジション単位の担保比率を持たないため、**本節も Apyx には適用されない**。

### 8.2 定理リスト

| # | 定理 | 主張 | 形 | 状態 |
|---|---|---|---|---|
| **S17** | `all_healthy_preserved` | 負債増加・担保減少の**全 op** の後で、書帳の**どのポジションも**健全。リスク源(価格・accrual)は名指しで除外 | 定理(**全 op 網羅**) | 証明済 |
| **S17b** | `redeem_preserves_health` | 償還は担保を抜くので健全性は自明でない。**債務減少を切り上げる(I4)** かつ **過剰担保** の2条件でのみ保たれる | 定理 | 証明済 |
| **S18** | `liquidate_requires_unhealthy` + `liquidation_seizure_bounded` | 健全なポジションは清算できず、押収額は担保額を超えない | 定理 | 証明済 |
| **S18b** | `liquidation_unprofitable_witness` | 清算が**許可されるが採算が合わない**状態が到達可能。誰も執行しないのでポジションが残り差額が育つ | **gap-witness** | 証明済 |
| **S19** | `sorted_preserved` + `redeem_hits_head_only` | 約束した優先順序が**全 op で保存**され、償還は先頭しか触らない | 定理(**全 op 網羅**) | 証明済 |
| **S20** | `index_monotone` + `accrual_never_lowers_debt` | accrual index は非減少で、健全性を悪化方向にしか動かさない | 定理 | 証明済 |
| **S21** | `loss_pool_conserves` | 社会化損失プールの積和会計が価値を創出しない | 定理 | **スキーマのみ** |
| **S22** | `min_ratio_immutable` | 「不変」と宣言したパラメータに**変更経路が存在しない** | 定理(**全 op 網羅**) | 証明済 |
| **S23** | `liquidation_accounts_shortfall` + `bad_debt_only_from_liquidation` | 清算で回収できなかった債務が**明示的に計上**される。他のどの op も不良債権を生まない | 定理(**全 op 網羅**) | 証明済 |
| **S24** | `oracle_move_enables_full_seizure` | 健全なポジションが**1回の価格更新**で全担保押収の対象になる。S17–S23 は全て成立したまま | **gap-witness** | 証明済 |

**S17 が本節の中心**。Euler 型の欠陥は「全経路で成立するが1経路だけ抜けている」不変条件であり、
`cases op` の全枝が通らないとビルドが落ちる形にすれば**構造的に起こりえない**。除外する op
(価格更新・accrual)を**名指しで宣言する**のが正直形で、これは S2 が `WellFormed` 仮説を
トレール各点で再供給するのと同じ作法である。

**S18b / S23 は「安全性だけでは足りない」ことを示す**。S17–S22 は全部成立したままプロトコルが
損失を出しうる。安全性は「どの操作が禁止か」を述べるだけで、「誰かが実際に実行するか」を述べない。
清算が許可されても回収額が債務を下回れば誰も執行せず、差額は accrual のたびに育つ(S18b)。そして
ポジションを書帳から落とすときに未回収分をどこにも計上しなければ、それは**無言の債務放棄**になる
(S23)。参照実装の初版はまさにそれをやっており、**他の全定理は通ったまま**だった。
これは docs/08 §A.2 が「清算は必ず bad debt を減らす」と挙げている性質そのもので、
Tier 1-C に定理が無かった箇所である。

**S19 は「補助関数の補題」と「系の不変条件」の違いを示す**。初版は `insertPos_sorted`(挿入関数が
順序を保つ)だけを証明して止まっており、`Sorted` は `step` と一度も接続されていなかった — つまり
走行中に順序が崩れても何も検出しない状態だった。S17 を書帳全体で述べたのと同じ理由で、
順序も**全 op で保存されること**を証明する必要がある。

**S17b は「除外しなかった op」の価値を示す**。償還は担保を減らすので、返済や担保追加と違って
健全性が自明に保たれない。切り上げ丸めを切り捨てに変えるか過剰担保を外すと、償還を繰り返すだけで
健全なポジションを清算圏に追い込める。**モデルに相手方の受け取りを入れて初めてこの定理は意味を持つ** —
参照実装の初稿は償還が「担保を渡さず債務だけ消す」形になっており、定理は全部通るのに
現実のどのプロトコルとも対応しない操作についての主張になっていた。

**S22 は Tier を採らなくても持ち出す価値がある**。§4b の `redeem_payout_has_no_cap`(境界の不在を
witness で確定させる)の**双対**で、「不変だと主張している ⇒ 変更経路が無いことを証明する」は
`cases op` 1回でほぼ無料に書ける。デプロイ時のコメントが定理になり、将来こっそり setter が
生えればビルドが落ちる。

### 8.2b 外部プリミティブから見たときの位置づけ

**フラッシュローン — 構造で答えが出る**。問うべきは「残高チェックが効くか」ではなく(借入資本は残高
チェックを無効化する)、「攻撃者が貧しいことに依存している不変条件があるか」である。§7 の非同期
vault では答えは No で、しかも偶然ではない: 成熟窓が非ゼロなら申請と決済は同一ラウンドで成立せず、
攻撃者はラウンド境界を支配できない(S10e)。**`delay` は MEV 対策の飾りではなく、この族が無限資本の
敵に対して述べられる理由そのもの**である。ゼロにすると消える。

**オラクル — 本 Tier の境界そのもの**。S24 は健全なポジションを1回の価格更新で全担保押収の対象に
する。**S17–S23 は全部成立したまま**であり、それは各定理が「入力を与えられた上での」遷移系の主張で
あって、価格は入力だからである。これは docs/08 のパターン A(最大の損失カテゴリ)で、Tier 1-C は
これを扱わない。道具は Tier 3 の**被害上限**であって、オラクルの正しさの証明ではない。
**I16–I22 を引く監査レポートには、保証が価格入力に条件付きであることを明記すること。**

**VRF・乱数 — どちらの参照実装もカバーしておらず、偽装もしない**。両モデルに乱数入力は無く、
したがって乱数について述べた定理は一本も無い。名指ししておく理由は、これが上記の発見からの自然な
次の一歩だからである: S11c(先着総取り)の標準的な修正は**順序の乱数化**であり、順序が乱数になった
瞬間にプロトコルは新しい不変条件族を抱え込む — **抽選から利益を得る当事者が、結果を予測・干渉・
引き直しできないこと**。インスタンス化するには乱数を明示的な `Op` 入力にし、コミット点を設け、
コミットから開示までの間のどの操作も勝者を変えないこと、および外れた caller が引き直しを起こせない
ことを証明する必要がある。**キューの定理群を乱数キューに適用してはならない。**

### 8.3 §7 との関係

§7(非同期)と §8(口座単位)は**独立した軸**である。同期型の CDP は §8 だけ、非同期の pooled vault は
§7 だけ、両方持つ設計は両方要る。Step 0b(§7)と Step 0c(§8)の質問に別々に答えること —
[`templates/invariants/`](../templates/invariants/)。

## 参考リンク

- crytic/properties (Trail of Bits) — ERC4626の37安全性性質: https://github.com/crytic/properties/blob/main/PROPERTIES.md
- ERC-7540 Asynchronous ERC-4626 Tokenized Vaults(request→claim の2相モデル): https://eips.ethereum.org/EIPS/eip-7540
- a16z erc4626-tests / ERC4626 inflation attack (OZ, Zellic Perennial finding)
- 2024 DeFi exploit taxonomy: Three Sigma, Hacken Top-10 2025, Halborn Top-100 DeFi Hacks 2025
- AMM-in-Lean4 (arXiv:2402.06064), Clockwork Finance(経済的安全性の形式化) — docs/01-related-work.md
- ethereum-vuln-dataset(`~/workspace/ethereum-vuln-dataset`)— 合意プロトコル安全性メモ用のボトムアップ入力(DeFi用ではない)
