# docs2formalspec 実装方針 (v0 draft, 2026-07-06)

## 目的
ドキュメントURL / 相対ファイルパスを入力に、
1. RFC 2119 準拠の完備されたスペック文書 (SPEC.md)
2. その Lean 4 形式検証コード(state machine モデル + 要件ごとの theorem)
を出力するツール。最終的に SPECA レポジトリから LLM が呼び出せるハーネスプラグインになる。

## LLM 基盤
- **Ollama Cloud** (`https://ollama.com/v1`, OpenAI互換)。APIキーは `~/.hermes/.env` の `OLLAMA_API_KEY`(HermesAgent と同一基盤)。
- 役割別モデル(環境変数で差し替え可: `D2FS_EXTRACT_MODEL` など):
  - 要件抽出 / スペック執筆: `gpt-oss:120b`(ethereum-vuln-dataset の評価でバランス良)
  - Lean 生成 / 修復: `qwen3-coder:480b`(コード特化・precision寄り)
- 過去実績 (ethereum-vuln-dataset/docs/model_evaluation.md): gemma4:31b が分類系で最高F1、qwen3-coder:480b は precision 0.90。reasoning系 (glm-5, deepseek) は1コール20-45sで遅くスケールしない。

## パイプライン (src/d2fs/) と一気通貫ワークフロー

**現行の自動パイプライン(柱1のみ)**:
```
ingest (URL→trafilatura→markdown | file→text)
  → extract (doc毎にRFC2119要件をJSON抽出 → 複数doc時はmerge/dedup/矛盾検出)
  → render_spec (RFC2119スペック文書をmarkdownで執筆)
  → model summary (state-transition モデル要約)
  → gen_lean (structure State + 操作関数 Option State + theorem req_*)
  → check_and_repair (lake build → エラーをLLMに渡して修復、最大6ラウンド)
```

**一気通貫ワークフロー(4本柱 + 実装照合 + 相互改善)= [`docs/09-end-to-end-workflow.md`](09-end-to-end-workflow.md)**。
Apyx で確立した全工程を新プロトコルに端から端まで適用する runbook。上の自動パイプラインは**柱1**に相当し、
以降が追加された:
```
Ingest(docs + ★Solidity 取得) → Extract/Specify → Model → 柱1(req_*)
  → ★Source-tracing gate(corpus→Solidity で原典照合。抽出欠陥 D6 と原典欠陥を峻別)
  → 柱2 blast-radius(templates/blast-radius/)     … 鍵漏洩・結託の被害上限
  → 柱3 design-invariants(templates/invariants/)  … コア4(I1-I5)全経路証明 + I7 + gap-witness
  → 柱4 spec-consistency(docs/07)                 … 充足性/realizability/vacuity/被覆
  → Report(review.json 4由来分類 + README §6.4 実装層 hand-off)
  ↖──── 相互改善ループ: 実装(最終真実)に照らし spec ↔ model ↔ Lean を co-improve ────↙
```
**方針**: 生成物は一発では正しくない。**実装(Solidity)を ground truth**、corpus はその非形式記述とみなし、
矛盾/曖昧/vacuity 候補は必ず原典に遡って三分((a)原典欠陥 / (b)抽出欠陥 D6 / (c)corpus 曖昧→実装で確定)。
各フェーズ後に「`lake build` 緑・`sorry` 0・公理クリーン・4ドキュメント(requirements/SPEC/model/README)整合」を
不変条件として維持する。再利用資産は **[`templates/`](../templates/)**(blast-radius / invariants)と本 runbook。
関連: 柱2=[docs/05](05-blast-radius.md)、柱3=[docs/06](06-safety-properties.md)+[docs/08](08-defi-vuln-patterns.md)、
柱4=[docs/07](07-spec-defects.md)。

## Lean 側の設計判断
- **mathlib 非依存**(lean/ は素の lake プロジェクト、Lean 4.31.0)。理由: コンパイルチェックループを数百msで回すため。DeFiの会計は Nat/Int で足りる。
- 失敗する操作は `Option State`(`none` = revert)でモデル化。
- 証明しきれない定理は `sorry` 許容(「形式化された要件」としての価値は残る)。sorry数を品質メトリクスとして出力 (leancheck.json)。

## 品質メトリクス (outputs/<name>/leancheck.json)
- lake build 成功 / 修復ラウンド数 / theorem数 / sorry数
- 今後: 要件カバレッジ(formalizable要件のうちtheorem化された率)、vacuity check(`True`定理の検出)

## 出力ディレクトリ規約
`run --name <n>` は `outputs/<n>/` を毎回上書きする(コード側に自動アーカイブなし)。
複数ラン/プロジェクトの結果を残す場合は、上書き前に `outputs/<n>-run<N>-archive/` の
ような**兄弟フォルダを作らず**、`outputs/<n>/archive/run<N>/` に退避すること。
生ログも `outputs/<n>/logs/` に集約(`.gitignore` は `outputs/**/*.log`)。
プロジェクトが変わっても(apyx 以外でも)この一箇所集約を踏襲する。

## ステータス (2026-07-06 終了時点)
- [x] 類似研究サーベイ → docs/01-related-work.md
- [x] フルパイプライン実装(評価ケーススタディはapyx、詳細 docs/03-eval-log.md)
  - per-declaration修復エンジン + ブロック単体検証(カスケード誤爆根絶)
  - vacuityゲート / バッチ即時検証 / カバレッジ照合 / cheap-tactic自動証明
  - Clover式ラウンドトリップreview + 審判フィードバック再生成
  - モデル再サンプリング + modelgen専用ロール(deepseek-v4-pro)
- [x] SPECAプラグイン → skill/SKILL.md + docs/04-speca-plugin.md
- [x] 証明ディスチャージ(cheap tactics 実装済; Goedel-Prover-V2 はOllama Cloud未提供)

## 到達点(2026-07-08 更新 — 4本柱 + 実装照合の相互改善後)
- **apyx: 170 機械証明定理、`sorry` 0、公理は `propext`/`Quot.sound`(一部 `Classical.choice`)のみ**。
  - 柱1 要件適合 82(`Apyx.lean`)/ 柱2 blast-radius 56(`BlastRadius.lean`)/ 柱3 design-safety 30(`Safety.lean`)/ 柱4 spec-consistency + gap-witness 2(`SpecDefects.lean`)。
  - Solidity(`apyx-labs/evm-contracts`)照合で **catastrophic の per-unit 次元修正**・**mint スプレッドはオフチェーン**・**交換レートは apxUSD 建てで stress 分離**を確定。
  - **抽出欠陥1件を検出・修正**(buffer-non-decreasing の過剰一般化)、**設計の弱点を機械証明**(admin+RFQ 結託全損 / 償還価格にフロア・上限無し / timelock 無し)。
- **sorry 方針の更新**: LLM 一発生成では `sorry` 許容だが、**相互改善ループを回した最終成果物は `sorry` 0 を目標**とする(Apyx で達成)。「形式化された要件」としての価値は残しつつ、機械証明を基準線に。

## 残TODO(2026-07-29 更新)

A–D は Apyx の保証レベルを上げる作業、E は外部提案の取り込み、F はパイプライン自動化の継続。A が他の前提になる。

### A. Apyx — 時計(`Op.tick`)の導入【最優先】

現行モデルは `step`(`outputs/apyx/Apyx.lean:535–787`)の中で `now` を一度も更新しない。`State.now` は読まれるだけで、どのトレースでも時間が進まない。結果として **要件適合82本のうち32本が時計・期間の項を含むのに、時間が動く実行の上では1本も述べられていない**(82本すべて single-step、statement に `execTrace` を含むものは 0)。

- [x] `Op.tick dt` を追加済(`now` を `dt` 進め、値フィールドには触れない。時間を待つのは特権行為ではないので permissionless)。**既存170定理は1本も書き換えずに通った** — 必要だったのは `tick` 枝にガードが無いことによる `split` 失敗の吸収18箇所(`(try split at h_step)`、`Apyx.lean` 8 / `BlastRadius.lean` 8 / `Safety.lean` 2)のみ。`sorry` 0、公理は `propext`/`Quot.sound`。
- [x] statement が `now` に触れる全op網羅の6本(`rounding_favors_protocol` / `no_role_seizes_unlock_position` / `apxUSD_credit_is_backed` / `unlock_position_created_only_by_vault_ops` / `req_singleton_unlock_token_instance` / `req_unlock_cannot_be_cancelled`)は、いずれも無修正で通った。
- [ ] **時計を1本に統一する**。`BlastRadius.lean` の `RLOp.advanceEpoch` / `TLOp.tick` は独立した時計なので、`epoch = now / epochLength` に導出して `advanceEpoch` を op から落とす。二重時計のままだと「100 epoch 経過したが `now` は不動」というトレースが書けてしまい、`rate_limit_linear_bound` の `cap × epochs` を経過時間(=1日あたりの被害)に翻訳できない。
  - 段階移行する場合は、両フィールドを残したまま `epoch * epochLength ≤ now < (epoch+1) * epochLength` を1本証明して drift を止め、リファクタは後追いにする。
- [ ] `solvency_preserved` の `h_excl` から `claimUnlock` / `flexibleClaimUnlock` を外す。現状は `cooldownEnd = now + 20日` かつ `now` 不動のため request と claim が同一トレース内で両立せず、除外がほぼ無コストになっている。`tick` 後は同じ除外が主要な償還フローを外すことになる。`requestUnlock` 側は `requestUnlock_backs_claim_by_burn`(S8)が押さえているので、書き足すのは claim 側。**ここが本作業の実質的な工数。**
- [x] 測定完了 — 既存のトレース級定理21本(`Safety.lean` 4 / `BlastRadius.lean` 17)は**21本すべて無修正で通る**。`tick` が値フィールドを動かさないので、保存則・solvency・blast-radius はいずれも時間経過に対して不変だった。→ D で `outputs/apyx/README.md` に記載する。
- [x] 時計が入って初めて述べられるようになったことの実例を1本追加 — `redemption_cycle_closes_after_cooldown`(request → `tick cooldownPeriod` → claim が同一トレースで成立)。`req_redemption_async_process` は「即時 claim が必ず落ちる」という否定側しか述べておらず、肯定側は時計が無い間は未証明ではなく**述べられなかった**。

### B. Apyx — `updateRedemptionValue` の実装

`Op.updateRedemptionValue`(`Apyx.lean:742`)は oracle-gated だが本体が `some s` の placeholder。モデル上 `redemptionValue` を書き換える op は `catastrophicBackstop`(`emergencyFlag` 必須)だけになっており、**正直な運用の中でレートが動く状況が表現できない**。A の時計とセットで初めて意味を持つ。

- [x] `updateRedemptionValue newValue` を実装済。oracle ロール + `newValue ≠ 0` のみをガードとし、デプロイ側の2つの setter(`ApxUSDRateOracle.setRate` / `RedemptionPoolV0.setExchangeRate`)に合わせた。上限・下限・1回あたりの変動幅・頻度の制約はどれも実装に無いので、モデルにも入れない。
- [ ] 実装後に初めて問えるようになるもの:
  1. 承認済み RFQ カウンターパーティが**単独で**、レート下落の瞬間を狙って `executeRFQRedemption` を実行して抜けられるか。既存 finding `admin_rfq_coalition_drains` は admin + counterparty の2鍵前提なので、成立すれば必要な鍵が1本少ない。
  2. `executeRFQRedemption` を強制する仕組みが無いこと(決済期限の不在)。
  3. `rfqRequests` / `unlockRequests` を未決済債務として保存する不変条件。
- [x] stub 前提だった3定理を正確な形に書き直した。`step_updateRedemptionValue_exact`(「何も変えない」→「oracle が任意の非ゼロ値を publish する」)、`oracle_frame` / `oracle_trace_blast_radius`(フレームの除外フィールドに `redemptionValue` を追加)、`oracle_alone_preserves_balances`(`redemptionValue` 不変の結論を削除。残高・供給・準備金の保全は成立したまま)。
- [x] `redemption_price_admin_only` を `redemption_price_writers` に一般化(全op網羅)。`redemptionValue` を書けるのは **`catastrophicBackstop`(admin・緊急フラグ必須・値は公正 pro-rata に固定・reserve と buffer を同時に0にする「騒がしい」書き込み)か `updateRedemptionValue`(oracle・任意の非ゼロ値・副作用なしの「静かな」書き込み)の2つ**。旧称の定理は「oracle の setter を除けば」という仮説付きの系として残した。
- [x] 新しく述べられるようになったことを2本追加 — `oracle_alone_moves_redemption_price`(緊急フラグ無しで oracle 単独が1ステップで任意の非ゼロ価格を publish できる)、`rfq_payout_is_set_by_execution_timing`(同一の request に対し、即時実行なら 100 USDC、正直な oracle 更新1回のあとに実行すれば 50 USDC。どちらを選ぶかはカウンターパーティ側にあり、ユーザーに発言権が無い)。
- [ ] 時計は S6(`caller_net_nonpositive`)のトレース閉包にも効く。`exchangeRate` が時間で動くので、レート移動を tick 数で量化した形が初めて**定式化できる**ようになる(証明が済むという意味ではない)。

### C. 実装照合(source-tracing)の修正

`apyx-labs/evm-contracts` を読み直したところ、`model.md` の対応付けに誤りがある。

- [x] `model.md` L29 / L73 を修正済。`redemptionValue` の対応先を `RedemptionPoolV0.exchangeRate` に変更。`ApxUSDRateOracle` は Curve Stableswap-NG 向けで `src/` 配下に消費者がいないことも明記。
- [x] スケールの記述を修正済。実装は両方 **1e18**、モデルは `ray = 1e27`。共有しているのは次元(per-unit、集計値ではない)だけである旨に書き換えた。
- [x] 2本の価格については**モデルを割らない**と判断。`ApxUSDRateOracle.rate` を読む主体はモデル化した系の中に存在しない(Curve プールが `staticcall rate()` で読む)ので、フィールドを足しても定理が1本も増えない。未モデル化なのは2本の**乖離**のほうで、そちらはプール境界の外側。`model.md` §5 と `README.md` §12 の #17 に記載。
- [x] `README.md` の「total-loss path は2鍵」に carve-out を2つ付記済。(1) カウンターパーティは admin 鍵ではなく時計だけあれば足りる(`rfq_payout_is_set_by_execution_timing`)、(2) `RedemptionPoolV0.withdraw` / `withdrawTokens` は `ADMIN_ROLE` で、償還を経ずに reserve を抜ける。`README.md` §12 の対象外リストに #16 として追加。
- [ ] **未決**: 特権 reserve 引き出しを `Op` として起こすか。起こすと `reserve_outflow_only_via_redemption` が偽になり、blast-radius の headline が「2鍵の結託」から「admin 単独」に変わる。`Roles.sol` が `withdrawTokens` を `ADMIN_ROLE` に割り当てているのは確認済だが、`RedemptionPoolV0` がライブ経路かは未確認なので、そこが取れてから判断する。
- [ ] **未決**: `updateRedemptionValue` のロール対応。`Roles.assignAdminTargetsFor` は `setExchangeRate` を **`ADMIN_ROLE`** に割り当てており、モデルの `oracle` ゲートは実装と一致していない。`oracle` → `admin` に寄せると `redemption_price_writers` が「admin が2経路持つ」に畳まれる。ライブの `AccessManager` 設定を確認してから決める。
- [ ] 実装側に確認 — ライブの AccessManager が各セレクタに実際に何を割り当てているか、および遅延値(`Roles.sol` はセットアップ用ライブラリであってチェーン状態のスナップショットではない。外部のリスク評価では admin は 4-of-6 Safe)/ `RedemptionPoolV0` がデプロイ済みで現行の償還経路か(`README.md` に載っている公開アドレスは apxUSD / apyUSD / UnlockToken の3つだけ)/ `ApxUSDRateOracle` の UUPS `_authorizeUpgrade`(実装差し替えは `setRate` より強い権限。`README.md` §12 #12 で対象外扱いのままでよいか)。
- [x] 判明した対応関係は `model.md` §5 に表としてまとめた。償還が `ROLE_REDEEMER` ゲートであること、`redeem` に `minReserveAssetOut` があるので**ユーザー起点の経路は `redemption_has_no_floor` が示すより実際はマシ**であること(RFQ のようにユーザーが実行しない経路には効かない)、decimal スケーリングが未モデル化であることも記載。

### D. 報告の正確さ(Phase 9)

定理が通っていることと、**そのモデルが問題を表現できること**は別。後者が報告に出ていない。

- [ ] `outputs/<name>/README.md` に「単発 `step` についての保証」と「トレース上の保証」の書き分けを入れる。Apyx では要件適合82本すべてが single-step、トレース級は `Safety.lean` 4 / `BlastRadius.lean` 17。
- [ ] 仮説を持つ定理には、その仮説を満たす状態に到達するトレースを併記する(到達可能性を成果物にする)。現状 `req_unlock_claimable_after_3d` は `requestTime = now - minFlexibleClaim` という、どの操作列でも作れない状態を仮定している。
- [ ] 「このモデルが反証できないこと」の一覧を README に置く — 時計なし / 符号なし台帳 / 集約台帳 / 単一価格 / oracle stub と、それぞれが何を述べられなくしているか。定理リストは「何を証明したか」に答えるが「何を反証できたか」に答えていない。
- [ ] 補助関数についての補題を系の保証として数えない。`req_early_unlock_fee_linear_decline` は `flexibleUnlockFee` 単体の算術定理で、`step` に接続されていない。
- [ ] 非同期償還の完了側(request → claim のサイクルが閉じること)は liveness なので本枠組みの対象外である旨を明記する。`req_redemption_async_process` が証明しているのは「即時 claim が必ず落ちる」= クールダウンの強制であって、サイクルの完了ではない。

### E. PR #3(async / per-account の2族)の取り込み

診断・テンプレート・適用ゲートとして取り込む。Tier 1.5 の Apyx 実証は A / B の後。

- [ ] 取り込み時に I10 をリネームする(「決済タイミング中立」→ オプションの移転)。`settle` が `caller` を読まないので決済者の利得はモデルに存在せず、定理は払出規則についてのもの。`S10c`(決済期限の不在)/ `S10d`(取消・再申請による申請価格の吊り上げ)を I10 の射程を確定させる対として並べ直す。
- [ ] `accrual_never_lowers_debt` の statement を pin する。現状は「`s.positions` のどこかに `q.debt` 以下の debt を持つ位置がある」という存在量化なので、`debt = 0` のポジションが1つでもあれば無条件に成立する。証明は `List.mem_map` の pre-image を取っているので強い形に差し替え可能。
- [ ] PR 本文の Evidence 節の定理数を修正(15 / 37 → 実測 22 / 39、"three depend on none" → 6本)。
- [ ] Step 0b / 0c のゲートを、アーキタイプ名ではなく**モデル特徴**(時計 / 二相 op / in-flight 状態 / 符号付き価値 / 有界共有キュー)を主、アーキタイプ一覧を例示として書き直す。製品カテゴリで判定すると新しい型が出るたびに更新が要る。
- [ ] `Nat` 空虚性(`nat_solvency_is_vacuous` / `insolvency_witness`)は族の採否と独立に Step 0 プロファイルへ入れる。「純資産が負になりうるか」が Yes なら台帳を `Int` にする。
- [ ] `I21`(不変パラメータの証明)を族と独立に柱3へ追加する。`cases op` 1回で書けて、将来 setter が生えればビルドが落ちる。

### F. パイプライン自動化(継続)

- [ ] **柱2–4 + source-tracing の自動化**: `gen_lean` が Step-0 プロファイルから `templates/{blast-radius,invariants}` をインスタンス化し、原典照合(corpus→Solidity)を LLM+SMT で回す(現状は human/agent 協働)。C の誤りは人手照合の取りこぼしなので、自動化の受け入れ条件に「モデルの各フィールドが実装のどの変数に対応するか」の明示を含める。
- [ ] **相互改善ループの自動オーケストレーション**: 各フェーズ後の「build 緑・sorry 0・4ドキュメント整合」チェックを CI 化。
- [ ] few-shot exemplar(AMM-in-Lean4イディオム)をモデル/定理プロンプトへ注入
- [ ] モデル k-sample 選抜(プローブバッチ通過率でベスト採用)
- [ ] docsサイトの自動クロール(llms.txt/sitemap対応)
- [ ] EARS制約構文の抽出プロンプト導入(MAY節・スコープ副詞・例外条項の取りこぼし防止 = D6 抽出欠陥の予防)
