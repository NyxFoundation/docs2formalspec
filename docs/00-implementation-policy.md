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

## 到達点(2026-07-29 更新 — 時計の導入と実装照合のやり直し後)
- **モデルに時計(`Op.tick`)を入れた**。それまで `step` は `now` を一度も書かず、どのトレースでも時間が進まなかった。要件定理82本のうち32本が時計・期間の項を持つのに、時間が動く実行の上では1本も述べられていない状態だった。
  - **既存170定理は1本も書き換えずに通った**。必要だったのは `tick` 枝にガードが無いことによる `split` 失敗の吸収18箇所のみ。トレース級21本も全数無修正。値フィールドを動かさない op なので、保存則・solvency・blast-radius は時間経過に対して不変だった。
  - 時計が入って初めて述べられるようになったことを実証: `redemption_cycle_closes_after_cooldown`(request → `tick` → claim が同一トレースで成立)、`flexible_fee_schedule_is_reachable`(3日待ちで手数料299bps・10日で180・20日で10、返却額 9701 / 9820 / 9990)。
- **`updateRedemptionValue` を実装した**(旧: `some s` の placeholder)。stub 前提だった4定理を正確な形へ。`redemption_price_admin_only` は `redemption_price_writers` に一般化 — `redemptionValue` を書けるのは `catastrophicBackstop`(admin・緊急フラグ必須・値は公正 pro-rata・reserve と buffer を同時に0にする**騒がしい**書き込み)と `updateRedemptionValue`(oracle・任意の非ゼロ値・副作用なしの**静かな**書き込み)の2つだけ。
  - `rfq_payout_is_set_by_execution_timing`: 同一 state・同一ユーザー・同一 request・同一カウンターパーティで、即時実行なら 100 USDC、正直な oracle 更新1回のあとなら 50 USDC。**`admin_rfq_coalition_drains` が2鍵の結託としてしか書けなかったのは、敵の強さの上界ではなくモデルの表現力の限界だった。**
- **実装照合をやり直した**。`redemptionValue` の対応先は `ApxUSDRateOracle.rate` ではなく `RedemptionPoolV0.exchangeRate`(前者は Curve Stableswap-NG 向けで `src/` 配下に消費者がいない)。スケールも実装 1e18 / モデル `ray = 1e27` で不一致。`withdraw` / `withdrawTokens` は `ADMIN_ROLE` で償還を経ずに reserve を抜ける。→ `outputs/apyx/model.md` §5、`README.md` §6.4 の #16 / #17。
- **報告の形を変えた**(`outputs/apyx/README.md` §6.0)。定理の本数ではなく **量化のスコープ**(トレース級は22本のみ、要件適合82本を含む残りは single-step)と **反証可能性**(符号なし台帳 / 集約台帳 / 単一価格が何を述べられなくしているか)を出す。解消済みの2件(時計なし・oracle stub)も、この問いを立てなかったコストの実例として残した。
- **PR #3(async / per-account の2族)を取り込んだ**。診断・テンプレート・適用ゲートとして。I10 のリネーム、`accrual_never_lowers_debt` の pin、ゲートのモデル特徴化、`Nat` 空虚性の Step 0 への移動、I21 のコア昇格を適用済。
- 現在: `outputs/apyx` 183定理 + テンプレート参照実装63定理、`lake build` 緑、`sorry` 0。

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
- [x] **解決**: 特権 reserve 引き出しを `Op.withdrawReserve` として起こした。決め手は `RedemptionPool/Access.t.sol` に `test_RevertWhen_WithdrawNotAdmin` / `test_RevertWhen_WithdrawTokensNotAdmin` があること — 見落としではなく**意図的にテストされた admin 機能**。帰結: `reserve_outflow_only_via_redemption` に「償還ではない第3の出口」が増え、`solvency_preserved` は stress / backstop と並べて名指し除外、`no_free_value_trace` は**贈与経路**として名指し除外(admin が指定したアドレスに、対価なしで USDC が入るため)。blast-radius の headline は「2鍵の結託」から **「admin 単独」** に変わった。
- [x] **解決**: `updateRedemptionValue` を `oracle` → `admin` に再ゲート。決め手は `Roles.assignAdminTargetsFor` と `test_RevertWhen_SetExchangeRateNotAdmin`。`redemption_price_writers` は「**admin が償還価格に2経路持つ**」に畳まれた — 緊急フラグ必須で reserve と buffer を同時に0にする**騒がしい**経路(`catastrophicBackstop`)と、副作用なしの**静かな**経路(`updateRedemptionValue`)。oracle 系の定理は市場価格のみを扱う形に戻した。
- [x] **解決**: RFQ 経路の機構を両レグに分けた。`Op.executeRFQRedemption` は**文書上のプロセス**(ユーザー自身の記録済み request に対する決済)、新設の `Op.poolRedeem amount receiver minOut` は**オンチェーンの契約**(`ROLE_REDEEMER` ゲート・`burnFrom(msg.sender)`・指名 `receiver`・`minReserveAssetOut` フロア)。request レジストリにオンチェーンの対応物は無く、ユーザーの同意と引き渡しはこの状態機械の外側で起きる。
  - `no_role_transfers_user_funds`: `poolRedeem` が触れるのは**呼び出し元自身の残高だけ**なので carve-out が要らない(`executeRFQRedemption` と対照的)。
  - `no_free_value_trace` / `ValuePreservingOp`: `receiver` を指名して USDC を渡すので**贈与経路**として名指し除外。
  - `reserve_outflow_only_via_redemption`: 焼く先と払う先が別アドレスなので独立の disjunct。
  - `pool_redeem_floor_is_the_redeemers`: 同一 state・同一 receiver・同一 100 apxUSD で、par なら 100、正直な価格更新1回のあとなら 50。しかも後者は**受理される**(フロアが0で、フロアを選ぶのは redeemer だから)。redeemer はフロアを 100 にすれば拒否できる。**価格保護のレバーは、晒されていない側が握っている。**
- [x] **オンチェーンで解決**(2026-07-30、≈ block 25,641,600 時点。`outputs/apyx/model.md` §6 に記録)。
  - AccessManager は `0xe167330E…2824`。ロールは**遅延の階段**になっている — 21=0(pause) / 22=4時間(価格 push) / 23=24時間 / 24=3日(`upgradeToAndCall`) / 25=7日(`setAuthority`)。遅延の**短縮**は `minSetback` 5日、role 0 の付与は 7日。遅延ゼロで残っているのは **ADMIN_ROLE 本体**だけで、保有者は Safe `0xABdd8c8e…65e96` 1つ(デプロイヤ EOA と運用 Safe は付与後に**剥奪済**)。
  - **`RedemptionPoolV0` はこの authority 配下にデプロイされていない。** `setExchangeRate` / `redeem` / `ApxUSDRateOracle.setRate` のセレクタは function-role テーブルに1つも現れない。
  - 償還価格の実体は **`ApyxRedemptionOracle`**(`0x2037a5eb…23b4`)。**setter を一切持たない**読み取り専用アグリゲータで、`min(担保比率, cap)` を publish し **`cap()` = 1.00**。上流の `ApyxCollateralRatioOracle.pushRound` は role 22 = **4時間の予約実行**。
  - 帰結3件を `README.md` に反映済 — (a)「償還価格に上限が無い」は**設計**についての主張で、デプロイには上限がある、(b) `Safety.lean` の仮説 `h_rv : redemptionValue ≤ ray` は **cap によってデプロイ不変条件になっている**(仮定ではなく強制)、(c)「admin 変更は同一ブロックで発効」は**モデルについては真、デプロイについては ADMIN_ROLE 以外は偽**。
  - `withdrawReserve` の live 対応物は `YieldDistributor.withdrawTokens` で、role 23 = **24時間の予約実行**。
- [x] **Safe とキューも確認済**。admin Safe `0xABdd8c8e…65e96` は **4-of-6**、運用 Safe `0xf9862EfC…63cE2` は **3-of-6**、**署名者6名は同一**。つまり無遅延 admin 層と遅延層の分離は「署名者の分離」ではなく「閾値の分離」。
  - ただし**迂回はできない** — `getRoleGrantDelay` が全運用ロール(0/21/22/23/24/25)で **7日**なので、無遅延の新規保有者を作れない。セレクタを role 21 に付け替える経路も collateral oracle の `getTargetAdminDelay` = **3日**、遅延短縮は `minSetback` **5日**。**無遅延の価格書き込みに至る最短経路で約3日の公開猶予**がある = `timelock_escape_guarantee` が形式化している escape window がデプロイに存在し、しかも定量化できた。
  - キュー: `expiration()` は7日。累計896件中 執行169・取消5、残りはほぼ期限切れ。読み取り時点で生きているのは4件で全て housekeeping(`pushRound(int256,uint80)` を role 22 へ、`setUpstreamOracle` を role 24 へ、`MinterV0.setRateLimit(1e24, 86400)`、および既に反映済の実装への `upgradeToAndCall`)。
  - なお `pushRound(int256,uint80)` / `setUpstreamOracle` / `clearOverride` は現時点で **role 0(admin・無遅延)**のまま。上記キューはそれを塞ぐ方向の変更。
- [x] Safe 6署名者は**全員が素の EOA**(ENS なし・public tag なし・いずれも multisig ではない)。チェーンからはこれ以上分からないので、実体の確認は実装側の質問として残る。
- [x] **個人 EOA が無遅延の権限を2つ持っている**ことを確認。role 31(付与遅延0・実行遅延0)は Safe ではなく**署名者6名のうち5名 + デプロイヤ EOA に個別付与**されていて、`MinterV0.cancelMint`(ガーディアン停止、即時で妥当)と `OrderDelegate.transferToken` / `transfer`(`OrderDelegate` と**未検証コントラクト** `0xdbEF8322…20ef` 上)を覆う。読み取り時点で両者の残高は0なので現エクスポージャはゼロだが、能力としては Safe 閾値の外側で単独・無遅延。role 41(`batchLiquidate`)も同型の単独 keeper。
- [x] **統治対象とモデル対象のズレを確定**(前回の記述を訂正済)。効くのは1点だけだった。
  - **モデル化している unlock 経路(`UnlockToken`)の残高は 24,936 apxUSD。同じ authority 配下に、構造が同一の `CommitToken` "CT-apxUSD" があり、そちらは 6,226,697 apxUSD = 供給の1.90%、250倍。** 時計の導入で開いた非同期償還の議論は、2桁半小さいほうのインスタンスに向いていた。証明の誤りではなく Step-0 のスコープ誤り。`README.md` §6.4 #18 を書き直した。
  - `LiquidationBatcher` は**前回の書き方が過大だった**。ソースを読むと **Morpho Blue** に対する清算バッチャーで、Apyx 内部の清算機構ではない(Apyx に口座別担保ポジションが無いので、そもそも欠けている内部機構は存在しない)。市場 allowlist はコンストラクタ固定で setter 無し、`withdrawTokens` は宛先引数を取らず不変の `WITHDRAW_DESTINATION`(運用 Safe)固定、pausable でも upgradeable でもない。**無遅延の role 41 keeper は構成によって「どの市場を清算できるか」「収益がどこへ行くか」の両方を縛られている**。README §6.4 #2(クロスプロトコル合成)の管轄で、設定としてはむしろ堅い。
- [ ] 次段: Step-0 プロファイルを**ドキュメントだけでなくオンチェーンの authority グラフから**起こす手順にする(F の自動化に組み込む)。今回のスコープ誤りはこれが無かったことに起因する。
- [x] **CommitToken を4インスタンス全対応に一般化**。cooldown と supply cap は state フィールドなので1モデルで足りる。`liveDeployments` に4件(CT-apxUSD 14d/100M、CT-apyUSDapx 14d/20M、CT-apxUSDUSDC 14d/50M、UnlockToken 20d/上限なし)を列挙し、`cycle_closes_at_every_live_deployment` で liveness をそれぞれに当てた。
- [x] **償還価格パイプラインをモデル化** — `outputs/apyx/RedemptionOracle.lean`(8定理)。`ApyxCollateralRatioOracle.pushRound`(role 22・4時間予約)→ `ApyxRedemptionOracle` の `min(担保比率, cap)`。§6 で散文として書いた訂正が定理になった。
  - `published_never_exceeds_par` / `cap_immutable(_trace)` — 全トレースで cap 以下、かつパイプラインのどの操作も cap を動かさない(I21 を実デプロイに適用した形)。**`Safety.lean` の `h_rv : redemptionValue ≤ ray` はこれで仮定ではなく強制になる。**
  - `published_has_no_floor` — 0 を push すれば 0 が publish される。**§9.1 の2つの finding のうち、cap 側はデプロイが答え、floor 側は生き残る**、が証明で分かれた。
- [x] **3ドキュメントを同期**。`README.md`(§4.4 を4インスタンスに、§4.5 を新設、§9.1 と artifact map を追随)、`model.md`(§7 新設 — 2モジュールとインスタンス表)、`SPEC.md`(§10a 新設。**由来がドキュメントではなくチェーン**であることを明示し、DR-1〜DR-11 として分離)。
- [x] **非同期償還族を CT-apxUSD に対してインスタンス化した** — `outputs/apyx/CommitToken.lean`(8定理・`lake build` 緑・`sorry` 0・公理は `propext`/`Quot.sound`)。`docs/06` §7 が「実プロトコルの worked reference は一つも無い」としていた状態を解消。
  - 成立するもの: `cycle_closes_after_the_live_delay`(実デプロイの14日を待って claim が同一トレースで成立)/ `claim_conserves`(焼いた分ちょうどを払う)/ `commitment_is_bounded_by_balance`(保有以上にコミットできない)。
  - 保有者が知っておくべき挙動3件(いずれもコードの約束には違反しない): **`topup_restarts_the_whole_cooldown`**(トランシェが無く `requestedAt` を丸ごと上書きするので、14日経過済みの請求に1単位足すと全額がもう14日ロックされる)/ **`no_partial_claim`**(`redeem` は完全一致のみ。上と合成すると、積み増した保有者は満期済み部分だけ引き出すことができない)/ **`raising_the_delay_unclaims_pending_requests`**(`_cooldownRemaining` が storage の現在値を読むため、遅延の延長が**未決済の請求すべてに遡及**する。`setUnlockingDelay` は role 24 = 3日の予約実行なので、契約ではなくガバナンスで縛られている)。
  - `request_does_not_escrow` はコントラクト自身が docstring で挙げている ERC-7540 逸脱(請求してもシェアは owner の残高に残る)を記録し、それを安全にしている算術チェックと対にした。
- [x] 判明した対応関係は `model.md` §5 に表としてまとめた。償還が `ROLE_REDEEMER` ゲートであること、`redeem` に `minReserveAssetOut` があるので**ユーザー起点の経路は `redemption_has_no_floor` が示すより実際はマシ**であること(RFQ のようにユーザーが実行しない経路には効かない)、decimal スケーリングが未モデル化であることも記載。

### D. 報告の正確さ(Phase 9)

定理が通っていることと、**そのモデルが問題を表現できること**は別。後者が報告に出ていない。

- [x] `outputs/apyx/README.md` に §6.0 を新設。量化のスコープ(トレース級は22本 — `Safety.lean` 4 / `BlastRadius.lean` 18。要件適合82本を含む残りは single-step)と、モデルが反証できないことの一覧を記載。
- [x] 到達可能性を成果物にした。`flexible_fee_schedule_is_reachable`(申請 → `tick` → claim で、3日待ちなら手数料299bps・10日で180・20日で10、返却額はそれぞれ 9701 / 9820 / 9990)が `req_unlock_claimable_after_3d` の仮定を実際に到達させている。標準 unlock 側は `redemption_cycle_closes_after_cooldown`。
- [x] README §6.0 に「反証できないこと」の表を設置(符号なし台帳 / 集約台帳 / 単一価格)。加えて**解消済みの2件**(時計なし・oracle stub)も、この問いを立てなかったコストの実例として明記した。
- [x] `req_early_unlock_fee_linear_decline` が `flexibleUnlockFee` 単体の算術定理である点を明記し、系として発火することを `flexible_fee_schedule_is_reachable` で別途証明した。
- [x] `req_redemption_async_process` が証明しているのは「即時 claim が必ず落ちる」= クールダウンの強制であって、サイクルの完了ではない旨を README §6.0 に明記。完了側は liveness で、誰にも行動を強制しない本枠組みの対象外(§6.3)。ただし到達可能性は上記2本で示した。

### E. PR #3(async / per-account の2族)の取り込み

診断・テンプレート・適用ゲートとして取り込む。Tier 1.5 の Apyx 実証は A / B の後。

- [x] I10 を「決済タイミング中立」→ **「払出の非吊り上げ」**にリネーム済(`docs/06` S10 / `docs/08` I10 / `docs/09` / `templates/invariants/`)。`settle` が `caller` を読まないので決済者の利得はモデルに存在せず、定理は払出規則についてのもの。S10c(決済期限の不在)と S10d(取消・再申請)を射程を確定させる対として並べ直した。
- [x] `accrual_never_lowers_debt` を pin 済。`s'.positions = s.positions.map f ∧ ∀ p ∈ s.positions, p.debt ≤ (f p).debt` に変更し、呼び出し側向けに pre-image 形の `accrual_never_lowers_debt_pointwise` を追加。骨格テンプレート側も同じ形に直した。
- [x] 定理数を実測値に修正(`docs/06` §8 の 39 → **41**。pin 化で1本増えたため)。PR 本文側の 15 / 37 と "three depend on none" は PR の説明文なので取り込みでは触らない。
- [x] Step 0b をモデル特徴主・アーキタイプ例示に書き直し済。Step 0c 側も「CDP かどうか」ではなく**量化構造**(プール単位の不等式1本 vs コレクション上の全称量化)で説明し、per-user レコードを持つ設計全般(ステーキング / ベスティング / NFT 担保)に効くこと、およびそれが「補助関数の補題を `step` に運び忘れる」特徴的バグを生むことを明記。
- [x] `Nat` 空虚性を Step 0 プロファイル側の話として書き直し済。族を採らなくても「純資産が負になりうるか」を問う。あわせて**一般形**(定理の強さはモデルが失敗を提示できるかで上から抑えられる。時計なし / 集約台帳 / 単一価格も同型)を明記し、`outputs/apyx/README.md` §6.0 を worked example として参照。
- [x] `I21` をコア集合へ昇格済。`templates/invariants/README.md` のコア表にパターン G の隣として追加し、骨格テンプレートでも Tier 1-C 節から G の直後へ移動。Step 0c のゲートには「このゲートの答えに関わらず採る」と注記。

### F. パイプライン自動化(継続)

- [ ] **柱2–4 + source-tracing の自動化**: `gen_lean` が Step-0 プロファイルから `templates/{blast-radius,invariants}` をインスタンス化し、原典照合(corpus→Solidity)を LLM+SMT で回す(現状は human/agent 協働)。C の誤りは人手照合の取りこぼしなので、自動化の受け入れ条件に「モデルの各フィールドが実装のどの変数に対応するか」の明示を含める。
- [ ] **相互改善ループの自動オーケストレーション**: 各フェーズ後の「build 緑・sorry 0・4ドキュメント整合」チェックを CI 化。
- [ ] few-shot exemplar(AMM-in-Lean4イディオム)をモデル/定理プロンプトへ注入
- [ ] モデル k-sample 選抜(プローブバッチ通過率でベスト採用)
- [ ] docsサイトの自動クロール(llms.txt/sitemap対応)
- [ ] EARS制約構文の抽出プロンプト導入(MAY節・スコープ副詞・例外条項の取りこぼし防止 = D6 抽出欠陥の予防)
