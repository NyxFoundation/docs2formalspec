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

## 残TODO(次段の改善)
- [ ] **柱2–4 + source-tracing の自動化**: `gen_lean` が Step-0 プロファイルから `templates/{blast-radius,invariants}` をインスタンス化し、原典照合(corpus→Solidity)を LLM+SMT で回す(現状は human/agent 協働)。
- [ ] **相互改善ループの自動オーケストレーション**: 各フェーズ後の「build 緑・sorry 0・4ドキュメント整合」チェックを CI 化。
- [ ] few-shot exemplar(AMM-in-Lean4イディオム)をモデル/定理プロンプトへ注入
- [ ] モデル k-sample 選抜(プローブバッチ通過率でベスト採用)
- [ ] docsサイトの自動クロール(llms.txt/sitemap対応)
- [ ] EARS制約構文の抽出プロンプト導入(MAY節・スコープ副詞・例外条項の取りこぼし防止 = D6 抽出欠陥の予防)
