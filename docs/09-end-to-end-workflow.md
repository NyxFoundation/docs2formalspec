# 一気通貫ワークフロー — 新プロトコルへの適用 runbook

(2026-07-08。Apyx で確立した全工程を、任意の DeFi プロトコルに**端から端まで**適用するための手順書。docs/00 の方針を実務手順に落とし込み、docs/05〜08 と `templates/` を1本のパイプラインに束ねる。)

## 0. 全体像

**入力**: プロトコルの公開ドキュメント(URL/ファイル)+ **実装 Solidity ソース**(`<org>/<repo>`、あれば必須取得)。
**出力**: `outputs/<app>/` に —
- `corpus.md`(原典ドキュメント)/ `requirements.json`(各要件に `source_quote` 必須)/ `SPEC.md`
- `model.md`(state machine の平易記述)/ `<App>.lean`(モデル + **柱1**)
- `BlastRadius.lean`(**柱2**)/ `Safety.lean`(**柱3**)/ `SpecDefects.lean`(**柱4** + gap-witness)
- `review.json`(定理を**4由来**で分類)/ `README.md`(§6.4 に実装層 hand-off リスト)

**中核方針**: 生成物は一発では正しくない。**spec ↔ model ↔ Lean ↔ implementation を相互改善するループ**を回し、各フェーズ後に「`lake build` 緑・`sorry` 0・公理クリーン・4ドキュメント整合」を不変条件として維持する。**実装(Solidity)が最終真実**、corpus はその非形式記述にすぎない。

```
Ingest(docs + Solidity) → Extract/Specify → Model → 柱1 → ★Source-tracing gate
   → 柱2(blast-radius) → 柱3(design-invariants) → 柱4(spec-consistency) → Report
   ↖────────────── 相互改善ループ(実装照合で spec/model/Lean を co-improve)──────────────↙
```

---

## Phase 1 — Ingest(**Solidity も取得**)

1. ドキュメントを ingest → `corpus.md`(現行 pipeline)。
2. **実装ソースを clone**(`gh repo clone <org>/<repo>` を scratchpad へ)。これが ground truth。主要コントラクトを棚卸し(トークン、vault、minter、redemption、oracles、roles/AccessManager、vesting、bridge)。
3. Step 0 の**モデルプロファイル**を埋める(`templates/blast-radius/README.md` と `templates/invariants/README.md` の Step-0 表): value フィールド、role アドレス、role-gated ops、debit sites、reserve outflow、price/param writers、accounted-mint ops、raw-transfer 有無、conversion 丸め方向、境界付き/無しパラメータ。→ 以降の全柱の設計図。

## Phase 2 — Extract & Specify

1. RFC 2119 要件を抽出 → `requirements.json`。**各要件に `source_quote` を必ず付与**(後の原典照合 §Phase 5 の要)。EARS 制約構文で MAY 節・スコープ副詞(during routine/stress 等)・例外条項を**落とさない**(抽出欠陥 D6 の予防)。
2. `SPEC.md` を render。

## Phase 3 — Model(State / Op / step)

1. `State` レコード、**閉じた** `inductive Op`、`step : State → Op → Address → Option State`(`none`=revert)。`model.md` を並走生成。
2. 閉じた `Op` が全柱の網羅証明の土台(「どの op も不変条件を破らない」を*定理*にできる)。

## Phase 4 — 柱1: 要件適合(`req_*`)

各 formalizable 要件 → `theorem req_*`。`leancheck` 修復ループ(`lake build` → per-declaration 修復、最大6ラウンド)。`leancheck.json` にメトリクス。

## Phase 5 — ★ Source-tracing gate(**新規・必須**、docs/07 §3.0)

**ここが今回追加した中核**。柱1で出た**矛盾・曖昧・vacuity・under-specification** の各候補を、機械的に判定して終わらせず、**必ず原典に遡る**:

1. 候補の各要件の `source_quote` を確認。
2. **原典を優先順位で読む**: ① `corpus.md` → ② corpus が曖昧・暗黙・不精密なら **Solidity 実装を ground truth** とする。
3. 根本原因を三分:
   - **(a) 原典仕様の欠陥** → finding(設計欠陥/不完全性)。柱4で機械証明 or gap-witness 化。
   - **(b) 抽出欠陥(D6)** → 原典を取りこぼした/過剰一般化した → **`requirements.json`/`SPEC.md` を修正**(ツール側の欠陥)。
   - **(c) corpus 曖昧 → Solidity で確定** → 実装どおりに **spec を構成し、必要なら model も修正**。
4. **相互改善ループ**を回す: 修正が spec/model/Lean/README のどれに波及するかを追い、各所を整合させる(今回 `model.md`/`README` が stale 化した教訓 → **変更のたびに4ドキュメントを照合**)。モデル修正(例: catastrophic の per-unit 次元修正)は依存定理へカスケードするので `lake build` 緑を都度確認。

> **この gate を省くと、ツール自身の抽出ミスを「プロトコルの欠陥」と誤報告する**(Apyx で候補1がまさにこの罠だった)。原典照合は偽陽性防止の要。

## Phase 6 — 柱2: blast-radius(`templates/blast-radius/`)

役割集合ごとの被害上限(鍵漏洩・多役割結託)。テンプレの Step-0 プロファイルからインスタンス化。`execTrace`、role 述語、exact-effect frame、trace 帰納、非保管性(T4)、被害上限、rate-limit/timelock ラッパー(設計定理)。→ `BlastRadius.lean`。

## Phase 7 — 柱3: design-safety invariants(`templates/invariants/`)

**コア不変条件を閉じた `Op` 上で全経路証明**(業界最頻・最大損失の Euler 型を構造的に閉じる):
- **I1 保存則 / I2 solvency / I3 非希釈 / I4 丸め有利 / I5 donation 免疫**(コア4+I1)、**I7 単調 accumulator**。
- **G gap-witness**: 境界の無い経済パラメータは「悪状態の到達可能性を witness 付きで証明」= **確定した脆弱性**(例 `redemption_has_no_floor` / `redeem_payout_has_no_cap`)。
→ `Safety.lean`(+ 必要なら `SpecDefects.lean` に gap-witness)。被覆マトリクスは docs/08 §B.4。

## Phase 8 — 柱4: spec-consistency(docs/07)

要件集合そのものの健全性を検査(挙動モデル化の**前**に効く上流工程):
- **M1 充足性 / realizability**(Beanstalk の MAY-vs-MUST、Terra の unrealizable を捕捉)。
- **M2 ペア/トリプル矛盾**(合成的矛盾 D1c は三つ組を見る)。
- **M4 vacuity 全走査 / M5 被覆・沈黙解析**。
- 確定した矛盾/gap は `SpecDefects.lean` に機械証明。
→ Phase 5 の gate と連動(源流照合込み)。

## Phase 9 — Report

- `review.json` に各定理を**4由来**で分類: 要件由来 / 脅威モデル由来 / 設計不変条件由来(証明 or gap-witness)/ spec-consistency 由来。
- `README.md`: 4本柱の結果 + **設計の弱点(finding)**を正直に + **§6.4 実装層 hand-off リスト**(静的解析/SMT/fuzz で何を確認すべきか。docs/08 参照)+ **bytecode⊨model は Certora/Halmos で再確認**の明記。

---

## 相互改善ループの不変条件(毎フェーズ後にチェック)

1. `cd lean && lake build` **緑**、live `sorry` **0**、公理は `propext`/`Quot.sound`(+ 必要な `Classical.choice`)のみ。
2. **4ドキュメント整合**: `requirements.json` / `SPEC.md` / `model.md` / `README.md` が現在の Lean と一致(モデル/仕様を変えたら**必ず**全部を照合。stale を残さない)。
3. **実装が最終真実**: corpus と実装が食い違えば実装に合わせて spec/model を直す(§Phase 5)。
4. 出力は `outputs/<app>/` 一箇所に集約(docs/00 の規約)。

## 次プロトコル適用チェックリスト(要約)

- [ ] Phase 1: docs ingest + **Solidity clone** + Step-0 プロファイル。
- [ ] Phase 2–4: requirements(source_quote 必須)→ SPEC → model → 柱1(`lake build` 緑)。
- [ ] **Phase 5: source-tracing gate**(候補を corpus→Solidity で三分、抽出欠陥は spec 修正、相互改善)。
- [ ] Phase 6: `templates/blast-radius/` をインスタンス化 → 柱2。
- [ ] Phase 7: `templates/invariants/` をインスタンス化 → コア4 + I7 + gap-witness → 柱3。
- [ ] Phase 8: spec-consistency(充足性/realizability/vacuity/coverage)→ 柱4。
- [ ] Phase 9: review.json(4由来)+ README(finding + §6.4 実装 hand-off)。
- [ ] 各フェーズ後: 4ドキュメント整合 + build 緑を確認。

## 自動化ステータス(honest)

- **柱1 は現行 `src/d2fs/` で自動化済み**(ingest→extract→spec→model→gen_lean→leancheck 修復)。
- **柱2–4 + Phase 5 の source-tracing + 相互改善は、現状 `templates/` 駆動の human/agent 協働**(Apyx が worked reference)。完全自動化は次段: gen_lean が Step-0 プロファイルからテンプレをインスタンス化し、原典照合(corpus→Solidity)を LLM+SMT で回す構想(docs/00 残TODO)。
- 品質は「LLM 一発生成」より「テンプレ + 実装照合 + 機械検証ループ」に依存する、というのが Apyx の実証的教訓(docs/03 の 53% プラトー参照)。**再利用可能な資産はテンプレと本 runbook**。
