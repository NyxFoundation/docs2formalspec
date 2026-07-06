# SPECA ハーネスプラグイン設計 (2026-07-06)

## SPECA 側の規約(調査結果)
SPECA (`~/workspace/speca`) のハーネスプラグインは **Claude Code スキル**形式:
`.claude/skills/<name>/SKILL.md` に frontmatter(name / description / allowed-tools /
context: fork)+ JSON入力契約 + 手順を記述し、LLM がツールとして起動する
(例: `spec-discovery`, `subgraph-extractor`)。

## docs2formalspec プラグイン
- スキル名: `docs2formalspec`
- 入力契約:
```json
{
  "system_name": "apyx",
  "sources": ["https://docs.apyx.fi/apyx-overview/how-apyx-works.md", "..."]
}
```
- 実行: `uv run --project <docs2formalspecパス> d2fs run --name <system_name> <sources...>`
- 出力: `outputs/<name>/` の SPEC.md / <Name>.lean / requirements.json / leancheck.json / review.json。
  スキルは leancheck.json と review.json のメトリクスを読んで結果サマリをLLMへ返す。
- SPECA 連携価値: SPECA の 01a spec-discovery が見つけた URL 群をそのまま本スキルの
  `sources` に渡すと、RFC2119チェックリスト(SPECAのproperty生成の入力)と
  Lean4形式化(監査時のproof-attemptの機械検証可能な参照)が得られる。

本レポジトリ `skill/SKILL.md` に設置用ファイルを用意(speca側へは
`cp -r skill /path/to/speca/.claude/skills/docs2formalspec` で導入)。

## 品質ゲート(スキルが返すべき判定)
- `lean_ok == true` 必須
- `vacuous == 0` 必須
- 推奨閾値: `theorems ≥ 0.5 × formalizable`, review の full+partial ≥ 50%
- 閾値未達なら「参考出力」としてフラグ付きで返す
