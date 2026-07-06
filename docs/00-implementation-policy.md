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

## パイプライン (src/d2fs/)
```
ingest (URL→trafilatura→markdown | file→text)
  → extract (doc毎にRFC2119要件をJSON抽出 → 複数doc時はmerge/dedup/矛盾検出)
  → render_spec (RFC2119スペック文書をmarkdownで執筆)
  → model summary (state-transition モデル要約)
  → gen_lean (structure State + 操作関数 Option State + theorem req_*)
  → check_and_repair (lake build → エラーをLLMに渡して修復、最大6ラウンド)
```

## Lean 側の設計判断
- **mathlib 非依存**(lean/ は素の lake プロジェクト、Lean 4.31.0)。理由: コンパイルチェックループを数百msで回すため。DeFiの会計は Nat/Int で足りる。
- 失敗する操作は `Option State`(`none` = revert)でモデル化。
- 証明しきれない定理は `sorry` 許容(「形式化された要件」としての価値は残る)。sorry数を品質メトリクスとして出力 (leancheck.json)。

## 品質メトリクス (outputs/<name>/leancheck.json)
- lake build 成功 / 修復ラウンド数 / theorem数 / sorry数
- 今後: 要件カバレッジ(formalizable要件のうちtheorem化された率)、vacuity check(`True`定理の検出)

## TODO / 未決
- [ ] 類似研究サーベイの反映(調査エージェント実行中 → docs/01-related-work.md)
- [ ] apyx プロトコルのドキュメントURL確定(調査中 → docs/02-apyx.md)
- [ ] docsサイトのクロール(単一URLだけでなくサイトマップ/リンク追跡)
- [ ] SPECAプラグイン化のインターフェース設計(docs/03-speca-plugin.md 予定)
- [ ] 自己改善ループ: 出力レビュー用モデル (`review_model`) による spec 完備性チェック
