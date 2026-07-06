# 評価ログ

## Run 1 — ベースライン (2026-07-06, commit 061f547 相当)

入力: apyx コアdocs 9 URL。モデル: extract=gpt-oss:120b, lean=qwen3-coder:480b。

| メトリクス | 値 |
|---|---|
| 抽出要件 | 75 (formalizable判定 64) |
| SPEC.md | 29.5KB、RFC2119キーワード98出現、ボイラープレート/用語集/システムモデルあり |
| Lean コンパイル | ✅ round 3/6 |
| theorems / sorries | 64 / 64 |
| 空虚定理 (`: True`) | **64/64 (100%)** ← 致命的 |

### 所見
- **良**: SPEC.md は構造・網羅性とも実用レベル。State/操作関数のLeanモデル(pause/denylistゲート、cooldown、Option State)は妥当な形。
- **致命的**: 全定理が `theorem req_x : True := sorry`。一括生成 + コンパイル成功だけを報酬にした結果、モデルが定理を空虚化して逃げた。Clover/vacuity check の必要性(01-related-work.md)がそのまま再現。
- **中**: formalizable が過剰判定(オフチェーン custody/attestation 系まで true)。
- **小**: ingest のタイトルがサイト共通ボイラープレート行になる。`isWhitelistedUser := true` 等のプレースホルダがモデルを弱める。

### Run 2 に向けた変更
1. leangen 2段階化: モデル生成 → 要件バッチ(8件)毎に定理生成(モデル全文をコンテキスト、miniCTX知見)
2. 空虚定理の明示的禁止 + few-shot(executeOperation を参照する定理形を提示)
3. leancheck に vacuity 検出を追加、検出時は専用修復ラウンド
4. 証明試行の指示(simp [executeOperation] / omega / decide → 失敗時 sorry)
5. formalizable 基準: 「on-chain状態遷移モデル上で述語として書ける」に限定
6. ingest タイトル = 最初の `# ` 見出し
