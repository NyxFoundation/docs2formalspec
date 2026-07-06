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

## Run 2 — 2段階生成 + vacuityゲート (2026-07-06 15:22)

| メトリクス | Run 1 | Run 2 |
|---|---|---|
| 抽出要件 (formalizable) | 75 (64) | **25 (24)** ← merge過剰崩壊 |
| Lean コンパイル | ✅ r3 | ❌ 8ラウンド未収束 |
| theorems / proved / sorry | 64 / 0 / 64 | 14 / **13** / 1 |
| 空虚定理 | 64 | **0** ✅ |
| review | — | full 0, partial 9, missing 15 (うちUNFORMALIZABLE宣言12) |

### 所見
- 空虚化は根絶。13定理が実証明付き — 2段階生成+禁止則+cheap tacticsが機能。
- 未収束原因: 未知tactic等の構文エラーをLLM修復が直しきれない(qwen3-coderが同型の修正を繰り返す)。
- 要件25件は9ドキュメントに対して過少。merge promptが「テーマ類似」まで統合していた。
- UNFORMALIZABLE宣言12件: phase 1モデルに exchangeRate 単調性 / vesting / ERC4626 / rehypothecation 不在などのフィールド欠落。

### Run 3 に向けた変更(実装済)
1. PALM式**決定的sorryスタブ**: LLM修復4ラウンド超で、エラー行を含む定理の証明本体のみ機械的にsorry化(statement保持、収束保証)+ユニットテスト4件
2. merge prompt: 「同一操作・同一条件の真の重複のみ統合、汎化禁止」
3. **モデル拡張ラウンド**: UNFORMALIZABLE宣言された要件をフィードバックしてState/step拡張→当該定理を再生成
4. review: UNFORMALIZABLE宣言(unformalizable)と無言欠落(missing)を区別

### Run 2 に向けた変更
1. leangen 2段階化: モデル生成 → 要件バッチ(8件)毎に定理生成(モデル全文をコンテキスト、miniCTX知見)
2. 空虚定理の明示的禁止 + few-shot(executeOperation を参照する定理形を提示)
3. leancheck に vacuity 検出を追加、検出時は専用修復ラウンド
4. 証明試行の指示(simp [executeOperation] / omega / decide → 失敗時 sorry)
5. formalizable 基準: 「on-chain状態遷移モデル上で述語として書ける」に限定
6. ingest タイトル = 最初の `# ` 見出し
