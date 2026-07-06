# 評価ログ

## Run 12 (relean, modelgen=deepseek-v4-pro) — 2026-07-06 21:20 ✅ 現時点のベスト

| メトリクス | Run 8 (旧ベスト) | **Run 12** |
|---|---|---|
| モデルゲート | r1通過 | r2通過、**拡張もr1通過** |
| theorems (live) / killed | 49 / 2 | 43 / 22 |
| proved (機械証明) | 8 | 7 (auto-prove +4) |
| vacuous (live) | 0 | 0 |
| review full | 11 | **14**(フィードバック前9→14) |
| review full+partial | 35/72 (49%) | 36/77 (47%) |

- deepseek-v4-pro のモデルは64定理(過去最多)を引き出したが、statementの外れも増え
  killed 22。full判定は最多で、審判フィードバック再生成の効果(+5 full)も確認。
- **結論**: ローカルLLM構成での到達点はおよそ「コンパイル100%・忠実カバレッジ~50%・
  機械証明~15-20%」。Verina(ICLR 2026)のフロンティアモデル値(スペック健全完全51%)
  とほぼ同水準であり、パイプライン設計としては飽和点に到達。

## 総括(12ラン)

| 失敗モード | 対策 | 効果 |
|---|---|---|
| 空虚定理 (Run 1: 64/64) | 2段階生成+禁止則+de-vacuate | 恒久的に0 |
| whole-file修復の定理削除 (Run 4) | per-declaration修復エンジン | 削除消滅 |
| パースエラーのカスケード誤爆 (Run 6-7) | **ブロック単体コンパイル検証** | killed 40→2 (Run 8) |
| statement幻覚識別子 | バッチ即時検証+リトライ | 部分的 |
| 証明の弱さ | cheap-tactic自動証明 | +4〜6/run |
| 要件の無言ドロップ | カバレッジ照合パス | missing 23→10 |
| 不忠実な形式化 | Clover式review+審判フィードバック再生成 | full +5/run |
| モデルサンプル分散 | ゲート+再サンプル+modelgen専用ロール | ゲート失敗の下流汚染を根絶 |

### 次の改善候補(未実装、優先順)
1. **few-shot exemplar**: AMM-in-Lean4 論文(arXiv:2402.06064)のイディオムを
   MODEL_SYSTEM / THEOREM_SYSTEM に注入(PropertyGPT のRAG知見の軽量版)
2. モデル k-sample 選抜(プローブバッチのコンパイル率でベスト選択)
3. 証明専用パス(Goedel-Prover-V2 はOllama Cloud未提供のため要ローカルGPU)


## Run 9–11 — 2026-07-06 18:00–19:30

| メトリクス | Run 9 | Run 10 (full) | Run 11 |
|---|---|---|---|
| 抽出 | (Run 3 の83再利用) | **82 (77 formalizable)** | Run 10 を再利用 |
| モデルゲート | ○ | **✗ 4ラウンド全滅→中断** | 4ラウンド目で辛勝 |
| theorems / proved / killed | 49 / 10 / 12 | — | 15 / 0 / 8 |
| auto-prove | +6 | — | +0 |
| coverage照合 | 8件回収 | — | 14+4件回収 |
| review full/partial | 9 / 25 | — | (log参照) |

### 知見
- 自動証明パス(+6)とカバレッジ照合(missing 23→10)は機能。
- **実行間分散の支配要因はドメインモデルの品質**: Run 8(良サンプル)49定理/killed 2
  vs Run 11(悪サンプル)15定理/proved 0。モデルが貧しいと定理は形式化不能宣言や
  キルに流れる。
- Run 10: モデルがゲート4ラウンド全滅 → best-effort続行が全下流を汚染 → **再サンプリング**
  実装(3サンプル、全滅なら明示エラー)。
- モデル生成専用ロール `D2FS_MODELGEN_MODEL` 追加。Run 12 で deepseek-v4-pro を試験
  (1コールなので速度より品質)。


## Run 8 (relean, ブロック単体検証) — 2026-07-06 17:45 ✅ 構造的ブレークスルー

| メトリクス | Run 7 | **Run 8** |
|---|---|---|
| コンパイル | ✅ r4(キル40の空洞) | **✅ r3** |
| theorems 生存 | 13/53 | **49/50**(キル2のみ) |
| proved / sorries | 3 / 10 | 8 / 41 |
| vacuous | 0 | 0 |
| review full/partial/mismatch | 5/5/1 | **11**/24/11 |

ブロック単体コンパイル検証がカスケード誤爆を根絶。収束も速い(3ラウンド)。

### 残課題 → Run 9 の変更(実装済)
1. proved 8/49 → **cheap-tactic自動証明パス**(LLM不要): sorryスタブに
   simp[step]/simp_all/unfold+split/omega/decide を順に試し、通れば採用
2. 真の欠落23要件(バッチ再生成時の無言ドロップ)→ **カバレッジ照合パス**:
   定理もUNFORMALIZABLE宣言も無い要件を検出して追加バッチ生成(≤2周)
3. (次回) review mismatch/vacuous 判定の修復ループへのフィードバック


## Run 7 (relean, バッチ即時検証) — 2026-07-06 17:25

結果: ✅コンパイル(r4)だが theorems 13 / proved 3 / **killed 40**。バッチ再生成の成功は 3/13。

### 決定的発見: エラー帰属のカスケード誤爆
キルされた定理を現行モデルに対し**単体コンパイルすると成功する**ことを確認。
壊れた定理Aのパースエラーは次の定理Bの行に「unexpected token 'theorem'」として
報告されるため、行範囲によるエラー帰属は無実の隣接ブロックを連鎖的に処罰していた
(Run 6-7 の大量キルの真因。バッチ検証の「失敗」も同じカスケードで過大計上)。

### Run 8 に向けた変更(実装済)
- エラー帰属を全廃し、**ブロック単体コンパイル検証**へ: 各定理を model+単体 でビルドし、
  本当に失敗するものだけをエスカレーション(修復→スタブ→キル)。検証済みはキャッシュ。
- 重複定理名の決定的デデュープ(後勝ちをキル)。
- フルビルドが個別検証後も失敗する場合のみ: モデル修復 or 該当ブロックの検証無効化。


## Run 5 / Run 6 (relean, per-decl修復エンジン) — 2026-07-06 16:30–17:15

| メトリクス | Run 5 | Run 6 |
|---|---|---|
| コンパイル | ❌ (境界バグでモデル修復が空回り) | ✅ round 5 |
| theorems / proved | 33 / 20 | 11 / (キル42) |
| vacuous | 0 | 0 |
| review full/partial/mismatch | 4 / 23 / 4 | 1 / 7 / 2 |

### Run 5 の失敗: 境界の行数不整合
build_file はモデル領域を rstrip して組み立てるのに、境界判定は未stripの行数を使用
→ モデル末尾の空行分だけ境界が最初の定理ブロックに食い込み、定理エラーが
「モデルエラー」と誤帰属 → モデルゲート(単体ではOK)を10回空回り。
→ 修正: 境界を組立時のオフセット(最初のブロックの開始行)から取得。

### Run 6 の失敗: statementの幻覚識別子で大量キル
53定理中42のstatementがモデルに存在しない識別子/フィールドを参照。
修復(モデル文脈が末尾12k切断で不十分)→スタブ(statementは残るので失敗)→キル
の順で53→11に減少。「コンパイル成功」は達成したが空洞化。
また旧メトリクスは BROKEN コメント内の sorry まで数えて proved=-34 と表示。

### Run 7 に向けた変更(実装済)
1. **バッチ即時検証** (AutoSpec式): 各定理バッチ生成直後に model+batch を単体コンパイル、
   失敗ならエラー付きで1回再生成(幻覚識別子をその場で修正)
2. repair_decl のモデル文脈を先頭14k(State/Op/stepは先頭にある)
3. メトリクスをlive行のみでカウント、killed を別掲


## Run 3 (フルパイプライン) / Run 4 (relean) — 2026-07-06 15:50–16:30

| メトリクス | Run 3 | Run 4 |
|---|---|---|
| 要件 (formalizable) | **83 (72)** ✅ merge修正が効いた | 同左を再利用 |
| モデルゲート | (未実装) | **phase1/拡張とも round 1 通過** ✅ |
| 定理数の推移 | 56 | 48 → **23**(修復が25定理を削除) |
| コンパイル | ❌ | ❌(手動kill) |

### Run 3 の失敗: 決定的スタブ自体のバグ
複数行statement内の `let s' :=` の `:=` を証明開始と誤認して statement を切断、
`let s' := sorry` というゴミを量産(51定理スタブしても収束しない原因)。
→ 修正: 最後の `:= by` でのみスタブ、term証明/破損statementは `-- BROKEN` キル。

### Run 4 の失敗: whole-file LLM修復がスケールしない
48定理+モデルのファイル全体をLLMに書き直させると出力上限で切断され、定理が
silently 消える(48→23)。「定理を削除するな」というプロンプト制約はサイズ限界に勝てない。

### Run 5 に向けた再設計(実装済): per-declaration 修復エンジン
- ファイルを「モデル領域 + 定理ブロック列」に分解、ビルドエラーを行範囲でブロックに帰属
- 失敗定理ごとに決定的エスカレーション: ①該当定理のみの標的LLM修復 → ②sorryスタブ → ③BROKENキル
- whole-file LLM書き直しを全廃。de-vacuationもブロック単位
- ユニットテスト5件(分解/再組立roundtrip、multiline-let保持、term証明キル等)


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
