# 類似研究サーベイ: NLドキュメント → RFC2119スペック → 形式検証 (Lean 4)

(調査日 2026-07-06、Web調査 ~30クエリ。docs2formalspec の設計根拠)

**結論: 「任意のdoc URL → RFC2119規範スペック文書 → コンパイル可能なLean 4形式化」のフルパイプラインを出荷した既存ツールは存在しない。** 各セグメントは個別に実証済みで、その合成がこのツールの新規性。

## 1. NL → 形式スペック生成 (autoformalization)

- **nl2spec** (CISPA/Stanford 2023, [arXiv:2303.04864](https://arxiv.org/abs/2303.04864)): NL→LTL。サブ翻訳(部分式↔NL断片の対応)で人間が検査・修正可能に。教訓: 曖昧性は対応付けの可視化で扱う。
- **SpecGen** (ICSE 2025, [arXiv:2401.08807](https://arxiv.org/abs/2401.08807)): LLMでJMLスペック生成。検証器フィードバック対話 + 失敗スペックへの4種の変異オペレータ。Java基準で~60%。
- **Clover** (Stanford, [arXiv:2310.17807](https://arxiv.org/abs/2310.17807)): コード/docstring/形式注釈の3者**整合性チェック**(6方向ペアワイズ)。87%受理・偽陽性ゼロ。→ 我々のStage 4(ラウンドトリップ整合ゲート)の根拠。
- **DafnyBench** ([arXiv:2406.08467](https://arxiv.org/abs/2406.08467)): 750+ Dafnyプログラム。**検証器エラーメッセージのリトライループで成功率が向上**が定量実証。
- **nl2postcond** (FSE 2024, [arXiv:2310.01831](https://arxiv.org/abs/2310.01831)): 正しさ + **弁別力**(バグ識別能力)メトリクス。生成postconditionがDefects4Jの64バグを検出。→ 生成Lean性質の評価指標の参考。
- **AutoSpec** (CAV 2024, [arXiv:2404.00762](https://arxiv.org/pdf/2404.00762)): LLM+静的解析+検証器ループでACSL生成、79%検証成功。ラウンド毎の候補検証でエラー蓄積を防止。
- **LeanDojo/ReProver** (NeurIPS 2023, [arXiv:2306.15626](https://arxiv.org/abs/2306.15626)): LLM↔Lean相互作用の事実上の標準インフラ(MIT)。
- **Draft, Sketch, and Prove** (ICLR 2023, [arXiv:2210.12283](https://arxiv.org/abs/2210.12283)): 非形式証明→形式スケッチ→自動証明器。**人間可読な中間産物を挟む段階的形式化** = RFC2119文書を「スケッチ」として挟む我々の構成の理論的先行。
- **AlphaProof** (DeepMind, [Nature 2025](https://www.nature.com/articles/s41586-025-09833-y)): ~80M NL文の一括autoformalization + 検証器フィルタが機能する証拠。
- **Verina** (UCB, ICLR 2026, [arXiv:2505.23135](https://arxiv.org/abs/2505.23135)): NL→Lean4 コード+スペック+証明の189タスク。最良モデルでスペック健全完全 51%、証明 pass@1 **3.6%**(64回のコンパイラフィードバックで22.2%)。→ **「statementがコンパイルする」を出荷保証にし、証明はsorry許容+オプショナルパス**という我々のスコープ設定の定量根拠。
- Gupte et al. 2025 ([arXiv:2511.11829](https://arxiv.org/pdf/2511.11829)): NL要件→命題Lean4。FVEL ([arXiv:2406.14408](https://arxiv.org/abs/2406.14408))、FormL4 ([arXiv:2406.06555](https://arxiv.org/pdf/2406.06555))、航空宇宙要件→LTL ([arXiv:2604.21715](https://arxiv.org/pdf/2604.21715))、RE×LLM展望 ([arXiv:2507.14330](https://arxiv.org/html/2507.14330v1))。

## 2. RFC2119要件抽出

- **RFCNLP** (IEEE S&P 2022, [PDF](https://cnitarot.github.io/papers/rfcnlp_sp2022.pdf)): RFCから規範文タグ付け→FSM抽出→攻撃合成。教訓: 汎用NLPは技術文書で失敗、ドメイン適応必須。
- **PROSPER** (HotNets 2023, [PDF](https://conferences.sigcomm.org/hotnets/2023/papers/hotnets23_sharma.pdf)): LLMがRFC散文で古典NLPに勝つ実証。
- **SPECA** ([arXiv:2602.07513](https://arxiv.org/pdf/2602.07513)): スペック文書→**RFC2119規範要件のチェックリスト(トレーサビリティID+出典位置付き)**→実装監査。我々の抽出ステージに最も近い公開研究(※本ツールの統合先レポジトリ)。形式検証コードまでは出力しない。
- パーサ検証向けRFC解釈 ([arXiv:2504.18050](https://arxiv.org/pdf/2504.18050)): 出典文まで遡れる抽出(provenanceパターン)。
- **Kiro** (AWS 2025, [docs](https://kiro.dev/docs/specs/feature-specs/)): EARS記法の requirements.md 生成 + neuro-symbolic整合チェック。**制約構文でLLM出力を縛る**産業前例。
- RE×LLM系統的レビュー ([arXiv:2509.11446](https://arxiv.org/abs/2509.11446), [arXiv:2409.06741](https://arxiv.org/pdf/2409.06741))。単体の「RFC2119抽出器」OSSは存在しない — 本ツールが埋めるギャップ。

## 3. DeFi / スマートコントラクトのスペック形式化

- **PropertyGPT** (NDSS 2025 Distinguished Paper, [arXiv:2405.02580](https://arxiv.org/abs/2405.02580)): Certora監査23案件の**623人手CVL性質をRAG**し新性質を生成、コンパイル/静的解析フィードバックで修正。recall 80%、ゼロデイ12件。→ 盗むべき技法: 既存形式性質コーパスのRAG。
- **Certora AIComposer** ([GitHub](https://github.com/Certora/AIComposer)): ドキュメント+CVLスペック→検証済み実装(prover-in-the-loop)。方向は逆(spec→code)だが production 品質のループ実装。
- **Runtime Verification / K**: KEVM、MakerDAO MCD検証、Clockwork Finance。スペックは形式的かつ実行可能だが人手。
- **Nethermind Clear / EVMYulLean** ([Clear](https://github.com/NethermindEth/Clear), [EVMYulLean](https://github.com/NethermindEth/EVMYulLean)): Yul/EVMのLean 4意味論(Ethereumテスト99.99%通過)。**Lean 4がEVM隣接スペックのターゲットとして実用的である最良の証拠**。
- **Lean 4 AMM形式化** ([arXiv:2402.06064](https://arxiv.org/abs/2402.06064), [arXiv:2602.00101](https://arxiv.org/html/2602.00101)): state record + 操作関数 + 不変条件定理という**DeFi形式化のLean 4イディオムの模範**。few-shot例の供給源。MEV ([arXiv:2510.14480](https://arxiv.org/pdf/2510.14480))。
- Ethereum Lean Consensus: FOCIL in Lean 4 ([ethresear.ch](https://ethresear.ch/t/formalizing-focil-in-lean-4/24950))、SizzLean、[leanroadmap.org](https://leanroadmap.org/)。
- **AWS Cedar** ([lean-lang.org/use-cases/cedar](https://lean-lang.org/use-cases/cedar/)): Leanモデル+実装への差分テスト(verification-guided development)の産業実証。
- **Verso** ([GitHub](https://github.com/leanprover/verso)): Lean FROの文書オーサリング基盤。RFC2119散文とLeanコードを単一のビルド検査付き文書に同居可能 — 将来の出力形式候補。

## 4. コンパイラフィードバック自己修復ループ

- **PALM** (ASE 2024, [arXiv:2409.14274](https://arxiv.org/abs/2409.14274)): 生成→決定的修復→バックトラック。**LLMは構造を当て詳細を外す**ので、LLM再呼び出しの前に安価な決定的修復を挟む。
- **LeanAgent** ([arXiv:2410.06209](https://arxiv.org/abs/2410.06209)): 新規Leanレポジトリへの継続適応。
- **miniCTX** (CMU, [arXiv:2408.03350](https://arxiv.org/html/2408.03350v2)): **ファイル内コンテキストが決定的**(35.9% vs 19.5%)。生成スペックファイルは新規定義だらけなので、修復時は常に全ファイルを渡す(我々のrepairは全ファイル渡し — 正解)。
- **Pantograph** ([GitHub](https://github.com/leanprover/Pantograph)) / **lean-lsp-mcp** ([GitHub](https://github.com/oOo0oOo/lean-lsp-mcp)): tactic粒度のLean対話基盤。lake buildより細粒度が要る時の選択肢。
- **Goedel-Prover-V2** (8B/32B, [arXiv:2508.03613](https://arxiv.org/pdf/2508.03613)): 最良のローカル実行可能Lean証明器。コンパイラエラーからの自己修正を学習済み。→ 証明ディスチャージ専用パスの候補。APOLLO ([arXiv:2505.05758](https://arxiv.org/html/2505.05758v5))。
- ループの価値の収束的証拠: DafnyBench / Verina (3.6%→22.2%) / SpecGen / AutoSpec / PropertyGPT。**ループは品質の主要源泉であり省略不可**。

## 5. 最近傍OSSツール比較

| ツール | カバー範囲 |
|---|---|
| Kiro (AWS, 商用) | prompt/codebase → EARS requirements.md |
| SPECA | スペック文書 → RFC2119チェックリスト(traceability付) |
| Certora AIComposer | doc+CVL → 検証済み実装 |
| PropertyGPT | code+性質コーパス → CVL性質 |
| LeanAide ([GitHub](https://github.com/siddhartha-gadgil/LeanAide)) | NL数学文 → Lean 4 statement |
| llm-formal ([GitHub](https://github.com/yuzhoumao/llm-formal)) | NLプロトコル記述 → TLA+ |
| lean-lsp-mcp | Lean 4 コンパイル/診断ループ (MCP) |

## 設計への反映(採用決定)

1. **Provenance必須** (SPECA): 全要件に REQ-ID + source_anchor。Lean定理docstringにRFC2119文を埋め、双方向トレーサビリティ。
2. **EARS風制約構文** (Kiro): 「WHEN <trigger>, the <actor> MUST <behavior>」テンプレートを抽出JSONに強制 → Lean化が容易に。
3. **ドメインモデル先行** (miniCTX/AMM形式化): 要件を1件ずつ孤立定理化せず、まず State/操作関数のLeanドメインモデルを合成し、次に REQ→theorem マッピング。
4. **スコープ**: 出荷保証は「statementコンパイル」。証明は cheap tactics (simp/omega/decide) → sorry 許容 → 将来 Goedel-Prover-V2 パス。
5. **修復ループ** ≤ N ラウンド、全ファイルコンテキスト、失敗宣言のみ再生成(将来最適化)。
6. **Clover風ラウンドトリップゲート**: Lean定理を逆informalizeして元のRFC2119文とLLM判定比較、不一致をフラグ。
7. **将来**: AMM論文コード等のLean DeFi形式化コーパスをfew-shot/RAGに、Verso出力、Pantograph化。
