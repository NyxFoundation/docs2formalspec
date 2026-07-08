# 設計エッジの効いた機関 DeFi — 形式検証の重点候補リスト

(2026-07-08。機関投資家が2026年に使う DeFi のうち、**設計そのものにエッジ(新規性・攻めた機構)がある**ものを、docs2formalspec の適用先として優先順位付けしたリスト。「設計エッジ」= 標準的な過剰担保レンディングではなく、**リスクが新規の機構そのものに宿る**プロトコル。これが設計層の形式検証(本ツールの強み)で最も価値が出る領域。分類は docs/08 の DeFi 脆弱性パターン A–I / コア不変条件 I1–I9 に対応。)

## 選定基準

「エッジが効いている」= 次のいずれかを持つ:
- **新規の担保/裏付け機構**(合成・デルタニュートラル・無担保・リハイポセケーション)で solvency が自明でない。
- **realizability が非自明**(「常に $1」+「裏付けは市場依存」を同時に満たせるか = Terra/Beanstalk 型)。
- **境界のない/floor のない経済パラメータ**(gap-witness で確定脆弱性を出せる)。
- **既に設計ストレス事象**(de-peg・清算失敗・強制 exit)を起こしている。
- **公開ソース**があり bytecode 照合まで通せる(permissionless + OSS が理想)。

各候補の「なぜ Lean/本ツール向きか」を明記。数値は mid-2026 スナップショットの桁感。**engaging 前に現行パラメータを必ず再確認**。

---

## Tier S — 最も設計エッジが効いている(最優先候補)

### S1. Ethena USDe / sUSDe — 合成ドル(デルタニュートラル)
- **設計エッジ**: 裏付けが担保ではなく **long ステーク ETH/BTC + 短 perp 先物のベーシス取引**。solvency が **funding rate が非負であり続けること**と**オフチェーン CEX/カストディ相手方(短脚)**に依存。TVL はピーク ~$14.8B → funding 低下と Pendle/Aave のレバレッジループ巻き戻しで >50% 縮小した実績 = 生きたストレス例。
- **FV ターゲット**: **realizability(D5)** — 「1 USDe = $1」+「裏付け = funding 依存ヘッジ」がストレス下で同時充足不能になる条件を gap-witness 化 / オラクル(A)/ 保険基金の充足性(I2)。
- **公開性**: USDe/sUSDe は permissionless・OSS(iUSDe 機関版は許可制)。→ **理想的な適用先**。
- **本ツール適合**: Terra 型を「不変条件の到達不能悪状態」として構造的に検証する柱3/柱4 が直撃。

### S2. リステーキング(EigenLayer / Symbiotic / Ether.fi)
- **設計エッジ**: ステーク ETH を**複数 AVS に再担保(rehypothecation)**し、slashing 条件を **AVS 側が自由定義**。EigenLayer ~$15B(リステーキング ~94%)。段階的 slashing・operator-set 信頼・出金キューが新規で自明でない。
- **FV ターゲット**: **slashing 合成の健全性**(複数 AVS 同時 slash で担保が枯渇しないか)/ operator 信頼仮定 / **LRT の share↔asset 償還不変条件(I3 非希釈・I7 単調)** / 出金キュー活性。
- **公開性**: permissionless・OSS。Symbiotic はよりモジュラー。→ 適用可。
- **本ツール適合**: 「どの operator 集合の結託で担保がいくら失われるか」= 柱2 blast-radius がそのまま効く。

### S3. 無担保オンチェーン信用(3Jane 等)
- **設計エッジ**: **無担保** USDC 与信枠を、オフチェーン信用データ(Plaid)+ **zkTLS 証明**+ 信用アルゴリズムで発行。担保不変条件が**存在しない**という最もエッジな設計。Paradigm 主導・初期段階。
- **FV ターゲット**: 与信上限・デフォルト分配の会計保存則(I1/D)/ zkTLS 証明の前提 / **境界のないパラメータ(G)**。
- **公開性**: 初期・要確認。novel-risk が高い分、設計層の検証価値は最大級。

### S4. Usual USD0 / USD0++ — ボンド型利回りステーブル
- **設計エッジ**: T-bill(USYC/M0)裏付けの USD0 に対し **USD0++ はボンド化した利回り版**で、**早期償還フロア**を巡る設計が **2025年1月に de-peg** を起こした実績(floor 変更で市場価格が乖離)。~$1.7B ピーク。
- **FV ターゲット**: **floor/redemption 機構の gap-witness(G)**(まさに Apyx の `redemption_has_no_floor` と同型)/ ボンド満期会計(I1)/ USUAL 報酬希釈(I3)。
- **公開性**: permissionless・OSS。→ **Apyx と最も学びが転用できる**。

---

## Tier A — エッジが効いており公開性も良い(高適合)

### A1. Hyperliquid — オンチェーン perp + HLP 金庫
- **設計エッジ**: 独自 L1(HyperCore、~200k orders/sec)上のオーダーブック perp、~70% シェア。**HLP(自動マーケットメイク金庫)が損失を被る**設計で、2025年に大口ポジション清算(JELLY 事案)で金庫が損失リスクに晒され介入が入った = 生きた清算エンジンのストレス例。
- **FV ターゲット**: **証拠金・清算エンジンの solvency(I2/F)**/ 保険・HLP 金庫の充足性 / オラクル遅延・操作(A)/ ソケット/清算インセンティブ算術。
- **公開性**: L1 独自だがロジック公開。清算設計は最重要 FV ターゲット。

### A2. Pendle — 利回りトークン化(PT / YT)
- **設計エッジ**: 利回り資産を **元本トークン PT と利回りトークン YT に分離**。Ethena/Aave と組んだ **PT レバレッジループ**が systemic なリフレクシビティを生む(S1 の巻き戻しの震源)。
- **FV ターゲット**: PT/YT 満期での価値保存(I1)/ AMM 価格式の丸め(C/I4)/ ループ合成の feature-interaction 矛盾(D1c)。
- **公開性**: permissionless・OSS。

### A3. Aave v4 — Hub-and-Spoke + 新清算エンジン
- **設計エッジ**: リスクプレミアム・**再設計した清算エンジン**・オンチェーンレポ市場を狙う Hub-and-Spoke。GHO(ネイティブステーブル)・Horizon(許可制 RWA 市場)。新機構ゆえ清算・隔離設計が未検証。
- **FV ターゲット**: **solvency(Σsupply ≥ Σborrow+reserve, I2)**/ 清算の bad-debt 上限(F)/ 隔離市場封じ込め / RWA NAV オラクル(A)/ pause/whitelist 管理鍵(柱2)。
- **公開性**: OSS。規模最大(DeFi TVL の ~29%)ゆえ影響も最大。

### A4. Morpho Blue — 不変・最小レンディングプリミティブ + curator
- **設計エッジ**: 逆方向のエッジ = **不変(immutable)・permissionless の最小プリミティブ**にリスクを削ぎ落とし、**curator の金庫**に risk を寄せる。~$7–13B、Coinbase の USDC レンディング基盤。
- **FV ターゲット**: プリミティブの隔離市場会計・清算(I2/F、証明しやすい)/ **curator 金庫のロール・配分権限(柱2 blast-radius)**。
- **公開性**: 不変・公開ソース。→ **最短で通せる理想的な最初の外部適用先**(bytecode 照合まで現実的)。

---

## Tier B — 機関中核だが設計は比較的成熟(横展開・比較用)

- **Sky sUSDS / Spark**: RWA 担保 + 貯蓄レート。成熟(Maker 系譜)だが RWA counterparty・freeze 権限が設計面。I2/D。
- **LST(Lido stETH / Ether.fi)**: rebase・償還の **share↔asset 整合(ERC4626 型、I3/I7)**。Apyx の apyUSD accumulator と同型。
- **RWA 償還トークン(BUIDL / USYC / OUSG 型)**: **Apyx と最も同型**(償還機構・NAV オラクル・**凍結/管理鍵**)。許可制でも設計層(柱1+柱2+柱3)は監査可。
- **Ondo Global Markets**: トークン化株式の **on-chain↔off-chain equity ブリッジ**の mint/redeem 設計。

---

## docs/08 パターン × 候補 マトリクス

| 候補 | 主パターン(docs/08) | 中核不変条件 | gap-witness 見込み |
|---|---|---|---|
| Ethena (S1) | A オラクル / D5 realizability | I2 solvency / 保険基金 | ○(ストレス下 de-peg) |
| リステーキング (S2) | 独自 slashing / B 希釈 | I3 非希釈 / I7 単調 | △(slash 合成) |
| 無担保信用 (S3) | 会計 D / G 境界 | I1 保存則 | ◎(担保不変条件なし) |
| Usual USD0++ (S4) | G 境界(floor) | I1 満期会計 | ◎(floor 欠如=Apyx 同型) |
| Hyperliquid (A1) | F 清算 / A オラクル | I2 証拠金 solvency | ○(金庫充足) |
| Pendle (A2) | C 丸め / D1c 合成 | I1 保存則 | △(ループ相互作用) |
| Aave v4 (A3) | F 清算 / A オラクル | I2 solvency | ○(bad-debt 上限) |
| Morpho Blue (A4) | F 清算(封じ込め) | I2 solvency | △(curator 権限=柱2) |

## 適用の優先順位(推奨)

1. **Morpho Blue** — 不変・公開・会計明快。**最短で外部プロトコル初適用**を通し runbook(docs/09)を実証。
2. **Usual USD0++** または **RWA 償還トークン** — **Apyx の gap-witness/blast-radius がそのまま転用**でき費用対効果が高い。
3. **Ethena** — realizability(D5)の旗艦事例。柱4 の価値を最も鮮明に示せる。
4. **リステーキング** — 柱2 blast-radius(operator 結託の被害上限)の応用として novel。

> 注: 許可制(BUIDL/USYC/Maple/Horizon)もコントラクトは検証済みが多く、設計層(柱1–3)は監査可能。最も価値が高いのは公開データの薄い**管理鍵/multisig・オフチェーン与信・カストディ**の on-chain 表現部分。

## 主要ソース

RWA.xyz / DeFiLlama / Messari、Ethena(ethena.fi, Q1 2026 report)、EigenLayer・Symbiotic・Ether.fi 集計、Usual(usual.money)、Hyperliquid(defillama.com/perps)、Aave(aave.com/blog Horizon・2025 recap・v4)、Morpho(“The Morpho Effect 2025”)、Pendle docs、RedStone Tokenization 2026 report。詳細な調査ログは会話履歴の research エージェント2件を参照。
