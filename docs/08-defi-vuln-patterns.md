# DeFi 設計脆弱性パターンと、その Lean 形式検証戦略 — 設計メモ

(調査日 2026-07-08。Apyx に限らず任意の DeFi プロトコルを監査する土台として、①設計/仕様レベルの脆弱性パターンをリンク付きで整理し、②それを Lean で形式検証する際に**最もクリティカルかつ広範囲**な保証を与える方針を提案する。)

## 0. 前提 — 「設計/仕様欠陥」型と「実装バグ」型

reentrancy・overflow・modifier ミス等の**実装バグ**は静的解析・監査で捕捉されるようになり、いま大型損失を占めるのは「**コードは仕様どおりだが、仕様(不変条件)が間違っている/欠けている**」型である。Trail of Bits の *invariant-driven development* の核心的問いは:

> **「この悪状態を禁じている要件はどれか?」— 答えが無ければ、それはバグではなく仕様矛盾。**

DeFi 攻撃の SoK は実インシデント181件・$3.24B、その多くが non-atomic(=不変条件を1つ書いていれば検知できた)と報告する([arXiv 2208.13035](https://arxiv.org/abs/2208.13035))。本メモ Part A はこのパターン群を、Part B はそれを Lean で捉える方針を扱う。

---

# Part A — 設計脆弱性パターン(監査リファレンス)

## A.1 最頻・最大コストのパターン(破られる不変条件付き)

| # | パターン | 破られる不変条件 | 代表事例 |
|---|---|---|---|
| **A** | **オラクル設計欠陥**(最頻・最大) | 評価入力は攻撃者の制御窓(1tx)で**操作耐性**を持つ | spot/single-pool/`get_virtual_price`/誤合成 feed。flash loan で1ブロック撃破 |
| **B** | **シェアインフレ / first-depositor / donation**(ERC4626) | share 価格は**未計上の残高変化で動かない**;実入金が 0 share に丸められない | 空 vault に 1 wei mint→donate。wUSDM |
| **C** | **丸め方向エラー** | 丸めは**常にプロトコル有利** | KyberSwap Elastic $48M(tick 境界の二重丸め) |
| **D** | **会計 / 保存則破壊** | 発行総量 ≤ 裏付け;二重計上なし | mint>backing、liquidity 二重計上 |
| **E** | **状態変更経路の solvency チェック欠落** | 健全性を悪化させうる**全経路**が solvency 表明で終わる | **Euler $197M**(`donateToReserves` が `checkLiquidity` を欠く) |
| **F** | 清算メカニズム設計 | 清算は必ずリスクを減らし人為誘発で利益化しない | self-liquidation、動的割引の利益化 |
| **G** | **無制限パラメータ**(caps/floors/rate-limit 無し) | 経済的に敏感な全パラメータに強制上下限 | Moonwell が 1.65M ETH/token を受理 |
| **H** | 報酬 / emission 会計 | 累計請求 ≤ 累計獲得;accumulator 単調 | Sorra:既配布を引かず再請求 |
| **I** | 金利 / index 単調性 | accrual index は単調・読み取り前に1回だけ更新 | 非単調更新で有利な瞬間を捕捉 |

補助クラス:
- **ガバナンス/鍵**: flash-loan governance(Beanstalk $182M)、0秒 timelock/退出窓なし、多役割結託、upgrade 濫用。
- **合成性(composability)**: read-only reentrancy(mutable な外部 view を信頼:dForce $3.7M)、操作可能な外部状態を feed に、クロスプロトコル donation。

## A.2 アーキタイプ別:守るべき不変条件と破れ方

- **AMM / DEX** — `x·y ≥ k`、tick 会計(境界越えで liquidity 保存)、**mid-block price をオラクルにしない**。破れ:KyberSwap(丸め→保存則破壊)、Curve `get_virtual_price()` を中間状態で読む(dForce)。fee-on-transfer/rebasing/JIT も「未規定の前提」。
- **Lending / CDP** — グローバル `Σ資産 ≥ Σ負債`、各口座 `health ≥ 1` を**全残高変更後に**、清算は必ず bad debt を減らす。破れ:**Euler**(不変条件が1関数だけ欠落=仕様矛盾)、self-liquidation、bad-debt socialization、accrual timing。
- **Vault / yield(ERC4626)** — `convertToShares/Assets` はプロトコル有利丸め、`totalAssets` は**donate 不可分**、round-trip で他者価値を抜けない。Certora Kamino の定式化:`sharesIssued ≤ underlyingAssets` かつ「**どの op も1 share の価値を下げない**」。
- **Stablecoin / redemption** — `C ≥ 1` を mint/redeem で保存、**redemption フロア**、裏付けが自己需要に**反射的に連動しない**。破れ:**Terra/UST の死のスパイラル**=「常に $1 で償還」と「裏付け=償還で価格が下がる LUNA」が stress 下で**両立不能**(Iron Finance も同型)。mint-at-$1 vs redeem-at-market のテンション。
- **Governance / access** — 投票力は**提案前スナップショット**由来、全提案に timelock、**MAY が MUST を破らない**。破れ:Beanstalk の `emergencyCommit`(MAY)が timelock(MUST)を否定。

## A.3 「仕様矛盾」の純粋3型(本ツール `docs/07` のタクソノミーと対応)

設計欠陥は最終的に3つに集約される:

1. **不変条件ギャップ(D3 不完全性)** — 悪状態を禁じる要件が**無い/1経路だけ欠落**。→ Euler。検出法 `docs/07` **M3(悪状態到達 witness)/ M5(被覆解析)**。
2. **許可 vs 義務の矛盾(D1)** — **MAY が MUST を破る**。→ Beanstalk。検出法 **M12**。
3. **実現不能な仕様(D5 unrealizability)** — 2要件が stress 下で**同時に守れない**。→ Terra/UST。検出法 **M1 充足性 / realizability**。

## A.4 具体事例(2023–2025、root cause = 設計)

| プロトコル | 損失 | 仕様レベル根本原因 | リンク |
|---|---|---|---|
| Euler Finance | $197M | 状態変更経路 `donateToReserves` が solvency チェックを欠く | [Cyfrin](https://www.cyfrin.io/blog/how-did-the-euler-finance-hack-happen-hack-analysis) · [Olympix](https://olympixai.medium.com/eulers-197m-collapse-shows-why-invariants-matter-more-than-audits-451da9026e12) |
| KyberSwap Elastic | ~$48M | tick 境界の丸め方向誤り→liquidity 二重計上 | [BlockSec](https://blocksec.com/blog/kyberswap-incident-masterful-exploitation-of-rounding-errors-with-exceedingly-subtle-calculations) |
| dForce | $3.7M | Curve 中間 `get_virtual_price()` を信頼(read-only reentrancy) | [CertiK](https://www.certik.com/resources/blog/1oDd0j4Kx9dfym2vRwvf5Y-curve-conundrum-the-dforce-attack-via-a-read-only-reentrancy-vector-exploit) · [ChainSecurity](https://www.chainsecurity.com/blog/heartbreaks-curve-lp-oracles) |
| wUSDM(ERC4626) | ~$700K | direct-donation で share 価格操作、ガード無し | [OZ inflation](https://www.openzeppelin.com/news/a-novel-defense-against-erc4626-inflation-attacks) |
| Moonwell | 大 | 無制限オラクル(偏差上限なし) | [BlockSec/YieldBlox](https://blocksec.com/blog/yieldblox-dao-incident-on-stellar-oracle-misconfiguration-enabled-a-10m-drain) |
| Sorra Finance | ~$41K | 報酬会計が既配布を引かず再請求 | [Coinmonks](https://medium.com/coinmonks/sorra-finance-staking-exploit-41-000-drained-in-flawed-reward-logic-3771a6efb019) |
| Beanstalk | $182M | flash-loan governance:残高投票 + timelock バイパス | [Immunefi](https://medium.com/immunefi/hack-analysis-beanstalk-governance-attack-april-2022-f42788fc821e) |
| Terra / UST | $40B+ | 「$1 償還」と「反射的裏付け」が stress 下で両立不能 | [arXiv 2207.13914](https://arxiv.org/pdf/2207.13914) · [Richmond Fed](https://www.richmondfed.org/publications/research/economic_brief/2022/eb_22-24) |

## A.5 「最重要の6不変条件」(2023–25 の大型損失の大半をカバー)

1. **オラクル入力は 1tx 操作耐性**を持つ(または被害上限が有界)。
2. **share 価格 / 会計は未計上 donation に不変**。
3. **丸めは常にプロトコル有利**。
4. **全状態変更経路が solvency / 保存則の表明で終わる**。
5. **全経済パラメータに caps / floors / rate-limit**。
6. **ガバナンスは決定と発効を snapshot + timelock で分離**。

## A.6 償還が非同期な DeFi アーキタイプのパターン(J/K/L)

A.1–A.5 は「入金も償還も1トランザクションで原子的に完結する」プロトコルを前提にしている。
**償還が2相に分かれる DeFi プロトコル**はこの前提の外にあり、A.1 の不変条件をすべて証明しても
攻撃面の大半に触れられない。該当するアーキタイプ:

| アーキタイプ | 2相になる理由 | 該当する J/K/L |
|---|---|---|
| **非同期 vault / RWA ファンド**(ERC-7540) | NAV 確定・オフチェーン決済・ガバナンス承認を待つ | J(決済価格)・K(pending 滞留) |
| **LST / LRT の unstaking キュー** | バリデータ退出待ちで FIFO 化する | K(飢餓・占有) |
| **遅延償還ステーブル / 出金キュー付き vault** | 流動性が貯まるまで claim を待たせる | J・K |
| **デルタニュートラル・多拠点運用** | 会計拠点をまたぐ移送に遅延がある | L(意図と実現の乖離) |
| **負債・建て玉を持つ vault** | 純資産が負になりうる | (I15。§B.2 Tier 1.5) |

これらに共通するのは「**償還請求と実際の支払の間に時間が入る**」ことで、そこに3種類の抜け道が開く。
J は待っている間に価格が動くこと、K は前の人が詰まると自分も出られないこと、L は帳簿だけ先に動いて
実際の執行が付いてこないこと。いずれも A.1 の同期型不変条件では原理的に検出できない。

| # | パターン | 破られる不変条件 | 根拠 |
|---|---|---|---|
| **J** | **非同期決済のタイミング選択** | 決済価格は**実行者の裁量で選べない**。request 時と settle 時のプロトコル有利側で評価される | **ERC-7540 が規格の Security Considerations 自身で認めている**: 「`redeem`/`withdraw` で受け取る `assets` は Request 時点の `convertToAssets(shares)` と等しいとは限らない。Pending から Claimed の間に価格が動きうるからである」「最終的な交換レートを Request 時に知りえないため、ユーザーは交換レートの計算と Request の履行についてその実装を**信頼するほかない**」。「コミット後に実行するかどうかを選べる裁量 = 無償のオプション」という経済的対象そのものは [Mazorra–Öz–Schlegel–Wu, *The Free Option Problem of ePBS*](https://arxiv.org/abs/2509.24849) が別ドメインで形式化しており、そこでもボラティリティが高い局面ほど行使確率が跳ね上がると報告されている |
| **K** | **キュー飢餓 / 容量グリーフィング** | 共有キューは**有界コストで占有できない**。先行要求が後続を恒久的にブロックしない | ERC-7540 Security Considerations が「Request のためにロックされた share/asset は **Pending 状態のまま滞留しうる**」と明記。本番設計が実際に境界で防いでいる例として [Lido `WithdrawalQueueERC721`](https://docs.lido.fi/contracts/withdrawal-queue-erc721/) — FIFO キューで、1件あたり最小 `100 wei`・最大 `1000 ETH` を課し、その理由を「極端に大きな request でキューが詰まるのを避けるため」と明示している。飢餓の形そのものは分散システムの [head-of-line blocking](https://en.wikipedia.org/wiki/Head-of-line_blocking) と同型 |
| **L** | **意図 vs 実現の乖離** | 「発注したつもりの状態」と「実現した状態」の差に**強制上界**がある | 分散システムでは [**dual-write problem**](https://docs.aws.amazon.com/prescriptive-guidance/latest/cloud-design-patterns/transactional-outbox.html) として既知の失敗様式 — 「1つの論理操作が2つの異なるシステムに書き込み、片方が失敗すると不整合な状態に入りうる」。オンチェーン会計が先に確定し、実際の反映を外部の実行主体に委ねる設計はこの形。最小実行サイズ未満の指示が黙って捨てられるなど、片側だけが**設計上意図的にスキップされる**場合、収束を強制する仕組みが無ければ差は単調に累積する |

**引用の質(正直な明示)**: 3パターンで**根拠の種類が違う**。J と K は規格(ERC-7540)と本番設計
(Lido)の**一次文献**。L は分散システムの一般クラス(dual-write)としては確立しているが、
**DeFi 固有の公開インシデントは見つかっていない** — 探した範囲で当たったのは実装バグ側の
近縁形(外部呼び出しの戻り値未チェック)と、運用リスクとしてのヘッジ乖離の記述だけである。
K に head-of-line blocking を当てたのと同じく、L も分野横断の構造アンカーで留めてある状態。

なお J/K についても **A.1 には昇格させない**。A.1 は「損失規模でランクした最頻・最大コストの
パターン」であり、J/K の裏付けは規格の Security Considerations と本番設計の防御策であって、
損失規模つきインシデントではない。根拠の種類が違うものを同じ表に混ぜると A.1 のランキングとしての
意味が壊れる。

**Lean 側の対処は3つで共通**: 破れ方はいずれも「時間が状態の一部になっている」形なので
(J は request と settle の間、K はキューが掃ける間、L は指示と反映の間)、**遷移系に時計を
入れる**という一つの拡張が3パターン同時に効く。具体的な定理は Part B.2 Tier 1.5。

なお K と L には分散システム側に確立した呼び名がある(head-of-line blocking / dual-write)。
上表で引いているのは**その構造アンカーとしてであって、DeFi の損失事例としてではない**。
両者の区別は下記のとおり。

---

# Part B — Lean で最もクリティカル&広範囲な保証を与える提案

## B.1 なぜ「閉じた `Op` 型 + 網羅ケース分析」が広範囲保証に最適か

docs2formalspec のモデルは `State` レコード・**閉じた** `Op` 帰納型・`step : State → Op → Address → Option State`。この構造が Part A のパターンに対して固有の強みを持つ:

- **網羅性が定理になる**。`step` が閉じた `Op` 上で定義されるため、不変条件を「全 `op` について保つ」ことを `cases op` の**全枝を証明しないとビルドが通らない**形で示せる。→ **Euler(パターン E)の「1経路だけチェック欠落」は、閉世界網羅では構造的に不可能**。バイトコード fuzzer/symbolic が「標本」で反例を*探す*のに対し、こちらは「無い」を*証明*する。これが最大の広範囲性。
- **トレースレベル帰納**。単発の不変条件を任意長の操作列へ帰納で持ち上げられる(bounded model checking と違い**列長に上限が無い**)。Apyx の `solvency_preserved` / `no_free_value_trace` が実例。
- **敵対者を第一級で表現**。役割集合 `R ⊆ roles` を callers に固定した攻撃列で「被害上限」を定理化(`docs/05` blast-radius)。オラクル/ガバナンスの被害を**定量**できる。
- **公理クリーンな機械検証**(`propext`/`Quot.sound` のみ)。

**トレードオフ(正直に)**: 抽象モデルの証明であって bytecode ではない(model-vs-implementation gap)。よって**設計層の保証**であり、Certora/Halmos/Echidna 等の**実装層**ツールと併用する。再入・flash-loan のクロスプロトコル合成・gas/storage は原理的に範囲外(`docs/06` §4)。→ 役割分担: **本ツールで設計不変条件を全経路証明 → 実装層で bytecode を検証**。

## B.2 コア不変条件ライブラリ(最もクリティカル&広範囲)

Part A の6不変条件のうち、**閉じた `Op` 上で全経路証明でき、かつ複数アーキタイプを横断カバーする**ものを Tier 1 とし、protocol-agnostic な Lean schema にして再利用する。各不変条件は次の2段で証明する:

```
-- 単発(全 op 網羅): Inv を保つ
theorem inv_step (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (hpre : Inv s) : Inv s'
-- トレース帰納: 任意長で保つ
theorem inv_trace (s : State) (σ : List (Op × Address)) (h0 : Inv s)
    (h : ∀ n, WellFormed (execTrace s (σ.take n))) : Inv (execTrace s σ)
```

**Tier 1 — 普遍 safety 不変条件(最優先。Apyx で実証済 → テンプレ化)**

| 不変条件 | 主張 | 捕捉するパターン | Apyx の既存実装 |
|---|---|---|---|
| **I1 保存則 / no-free-value** | 任意アドレスの受領 ≤ 支払 + 初期残高。無から価値は生まれない | A(一部)・D・E | `no_free_value_trace`, `apxUSD_credit_is_backed` |
| **I2 solvency** | `Σ 請求 ≤ Σ 裏付け` を全 step で保存 | **E**・D・Lending/CDP 全般 | `solvency_preserved` |
| **I3 share 価値単調 / 非希釈** | どの op も傍観者の per-share 償還価値を下げない | **B**・Vault 全般 | `no_dilution` |
| **I4 丸めプロトコル有利** | 変換の往復が価値をユーザーにクレジットしない;引出は切上げ | **C** | `rounding_favors_protocol`, `withdrawShares_rounds_up` |
| **I5 donation 免疫** | `totalAssets` / 会計は計上済み op でのみ動く(生 transfer で動かない) | **B の根**・D | `donation_free`, `no_inflation_attack` |

> **コア4 の推奨**: I2(solvency)+ I3/I5(share 価値・donation)+ I4(丸め)を最優先。これだけで **Lending・Vault・AMM・Stablecoin を横断**して Part A の B/C/D/E を覆う(=最も広範囲)。Apyx の `Safety.lean` は既にこの5本を証明済みで、**テンプレ化の worked reference** になる。

**Tier 1.5 — 非同期・多拠点・符号付き価値(パターン J/K/L。`docs/06` §7)**

Tier 1 は「原子的・単一拠点・非負値」の遷移系を前提にしている。その前提が崩れるアーキタイプ
向けの不変条件族で、**遷移系に時計(`Op.tick`)を入れることが前提**になる。設計メモは
[`docs/06-safety-properties.md`](06-safety-properties.md) §7、スキーマは
[`templates/invariants/`](../templates/invariants/)。

| 不変条件 | 主張 | 捕捉するパターン | 状態 |
|---|---|---|---|
| **I10 決済タイミング中立** | request と settle の間の価格移動が、実行タイミングを選べる者に利得を与えない | **J** | スキーマ + 架空モデル実証 |
| **I11 キュー生存性** | 正直ユーザーの pending が有限トレースで claim 可能。反例は witness 化 | **K** | 同上(既定は gap-witness) |
| **I12 in-flight 保存** | 未決済+決済済みの総和が保存。「次ラウンドで未決済は 0」は仮説として明示 | D の非同期版 | スキーマ + 架空モデル実証 |
| **I13 拠点間保存** | Σ(拠点 + 移送中)が内部移送で保存 | D の多拠点版 | スキーマ |
| **I14 乖離上界** | 意図と実現の差に上界。無ければ不在を証明 | **L** | スキーマ(G と同型) |
| **I15 符号付き支払能力** | 純資産が負になるトレースの有無。**`Nat` 台帳では空虚に真になる** | E の符号付き版 | スキーマ |

> **`Nat` 空虚性の罠**: 保有価値を `Nat` で持つモデルは、切り詰め減算のせいで債務超過を
> **そもそも表現できない**。この状態で「支払能力は保存される」を証明しても情報量はゼロである。
> Step 0 プロファイルで「純資産は負になりうるか」を必ず問い、Yes なら台帳を `Int` にすること。
> これは I15 を採らない場合でも独立に成り立つ指摘。

**Tier 2 — パラメータ境界・単調性(パターン G/I)**

- **I6 パラメータ境界**: `redemptionValue`/price/fee/collateral-factor 等に `step` ガードで floor/cap があることを証明。**無ければ、その不在を証明する**(下記 B.3)。
- **I7 単調 accumulator**: 金利 index / exchange rate / reward accumulator が非減少。

**Tier 3 — オラクル/敵対時間(パターン A、最難)**

- **I8 オラクル被害上限**: spot feed の「操作耐性」は**証明できない**(仕様上操作可能)。honest な成果物は「敵対オラクルが抽出できる額 ≤ f(reserve, 設定レンジ)」の**上限定理**(blast-radius T6 型)。Apyx `redeem_payout_has_no_cap` が「上限が存在しない」を witness 付きで示した実例。

**Tier 4 — spec-consistency(パターンの上流、`docs/07`)**

- **I9 要件集合の一貫性/realizability**: 充足性 witness・許可 vs 義務・realizability を**挙動モデル化の前に**チェック。**Beanstalk(MAY vs MUST)・UST(unrealizable)型はここで捕捉**できる(デプロイ前)。

## B.3 「否定して witness」= ギャップ検出(パターン G と E の残余)

安全性を*証明*できないとき、**悪状態の到達可能性を witness 付きで証明する**のが最も説得力ある成果物になる。これは「フロア/キャップの不在」「ある経路の solvency チェック欠落」を**確定的な発見**に変える:

```
theorem gap_witness : ∃ s σ, reachable s σ ∧ BadState (execTrace s σ) ∧ (¬ どの要件も違反していない)
```

Apyx は `redeem_payout_has_no_cap`(払戻上限の不在)・`admin_rfq_coalition_drains`(結託で全損)で実証済み。**「証明できた安全性」と同等に「証明できた脆弱性」を出す**のが本手法の非対称的な強み。

## B.4 被覆マトリクス(パターン → Lean 保証)

| Part A パターン | 主たる Lean 保証 | 手段 |
|---|---|---|
| A オラクル操作 | I8 被害上限 / I2 solvency | Tier 3 + blast-radius |
| B インフレ/donation | **I5 donation 免疫 + I3 非希釈** | Tier 1(証明) |
| C 丸め | **I4 丸めプロトコル有利** | Tier 1(証明) |
| D 会計/保存則 | **I1 保存則 + I2 solvency** | Tier 1(証明) |
| E solvency チェック欠落 | **I2 solvency を全 op 網羅** | Tier 1(**閉世界網羅で構造的に閉じる**) |
| F 清算設計 | I2 + gap witness | Tier 1 + B.3 |
| G 無制限パラメータ | **I6 / gap witness** | Tier 2 + B.3(不在の証明) |
| H 報酬会計 | I1 保存則(reward 版) | Tier 1 |
| I index 単調 | **I7 単調 accumulator** | Tier 2(Apyx 実装済: `exchange_rate_monotone_deposit`〔新規入金は希釈しない〕・`exchange_rate_monotone_creditYield`〔yield credit は不変〕・`req_exchange_rate_non_decreasing`〔時間方向〕) |
| ガバナンス結託 | blast-radius(役割集合)+ I9 realizability | Tier 3/4 |
| 死のスパイラル | **I9 realizability**(挙動前) | Tier 4(`docs/07`) |
| **J 決済タイミング選択** | **I10 決済タイミング中立** | Tier 1.5(時計が前提) |
| **K キュー飢餓/占有** | **I11 キュー生存性** | Tier 1.5(既定は **gap-witness**) |
| **L 意図vs実現の乖離** | **I14 乖離上界** | Tier 1.5 + B.3(不在の証明) |
| 非同期会計の二重計上 | **I12 in-flight 保存 / I13 拠点間保存** | Tier 1.5 |
| 負債込みの債務超過 | **I15 符号付き支払能力** | Tier 1.5(`Int` 台帳が前提) |

## B.5 実装ロードマップと優先順位(criticality × breadth)

優先度 = 「捕捉する損失パターン数 × 平均損失規模 × テンプレ再利用性」で評価する:

1. **`templates/invariants/`(コア4:I2,I3,I5,I4 + I1 + gap-witness)を汎用化 — ✅ 実装済み**([templates/invariants/](../templates/invariants/):README = 記入ガイド、`Invariants.template.lean` = 骨格)。generic な `‹State›/‹Op›/‹step›` に対する schema + Step-0 プロファイル + インスタンス化チェックリスト。Apyx `Safety.lean`/`SpecDefects.lean` を worked reference に。→ **単一の投資で Lending/Vault/AMM/Stablecoin を横断**。最も高い breadth。
2. **gap-witness テンプレ(B.3)** を同梱。安全性が証明できない箇所を「確定した脆弱性」に。特に **I6 無制限パラメータの不在証明**(業界最頻の G を確定発見に)。
3. **blast-radius テンプレ(`docs/05`)** を役割集合パラメトリックに。鍵漏洩・多役割結託(2024-25 最大の損失バケット)を被害上限で定量。
4. **spec-consistency 層(`docs/07`)を監査の第一歩に**。realizability/充足性で Beanstalk/UST 型を**モデル化前に**除外。安価で上流。
5. **オラクル被害上限(I8)** をアーキタイプ別に。「操作耐性は証明できない、上限は出せる」を標準成果物に。
6. **Tier 1.5(I10–I15)を、対象が非同期・多拠点・符号付きのときだけ有効化**。判定は Step 0
   プロファイルの5問(時計 / 二相操作 / in-flight 状態 / 符号付き価値 / 有界共有キュー)で機械的に決まる。
   投資対効果の順は **時計(E1)→ 明示キュー(E4)→ `Int` 台帳(E3)→ 拠点分割(E2)**。最初の2つで
   J/K と `docs/06` §7.3 の S6 開放問題の定式化までが開き、拠点分割だけが重い。

## B.6 監査ワークフローへの組み込み

各プロトコル監査で、生成定理を **4 由来**に分類して `review.json` で区別報告する(トレーサビリティ):
- **要件由来**(第1柱、`model ⊨ requirement`)
- **脅威モデル由来**(blast-radius、鍵漏洩の被害上限)
- **設計不変条件由来**(本 Part B のコア不変条件、全経路証明 or gap witness)
- **spec-consistency 由来**(`docs/07`、要件集合の矛盾/曖昧/不完全)

そして **corpus → Solidity の原典照合(`docs/07` §3.0)を常時適用**し、抽出欠陥(D6)を設計欠陥と峻別する。

## B.7 一行結論

> **最もクリティカルかつ広範囲な一手は、Part A.5 の「6不変条件」のうち閉じた `Op` 上で全経路証明できる I2/I3/I4/I5(コア4)を `templates/invariants/` として汎用化し、証明できない箇所は gap-witness で「確定脆弱性」に変えること。** 閉世界網羅は業界最頻・最大損失の Euler 型(E)を**構造的に**閉じ、コア4は Lending/Vault/AMM/Stablecoin を横断カバーする。その上に blast-radius(鍵/結託)と spec-consistency(realizability、`docs/07`)を重ね、オラクルは被害上限で honest に扱う。Apyx の `Safety.lean`/`BlastRadius.lean`/`SpecDefects.lean` は既にこの3層の worked reference になっている。

---

## 参考文献

**統計・総論**: [Chainalysis 2024](https://www.chainalysis.com/blog/crypto-hacking-stolen-funds-2025/) · [Chainalysis 2025](https://www.chainalysis.com/blog/crypto-hacking-stolen-funds-2026/) · [OpenZeppelin 2024 Rewind](https://www.openzeppelin.com/news/web3-security-auditors-2024-rewind) · [Three Sigma 2024 exploits](https://threesigma.xyz/blog/exploit/2024-defi-exploits-top-vulnerabilities) · [DeFi Attacks SoK (arXiv 2208.13035)](https://arxiv.org/abs/2208.13035) · [DeFi Security SoK (arXiv 2206.11821)](https://arxiv.org/pdf/2206.11821)

**オラクル**: [OZ ERC-4626 exchange-rate risks](https://www.openzeppelin.com/news/erc-4626-tokens-in-defi-exchange-rate-manipulation-risks) · [Cyfrin oracle manipulation](https://www.cyfrin.io/blog/price-oracle-manipulation-attacks-with-examples) · [ChainSecurity Curve LP oracles](https://www.chainsecurity.com/blog/heartbreaks-curve-lp-oracles) · [SecPLF oracle (arXiv 2401.08520)](https://arxiv.org/pdf/2401.08520)

**ERC4626 インフレ/donation**: [OZ novel defense](https://www.openzeppelin.com/news/a-novel-defense-against-erc4626-inflation-attacks) · [OZ ERC4626 docs](https://docs.openzeppelin.com/contracts/5.x/erc4626) · [Euler exchange-rate manipulation](https://www.euler.finance/blog/exchange-rate-manipulation-in-erc4626-vaults) · [Solodit donation checklist](https://checkwithhans.substack.com/p/solodit-checklist-explained-3-donation)

**非同期決済・キュー(A.6 / Tier 1.5)**: [ERC-7540 Asynchronous ERC-4626 Tokenized Vaults](https://eips.ethereum.org/EIPS/eip-7540)(規格本体の Security Considerations が J と K の一次根拠) · [The Free Option Problem of ePBS (arXiv 2509.24849)](https://arxiv.org/abs/2509.24849)(コミット後の実行裁量 = 無償オプションの形式化) · [Lido WithdrawalQueueERC721 docs](https://docs.lido.fi/contracts/withdrawal-queue-erc721/)(FIFO + 1件あたり最小/最大額という本番の防御策) · [head-of-line blocking](https://en.wikipedia.org/wiki/Head-of-line_blocking)(K の飢餓の形) · [AWS Prescriptive Guidance — transactional outbox / dual-write problem](https://docs.aws.amazon.com/prescriptive-guidance/latest/cloud-design-patterns/transactional-outbox.html)(L の構造アンカー)

**不変条件・形式検証**: [Trail of Bits — invariant-driven development](https://blog.trailofbits.com/2025/02/12/the-call-for-invariant-driven-development/) · [ToB reusable properties](https://blog.trailofbits.com/2023/02/27/reusable-properties-ethereum-contracts-echidna/) · [Certora — securing Kamino](https://www.certora.com/blog/securing-kamino-lending) · [Certora — stopping DeFi bugs at scale](https://medium.com/certora/stopping-defi-bugs-at-scale-6e3fba22dd3d) · [Certora CVL invariants](https://docs.certora.com/en/latest/docs/cvl/invariants.html)

**事例**: [Euler (Cyfrin)](https://www.cyfrin.io/blog/how-did-the-euler-finance-hack-happen-hack-analysis) · [KyberSwap (BlockSec)](https://blocksec.com/blog/kyberswap-incident-masterful-exploitation-of-rounding-errors-with-exceedingly-subtle-calculations) · [dForce (CertiK)](https://www.certik.com/resources/blog/1oDd0j4Kx9dfym2vRwvf5Y-curve-conundrum-the-dforce-attack-via-a-read-only-reentrancy-vector-exploit) · [Beanstalk (Immunefi)](https://medium.com/immunefi/hack-analysis-beanstalk-governance-attack-april-2022-f42788fc821e) · [Sorra (Coinmonks)](https://medium.com/coinmonks/sorra-finance-staking-exploit-41-000-drained-in-flawed-reward-logic-3771a6efb019) · [Terra/UST (arXiv 2207.13914)](https://arxiv.org/pdf/2207.13914) · [Staking-reward defects (arXiv 2601.05827)](https://arxiv.org/pdf/2601.05827)
