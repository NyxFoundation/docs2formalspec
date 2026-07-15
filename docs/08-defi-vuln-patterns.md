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

## B.5 実装ロードマップと優先順位(criticality × breadth)

優先度 = 「捕捉する損失パターン数 × 平均損失規模 × テンプレ再利用性」で評価する:

1. **`templates/invariants/`(コア4:I2,I3,I5,I4 + I1 + gap-witness)を汎用化 — ✅ 実装済み**([templates/invariants/](../templates/invariants/):README = 記入ガイド、`Invariants.template.lean` = 骨格)。generic な `‹State›/‹Op›/‹step›` に対する schema + Step-0 プロファイル + インスタンス化チェックリスト。Apyx `Safety.lean`/`SpecDefects.lean` を worked reference に。→ **単一の投資で Lending/Vault/AMM/Stablecoin を横断**。最も高い breadth。
2. **gap-witness テンプレ(B.3)** を同梱。安全性が証明できない箇所を「確定した脆弱性」に。特に **I6 無制限パラメータの不在証明**(業界最頻の G を確定発見に)。
3. **blast-radius テンプレ(`docs/05`)** を役割集合パラメトリックに。鍵漏洩・多役割結託(2024-25 最大の損失バケット)を被害上限で定量。
4. **spec-consistency 層(`docs/07`)を監査の第一歩に**。realizability/充足性で Beanstalk/UST 型を**モデル化前に**除外。安価で上流。
5. **オラクル被害上限(I8)** をアーキタイプ別に。「操作耐性は証明できない、上限は出せる」を標準成果物に。

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

**不変条件・形式検証**: [Trail of Bits — invariant-driven development](https://blog.trailofbits.com/2025/02/12/the-call-for-invariant-driven-development/) · [ToB reusable properties](https://blog.trailofbits.com/2023/02/27/reusable-properties-ethereum-contracts-echidna/) · [Certora — securing Kamino](https://www.certora.com/blog/securing-kamino-lending) · [Certora — stopping DeFi bugs at scale](https://medium.com/certora/stopping-defi-bugs-at-scale-6e3fba22dd3d) · [Certora CVL invariants](https://docs.certora.com/en/latest/docs/cvl/invariants.html)

**事例**: [Euler (Cyfrin)](https://www.cyfrin.io/blog/how-did-the-euler-finance-hack-happen-hack-analysis) · [KyberSwap (BlockSec)](https://blocksec.com/blog/kyberswap-incident-masterful-exploitation-of-rounding-errors-with-exceedingly-subtle-calculations) · [dForce (CertiK)](https://www.certik.com/resources/blog/1oDd0j4Kx9dfym2vRwvf5Y-curve-conundrum-the-dforce-attack-via-a-read-only-reentrancy-vector-exploit) · [Beanstalk (Immunefi)](https://medium.com/immunefi/hack-analysis-beanstalk-governance-attack-april-2022-f42788fc821e) · [Sorra (Coinmonks)](https://medium.com/coinmonks/sorra-finance-staking-exploit-41-000-drained-in-flawed-reward-logic-3771a6efb019) · [Terra/UST (arXiv 2207.13914)](https://arxiv.org/pdf/2207.13914) · [Staking-reward defects (arXiv 2601.05827)](https://arxiv.org/pdf/2601.05827)
