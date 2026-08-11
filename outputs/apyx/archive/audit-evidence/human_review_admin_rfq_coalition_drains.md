# 人間査読報告: `admin_rfq_coalition_drains`

- **対象**: `Apyx.admin_rfq_coalition_drains`(`D2fsSpecs/BlastRadius.lean:2646-2700`、T10 witness 定理、mainTheorem)
- **査読日**: 2026-07-12
- **査読方法**: Lean Atlas 人間査読フィルターの CLI 再現(後述)
- **判定**: **perfect 昇格は保留 — `confidence high` に留める**

## 判定要旨

定理は Lean モデルに対する主張としては真で、機械検証は健全(`lake build` 通過、sorry なし、公理は `propext` / `Quot.sound` / `Classical.choice` の標準 3 つのみ)。しかし mainTheorem として掲げる「プロトコルの唯一の構造的全損経路」という主張は、原典文書(corpus.md / model.md / SPEC.md)と食い違うモデル簡略化 3 点に依存しており、その注記が定理の docstring / formalMeta に一切ないため承認しない。

## 査読方法(CLI での人間査読フィルター再現)

Web ビューワーの「人間検証対象のみ表示」(typeReachableOnly) と同一ロジックを Python スクリプトで再現し、`lake exe atlas graph-data --no-cache` で再生成した graph.json に適用した:

1. シンク定理から `node.dependencies`(全依存)を推移的に辿り閉包を取る
2. 閉包内の mainTheorem を種とする
3. 証明本体エッジ(`theorem_value_to_definition` / `theorem_value_to_theorem`)を**除外**したエッジのみで到達可能集合を計算する

結果は **検証対象 73 ノード**(定理 1 + 定義 72)。証明専用補題(`rfq_payout_formula`、`step_catastrophicBackstop_forward` 等)は正しく除外された(機械検証済みのため人間査読対象外)。73 ノードのうち定理の真偽に負荷がかかるのは `State`(+射影)、`Op`、`step` の該当 2 分岐、`burnApxUSD`、`ray` で、残りは `step` の他分岐由来のヘルパー(vesting 系等)であることを確認した。

## 所見(重大度順)

### F1(重大・忠実性): RFQ 実行にユーザーの依頼がモデル化されていない

corpus.md:381 は「Users may submit redemption requests … allowing approved counterparties to provide competitive execution」、SPEC.md の REQ-rfq-redemption-allowed も「execute **those** requests」と、counterparty が執行するのは*ユーザーが提出した依頼*である。ところが `step` の `executeRFQRedemption` 分岐(`D2fsSpecs/Apyx.lean:706`)は counterparty が `(user, amount)` を一方的に指定でき、依頼レジストリも同意チェックも存在しない(分岐冒頭のコメント自身が "execute a user's redemption request" と書きながら、依頼の検査がない)。

本定理の全損経路は「被害者が何もしていないのに焼却される」ことに依存する。文書忠実なモデルでは、主張は「未執行の RFQ 依頼を持つユーザーは執行時点の暴落価格を適用される」という、実在するがより狭いリスクに縮小する。

### F2(重大・忠実性): `catastrophicBackstop` の権限・効果が文書と乖離

- **権限**: model.md:71 のガードは「Governance emergency flag set」。Lean 版(`D2fsSpecs/Apyx.lean:731`)は admin 単独トリガーで、emergencyFlag は自分で立てる。corpus はトリガー権限を無指定。「{admin, RFQ} の 2 鍵で足りる」という headline は、この敵対的に最も広い解釈(admin 単独・無条件)に立脚している。
- **補償脚の省略**: corpus.md:375 は「the entire reserve, buffer included, is distributed pro-rata to remaining holders」と補償を明記するが、Lean 版は pro-rata 分配を省略。「uncompensated」が非空リザーブ構成でも成立するのはこの省略の産物。
- **単位跨ぎの直代入**: `redemptionValue := totalCollateralValue` は単位を跨ぐ(`overcollateralizationBuffer` の定義 `D2fsSpecs/Apyx.lean:237` から tCV はトークン数量単位、redemptionValue は ray/token)。完全に solvent な状態(例: tCV = supply = 100)でも backstop 後の価格は 100/10²⁷ ≈ 0 になり、モデルの backstop は solvency と無関係な価格破壊 op になっている。witness は tCV = 0 なので両解釈が一致する領域にあり、定理自体は救われる。

パイプラインの過去レビュー(review_run1–3)も `catastrophic-backstop` / `rfq-redemption-allowed` をともに "partial" と全会一致で判定しており、F1・F2 と整合する。

### F3(中・witness 品質): witness が非 well-formed で、docstring の反実仮想が偽

`coalWitness`(`D2fsSpecs/BlastRadius.lean:2638`)は:

- `apxUSDBal victim = 100` なのに `totalSupply_apxUSD = 0` — 台帳不整合で到達不能な状態
- `usdcReserve = 0`、victim は非 whitelist(`default` 由来)

docstring の「the victim could redeem 100 apxUSD for 100 USDC」は witness 上では偽 — `redeemApxUSD`(`D2fsSpecs/Apyx.lean:584`)は whitelist ガードとリザーブガードの両方で失敗する。また model.md:68 が要求する `whitelist[user]` ガードは Lean の RFQ 分岐に存在せず、文書忠実なら現 witness の第 2 step 自体が失敗する(victim を whitelist すれば直るため、真偽でなく忠実性の問題)。

**修正案**: witness に `totalSupply_apxUSD := 100`、`usdcReserve := 100`、`whitelist := (· = 0)` を追加する。∃ 文なので**声明は不変**、証明の微修正のみ。reserve = 100 なら「価値がリザーブに残っているのに被害者は 0 を受け取る」というより鋭い形になり、反実仮想も真になる。

### F4(軽微・表現): formalMeta summary の "requiring two colluding roles"

本定理が証明するのは結託の**十分性**のみで、必要性(単独鍵では抽出 0)は `single_key_bounds` が担う。summary の "requiring" は過大表現。

## 良い点

- 声明は自己完結の存在証言で、7 つの条件(`0 < amount`、事前残高 = amount、事前・事後 USDC = 0、事前価格 ≥ ray、counterparty 承認、両 step 成功、事後残高 0)はすべて意図どおりに配置されている。
- `step` の該当 2 分岐と witness の手計算追跡は証明と一致した。
- 「モデル内の主張」としての品質は高く、`confidence high` 相当の信頼性は十分にある。

## 昇格の前提となる推奨アクション

1. F3 の witness 修正(声明不変)
2. docstring / formalMeta に前提を明示する: RFQ 依頼はモデル外、backstop は admin 単独トリガー仮定、pro-rata 分配は省略
3. その上で再査読 → perfect 昇格

---

# 再査読報告(2026-07-30、モデルによる査読フィルター再現)

- **査読者**: Claude(モデルによる再現査読 — 人間の最終確認を置換するものではない)
- **対象**: `Apyx.admin_rfq_coalition_drains_funded`(新設の資金付き変種)と、推奨アクション 1–2 の適用状況
- **方法**: Lean Atlas ツーリングは撤去済みのため graph 抽出は再現せず、同等の人手手順で実施 —
  声明の連言の逐条読解、witness の手計算追跡、docstring の主張と Lean 本文の突合、公理検査
- **公理**: `propext` / `Quot.sound` のみ(初回査読時の 3 つより少なく、`Classical.choice` 不要)

## アクション適用の判定

**アクション 1(F3)— 適用済み、ただし修正案の文字通りの形は現行モデルで不成立と判明。**
初回査読後に backstop の pro-rata 補償脚がモデル化された(F2 対応のマージ)結果、
修正案どおり「reserve 100・被害者が全供給を保有」とすると backstop 自体が被害者に
reserve 全額を補償し、損失が消える。`admin_rfq_coalition_drains_funded` は被害者を
供給の半分に**希釈**する形でこれを回避しており、正当な適応と判定する。さらに:

- 初回査読が偽と指摘した反実仮想(「被害者は攻撃前なら額面で償還できた」)は、
  **声明の連言として機械検証されている**(`redeemApxUSD` の成功と全額支払いの ∃)。
- 再分配も**連言として機械検証**: 結託が一切名指ししない傍観者(address 4)が
  USDC 0 から始まり、被害者の元本のちょうど半分を backstop の pro-rata 脚から受領する。
- witness は `Safety.WellFormed` の両連言を満たす(全残高 ≤ 供給、`redemptionValue = ray ≤ ray`)。

**アクション 2 — 適用済み。** docstring 最終段落が 3 前提を明示する: RFQ 依頼の
オフチェーン合意フローはスコープ外(§6.1)、backstop は `emergencyFlag` 下で admin
単独署名、pro-rata 脚は**モデル化済み**(初回査読時の「省略」から状況が変わり、
本 witness ではまさにそれが傍観者への支払いを行う)。

## 手計算追跡(witness → 2 step)

`coalWitnessFunded`(供給 200、victim=0 が 100、bystander=4 が 100、reserve 100、
tCV 0、price ray、victim の RFQ request 100、emergencyFlag up)→
`catastrophicBackstop`(admin=1): price := 0·ray/200 = 0、victim +50、bystander +50、
reserve := 0 → `executeRFQRedemption 0 100`(counterparty=2): 6 ガードすべて通過
(pause false / counterparty ∈ / whitelist / request 100 ≥ 100 / bal 100 ≥ 100 /
payout 0 ≤ 0)、victim の apxUSD 100 → 0、payout 100·0/ray = 0。終状態: victim
(0 apxUSD, 50 USDC)、bystander (100 apxUSD, 50 USDC)。声明の全連言と一致。

## 残存所見

- **F2 の単位跨ぎは未解決のまま**(backstop 価格式 `totalCollateralValue * ray / totalSupply`
  の単位問題)。本 witness も tCV = 0 の両解釈一致領域にあり、定理の真偽には影響しないが、
  backstop を tCV > 0 で使う将来の witness はこの欠陥に直面する。
- F4(summary の "requiring")は本定理の docstring には現れない(十分性のみを主張)。

## 判定

**モデル内主張として perfect 昇格相当と判定する。** 定理は真、証明は健全、
初回査読の全所見が解消または明示的免責済み、反実仮想と再分配は機械検証済み。
人間査読者による最終確認を経て正式昇格とすることを推奨する。
