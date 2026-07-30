# 仕様レベル欠陥(spec-level defect)の発見手法 — 設計メモ

(調査日 2026-07-08。docs2formalspec 第4のテーマ:「モデルが仕様に適合するか」から「**仕様そのものが健全か**」への転回。)

## 0. 問題設定 — なぜ現行パイプラインは仕様欠陥を見つけないのか

これまで本ツールが Apyx で見つけたのは次の2種だった:

- **モデル忠実性ギャップ** — Lean モデルが仕様/実コントラクトと乖離していた箇所(例: vesting の2アキュムレータ設計を1つに畳み込んでいた §`docs/06` §4b)。これは *モデルの誤り* であって仕様の欠陥ではない。
- **防御機構の不在(設計提案)** — 鍵漏洩時に被害が無限大になる、redemption 価格にフロアが無い等(§`docs/05`)。これは *設計の弱点* だが、要件どうしの内部矛盾ではない。

**仕様そのものの内部矛盾・欠陥は体系的に探していない。** 理由は構造的である:

> 第1の柱(要件適合)は各要件 `R` について「モデル `⊨ R`」を証明する。これは**仕様を ground truth とみなす**営みなので、原理的に「仕様が間違っている」ことは見つけられない。第2・3の柱(被害上限・設計安全性)は設計の弱点を出すが、対象は *モデルの振る舞い* であって *要件集合の内部整合性* ではない。

したがって「仕様欠陥の発見」は、要件適合とは**逆向き**の第4の活動を要する: 仕様を真とせず、**要件集合それ自体を敵対的に検査する**。本メモはその手法をまとめる。

---

## 1. 仕様レベル欠陥のタクソノミー

要件工学は仕様品質を4つの欠陥クラスで捉える(Ott et al. のレビュー[^ott]): **不整合・不完全・曖昧・冗長**。ここに形式手法の視点(実現不能性)を加えて整理する。

| # | 欠陥クラス | 定義 | 例 |
|---|---|---|---|
| D1 | **矛盾/不整合** (inconsistency) | 2つ以上の要件が同時に成立不能 | 「常に閉」+「いつか開く」 |
| D1a | ├ 無条件矛盾 | 全状態で衝突 | — |
| D1b | ├ 条件付き矛盾 | ある到達可能状態でのみ衝突 | ストレス時のみ衝突 |
| D1c | └ **合成的矛盾** (compositional / feature interaction) | A と B は個別に無矛盾だが、第3の要件/定義 C を介して衝突 | ← 最重要・見落とされやすい |
| D2 | **曖昧性** (ambiguity) | 複数の非等価な解釈を許す。特に「危険な曖昧性」= 読者が気づかないもの[^berry] | 単位・次元の不一致、多義語 |
| D3 | **不完全性** (incompleteness) | 仕様が沈黙している部分。*unspecified*(要件丸ごと欠落)vs *underspecified*(詳細不足) | パラメータの下限未規定、未被覆の状態/操作 |
| D4 | **冗長/過剰制約** (redundancy / over-constraint) | load-bearing でない要件、または過剰制約で実現可能性を壊す | — |
| D5 | **実現不能性** (unrealizability) | 充足可能でも、敵対的環境下で守れる戦略が存在しない | 防御機構の不在はこの形 |
| **D6** | **抽出欠陥** (extraction defect) | **原典は健全だが、NL→要件/形式化の変換で取りこぼし・過剰一般化・誤解釈が入り、抽出物どうしが矛盾/曖昧になる** | ← 本ツール自身の出力の欠陥。§3.0 の照合で D1–D3 と峻別。候補1が実例 |

**合成的矛盾(D1c)の重要性**: 自然言語推論(NLI)ベースの要件矛盾検出は要件を **対(ペア)** で見るため、A+B が第3の要件 C を介して初めて衝突する合成的矛盾を**構造的に見落とす**ことが知られる[^fantechi]。これは通信ソフトウェアの **feature interaction 問題**と同型であり[^fi]、検出には**三つ組(トリプル)以上**を見る必要がある。後述の Apyx 候補1はまさにこの型。

---

## 2. 発見手法カタログ

各手法について「何を検出 / 原理 / 本 Lean パイプラインへの写像 / コスト」を示す。形式手法側(§2.1)と要件工学側(§2.2)に分ける。

### 2.1 形式手法による検出

| 手法 | 何を検出 | 原理 | Lean パイプラインへの写像 |
|---|---|---|---|
| **M1 充足性チェック** (satisfiability) | D1 矛盾 | 全要件述語の連言を満たす具体モデルの存在を問う。UNSAT ⇒ 矛盾。SMT/SAT は最小の **unsat core** を返し衝突箇所を局所化[^smt] | 要件述語 `R₁…Rₙ` を満たす具体 `State`(+trace)を構成: `∃ s, R₁ s ∧ … ∧ Rₙ s`。反対に、ある到達可能状態で `Rᵢ ∧ Rⱼ → False` を証明できれば条件付き矛盾 |
| **M2 ペア/トリプル矛盾探索** | D1a–D1c | 同一 State フィールド/Op を制約する要件の対・三つ組を列挙し、到達可能状態で連言の不能を試みる | **三つ組まで**見て合成的矛盾を捕捉。候補1がこの適用例 |
| **M3 悪状態到達可能性(否定定理)** | D3 ギャップ / D5 | 望ましくない `BadState`(insolvency, free value, buffer 枯渇, payout=0)を定義し、`∃ trace, reachable BadState ∧ (どの要件も違反していない)` を **witness 付きで**証明。仕様が悪状態を排除していない = ギャップ | ← 既存 `redeem_payout_has_no_cap`(§`docs/05` T6)が実例。「クランプが無く払戻上限が存在しない」を witness 付きで証明済み。これは**既に仕様レベルの発見**だった |
| **M4 Vacuity / witness チェック** | D2/D3 の兆候 | 各要件定理の**前提が到達可能か**を確認。前提が充足不能なら定理は空虚に真=何も制約しない[^vacuity](Beer et al./Kupferman–Vardi) | 各 `req_*` の前提を満たす具体状態 `∃ s, hyp s` を要求。空虚な定理は「仕様/モデルが当該挙動を一度も励起しない」兆候。← 本プロジェクトは既に空虚定理(`∃x,y=x` 等)を修正済み。これを**体系的なパス**にする |
| **M5 被覆/沈黙解析** | D3 不完全性 | State フィールド・Op を列挙し、各が何らかの要件で制約されるかを確認。無制約な表面 = underspecification。状態/入力空間の被覆として形式化[^coverage] | 閉じた `Op` 型と `State` レコードを機械的に走査し、各フィールド/op に対応する `req_*` の有無を表にする。無いものが沈黙点。← `redemptionValue` の**下限**を制約する要件が無い、が実例 |
| **M6 実現不能性 / 反実現戦略** | D5 | 充足可能でも敵対的環境に対し要件を守る戦略が無ければ conflict。GR(1) 等は **counter-strategy**(敵の反例プレイ)を返す[^gr1] | ← blast-radius の脅威モデル(攻撃者=環境)がこれ。`admin_rfq_coalition_drains` の攻撃トレースが counter-strategy に相当 |
| **M7 Deadlock / liveness** | D3/D1 | 全 Op が revert する到達可能状態(資金ロック)や、望ましい状態の到達不能を探す[^tlc] | `∃ s reachable, ∀ op c, step s op c = none`(全操作 revert=デッドロック)を探索。TLC の deadlock 検出に対応 |
| **M8 Mutation / load-bearing 解析** | D4 冗長 / D3 ギャップ | 要件を除去・反転して safety 定理が壊れるかを見る。壊れない ⇒ 冗長 or 別要件が担保。壊れる ⇒ load-bearing(その欠落は gap) | ある `req` を仮定から外して依存する安全性定理が再証明できるかを確認 |

### 2.2 要件工学(自然言語)側の検出

Lean 化の**前段**、自然言語 RFC 2119 要件(`requirements.json`/`SPEC.md`)の段階で効く手法:

- **M9 多サンプル形式化の不一致(曖昧性検出)** — 同一要件を**独立に複数回**形式化し、得られた論理式の充足性/意味が食い違えば、その要件は複数の読み方を許す(=曖昧)。ground truth 無しに曖昧性を測れるのが要点[^neurosym]。**本ツールの blind LLM judge**(定理の意味を docstring 抜きで読み要件と照合し `full`/`partial`/`mismatch` を付ける §`docs/06` §0)は、まさにこの「独立形式化の一致度」測定であり、`mismatch`/`partial` は曖昧性・不完全性の信号として再解釈できる。`review.json` に defect クラスを区別報告するのが自然な拡張。
- **M10 形式化=検出器(formalization as forcing function)** — 「NL 要件を論理に書き下す行為そのものが、隠れた曖昧性・矛盾を強制的に露出させる」ことは複数の一次資料が支持する[^formalize][^neurosym]。実際、本プロジェクトの Lean 化過程で `catastrophic-backstop` の「Redemption Value = Total Collateral Value」の単位不一致(候補3)や、vesting の畳み込み(モデル欠陥)が露出した。
- **M11 予防層(CNL テンプレート)** — EARS(Easy Approach to Requirements Syntax)等の制約付き自然言語で MUST/SHALL 節を型化し、曖昧性を発生源で抑える[^ears]。標準文書ですら仕様分裂は起きる(例: ERC-1271 は署名型 `bytes` vs `bytes32` で非互換な複数版が流通[^erc1271])。
- **M12 対/三つ組の意味的矛盾スキャン** — FSARC/NLI 等で要件対の矛盾を分類。ただし §1 の通り**三つ組**まで拡張して合成的矛盾を捕捉すること。

### 2.3 DeFi 設計欠陥に特化した「invariant ギャップ」法

Trail of Bits の **invariant-driven development**[^idd] は、設計欠陥(business logic flaw)の体系的ギャップ探索を与える。本ツールの M3/M5 と合流する:

1. **保つべき不変条件を列挙する** — function-level(純計算: 金利は単調増加)/ system-level(`balance ≤ totalSupply`, `x·y=k`)/ high-level economic(solvency: 資産≥負債、conservation: 価値保存)。
2. **各を表に文書化** — ID・英語記述・影響コントラクト・検証戦略(fuzz/formal/unit)。複雑なものは Hoare 三つ組(事前条件・命令・事後条件)で。
3. **仕様要件を各不変条件に写像** — 「各不変条件を *全経路で* 強制する要件/チェックはどれか?」を問う。**強制する要件が無い不変条件 = ギャップ**(=「どの要件も禁じていない悪状態」)。Euler の `donateToReserves` が `checkLiquidity` を欠いていた $197M 事件はまさにこの型[^euler]。
4. **否定を敵対的に検証** — 各不変条件を prover/fuzzer に `assert(P)` として渡す。反例トレース = ギャップが到達可能である確証。

**得られるチェックリスト骨格**: solvency / conservation / monotonicity / share↔asset 整合(インフレ攻撃経路の不在)/ 全状態変更への認可 / パラメータ境界(caps・floors・rate-limit)/ oracle 頑健性(合成・可操作性・staleness)/ liveness(常に引き出せる)。各行につき「否定を全経路で禁じる要件が仕様にあるか」を検証し、無ければ設計欠陥。

---

## 3. Apyx 仕様の欠陥候補(本手法の初期適用)

以下は §2 の手法を Apyx の `requirements.json` に手動適用して得た候補。**候補1 は Lean で機械証明済み**だが、原典照合の結果 **抽出欠陥(下記 §3.0)** と判明した。候補2–5 は未検証の仮説。

> ### 3.0 最重要の教訓 — 抽出欠陥 vs 原典仕様欠陥を必ず区別せよ
>
> 候補を機械証明できても、それは「**抽出された** requirements.json が矛盾する」ことしか示さない。矛盾の**根本原因**が (a) 原典仕様(corpus.md / 実コントラクト)自体の欠陥なのか、(b) LLM 抽出が原典を**取りこぼした/過剰一般化した**「**抽出欠陥**(D6)」なのかは、**各要件をその `source_quote` と原典に遡って**初めて判定できる。**この照合を省くと、ツール自身の抽出ミスを「プロトコルの欠陥」と誤報告する。** 候補1がまさにこの罠だった(下記)。
>
> **手順**: 矛盾を検出 → 各要件の `source_quote` を確認 → 原典で当該条項のスコープ・例外・単位を読む → (a)/(b) を判定。**原典の優先順位: ① corpus.md(散文ドキュメント)→ ② corpus が曖昧・暗黙・不精密な場合は Solidity 実装(`apyx-labs/evm-contracts`)を ground truth とし、それに従って spec を構成する。** 実装が最終真実(corpus は実装の非形式的記述にすぎない)。候補2・3・5 は corpus が曖昧だったため Solidity で解決した(下記)。

### 候補1 ✅ **解決済み**(抽出欠陥 D6 と判明 → spec 修正・モデル整合済み、2026-07-08)

**経緯**: バッファ>0 の witness 上で `catastrophic-backstop` の step が**バッファを厳密に減少させる**ことを機械証明 ⇒ 抽出された「MUST NOT decrease(無条件)」と「buffer 全額分配」が矛盾。だが §3.0 の原典照合により **抽出欠陥(D6)** と判明:
- `corpus.md` は無矛盾:バッファは「**routine redemptions** の間は消費されない」「**stress events** を通じて保全」。catastrophic(終端事象)は「buffer 全額分配」と**別枠**。
- `buffer-non-decreasing` の `source_quote` は *stress events* の文なのに statement が無条件化されていた(過剰一般化)。正しくスコープした `buffer-preservation`(routine)・`buffer-growth-stress`(stress)が別に存在し冗長。

**是正(完了)**:
- `requirements.json` / `SPEC.md` の `buffer-non-decreasing` を原典どおり「**catastrophic を除き、routine/stress 下で** MUST NOT decrease」に修正済み。
- Lean モデルの `req_buffer_non_decreasing` は元から routine op 限定で**修正仕様と整合**(モデルは正しかった)。docstring を修正仕様に更新。
- SpecDefects の定理を `req_catastrophic_backstop_distributes_buffer` に改名し、**catastrophic 例外の肯定的言明**(backstop が buffer を 0 にする=修正済み要件が除外する挙動)として保持。`README` §6.2 の「catastrophic 第2節が未モデル化」ギャップを大きく closing(buffer→0 に加え、**各アドレスへの pro-rata クレジット `usdcReserve·apxUSDBal(a)/totalSupply` 自体を `req_catastrophic_backstop` で証明**。残るのは Σ 総和保存=分配総額と drained reserve の一致のみで、これが集約台帳の表現限界)。なお `catastrophicBackstop` は model.md の "Governance emergency flag set" ガードに忠実に `emergencyFlag == true` 前提で発火する(フラグは stress 経路 `handleStressEvent` が立てる)。
- **Apyx 側の修正は不要。** これはツール(抽出パイプライン)の欠陥だった。
- `buffer-non-decreasing`: 「overcollateralization buffer は **MUST NOT decrease**」
- `buffer-growth-stress`: 「ストレス事象では **むしろ増加** すべき(drain されない)」
- `catastrophic-backstop`: 「カタストロフィ検出時、Redemption Value を Total Collateral Value に等しくし、**buffer を含む reserve 全額を** holder に pro-rata 分配する」

→ カタストロフィ/ストレス状態において、「バッファを減らしてはならない」と「バッファを全額分配せよ」が**同時に要求される**。三つ組(あるいは buffer の定義 C を介した A+B+C)を見て初めて現れる合成的矛盾。**検証法 M1+M2**: バッファ>0 の到達可能なカタストロフィ状態で、`buffer-non-decreasing` の事後条件と `catastrophic-backstop` の事後条件の連言が `False` を導くことを Lean で示せる(候補中もっとも形式化しやすい — 次段の推奨)。

**候補2–5 の三分結果(2026-07-08、§3.0 の原典照合 = corpus → Solidity を実施)**: いずれも候補1のような *ハードな矛盾* ではなかった。候補2・3・5 は **corpus が曖昧**だったため **Solidity 実装を ground truth として解決**(下記、spec 修正済み・候補3 はモデルも修正)。候補4 は **真の不完全性(D3)** だが blast-radius で既に機械証明済み。**corpus 照合の段階で4件の偽陽性「仕様欠陥」報告を防ぎ、さらに Solidity 照合で確定的に解決** — §3.0 手順の有効性の実証。

### 候補2 → ✅ **Solidity で解決(D2 corpus 曖昧 → 実装が真実)**
- `issuance-price-one`(quote L123/L355「issuance is **always priced at $1**」)vs `price-may-include-spreads`(quote **L23**「spreads … during minting **and** redemption may be reflected in the price」)。corpus 自体に緊張(L23 と L123)。
- **Solidity 照合**: `src/MinterV0.sol` は `apxUSD.mint(beneficiary, amount, nonce)` で **order.amount をそのまま 1:1 で mint**(オンチェーンにスプレッド無し)。スプレッド/execution 費用は **オフチェーン**の USD 収受時に適用され、オンチェーン状態機械の**範囲外**。
- **解決**: `price-may-include-spreads` の rationale に「オンチェーンは 1:1、スプレッドはオフチェーン」を明記(spec 修正済み)。オンチェーンでは矛盾しない。モデルは exact-$1(`req_mint_price`)で忠実。

### 候補3 → ✅ **Solidity で解決 + モデル修正(D2 corpus 不精密 → 実装が真実)**
- `catastrophic-backstop`(quote L375「**Total Collateral Value becomes the redemption value**」)。総額を単価に等号で結ぶ不精密表現。
- **Solidity 照合**: `src/oracles/ApxUSDRateOracle.sol` の `rate` は **per-unit** apxUSD→USDC 価格(1e18)で `newRate > 0` ガード付き。したがって「TCV becomes redemption value」= **単価 = TCV / totalSupply**。
- **解決**: `requirements.json`/`SPEC.md` の `catastrophic-backstop` を per-unit(TCV ÷ totalSupply)に修正。**モデルも修正**: `Op.catastrophicBackstop` を `redemptionValue := totalCollateralValue * ray / totalSupply_apxUSD` に変更(旧 `:= totalCollateralValue` は総額を単価フィールドに代入する**次元エラー**だった)。`req_catastrophic_backstop`・`step_catastrophicBackstop_exact`・`redemption_price_admin_only`・`catastrophicBackstop_is_instantaneous`・coalition/timelock witness・`SpecDefects` を per-unit に整合(全緑・sorry 0)。

### 候補4 → **真の不完全性(D3)。ただし blast-radius で機械証明済み・提言済み。**
- `redemptionValue` の**下限**を縛る要件が無い。`catastrophic-backstop`+`handleStressEvent` で `totalCollateralValue`→0 ⇒ 償還 0 USDC。
- **原典照合**: L123/L367「Redemption Value acts as a **hard floor** where arbitrageurs step in」は *二次市場価格* が redemption value を下回らない話(裁定)であって、*redemptionValue 自体* の下限ではない。redemptionValue は「basket に追随し cash で緩和」(L353)して下落しうる。よって仕様は redemptionValue のフロアに **沈黙**(D3)。
- **状態**: 既に `BlastRadius.admin_rfq_coalition_drains`(redemptionValue=0 で 0 USDC 焼却)・`redeem_payout_has_no_cap` で機械証明済み。是正提案(redemption 価格フロア)も `README` §5 に記載済み。→ **新規証明は不要**、仕様の不完全性として本メモに再分類。

### 候補5 → ✅ **Solidity で解決(D3 corpus 沈黙 → 実装が真実)**
- `exchange-rate-non-decreasing`(quote L161「yield accrues through a **gradually increasing** exchange rate」)。corpus は stress/担保喪失が交換レートを下げるかに **沈黙**。
- **Solidity 照合**: `src/oracles/ApyUSDRateOracle.sol` の `rate` は `IERC4626(vault).convertToAssets(1e18)`(= apxUSD-per-apyUSD)× adjustment。すなわち apyUSD 交換レートは **apxUSD 建て**であり、担保 stress は *apxUSD の USD 償還価値*(ApxUSDRateOracle)を下げるだけで、vault が保有する *apxUSD トークン数* には影響しない。よって交換レートは stress から**構造的に分離**され、yield でのみ非減少に増える。
- **解決**: モデルの分離は **実装に忠実**(仮定ではなく実装どおり)。`req_exchange_rate_non_decreasing` は正しい。rationale に apxUSD 建ての根拠を明記(spec 修正済み)。

### 候補4 → **真の不完全性(D3)。blast-radius で機械証明済み・提言済み。**
- `redemptionValue` の**下限**を縛る要件が無い。
- **Solidity 照合**: `ApxUSDRateOracle.setRate` は `newRate > 0` ガードのみ(厳密 0 は不可だが 1 wei まで許容=実質フロア無し・上限も無し)。corpus L367「hard floor」は *二次市場価格* の話で redemptionValue 自体のフロアではない。
- **状態**: `BlastRadius.admin_rfq_coalition_drains`・`redeem_payout_has_no_cap` で機械証明済み。是正提案(redemption 価格フロア)は `README` §5。→ 新規証明不要。

### 候補2–5 のまとめ表(§3.0 = corpus → Solidity 適用後)
| 候補 | corpus | Solidity 照合の結論 | 状態 |
|---|---|---|---|
| 2 | 曖昧($1 vs minting spread) | オンチェーン mint は 1:1、スプレッドはオフチェーン(`MinterV0`) | ✅ spec rationale 修正・モデル忠実 |
| 3 | 不精密(総額=単価) | redemption value は per-unit=TCV/supply(`ApxUSDRateOracle`) | ✅ spec＋**モデル**を per-unit に修正 |
| 4 | 沈黙(フロア無し) | `setRate` は `>0` のみ・実質フロア無し | 既に blast-radius で証明・提言済 |
| 5 | 沈黙(stress→レート) | 交換レートは apxUSD 建てで stress から分離(`ApyUSDRateOracle`) | ✅ モデルは実装に忠実・spec rationale 修正 |

**結論**: corpus が曖昧・暗黙・不精密だった候補(2/3/5)は Solidity 実装を ground truth として **確定的に解決**(spec 修正済み、候補3 はモデルも per-unit に修正)。候補4 は既知の設計ギャップで対応済み。Apyx への「明確化依頼」は不要となった — 実装が答えを与えた。今後も corpus 曖昧時は Solidity に従う(§3.0)。

---

## 4. docs2formalspec への統合(第4の活動)

要件適合(第1柱)・被害上限(第2柱)・設計安全性(第3柱)に続く **第4の活動「仕様欠陥探索」** として位置づける:

- **向き**: 仕様を ground truth とせず、要件集合自体を敵対的に検査(第1柱の逆)。
- **予防層 + 検出層**: M11(EARS/CNL 型化)で発生源を抑えつつ、M1–M8(形式)/M9–M12(NL)で検出。
- **blind judge の再解釈**: 既存の LLM judge(§`docs/06`)を M9「多サンプル形式化不一致=曖昧性検出器」として活用。`review.json` に欠陥クラス(inconsistency/ambiguity/incompleteness/unrealizability)を区別報告する項目を追加。
- **invariant ギャップ表**(§2.3)を要件抽出時に併走生成し、各不変条件に「強制する要件」を紐付け、空欄=ギャップとして自動フラグ。
- **テンプレート化**: `templates/spec-defects/` に M1–M8 の Lean スケルトン(充足性 witness・トリプル矛盾・悪状態到達・vacuity・被覆表)を用意する構想。

**候補1(完了)**: M1+M2 で機械証明 → §3.0 の原典照合で **抽出欠陥(D6)** と判明 → `requirements.json`/`SPEC.md` 修正・Lean モデル整合・定理を `req_catastrophic_backstop_distributes_buffer`(catastrophic 例外の肯定形)に改名、まで完了。手法の有効性と**原典照合の不可欠性**を同時に実証した。次段は候補2(MAY vs MUST、M12)・候補4(下限の沈黙、M3+M5)を**原典照合込みで**検証する。

**是正先はツール(抽出パイプライン)**: `requirements.json` の `buffer-non-decreasing` を原典どおり routine/stress 限定に修正または削除する(冗長)。**Apyx 側の仕様修正は不要。** 併せて、抽出パイプラインに「MAY 節・スコープ副詞(during routine/stress 等)・例外条項を落とさない」チェック(M11 の予防層)を組み込むべき。

---

## 5. 正直な限界

- **充足性は必要条件にすぎない**: 「仕様に矛盾が無い(充足可能)」を示せても「仕様が正しい」は示せない。欠陥の *不在* 証明は原理的に不可能で、探索は反例発見型である。
- **Lean は手動 witness 寄り**: M1/M3 の充足性・反例探索は SMT(Z3)・Alloy(bounded model finding)・TLC(網羅探索)の方が自動化に向く。Lean は閉じた `Op` 型で網羅ケース分析ができる利点がある一方、witness/counterexample は手で構成する必要がある。将来的には NL 要件→SMT の自動化(M9)と Lean 証明を併用する二層構成が望ましい。
- **曖昧性・不完全性の *解消* はツール外**: 検出はできても、どう直すかはステークホルダー交渉とドメイン知識を要する — 研究の一致点[^neurosym]。本ツールは「ここが曖昧/矛盾/沈黙している」を機械的に指し示すところまでを担う。
- **候補≠確定**: §3 は手動適用の仮説。確定には §2 の手法での機械検証(または反証)が必要。

---

## 参考文献

### 仕様の矛盾・充足性・vacuity
[^smt]: Cimatti et al., *Automated SMT-based consistency checking of industrial critical requirements* — https://www.researchgate.net/publication/322846746 ; *Completeness and Consistency of Tabular Requirements: an SMT-Based Verification Approach* — https://www.researchgate.net/publication/388126195
[^vacuity]: Beer, Ben-David, Eisner, Rodeh, *Efficient Detection of Vacuity in ACTL* (CAV'97); Kupferman & Vardi, *Vacuity Detection in Temporal Model Checking* (STTT) — https://link.springer.com/article/10.1007/s100090100062
[^gr1]: GR(1) synthesis / unrealizable core & counter-strategy (FSE'15) — https://dl.acm.org/doi/10.1145/2786805.2786824 ; *Analyzing Unsynthesizable Specifications* (LTLMoP) — https://www.researchgate.net/publication/225229856
[^tlc]: TLA+ / TLC(deadlock・inductive invariant)— https://docs.tlapl.us/using:tlc:start ; *TLA+ Trifecta*(TLC/Apalache/TLAPS)— https://arxiv.org/pdf/2211.07216 ; Alloy unsat core — https://alloytools.org/quickguide/unsat.html

### 要件工学(矛盾・曖昧・不完全)
[^ott]: Ott et al., *Classification of defect types in requirements specifications* — https://www.researchgate.net/publication/261269780
[^fantechi]: Fantechi et al., NLI が合成的(第3要件経由)矛盾を見落とす — https://arxiv.org/abs/2405.05135
[^fi]: *Feature Interactions in Software and Communication Systems* — https://ebooks.iospress.nl/book/feature-interactions-in-software-and-communication-systems-ix
[^berry]: Berry, *The Ambiguity Handbook* — https://cs.uwaterloo.ca/~dberry/ambiguity.res.html
[^coverage]: Heimdahl/Leveson, *Completeness and Consistency in Hierarchical State-Based Requirements* — https://www.researchgate.net/publication/3187804 ; NIST, *Input Space Coverage Matters* — https://csrc.nist.gov/CSRC/media/Projects/automated-combinatorial-testing-for-software/documents/ieee-comp-jan-20.pdf
[^neurosym]: *Neurosymbolic Auditing of NL Requirements*(多サンプル SMT 不一致で曖昧性検出)— https://arxiv.org/pdf/2605.13817
[^formalize]: *Automated formalization of structured NL requirements*(形式化が欠陥を露出)— https://www.sciencedirect.com/science/article/abs/pii/S0950584921000707
[^ears]: EARS 他 RE テンプレートのベンチマーク — https://link.springer.com/article/10.1007/s00766-024-00427-0
[^erc1271]: ERC-1271 の非互換な複数仕様 — https://medium.com/taipei-ethereum-meetup/clarifications-on-erc-1271-smart-contract-signature-verification-and-signing-cd5c2fb7ac1b

### DeFi 設計欠陥・invariant ギャップ
[^idd]: Trail of Bits, *The call for invariant-driven development* — https://blog.trailofbits.com/2025/02/12/the-call-for-invariant-driven-development/ ; *Reusable properties for Ethereum contracts* — https://blog.trailofbits.com/2023/02/27/reusable-properties-ethereum-contracts-echidna/
[^euler]: Euler $197M 自己清算(設計欠陥: `donateToReserves` が `checkLiquidity` を欠く)— https://www.cyfrin.io/blog/how-did-the-euler-finance-hack-happen-hack-analysis
- ERC-4626 インフレ攻撃(設計欠陥)— https://www.openzeppelin.com/news/a-novel-defense-against-erc4626-inflation-attacks ; https://reports.zellic.io/publications/perennial/findings/critical-vaultsol-erc-4626-inflation-attack-on-vault
- Moonwell oracle 誤設定 $1.8M — https://www.theblock.co/post/390302/
- DeFi security SoK — https://www.sciencedirect.com/science/article/pii/S2667295226000024 ; 構造タクソノミー — https://arxiv.org/html/2511.09051
