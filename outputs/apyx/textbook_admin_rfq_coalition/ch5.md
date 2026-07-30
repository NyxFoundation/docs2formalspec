# 第5章 重大問題2(F2) — `catastrophicBackstop` の権限・効果・単位が原典と乖離

F2 は F1 と違い、**3つの独立した乖離** が1つの操作に同居しています。査読報告(F2 節)はこれを (a) 権限、(b) 補償脚の省略、(c) 単位跨ぎの3点に分けています。順に、第3章の型で解剖します。共通の題材は `catastrophicBackstop` の1分岐です。

再掲(`Apyx.lean:731`):

```lean
| Op.catastrophicBackstop =>
    if caller == s.admin then
      some { s with redemptionValue := s.totalCollateralValue, emergencyFlag := true }
    else none
```

たった4行です。この4行が、原典の backstop から3つの意味で乖離しています。

---

## 5.1 乖離(a): 権限 — 「緊急フラグ」が「admin 単独・無条件」に化けている

### 原典

**model.md:71(前提条件):**
> | catastrophicBackstop | – | **Governance emergency flag set** | RedemptionValue = ... |

原典モデルでは、backstop の発動条件は「**ガバナンスの緊急フラグが立っていること**」です。つまり「破滅的事態である」というガバナンス側の判断(緊急フラグ)が **前提** で、admin はその後で機械的に実行するだけ、という構図が読み取れます。

`corpus.md:375` はトリガー権限を **明示していません**(「破滅的な事態において」としか言わない)。ここが重要: **原典はトリガー権限を無指定のまま曖昧に残している。**

### Lean モデル

```lean
if caller == s.admin then
  some { s with redemptionValue := ..., emergencyFlag := true }
```

- ガードは `caller == s.admin` **のみ**。緊急フラグの事前チェックは無い。
- しかも効果の中で `emergencyFlag := true` を **自分で立てている**。フラグは前提ではなく、この操作の **結果** になっている。

つまりモデルは「**admin が単独で、いつでも、前提条件なしに** backstop を発動できる」と解釈しています。model.md:71 の「フラグが立っていること」という前提を、モデルは「フラグは自分で立てる」に反転させています。

### なぜこれが headline に効くか

第1章で述べた物語を思い出してください:「**{admin, RFQ} の 2 鍵で 100% 奪える**」。この「2鍵で足りる」という主張の強さは、**backstop が admin 単独で無条件に発動できる** という前提に完全に依存しています。

- もし backstop に「ガバナンスの緊急フラグが必要」なら、admin1人では価格を壊せません。**ガバナンスという第3の鍵が必要になり、「2鍵で足りる」が崩れます。**
- 査読報告(32行目)の言葉:「『{admin, RFQ} の 2 鍵で足りる』という headline は、この **敵対的に最も広い解釈(admin 単独・無条件)** に立脚している。」

**本質**: 原典がトリガー権限を曖昧にしている隙に、モデルは「攻撃者に最も有利な=最も広い」解釈を選んでいます。これは検証としてはむしろ **保守的(最悪ケースを取る)** で悪くない態度ですが、その選択を **明記していない** のが問題です(第3章の「隠された簡略化」)。読者は「2鍵で足りる」を額面通り受け取り、実際には第3の鍵(ガバナンス)が要るかもしれないことに気づけません。

---

## 5.2 乖離(b): 補償脚の省略 — 「按分分配」がまるごと消えている

### 原典

**corpus.md:375(製品原文):**
> Total Collateral Value becomes the redemption value, and **the entire reserve, buffer included, is distributed pro-rata to remaining holders.**

**SPEC.md の REQ-catastrophic-backstop(要件):**
> the system MUST set Redemption Value equal to Total Collateral Value **and MUST distribute the entire reserve, including the buffer, pro-rata to remaining holders.**

原典の backstop は **2つの脚(leg)** から成ります:

```
本来の catastrophicBackstop = 【脚1: 価格の一致】 ∧ 【脚2: 補償の分配】
  脚1: redemptionValue := totalCollateralValue    （価格を担保総額に合わせる）
  脚2: 準備金全体(buffer込み)を残る保有者に按分分配 （残った価値を全員に配る）
```

**脚2 こそが backstop の目的です。** 第1章で述べた通り、backstop は破滅時の **救済措置**。「もう続けられないから、残っている担保を全員で山分けする」。脚1(価格を tCV に合わせる)は、脚2(山分け)を正しく行うための **計算基準の設定** にすぎません。

### Lean モデル

```lean
some { s with redemptionValue := s.totalCollateralValue, emergencyFlag := true }
```

- 実装されているのは **脚1だけ**。`redemptionValue := totalCollateralValue`。
- **脚2(按分分配)が完全に省略されています。** 準備金を保有者に配る処理がどこにもない。

### なぜこれが headline に効くか

headline の核心語は「**uncompensated(無補償)**」の全損です。第2章の結論「被害者の apxUSD = 0、USDC = 0」——被害者は何も受け取らない。

しかし **原典に忠実なら、backstop は必ず脚2(按分分配)を伴います。** 準備金に価値が残っているなら、それは保有者に按分されるはずです。つまり:

```
現モデル（脚2を省略）:  価格が0になり、被害者は何も受け取れない → uncompensated
    ↓ 脚2を忠実に実装すると
本来:                    価格が0になっても、準備金の残りが按分分配される
                          → 準備金が非空なら、被害者は分配分を受け取る → compensated(部分補償)
```

査読報告(33行目)の言葉:「『uncompensated』が **非空リザーブ構成でも成立するのはこの省略の産物**。」

言い換えると: **「無補償の全損」が言えるのは、モデルが補償の脚を消しているからです。** 補償の脚を戻せば、準備金が空でない限り「無補償」は言えなくなる。headline の "uncompensated" は、脚2の省略という隠された簡略化の産物です。

---

## 5.3 乖離(c): 単位跨ぎの直代入 — backstop が「価格破壊器」に化けている

これが F2 の中で最も技術的に鋭く、あなたのエンジニア的感覚に最も刺さる点です。**型(単位)の不一致** です。

### 問題の1行

```lean
redemptionValue := s.totalCollateralValue
```

この代入は左辺と右辺で **単位(次元)が違います**。Solidity で言えば「`uint256 priceRay` に `uint256 tokenCount` を代入している」ようなもの——コンパイルは通るが意味的に壊れている、あの類です。

### なぜ単位が違うのか

`overcollateralizationBuffer` の定義(`Apyx.lean:237`)から、各変数の単位が逆算できます。

```lean
def overcollateralizationBuffer (s : State) : Nat :=
  let redemptionTotal := (s.totalSupply_apxUSD * s.redemptionValue) / ray
  if s.totalCollateralValue > redemptionTotal then s.totalCollateralValue - redemptionTotal else 0
```

ここで `redemptionTotal` と `totalCollateralValue` を比較・減算しているので、両者は同じ単位でなければなりません。`redemptionTotal` の単位を計算すると:

```
redemptionTotal = (totalSupply_apxUSD × redemptionValue) / ray
                =  [トークン数量]   ×  [ray/トークン]      / [ray]
                =  [トークン数量]                                    ← ドル価値ではなく「数量」相当
```

- `redemptionValue` の単位は **ray/token**(1トークンあたりの価格、ray スケール)。第1章で「返ってくる USDC = 金額 × redemptionValue / ray」と割り算していたのは、この ray スケールを打ち消すため。
- したがって `redemptionTotal` は **トークン数量** 単位。
- 比較相手の `totalCollateralValue` も同じ **トークン数量** 単位。

まとめると:

| 変数 | 単位 |
|---|---|
| `redemptionValue` | **ray / token**(価格) |
| `totalCollateralValue` | **token(数量)** |

**`redemptionValue := totalCollateralValue` は「価格(ray/token)」の変数に「数量(token)」を直接突っ込んでいる。** 単位を跨いだ代入です。

### この単位ミスが引き起こす災厄

具体例で見ます。**完全に健全な(solvent な)状態** を考えます:

```
totalCollateralValue = 100   （担保は100トークン相当ぶんある）
totalSupply_apxUSD   = 100   （発行済みapxUSDも100枚）
redemptionValue      = ray   （1枚 = $1.00、健全）
→ この状態は「担保100 = 発行100、1枚1ドルで返せる」完全に健全な状態
```

ここで backstop を呼ぶと:

```
redemptionValue := totalCollateralValue = 100
```

新しい `redemptionValue` は **100**。これは ray スケールの価格として解釈されるので:

```
1枚あたりの価格 = 100 / ray = 100 / 10^27 ≈ 0.0000...001 ドル ≈ 0
```

**完全に健全な状態(担保が発行額と一致)だったのに、backstop 後の価格は実質 0 になった。** solvency(支払い能力)は全く損なわれていないのに、価格だけが破壊された。

査読報告(34行目)の言葉:「完全に solvent な状態(例: tCV = supply = 100)でも backstop 後の価格は 100/10²⁷ ≈ 0 になり、**モデルの backstop は solvency と無関係な価格破壊 op になっている**。」

### 本質: backstop の「意味」が反転している

原典の backstop の脚1「`redemptionValue := totalCollateralValue`」は、**正しくは「価格 = 担保総額 ÷ 発行総数」であるべき** です。実際、原典は明示しています。

- `model.md:71`: `RedemptionValue = TotalCollateralValue / totalSupply_apxUSD`
- `model.md:69`(updateRedemptionValue): `RedemptionValue = TotalCollateralValue / totalSupply_apxUSD`

**原典は割り算(`/ totalSupply_apxUSD`)を含んでいるのに、Lean モデルは割り算を落として直代入しています。** この `/ totalSupply_apxUSD` の欠落が単位ミスの正体です。割り算を戻せば、`totalCollateralValue / totalSupply_apxUSD` は「1トークンあたりの担保価値」= 価格単位になり、健全な状態では ray 付近の妥当な値になります。

結果として、原典の backstop(担保に応じた **公正な返済価格の再設定** = 救済)が、モデルでは(健全でも価格を 0 に叩き潰す **無差別な価格破壊器**)に化けています。**意味が救済から破壊へ反転している。**

### witness はなぜこの罠を「すり抜ける」のか

ここで巧妙な点があります。witness では `totalCollateralValue = 0` に設定されていました(第2章)。tCV = 0 のとき:

- 正しい解釈(割り算あり): `0 / totalSupply = 0`
- 壊れた解釈(直代入): `0`

**両者が一致します。** つまり witness は「正しい backstop でも壊れた backstop でも同じ結果になる(price = 0)」領域を選んでいる。だから **定理そのものは救われます**(単位ミスがあっても、この特定の witness では結論は変わらない)。

査読報告(34行目)の言葉:「witness は tCV = 0 なので両解釈が一致する領域にあり、**定理自体は救われる**。」

**しかしこれは危うい。** 定理が「救われる」のは、たまたま tCV = 0 という特殊点を選んだからにすぎません。もし tCV ≠ 0 の witness を選んでいたら、壊れたモデルと正しいモデルで結論が食い違い、健全性そのものが疑わしくなっていたかもしれない。定理は綱渡りで生き延びている、というのが正確な理解です。

---

## 5.4 3つの乖離を1枚にまとめる

| | 原典が要求 | Lean モデル | headline への効き |
|---|---|---|---|
| **(a) 権限** | ガバナンス緊急フラグが前提(corpus は無指定) | admin 単独・無条件、フラグは自分で立てる | 「2鍵で足りる」が成立するのはこの最広解釈のおかげ |
| **(b) 補償脚** | 脚1(価格一致)+ 脚2(準備金を按分分配) | 脚1のみ、脚2を省略 | 「uncompensated」が言えるのは脚2省略のおかげ |
| **(c) 単位** | `redemptionValue = tCV / totalSupply`(割り算あり) | `redemptionValue := tCV`(直代入・単位跨ぎ) | backstop が救済から価格破壊器へ反転。witness の tCV=0 で辛うじて救われる |

---

## 5.5 過去レビューとの整合

査読報告(36行目)は F1 と同様、F2 も自動レビューと整合すると述べています。`review_run1.json` の該当 note:

> "The theorem **only guarantees Redemption Value = Total Collateral Value, omitting the required distribution of the entire reserve (including buffer) pro-rata to holders** and restricting the operation to the admin caller."

これは F2 の (b)(補償脚の省略)と (a)(admin 限定)を、独立に指摘しています。人間査読と自動レビューが再び一致しています。

---

## 5.6 本章のまとめ(次章への橋)

F2 は「1つの操作・3つの乖離」でした。

- **(a) 権限**: 「緊急フラグが前提」→「admin 単独・無条件」。「2鍵で足りる」を支える最広解釈。
- **(b) 補償脚**: 「価格一致 + 按分分配」→「価格一致のみ」。「uncompensated」を支える省略。
- **(c) 単位**: 「tCV ÷ 発行総数」→「tCV 直代入」。救済を価格破壊に反転させる単位ミス。witness の tCV=0 で定理は辛うじて救われる。

F1(攻撃の入口)と F2(攻撃の前段)を個別に解剖しました。次章では、この2つがどう **合流して headline 主張を組み立て**、そして忠実化するとその headline がどう崩れるのかを統合します。「唯一の構造的全損経路」という最も強い主張が、実は2つの隠れた簡略化の合成物である、という結論に至ります。
