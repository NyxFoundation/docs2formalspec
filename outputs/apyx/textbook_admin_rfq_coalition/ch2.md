# 第2章 定理を読む — `admin_rfq_coalition_drains` を1行ずつ

第1章で語彙を揃えました。本章では、査読対象の定理そのものを **Lean を読めなくても追える** ように分解します。あなたはカーネルの本質(型が命題、項が証明、`Prop` の証明無関係性)は掴んでいるとのことなので、文法の橋渡しに集中します。

---

## 2.1 まず「状態機械」という共通言語を確認する

Apyx の Lean モデルは、あなたがよく知る **状態機械** です。Solidity のコントラクトが「storage(状態)+ 関数(遷移)」であるのと1対1で対応します。

| Solidity | Lean モデル |
|---|---|
| コントラクトの storage 変数の集合 | `structure State`(第1章で見た全フィールド) |
| 関数呼び出し `f(args)` を `msg.sender` から | `step s op caller` |
| 呼び出し成功で storage が更新される | `step` が `some s'` を返す(`s'` が次状態) |
| `require(...)` で revert | `step` が `none` を返す |

つまり **`step : State → Op → Address → Option State`** は「この状態でこの操作をこの呼び出し者が行ったら、成功して次状態になる(`some s'`)か、revert する(`none`)か」を表す純関数です。`Option` の `none` が Solidity の revert、`some s'` が成功時の新 storage、と読み替えれば完全に対応します。

- `Op` は「呼べる操作の一覧」= 関数セレクタの列挙。第1章の catastrophicBackstop や executeRFQRedemption はこの `Op` のコンストラクタです。
- `caller` は `msg.sender`。

この対応さえ握れば、Lean のコードは「型が少しうるさい Solidity」として読めます。

---

## 2.2 定理の主張を「日本語の1文」に圧縮する

定理本体(`BlastRadius.lean:2671-2680`)はこうです。まず全体像を日本語で:

> **ある初期状態 `s` と、被害者・相手方・金額が存在して、次のシナリオが最後まで通る:**
> **(0) 金額は正で、被害者は初期に apxUSD をちょうどその金額だけ持ち、USDC は 0、返済価格は健全($1以上)、相手方は承認済み。**
> **(1) admin が catastrophicBackstop を呼ぶと成功し、その後 `redemptionValue = 0` になる。**
> **(2) 続けて相手方が executeRFQRedemption(被害者, 金額) を呼ぶと成功し、その後 被害者の apxUSD は 0、USDC も 0 になる。**

一言で言えば「**被害者は 100 の apxUSD を失い、見返りの USDC を1枚も受け取らない状態が、実際に到達可能である**」。これが「100% uncompensated loss(無補償の全損)」の意味です。

---

## 2.3 Lean 構文の橋渡し: `∃` と結論の連言

定理の頭部だけ抜き出します。

```lean
theorem admin_rfq_coalition_drains :
    ∃ (s s1 s2 : State) (victim counterparty amount : Nat),
      0 < amount ∧
      s.apxUSDBal victim = amount ∧ s.usdcBal victim = 0 ∧
      ray ≤ s.redemptionValue ∧
      s.rfqCounterparties.contains counterparty = true ∧
      step s Op.catastrophicBackstop s.admin = some s1 ∧
      s1.redemptionValue = 0 ∧
      step s1 (Op.executeRFQRedemption victim amount) counterparty = some s2 ∧
      s2.apxUSDBal victim = 0 ∧ s2.usdcBal victim = 0
```

構文の要点を、あなたの背景に合わせて最小限だけ:

- **`∃ (s s1 s2 : State) ...`**: 「〜を満たす `State` 型の `s, s1, s2` が **存在する**」。**これは存在証明(existential)** です。ここが最重要。存在証明とは「具体的な1例を挙げれば証明終わり」というもの。Solidity で言えば「この攻撃を実際に成立させる具体的な初期状態が1つある」と示すこと。**「全ての状態で起きる」とは言っていません。** ここは第3章・第6章で効いてきます。
- **`∧`**: 論理 AND。要求を数珠つなぎにしているだけ。
- **`s.apxUSDBal victim = amount`**: `s.apxUSDBal` は `Address → Nat` の写像(第1章の State フィールド)。`apxUSDBal victim` で被害者の残高。「= amount」で「ちょうど金額分持っている」。Solidity の `balanceOf[victim] == amount`。
- **`step s Op.catastrophicBackstop s.admin = some s1`**: 「状態 `s` で admin が backstop を呼ぶと成功し、結果が `s1`」。`some s1` は revert しなかったことを意味する。
- **`s1.redemptionValue = 0`**: その後 `s1` では返済価格が 0。
- **`step s1 (Op.executeRFQRedemption victim amount) counterparty = some s2`**: `s1` で相手方が「被害者から金額分の返済を執行」すると成功し、結果が `s2`。
- **結び `s2.apxUSDBal victim = 0 ∧ s2.usdcBal victim = 0`**: 最終状態で被害者の apxUSD は 0(全部焼かれた)、USDC も 0(何も貰えなかった)。

> **`Nat` について一点**: 全数量が `Nat`(非負整数)です。Solidity の `uint256` と同じく引き算は飽和(`0 - x = 0`)ではなく、Lean の `Nat` では `a - b` は `a < b` のとき 0 になる **切り捨て減算(truncated subtraction)** です。第1章の「返ってくる USDC = 金額 × redemptionValue / ray」の割り算も **整数除算(切り捨て)** です。`redemptionValue = 0` なら `金額 × 0 / ray = 0`。ここが「0 USDC しか返らない」の算術的な理由です。

---

## 2.4 witness — 「存在する」を実現する具体的な1例

存在証明は具体例(**witness、証人**)を1つ挙げれば済みます。この定理の witness が `coalWitness`(`BlastRadius.lean:2638`)です。

```lean
private def coalWitness : State :=
  { (default : State) with
      admin := 1
      rfqCounterparties := [2]
      apxUSDBal := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      totalCollateralValue := 0 }
```

Lean 構文の橋渡し:

- **`{ (default : State) with ... }`**: 「`default`(全フィールドがゼロ値の State)を土台に、列挙したフィールドだけ上書きした新しい State」。TypeScript のスプレッド `{...default, admin: 1}` と同じ。Solidity には直接対応物がないが、「構造体を作って一部だけ設定」と思えばよい。
- **`admin := 1`**: admin はアドレス `1`。
- **`rfqCounterparties := [2]`**: 承認済み相手方はアドレス `2` のみ。
- **`apxUSDBal := fun a => if a = 0 then 100 else 0`**: 残高写像を「アドレス 0 なら 100、他は 0」に。つまり **被害者はアドレス 0** で、100 apxUSD を持つ。
- **`redemptionValue := ray`**: 初期の返済価格は健全($1.00)。
- **`totalCollateralValue := 0`**: **準備金全体の価値は 0**。← ここが後で決定的に効く。

登場人物を整理:

| 記号 | witness での値 | 意味 |
|---|---|---|
| victim(被害者) | アドレス 0 | 100 apxUSD を持つ。攻撃の標的 |
| admin(攻撃者A) | アドレス 1 | backstop を呼ぶ |
| counterparty(攻撃者B) | アドレス 2 | RFQ を執行する |
| redemptionValue | `ray`(= $1.00) | 初期は健全 |
| totalCollateralValue | **0** | 準備金の価値がゼロ |

---

## 2.5 2ステップの攻撃を、状態遷移として追う

定理の証明本体は、この witness に対して2つの `step` を順に適用し、結論が成り立つことを計算で確かめます。あなたのために **算術だけ** を追います。

### ステップ1: admin が catastrophicBackstop を呼ぶ

`step` の該当分岐(`Apyx.lean:731`):

```lean
| Op.catastrophicBackstop =>
    if caller == s.admin then
      some { s with redemptionValue := s.totalCollateralValue, emergencyFlag := true }
    else none
```

- ガードは `caller == s.admin` だけ。admin(アドレス 1)が呼ぶので通る。
- 効果は **`redemptionValue := totalCollateralValue`**。witness では tCV = 0 なので、**`redemptionValue` が `ray`(=$1.00相当)から 0 に落ちる**。
- ついでに `emergencyFlag := true` を自分で立てる。

結果状態を証明では `R` と呼びます。`R.redemptionValue = 0`。**価格が瞬時に、下限も遅延もなく 0 になった。** これが定理の「the price crashes from ray to 0 with no floor and no delay」の中身です。

### ステップ2: counterparty が executeRFQRedemption(0, 100) を呼ぶ

`step` の該当分岐(`Apyx.lean:706`):

```lean
| Op.executeRFQRedemption user amount =>
    if s.globalPause then none
    else if ¬ (s.rfqCounterparties.contains caller) then none
    else if s.apxUSDBal user < amount then none
    else
      let usdcAmount := (amount * s.redemptionValue) / ray
      if s.usdcReserve < usdcAmount then none
      else
        let s1 := burnApxUSD s user amount
        let s2 := { s1 with
          usdcReserve := s1.usdcReserve - usdcAmount
          usdcBal := fun a => if a = user then s1.usdcBal a + usdcAmount else s1.usdcBal a }
        some s2
```

4つのガードを順に確認(全部通る):

1. `globalPause` は false → 通る。
2. `rfqCounterparties.contains caller`: 呼び出し者は 2、承認済みリストは `[2]` → 通る。
3. `apxUSDBal user < amount`: 被害者(0)の残高 100 < 100 は偽 → 通る。
4. `usdcReserve < usdcAmount`: `usdcAmount = 100 × redemptionValue / ray = 100 × 0 / ray = 0`。準備金 `< 0` は偽 → 通る。

効果:

- `burnApxUSD s user amount`: 被害者の apxUSD を 100 → 0 に焼く。
- `usdcBal[user] += usdcAmount = += 0`: 被害者の USDC は 0 のまま。

**最終状態 `s2`: 被害者の apxUSD = 0、USDC = 0。** 結論の通り。

### ステップ2で使われる補助定理(参考)

証明では `step_executeRFQRedemption_forward`(4ガードを渡すと成功して効果が確定する)と `rfq_payout_formula`(受け取り USDC が `amount × redemptionValue / ray` である)という2つの補助定理を使っています。これらは **証明専用の機械的補題** で、査読報告が「証明専用補題は人間査読対象外(機械検証済み)」として除外しているものです。**中身の正しさは Lean カーネルが保証済みなので、私たちが疑うべき対象ではありません。**

---

## 2.6 機械検証としては「健全」である、を確定させる

ここまでで、次が確認できました。

- 定理の主張は明確な存在証明である。
- witness `coalWitness` に対し、2ステップの攻撃が算術的に確かに成立する。
- 使われている `step` の分岐と補助定理は Lean のコードそのもの。

査読報告も冒頭でこれを認めています:「定理は Lean モデルに対する主張としては真で、機械検証は健全(`lake build` 通過、sorry なし、公理は標準3つのみ)」。

> **`sorry` と3公理について**: `sorry` は Lean の「証明の穴埋めを保留するプレースホルダ」で、これが1つでもあると証明は無効。この定理には無い。公理は `propext`(命題の外延性)/ `Quot.sound`(商型の健全性)/ `Classical.choice`(選択公理)の3つのみで、これは Lean/Mathlib の標準セット。**余計な公理を密輸していない** = カーネル的に信頼できる、という意味です。あなたが握っているカーネルの本質(証明が型検査を通れば正しい)がそのまま効いている状況です。

---

## 2.7 では、何が問題なのか — 次章への橋

ここで多くの人が「機械検証が通って健全なら、それで良いのでは?」と思います。**これがまさに落とし穴です。**

「Lean モデルに対して真」であることと、「**その Lean モデルが Apyx という現実の設計を正しく写している**」ことは、別のことです。証明はあくまで **モデル内部** の真偽しか保証しません。モデル自体が原典文書からずれていれば、真な定理でも **間違ったことを主張している** ことになります。

査読報告が「perfect 昇格は保留」とした理由はまさにここ——**F1・F2 は証明の穴ではなく、モデルと原典の乖離** です。次章では、この「何に対して正しいのか」という評価軸(**忠実性 / faithfulness**)を厳密に定義します。これが F1/F2 を理解する枠組みそのものになります。
