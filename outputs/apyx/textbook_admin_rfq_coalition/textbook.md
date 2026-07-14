# admin_rfq_coalition_drains の重大2問題を理解する教科書

> 対象読者: Solidity 実務経験があり、抽象化志向で、金融用語には不慣れ、
> Lean 文法は弱め、Apyx は未知のソフトウェアエンジニア。
>
> 出典: `human_review_admin_rfq_coalition_drains.md`（2026-07-12 人間査読報告）、
> および Lean モデル `D2fsSpecs/Apyx.lean` / `D2fsSpecs/BlastRadius.lean`、
> 原典 `corpus.md` / `SPEC.md` / `model.md`。

---

## 目次

1. 土台を作る — Apyx と、この定理を読むために必要な最小限のモデル
2. 定理を読む — `admin_rfq_coalition_drains` を1行ずつ
3. 「正しい」の二層構造 — 忠実性という評価軸
4. 重大問題1(F1) — RFQ に「ユーザーの依頼」が存在しない
5. 重大問題2(F2) — `catastrophicBackstop` の権限・効果・単位が原典と乖離
6. 統合 — 2つの欠陥が「headline」をどう組み立て、忠実化でどう崩れるか
7. 修正と判断 — witness を直し、簡略化を明記し、なぜ「保留」なのか

---

# 第1章 土台を作る — Apyx と、この定理を読むために必要な最小限のモデル

## 1.0 この教科書のゴール

査読報告 `human_review_admin_rfq_coalition_drains.md` は、`admin_rfq_coalition_drains` という Lean 定理について「**perfect 昇格は保留**」という判断を下しています。その理由の中核が **F1** と **F2** という2つの「重大・忠実性」所見です。

この教科書のゴールは、あなたが **F1 と F2 を、丸暗記ではなく、原理から再導出できる** ようになることです。そのために7章を次のように積み上げます。

| 章 | 問い | 得るもの |
|---|---|---|
| 1(本章) | Apyx とは何か。この定理を読むのに必要な語彙は何か | 最小限のドメインモデル |
| 2 | 定理 `admin_rfq_coalition_drains` は何を主張しているか | 定理本体の逐語的理解 |
| 3 | 「正しい」とは何に対して正しいのか | **忠実性**という評価軸 |
| 4 | F1: RFQ の欠陥 | 重大問題1の完全理解 |
| 5 | F2: backstop の欠陥 | 重大問題2の完全理解 |
| 6 | 2問題は headline 主張をどう壊すか | 統合的な結論 |
| 7 | どう直し、なぜ昇格を保留するのか | 実務判断への接続 |

あなたはスマートコントラクトの実プロダクトを書いたことがあるエンジニアなので、**「仕様と実装の乖離」という概念そのものは既知** のはずです。本質的には、F1/F2 はその一種です。ただし乖離しているのが「Solidity 実装 vs 仕様」ではなく「**Lean モデル vs 原典文書**」であるという、一段抽象化された構図になっている——これが唯一の新しさです。この構図を第3章で厳密にします。

---

## 1.1 ステーブルコインの本質を、いったん徹底的に削ぎ落とす

Apyx を「ステーブルコイン」として学ぼうとすると用語に埋もれます。あなたの抽象化志向に合わせ、まず金融の飾りを全部剥がします。

本質だけ言うと、Apyx は次の2つのトークンを発行する契約群です。

- **apxUSD**: 「1枚 = 約1ドル」を目指すトークン。**支払い手段**。
- **apyUSD**: apxUSD を預けると貰えるトークン。**利息の付く貯金**。時間とともに「1 apyUSD で引き出せる apxUSD 枚数」が増える。

この教科書で問題になる定理は **apxUSD 側だけ** を扱います。apyUSD(貯金・利息・vesting)は F1/F2 と無関係なので、以降ほぼ無視してかまいません。査読報告が「残りは vesting 系ヘルパー」と言って切り捨てているのはこのことです。

さらに削ると、apxUSD について知るべきは次の3つの数量関係だけです。

### 本質1: apxUSD は「準備金」に裏付けられている

契約は USDC(誰もが1ドルと信じる別のトークン)を **準備金(reserve)** として保有します。ユーザーが USDC を預けると、同額の apxUSD が発行(mint)されます。逆に apxUSD を契約に返す(burn する)と、USDC が返ってきます。

```
ユーザー → USDC を預ける → apxUSD をもらう   (発行 / mint)
ユーザー → apxUSD を返す  → USDC をもらう     (返済 / redeem)
```

> 用語注: この教科書では、原典が **redemption** と呼ぶ操作を「**返済**」または「**apxUSD を USDC に戻す**」と言い換えます。金融用語の「償還」と同じですが、本質は「トークンを担保に引き換える」だけです。

### 本質2: 「1枚いくらで返せるか」は固定ではなく、変数である

素朴には「1 apxUSD = 1 USDC で返せる」と思いたくなりますが、**そうではありません**。返済時の価格は `redemptionValue`(返済価格) という **状態変数** で決まります。

```
返ってくる USDC = 返した apxUSD 枚数 × redemptionValue / ray
```

- `ray` は「$1.00」を表す固定小数点の1単位、具体的には `10^27`。Solidity の `1e27` と同じ発想の固定小数点スケールです。
- したがって `redemptionValue = ray` なら「1枚 = 1ドル」、`redemptionValue = 0` なら「1枚 = 0ドル(何も返ってこない)」。

**この `redemptionValue` が攻撃で 0 に落とされる、というのがこの定理の全体像です。** 覚えておいてください。

### 本質3: 準備金には「余剰」がある(overcollateralization)

契約は、発行済み apxUSD を全部返済しても足りるだけの担保、さらにそれ以上の **余剰(buffer)** を持つ設計です。これを **overcollateralization(過剰担保)** と呼びます。

- `totalCollateralValue`(略して tCV): 準備金全体の価値。
- `redemptionValue × 発行済みapxUSD`: 全員が返済したときに支払うべき総額。
- その差 `buffer = tCV − 返済総額`: 余剰。「常に誰にでも見える安全マージン」。

この余剰は「stress(ストレス、市場急変)で減るのではなく、むしろ増やして守る」設計だと原典は言います。この buffer が **F2 で問題になる補償(pro-rata 分配)の対象** です。

---

## 1.2 この定理に登場する「役割(role)」

Apyx は複数の権限(role)を別々の鍵に分けています。Solidity の `AccessControl` の `ADMIN_ROLE` などと同じ発想です。定理に関係するのは主に2つ。

| 役割 | できること(本質) | この定理での立ち位置 |
|---|---|---|
| **admin** | 緊急時操作・パラメータ設定 | 攻撃者A(価格を壊す) |
| **RFQ counterparty**(承認済み相手方) | ユーザーの返済依頼を「執行」する | 攻撃者B(残高を焼く) |

**キーポイント**: 設計思想は「**1つの鍵だけでは資金を奪えない。奪うには複数の鍵の結託(coalition)が要る**」というものです。これを Lean で証明したのが姉妹定理 `single_key_bounds`(単独鍵では抽出額 0)であり、この教科書の主役 `admin_rfq_coalition_drains` は「**2つ結託すると 100% 奪える**」という対になる主張です。

つまり:

```
single_key_bounds        : どの1鍵単独でも  抽出 = 0
admin_rfq_coalition_drains: {admin + RFQ} なら 抽出 = 100%（被害者の全財産）
```

この2つで「鍵分離には価値がある(単独では安全、結託は危険)」という物語を作っています。**F1/F2 は、この「100% 奪える」側の物語が原典より誇張されている、という指摘です。**

---

## 1.3 RFQ とは何か — F1 の主題を先取りする

**RFQ (Request for Quote)** は、直訳すると「見積依頼」です。原典 `corpus.md:381` の説明を本質だけに削ると:

> ユーザーが「返済したい」という **依頼(request)** を出す。承認された相手方(counterparty)が、その **依頼に対して** 競争的な価格で執行する。

構図を図にすると:

```
[ユーザー] --- 返済依頼を提出 ---> [依頼レジストリ]
                                       |
[承認済み counterparty] --- その依頼を執行 ---> ユーザーの apxUSD を焼き、USDC を渡す
```

ここで **決定的に重要な前提** があります。counterparty が執行するのは「**ユーザーが自分の意志で出した依頼**」です。SPEC.md の REQ-rfq-redemption-allowed も "execute **those** requests"(**それらの**依頼を執行する)と、**ユーザー起点** であることを明示しています。

第4章で見るように、Lean モデルの RFQ にはこの「依頼」も「ユーザーの同意」も存在しません。counterparty が `(user, amount)` を **一方的に指定** できてしまう。これが **F1** の核心です。今は「RFQ は本来ユーザー起点のはず」という一点だけ握っておいてください。

---

## 1.4 catastrophicBackstop とは何か — F2 の主題を先取りする

**catastrophicBackstop**(破滅的事態への最終防壁)は、原典 `corpus.md:375` の本質を削ると:

> 破滅的な事態(致命的なハッキング、事業の畳み込み、プロトコル継続不能)において、`redemptionValue` を `totalCollateralValue` に一致させ、**準備金全体(buffer 込み)を残る保有者に按分(pro-rata)で分配する**。

つまり本来の backstop は「最悪でも、残った担保を全員で山分けする」という **救済措置** です。ポイントは2つ:

1. **いつ発動できるか(権限)**: 「破滅的事態の検知」時。`model.md:71` は「Governance emergency flag set(ガバナンスの緊急フラグが立っている)」を前提とする。
2. **何が起きるか(効果)**: 価格を tCV に合わせる **かつ** 準備金を全員に按分分配する。

第5章で見るように、Lean モデルの backstop は (1) admin 単独・無条件で発動でき、(2) 按分分配を **省略** し、(3) 単位の異なる値を直代入して価格を破壊します。これが **F2** の核心です。今は「本来の backstop は救済であって、価格破壊装置ではない」という一点を握ってください。

---

## 1.5 本章のまとめ(次章への橋)

この定理を読むために必要な語彙は、実はこれだけです。

- **apxUSD**: 1ドル目標の支払いトークン。返すと USDC が返ってくる。
- **redemptionValue(返済価格)**: 「1枚いくらで返せるか」を決める変数。`ray` = $1.00。**攻撃でこれが 0 になる**。
- **totalCollateralValue (tCV)**: 準備金全体の価値。
- **buffer(余剰)**: `tCV − 返済総額`。backstop で全員に按分されるべきもの。
- **admin / RFQ counterparty**: 2つの鍵。**単独では奪えない、結託すると奪える**という物語の主役。
- **RFQ**: 本来 **ユーザー起点** の返済依頼執行(→ F1 の欠陥はここ)。
- **catastrophicBackstop**: 本来 **救済措置**(価格一致 + 按分分配)(→ F2 の欠陥はここ)。

次章では、この語彙を使って定理本体を1行ずつ読みます。あなたは Lean の文法には不慣れとのことなので、Solidity との対応を取りながら進めます。


---

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


---

# 第3章 「正しい」の二層構造 — 忠実性という評価軸

第2章の最後で、決定的な区別に触れました。本章はその区別を **抽象化して厳密にする** 章です。F1/F2 はいずれもこの枠組みの中の特定のインスタンスにすぎない、と見えるようになるのが目標です。あなたの抽象化志向に最も直接に応える章です。

---

## 3.1 検証には2つの「正しさ」がある

形式検証(formal verification)には、混同されがちな2つの独立した正しさがあります。

```
        原典文書              Lean モデル              Lean 証明
      (corpus/SPEC/model)  ──①──▶  (State + step)  ──②──▶  (theorem)
         「意図」              「モデル化された意図」        「モデル内の真」

   ①: 忠実性 (faithfulness) —— モデルは意図を正しく写しているか？    ← 人間が査読する
   ②: 健全性 (soundness)    —— 証明はモデル内で本当に正しいか？      ← Lean カーネルが保証する
```

- **②健全性(soundness)**: 「書いた定理が、書いたモデルの中で本当に証明されているか」。これは **Lean カーネルが機械的に保証** します。`sorry` が無く、余計な公理も無く、`lake build` が通れば、②は完璧です。第2章で確認した通り、この定理の②は問題ありません。

- **①忠実性(faithfulness)**: 「書いたモデルが、原典文書(= 設計意図)を正しく写しているか」。これは **機械には判定できません**。なぜなら「原典文書」は自然言語で書かれた人間の意図であり、Lean はそれを読めないからです。**ここだけは人間が査読する必要がある。** これが「人間査読(human review)」の存在理由です。

**F1・F2 はどちらも①(忠実性)の欠陥です。②(健全性)には一切傷がありません。** この一点を取り違えると、査読報告全体を誤読します。

---

## 3.2 Solidity エンジニアの直感で捉え直す

あなたの実務経験に接続します。スマートコントラクト開発で、あなたは常に2種類のバグを相手にしてきたはずです。

| バグの種類 | 例 | Apyx での対応物 |
|---|---|---|
| **実装バグ** | コードがコンパイルされ動くが、書いたロジックが間違っている(オーバーフロー、リエントランシー) | ②健全性の欠陥 —— 今回は **無い** |
| **仕様バグ / 意図の誤解** | コードは書いた通り正しく動くが、**そもそも書くべきものが間違っていた**(要件を読み違えた) | ①忠実性の欠陥 —— **F1/F2 はこれ** |

F1/F2 は後者、「**そもそもモデル化した対象が原典とずれている**」タイプです。コード(Lean 証明)は完璧に動く。しかし写した対象(RFQ の挙動、backstop の挙動)が原典と食い違う。あなたが「要件定義書を読み違えたまま完璧に実装してしまった PR」をレビューするときの感覚が、まさにこの査読の感覚です。

---

## 3.3 「モデル簡略化(simplification)」は悪ではない — 悪いのは「隠された簡略化」

ここは公平を期すために重要です。**モデルは必ず現実を簡略化します。** 現実の全てを写したモデルは現実そのものであり、検証の意味がありません。だから簡略化それ自体は正しい行為です。

問題は簡略化そのものではなく、**簡略化が明示されているか** です。査読報告の判定要旨(10行目)を、この枠組みで読み直します。

> 「その注記が定理の docstring / formalMeta に一切ないため承認しない」

つまり査読者の論理はこうです:

```
簡略化がある             → それ自体は許容
簡略化が docstring に明記 → 読者は騙されない → 許容
簡略化が明記されず、
  かつ headline 主張が
  その簡略化に依存している → 読者が誤解する    → 却下
```

F1/F2 が却下される理由は「簡略化したから」ではなく、「**headline 主張(唯一の全損経路、2鍵で 100%)が、明記されていない簡略化に依存しているから**」です。この区別は第6章の結論に直結します。

実際、SPEC.md の他の箇所を見ると、モデル作者は簡略化を明記できるときはしています。例えば `model.md:82` の vesting の説明は「*(Model simplification vs contract: ... a documented remaining approximation.)*」と、簡略化を **括弧で明示** しています。**やればできるのに、RFQ と backstop についてはやっていない**——査読者はこの非対称を突いています。

---

## 3.4 忠実性を評価する「3点セット」= 原典の3層

忠実性を査読するには、「何と照合するのか」を確定する必要があります。Apyx では原典が3つのファイルに層状になっています。

| ファイル | 役割 | 抽象度 |
|---|---|---|
| `corpus.md` | 製品ドキュメント原文(GitBook をそのまま集めたもの) | 最も生・自然言語 |
| `SPEC.md` | 要件を `REQ-xxx` として構造化した仕様書 | 中間・半形式 |
| `model.md` | 各操作を「前提条件 / 効果」の表にした準形式モデル | 最も形式に近い |

忠実性査読は「Lean モデルが、この3層と整合するか」を各操作について照合する作業です。第4章(F1)と第5章(F2)は、まさにこの照合を RFQ と backstop について実行します。**照合の型は毎回同じ**なので、先に型だけ抽象化しておきます。

```
照合の型:
  1. 原典3層が何を要求しているかを引用する（corpus / SPEC / model）
  2. Lean モデルが実際に何をしているかを step の該当分岐から読む
  3. 差分を取る
  4. その差分が headline 主張の成立に「効いている」かを判定する
       効いている  → 重大（F1/F2 は重大）
       効いていない → 軽微
```

第4・5章はこの4ステップを機械的に踏むだけです。あなたが「あらゆる物事を本質に注目して抽象化する」タイプなら、以降の章は **この1つの型の2つのインスタンス** として読めます。

---

## 3.5 査読の「対象範囲」はどう決まったか — typeReachableOnly

もう一つ、忠実性査読を実務にするために必要な概念があります。「**73 ノードのうち、どれを人間が読むべきか**」という範囲決定です。査読報告の「査読方法」節がこれを説明しています。抽象化して要点だけ:

- Lean モデルには定理・定義が大量にあります。全部を人間が読むのは非現実的。
- そこで「**この定理の真偽に実際に効く定義だけ**」に絞る。これが Web ビューワーの「人間検証対象のみ表示(typeReachableOnly)」というフィルタで、CLI で再現された。
- 具体的には、証明の中身をたどるエッジ(`theorem_value_to_definition` 等)を **除外** し、「型・仕様として効く」依存だけをたどる。
- 結果、**検証対象は 73 ノード**。うち定理の真偽に本当に負荷がかかるのは `State`(+射影)、`Op`、`step` の該当2分岐、`burnApxUSD`、`ray` の6種。残りは無関係な vesting 系ヘルパー。

**なぜこれが重要か**: F1 は `step` の `executeRFQRedemption` 分岐、F2 は `catastrophicBackstop` 分岐 —— まさにこの「真偽に効く6種」の中にあります。査読が的を絞れているのは、この範囲決定のおかげです。この教科書が第2章で `step` の2分岐だけを精読したのも、同じ理由です。

---

## 3.6 本章のまとめ(次章への橋)

- 検証の正しさは2層:**②健全性**(機械が保証、今回は完璧)と **①忠実性**(人間が査読、F1/F2 はここ)。
- F1/F2 は「実装バグ」ではなく「**意図の誤写**」。あなたの言葉なら「要件を読み違えたまま完璧に実装した」タイプ。
- 簡略化は悪ではない。悪いのは「**明記されず、かつ headline 主張がそれに依存する**」簡略化。
- 忠実性査読の型は毎回同じ4ステップ(原典を引く → モデルを読む → 差分 → headline への効き)。
- 対象範囲は「定理の真偽に効く定義」に絞られ、F1/F2 はその中心にある。

準備は整いました。次章から、この4ステップの型を **RFQ(F1)** に適用します。


---

# 第4章 重大問題1(F1) — RFQ に「ユーザーの依頼」が存在しない

第3章の4ステップの型(原典を引く → モデルを読む → 差分 → headline への効き)を、RFQ に適用します。これが F1 の完全な解剖です。

---

## 4.1 ステップ1: 原典3層は RFQ に何を要求しているか

3層すべてが「**RFQ はユーザー起点である**」と言っています。証拠を並べます。

**corpus.md:381(製品原文):**
> Users may submit redemption requests … allowing approved counterparties to provide competitive execution

分解すると2つの動詞と2つの主語:
- **ユーザーが** 返済依頼を **submit(提出)** する
- **承認された相手方が** 執行を **provide(提供)** する

**SPEC.md の REQ-rfq-redemption-allowed(要件):**
> The system MUST allow users to submit redemption requests through the RFQ process and MUST permit only approved counterparties to execute **those** requests.

キーワードは **"those"**。「**それらの**(= ユーザーが提出した)依頼を執行する」。相手方が執行できるのは、宙に浮いた任意の依頼ではなく、**ユーザーが自分で出した特定の依頼** です。

**model.md:68(準形式モデル):**
> | executeRFQRedemption | user, amount | msg.sender ∈ approved RFQ counterparties ∧ **whitelist[user]** | Burn amount apxUSD from user; transfer USDC ... |

ここで注目すべきは前提条件に **`whitelist[user]`** がある点。model.md は「執行対象の user は whitelist に載っていなければならない」と要求しています(この点は第7章の F3 で再登場します)。

**原典が描く本来の RFQ の構図:**

```
[ユーザー] ──① 依頼を提出(私の apxUSD を返済したい)──▶ [依頼レジストリ]
                                                          │ 依頼が記録される
                                                          ▼
[承認済み counterparty] ──② レジストリにある依頼を執行──▶ 執行
```

**本質**: counterparty の権限は「**ユーザーが同意して出した依頼を代わりに処理する**」という **委任(delegation)** です。counterparty は勝手にユーザーの残高に触れません。あくまでユーザーの意志が起点にある。

---

## 4.2 ステップ2: Lean モデルの RFQ は実際に何をするか

`step` の該当分岐(`Apyx.lean:706`)を再掲します。

```lean
| Op.executeRFQRedemption user amount =>
    -- only approved RFQ counterparties may execute a user's redemption request
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

ガードを1つずつ点検します。**「ユーザーの意志」がどこにあるか** を探しながら読んでください。

| ガード | チェック内容 | ユーザーの意志は? |
|---|---|---|
| `globalPause` | 一時停止していないか | 無関係 |
| `¬ rfqCounterparties.contains caller` | 呼び出し者が承認済み相手方か | 相手方の資格のみ |
| `apxUSDBal user < amount` | 対象ユーザーの残高が足りるか | **残高チェックのみ。同意ではない** |
| `usdcReserve < usdcAmount` | 準備金が足りるか | 無関係 |

**決定的な発見**: この4ガードのどこにも「**ユーザーが依頼を出したか**」を確認する処理がありません。

- **依頼レジストリが存在しない。** 原典の「submit した依頼」を記録する場所がモデルに無い。
- **同意チェックが存在しない。** `user` はただの引数で、`caller`(相手方)が **好きなアドレスと好きな金額を一方的に指定** できる。
- 皮肉なことに、分岐冒頭のコメント自身が `-- only approved RFQ counterparties may execute a user's redemption request`(ユーザーの**返済依頼**を執行する)と書いています。**コメントは「依頼」を前提しているのに、コード上その依頼はどこにも検査されていない。** コメントと実装の乖離が、そのまま原典との乖離になっています。

Solidity で書き直すと、乖離が一目瞭然です。

```solidity
// 原典が要求するもの（本来あるべき姿）
function executeRFQRedemption(uint256 requestId) external onlyCounterparty {
    Request memory r = requests[requestId];   // ← ユーザーが submit した依頼を引く
    require(r.exists, "no such request");      // ← 依頼の存在チェック
    _burn(r.user, r.amount);                   // 依頼の内容通りに執行
    // ...
}

// Lean モデルが実際にやっていること
function executeRFQRedemption(address user, uint256 amount) external onlyCounterparty {
    // requestId も requests マッピングも存在しない
    // user と amount を counterparty が任意に指定できる
    require(balanceOf[user] >= amount);        // 残高チェックだけ
    _burn(user, amount);                       // ユーザーの同意なしに焼却
    // ...
}
```

**モデルの RFQ は、実質「承認済み相手方による、任意ユーザーに対する強制返済」** になっています。これは委任ではなく **収奪の権限** です。

---

## 4.3 ステップ3: 差分を取る

| 観点 | 原典3層 | Lean モデル | 差分 |
|---|---|---|---|
| 起点 | ユーザーの提出(submit) | 相手方の一方的指定 | **ユーザー起点が消えている** |
| 依頼レジストリ | 存在(submit された依頼を記録) | 無し | **レジストリが無い** |
| 同意 | 必要(そのユーザーの依頼) | 不要(任意 user を指定) | **同意チェックが無い** |
| 対象の制約 | `whitelist[user]`(model.md:68) | 無し | **whitelist ガードも欠落** |

差分の本質を1文で: **モデルは「ユーザーが返済したいという意志」を完全に落とし、counterparty が誰の apxUSD でも焼ける権限として RFQ をモデル化している。**

---

## 4.4 ステップ4: この差分は headline 主張に効くか — **決定的に効く**

ここが F1 を「重大」たらしめる核心です。

この定理の全損経路は、**「被害者が何もしていないのに焼却される」** ことに立脚しています。第2章の witness を思い出してください: 被害者(アドレス 0)は 100 apxUSD を持っているだけで、**依頼を出す step が証明に一切登場しません**。攻撃は「admin が価格を壊す → 相手方が被害者を勝手に焼く」の2手だけ。被害者は完全に受動的です。

もしモデルが原典に忠実で「依頼レジストリ + 同意」を持っていたら、攻撃は成立しません。なぜなら:

```
忠実なモデルでは:
  相手方が executeRFQRedemption を呼ぶには、
  被害者がすでに「返済依頼」を submit している必要がある。
  → 依頼を出していない被害者は、そもそも焼かれない。
  → 「何もしていない被害者が全損する」という headline が崩れる。
```

査読報告(28行目)がこう縮小させている通りです:

> 文書忠実なモデルでは、主張は「**未執行の RFQ 依頼を持つユーザーは執行時点の暴落価格を適用される**」という、実在するがより狭いリスクに縮小する。

つまり忠実なモデルでの真の主張は:

```
現モデルの主張（誇張）:  誰でも、何もしていなくても、全損する
    ↓ 忠実化すると
本来の主張（正確）:      「返済依頼を出して待っている」ユーザーだけが、
                          執行された瞬間に暴落後の価格を適用されて損する
```

この2つは **リスクの質が全く違います**。

- 前者は「プロトコルに触れてすらいない一般保有者が、コインを持っているだけで狙われる」という **無差別・受動的な全損**。
- 後者は「返済プロセスに自ら乗った(依頼を出した)ユーザーが、タイミングの悪さで暴落価格を掴まされる」という **限定的・能動的なリスク**。実在はするが、対象も条件も遥かに狭い。

headline は前者を主張しています。しかし原典に忠実なら後者しか言えません。**差分が headline の適用範囲を「全保有者」から「返済待機中のユーザー」へと劇的に狭める** —— だから重大なのです。

---

## 4.5 パイプラインの過去レビューとの整合

査読報告(36行目)は、この所見が単独の意見ではないことを補強しています。

> パイプラインの過去レビュー(review_run1–3)も `rfq-redemption-allowed` を … "partial" と全会一致で判定

実際、`review_run1.json` の該当エントリの note を見ると:

> "The theorem captures the 'only approved counterparties may execute' clause, but **only provides a sufficient condition for success rather than guaranteeing that every valid user redemption request is allowed**, and adds extra preconditions not stated in the requirement."

過去レビューの指摘は「REQ-rfq-redemption-allowed の要件は2部構成(① ユーザーが依頼を出せる ② 承認相手方だけが執行できる)なのに、モデルは②の片側だけを、しかも十分条件の形でしか捉えていない」というもの。**①「ユーザーが依頼を submit できる」という半分がモデルに存在しない**——これは F1 と完全に同じ穴を、別角度から指摘しています。人間査読(F1)と自動レビュー(partial)が独立に同じ結論に達している点が、F1 の信頼度を高めています。

---

## 4.6 本章のまとめ(次章への橋)

F1 を4ステップの型で解剖しました。

1. **原典**: RFQ はユーザー起点。相手方は「ユーザーが submit した依頼」だけを執行する委任。
2. **モデル**: 依頼レジストリも同意チェックも無い。相手方が任意 user・任意 amount を強制返済できる。
3. **差分**: ユーザーの意志が完全に欠落。委任が収奪に化けている。
4. **効き**: headline の「何もしていない被害者が全損」は、この欠落があって初めて成立する。忠実化すると「返済依頼を出して待っているユーザーが暴落価格を掴む」という遥かに狭いリスクに縮小する。

F1 は「攻撃の **入口**(誰の残高を焼けるか)」の忠実性欠陥でした。次章の F2 は「攻撃の **前段**(価格をどう 0 に落とすか)」の忠実性欠陥です。2つが合わさって初めて全損経路が完成する——その合流点が第6章です。


---

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


---

# 第6章 統合 — 2つの欠陥が「headline」をどう組み立て、忠実化でどう崩れるか

第4章(F1)と第5章(F2)を個別に解剖しました。本章は、その2つを **合流させ**、この定理が掲げる最も強い主張——docstring と formalMeta の headline——が、どのように成立し、どのように崩れるかを統合します。あなたの抽象化志向に向けて、「攻撃連鎖の合成」という1つの構造として提示します。

---

## 6.1 headline 主張を正確に取り出す

まず、この定理が「何を主張していることになっているか」を原文から確定します。3か所にあります。

**docstring(`BlastRadius.lean:2646`):**
> **the worst coalition, quantified: `{admin, RFQ-counterparty}` inflicts 100% loss.**

**formalMeta(`BlastRadius.lean:2669`):**
> "The **one structural total-loss path**, machine-checked: a compromised admin crashes redemptionValue to 0 via catastrophicBackstop, then an approved RFQ counterparty burns the victim's entire apxUSD for 0 USDC — 100% **uncompensated** loss, **requiring two colluding roles**."

査読報告(10行目)が問題視する「mainTheorem として掲げる主張」を分解すると、4つの強い言明が含まれています。

| # | 言明 | 依存する欠陥 |
|---|---|---|
| H1 | 「**唯一の**構造的全損経路」(the one structural total-loss path) | F1 + F2 の合成が前提 |
| H2 | 「**2鍵で足りる**」(requiring two colluding roles) | F2(a): admin 単独・無条件 |
| H3 | 「**無補償**の全損」(uncompensated) | F2(b): 補償脚の省略 |
| H4 | 「被害者の全 apxUSD を焼く」(何もしていない被害者) | F1: 依頼・同意の欠落 |

**この4つがすべて、第4・5章で見た隠れた簡略化に依存しています。** headline は「証明された事実」の顔をしていますが、実際には「特定のモデル化選択の帰結」です。

---

## 6.2 攻撃連鎖を1つの合成として見る

2つの欠陥がどう連鎖して全損を作るかを、1本の因果連鎖として描きます。

```
             ┌─────────────── F2 が支える前段 ───────────────┐
             │                                                │
  [admin]───▶ catastrophicBackstop を単独・無条件で発動        │  ← F2(a): 権限
             │   redemptionValue := totalCollateralValue      │  ← F2(c): 単位ミスで
             │   → 価格が 0 に落ちる                            │        健全でも0に
             │   （按分分配は起きない）                         │  ← F2(b): 補償脚の省略
             └────────────────────┬───────────────────────────┘
                                   │ redemptionValue = 0 の状態
             ┌─────────────────────▼─────────── F1 が支える入口 ──┐
             │                                                     │
  [RFQ]──────▶ executeRFQRedemption(victim, 100) を一方的に指定    │  ← F1: 依頼・同意なし
             │   burnApxUSD(victim, 100)  → apxUSD 100→0           │
             │   usdc = 100 × 0 / ray = 0 → USDC 0 のまま           │
             └─────────────────────┬───────────────────────────────┘
                                   ▼
                    victim: apxUSD = 0, USDC = 0  ← 無補償の全損
```

この図から見える本質:

- **F2 は「価格をどうやって 0 にするか」を担う前段。** admin 単独で発動でき(a)、按分分配なし(b)、健全でも価格破壊(c)。
- **F1 は「その 0 価格で、誰の残高を焼けるか」を担う入口。** 依頼も同意も要らないので、任意の被害者を選べる。
- **2つが直列に合成されて初めて「何もしていない被害者の無補償全損」が完成する。** どちらか一方でも忠実化すれば、連鎖は途切れます。

---

## 6.3 忠実化すると headline はどう崩れるか — 4つの言明を順に潰す

第3章の「差分が headline に効くか」を、H1〜H4 それぞれについて実行します。

### H4「何もしていない被害者の全損」の崩れ(F1 忠実化)

RFQ に依頼レジストリと同意を戻すと(第4章):

```
被害者が「返済依頼」を submit していなければ、executeRFQRedemption は失敗する。
→ 依頼を出していない一般保有者は焼かれない。
→ H4「何もしていない被害者」が成立しない。
→ 残るのは「返済依頼を出して待っているユーザーが暴落価格を掴む」という狭いリスク。
```

### H3「無補償」の崩れ(F2(b) 忠実化)

backstop に補償脚(按分分配)を戻すと(第5章):

```
準備金全体が残る保有者に按分分配される。
→ 準備金が非空なら、被害者は分配分を受け取る。
→ H3「uncompensated」が成立しない(部分補償になる)。
```

### H2「2鍵で足りる」の崩れ(F2(a) 忠実化)

backstop の発動条件を「ガバナンス緊急フラグが前提」に戻すと(第5章):

```
admin1人では緊急フラグを前提にできない。ガバナンスの関与が要る。
→ 必要な鍵は {admin, RFQ, ガバナンス} の3つになりうる。
→ H2「requiring two colluding roles(2鍵)」が成立しない。
```

### H1「唯一の構造的全損経路」の崩れ(H2〜H4 の帰結)

H1 は最も強く、最も脆い言明です。「唯一(the one)」と「構造的全損(structural total-loss)」の両方が、上の3つの成立に寄りかかっています。

```
H4 が崩れる → 全損の対象が「全保有者」から「返済待機ユーザー」に狭まる
H3 が崩れる → 「全損」が「部分損」に弱まる（準備金非空時）
H2 が崩れる → 「2鍵の経路」ではなくなる（3鍵かもしれない）
────────────────────────────────────────────────
∴ H1「2鍵による唯一の構造的無補償全損経路」は、忠実なモデルでは
   そのままの形では主張できない。より狭く・より弱い主張に置き換わる。
```

---

## 6.4 「真な定理が、間違ったことを主張する」という現象の正体

ここで第3章の枠組みに戻ります。この定理は **②健全性は完璧** です。Lean カーネルは「モデル内でこの存在証明は正しい」と保証しています。それは今も揺らぎません。

崩れたのは **①忠実性** です。モデルが写しているつもりの Apyx と、実際の Apyx(原典)がずれている。だから:

```
定理が証明しているもの: 「このモデルの中では、2鍵で無補償全損が起きる」← 真
headline が主張するもの: 「Apyx では、2鍵で無補償全損が起きる」        ← 忠実性ゆえに過大
```

**この2つのギャップこそが F1/F2 の正味の害です。** 証明は嘘をついていません。嘘をついているのは「モデル = Apyx」という **暗黙の等号** です。そしてその等号が成り立たない(F1/F2)ことは、docstring にも formalMeta にも一切書かれていない。読者は「Apyx について 2鍵で 100% 全損が証明された」と誤読します。

査読報告(10行目)の判定要旨がまさにこれを言っています:

> mainTheorem として掲げる「プロトコルの唯一の構造的全損経路」という主張は、原典文書と食い違うモデル簡略化3点に依存しており、その注記が定理の docstring / formalMeta に一切ないため承認しない。

---

## 6.5 なぜ「mainTheorem」であることが問題を増幅するか

最後に、なぜこの定理が特別扱いされるのかを押さえます。この定理には `mainTheorem` 属性が付いています(`BlastRadius.lean:2670`)。

- `mainTheorem` は「これがこの検証の **看板** です」というマーク。Lean Atlas のビューワーで最上位に表示され、「Apyx についてこれが証明された」と読者に提示されます。
- 補題や中間結果なら、多少の簡略化は文脈で許容されます。しかし **看板の定理は、その主張が額面通り受け取られる**。だから看板ほど忠実性の基準が厳しくなる。

つまり同じ F1/F2 でも、それが **看板 headline の成立に直結している** から重大なのです。もしこれが「返済待機ユーザーのタイミングリスク」という控えめな補題だったら、F1/F2 の一部は「明示された簡略化」で済んだかもしれません。**過大な看板が、隠れた簡略化を「誇張」に変えている** —— これが第6章の統合的結論です。

---

## 6.6 本章のまとめ(次章への橋)

- headline は4つの強い言明(H1 唯一の全損経路 / H2 2鍵 / H3 無補償 / H4 何もしていない被害者)から成る。
- そのすべてが F1・F2 の隠れた簡略化に依存する。F1 が入口(誰を焼けるか)、F2 が前段(価格を 0 にする権限・補償・単位)を担い、直列合成で全損が完成する。
- 忠実化すると H1〜H4 は順に崩れ、「返済待機ユーザーが暴落価格を掴む、部分補償されうる、鍵が3つ要るかもしれないリスク」という遥かに狭い主張になる。
- ②健全性は無傷。壊れているのは「モデル = Apyx」という暗黙の等号(①忠実性)。それが docstring に明記されていないから却下。
- `mainTheorem`(看板)であることが、この誇張を許容できないものにしている。

次章では、この診断を **どう直すか** に移ります。F3(witness 品質)の具体的修正、docstring への簡略化明記、そして「なぜ perfect ではなく high に留めるのか」という最終判断の論理を、実務の意思決定として締めくくります。


---

# 第7章 修正と判断 — witness を直し、簡略化を明記し、なぜ「保留」なのか

前章までで F1/F2 の診断は完了しました。最終章は「では、どう直すのか」「なぜ perfect に昇格させず high に留めるのか」という **意思決定** に接続します。ここまで理解したあなたなら、査読報告の推奨アクションが単なる指示ではなく、必然の帰結として読めるはずです。

まず、まだ触れていなかった第3の所見 F3(と軽微な F4)を片付け、その後に統合判断へ進みます。

---

## 7.1 F3(中・witness 品質) — 「証人」が非現実的で、docstring の反実仮想が偽

F1/F2 が「モデルの忠実性」の問題だったのに対し、F3 は「**witness(証人)の品質**」の問題です。第2章で見た `coalWitness` を再掲します。

```lean
private def coalWitness : State :=
  { (default : State) with
      admin := 1
      rfqCounterparties := [2]
      apxUSDBal := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      totalCollateralValue := 0 }
```

`default` を土台にしているので、明示されていないフィールドはすべてゼロ値です。ここに2つの不整合が潜んでいます。

### 問題1: 台帳の不整合(到達不能な状態)

- `apxUSDBal 0 = 100`(被害者は 100 apxUSD 保有)
- しかし `totalSupply_apxUSD` は明示されていないので **0**(default)

これは矛盾です。「誰かが 100 枚持っているのに、発行総数は 0」という状態は、正常な操作列では **決して到達できません**(mint すれば totalSupply も増えるはず)。査読報告(43行目)の「台帳不整合で到達不能な状態」です。

**なぜ問題か**: witness は「この攻撃が **実際に起こりうる** 状態で成立する」ことを示すためのもの。到達不能な状態を witness にすると、「現実には起こらない状況でしか成立しない攻撃」を証明しているように見えてしまい、証拠としての説得力が落ちます。

### 問題2: docstring の反実仮想が偽

docstring(`BlastRadius.lean:2651`)はこう書いています:

> the victim could redeem 100 apxUSD for 100 USDC

これは「攻撃さえなければ被害者は 100 apxUSD を 100 USDC に返済できたはずだ(だから 100 の損失は本物だ)」という **反実仮想(counterfactual)** です。損害の大きさを正当化する重要な一文。

ところが witness 上ではこの反実仮想が **偽** です。攻撃前の状態で被害者が本当に返済できるか確かめると:

- `usdcReserve = 0`(default)→ 準備金が空なので、返済しようにも渡す USDC が無い。
- victim(アドレス 0)は非 whitelist(default の whitelist は全員 false)→ `redeemApxUSD`(`Apyx.lean:584`)の whitelist ガードで弾かれる。

`redeemApxUSD` のガードを確認:

```lean
| Op.redeemApxUSD amount =>
    if s.globalPause then none
    else if ¬ s.whitelist caller then none          -- ← victim は非whitelist → ここで失敗
    else if ray ≤ s.apxUSDMarketPrice then none
    else if s.apxUSDBal caller < amount then none
    else
      let usdcAmount := (amount * s.redemptionValue) / ray
      if s.usdcReserve < usdcAmount then none         -- ← reserve=0 でも失敗しうる
      ...
```

**「攻撃がなければ 100 USDC 返済できた」は、この witness では成立しません。** 被害者は whitelist にもいないし、準備金も空。査読報告(45行目)の「docstring の反実仮想は witness 上では偽」です。損害の正当化が、実は成り立っていない。

### F3 の修正案(声明は不変)

査読報告(47行目)の修正案は明快です。witness に次を追加:

```lean
private def coalWitness : State :=
  { (default : State) with
      admin := 1
      rfqCounterparties := [2]
      apxUSDBal := fun a => if a = 0 then 100 else 0
      redemptionValue := ray
      totalCollateralValue := 0
      totalSupply_apxUSD := 100      -- ← 追加: 台帳整合(被害者の100枚が発行総数と一致)
      usdcReserve := 100             -- ← 追加: 準備金を用意
      whitelist := (· = 0) }         -- ← 追加: 被害者を whitelist に(反実仮想を真に)
```

- `totalSupply_apxUSD := 100`: 台帳整合が取れ、到達可能な状態になる。
- `usdcReserve := 100`: 準備金が存在するので反実仮想の返済が現実味を持つ。
- `whitelist := (· = 0)`: 被害者(アドレス 0)を whitelist に載せる。`(· = 0)` は「引数が 0 なら true」を返す関数(`fun a => a = 0` の略記)。これで `redeemApxUSD` の whitelist ガードを通過し、反実仮想「攻撃なければ返済できた」が真になる。

**決定的な点**: 定理は `∃`(存在証明)なので、witness をどう作り替えても **声明そのものは1文字も変わりません**。変わるのは「どの具体例で存在を示すか」だけ。証明本体の微修正で済みます。あなたが第2章で握った「存在証明は具体例を1つ挙げれば済む」がここで効いています。

さらに副産物として、修正後は攻撃の鋭さが増します。査読報告(47行目):「reserve = 100 なら『**価値がリザーブに残っているのに被害者は 0 を受け取る**』というより鋭い形になる」。準備金が空だと「そもそも返せる原資が無かった」と言い訳できますが、準備金 100 があるのに 0 しか返らないなら、収奪であることがより明白になります。

### F3 と F1 の交差点(model.md:68 の whitelist ガード)

F3 の修正で `whitelist := (· = 0)` を入れるのには、もう一つ F1 と絡む理由があります。第4章で見た通り、model.md:68 は executeRFQRedemption の前提に `whitelist[user]` を要求していますが、**Lean の RFQ 分岐にはこの whitelist ガードがありません**。

つまり文書忠実なら、被害者が非 whitelist の現 witness では **第2ステップ(RFQ 執行)自体が失敗するはず** です。査読報告(45行目):「文書忠実なら現 witness の第 2 step 自体が失敗する」。被害者を whitelist に載せる修正は、この忠実性ギャップの影響も同時に打ち消します。ただしこれは「victim を whitelist すれば直る」ので、**真偽の問題ではなく忠実性の問題** に分類されています(F3 が「中」に留まる理由)。

---

## 7.2 F4(軽微・表現) — formalMeta の "requiring" は過大

formalMeta(第6章 H2)の "requiring two colluding roles(2つの結託役割を **要する**)" という表現の指摘です。

この定理が実際に証明しているのは、結託の **十分性** だけです:「{admin, RFQ} が **あれば** 全損できる」。しかし "requiring(要する)" は **必要性** —「単独鍵では抽出 0(2つ **なければ** 奪えない)」も含意します。

必要性を担っているのは **姉妹定理 `single_key_bounds`** の方です(第1章参照)。この定理単体は必要性を証明していません。だから "requiring" は、この定理1つの守備範囲を超えた過大表現。査読報告(51行目):「summary の 'requiring' は過大表現」。

**修正は表現だけ**(例: "achievable by two colluding roles" 等)で、証明にもモデルにも影響しません。だから「軽微」。

---

## 7.3 4所見を1枚に整理する

| 所見 | 種別 | 重大度 | 本質 | 修正 |
|---|---|---|---|---|
| **F1** | 忠実性 | 重大 | RFQ にユーザーの依頼・同意が無い。委任が収奪に化ける | docstring に「RFQ 依頼はモデル外」と明記 |
| **F2** | 忠実性 | 重大 | backstop の権限(a)・補償脚(b)・単位(c)が原典と乖離 | docstring に3点の簡略化を明記 |
| **F3** | witness 品質 | 中 | witness が非現実的(台帳不整合)で反実仮想が偽 | witness に3フィールド追加(声明不変) |
| **F4** | 表現 | 軽微 | "requiring" が必要性を含意する過大表現 | 文言修正のみ |

**重大度の並びには論理があります**: F1/F2 は「**看板 headline の正しさ**」に直結する忠実性(第6章)。F3 は「証拠(witness)の質」で headline の文言(反実仮想)に関わるが真偽は揺らがない。F4 は文言だけ。上に行くほど「主張そのものの妥当性」に、下に行くほど「表現の精度」に関わります。

---

## 7.4 良い点も正しく評価する — なぜ「high」なのか

査読報告は却下一辺倒ではありません。「良い点」節(53-57行)で、この定理の質の高さを認めています。

- **声明が自己完結**: 7つの条件(`0 < amount`、事前残高 = amount、事前・事後 USDC = 0、事前価格 ≥ ray、counterparty 承認、両 step 成功、事後残高 0)がすべて意図通りに配置されている。第2章で追った通り、抜けも過剰もない。
- **手計算と証明の一致**: `step` の2分岐と witness の追跡が証明と完全一致(第2章で私たちも追った)。
- **「モデル内の主張」としての質は高い**: ②健全性は完璧。

だから査読報告の判定は「**却下(reject)」ではなく「保留(confidence high に留める)**」です。ここが本質的に重要:

```
confidence perfect = 「Apyx についての主張として、額面通り信頼してよい」
confidence high    = 「モデル内の主張としては信頼できる。ただし原典との対応に注記が要る」
```

この定理は後者。**証明として優れているが、看板として掲げるには忠実性の注記が足りない。** だから「high は十分に妥当、しかし perfect はまだ」。査読報告(57行目):「『モデル内の主張』としての品質は高く、`confidence high` 相当の信頼性は十分にある。」

---

## 7.5 昇格の前提 — 3つのアクションの論理

査読報告(59-63行)の推奨アクションを、ここまでの理解で「なぜそれが必要か」まで含めて読み直します。

1. **F3 の witness 修正(声明不変)**
   → 証拠を到達可能・現実的にし、反実仮想を真にする。第7.1節の3フィールド追加。声明が変わらないので低リスク。

2. **docstring / formalMeta に前提を明示する**
   → 3つの簡略化を明記:
   - 「RFQ 依頼はモデル外」(F1 への対応)
   - 「backstop は admin 単独トリガー仮定」(F2(a) への対応)
   - 「pro-rata 分配は省略」(F2(b) への対応)

   これが最重要。第3章で確立した通り、**簡略化は悪ではない。明記されない簡略化が headline を誇張にすることが悪**。明記すれば、読者は「これはモデルの簡略化下での主張だ」と理解でき、②健全性の高さがそのまま活きる。

3. **その上で再査読 → perfect 昇格**
   → 1・2 で忠実性の注記が整えば、「モデル = Apyx」の暗黙の等号が「明示された簡略化つきの対応」に置き換わり、看板として掲げられる。

**論理の骨格**: F1/F2 は「モデルを原典に一致させろ」とは要求していません(それは大改修で、時に検証上不要)。要求しているのは「**簡略化を隠すな、明記しろ**」です。これは第3章の中心命題そのもの。修正は数行の docstring 追記と witness の微修正で足り、証明本体はほぼ触らずに済みます。**低コストで忠実性の透明性を回復できる**——だから「却下」ではなく「保留 + 明確な昇格パス」なのです。

---

## 7.6 教科書全体の結論 — あなたが持ち帰るべき1つの構造

7章を通じて、F1/F2 という2つの重大問題を原理から再構成しました。最後に、全体を1つの抽象構造として畳みます。

```
【この定理の状態】
  ②健全性  = 完璧（Lean カーネルが保証。sorry なし、標準3公理のみ）
  ①忠実性  = 3点の隠れた簡略化により、看板 headline が原典より誇張
              ├─ F1: RFQ にユーザーの依頼・同意が無い（攻撃の入口を無差別化）
              └─ F2: backstop の 権限・補償・単位 が原典と乖離（攻撃の前段を過大化）

【誇張の中身】
  headline「2鍵による唯一の無補償全損経路」は、F1+F2 の合成の産物。
  忠実化すると「返済待機ユーザーが暴落価格を掴む、部分補償されうる、
                鍵が3つ要りうる」という遥かに狭いリスクに縮小する。

【判断】
  却下ではなく保留（confidence high）。証明の質は高い。
  昇格には「モデルを直す」のではなく「簡略化を docstring に明記する」だけでよい。
  = 隠れた簡略化を、明示された簡略化に変える。
```

あなたがスマートコントラクト開発で日々やっている「仕様と実装の照合」が、ここでは「**原典文書と形式モデルの照合**」という一段抽象化された舞台で行われている——それだけのことです。証明が正しくても、証明している対象が意図とずれていれば、主張は誤りうる。形式検証の価値は健全性(②)だけでなく忠実性(①)にも等しく宿り、後者は人間にしか査読できない。この定理は②で満点を取りながら①で注記を要する、という **形式検証の2層構造を最も鮮明に示す教材** でした。


---

