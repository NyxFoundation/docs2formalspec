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
