# ApyxをLeanで検証する

> 仕様を状態機械に写し、残高・償還・特権鍵の境界を定理にする。

仕様を状態機械に写すと、残高の保全、償還の待機、特権鍵の被害範囲を一つずつ検証できる。けれども、証明の強さは定理の数では決まらない。どの状態を表し、どの操作列を許し、どこまで実装に合わせているかで決まる。

Apyxの検証レポートは、公開文書と確認した実装をLeanで扱えるモデルに落とし、そのモデルについて定理を証明したものだ。Solidity bytecodeそのものを証明したものではない。`lake build`が成功しても、「Apyxは安全だ」と直ちに結論づけることはできない。モデルの中に何があり、何がないのかを確かめて、初めて個々の定理の意味が見えてくる。

---

## 1. Apyxの資産と償還の仕組み

Apyx で中心になる資産は、`USDC`、`apxUSD`、`apyUSD`、そして償還待ちの receipt である。

- `USDC` は担保・準備資産として使われる
- `apxUSD` はドルに連動する基礎トークンである
- `apyUSD` は vault の持分を表す share token で、保有中に利回りが反映される
- `apxUSD_unlock` は、すぐには換金できない償還請求を表す

利用者の操作を並べると、次のようになる。

```text
USDC を預ける
  → apxUSD を受け取る
  → apyUSD vault に預ける
  → apyUSD share を受け取る
  → 償還を申請する
  → cooldown の間待つ
  → receipt を claim する
  → apxUSD または USDC を受け取る
```

この流れを見ると、単に「入金すればトークンが増える」だけでは足りないことが分かる。pause や denylist はすべての残高移動を止めるのか。利回りは早取りできないのか。請求を別人に奪われないか。待っている間に価格が変わったら、誰がその影響を受けるのか。admin や oracle の鍵が侵害されたら、利用者の残高や準備金に何が起きるのか。

レポートの各ファイルは、これらの問いを分担している。

---

## 2. 仕様を状態機械に変える

### 2.1 償還を申請・待機・claimに分ける

公開文書の文章は、そのままではLeanの定理にならない。たとえば「償還は非同期で行われる」という一文には、申請、待機、claim、所有者、価格、期限など複数の条件が含まれている。

そこで、要求を RFC 2119 の表現に整理する。

- `MUST`: 必ず満たす
- `MUST NOT`: 決して行わない
- `MAY`: 許されるが、必須ではない

人間が読める仕様が [`SPEC.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/outputs/apyx/SPEC.md)、構造化された一覧が `requirements.json` である。仕様の各項目には、識別子、分類、根拠、元文書の引用が付いている。

### 2.2 仕様と実装を分けて考える

[`model.md`](https://github.com/NyxFoundation/docs2formalspec/blob/main/outputs/apyx/model.md) は、仕様を状態機械にしたときの説明書である。誰が操作するのか、どの残高を持つのか、どの操作が存在するのか、実装とどこが違うのかを整理している。

この段階で、仕様と実装を同じものだと思わないことが大切である。Lean は、モデルの中で漏れなく定理を確認する。しかし、モデルに存在しない操作やフィールドについては、何も言えない。

---

## 3. Leanで表す状態と操作

### 3.1 `State` は現在の台帳

`Apyx.lean` の `State` は、ブロックチェーン全体の完全なコピーではない。証明に必要な情報を抜き出した抽象的なスナップショットである。

代表的なフィールドは次の通り。

- `now`: 現在時刻
- `globalPause`: 全体停止フラグ
- `whitelist` / `denylist`: アドレスごとのアクセス制御
- `apxUSDBal`、`apyUSDBal`、`usdcBal`: アドレスごとの残高
- `totalSupply_apxUSD`、`totalSupply_apyUSD`: トークンの供給量
- `usdcReserve`: プロトコルが持つ準備金
- `unlockRequests`、`flexibleUnlockRequests`: 償還請求のレジストリ
- `vestTotal`、`vestStart`、`vestPeriod`: 利回りの vesting 状態
- `redemptionValue`: 償還に使う価格

Lean の `Address → Nat` は、アドレスを渡すと残高を返す関数である。Solidity の mapping に似ているが、数学的には無限個のアドレスに対する関数として扱われる。この抽象化は簡潔な一方、全アドレスの総和や、実際の ERC-20 storage の整合性を自動的には与えない。

### 3.2 `Op` は操作の一覧

```lean
inductive Op
  | depositUSDC (amount : Nat)
  | lockApxUSD (amount : Nat)
  | requestUnlock (amount : Nat)
  | claimUnlock (id : Nat)
  | tick (dt : Nat)
  | pause
  | updateRedemptionValue (newValue : Nat)
  | ...
```

`inductive` は、「操作の種類を列挙する型」と考えればよい。

操作を型の中に閉じ込めることには意味がある。`Op` に新しい操作を追加すると、全操作を調べる定理の多くが再検査される。残高を動かす新しい分岐を追加したのに、古い安全性定理がその分岐を見落とす、という事態をビルド時に発見しやすくなる。

### 3.3 `step` は1トランザクション

```lean
step (s : State) (op : Op) (caller : Address) : Option State
```

`step` は、状態 `s` に対して caller が op を呼んだ結果を返す。

- `some s'`: 操作が成功し、状態が `s'` になった
- `none`: 操作が revert した

たとえば deposit の分岐は、概念的には次のように動く。

```text
pause 中なら失敗
caller が許可されていなければ失敗
残高が足りなければ失敗
それ以外なら USDC を減らし、準備金と apxUSD を増やす
```

成功した操作については、次のような定理を書く。

```lean
theorem something
    (h : step s (Op.someOperation ...) caller = some s') :
    条件A ∧ 条件B ∧ s' = 期待した状態 := by
  ...
```

`h` は「この操作が成功した」という仮定である。結論には、成功するための条件と、成功後に変わった状態の両方が入る。

### 3.4 `execTrace` は操作列

```lean
execTrace s [(op1, caller1), (op2, caller2), ...]
```

は操作を順番に実行した最終状態である。失敗した操作は revert して状態を変えず、次の操作へ進む。

`step` の定理と `execTrace` の定理は、似ていても強さが違う。

- single-step: 1回の操作が何をするか
- trace-level: 任意の操作列を実行しても何が保たれるか

「deposit が成功すれば apxUSD が発行される」は single-step で十分である。「同じ利用者が操作を何度も組み合わせても無償価値を得られない」は trace-level でなければ言えない。

### 3.5 時間は `now` があるだけでは進まない

cooldown、vesting、rate limit、実行タイミングを扱うには、状態に `now` があり、操作列の中で時間を進められなければならない。`Op.tick dt` は `now` だけを `dt` 進める操作である。

償還なら、次の操作列を表現できる。

```text
requestUnlock
  → tick 20日
  → claimUnlock
```

時間を手で進めた状態を theorem に渡すだけでは、「実際の操作列でそこへ到達できる」とは限らない。早すぎる claim を拒否する safety と、待ってから claim できる liveness は別の性質である。

### 3.6 `Nat` の限界

金額は主に `Nat`、つまり0以上の整数で表される。これは残高計算には扱いやすいが、負債や負の純資産を表せない。

「残高が決して負にならない」という定理は、コントラクトの健全性を示しているとは限らない。そもそも負の値を入れられない型を使っているだけかもしれない。同じように、次の性質もモデルの構造に依存する。

- `Address → Nat` だけでは、全 holder の総和保存を自然に書けない
- 価格を1本のフィールドにまとめると、デプロイ側にある2つの価格の乖離を表せない
- 時間を進める操作がなければ、実行タイミングの選択を表せない

反例を表現できるモデルかどうかが、定理の強さを決める。

---

## 4. 償還を表す状態遷移

### 4.1 申請、待機、claim

`requestUnlock amount` は、caller の apxUSD を焼き、償還請求を記録する。直後に `claimUnlock id` を呼んでも、cooldown が終わっていないので `none` になる。

その後 `tick cooldownPeriod` を実行し、owner または vault operator が claim すれば、請求を消して所定量の apxUSD を戻す。

この3段階は、次の定理に対応する。

- `req_redemption_async_process`: request と即時 claim を同時には完了できない
- `req_unlock_cooldown`: deadline 前の claim は失敗する
- `redemption_cycle_closes_after_cooldown`: 時計を進めれば、request から claim まで同じ trace で完了する

最初の2つは早すぎる実行を拒否する safety、最後の1つは処理が完了する側の liveness である。「非同期償還に対応する」という一文を、ここまで細かく分けて初めて、何が証明されたかが分かる。

### 4.2 top-up と複数 request

標準の `requestUnlock` は、同じ利用者の既存 request を top-up する。金額を足すと cooldown の終了時刻も更新される。つまり、満期直前に少額を追加すると、合計額全体がもう一度待機になる。

これは `CommitToken` でさらに明確になる。`requestedAt` をトランシェごとに保存せず、1つの request 全体に対して上書きするからである。`redeem` は完全一致しか受け付けないため、部分 claim もできない。

この挙動は、必ずしもコードの約束違反ではない。ただし、利用者が「満期を迎えた分だけ取り出せる」と考えているなら、想定と実装の差になる。

### 4.3 償還価格と被害

償還の支払額は概ね次の式で決まる。

```text
amount × redemptionValue / ray
```

モデルに価格の floor がなければ、`redemptionValue = 0` の状態でも、token を焼いて0を受け取る witness を作れる。担保が不足しているからではなく、担保が十分にある状態を選んでこの結果を示している。

デプロイ済みの価格 pipeline には par の cap がある。価格は概ね次のように作られる。

```text
collateral ratio を push
  → min(collateral ratio, cap)
  → published redemption price
```

したがって、上限についてはデプロイ側に制約がある。一方、下限はなく、0を publish できる。`SpecDefects.lean` はモデル上の反例を、`RedemptionOracle.lean` はデプロイの価格 pipeline を扱っている。

---

## 5. 検証を分担するLeanファイル

### `Apyx.lean`: すべての土台

定数、`State`、状態更新関数、`Op`、`step` がここにある。`req_...` という theorem は、公開文書の要求をモデル上で確認する。

確認する順序は次の通りである。

1. `State` で何を記録しているか確認する
2. `computeExchangeRate`、vesting、fee、share conversion を見る
3. `Op` と `step` で、どの操作がどの条件で成功するかを見る
4. `req_...` の仮定と結論を確認する

`private theorem inv_...` は、成功した `step` から、ガードと結果の状態を取り出す補助定理である。証明スクリプトを最初から理解しなくても、theorem の型だけで役割を把握できる。

### `BlastRadius.lean`: 特権鍵が侵害された場合

仕様通りに行動する利用者を考える `Apyx.lean` に対して、こちらは privileged role の鍵が盗まれた場合を扱う。

中心になるのが frame theorem である。ある操作が状態のどのフィールドだけを変更するかを示す。

- pause controller は停止状態を変更する
- yield distributor は vest pool に credit する
- oracle は市場価格を publish する
- admin は、価格・準備金を含むより広い範囲を変更できる

「ユーザー残高を直接減らせない」と「ユーザーの価値を守れる」は別の話である。admin が残高を debit できなくても、準備金を移したり、償還価格を変えたりすれば、額面を残したまま換金価値を下げられる。

role-only trace の theorem は、対象 role の操作だけについての frame である。盗まれた鍵が通常の操作も呼べることまで、当然には含まれない。trace に置かれた仮定が、そのまま保証の範囲になる。

### `Safety.lean`: 正当な操作を組み合わせた攻撃

role が正しく動くと仮定し、一般利用者が合法的な操作の順番や金額を工夫して価値を抜けるかを調べる。

代表的な theorem は次の通り。

- `no_free_value_trace`: 何も持たない利用者が操作列だけで apxUSD を作れない
- `solvency_preserved`: 明示した well-formedness 条件の下で、供給と担保の関係を保つ
- `rounding_favors_protocol`: 丸め誤差が利用者への無償支払いにならない
- `no_dilution`: 他人の deposit が既存 holder の価値を下げない
- `vest_no_early_drain`: vesting 前の利回りを引き出せない
- `no_same_state_arbitrage_round_trip`: 同じ状態で mint と redeem の両方を使った裁定ができない

`solvency_preserved` はすべての操作列を無条件に扱う theorem ではない。`WellFormed` を各 prefix で仮定し、claim、stress、backstop、reserve withdrawal などを明示的に除外している。theorem の名前ではなく、仮定と除外条件まで含めて保証になる。

### `HolderValue.lean`: holder が本当に持つものを数える

初期の価値測定 `Safety.valueAt` は、wallet 残高と share を数えたが、pending unlock position を含んでいなかった。withdraw の結果が請求ポジションに入る設計では、この測定は不完全である。

`HolderValue.lean` は、standard unlock と flexible unlock を `List.range nextUnlockId` 上で合計し、`holderValue` として扱う。さらに、差分を `Int` の `netDelta` で表す。`Nat` の引き算のように、損失が0で切り捨てられることがない。

このファイルは、「定理が通ったか」だけでなく、「何を価値として測るべきか」が正しく定義されているかも検査している。

### `SpecDefects.lean`: 仕様そのものを検査する

通常の定理は、モデルが仕様を満たすかを調べる。仕様の抽出に誤りがあれば、モデルは誤った要求にも従えてしまう。

このファイルでは、次の見かけ上の矛盾を調べる。

- buffer は決して減ってはならない
- catastrophic backstop は buffer 全体を配る

元文書を読み直すと、「通常の償還や stress event では buffer を保つ」と「catastrophic な終了処理で配る」は別の範囲だった。矛盾はプロトコルではなく、抽出時に適用範囲が落ちたことによる。

同じファイルの `redemption_has_no_floor` は、危険な状態を具体的に構成する gap witness である。これは「証明できなかった」という曖昧な指摘ではなく、条件を満たす状態と操作を作って示す反例である。

### `CommitToken.lean`: 大きな非同期償還 vault

`CommitToken` は、request → wait → redeem の vault を独立にモデル化する。一つの定義で、`CT-apxUSD`、`CT-apyUSDapx`、`CT-apxUSDUSDC`、`UnlockToken` の4インスタンスを扱う。違いは asset、cooldown、supply cap だけだからである。

証明する性質は次の通りである。

- cooldown 後には request から claim まで完了する
- claim は要求分を正確に焼いて支払う
- 保有残高を超えて request できない

同時に、利用者にとって見落としやすい挙動も定理になっている。top-up は全体の `requestedAt` を更新し、redeem は完全一致のみを受け付け、storage 上の `unlockingDelay` を変更すると既存 request の claim 時期にも影響する。

### `RedemptionOracle.lean`: cap と floor

オンチェーンの価格 pipeline は、担保比率を受け取り、`min(collateral ratio, cap)` を publish する。

- `published_never_exceeds_par`: cap があるので par を超えない
- `cap_immutable_trace`: pipeline の操作で cap は動かない
- `published_has_no_floor`: 下限がなく、0を publish できる

これにより、モデルで仮定していた `redemptionValue ≤ ray` が、デプロイでは cap によって裏付けられる。一方、floor の欠如は残る。

### `MinterRateLimit.lean`: sliding-window mint 制限

Minter は、期間内に発行した量を履歴へ記録し、残りの発行可能量を計算する。

このモデルでは、上限を超える mint の拒否、履歴の合計が上限を超えないこと、上限を引き下げても既存の履歴を取り消さないこと、期限を迎えた履歴が window から外れることを確認する。

rate limit は時間と切り離せない。時間を誰でも自由に進められるなら、制限は制限として機能しない。そのため、ここにも `tick` と trace がある。

### `LiquidationBatcher.lean`: 遅延なしでも無制限ではない

role 41 は実行遅延を持たない。しかし、ソース上は liquidation 対象の allowlist に setter がなく、`withdrawTokens` の送付先も固定されている。

`allowlist_immutable`、`destination_immutable`、`unlisted_market_reverts_the_batch`、`role41_trace_blast_radius` は、この構成上の制約を確認する。対象は Apyx 内部の清算ではなく Morpho Blue である。Apyx 自体に口座別の担保ポジションがないため、内部清算機能の欠落を示す theorem ではない。

### `DeploymentGaps.lean`: 実装にあってモデルにないもの

verified Solidity とモデルを照らし合わせ、モデルの外側にある経路を記録する。

- `setBeneficiary`: vesting の受取人を変更し、未回収の yield を別アドレスへ送れる。実デプロイでは3日スケジュールだが、モデルには操作がない
- supply cap: `ApxUSD` には cap があるが、モデルにない。admin と minter の組み合わせなら cap を引き上げられる
- vest clock: 実装は `lastDepositTimestamp` と `lastTransferTimestamp` を分けるが、モデルは `vestStart` 1本で、pull のたびに時計を再アンカーする

これらの theorem が証明するのは、手書きした転記モデルについての性質である。転記が Solidity に忠実かどうかは、ソースの読み合わせとオンチェーン確認で判断する。

### `DeploymentFees.lean`: 実装の fee を数える

実デプロイの `ApyUSD._withdraw` は、receipt の可変 fee とは別に、withdraw/redeem のたびに vault-side `unlockingFee` をかける。live value は10 bpsで、fee は vault 外の fee wallet に送られる。

この fee がモデルになかったため、モデルは withdrawer に要求する share を少なく見積もり、vault に残る資産を多く見積もっていた。

また、`FeeCurve` の実装では `minDuration` が、claim 可能になる時刻と fee が減り始める時刻を兼ねる。文書から作ったモデルの曲線とは形が異なり、最初の claim 時点で最大 fee がかかる。

### `MulDivFidelity.lean`: 丸めの差を測る

モデルは `computeExchangeRate` を一度計算し、その値を使ってさらに割り算する。OpenZeppelin の ERC-4626 は、`totalSupply + 1` と `totalAssets + 1` を使った単一 `mulDiv` で変換する。

いきなり計算式を置き換えるのではなく、まず差の向きを定理にしている。

- `sharesOfCeil_pos`: 正の withdraw は必ず1 share以上を要求する
- `redeemAssets_le_assetsOf`: モデルは chain より多く redeem assets を払わない方向
- `sharesOf_le_lockShares`: deposit 側はモデルが多く share を発行し得る
- `rate_floors_to_zero_witness`: 極端な状態では中間 rate が0になり、計算結果が大きくずれる

このファイルの結論は「計算式をすぐ置き換えられる」ではない。どの定理を再証明しなければならないかが分かる、ということである。

### `review_witnesses/Regression.lean`: 自己レビューの回帰テスト

モデルの自己レビューで見つかった誤りを、具体的な witness としてもう一度確認する。定義を修正した後も、同じ誤りが戻っていないかを検査するためのファイルである。

---

## 6. 検証で分かったこと

### 残高の保全と、価値の保全は別である

全 operator key が侵害されても、受動的な利用者の `apxUSDBal`、`apyUSDBal`、`usdcBal` を直接減らせない、という定理がある。

しかし、これは額面の保全であって、換金価値の保全ではない。admin が準備金を動かしたり、償還価格を変えたりすれば、残高が同じでも価値は失われる。

そのため、`admin_cannot_touch_balances` と `admin_alone_drains_reserve`、`admin_alone_moves_redemption_price` は、反対の結論ではない。見ている対象が違う。

### 償還価格には下限がない

モデル上、`redemptionValue = 0` でも redeem のガードを通れる状態がある。担保がない状態ではなく、担保が供給を十分にカバーする witness になっている。

デプロイ側には par の cap があるので、上限についてはモデルより強い。しかし floor はなく、0の publish は止めない。レポートの正しい読み方は、モデル上のfindingとデプロイ構成上の制約を分けることである。

### 非同期 vault は、待ち時間の実装まで仕様である

`CommitToken` では、満期を迎えた request に少額を追加すると、全額の時計がリセットされる。部分 claim もできない。

これはコードが約束した動作に反しているとは限らない。ただし、「成熟した分だけ引き出せる」という利用者の期待とは食い違う可能性がある。formal verification は、こうした曖昧な期待を、実際の条件へ置き換えるのにも役立つ。

### vesting の良い点と、モデルの差分

`LinearVestV0` は、すでに accrue した yield を `fullyVestedAmount` に移してから時計を再設定する。この二重 accumulator は yield の forfeiture を防いでおり、`creditYield_preserves_accrued_vest` で確認されている。

一方、実装は pull で vesting の終了時刻を動かさないが、モデルは1本の `vestStart` を pull で更新する。実装の設計が正しいことと、モデルが実装を完全に写していることは分けて記録されている。

### README §5 の提案

提案は、見つかった経路に対応している。

| 提案 | 防ぎたいもの |
|---|---|
| redemption price の floor | 償還価格を0へ落とす経路 |
| withdrawal/redemption の rate limit | 準備金流出の集中 |
| privileged change の timelock | 監視や退出の時間がないこと |
| RFQ counterparty の監査と縮小 | 特権鍵と決済者の結託 |
| 二重 accumulator の維持 | accrue 済み yield の forfeiture |
| top-up 時の owner consistency | 他人の pending position の書き換え |
| ERC-4626 の inflation 対策の決定 | virtual share だけに依存する dust 攻撃 |
| bytecode-level audit | reentrancy、flash loan、upgrade、storage、gas |

これはすべて実装済みの機能一覧ではない。Lean で形式化した提案、デプロイ設定で確認できる制約、これから実装・監査が必要な項目を分けて記録している。

---

## 7. 保証の境界

### 言えること

- `Op` に列挙された操作について、ガードと状態更新を全分岐で確認できる
- 明示した仮定の下で、仕様要件を single-step theorem として確認できる
- trace-level に持ち上げた性質について、操作列全体の保存則や被害範囲を確認できる
- gap witness で、危険な状態とその操作を具体的に示せる
- 仕様の抽出範囲が正しいかを検査できる

### 言えないこと

- Lean のモデルがデプロイ済み bytecode と完全に同じであること
- reentrancy、flash loan、gas、storage layout、upgrade safety
- USDC 6桁と18桁トークンの decimal scaling の完全な挙動
- holder の総和が準備金と一致すること
- `Nat` では表せない負の純資産
- モデルにない2つ目の価格源の乖離
- オフチェーンの RFQ、UI の地域制限、treasury 運用

定理数は保証の強さではない。仮定、量化範囲、操作列の有無、モデルの盲点を定理ごとに確認する必要がある。

---

## 8. ビルドして確かめる

このプロジェクトは mathlib に依存しない。Lean toolchain を用意したら、次を実行する。

```bash
cd lean
lake build D2fsSpecs
```

`D2fsSpecs` は [`lean/D2fsSpecs.lean`](https://github.com/NyxFoundation/docs2formalspec/blob/main/lean/D2fsSpecs.lean) から、Apyx 関連の12モジュールをまとめて import する。

検査の入口は、`by` 以下の証明手順ではなく、定義と theorem の型である。確認する順序は次の通り。

```text
State のフィールド
  ↓
Op の種類
  ↓
step のガードと状態更新
  ↓
代表 theorem の仮定と結論
  ↓
execTrace に持ち上がっているか
  ↓
README の finding と out-of-scope
```

`Op` に新しい残高移動操作を追加した場合、frame theorem や安全性 theorem が壊れるかを確認する。ビルドの失敗は、証明が邪魔をしているのではなく、分析対象が変わったことを知らせている。

---

## 9. 定理を読むときの基準

Lean は、プロトコルを「状態」「操作」「遷移」に分解し、主張を数学の文にして、全分岐について確認する道具である。安全かどうかを一言で判定する道具ではない。

Apyx のレポートで価値があるのは、定理が通ったことだけではない。価格の上限と下限、額面と価値、申請と claim、モデルと実装の差を、別々の問いとして扱えるようにしたことにある。

各 theorem の意味は、次の三点で決まる。

> どの状態から、どの操作または操作列について、何を保証しているか。

この一文を手元に置いて `Apyx.lean` と README を往復すると、Lean の構文をすべて知らなくても、証明が保証する範囲と、まだ検証されていない範囲を読み分けられる。
