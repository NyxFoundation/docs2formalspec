# Lean コードレビュー — `outputs/apyx/`

レビュー日: 2026-07-30 · 対象: `Apyx.lean` (4187行) / `BlastRadius.lean` (3141行) / `Safety.lean` (1550行) /
`SpecDefects.lean` / `CommitToken.lean` / `RedemptionOracle.lean` / `MinterRateLimit.lean` /
`LiquidationBatcher.lean` — 計 9776 行。`lean/D2fsSpecs/` の同名ファイルと byte 一致。

---

## 0. 総評

**証明そのものは健全です。** `sorry` / `admit` / `native_decide` / 独自 `axiom` は生きたコードに一つもなく
(9件の grep ヒットは全て `-- BROKEN:` コメント内)、主要定理16本の `#print axioms` を実測した結果は
`propext` / `Quot.sound` のみ、`admin_alone_drains_reserve` だけ `Classical.choice` を追加で使用。
README §7 の記述どおりで、kernel 検証は本物です。

**問題は証明の中身ではなく、定理と README の散文の距離にあります。** 最も価値の高い結果
(`admin_alone_drains_reserve`, `admin_alone_moves_redemption_price`, `pauser_trace_blast_radius`,
`published_never_exceeds_par`) は正確に述べられている一方、README の見出し級の主張のうち少なくとも
8つが、対応する Lean 定理より強い内容を主張しています。第三者監査レポートとして出す前に、
下記 §1 の修正が必要です。

**そのうち3つは単なる文言の問題ではなく、モデル上で反例が構成できます。** ERC-4626 の希釈免疫と
inflation-attack 免疫は成立しておらず、`review_witnesses/` に **Lean kernel で通る反例5本**を
置きました (§1.0)。特に `W2_honest_lifecycle_dilution.lean` は、鍵の漏洩なし・全ロール正直の
操作列だけで既存ホルダーが 25% 希釈されることを示します。根本原因の一つ
(`exchangeRate` キャッシュのレート不整合) は**モデルの人工物ではなく実装に持ち帰るべき指摘**です。

**ビルド**: `Japandefencemap.lean` が構文エラーのままコミットされ (commit 7749566)、`D2fsSpecs.lean`
の root から import されていたため、README §7 が読者に指示する `lake build D2fsSpecs` が exit 1 で
失敗していました。**本レビューで import を削除し、exit 0 を確認済み**(`lean/D2fsSpecs.lean`)。

---

## 1. 重大 — README の主張が定理より強い

### 1.0 【最重要】ERC-4626 の希釈・inflation attack 免疫は成立していない — 機械検証済みの反例あり

`review_witnesses/` に **Lean kernel で通る反例5本**を置きました (全て `by decide` / `rfl`、
`native_decide` 不使用、2026-07-30 に通過確認済み)。実行方法は同ディレクトリの README を参照。

**根本原因は `exchangeRate` がキャッシュであり、レート整合の不変量が存在しないことです。**
`Op.lockApxUSD` は**格納された古いレート**で株を発行し (`Apyx.lean:594`)、`updateExchangeRate` は
その**後**に呼ばれます。`creditYield` / `tick` / vesting はキャッシュを更新しないので、vault 操作の
合間はキャッシュが真の価格より systematically 低くなります。`s.exchangeRate = computeExchangeRate s`
を述べた定義・定理は `Apyx.lean` / `Safety.lean` の両方に存在しません。

#### (a) 正直な操作列だけで真の株価が下落し、既存ホルダーが 25% 希釈される

`review_witnesses/W2_honest_lifecycle_dilution.lean`。レート整合な初期状態
(`w0.exchangeRate = computeExchangeRate w0`) から、**鍵の漏洩なし・全ロール正直**の操作列:

```
[(lockApxUSD 100, A), (creditYield 100, 本物の yieldDistributor), (tick 100日), (lockApxUSD 100, B)]
```

| 量 | B の預入直前 (`w3`) | 直後 (`w4`) |
|---|---|---|
| 格納 `exchangeRate` | `ray` (古い) | `1.5·ray` |
| `computeExchangeRate` (真の値) | `2·ray` | `1.5·ray` ← **下落** |
| A の真の償還可能額 | 200 | 150 |
| B: 100 apxUSD 支払い、保有株の価値 | — | 150 |

`no_dilution` の仮説 `hTS : 0 < totalSupply_apyUSD` と `hbacked` は**両方 `w3` で成立**し、結論も
成立します — A の事前価値を古い `ray` で見積もるため「100 → 150 に増加」と報告されるからです。

→ README §4.2 の「**No dilution** | A deposit by someone else never lowers an existing holder's
redeemable value」と「**Share-price monotonicity** | A new deposit never dilutes the exchange rate
… the ERC-4626 dilution invariant」は、**真の株価については偽**です。単調なのはキャッシュ
アキュムレータだけです。なお同じ README 行が引用する `req_exchange_rate_non_decreasing` は
`computeExchangeRate` についての主張なので、1行の中で異なる2つの量が混同されています。

同じ古さは `withdrawShares` / `redeemAssets` の払い出しも古い(低い)レートで値付けするため、
償還者から預入者へ価値を移します。この方向はここのどの定理からも見えません。

#### (b) ERC-4626 inflation attack は「構造的に不可能」ではなく、実際に成立する

`review_witnesses/W3_inflation_attack.lean`。`lockShares = amount * ray / exchangeRate` は
`amount · ray < exchangeRate` のとき floor して **0** になり、下限チェックがありません。

レート整合・非退化状態 (攻撃者が唯一の1株を保有、vault に 200 資産、株価は正直に `200·ray`) で:

- 被害者が 150 apxUSD を `lockApxUSD` → **0 株**、150 apxUSD 全額喪失
- 攻撃者の1株は 200 → **350** に増価

`no_dilution` の結論は**攻撃者について**成立します(保護対象は「預入していないホルダー」であり、
希釈の被害者は預入者本人 — どの定理もカバーしていません)。`no_inflation_attack` も成立します
(`lockApxUSD` で `amount ≤ apxUSDBal caller` を報告するだけで、**発行株数について何も述べない**)。

→ README §4.2 の「**Inflation-attack immunity** | The ERC-4626 first-depositor / donation attack is
structurally impossible — there is no raw donation primitive; every vault-asset increase is matched
by a share mint」は偽です。「every vault-asset increase is matched by a share mint」は
`no_inflation_attack` / `donation_free` の**statement ではなく**(両者は `totalSupply_apyUSD` にも
`apyUSDBal` にも言及しない)、モデル上も偽です。**sub-share dust の `lockApxUSD` が、存在しないと
された raw donation primitive です。**

`W5_first_depositor_steal.lean` は退化版: `default` 由来状態 (`exchangeRate = 0`) で最初の預入者が
100 apxUSD → 0 株、レートが `ray` にリセットされ、次の攻撃者が 1 apxUSD で 1 株を得て
vault 全額 101 を `redeem` で持ち出します。

#### (c) `x/0 = 0` により、0 株のアドレスが vault を全額抜ける

`review_witnesses/W4_zero_rate_drain.lean`。`exchangeRate = 0`(`default` の値であり、全ての
トレース定理が量化する状態形)かつ vault に資金がある状態で `withdrawShares 100 0 = 0` となるため、
ガード `s1.apyUSDBal caller < shares` が `0 < 0` = false になります。結果、**株を1つも持たない
アドレス**が `Op.withdraw 100 self` を実行し、`vaultApxUSDBal` を 0 にして、株を1つも焼かずに
100 apxUSD の請求可能ポジションを得ます。

3つの見出し定理すべてが生き残ります: `rounding_favors_protocol` の clause (3) は
`0 < exchangeRate` を仮説で除外 (`Safety.lean:698`)、`caller_net_nonpositive` はポジションを
測らないので「価値は減少」と見る、`no_free_value_trace` は `withdraw n a` を名前で除外。

#### (d) `setVestPeriod 0` が vest ストリームを全額即時実現する

同じ `W4`。admin の `Op.setVestPeriod 0` 一発で `vestedAmount` が 0 → 1000、`totalAssets` が
0 → 1000 になります。`vest_no_early_drain` の docstring が言う「no sequence of calls (at whatever
times) can exceed …」はトレースレベルの主張ですが**述べられても証明されてもおらず**、保存則の
双子定理は両方 `0 < vestPeriod` (`:1250`) / `0 < p` (`:1284`) でこの状態を仮説から除外しています。
なお `default.vestPeriod = 0` です。

#### (e) `Solvent` の「必要マージン」項は恒等的にゼロ

`Safety.lean:581` の `Solvent s := s.totalSupply_apxUSD + s.overcollateralizationBuffer ≤ …` は
`State` **フィールド**への dot 記法で、`def overcollateralizationBuffer` (`Apyx.lean:244`、
`redeemApxUSD` のガードが使う関数) とは**別の対象**です。このフィールドを書く op は
`catastrophicBackstop` ただ一つで、しかも `0` を代入します (`Apyx.lean:817`)。`default` でも `0`。

`W3_inflation_attack.lean` で機械検証済み: `t2.overcollateralizationBuffer = 0` (`rfl`) の一方で
`Apyx.overcollateralizationBuffer t2 = 500`。

→ **到達可能な全トレースでマージン項は 0** なので、`solvency_preserved` は
`totalSupply_apxUSD ≤ totalCollateralValue + usdcReserve` に退化します。定理名・`Solvent` の
docstring (「plus the required margin」)・README の行はいずれも中身より強いです。

### 1.1 「全鍵漏洩でも受動的ユーザーは何も失わない」は名目残高の単調性にすぎず、同じファイルが反例を証明している

`BlastRadius.lean:1491` `user_assets_immune_to_total_key_compromise` の結論は
`apxUSDBal u`, `apyUSDBal u`, `usdcBal u` の非減少と `governanceTokenBal u` の不変のみ。
**価値については一言も述べていません。**

定理が許す操作列で反例が作れます:

```
σ = [(Op.updateRedemptionValue 1, admin), (Op.withdrawReserve s.usdcReserve admin, admin)]
```

両仮説 (`admin ≠ u`、`u` を狙った RFQ なし) は成立し、結論も成立しますが、USDC 裏付けは全額
攻撃者の `usdcBal` に移り、`u` の apxUSD は `amount × 1 / 10²⁷ = 0` で償還されます。
これは仮想の話ではなく、同ファイル 400 行後の `admin_alone_moves_redemption_price` (L1900) と
`admin_alone_drains_reserve` (L1909) がまさに証明している内容です。

→ README の「**all keys at once** | A passive, non-RFQ-targeted user loses nothing」という行は
経済的主張として偽であり、自ファイル内で矛盾しています。**Lean の主張は健全、貼られたラベルが不当。**
「名目残高は減らない (価値の保証ではない)」に書き換えるべきです。

同根の問題として `single_key_bounds` (L2929) は "no single compromised key extracts principal" と
題しながら admin 行の結論は `usdcReserve ≤ s.usdcReserve` — reserve がゼロになる(=admin の懐に入る)
ケースを満たします。docstring (L2918) は今も reserve が「never to the admin's discretion」と
書いており、`admin_alone_drains_reserve` に直接反駁されています。

`admin_cannot_touch_balances` (L831) も同様で、USDC の結論は `∀ a, s.usdcBal a ≤ s'.usdcBal a`
(pointwise credit-only)。`withdrawReserve amount admin` はこれを満たします — **窃盗犯自身の残高が
credit 側にあるから**です。定理名が実態と乖離しています。

### 1.2 レートリミット/タイムロックの防御ラッパーは、時間軸が攻撃者の自由変数になっている

**`rate_limit_linear_bound` (L2371) は「時間に対して線形」ではありません。**
`step2 rs RLOp.advanceEpoch = some {rs with epoch+1, spentThisEpoch := 0}` (L2206) には
caller もガードもなく、**`base.now` や `Op.tick` との関係が一切ありません**。`countEpochs τ` (L2220)
は攻撃者が自分のトレースに置いた `advanceEpoch` マーカーを数えるだけです。したがって

```
τ = [base(withdrawReserve cap, admin), advanceEpoch, base(withdrawReserve cap, admin), advanceEpoch, …]
```

は base 時刻を1秒も進めずに reserve を全額抜き、定理は `k` = 攻撃者が要求したリセット回数で成立します。
docstring の核心である「the clock is not attacker-favourable: more epochs only means more elapsed
time」(L2356) は、まさに未証明の仮定です。README §5-2 の「damage becomes at most linear in time」は
現状の定理では支えられません。

**加えてメーターの対象がずれています。** `step2` は `usdcReserve` の流出額のみを課金します (L2202)。
ところが `admin_rfq_coalition_drains` の攻撃は価格を 0 に落として 100 apxUSD を **0 USDC** で
焼くので、課金はゼロ、`cap` をどれだけ小さくしても素通りします。

**`timelock_escape_guarantee` (L2686) は `delay` 個の構文上の `tick` トークンの存在を証明するだけ**で、
`delay` だけ時間が経過したことは証明していません。`TLOp.tick` (L2494) は無償・無認可で、`tl.now` は
`base.now` と無関係な独立カウンタです。

さらに **ラッパー自身が約束した escape を不可能にしています**: `TLOp.queue (op : Op) (caller)` (L2482)
は特権操作フィルタなしに**任意の Op** を受け付け、`execute` が base への唯一の経路 (L2496)。
つまり退避したいユーザーも自分の `redeemApxUSD` を queue して `delay` 待つ必要があり、その時には
先に queue された攻撃者の変更が既に成熟しています。docstring の「throughout that window ... users
can still exit against the pre-change parameters」(L2682) はモデル上成立しません。

### 1.3 「ユーザーごとに保留中の償還はひとつ」は不変量でもなく一意性でもない

`Apyx.lean:2286` `req_single_pending_redemption_per_user` の結論は
`∃ id amt, s'.unlockRequestId caller = some id ∧ s'.unlockRequests id = some (caller, amt, …)` —
**存在のみで「多くともひとつ」を一切述べていません。**

しかもモデル自体が破っています。`Op.withdraw` / `Op.redeem` (L648, L663) は `createStandardUnlock`
を無条件に呼び、top-up ロジック (`requestUnlockStep`) を経由しません。`createStandardUnlock` (L160)
は受取人の `unlockRequestId` ポインタを黙って上書きします。

→ `requestUnlock 100` の後に `withdraw 50 self` を実行すると、**同一ユーザーが2つの生きた標準ポジション**
を持ち、両方 `claimUnlock` 可能で、古い方はポインタから孤立します。

### 1.4 「exchange rate は非減少」は時間経過のみの主張で、ステップ間では偽

`Apyx.lean:1488` `req_exchange_rate_non_decreasing` は
`computeExchangeRate s ≤ computeExchangeRate { s with now := s.now + dt }` — **操作が登場しません。**

原因はモデル設計です。`exchangeRate` は `lockApxUSD` / `withdraw` / `redeem` の内部でのみ更新される
キャッシュで、`tick` と `creditYield` は真の `computeExchangeRate` を動かすのにキャッシュを更新しません。
`lockApxUSD` (L594) は古いキャッシュレートで mint するので、`creditYield` → `tick 20d` → `lockApxUSD`
の到達可能な列で `computeExchangeRate` は**厳密に減少**します。

### 1.5 `apxUSD_credit_is_backed` は単一ステップ、README は「操作列」と書いている

docstring 自身がトレース版を「left as the stated next step」(L2026) と認めています。
このギャップはモデル内で悪用可能です:

1. admin: `updateRedemptionValue (2*ray)`
2. oracle: `setApxUSDMarketPrice (ray+1)` → `mintApxUSD` のゲートが開く
3. 攻撃者: `mintApxUSD self 100` → 100 USDC 支払い (各ステップは "backed")
4. oracle: `setApxUSDMarketPrice (ray-1)` → `redeemApxUSD` のゲートが開く
5. 攻撃者: `redeemApxUSD 100` → **200 USDC 受領**

差額 +100 USDC は他ユーザーの預託金から出ます。各ステップは `apxUSD_credit_is_backed` を満たし、
列は満たしません。そして被害者全員は `user_assets_immune` を満たし続けます — 減ったのは
`usdcBal` ではなく reserve だからです。

### 1.6 主力の攻撃 witness が `usdcReserve = 0` を前提にしている

`admin_rfq_coalition_drains` (L3004) の結論に `s.usdcReserve = 0` (L3011) が入っています。
reserve が 0 かつ `redemptionValue = ray` なら、被害者は**連合が動く前から**償還で何も得られません
(`redeemApxUSD` / `executeRFQRedemption` はどちらも reserve ガードで revert)。
つまりこの定理が示すのは、実現価値がすでにゼロだった名目請求権の消滅であり、連合に帰属する損失では
ありません。

既存の `human_review_admin_rfq_coalition_drains.md` (F3) がまさに鋭い witness (`usdcReserve := 100`)
を推奨しており、`totalSupply` と `whitelist` は修正されたのに **`usdcReserve` は修正されず**、
代わりに docstring が reserve-0 を前提として書き直されています。

---

## 2. モデル忠実性 / 定義のバグ

| # | 箇所 | 内容 |
|---|---|---|
| 2.1 | `Apyx.lean:720-734` `Op.creditYield` | **同じ1ドルを二重計上**。`usdcReserve += amount` と `vestTotal += amount` を両方実行。USDC 償還 reserve が USDC の流入なしに増え、同じ yield が後に `pullVestedYield` 経由で `vaultApxUSDBal` にも入ります。`req_overcollateralization_limit` / `Safety.solvency_preserved` の右辺を無償で膨らませる方向に効きます。 |
| 2.2 | `Apyx.lean:203` `burnUnlockNFT` + L605 `claimUnlock` | `unlockTokenOwner` / `unlockTokenAmount` はクリアするが **`unlockRequests id` と `unlockRequestId owner` を残す**。claim 後に再度 `requestUnlock` すると死んだエントリに top-up され、`unlockTokenOwner id = none` で claim ガードに落ちて**資金が恒久的に請求不能**になります。 |
| 2.3 | `Apyx.lean:125-132` `flexibleUnlockFee` | 手数料の起点が request 時刻。最短 claim 可能時点 (elapsed = 3日) の手数料は 350 − (3·340)/20 = **299 bps**。**到達可能な claim で 3.5% が課されることは絶対にありません**。`flexibleUnlockFee_le_start` (L1036) は到達不能な上限を証明しているだけで、README の「[0.1%, 3.5%]」は上端が空です。また *linearity* (単位時間あたり一定の減少) はどの定理の結論にもなっていません (証明されているのは反単調性 + 上下界 + 終端 10 bps)。 |
| 2.4 | `Apyx.lean:683` | 手数料 `(amount * feeBps) / 10000` は**ユーザー有利に floor**。ファイル内で唯一プロトコルに不利に丸める箇所で、`10000/feeBps` 未満の dust claim は手数料ゼロで抜けます。 |
| 2.5 | `Apyx.lean:842` `mintForMaxAssets` | `lockApxUSD (previewMint s shares)` を実行するので `convertToShares (convertToAssets shares) ≤ shares` しか mint されない。ERC-4626 `mint(shares)` は厳密に `shares` を渡す必要があります。厳密性を固定する定理はありません。 |
| 2.6 | `Apyx.lean:605, 674` | `claimUnlock` / `flexibleClaimUnlock` が `globalPause` を見ない (全体停止中も claim 可能)。また `redeemApxUSD` / `requestUnlock` / `flexibleRequestUnlock` / `poolRedeem` に denylist チェックがない (denylist 済みかつ whitelist 済みのアドレスが償還可能)。どちらも文書化も定理化もされていません。 |
| 2.7 | `Apyx.lean:735-738` `voteBufferDeployment` | 投票ではありません。単一 caller の残高が閾値以上なら buffer が deploy され、集計がありません。`governanceThreshold = 0` なら任意の保有者が単独で deploy できます。 |
| 2.8 | `Apyx.lean:57` vs L244 | `State.overcollateralizationBuffer` フィールドは `catastrophicBackstop` のみが書く ghost で、計算関数 `overcollateralizationBuffer` と一度も同期されません。`req_overcollateralization_limit` と `Safety.Solvent` の左辺の「必要マージン」項が実質任意の定数になっています。 |
| 2.9 | `BlastRadius.lean:76` `OracleOp` | `Op.updateRedemptionValue` を除外していますが、`Apyx.lean:529` のその op 自身の doc-comment は「**The oracle** publishes a new per-apxUSD redemption price」と書いており、`step` のガードは `s.admin` (L772)。モデル内でコメントとガードが矛盾したまま、「oracle の blast radius = 0」という結果がその未解決の帰属の上に乗っています。 |

---

## 3. 量化子の範囲 — トレース定理の実数

README は「18 theorems quantify over an arbitrary operation sequence (`execTrace`)」と書いています。実測:

- `execTrace*` に言及する public 定理: **19**
- うち任意トレースを量化: **16** (3つは固定の具体トレース)
- うち **6つはラッパートレース** (`execTrace2` / `execTraceTL`) — プロトコルに存在しない機構の話
- 残る base-model の任意 `Op` トレース: **10**、しかし **そのうち8つは σ を単一ロールの op クラスに制限**
  (`PauserOp` = 2 ops, `DistributorOp` = 1 op, `OracleOp` = 1 op)
- **真に無制限の `Op` トレースを量化しているのは 2つ** — `user_assets_immune_to_total_key_compromise` と
  `no_theft_ledger` (後者は前者の `omega` 一発の系)

ロール制限版は frame 定理として正当で、ファイル自身は L64-67 で明示しています。しかし README の表は
これらを「鍵が漏れたときの blast radius の上界」として提示しており、漏れた鍵はロール外の op も
当然投げられます。

`Safety.lean` 側も同様です:
- `solvency_preserved` (L613) は `claimUnlock`, `flexibleClaimUnlock`, `handleStressEvent`,
  `catastrophicBackstop`, `withdrawReserve` の5 op を除外し、さらに `WellFormed` を**全ての prefix で
  仮定**します (帰納的に保存されることは証明されていない)。`claimUnlock` の除外は必然です —
  `requestUnlock` が apxUSD を焼く際に保留債務を帳簿に載せないので、claim 時の再 mint が必ず
  `Solvent` を破ります。**償還サイクルを1周含むトレースでは連鎖できません。**
- `caller_net_nonpositive_trace` (L1428) の `ValuePreservingOp` は **9 op を除外**
  (`mintApxUSD`, `lockApxUSD`, `withdraw`, `redeem`, `claimUnlock`, `flexibleClaimUnlock`,
  `catastrophicBackstop`, `withdrawReserve`, `poolRedeem`)。README は「redemption / RFQ / request
  channels」をカバーと書きますが、`claimUnlock` は除外された償還チャネルです。
- 価値尺度 `valueAt` (L920) は `apxUSDBal + redeemAssets(apyUSDBal, R) + usdcBal` で、
  **unlock ポジションを含みません** — 償還中のユーザーの apxUSD が実際に置かれている場所です。
  ところが `withdraw` / `redeem` / `requestUnlock` は**まさに unlock ポジションに払い出します**。
  つまり `caller_value_withdraw_fixedRate` / `caller_value_redeem_fixedRate` が
  「引き出すと測定価値が下がる」と言えるのは、**受け取った分を測っていないから**です
  (docstring は認めていますが README は認めていません)。
  `BlastRadius.netHoldings` (L1798) も同じ欠落に加え、apyUSD *株数* を apxUSD / USDC *ドル* に
  足しており次元が合っていません。
  さらに事前・事後を**同じ**事前レート `R` で値付けするため、caller 自身が起こしたレート変動が
  不可視になります。§1.0-a の witness では B の `valueAt ray` は前後とも 100 のまま (機械検証済み)
  ですが、B は実質 +50 を得ています。
- `no_free_value_trace` の `Penniless` (`:298`) は **`apyUSDBal a = 0` を要求していません** —
  apyUSD 株を無制限に持つアドレスも「penniless」です。加えて除外リストが `withdraw n a` /
  `redeem n a` を含むので、**`a` 自身の自己宛キャッシュアウトを禁じています**。docstring の
  「Everything else — including `a` itself calling every operation with every amount — is
  quantified over」(`:291`) は偽です。また per-address なので、収益を共犯者に流す2アドレス連合には
  何も言いません。
- `caller_net_nonpositive_trace` が「どのアドレスの保有も増えない」と言えるのは、**`Op` に転送操作が
  一つも無いから**です。`transferApxUSD` は定義されていますが (`Apyx.lean:233`) `step` から到達不能で、
  `Apyx.lean:1457` が転送は未モデルであると認めています。ERC-20 の世界では任意の贈与転送が反例です。
  加えて `R` 固定なので株式の増価は**定義上ゼロ**であり、プロトコル唯一の価値創出機構に対して
  構造的に盲目です。
- `requestUnlock_backs_claim_by_burn` (`:1322`) は記録されるポジション額を `∃ amt` で述べ、
  **`amount` との関係を一切課しません**。「the obligation is exactly equal to the apxUSD burned
  (no free claim)」は証明されておらず、`amt = 2*amount` を記録するモデルでも定理は成立します。
  厳密なのは焼却側 (`s.apxUSDBal caller = s'.apxUSDBal caller + amount`) のみです。
- `no_same_state_arbitrage_round_trip` (`:1309`) は**単一状態の選言**で、`globalPause = true` なら
  両脚が revert するため自明に成立します。一方「round trip」は2ステップの現象で、脚の間に
  `Op.setApxUSDMarketPrice` を挟めば可能になります。

---

## 4. 定理数の不一致（2026-07-30時点の旧スナップショット）

| README の主張 | 実測 |
|---|---|
| BlastRadius 56 | public `theorem` **61** (private 25 を除く)。56 になる自然な部分集合は見当たらない |
| Safety 30 | **32** |
| Apyx 82 (requirement) | 旧スナップショットでは `req_` 接頭辞 **82** で一致。proof map cleanup 後の active `req_` 宣言は **27** |
| SpecDefects 2 / CommitToken 9 / RedemptionOracle 8 / MinterRateLimit 4 / LiquidationBatcher 5 | すべて一致 |
| `BlastRadius.lean:37` ヘッダ「81 requirement theorems」 | README と `leancheck.json` は 82 |
| `BlastRadius.lean:810, 613`「the eight of `AdminOp`」 | `AdminOp` (L80) の constructor は **10** |

`leancheck.json` の active requirement count は cleanup 後に **27**。`requirements.json` の82件は
抽出された要求レコード数であり、active Lean theorem surface の数ではありません。

---

## 5. 証明衛生

- **生きたコードに `sorry` / `admit` / `native_decide` / 独自 `axiom` はゼロ**(確認済み)。
- **`Apyx.lean` に約800行の `-- BROKEN:` コメント死骸** (L2052-2252, L2875-3266 ほか6ブロック)。中に
  `State` / `step` の**古い重複モデルが3つ**、`sorry` を含む形で残っています。読み間違いを招くので
  削除すべきです。
- 内容のない定理: `totalAssets` の重複定理と、`unlockTokenAmount` が `now` に言及しない
  no-yield 定理は、proof map に不要な生成物として削除済み。`step2tl_queue_exact` /
  `step2tl_tick_exact` (L2526/2532) も `rfl`。
- 重複ペア: buffer 要求、vault-pull 要求、`withdrawForMaxShares` の旧版は、
  proof map に採用した証明面から外して削除済み。
  `withdrawForMaxShares` の2定理 (L3534, L3587)。
- `BlastRadius.lean` の docstring に古い記述が残存: L927, L1537, L1856 は `updateRedemptionValue` を
  「placeholder no-op」と書いており、同ファイルの `step_updateRedemptionValue_exact` (L944) と
  `admin_alone_moves_redemption_price` (L1900) に反駁されています。L2402 は
  `catastrophicBackstop` を「sole writer」と呼びますが `redemption_price_writers` (L1569) は
  書き手が2つあることを証明しています。
- lint 警告 28件 (未使用 simp 引数、`simpa`→`simp`、未参照変数名)。機能影響なし。

---

## 6. 正確に述べられている主張(評価できる点)

- **`admin_alone_drains_reserve` (L1909) / `admin_alone_moves_redemption_price` (L1900)** —
  鋭く正確で、このファイルで最も価値のある結果。§1.1 の過大主張を falsify するのもこれらです。
- **`pauser_trace_blast_radius` (L486)** — 完全な frame
  (`{execTrace s σ with globalPause := b} = {s with globalPause := b}`)、任意長・任意 caller。強い。
- **`yield_distributor_trace_blast_radius` (L577)** — accrue-first 方式では `vestTotal` 単独が単調で
  ないことを docstring が正しく指摘し、`fullyVestedAmount + vestTotal` の合計で境界を証明。誠実。
- **`no_role_transfers_user_funds` / `no_role_burns_user_shares` / `no_role_debits_usdc` /
  `governance_token_balances_immutable`** — `poolRedeem`, `withdrawReserve`, `tick` を含めて `Op` 全網羅。
  RFQ の carve-out も隠さず開示。
- **`redemption_price_writers` (L1569) / `reserve_outflow_only_via_redemption` (L1661)** — 網羅的で正確。
  `withdrawReserve` / `poolRedeem` の出口を後から誠実に追加した経緯もインラインに記録。
- **`rfq_payout_is_set_by_execution_timing` (L3090)** — 算術を検算済み (100·ray/ray = 100、
  100·(ray/2)/ray = 50)。ただし README の「the counterparty does not need the admin key at all,
  only the clock」は言い過ぎです。trace 2 の価格変更は `s.admin` が呼ぶ `Op.updateRedemptionValue`
  そのもので、示されているのは *正直な admin* の価格更新 + counterparty のタイミング選択であって、
  counterparty 単独の攻撃ではありません。
- **`RedemptionOracle.lean` 全体** — 8定理すべて健全。`published_le_cap` が
  `Nat.min_le_right` 一行で構造的境界であることを示し、`cap_immutable` を閉じた `Op` 上で網羅、
  トレースに持ち上げ。cap は実在し floor は実在しないという**逆方向の2つの結論**を出しているのが
  このモジュールの価値です。
- **`LiquidationBatcher.lean` 全体** — 5定理すべて健全。「遅延なし」と「無制限」を分離するという
  目的にちょうど合った強さ。
- **`CommitToken.lean`** — active surface は clock、cooldown、delay-change、commitment-bound の
  基礎定理に絞った。4インスタンス用の liveness witness と、top-up / all-or-nothing claim の
  単独 witness は proof map 外の生成物として削除済み。
  ただし `h_mem : d ∈ liveDeployments` が証明中で使われておらず (lint 警告)、定理は
  `h_cfg : s.unlockingDelay = d.unlockingDelay` だけで通ります — つまり「live な4つ」という
  限定は飾りで、実質は任意の delay に対する一般命題です(命題としては強いので害はないが、
  「4インスタンスで具体化した」という読み方は不正確)。
- **`MinterRateLimit.lean`** — 4定理。`tightening_does_not_unwind_the_window` と
  `window_frees_in_one_step` はどちらも具体 witness で正確。
- **`SpecDefects.lean`** — 2定理。`redemption_has_no_floor` は
  `∃ s'` を revert 分岐の排除まで含めてきちんと証明しています。
- **`Apyx.lean` で正確なもの**: 1:1 mint と 20日クールダウンの遷移効果、および
  `redemption_cycle_closes_after_cooldown` —
  deadline の `<` / `≤` 境界は正しく、ちょうど deadline での claim は成功)、
  flexible の3日最短と並行リクエスト、二重アキュムレータ vesting の保存
  (`req_credit_preserves_accrued_vest`)、no-rehypothecation (閉じた `Op` の全網羅)、
  mint/redeem の whitelist ゲート。

---

## 7. 推奨アクション(優先順)

0. **レート整合を不変量として証明するか、`lockApxUSD` の価格決定順序を直す** (§1.0-a) —
   `s.exchangeRate = computeExchangeRate s` を帰納的不変量として立てるか、`lockApxUSD` が
   価格決定の**前**に `pullVestedYield` / `updateExchangeRate` を呼ぶようにする。
   **実装側にも確認が必要な指摘**です。併せて `lockShares` の下限チェック
   (最小株数、または ERC-4626 の virtual shares / offset) を入れ (§1.0-b)、
   deployed contract 側に同等の緩和策があるかを確認する。
   README §4.2 の "No dilution" / "Inflation-attack immunity" / "Share-price monotonicity" の
   3行は、修正が入るまで**撤回または大幅に弱める**必要があります。
1. **README の残る見出しを定理に合わせて書き換える** — §1.1 (全鍵漏洩)、§1.3 (single-pending)、
   §1.4 (exchange rate)、§1.5 (credit_is_backed の単一ステップ性)、§2.3 (手数料 3.5%)、
   §1.0-e (`Solvent` の「required margin」)。これはコード修正なしで今日できます。
2. **`rate_limit_linear_bound` と `timelock_escape_guarantee` の時間軸を base クロックに結び付ける** —
   `advanceEpoch` / `TLOp.tick` を `Op.tick` 経由に変え、`countEpochs` / `countTicks` の代わりに
   `base.now` の差分で述べる。そうでなければ README §5-2/§5-3 からこれらの定理の引用を外す。
3. **`admin_rfq_coalition_drains` の witness を `usdcReserve := 100` にする** —
   既存の human review の指摘どおり。連合に帰属する実損を示せるようになります。
4. **`Op.withdraw` / `Op.redeem` を `requestUnlockStep` 経由に統一** し、
   `req_single_pending_redemption_per_user` を一意性 (`∀ id, … → id = id₀`) として述べ直す。
5. **`claimUnlock` で `unlockRequests` / `unlockRequestId` をクリア** (§2.2) — 恒久ロックのバグ。
6. **`creditYield` の二重計上を解消** (§2.1) — `usdcReserve` か `vestTotal` のどちらか一方に。
7. **`flexibleUnlockFee` の起点を `minFlexibleClaim` に移す** (§2.3) — 仕様が「最初に claim できる時点で
   3.5%」なら `350 − ((elapsed − minFlexibleClaim)·340)/(cooldownPeriod − minFlexibleClaim)`。
8. **`-- BROKEN:` 約800行を削除** (§5) と定理数の訂正 (§4)。
9. `Japandefencemap.lean` を修正して import に戻すか、`outputs/` 側の成果物と切り離す
   (現状 import は削除済み、ファイルは残置)。
