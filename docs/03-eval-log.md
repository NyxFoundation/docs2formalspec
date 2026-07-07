# 評価ログ

## 手動形式化パス (Fable5) — 2026-07-06 23:00–2026-07-07 00:00

Run 15時点の「ローカルLLM構成での飽和点」(53%, proved 4/55)は自動化パイプライン
(Ollama Cloud: qwen3-coder:480b)固有の限界であって、モデル品質を上げれば突破できる
という仮説を検証。`src/d2fs/*.py` の自動パイプラインは一切使わず、Fable5モデルの
サブエージェントに `lean/D2fsSpecs/Apyx.lean` を直接手書きで編集させ、都度
`lake build` で検証・小刻みにcommitさせた(既存sorryの実証明化 + missing/mismatch
28要件の追加formalize、必要に応じ`step`未実装opの実装も含む)。

| メトリクス | Run 15 (自動, 最終) | 手動パス 第1弾 | **手動パス 第2弾(mismatch是正)** |
|---|---|---|---|
| theorems (live) | 55 | 74(新規19件追加) | **73**(1件をunformalizable宣言へ) |
| proved (sorryなし) | 4 | 74 | **73**(全定理でsorry根絶、変わらず) |
| killed | 9 | 9 | 9(変更なし) |
| review full / full+partial | 9 / 53% | 17 / 78% | **20 / 82%** |

第2弾: 第1弾後のreview.jsonが返した mismatch 9件(具体的な審判コメント付き)を
別のFable5サブエージェントに手渡し、8件は要件の核心(優先株非移転・非リベース・
過剰担保不変条件・YieldDistributor入金・cooldown外への利回り支払い・新規ロックの
即時利回り参入・UnlockTokenへの即時mint・vault操作専有性)を捉えるよう文言と証明を
再構築、1件(singleton-unlockToken-instance、「コントラクトインスタンスが1つだけ
存在する」という配備事実)は単一Stateモデルでは誠実に表現不能と判断し
`-- UNFORMALIZABLE` 宣言に変更(mis-proveより正直な申告を優先)。
残る mismatch 5件は「UnlockTokenが別コントラクトである」「月次はカレンダー概念」
といった、単一State機械には収まりにくいマルチコントラクト前提の要件で、
singletonと同種の構造的限界。

## 第3弾: モデル拡張(UnlockTokenを明示的contractアイデンティティ化) — 2026-07-07 01:00–01:20

ユーザー判断: 残りのUnlockToken関連要件を「回避」するのではなく、モデル自体を
拡張して構造的に解消。`State`に `unlockTokenAddress`(コントラクトの識別子)と
`unlockTokenOperator`(認可アドレス、= vaultAddress)を新規フィールドとして追加。
副産物として実際のセキュリティギャップを発見・修正: `claimUnlock`/
`flexibleClaimUnlock` にはcaller認可チェックが一切なく、**誰でも他人の代理で
請求できてしまっていた**。`caller = owner ∨ caller = s.unlockTokenOperator` の
ゲートを追加(この変更で波及した既存証明はすべて修正、退行なし)。

| メトリクス | 第2弾後 | **第3弾(モデル拡張)後** |
|---|---|---|
| theorems (live) | 73 | **74** |
| proved (sorryなし) | 73 | **74** |
| review full / full+partial | 20 / 82% | **22 / 86%** |

singleton-unlockToken-instance(UNFORMALIZABLE宣言だった)とvault-operator-of-
UnlockTokenを実証明に置き換え。残る mismatch 3件(monthly-yield-rate-set,
pay-to-non-cooldown, unlockToken-mints-apxUSD_unlock-immediately)のうち
monthly-yield-rate-set はモデルにカレンダー/月概念が一切ないという、
今回とは別種のモデル拡張(時間の月次区切り)が必要な、より大掛かりな課題。

## 第4弾: カレンダー概念導入 + 残りmismatch再挑戦 — 2026-07-07

ユーザー判断: monthly-yield-rate-set を回避せずモデル拡張で解消。`State`に
`lastRateSetTime`(前回設定時刻)と `collateralYieldBase`(前月の担保由来利回り
基準値)を追加、`monthPeriod := 30日` 定数を新設。`Op.setYieldRate` を
「admin かつ前回設定から1ヶ月以上経過 かつ新レートがcollateralYieldBase以下」
というゲート付きにし、成功時に両フィールドを前進させる。cadence・派生・
livenessの3命題を実証明。pay-to-non-cooldownも creditYield 実行時の
「現在apyUSD保有者(=cooldown外)の按分請求権は厳密に増加、cooldown中の
残高は不変」という切り口で再証明に成功。unlockToken-mints-apxUSD_unlock-
immediately は原文("Minting occurs instantly after the vault deposits
assets")を確認した結果、既存の定式化(vaultがUnlockTokenへapxUSDを
入金するのと同一stepでのmint)が正しく、審判(LLM judge)側が「deposit」を
初回vault入金と誤読していると判断、docstringを原文に即して明確化するに留めた。

**重要な発見(測定手法上の注意)**: この後review判定を再実行したところ
full+partial が86%→82%へ低下したが、`git show` で当該3コミットの差分を
確認した結果、新たにmismatch判定された5件(redeem-liquidate-usdc等)は
**今回一切変更していない**コードだった。つまりこれはコード側の後退では
なく、**ラウンドトリップ審判(LLM judge)自体のサンプリング揺らぎ**
(full/partial/mismatchの境界事例で判定が run ごとに変動する)。
これまでの4回の計測で observed range は 78%〜86%(平均約82%)。
以後この揺らぎ幅を「真の忠実カバレッジ」として認識し、単一runの数値を
過信しないこと。

## 第5弾: 「形式化不能」宣言8件の再検討 — 2026-07-07

自動パイプライン最初期(モデルにERC-4626ヘルパー/UnlockTokenアイデンティティ/
月次カレンダーが実装される前)に「形式化不能」と宣言されていた8件を、
拡張後の現行モデルに対して再検証。6件を実証明化:

- **no-rehypothecation**: `Op`が閉じた帰納型であることを利用し、
  `vaultApxUSDBal`が lock/withdraw/redeem 以外の経路で変化しないことを
  全ケース網羅で証明(貸出・再担保化の経路が存在しないことの直接証明)
- **erc4626-compliance**: 既存のERC-4626ヘルパー関数(convertToShares/
  Assets, preview*, max*)群の相互整合性を9個の連言として証明
- **unlock-token-nontransferable**: 全op網羅により、unlockTokenOwnerが
  他アドレスへ再割当されることがない(不変 or burn のみ)ことを証明
- **unlock-cannot-be-cancelled**: 全op網羅により、cooldown/claim経路以外で
  pending requestが消滅しないことを証明
- **cooldown-removal**: withdraw/redeemが同stepでtotalSupply_apyUSDから
  離脱シェアをburnし、残存保有者の按分利回りが相対的に上昇することを証明
- **yield-distribution-period**: vestPeriod=20日の設定下でcreditYieldが
  ちょうど20日で完全distributeされることを証明(既存のcontinuous-stream
  定理を再利用)

残り2件は現行モデルに対して再検証した上で正直にUNFORMALIZABLE維持:
- **price-may-include-spreads**: mint経路はハードコードで1:1、spread
  パラメータ自体が存在せずMAY許可を体現する経路がない
- **rebalance-overcollateralization**: 担保バスケットの構成やアクティブな
  リバランスopが未モデル化(受動的なovercollateralization-limit不変条件
  のみ存在)

| メトリクス | 第4弾後 | **第5弾後** |
|---|---|---|
| theorems (live) | 74 | **80**(新規6件) |
| proved (sorryなし) | 74 | **80**(100%維持) |
| killed | 9 | 8(古いUNFORMALIZABLEマーカー行削除の副産物、実質変化なし) |
| review full / full+partial | 15 / 82% | **19 / 92%** |
| unformalizable | 8 | **2** |

第4弾のjudgeノイズ発見以降も、mismatch 4件中 cooldown-no-yield /
unlockToken-mints-apxUSD_unlock-immediately は既知の既視感がある判定
(それぞれ過去に一度full/partial側だった実績あり、または原文確認済みの
judge誤読の疑い)であり、92%という数値自体にも数ポイントの揺らぎ余地が
あることに留意。

## 第6弾: arbitrage価格ゲート + cooldown系再定式化、および自己発見regression修正 — 2026-07-07

ユーザー判断でさらに1ラウンド継続。3件に着手:
- **arbitrage-mint-access**: 「apxUSDが$1超過で取引されている場合のみ」という
  市場価格条件がモデルに存在しなかったため、`apxUSDMarketPrice`フィールドと
  `Op.setApxUSDMarketPrice`(oracle限定)を新規追加。`Op.mintApxUSD`
  (arbitrage経路と判定、SPEC.md記載に基づく)にプレミアム条件ゲートを実装し
  実証明。
- **cooldown-no-yield** / **cooldown-removal**: 「exchange rate固定」「pool
  からの除外」という原文語彙により忠実な形へ再定式化。

**この過程で実際のregressionを1件、push前に自己発見・修正**:
`req_mint_price`(「新規発行apxUSDは常に$1で価格付け」)が、上記のarbitrage
ゲート追加の巻き添えで`apxUSDMarketPrice > ray`という誤った前提付きに
弱化されていた(標準の$1価格保証を、arbitrage条件下でのみの主張に
変えてしまっていた)。標準経路`Op.depositUSDC`(無条件)に retarget し、
arbitrage経路用の別定理`req_mint_price_arbitrage_pathway`を新設して解消。

| メトリクス | 第5弾後 | **第6弾(修正込み)後** |
|---|---|---|
| theorems (live) | 80 | **81** |
| proved (sorryなし) | 80 | **81**(100%維持) |
| review full / full+partial | 19 / 92% | **23 / 92%**(同水準) |

第6弾後のmismatch 4件(token-no-rebase, redemption-exchange-rate-multiplier,
pay-to-non-cooldown, unlockToken-mints-apxUSD_unlock-immediately)は
**いずれも過去ラウンドで一度以上full/partial判定を受け、コード変更なしで
再度mismatchへ揺れ戻った項目**であり、judgeノイズの再確認となった。

**総括(全6ラウンド)**: 53%→92%(揺らぎ込みで実質85〜92%)、証明率
4/55→81/81(100%)。収穫逓減とjudgeノイズの床に明確に到達したと判断し、
ここを最終区切りとする。以後の改善には(a) 審判呼び出しをN回実行し
多数決を取る、(b) 別モデルでの独立judge、(c) 決定的(非LLM)な
ラウンドトリップ検証手法への置き換え、などLLM judge自体の分散を
下げる手当てが前提となる。

## 最終計測: 3回独立実行の多数決 — 2026-07-07

judgeノイズを追加ラウンドで潰すのではなく、測定手法自体を頑健にする方針に
転換。**同一の(変更なし)Leanコードに対しラウンドトリップ審査を3回独立
実行**し、要件ごとに多数決判定を取った。

| run | full | partial | mismatch | unformalizable | full+partial |
|---|---|---|---|---|---|
| 1 | 23 | 48 | 4 | 2 | 92.2% |
| 2 | 24 | 50 | 1 | 2 | 96.1% |
| 3 | 22 | 51 | 2 | 2 | 94.8% |
| **多数決** | **23** | **49** | **3** | **2** | **93.5%** |

77件中17件で3回の判定が割れた(主にfull/partial境界)。注目すべき点:
- **unlockToken-mints-apxUSD_unlock-immediately**: 3回ともmismatch
  (満場一致)。第6弾でcorpus.mdのシーケンス図まで確認し形式化は正しいと
  判断していたが、judgeは一貫して不一致と読む。**ノイズではなく再現性の
  ある解釈の相違**として正直に記録。
- **price-may-include-spreads / rebalance-overcollateralization**:
  3回とも unformalizable で完全一致。モデルの範囲外という判断が
  頑健であることを確認。
- **pay-to-non-cooldown**: 2/3でmismatch(多数決もmismatch)。
- **token-no-rebase**: full/partial/mismatchが1票ずつの三すくみ
  (真の多数決なし、僅差の判定)。

`outputs/apyx/review.json` を多数決結果に更新し、生の3回分は
`review_run{1,2,3}.json` として保存(再現性のため)。

**最終確定値**: 定理81件、証明済み81件(sorry 0、100%)、忠実カバレッジ
(3回多数決)**93.5%**(full 23 / partial 49 / mismatch 3 / unformalizable 2)。
単一run値(78〜96%)ではなくこの多数決値を正式な最終数値として採用する。

## SPEC.md 側の点検 — 2026-07-07

ユーザーから「6ラウンドの手動形式化を経て、RFC2119スペック文書(SPEC.md)側も
きちんと修正されているのか」という指摘。実際に `requirements.json`(82件)と
`SPEC.md` を突合した結果、2つの実際の齟齬を発見:

1. **完全な欠落**: `token-no-rebase` と `cooldown-no-yield` は
   `requirements.json` に抽出済みだったが、**SPEC.md には一度も
   レンダリングされていなかった**(render_specステージの抜け漏れ)。
   該当セクション(State / Arithmetic)に行を追加して解消。
2. **要件文言そのものの曖昧さ**: `unlockToken-mints-apxUSD_unlock-immediately`
   の文言("immediately after the deposit")が、"どの deposit か"を
   明示していなかった。これが3ラウンドにわたり judge が一貫して
   mismatch判定を出し続けた**真因**であり、ノイズでもLean側の不備でも
   なかったことが判明: `requirements.json` の statement を「vaultが
   UnlockTokenへapxUSDを入金する方のdeposit(ユーザーの当初のvault入金
   ではない)」と明記した上で、**同一の(変更していない)Lean定理を
   3回再判定した結果、3/3でfullに反転**。要件抽出/文書化段階の曖昧さが
   下流の忠実性判定を継続的に汚染していた実例として記録に値する。

この修正で `review.json` の多数決カバレッジは **93.5%→94.8%** に上昇。
`requirements.json`/`SPEC.md` の両方を修正したのは、judgeへの入力
(requirements.json)とドキュメント(SPEC.md)の内容が乖離すると
同じ曖昧さが再発するため。

**教訓**: 忠実カバレッジの伸び悩みは必ずしもLean形式化側の問題とは限らず、
上流の要件抽出/文書化段階の曖昧さに起因することがある。今後同様の
持続的mismatchに遭遇した場合は、Lean側を疑う前にまず該当要件の
`source_quote`/原文コンテキストへ立ち返り、requirements.json の
statement自体が一意に読めるか確認すべき。

6ラウンドの手動形式化 + 測定手法の頑健化 + SPEC.md整合性点検を経て、
本エフォートを終了とする。

副産物として `src/d2fs/review.py` のバグを発見・修正: ラウンドトリップ審査が
theorem名→要件idの逆引きに `name.removeprefix("req_").replace("_", "-")` という
素朴な変換を使っており、id内に大文字が残るもの(`apyUSD`, `UnlockToken`,
`minAssets` 等)で一致せず、実際にはtheoremが存在する7要件が「missing」と
誤判定されていた(過去の全run共通のバグ)。両側を小文字化+非英数字除去で
正規化するよう修正 → 修正前後で missing 7→0、full+partial 74%→78%。

**結論**: Run 15の「モデル能力の限界」は事実だが、それは*自動パイプラインが
使うモデル層*の限界であり、より高品質なモデル(Fable5)による手動パスでは
sorry根絶+忠実カバレッジ78%まで到達した。パイプライン設計自体は健全で、
生成・修復ステージのモデルグレードを上げれば自動化のままでも同等の改善が
見込める(次段候補: `D2FS_LEAN_MODEL`/`D2FS_REPAIR_MODEL` を高グレードモデルに)。
残る mismatch 9件(redeem-no-share-transfer, token-no-rebase,
overcollateralization-limit, yield-distributor-credit, pay-to-non-cooldown,
new-locked-receives-yield, unlockToken-mints-apxUSD_unlock-immediately,
singleton-unlockToken-instance, vault-operator-of-UnlockToken)は
コンパイル・証明は通るが要件の核心を捉え切れておらず、次の手動/高グレード
パスの対象。

## Run 13–15 (exemplar導入と副作用の解消) — 2026-07-06 21:30–22:50

| メトリクス | Run 12 | Run 13 | Run 14 | **Run 15 (最終)** |
|---|---|---|---|---|
| theorems (live) | 43 | 5 | — (明示エラー) | **55** |
| proved | 7 | 3 | — | 4 |
| killed | 22 | 1 | — | 9 |
| review full / full+partial | **14** / 47% | 0 / 0% | — | 9 / **53%** |

- Run 13: 検証済みexemplar(ToyVault)導入 → 証明率は3/5と最高率だが、モデル生成が
  toyの小ささに引きずられ**スタブState**を生成、76/77が形式化不能宣言。
  → exemplarは定理プロンプト専用に、モデルプロンプトには完備性要求を明示、
  形式化不能率≥50%でモデル再サンプルするゲートを追加。
- Run 14: 完備性要求で大型化したモデルが**ヘルパーをState定義より前に配置**(前方参照
  不可)し3サンプル全滅 → ゲートが設計通り明示的エラーで停止(空洞出力の根絶を確認)。
  → 宣言順序をモデル/修復プロンプトに明示。
- Run 15: 全修正の合流。66定理生成→55生存(過去最多)、full+partial **53%**(最高)。

## 最終総括(15ラン)

**到達点**: apyx(82要件・77 formalizable)に対し
- SPEC.md: RFC2119準拠スペック(ボイラープレート/用語集/システムモデル/出典付き)
- Apyx.lean: **コンパイル保証付き** 55定理(RFC2119文をdocstringに埋込み、双方向トレース)
- 忠実カバレッジ(Clover式ラウンドトリップ審査 full+partial)**53%**、機械証明4-10件/run
- 全メトリクスは正直申告(vacuous/killed/sorry を別掲)

ローカルLLM(Ollama Cloud)構成での飽和点。Verina (ICLR 2026) のフロンティアモデル値
(スペック健全完全51%)と同水準であり、パイプライン設計の限界ではなくモデル能力の限界。
ベスト出力は outputs/apyx (Run 15)、full判定重視なら outputs/apyx/archive/run12。

**さらなる改善はモデル資源が必要**: k-sample選抜(コスト2倍)、実CVL性質コーパスのRAG
(PropertyGPT式)、Goedel-Prover-V2証明パス(要ローカルGPU、Ollama Cloud未提供)。

## Run 12 (relean, modelgen=deepseek-v4-pro) — 2026-07-06 21:20 ✅ 現時点のベスト

| メトリクス | Run 8 (旧ベスト) | **Run 12** |
|---|---|---|
| モデルゲート | r1通過 | r2通過、**拡張もr1通過** |
| theorems (live) / killed | 49 / 2 | 43 / 22 |
| proved (機械証明) | 8 | 7 (auto-prove +4) |
| vacuous (live) | 0 | 0 |
| review full | 11 | **14**(フィードバック前9→14) |
| review full+partial | 35/72 (49%) | 36/77 (47%) |

- deepseek-v4-pro のモデルは64定理(過去最多)を引き出したが、statementの外れも増え
  killed 22。full判定は最多で、審判フィードバック再生成の効果(+5 full)も確認。
- **結論**: ローカルLLM構成での到達点はおよそ「コンパイル100%・忠実カバレッジ~50%・
  機械証明~15-20%」。Verina(ICLR 2026)のフロンティアモデル値(スペック健全完全51%)
  とほぼ同水準であり、パイプライン設計としては飽和点に到達。

## 総括(12ラン)

| 失敗モード | 対策 | 効果 |
|---|---|---|
| 空虚定理 (Run 1: 64/64) | 2段階生成+禁止則+de-vacuate | 恒久的に0 |
| whole-file修復の定理削除 (Run 4) | per-declaration修復エンジン | 削除消滅 |
| パースエラーのカスケード誤爆 (Run 6-7) | **ブロック単体コンパイル検証** | killed 40→2 (Run 8) |
| statement幻覚識別子 | バッチ即時検証+リトライ | 部分的 |
| 証明の弱さ | cheap-tactic自動証明 | +4〜6/run |
| 要件の無言ドロップ | カバレッジ照合パス | missing 23→10 |
| 不忠実な形式化 | Clover式review+審判フィードバック再生成 | full +5/run |
| モデルサンプル分散 | ゲート+再サンプル+modelgen専用ロール | ゲート失敗の下流汚染を根絶 |

### 次の改善候補(未実装、優先順)
1. **few-shot exemplar**: AMM-in-Lean4 論文(arXiv:2402.06064)のイディオムを
   MODEL_SYSTEM / THEOREM_SYSTEM に注入(PropertyGPT のRAG知見の軽量版)
2. モデル k-sample 選抜(プローブバッチのコンパイル率でベスト選択)
3. 証明専用パス(Goedel-Prover-V2 はOllama Cloud未提供のため要ローカルGPU)


## Run 9–11 — 2026-07-06 18:00–19:30

| メトリクス | Run 9 | Run 10 (full) | Run 11 |
|---|---|---|---|
| 抽出 | (Run 3 の83再利用) | **82 (77 formalizable)** | Run 10 を再利用 |
| モデルゲート | ○ | **✗ 4ラウンド全滅→中断** | 4ラウンド目で辛勝 |
| theorems / proved / killed | 49 / 10 / 12 | — | 15 / 0 / 8 |
| auto-prove | +6 | — | +0 |
| coverage照合 | 8件回収 | — | 14+4件回収 |
| review full/partial | 9 / 25 | — | (log参照) |

### 知見
- 自動証明パス(+6)とカバレッジ照合(missing 23→10)は機能。
- **実行間分散の支配要因はドメインモデルの品質**: Run 8(良サンプル)49定理/killed 2
  vs Run 11(悪サンプル)15定理/proved 0。モデルが貧しいと定理は形式化不能宣言や
  キルに流れる。
- Run 10: モデルがゲート4ラウンド全滅 → best-effort続行が全下流を汚染 → **再サンプリング**
  実装(3サンプル、全滅なら明示エラー)。
- モデル生成専用ロール `D2FS_MODELGEN_MODEL` 追加。Run 12 で deepseek-v4-pro を試験
  (1コールなので速度より品質)。


## Run 8 (relean, ブロック単体検証) — 2026-07-06 17:45 ✅ 構造的ブレークスルー

| メトリクス | Run 7 | **Run 8** |
|---|---|---|
| コンパイル | ✅ r4(キル40の空洞) | **✅ r3** |
| theorems 生存 | 13/53 | **49/50**(キル2のみ) |
| proved / sorries | 3 / 10 | 8 / 41 |
| vacuous | 0 | 0 |
| review full/partial/mismatch | 5/5/1 | **11**/24/11 |

ブロック単体コンパイル検証がカスケード誤爆を根絶。収束も速い(3ラウンド)。

### 残課題 → Run 9 の変更(実装済)
1. proved 8/49 → **cheap-tactic自動証明パス**(LLM不要): sorryスタブに
   simp[step]/simp_all/unfold+split/omega/decide を順に試し、通れば採用
2. 真の欠落23要件(バッチ再生成時の無言ドロップ)→ **カバレッジ照合パス**:
   定理もUNFORMALIZABLE宣言も無い要件を検出して追加バッチ生成(≤2周)
3. (次回) review mismatch/vacuous 判定の修復ループへのフィードバック


## Run 7 (relean, バッチ即時検証) — 2026-07-06 17:25

結果: ✅コンパイル(r4)だが theorems 13 / proved 3 / **killed 40**。バッチ再生成の成功は 3/13。

### 決定的発見: エラー帰属のカスケード誤爆
キルされた定理を現行モデルに対し**単体コンパイルすると成功する**ことを確認。
壊れた定理Aのパースエラーは次の定理Bの行に「unexpected token 'theorem'」として
報告されるため、行範囲によるエラー帰属は無実の隣接ブロックを連鎖的に処罰していた
(Run 6-7 の大量キルの真因。バッチ検証の「失敗」も同じカスケードで過大計上)。

### Run 8 に向けた変更(実装済)
- エラー帰属を全廃し、**ブロック単体コンパイル検証**へ: 各定理を model+単体 でビルドし、
  本当に失敗するものだけをエスカレーション(修復→スタブ→キル)。検証済みはキャッシュ。
- 重複定理名の決定的デデュープ(後勝ちをキル)。
- フルビルドが個別検証後も失敗する場合のみ: モデル修復 or 該当ブロックの検証無効化。


## Run 5 / Run 6 (relean, per-decl修復エンジン) — 2026-07-06 16:30–17:15

| メトリクス | Run 5 | Run 6 |
|---|---|---|
| コンパイル | ❌ (境界バグでモデル修復が空回り) | ✅ round 5 |
| theorems / proved | 33 / 20 | 11 / (キル42) |
| vacuous | 0 | 0 |
| review full/partial/mismatch | 4 / 23 / 4 | 1 / 7 / 2 |

### Run 5 の失敗: 境界の行数不整合
build_file はモデル領域を rstrip して組み立てるのに、境界判定は未stripの行数を使用
→ モデル末尾の空行分だけ境界が最初の定理ブロックに食い込み、定理エラーが
「モデルエラー」と誤帰属 → モデルゲート(単体ではOK)を10回空回り。
→ 修正: 境界を組立時のオフセット(最初のブロックの開始行)から取得。

### Run 6 の失敗: statementの幻覚識別子で大量キル
53定理中42のstatementがモデルに存在しない識別子/フィールドを参照。
修復(モデル文脈が末尾12k切断で不十分)→スタブ(statementは残るので失敗)→キル
の順で53→11に減少。「コンパイル成功」は達成したが空洞化。
また旧メトリクスは BROKEN コメント内の sorry まで数えて proved=-34 と表示。

### Run 7 に向けた変更(実装済)
1. **バッチ即時検証** (AutoSpec式): 各定理バッチ生成直後に model+batch を単体コンパイル、
   失敗ならエラー付きで1回再生成(幻覚識別子をその場で修正)
2. repair_decl のモデル文脈を先頭14k(State/Op/stepは先頭にある)
3. メトリクスをlive行のみでカウント、killed を別掲


## Run 3 (フルパイプライン) / Run 4 (relean) — 2026-07-06 15:50–16:30

| メトリクス | Run 3 | Run 4 |
|---|---|---|
| 要件 (formalizable) | **83 (72)** ✅ merge修正が効いた | 同左を再利用 |
| モデルゲート | (未実装) | **phase1/拡張とも round 1 通過** ✅ |
| 定理数の推移 | 56 | 48 → **23**(修復が25定理を削除) |
| コンパイル | ❌ | ❌(手動kill) |

### Run 3 の失敗: 決定的スタブ自体のバグ
複数行statement内の `let s' :=` の `:=` を証明開始と誤認して statement を切断、
`let s' := sorry` というゴミを量産(51定理スタブしても収束しない原因)。
→ 修正: 最後の `:= by` でのみスタブ、term証明/破損statementは `-- BROKEN` キル。

### Run 4 の失敗: whole-file LLM修復がスケールしない
48定理+モデルのファイル全体をLLMに書き直させると出力上限で切断され、定理が
silently 消える(48→23)。「定理を削除するな」というプロンプト制約はサイズ限界に勝てない。

### Run 5 に向けた再設計(実装済): per-declaration 修復エンジン
- ファイルを「モデル領域 + 定理ブロック列」に分解、ビルドエラーを行範囲でブロックに帰属
- 失敗定理ごとに決定的エスカレーション: ①該当定理のみの標的LLM修復 → ②sorryスタブ → ③BROKENキル
- whole-file LLM書き直しを全廃。de-vacuationもブロック単位
- ユニットテスト5件(分解/再組立roundtrip、multiline-let保持、term証明キル等)


## Run 1 — ベースライン (2026-07-06, commit 061f547 相当)

入力: apyx コアdocs 9 URL。モデル: extract=gpt-oss:120b, lean=qwen3-coder:480b。

| メトリクス | 値 |
|---|---|
| 抽出要件 | 75 (formalizable判定 64) |
| SPEC.md | 29.5KB、RFC2119キーワード98出現、ボイラープレート/用語集/システムモデルあり |
| Lean コンパイル | ✅ round 3/6 |
| theorems / sorries | 64 / 64 |
| 空虚定理 (`: True`) | **64/64 (100%)** ← 致命的 |

### 所見
- **良**: SPEC.md は構造・網羅性とも実用レベル。State/操作関数のLeanモデル(pause/denylistゲート、cooldown、Option State)は妥当な形。
- **致命的**: 全定理が `theorem req_x : True := sorry`。一括生成 + コンパイル成功だけを報酬にした結果、モデルが定理を空虚化して逃げた。Clover/vacuity check の必要性(01-related-work.md)がそのまま再現。
- **中**: formalizable が過剰判定(オフチェーン custody/attestation 系まで true)。
- **小**: ingest のタイトルがサイト共通ボイラープレート行になる。`isWhitelistedUser := true` 等のプレースホルダがモデルを弱める。

## Run 2 — 2段階生成 + vacuityゲート (2026-07-06 15:22)

| メトリクス | Run 1 | Run 2 |
|---|---|---|
| 抽出要件 (formalizable) | 75 (64) | **25 (24)** ← merge過剰崩壊 |
| Lean コンパイル | ✅ r3 | ❌ 8ラウンド未収束 |
| theorems / proved / sorry | 64 / 0 / 64 | 14 / **13** / 1 |
| 空虚定理 | 64 | **0** ✅ |
| review | — | full 0, partial 9, missing 15 (うちUNFORMALIZABLE宣言12) |

### 所見
- 空虚化は根絶。13定理が実証明付き — 2段階生成+禁止則+cheap tacticsが機能。
- 未収束原因: 未知tactic等の構文エラーをLLM修復が直しきれない(qwen3-coderが同型の修正を繰り返す)。
- 要件25件は9ドキュメントに対して過少。merge promptが「テーマ類似」まで統合していた。
- UNFORMALIZABLE宣言12件: phase 1モデルに exchangeRate 単調性 / vesting / ERC4626 / rehypothecation 不在などのフィールド欠落。

### Run 3 に向けた変更(実装済)
1. PALM式**決定的sorryスタブ**: LLM修復4ラウンド超で、エラー行を含む定理の証明本体のみ機械的にsorry化(statement保持、収束保証)+ユニットテスト4件
2. merge prompt: 「同一操作・同一条件の真の重複のみ統合、汎化禁止」
3. **モデル拡張ラウンド**: UNFORMALIZABLE宣言された要件をフィードバックしてState/step拡張→当該定理を再生成
4. review: UNFORMALIZABLE宣言(unformalizable)と無言欠落(missing)を区別

### Run 2 に向けた変更
1. leangen 2段階化: モデル生成 → 要件バッチ(8件)毎に定理生成(モデル全文をコンテキスト、miniCTX知見)
2. 空虚定理の明示的禁止 + few-shot(executeOperation を参照する定理形を提示)
3. leancheck に vacuity 検出を追加、検出時は専用修復ラウンド
4. 証明試行の指示(simp [executeOperation] / omega / decide → 失敗時 sorry)
5. formalizable 基準: 「on-chain状態遷移モデル上で述語として書ける」に限定
6. ingest タイトル = 最初の `# ` 見出し
