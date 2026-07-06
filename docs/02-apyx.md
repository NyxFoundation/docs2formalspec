# Apyx プロトコル調査メモ (2026-07-06)

## 概要
**Apyx (apyx.fi)** — 初の「Dividend-Backed Dollar (DBD)」プロトコル。DAT企業(Strategy の STRC 11.25% / SATA 12% 優先株)+短期国債+ステーブルコインを担保とする合成ドル。DeFi Development Corp (Nasdaq: DFDV) チームが構築。ETHメインネット 2026-02-18 ローンチ、Base / BNB 展開済。apxUSD供給 ~524M(cap 750M)。

※ Apyx Medical (Nasdaq: APYX、医療機器) は別物。

## 入力に使うドキュメントURL
インデックス: **https://docs.apyx.fi/llms.txt**(各ページが `.md` 直配信 — trafilatura不要、生Markdownで取得可能)

コア(パイプライン入力の第一候補):
- https://docs.apyx.fi/apyx-overview/how-apyx-works.md
- https://docs.apyx.fi/product-overview/apxusd-overview.md
- https://docs.apyx.fi/product-overview/apyusd-overview.md
- https://docs.apyx.fi/solution-overview/peg-stability-model.md
- https://docs.apyx.fi/solution-overview/apyusd-yield-distribution.md
- https://docs.apyx.fi/solution-overview/capitalization-framework.md
- https://docs.apyx.fi/technical-overview/protocol-contracts-overview.md
- https://docs.apyx.fi/technical-overview/locking.md
- https://docs.apyx.fi/technical-overview/unlocking.md

補助: risk-management/apyx-and-dat-risks.md, resources/audits.md, technical-overview/glossary.md

## コード / 監査
- GitHub: https://github.com/apyx-labs/evm-contracts (Foundry, invariantテストあり)
- 契約docs: https://apyx-labs.github.io/evm-contracts/
- 監査: Quantstamp 2026-02, Zellic 2026-03, **Certora 2026-03** (https://www.certora.com/reports/apyx-apxusd), Quantstamp 2026-04, Halborn 2026-06
- Yearn リスク評価 3.66/5 "Elevated": https://github.com/yearn/risk-score/blob/master/reports/report/apyx-apxusd.md
  - 最大リスク指摘: **ApxUSDRateOracle の setRate がタイムロック0秒**

## メカニズム(形式化対象)
- **apxUSD**: 非利回り合成ドル。UUPS proxy、supply cap、pause、denylist、EIP-2612。MinterV0(EIP-712署名オーダー、m-of-n multisig、レート制限、60s delay)で$1ミント。償還はホワイトリスト制・USDC建てで償還価値ベース。
- **apyUSD**: apxUSDをラップする ERC-4626 vault(「locking」)。月次オフチェーン配当を LinearVestV0 で ~20日線形ベスト。YieldDistributor がミント手数料もベストへ。アンロックは CommitToken/UnlockToken 経由のクールダウン式非同期償還。**預託apxUSDの再担保化(rehypothecation)なし**が明示的不変条件。
- **アクセス制御**: OZ AccessManager。ADMIN=4-of-6 Safe(0s)、UPGRADER=3-of-6(3日delay)、PAUSER即時、MINT_STRAT=MinterV0(60s)。

## 形式化候補プロパティ(調査エージェント提案)
1. `totalSupply ≤ supplyCap`、供給変化は認可mint/burnのみ
2. ERC-4626健全性: round-trip `convertToAssets(convertToShares(a)) ≤ a`
3. vault資産保存: 増=deposit+vest release、減=withdraw/unlockのみ(再担保化パス不存在)
4. LinearVestV0: released ≤ funded、時間単調、線形スケジュール超過なし
5. share price 非減少(明示的admin loss以外)、他ユーザー希釈なし
6. 丸めは常にvault有利(インフレ攻撃防止)
7. Commit/Unlock: cooldown後の引出可能性(liveness)、コミット超過引出不可、cooldownバイパス不可、他人のコミット請求不可
8. mint権限はMINT_STRATのみ、upgrade は3日delay後のみ
9. denylist健全性: 凍結アドレスは全パスで送受信・mint不可
10. rate oracle: setRate権限制限、任意rate値での安全性(zero-rate mint exploit なし)← Yearn指摘の最重要ターゲット
11. pause時の全状態変更操作の失敗、unpauseでの完全復元

## 主要コントラクトアドレス (Ethereum)
apxUSD `0x98A878b1Cd98131B271883B390f68D2c90674665` / apyUSD `0x38EEb52F0771140d10c4E9A9a72349A329Fe8a6A` / AccessManager `0xe167330e2eac88666de253e9607c6d9ae0ca2824` / RateOracle `0xa2ef2e7bf32248083e514a737259f3785ea8d37d` / UnlockToken `0x93775E2dFa4e716c361A1f53F212c7AE031BF4e6`
