#!/usr/bin/env bash
#
# build.sh — 7章のマークダウンを結合し、目次付きの1ファイル textbook.md を生成する。
#
# 使い方:
#   ./build.sh            # このスクリプトのあるディレクトリで実行
#
# 出力:
#   textbook.md           # 表紙 + 目次 + ch1..ch7 を章区切りで結合したもの
#
set -euo pipefail

# スクリプト自身の場所を基準にする（どこから呼んでも動くように）
cd "$(dirname "$0")"

OUT="textbook.md"
CHAPTERS=(ch1.md ch2.md ch3.md ch4.md ch5.md ch6.md ch7.md)

# 全章が揃っているか先に検査する
for f in "${CHAPTERS[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "エラー: 章ファイルが見つかりません: $f" >&2
    exit 1
  fi
done

# 表紙を書き出す（> でファイルを新規作成）
cat > "$OUT" <<'HEADER'
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

HEADER

# 各章を順に追記する（>> で追記）。章の間には水平線と改行を挟む。
for f in "${CHAPTERS[@]}"; do
  cat "$f" >> "$OUT"
  printf '\n\n---\n\n' >> "$OUT"
done

# 末尾の余分な区切りを整える情報を出力
LINES=$(wc -l < "$OUT" | tr -d ' ')
echo "生成完了: $OUT (${LINES} 行、${#CHAPTERS[@]} 章)"
