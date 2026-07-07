"""Renders docs/assets/architecture.png: the docs2formalspec pipeline diagram.

Run with: uv run --with matplotlib python docs/generate_architecture.py
Mirrors the actual stage sequence in src/d2fs/pipeline.py; keep in sync when it changes.
"""

from __future__ import annotations

import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch

STAGE_COLOR = "#3B5C8C"
STAGE_TEXT = "#FFFFFF"
ARTIFACT_COLOR = "#EDEBE3"
ARTIFACT_EDGE = "#8A8577"
ARTIFACT_TEXT = "#2B2B2B"
ARROW_COLOR = "#3B5C8C"
LOOP_COLOR = "#B0472B"
BG = "#FFFFFF"

STAGE_W, STAGE_H = 3.6, 0.72
ART_W, ART_H = 2.6, 0.56
STAGE_X = 1.2
ART_X = STAGE_X + STAGE_W + 1.0

stages = [
    ("ingest", "URL / .md / file -> markdown"),
    ("extract_requirements", "per-doc RFC2119 JSON, merge + dedup\n+ contradiction check"),
    ("render_spec", "normative spec document"),
    ("model summary (LLM)", "state-transition model in prose"),
    ("gen_lean", "State + Op + step, one theorem\nper formalizable requirement"),
    ("check_and_repair", "lake build loop: per-decl repair ->\nsorry-stub -> BROKEN-kill, <=6 rounds"),
    ("roundtrip_review", "LLM judge: informalize each theorem,\ncompare against the requirement"),
]

artifacts = [
    "corpus.md",
    "requirements.json",
    "SPEC.md",
    "model.md",
    None,
    "<Name>.lean\nleancheck.json",
    "review.json",
]

n = len(stages)
row_h = 1.35
fig_h = row_h * n + 3.4
fig_w = 13.2

fig, ax = plt.subplots(figsize=(fig_w, fig_h))
fig.patch.set_facecolor(BG)
ax.set_facecolor(BG)
ax.set_xlim(0, fig_w)
ax.set_ylim(0, fig_h)
ax.axis("off")

title_y = fig_h - 0.6
ax.text(fig_w / 2, title_y, "docs2formalspec pipeline", ha="center", va="center",
        fontsize=18, fontweight="bold", color="#1A1A1A", family="sans-serif")
ax.text(fig_w / 2, title_y - 0.42, "sources (documentation URLs / files) -> RFC 2119 spec + machine-checked Lean 4 model",
        ha="center", va="center", fontsize=10.5, color="#555555", family="sans-serif")

top_y = fig_h - 2.3
centers = [top_y - i * row_h for i in range(n)]

# entry point above the first stage
entry_y = centers[0] + row_h * 0.62
ax.text(STAGE_X + STAGE_W / 2, entry_y, "sources: list[str]", ha="center", va="center",
        fontsize=10, style="italic", color="#333333")
ax.add_patch(FancyArrowPatch((STAGE_X + STAGE_W / 2, entry_y - 0.12),
                              (STAGE_X + STAGE_W / 2, centers[0] + STAGE_H / 2 + 0.03),
                              arrowstyle="-|>", mutation_scale=14, color=ARROW_COLOR, linewidth=1.6))

for i, ((name, detail), art) in enumerate(zip(stages, artifacts)):
    cy = centers[i]
    box = FancyBboxPatch((STAGE_X, cy - STAGE_H / 2), STAGE_W, STAGE_H,
                          boxstyle="round,pad=0.06,rounding_size=0.08",
                          linewidth=0, facecolor=STAGE_COLOR)
    ax.add_patch(box)
    ax.text(STAGE_X + STAGE_W / 2, cy + 0.10, name, ha="center", va="center",
            fontsize=11.5, fontweight="bold", color=STAGE_TEXT, family="monospace")
    ax.text(STAGE_X + STAGE_W / 2, cy - 0.19, detail, ha="center", va="center",
            fontsize=8.3, color="#DCE3EE", linespacing=1.4)

    if art:
        abox = FancyBboxPatch((ART_X, cy - ART_H / 2), ART_W, ART_H,
                               boxstyle="round,pad=0.05,rounding_size=0.06",
                               linewidth=1.1, edgecolor=ARTIFACT_EDGE, facecolor=ARTIFACT_COLOR)
        ax.add_patch(abox)
        ax.text(ART_X + ART_W / 2, cy, art, ha="center", va="center",
                fontsize=9, color=ARTIFACT_TEXT, family="monospace", linespacing=1.3)
        ax.add_patch(FancyArrowPatch((STAGE_X + STAGE_W + 0.05, cy), (ART_X - 0.05, cy),
                                      arrowstyle="-|>", mutation_scale=11,
                                      color=ARTIFACT_EDGE, linewidth=1.1, linestyle=(0, (3, 2))))

    if i > 0:
        prev_cy = centers[i - 1]
        ax.add_patch(FancyArrowPatch((STAGE_X + STAGE_W / 2, prev_cy - STAGE_H / 2 - 0.03),
                                      (STAGE_X + STAGE_W / 2, cy + STAGE_H / 2 + 0.03),
                                      arrowstyle="-|>", mutation_scale=14,
                                      color=ARROW_COLOR, linewidth=1.6))

# feedback loop: roundtrip_review -> regen_flagged -> back into check_and_repair
review_cy = centers[-1]
repair_cy = centers[-2]
loop_x = STAGE_X - 0.75
ax.add_patch(FancyArrowPatch((STAGE_X, review_cy), (loop_x, review_cy),
                              connectionstyle="arc3,rad=0", arrowstyle="-", color=LOOP_COLOR, linewidth=1.6))
ax.add_patch(FancyArrowPatch((loop_x, review_cy), (loop_x, repair_cy),
                              connectionstyle="arc3,rad=0", arrowstyle="-", color=LOOP_COLOR, linewidth=1.6))
ax.add_patch(FancyArrowPatch((loop_x, repair_cy), (STAGE_X - 0.03, repair_cy),
                              arrowstyle="-|>", mutation_scale=14, color=LOOP_COLOR, linewidth=1.6))
ax.text(loop_x - 0.18, (review_cy + repair_cy) / 2, "regen_flagged\n(mismatch/vacuous ->\nregenerate w/ judge note)",
        ha="right", va="center", fontsize=8, color=LOOP_COLOR, linespacing=1.3, style="italic")

# relean shortcut: skip ingest..model summary, re-enter at gen_lean using saved requirements.json + model.md
shortcut_x = ART_X + ART_W + 0.7
shortcut_y_top = centers[1] + STAGE_H / 2 + 0.22
gen_lean_cy = centers[4]
ax.add_patch(FancyArrowPatch((shortcut_x, shortcut_y_top), (shortcut_x, gen_lean_cy),
                              connectionstyle="arc3,rad=0", arrowstyle="-", color="#5A8A3A", linewidth=1.6,
                              linestyle=(0, (5, 3))))
ax.add_patch(FancyArrowPatch((shortcut_x, gen_lean_cy), (STAGE_X + STAGE_W + 0.05, gen_lean_cy),
                              arrowstyle="-|>", mutation_scale=13, color="#5A8A3A", linewidth=1.6,
                              linestyle=(0, (5, 3))))
ax.plot([shortcut_x], [shortcut_y_top], marker="o", color="#5A8A3A", markersize=5)
ax.text(shortcut_x + 0.15, (shortcut_y_top + gen_lean_cy) / 2,
        "d2fs relean\n(reuse saved\nrequirements.json\n+ model.md,\nskip ingest/extract/\nspec/model steps)",
        ha="left", va="center", fontsize=8, color="#5A8A3A", linespacing=1.3, style="italic")

# final output note
done_y = centers[-1] - row_h * 0.62
ax.add_patch(FancyArrowPatch((STAGE_X + STAGE_W / 2, centers[-1] - STAGE_H / 2 - 0.03),
                              (STAGE_X + STAGE_W / 2, done_y + 0.12),
                              arrowstyle="-|>", mutation_scale=14, color=ARROW_COLOR, linewidth=1.6))
ax.text(STAGE_X + STAGE_W / 2, done_y - 0.05,
        "outputs/<name>/  (all artifacts above, one directory per analyzed system)",
        ha="center", va="center", fontsize=9.5, style="italic", color="#333333")

plt.tight_layout()
out_path = "docs/assets/architecture.png"
plt.savefig(out_path, dpi=200, facecolor=BG, bbox_inches="tight")
print(f"wrote {out_path}")
