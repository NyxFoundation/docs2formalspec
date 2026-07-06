"""Stage 5: Clover-style round-trip consistency gate.

Informalize each generated Lean theorem back to English, compare against the
source RFC2119 requirement with an LLM judge, and report coverage/mismatches.
"""

from __future__ import annotations

import re

from .config import Config
from .extract import Requirement
from .llm import LLM


def _normalize_id(s: str) -> str:
    """Case/separator-insensitive key so req ids with internal capitals (apyUSD,
    UnlockToken, minAssets, ...) still match their `req_<snake_case>` theorem name."""
    return re.sub(r"[^a-z0-9]", "", s.lower())

INFORMALIZE_SYSTEM = """\
You read Lean 4 theorem statements and restate exactly what they assert in plain \
English, faithfully — including what they do NOT assert. Do not consult the docstring \
comment; derive meaning from the formal statement alone. Output JSON only."""

JUDGE_SYSTEM = """\
You judge whether a formalization captures a normative requirement. Given an RFC 2119 \
requirement and an English reading of a Lean theorem, classify the match:
- "full": theorem faithfully captures the requirement's normative content
- "partial": captures a meaningful weakening/fragment (state which part is missing)
- "vacuous": theorem is trivially true or unrelated to the model's behavior
- "mismatch": asserts something different from the requirement
Be skeptical: a theorem about the wrong operation or missing the key condition is not \
"full". Output JSON only."""


REGEN_SYSTEM = """\
You rewrite ONE Lean 4 (v4.31, core + Std, NO mathlib) theorem whose formalization \
was judged inadequate against its RFC 2119 requirement. You receive the requirement, \
the judge's note explaining the inadequacy, the model (which compiles), and the old \
theorem. Return ONLY the corrected theorem (same name, with docstring) in one Lean \
code block. The statement must constrain the model's `step`/functions per the \
requirement; never `True`; use `sorry` for the proof if needed."""


def regen_flagged(llm: LLM, cfg: Config, reqs: list[Requirement], lean_code: str,
                  review: dict, module_name: str, log=print) -> tuple[str, int]:
    """Regenerate theorems judged mismatch/vacuous, keeping only compiling fixes."""
    from .leancheck import (_thm_name, build_file, compile_snippet, split_decls,
                            split_theorem_region)
    from .leangen import strip_lean_block

    flagged = {x["id"]: x for x in review["results"]
               if x.get("verdict") in ("mismatch", "vacuous")}
    if not flagged:
        return lean_code, 0
    model_region, region = split_theorem_region(lean_code, module_name)
    blocks = split_decls(region)
    req_by_id = {r.id: r for r in reqs}
    changed = 0
    for i, b in enumerate(blocks):
        name = _thm_name(b)
        if not name:
            continue
        rid = next((r.id for r in reqs
                    if _normalize_id(r.id) == _normalize_id(name.removeprefix("req_"))), None)
        if rid is None or rid not in flagged or rid not in req_by_id:
            continue
        r = req_by_id[rid]
        note = flagged[rid].get("note", "")
        log(f"[review] regenerating {name} ({flagged[rid]['verdict']})")
        text = llm.chat(
            cfg.lean_model,
            REGEN_SYSTEM,
            f"Requirement {r.id}: {r.statement}\n\nJudge's note: {note}\n\n"
            f"Model (compiles):\n```lean\n{model_region[:14_000]}\n```\n\n"
            f"Old theorem:\n```lean\n{b}\n```",
            max_tokens=4000,
        )
        cand = strip_lean_block(text).strip()
        if "theorem" in cand:
            ok, _ = compile_snippet(cfg, module_name, model_region, cand)
            if ok:
                blocks[i] = cand
                changed += 1
    if not changed:
        return lean_code, 0
    new_code, _ = build_file(model_region, blocks, module_name)
    return new_code, changed


def _split_theorems(lean_code: str) -> dict[str, str]:
    """Map theorem name -> full theorem text (docstring excluded)."""
    thms = {}
    pattern = re.compile(
        r"^theorem\s+([A-Za-z0-9_']+)(.*?)(?=^(?:/--|theorem|def|end|structure|--)\s|\Z)",
        re.S | re.M,
    )
    for m in pattern.finditer(lean_code):
        thms[m.group(1)] = ("theorem " + m.group(1) + m.group(2)).strip()
    return thms


def roundtrip_review(llm: LLM, cfg: Config, reqs: list[Requirement], lean_code: str) -> dict:
    theorems = _split_theorems(lean_code)
    by_req: dict[str, str] = {}
    for name, text in theorems.items():
        by_req[_normalize_id(name.removeprefix("req_"))] = text

    from .leangen import find_unformalizable

    declared_unform = set(find_unformalizable(lean_code))
    results = []
    for r in reqs:
        if not r.formalizable:
            continue
        thm = by_req.get(_normalize_id(r.id))
        if thm is None:
            verdict = "unformalizable" if r.id in declared_unform else "missing"
            results.append({"id": r.id, "verdict": verdict,
                            "note": "declared unformalizable by generator" if verdict == "unformalizable"
                            else "no theorem generated"})
            continue
        reading = llm.chat_json(
            cfg.review_model,
            INFORMALIZE_SYSTEM,
            f"Lean theorem:\n```lean\n{thm}\n```\n\nContext (type/function defs):\n```lean\n{lean_code[:12_000]}\n```\n\n"
            'Return {"english": "<plain-English reading of exactly what the theorem asserts>"}',
        )
        english = reading.get("english", "") if isinstance(reading, dict) else str(reading)
        verdict = llm.chat_json(
            cfg.review_model,
            JUDGE_SYSTEM,
            f"Requirement {r.id} ({r.category}): {r.statement}\n\n"
            f"Theorem's plain-English reading: {english}\n\n"
            'Return {"verdict": "full|partial|vacuous|mismatch", "note": "<=2 sentences"}',
        )
        if isinstance(verdict, dict):
            results.append({"id": r.id, "verdict": verdict.get("verdict", "?"),
                            "note": verdict.get("note", ""), "reading": english})

    counts: dict[str, int] = {}
    for x in results:
        counts[x["verdict"]] = counts.get(x["verdict"], 0) + 1
    n = len(results) or 1
    return {
        "results": results,
        "counts": counts,
        "coverage_full": counts.get("full", 0) / n,
        "coverage_full_or_partial": (counts.get("full", 0) + counts.get("partial", 0)) / n,
    }
