"""Stage 5: Clover-style round-trip consistency gate.

Informalize each generated Lean theorem back to English, compare against the
source RFC2119 requirement with an LLM judge, and report coverage/mismatches.
"""

from __future__ import annotations

import re

from .config import Config
from .extract import Requirement
from .llm import LLM

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
        rid = name.removeprefix("req_").replace("_", "-")
        by_req[rid] = text

    from .leangen import find_unformalizable

    declared_unform = set(find_unformalizable(lean_code))
    results = []
    for r in reqs:
        if not r.formalizable:
            continue
        thm = by_req.get(r.id)
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
