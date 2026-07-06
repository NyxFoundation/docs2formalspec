"""Stage 3: generate a Lean4 formal model + theorems from formalizable requirements."""

from __future__ import annotations

import json
from dataclasses import asdict

from .config import Config
from .extract import Requirement
from .llm import LLM

LEAN_SYSTEM = """\
You are an expert Lean 4 (v4.31, NO mathlib — core Lean + Std only) formal methods \
engineer. You model protocols as state machines: a `structure State`, operations as \
total functions `State -> Input -> Option State` (returning `none` on revert), and \
requirements as theorems. Use Nat for token amounts (no negative balances), avoid \
Real/Float. Prove what you can with `simp`, `omega`, `decide`, `constructor`, `intro`, \
`cases`, `unfold`; for genuinely hard proofs state the theorem and use `sorry` — a \
sorried theorem is still a formalized requirement. Prefer many small provable lemmas. \
NEVER use `import Mathlib`. Output ONLY a Lean code block."""

LEAN_USER_TMPL = """\
System: {system_name}

System model summary (from the specification):
{model_summary}

Formalizable requirements (JSON):
{reqs_json}

Write a single self-contained Lean 4 file `{module_name}.lean`:
1. `namespace {module_name}`
2. `structure State` capturing the state variables.
3. One function per operation modeling its semantics per the spec (Option State for failure).
4. For EACH requirement, a theorem named `req_<id_with_underscores>` with a docstring \
quoting the RFC 2119 statement. Theorems must reference the model functions, not be \
vacuous `True` statements.
5. Close the namespace.

Constraints: Lean 4 syntax (def/theorem/:= by), no mathlib, no `partial` unless needed, \
compile-ready.
"""

REPAIR_SYSTEM = """\
You fix Lean 4 (v4.31, core only, NO mathlib) compile errors. You receive a file and \
compiler output. Return the COMPLETE corrected file in one Lean code block. Preserve \
all theorem names and statements when possible; if a proof cannot be completed, \
replace the proof body with `sorry` rather than deleting or weakening the theorem. \
Never add `import Mathlib`."""


def gen_lean(llm: LLM, cfg: Config, system_name: str, module_name: str,
             model_summary: str, reqs: list[Requirement]) -> str:
    formalizable = [r for r in reqs if r.formalizable]
    text = llm.chat(
        cfg.lean_model,
        LEAN_SYSTEM,
        LEAN_USER_TMPL.format(
            system_name=system_name,
            module_name=module_name,
            model_summary=model_summary,
            reqs_json=json.dumps([asdict(r) for r in formalizable], ensure_ascii=False, indent=1),
        ),
        max_tokens=20_000,
    )
    return strip_lean_block(text)


def repair_lean(llm: LLM, cfg: Config, lean_code: str, compiler_output: str) -> str:
    text = llm.chat(
        cfg.repair_model,
        REPAIR_SYSTEM,
        f"File:\n```lean\n{lean_code}\n```\n\nCompiler output:\n```\n{compiler_output[:8000]}\n```\n\nReturn the complete corrected file.",
        max_tokens=20_000,
    )
    return strip_lean_block(text)


def strip_lean_block(text: str) -> str:
    import re

    text = re.sub(r"<think>.*?</think>", "", text, flags=re.S)
    blocks = re.findall(r"```(?:lean4?)?\s*\n(.*?)```", text, flags=re.S)
    if blocks:
        return max(blocks, key=len).strip() + "\n"
    return text.strip() + "\n"
