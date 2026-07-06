"""Stage 3: generate a Lean4 formal model + theorems from formalizable requirements.

Two-phase generation (survey findings, docs/01-related-work.md):
  1. domain model (State + operations) from the spec's model summary
  2. theorems in small batches, each with the full model file as context (miniCTX)
Vacuous theorems (`: True`) are explicitly forbidden and detected downstream.
"""

from __future__ import annotations

import json
import re

from .config import Config
from .extract import Requirement
from .llm import LLM

MODEL_SYSTEM = """\
You are an expert Lean 4 (v4.31, core Lean + Std only, NO mathlib) formal methods \
engineer. You model DeFi protocols as state machines in the style of published Lean 4 \
AMM formalizations: a `structure State`, an `inductive Op` for operations, and a total \
step function `step : State -> Op -> Address -> Option State` (`none` = revert). \
Use Nat for amounts. Model access control as State fields (e.g. `admins : List Address`, \
`whitelist : List Address`) — NEVER as constant placeholder functions returning `true`, \
because those make safety properties unprovable or vacuous. Prefer List/Function maps \
(`Address -> Nat`) over HashMap for provability. Output ONLY a Lean code block."""

MODEL_USER_TMPL = """\
System: {system_name}

State-transition model summary (from the RFC2119 specification):
{model_summary}

Requirement themes the model must support (you will later prove theorems about these):
{themes}

Write the MODEL ONLY (no theorems) for file `{module_name}.lean`:
- `namespace {module_name}`
- type abbrevs, `structure State` (include every field needed by the requirement themes,
  including access-control sets and any supply/balance/cap/cooldown/vesting variables)
- `inductive Op` covering the operations
- `def step (s : State) (op : Op) (caller : Address) : Option State` with realistic
  guard conditions (pause, denylist, caps, balances, cooldowns) and state updates
- small helper defs where useful (e.g. `def totalSupply`, `def sharePrice`)
- do NOT close the namespace (theorems will be appended)
Balance maps as functions: `bal : Address -> Nat`, updated via
`fun a => if a = receiver then bal a + amt else bal a`.
"""

THEOREM_SYSTEM = """\
You are an expert Lean 4 (v4.31, core + Std, NO mathlib) proof engineer. You write \
theorems formalizing RFC 2119 requirements against a given state-machine model. \
HARD RULES:
1. Every theorem statement MUST mention `step` or another model function/field — the
   theorem must constrain the model's behavior.
2. `theorem foo : True` or any vacuously true statement is FORBIDDEN and counts as
   failure. If a requirement cannot be stated against the model, emit instead a comment
   `-- UNFORMALIZABLE req_<id>: <one-line reason>`.
3. Try to PROVE each theorem with cheap tactics first:
   `by simp [step]`, `by intro ...; simp_all [step]`, `by omega`, `by decide`, `rfl`,
   `by unfold step; split <;> simp_all`. Only if you genuinely cannot, use `sorry`.
4. Each theorem gets a docstring `/-- REQ <id>: <the RFC 2119 statement> -/`.
5. Name theorems `req_<id_with_underscores>`.
Typical shapes: guard properties (`s.paused = true -> step s (.deposit a r) c = none`),
frame properties (state field unchanged by an op), monotonicity, conservation sums,
bounds (`totalSupply s' <= s'.cap`). Output ONLY a Lean code block containing theorems
(and comments), no imports, no namespace lines."""

THEOREM_USER_TMPL = """\
Model file (already compiles, your theorems are appended INSIDE the namespace):
```lean
{model_code}
```

Formalize each of these requirements as one theorem (JSON):
{reqs_json}
"""

REPAIR_SYSTEM = """\
You fix Lean 4 (v4.31, core + Std, NO mathlib) compile errors. You receive a file and \
compiler output. Return the COMPLETE corrected file in one Lean code block. Rules: \
preserve every theorem name and keep each theorem statement as strong as possible; if \
a proof cannot be completed, replace the proof body with `sorry` — NEVER weaken a \
statement to `True` and never delete a theorem. Never add `import Mathlib`."""

DEVACUATE_SYSTEM = """\
You strengthen vacuous Lean 4 theorems. You receive a compiling file in which some \
theorems are stated as `True` (vacuous). Rewrite ONLY those theorems into meaningful \
properties of the model's `step` function per their REQ docstrings, keeping names. \
Prove with cheap tactics (simp [step], omega, decide) or use `sorry`. Return the \
COMPLETE file in one Lean code block. No mathlib."""


def gen_model(llm: LLM, cfg: Config, system_name: str, module_name: str,
              model_summary: str, reqs: list[Requirement]) -> str:
    themes = "\n".join(f"- [{r.category}] {r.id}: {r.statement}" for r in reqs if r.formalizable)
    text = llm.chat(
        cfg.lean_model,
        MODEL_SYSTEM,
        MODEL_USER_TMPL.format(system_name=system_name, module_name=module_name,
                               model_summary=model_summary, themes=themes[:12_000]),
        max_tokens=16_000,
    )
    return strip_lean_block(text)


def gen_theorems(llm: LLM, cfg: Config, model_code: str, reqs: list[Requirement],
                 batch_size: int = 8, log=print) -> str:
    formalizable = [r for r in reqs if r.formalizable]
    chunks = []
    for i in range(0, len(formalizable), batch_size):
        batch = formalizable[i : i + batch_size]
        log(f"[leangen] theorem batch {i // batch_size + 1}/{-(-len(formalizable) // batch_size)}")
        text = llm.chat(
            cfg.lean_model,
            THEOREM_SYSTEM,
            THEOREM_USER_TMPL.format(
                model_code=model_code,
                reqs_json=json.dumps(
                    [{"id": r.id, "category": r.category, "statement": r.statement}
                     for r in batch], ensure_ascii=False, indent=1),
            ),
            max_tokens=12_000,
        )
        chunk = strip_lean_block(text)
        # theorems are appended inside the namespace; drop stray closers/imports
        chunk = re.sub(r"^(import .*|namespace .*|end .*)$", "", chunk, flags=re.M)
        chunks.append(chunk.strip())
    return "\n\n".join(chunks)


def assemble(module_name: str, model_code: str, theorems_code: str) -> str:
    model = model_code.rstrip()
    # ensure the namespace stays open until after the theorems
    model = re.sub(rf"^end {module_name}\s*$", "", model, flags=re.M).rstrip()
    return f"{model}\n\n-- Requirements as theorems\n\n{theorems_code}\n\nend {module_name}\n"


def gen_lean(llm: LLM, cfg: Config, system_name: str, module_name: str,
             model_summary: str, reqs: list[Requirement], log=print) -> str:
    log("[leangen] phase 1: domain model")
    model_code = gen_model(llm, cfg, system_name, module_name, model_summary, reqs)
    log("[leangen] phase 2: theorems")
    theorems_code = gen_theorems(llm, cfg, model_code, reqs, log=log)
    return assemble(module_name, model_code, theorems_code)


def repair_lean(llm: LLM, cfg: Config, lean_code: str, compiler_output: str) -> str:
    text = llm.chat(
        cfg.repair_model,
        REPAIR_SYSTEM,
        f"File:\n```lean\n{lean_code}\n```\n\nCompiler output:\n```\n{compiler_output[:8000]}\n```\n\nReturn the complete corrected file.",
        max_tokens=24_000,
    )
    return strip_lean_block(text)


def devacuate_lean(llm: LLM, cfg: Config, lean_code: str, vacuous_names: list[str]) -> str:
    text = llm.chat(
        cfg.lean_model,
        DEVACUATE_SYSTEM,
        f"Vacuous theorems: {vacuous_names}\n\nFile:\n```lean\n{lean_code}\n```",
        max_tokens=24_000,
    )
    return strip_lean_block(text)


def find_vacuous(lean_code: str) -> list[str]:
    """Theorem names whose statement is just True (modulo whitespace)."""
    return re.findall(r"theorem\s+([A-Za-z0-9_']+)[^:]*:\s*True\s*:=", lean_code)


def strip_lean_block(text: str) -> str:
    text = re.sub(r"<think>.*?</think>", "", text, flags=re.S)
    blocks = re.findall(r"```(?:lean4?)?\s*\n(.*?)```", text, flags=re.S)
    if blocks:
        return max(blocks, key=len).strip() + "\n"
    return text.strip() + "\n"
