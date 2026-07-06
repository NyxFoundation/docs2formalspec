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

# Condensed idiom from published Lean 4 AMM formalizations (arXiv:2402.06064 style):
# state record + total step function + guard conditions, written to be provable by simp.
EXEMPLAR = """\
Example of the expected style (a toy vault — adapt, don't copy):
```lean
namespace ToyVault
abbrev Address := Nat
abbrev Amount := Nat

structure State where
  paused : Bool
  admins : List Address
  cap : Amount
  supply : Amount
  bal : Address → Amount

inductive Op
  | deposit (amt : Amount) (to : Address)
  | pause

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | .deposit amt to =>
    if s.paused ∨ amt = 0 ∨ s.supply + amt > s.cap then none
    else some { s with supply := s.supply + amt,
                       bal := fun a => if a = to then s.bal a + amt else s.bal a }
  | .pause =>
    if s.admins.contains caller then some { s with paused := true } else none

/-- REQ pause-blocks-deposit: WHEN paused the vault MUST reject deposits. -/
theorem req_pause_blocks_deposit (s : State) (amt : Amount) (to c : Address)
    (h : s.paused = true) : step s (.deposit amt to) c = none := by
  simp [step, h]

/-- REQ supply-cap: total supply MUST NOT exceed the cap. -/
theorem req_supply_cap (s s' : State) (amt : Amount) (to c : Address)
    (hc : s.supply ≤ s.cap) (h : step s (.deposit amt to) c = some s') :
    s'.supply ≤ s'.cap := by
  simp [step] at h
  obtain ⟨⟨_, _, hle⟩, rfl⟩ := h
  simpa using hle
end ToyVault
```
Note how guards are plain `if` conditions on State fields, updates are function
overrides, and theorems quantify over pre/post states linked by `step ... = some s'`.
After `simp [step] at h` the guard becomes a conjunction: destructure it with
`obtain ⟨⟨...⟩, rfl⟩ := h` and close with `simpa`/`omega`."""


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

{exemplar}
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

{exemplar}
"""

REPAIR_SYSTEM = """\
You fix Lean 4 (v4.31, core + Std, NO mathlib) compile errors. You receive a file and \
compiler output. Return the COMPLETE corrected file in one Lean code block. Rules: \
preserve every theorem name and keep each theorem statement as strong as possible; if \
a proof cannot be completed, replace the proof body with `sorry` — NEVER weaken a \
statement to `True` and never delete a theorem. Never add `import Mathlib`."""

EXTEND_SYSTEM = """\
You extend a Lean 4 (v4.31, core + Std, NO mathlib) state-machine model so that more \
requirements become formalizable. You receive the current model and requirements that \
could not be stated against it. Add the missing State fields, Ops, step cases, or \
helper defs (e.g. sharePrice, totalSupply, vesting schedule fields) needed to state \
them — keep every existing definition and its behavior intact, only extend. Do NOT \
close the namespace. Output ONLY a Lean code block with the COMPLETE extended model \
(no theorems)."""


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
        cfg.modelgen_model,
        MODEL_SYSTEM,
        MODEL_USER_TMPL.format(system_name=system_name, module_name=module_name,
                               model_summary=model_summary, themes=themes[:12_000],
                               exemplar=EXEMPLAR),
        max_tokens=16_000,
    )
    return strip_lean_block(text)


BATCH_FIX_SYSTEM = """\
You fix a batch of Lean 4 (v4.31, core + Std, NO mathlib) theorems that fail to \
compile against a model that itself compiles. Common causes: identifiers or fields \
that do not exist in the model — replace them with the actual names from the model, \
or restate the property using what the model provides. Keep every theorem and its \
name; use `sorry` for proofs you cannot complete; never state `True`. Output ONLY a \
Lean code block with the corrected theorems."""


def _clean_chunk(text: str) -> str:
    chunk = strip_lean_block(text)
    # theorems are appended inside the namespace; drop stray closers/imports
    return re.sub(r"^(import .*|namespace .*|end .*)$", "", chunk, flags=re.M).strip()


def gen_theorems(llm: LLM, cfg: Config, model_code: str, reqs: list[Requirement],
                 batch_size: int = 8, log=print, batch_gate=None) -> str:
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
                exemplar=EXEMPLAR,
                reqs_json=json.dumps(
                    [{"id": r.id, "category": r.category, "statement": r.statement}
                     for r in batch], ensure_ascii=False, indent=1),
            ),
            max_tokens=12_000,
        )
        chunk = _clean_chunk(text)
        if batch_gate and chunk:
            ok, errs = batch_gate(chunk)
            if not ok:
                log("[leangen]   batch failed pre-validation; regenerating with errors")
                retry = llm.chat(
                    cfg.lean_model,
                    BATCH_FIX_SYSTEM,
                    f"Model (compiles):\n```lean\n{model_code[:14_000]}\n```\n\n"
                    f"Failing batch:\n```lean\n{chunk}\n```\n\nErrors:\n```\n{errs[:6000]}\n```",
                    max_tokens=12_000,
                )
                fixed = _clean_chunk(retry)
                if fixed and "theorem" in fixed:
                    ok2, _ = batch_gate(fixed)
                    if ok2:
                        chunk = fixed
                        log("[leangen]   batch fixed on retry")
                    else:
                        chunk = fixed  # still better odds; per-decl engine finishes the job
        chunks.append(chunk)
    return "\n\n".join(c for c in chunks if c)


def assemble(module_name: str, model_code: str, theorems_code: str) -> str:
    model = model_code.rstrip()
    # ensure the namespace stays open until after the theorems
    model = re.sub(rf"^end {module_name}\s*$", "", model, flags=re.M).rstrip()
    return f"{model}\n\n-- Requirements as theorems\n\n{theorems_code}\n\nend {module_name}\n"


def find_unformalizable(theorems_code: str) -> list[str]:
    """Req ids declared unformalizable by the theorem generator."""
    ids = re.findall(r"--\s*UNFORMALIZABLE\s+req[_-]([A-Za-z0-9_-]+)", theorems_code)
    return [i.replace("_", "-") for i in ids]


def extend_model(llm: LLM, cfg: Config, model_code: str, reqs: list[Requirement]) -> str:
    text = llm.chat(
        cfg.modelgen_model,
        EXTEND_SYSTEM,
        "Current model:\n```lean\n" + model_code + "\n```\n\nUnformalizable requirements:\n"
        + json.dumps([{"id": r.id, "category": r.category, "statement": r.statement}
                      for r in reqs], ensure_ascii=False, indent=1),
        max_tokens=20_000,
    )
    return strip_lean_block(text)


def gen_lean(llm: LLM, cfg: Config, system_name: str, module_name: str,
             model_summary: str, reqs: list[Requirement], log=print,
             compile_gate=None, batch_gate=None) -> str:
    """compile_gate: optional (model_code) -> (ok, repaired_code); models that fail
    the gate are still used (best effort) but extensions that fail are discarded.
    batch_gate: optional (model_code, chunk) -> (ok, errors) for immediate
    per-batch statement validation."""
    log("[leangen] phase 1: domain model")
    # a broken model poisons every downstream stage; resample rather than proceed
    for sample in range(1, 4):
        model_code = gen_model(llm, cfg, system_name, module_name, model_summary, reqs)
        if not compile_gate:
            break
        ok, model_code = compile_gate(model_code)
        if ok:
            break
        log(f"[leangen] model sample {sample} failed compile gate; resampling")
    else:
        raise RuntimeError("model generation failed compile gate after 3 samples")
    log("[leangen] phase 2: theorems")
    gate_for = (lambda m: (lambda chunk: batch_gate(m, chunk))) if batch_gate else (lambda m: None)
    theorems_code = gen_theorems(llm, cfg, model_code, reqs, log=log,
                                 batch_gate=gate_for(model_code))

    # model-extension feedback round: if requirements were declared unformalizable,
    # extend the model to support them and regenerate just those theorems
    missing_ids = set(find_unformalizable(theorems_code))
    missing = [r for r in reqs if r.formalizable and r.id in missing_ids]
    if missing:
        log(f"[leangen] phase 3: extending model for {len(missing)} unformalizable reqs")
        extended = extend_model(llm, cfg, model_code, missing)
        ext_ok = True
        if compile_gate:
            ext_ok, extended = compile_gate(extended)
        if ext_ok:
            model_code = extended
            extra = gen_theorems(llm, cfg, model_code, missing, log=log,
                                 batch_gate=gate_for(model_code))
            kept = "\n".join(
                l for l in theorems_code.splitlines()
                if not re.match(r"\s*--\s*UNFORMALIZABLE", l)
            )
            theorems_code = kept + "\n\n-- Theorems added after model extension\n\n" + extra
        else:
            log("[leangen] extension failed compile gate; keeping original model")

    # coverage reconciliation: requirements with neither a theorem nor an explicit
    # UNFORMALIZABLE declaration were silently dropped (batch retries lose items)
    for _pass in range(2):
        covered = {n.replace("_", "-") for n in
                   re.findall(r"^\s*theorem\s+req_([A-Za-z0-9_']+)", theorems_code, flags=re.M)}
        declared = set(find_unformalizable(theorems_code))
        dropped = [r for r in reqs if r.formalizable
                   and r.id not in covered and r.id not in declared]
        if not dropped:
            break
        log(f"[leangen] coverage pass {_pass + 1}: regenerating {len(dropped)} dropped reqs")
        extra = gen_theorems(llm, cfg, model_code, dropped, log=log,
                             batch_gate=gate_for(model_code))
        if not extra.strip():
            break
        theorems_code += "\n\n-- Theorems added by coverage reconciliation\n\n" + extra
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
