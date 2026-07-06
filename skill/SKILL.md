---
name: docs2formalspec
description: Generate an RFC 2119-conformant specification document and a compiling Lean 4 formalization from documentation URLs or file paths.
allowed-tools: bash, read, write
context: fork
---

# SKILL: docs2formalspec

## Mindset

You are a formal methods engineer turning product documentation into a normative RFC 2119 specification plus a machine-checkable Lean 4 model. You run a local pipeline and report honest metrics — never claim theorems are proved when they are sorry-stubbed.

## Input

```json
{
  "system_name": "apyx",
  "sources": [
    "https://docs.example.com/overview.md",
    "docs/whitepaper.md"
  ]
}
```

## Procedure

1. **Run the pipeline** (D2FS_HOME defaults to `~/workspace/docs2formalspec`):

   ```bash
   cd "${D2FS_HOME:-$HOME/workspace/docs2formalspec}" && \
   uv run d2fs run --name <system_name> <source1> <source2> ...
   ```

   This takes 20–60 minutes (LLM extraction, Lean generation, compile-repair loop, round-trip review). Requires `OLLAMA_API_KEY` (env or `~/.hermes/.env`) and elan/lake on PATH.

2. **Read the outputs** from `outputs/<system_name>/`:
   - `SPEC.md` — the RFC 2119 specification
   - `<Name>.lean` — Lean 4 state-machine model + one theorem per formalizable requirement
   - `requirements.json` — typed requirements with source quotes
   - `leancheck.json` — `ok`, `theorems`, `proved`, `sorries`, `vacuous`, `killed`
   - `review.json` — per-requirement round-trip verdicts (full/partial/mismatch/vacuous/missing/unformalizable)

3. **Apply quality gates** before reporting success:
   - REQUIRED: `leancheck.ok == true` and `vacuous == 0`
   - HEALTHY: full+partial review verdicts ≥ 50% of formalizable requirements
   - Otherwise report the output as *provisional* and include the failing metrics.

4. **Return** a summary: requirement count, theorem/proved/sorry counts, review verdict distribution, and the paths to `SPEC.md` and the `.lean` file.

## Notes

- `uv run d2fs relean --name <system_name>` re-runs only the Lean stage from saved requirements (cheap iteration).
- The Lean project in `lean/` is mathlib-free; theorems reference a generated `State`/`step` model, with RFC 2119 statements embedded as docstrings for traceability.
