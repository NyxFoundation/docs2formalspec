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

## Deepening beyond pillar 1 (the full end-to-end workflow)

The automated `d2fs run` above produces **pillar 1 only** (requirement-conformance theorems). The full,
audit-grade assurance for a protocol adds three more pillars and an implementation cross-check, driven by the
templates and the runbook — see **[`docs/09-end-to-end-workflow.md`](../docs/09-end-to-end-workflow.md)**:

1. **Fetch the Solidity source** (`gh repo clone <org>/<repo>`) — the implementation is ground truth; corpus is
   its informal description.
2. **Source-tracing gate** (`docs/07` §3.0): every contradiction / ambiguity / vacuity candidate is traced to
   its `source_quote` → corpus → Solidity, to separate a genuine spec defect from a tool **extraction defect
   (D6)** and to construct the spec from the implementation where corpus is ambiguous. **Do not report a tool
   extraction miss as a protocol defect.**
3. **Pillars 2–4 from the templates**: blast-radius (`templates/blast-radius/`, key-compromise bounds),
   design-safety invariants (`templates/invariants/`, core I1–I5 + I7 + parameter-bound gap-witnesses),
   spec-consistency (`docs/07`, satisfiability / realizability / vacuity / coverage).
4. **Co-improve** spec ↔ model ↔ Lean against the implementation, keeping `lake build` green, `sorry` 0, and the
   four docs (`requirements.json`/`SPEC.md`/`model.md`/`README.md`) mutually consistent after every change.
5. **Report** with `review.json` tagging each theorem by provenance (requirement / threat-model / design-invariant
   / spec-consistency) and a README that lists the **implementation-layer hand-off** (what static analysis / SMT /
   fuzzing must still check; `docs/08`). Apyx (`outputs/apyx/`) is the worked reference for all of this.
