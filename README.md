# docs2formalspec

Documentation URLs / file paths in → **RFC 2119-conformant specification** + **Lean 4 formal verification code** out. Runs entirely on local-class LLMs via Ollama Cloud (OpenAI-compatible). Destined to become a harness plugin callable from the [SPECA](https://github.com/NyxFoundation/speca) repository.

## Usage

```bash
uv sync
uv run d2fs run --name apyx https://docs.apyx.fi/apyx-overview/how-apyx-works.md [...]
```

Outputs land in `outputs/<name>/`:

| File | Content |
|---|---|
| `corpus.md` | ingested source documents |
| `requirements.json` | extracted RFC 2119 requirements (typed, sourced, formalizability flag) |
| `SPEC.md` | the RFC 2119 specification document |
| `model.md` | state-transition model summary |
| `<Name>.lean` | Lean 4 model + one theorem per formalizable requirement |
| `leancheck.json` | compile status, repair rounds, theorem/sorry counts |

## Pipeline

`ingest` (URL/.md/file → markdown) → `extract` (per-doc RFC2119 requirement JSON, multi-doc merge + contradiction check) → `render_spec` → model summary → `gen_lean` (state machine: `structure State`, ops as `State → Input → Option State`, `theorem req_*`) → `check_and_repair` (`lake build` feedback loop, ≤6 rounds).

Lean project in `lean/` is mathlib-free (Lean 4.31) so the compile-check loop runs in milliseconds.

## Configuration

`OLLAMA_API_KEY` from env or `~/.hermes/.env`. Model roles overridable via `D2FS_EXTRACT_MODEL`, `D2FS_LEAN_MODEL`, `D2FS_REPAIR_MODEL`, `D2FS_REVIEW_MODEL`.

Design notes and research log live in `docs/`.
