# docs2formalspec

Documentation URLs / file paths in → **RFC 2119-conformant specification** + **Lean 4 formal verification code** out. Runs entirely on local-class LLMs via Ollama Cloud (OpenAI-compatible). Destined to become a harness plugin callable from the [SPECA](https://github.com/NyxFoundation/speca) repository.

## Status

Evaluated over 15 iterative runs against [Apyx](https://docs.apyx.fi) (a dividend-backed stablecoin protocol), then taken further with a higher-grade hand-formalization pass. Current best result (`outputs/apyx/`):

| Metric | Value |
|---|---|
| Requirements extracted (formalizable) | 82 (77) |
| Lean 4 compilation | ✅ passes |
| Theorems (live / killed) | 81 / 8 |
| Mechanically proved | 81 (0 sorry) |
| Vacuous theorems (`: True`) | 0 |
| Faithful coverage (full + partial review) | ~85–92% (run-to-run judge variance; see note) |

The automated pipeline (local-class LLMs via Ollama Cloud) plateaus around 53% faithful coverage with a 4/55 proof rate — roughly on par with frontier-model results reported in Verina (ICLR 2026, ~51% spec-sound-complete). A higher-grade model doing the same hand-editing task over five rounds (proof by real tactics instead of `sorry`; formalizing requirements the pipeline had left missing/mismatched; extending the domain model itself with an explicit UnlockToken contract identity/operator and a monthly rate-setting calendar; and re-examining every requirement the very first pipeline run had given up on as "unformalizable") pushed proof rate to 100% (80/80) and faithful coverage into the ~85–92% range, confirming the original plateau was a model-grade limit rather than a pipeline-design or domain-model-expressiveness limit. Only 2 requirements remain genuinely unformalizable against this model (a MAY-permission with no witness path, and an active rebalancing mechanism that isn't modeled). Note: the round-trip review is itself an LLM judge and its full/partial/mismatch calls have observed run-to-run variance of several points on borderline cases even with zero code changes — treat any single review run's percentage as a point in that range, not an exact figure. Full run-by-run history and failure-mode analysis in [`docs/03-eval-log.md`](docs/03-eval-log.md).

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
