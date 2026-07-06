"""End-to-end pipeline: sources -> RFC2119 spec markdown + verified Lean4 module."""

from __future__ import annotations

import json
import re
from dataclasses import asdict
from pathlib import Path

from .config import Config
from .extract import Requirement, extract_requirements, render_spec
from .ingest import ingest
from .leancheck import CheckResult, check_and_repair, ensure_compiles
from .leangen import gen_lean
from .llm import LLM
from .review import roundtrip_review

MODEL_SUMMARY_SYSTEM = """\
You summarize a protocol as a formal state-transition model: list state variables \
(name, type, meaning), actors, and operations (name, inputs, preconditions, effects). \
Be concrete and quantitative. Output markdown, <=60 lines."""


def slugify_module(name: str) -> str:
    parts = re.split(r"[^A-Za-z0-9]+", name)
    return "".join(p.capitalize() for p in parts if p) or "Spec"


def run(system_name: str, sources: list[str], cfg: Config | None = None, log=print) -> dict:
    cfg = cfg or Config()
    llm = LLM(cfg)
    outdir = cfg.outputs_dir / re.sub(r"[^a-z0-9-]+", "-", system_name.lower())
    outdir.mkdir(parents=True, exist_ok=True)

    log(f"[ingest] {len(sources)} sources")
    docs = ingest(sources)
    log(f"[ingest] got {len(docs)} documents: {[d.title for d in docs]}")
    (outdir / "corpus.md").write_text(
        "\n\n---\n\n".join(f"# {d.title}\n_source: {d.source}_\n\n{d.markdown}" for d in docs)
    )

    log("[extract] extracting requirements")
    reqs = extract_requirements(llm, cfg, docs)
    log(f"[extract] {len(reqs)} requirements ({sum(r.formalizable for r in reqs)} formalizable)")
    (outdir / "requirements.json").write_text(
        json.dumps([asdict(r) for r in reqs], ensure_ascii=False, indent=1)
    )

    log("[spec] rendering RFC2119 spec")
    spec_md = render_spec(llm, cfg, system_name, reqs, [d.source for d in docs])
    spec_path = outdir / "SPEC.md"
    spec_path.write_text(spec_md)

    log("[model] summarizing state-transition model")
    model_summary = llm.chat(
        cfg.extract_model,
        MODEL_SUMMARY_SYSTEM,
        f"Specification:\n{spec_md[:40_000]}",
    )
    (outdir / "model.md").write_text(model_summary)

    return lean_stage(system_name, reqs, model_summary, outdir, cfg, llm, log,
                      extra={"spec": str(spec_path), "requirements": len(reqs)})


def lean_stage(system_name: str, reqs: list[Requirement], model_summary: str,
               outdir: Path, cfg: Config, llm: LLM, log=print, extra: dict | None = None) -> dict:
    module_name = slugify_module(system_name)
    log(f"[lean] generating {module_name}.lean")
    gate = lambda code: ensure_compiles(llm, cfg, module_name, code, log=log)  # noqa: E731
    lean_code = gen_lean(llm, cfg, system_name, module_name, model_summary, reqs,
                         log=log, compile_gate=gate)
    result: CheckResult = check_and_repair(llm, cfg, module_name, lean_code, log=log)
    (outdir / f"{module_name}.lean").write_text(result.lean_code)
    (outdir / "leancheck.json").write_text(json.dumps({
        "ok": result.ok, "attempts": result.attempts, "theorems": result.theorem_count,
        "sorries": result.sorry_count, "vacuous": result.vacuous_count,
        "proved": result.theorem_count - result.sorry_count,
    }, indent=1))
    log("[review] round-trip consistency gate")
    review = roundtrip_review(llm, cfg, reqs, result.lean_code)
    (outdir / "review.json").write_text(json.dumps(review, ensure_ascii=False, indent=1))
    log(f"[review] verdicts={review['counts']} full-coverage={review['coverage_full']:.0%}")

    log(f"[done] ok={result.ok} theorems={result.theorem_count} sorries={result.sorry_count}")
    return {
        "outdir": str(outdir),
        "lean_ok": result.ok,
        "theorems": result.theorem_count,
        "proved": result.theorem_count - result.sorry_count,
        "sorries": result.sorry_count,
        "vacuous": result.vacuous_count,
        "review": review["counts"],
        **(extra or {}),
    }


def relean(system_name: str, cfg: Config | None = None, log=print) -> dict:
    """Re-run only the Lean stage from saved requirements.json + model.md."""
    cfg = cfg or Config()
    llm = LLM(cfg)
    outdir = cfg.outputs_dir / re.sub(r"[^a-z0-9-]+", "-", system_name.lower())
    reqs_raw = json.loads((outdir / "requirements.json").read_text())
    reqs = [Requirement(**{k: r.get(k) for k in Requirement.__dataclass_fields__}) for r in reqs_raw]
    model_summary = (outdir / "model.md").read_text()
    return lean_stage(system_name, reqs, model_summary, outdir, cfg, llm, log)
