"""Stage 4: compile-check Lean output inside the lake project, with LLM repair loop."""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .config import Config
from .leangen import devacuate_lean, find_vacuous, repair_lean
from .llm import LLM


@dataclass
class CheckResult:
    ok: bool
    attempts: int
    sorry_count: int
    theorem_count: int
    vacuous_count: int
    last_output: str
    lean_code: str


def _write_module(cfg: Config, module_name: str, code: str) -> Path:
    path = cfg.lean_dir / "D2fsSpecs" / f"{module_name}.lean"
    path.write_text(code)
    root = cfg.lean_dir / "D2fsSpecs.lean"
    imports = set(root.read_text().splitlines()) if root.exists() else set()
    line = f"import D2fsSpecs.{module_name}"
    if line not in imports:
        root.write_text("\n".join(sorted(imports | {line})) + "\n")
    return path


def _lake_build(cfg: Config, module_name: str) -> tuple[bool, str]:
    proc = subprocess.run(
        ["lake", "build", f"D2fsSpecs.{module_name}"],
        cwd=cfg.lean_dir,
        capture_output=True,
        text=True,
        timeout=600,
    )
    out = proc.stdout + proc.stderr
    return proc.returncode == 0, out


_DECL_RE = re.compile(r"^(?:theorem|def|structure|inductive|abbrev|instance)\s", re.M)


def _error_lines(build_output: str) -> list[int]:
    return [int(m.group(1)) for m in re.finditer(r"\.lean:(\d+):\d+", build_output)]


def sorry_stub_failing_proofs(code: str, build_output: str) -> tuple[str, int]:
    """Deterministic PALM-style fallback: for every compile error located inside a
    theorem's proof, replace that proof body with `sorry`, keeping the statement.
    Returns (new_code, number_of_stubbed_theorems)."""
    lines = code.splitlines()
    # start line (0-based) of each declaration
    decl_starts = [i for i, l in enumerate(lines) if _DECL_RE.match(l)]
    if not decl_starts:
        return code, 0
    stub_targets: set[int] = set()
    for el in _error_lines(build_output):
        idx = el - 1
        encl = max((s for s in decl_starts if s <= idx), default=None)
        if encl is not None and lines[encl].lstrip().startswith("theorem"):
            stub_targets.add(encl)
    if not stub_targets:
        return code, 0
    decl_starts.append(len(lines))
    out_lines = list(lines)
    for start in sorted(stub_targets, reverse=True):
        end = min(s for s in decl_starts if s > start)
        decl_text = "\n".join(lines[start:end])
        m = re.search(r":=\s*(by\b|calc\b|sorry\b)?", decl_text)
        if not m:
            continue
        stubbed = decl_text[: m.start()].rstrip() + " := sorry\n"
        out_lines[start:end] = stubbed.splitlines() + [""]
    return "\n".join(out_lines) + "\n", len(stub_targets)


def _metrics(code: str) -> tuple[int, int, int]:
    return (len(re.findall(r"\bsorry\b", code)),
            len(re.findall(r"\btheorem\b", code)),
            len(find_vacuous(code)))


def check_and_repair(llm: LLM, cfg: Config, module_name: str, lean_code: str,
                     max_rounds: int = 8, max_devac_rounds: int = 2,
                     llm_repair_rounds: int = 4, log=print) -> CheckResult:
    code = lean_code
    out = ""
    devac_used = 0
    attempt = 0
    while attempt < max_rounds:
        attempt += 1
        _write_module(cfg, module_name, code)
        ok, out = _lake_build(cfg, module_name)
        n_sorry, n_thm, n_vac = _metrics(code)
        log(f"[leancheck] round {attempt}: ok={ok} theorems={n_thm} sorries={n_sorry} vacuous={n_vac}")
        if ok:
            vac = find_vacuous(code)
            if vac and devac_used < max_devac_rounds:
                devac_used += 1
                log(f"[leancheck] de-vacuating {len(vac)} theorems (pass {devac_used})")
                code = devacuate_lean(llm, cfg, code, vac)
                continue
            n_sorry, n_thm, n_vac = _metrics(code)
            return CheckResult(True, attempt, n_sorry, n_thm, n_vac, out, code)
        if attempt > llm_repair_rounds:
            # LLM repair is not converging — deterministically stub failing proofs
            stubbed, n = sorry_stub_failing_proofs(code, out)
            if n:
                log(f"[leancheck] sorry-stubbed {n} failing proofs (deterministic fallback)")
                code = stubbed
                continue
        code = repair_lean(llm, cfg, code, out)
    _write_module(cfg, module_name, code)
    ok, out = _lake_build(cfg, module_name)
    n_sorry, n_thm, n_vac = _metrics(code)
    return CheckResult(ok, attempt, n_sorry, n_thm, n_vac, out, code)
