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


def _metrics(code: str) -> tuple[int, int, int]:
    return (len(re.findall(r"\bsorry\b", code)),
            len(re.findall(r"\btheorem\b", code)),
            len(find_vacuous(code)))


def check_and_repair(llm: LLM, cfg: Config, module_name: str, lean_code: str,
                     max_rounds: int = 8, max_devac_rounds: int = 2, log=print) -> CheckResult:
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
        code = repair_lean(llm, cfg, code, out)
    _write_module(cfg, module_name, code)
    ok, out = _lake_build(cfg, module_name)
    n_sorry, n_thm, n_vac = _metrics(code)
    return CheckResult(ok, attempt, n_sorry, n_thm, n_vac, out, code)
