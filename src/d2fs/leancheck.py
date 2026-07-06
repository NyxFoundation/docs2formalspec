"""Stage 4: compile-check Lean output inside the lake project, with repair loop.

Repair is per-declaration (AutoSpec/PALM lessons): the model region is compile-gated
before theorem generation, so build errors are attributed to individual theorem
blocks. Each failing theorem escalates deterministically:
  1st failure -> targeted LLM repair of just that theorem
  2nd failure -> proof stubbed with `sorry` (statement kept)
  3rd failure -> whole declaration commented out with a BROKEN marker
Whole-file LLM rewrites are never used (they truncate and delete theorems).
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .config import Config
from .leangen import devacuate_lean, find_vacuous, repair_lean, strip_lean_block
from .llm import LLM

THEOREM_MARKER = "-- Requirements as theorems"


@dataclass
class CheckResult:
    ok: bool
    attempts: int
    sorry_count: int
    theorem_count: int
    vacuous_count: int
    last_output: str
    lean_code: str


# ---------------------------------------------------------------- lake plumbing

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


def _error_lines(build_output: str) -> list[int]:
    return [int(m.group(1)) for m in re.finditer(r"\.lean:(\d+):\d+", build_output)]


def _errors_for_range(build_output: str, lo: int, hi: int) -> str:
    """Extract error message segments whose location falls within [lo, hi]."""
    segs = re.split(r"(?=error: )", build_output)
    picked = []
    for seg in segs:
        m = re.match(r"error: .*?\.lean:(\d+):\d+", seg)
        if m and lo <= int(m.group(1)) <= hi:
            picked.append(seg.strip())
    return "\n".join(picked)


# ---------------------------------------------------------- file decomposition

def split_theorem_region(code: str, module_name: str) -> tuple[str, str]:
    """(model_region, theorem_region); the trailing `end <module>` is stripped."""
    body = re.sub(rf"^end {module_name}\s*$", "", code, flags=re.M)
    idx = body.find(THEOREM_MARKER)
    if idx == -1:
        m = re.search(r"^(?:/--|theorem\s)", body, flags=re.M)
        idx = m.start() if m else len(body)
        return body[:idx], body[idx:]
    return body[:idx], body[idx + len(THEOREM_MARKER):]


def split_decls(region: str) -> list[str]:
    """Split a theorem region into blocks: each theorem keeps its preceding
    docstring; other content becomes passthrough blocks."""
    blocks: list[list[str]] = []
    cur: list[str] = []
    in_doc = False

    def flush():
        nonlocal cur
        if any(l.strip() for l in cur):
            blocks.append(cur)
        cur = []

    for line in region.splitlines():
        s = line.lstrip()
        if in_doc:
            cur.append(line)
            if "-/" in s:
                in_doc = False
            continue
        if s.startswith("/--"):
            flush()
            cur = [line]
            in_doc = "-/" not in s[3:]
            continue
        if s.startswith("theorem"):
            if cur and cur[0].lstrip().startswith("/--") and not any(
                c.lstrip().startswith("theorem") for c in cur
            ):
                cur.append(line)
            else:
                flush()
                cur = [line]
            continue
        cur.append(line)
    flush()
    return ["\n".join(b).rstrip() for b in blocks]


def is_theorem_block(block: str) -> bool:
    return any(l.lstrip().startswith("theorem") for l in block.splitlines())


def build_file(model_region: str, blocks: list[str], module_name: str
               ) -> tuple[str, list[tuple[int, int]]]:
    """Assemble the full file; return (text, 1-based inclusive line range per block)."""
    head = model_region.rstrip() + f"\n\n{THEOREM_MARKER}\n\n"
    line = head.count("\n") + 1
    offsets: list[tuple[int, int]] = []
    chunks: list[str] = []
    for b in blocks:
        nb = b.rstrip() + "\n\n"
        n = nb.count("\n")
        offsets.append((line, line + n - 1))
        chunks.append(nb)
        line += n
    return head + "".join(chunks) + f"end {module_name}\n", offsets


# ------------------------------------------------------- deterministic repairs

def stub_block(block: str) -> str:
    """Replace the proof (from the LAST `:= by`) with sorry; else kill."""
    by_matches = list(re.finditer(r":=\s*by\b", block))
    if by_matches:
        return block[: by_matches[-1].start()].rstrip() + " := sorry"
    return kill_block(block)


def kill_block(block: str) -> str:
    return "\n".join(
        l if l.lstrip().startswith("-- BROKEN:") else "-- BROKEN: " + l
        for l in block.splitlines()
    )


# --------------------------------------------------------------- LLM repairs

REPAIR_DECL_SYSTEM = """\
You fix ONE Lean 4 (v4.31, core + Std, NO mathlib) theorem that fails to compile. \
You get the model definitions (which already compile), the failing theorem, and its \
compiler errors. Return ONLY the corrected theorem (with its docstring) in one Lean \
code block. Keep the theorem name; keep the statement as strong as possible — fix \
statement type errors if needed, and if the proof cannot be completed use `sorry`. \
Never weaken the statement to `True`, never return an empty block."""


def repair_decl(llm: LLM, cfg: Config, model_region: str, block: str, errors: str) -> str:
    text = llm.chat(
        cfg.repair_model,
        REPAIR_DECL_SYSTEM,
        f"Model (compiles, for reference):\n```lean\n{model_region[-12_000:]}\n```\n\n"
        f"Failing theorem:\n```lean\n{block}\n```\n\nErrors:\n```\n{errors[:4000]}\n```",
        max_tokens=4000,
    )
    fixed = strip_lean_block(text).strip()
    return fixed if "theorem" in fixed else stub_block(block)


# ------------------------------------------------------------------ model gate

def ensure_compiles(llm: LLM, cfg: Config, module_name: str, code: str,
                    max_rounds: int = 4, log=print) -> tuple[bool, str]:
    """Compile gate for the model section alone."""
    closed = code.rstrip() + f"\n\nend {module_name}\n"
    ok = False
    for i in range(1, max_rounds + 1):
        _write_module(cfg, module_name, closed)
        ok, out = _lake_build(cfg, module_name)
        log(f"[leancheck] model gate round {i}: ok={ok}")
        if ok:
            break
        closed = repair_lean(llm, cfg, closed, out)
    opened = re.sub(rf"^end {module_name}\s*$", "", closed, flags=re.M).rstrip() + "\n"
    return ok, opened


# ------------------------------------------------------------------- main loop

def _metrics(code: str) -> tuple[int, int, int]:
    return (len(re.findall(r"\bsorry\b", code)),
            len(re.findall(r"^\s*theorem\b", code, flags=re.M)),
            len(find_vacuous(code)))


def check_and_repair(llm: LLM, cfg: Config, module_name: str, lean_code: str,
                     max_rounds: int = 10, max_devac_rounds: int = 2, log=print) -> CheckResult:
    model_region, theorem_region = split_theorem_region(lean_code, module_name)
    blocks = split_decls(theorem_region)
    fail_counts: dict[int, int] = {}
    devac_used = 0
    attempt = 0
    text, out = lean_code, ""
    while attempt < max_rounds:
        attempt += 1
        text, offsets = build_file(model_region, blocks, module_name)
        _write_module(cfg, module_name, text)
        ok, out = _lake_build(cfg, module_name)
        n_sorry, n_thm, n_vac = _metrics(text)
        log(f"[leancheck] round {attempt}: ok={ok} theorems={n_thm} sorries={n_sorry} vacuous={n_vac}")
        if ok:
            vac = find_vacuous(text)
            if vac and devac_used < max_devac_rounds:
                devac_used += 1
                log(f"[leancheck] de-vacuating {len(vac)} theorems (pass {devac_used})")
                for i, b in enumerate(blocks):
                    names = find_vacuous(b)
                    if names:
                        fixed = strip_lean_block(devacuate_lean(llm, cfg, model_region + "\n" + b, names))
                        # keep only the theorem part of the response
                        _, fixed_thms = split_theorem_region(fixed, module_name)
                        cand = fixed_thms.strip() or fixed.strip()
                        if "theorem" in cand:
                            blocks[i] = cand
                continue
            return CheckResult(True, attempt, n_sorry, n_thm, n_vac, out, text)

        err_lines = _error_lines(out)
        # boundary from actual assembly: first block's start line (build_file rstrips
        # the model region, so counting model_region's own newlines would overshoot)
        boundary = offsets[0][0] if offsets else text.count("\n") + 1
        model_errs = [el for el in err_lines if el < boundary]
        if model_errs and len(model_errs) == len(err_lines):
            log("[leancheck] model-region errors — repairing model region")
            _, model_region = ensure_compiles(llm, cfg, module_name, model_region, max_rounds=2, log=log)
            continue

        failing = set()
        for el in err_lines:
            for i, (lo, hi) in enumerate(offsets):
                if lo <= el <= hi:
                    failing.add(i)
        if not failing:
            log("[leancheck] errors not attributable to any block — stopping")
            break
        for i in sorted(failing):
            fail_counts[i] = fail_counts.get(i, 0) + 1
            errs = _errors_for_range(out, *offsets[i])
            if not is_theorem_block(blocks[i]) or fail_counts[i] >= 3:
                blocks[i] = kill_block(blocks[i])
            elif fail_counts[i] == 2:
                blocks[i] = stub_block(blocks[i])
            else:
                blocks[i] = repair_decl(llm, cfg, model_region, blocks[i], errs)

    n_sorry, n_thm, n_vac = _metrics(text)
    return CheckResult(False, attempt, n_sorry, n_thm, n_vac, out, text)
