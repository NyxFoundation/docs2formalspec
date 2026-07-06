"""Runtime configuration: Ollama Cloud endpoint, model roster, paths."""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from pathlib import Path

HERMES_ENV = Path.home() / ".hermes" / ".env"


def _load_ollama_key() -> str:
    key = os.environ.get("OLLAMA_API_KEY", "")
    if key:
        return key
    if HERMES_ENV.exists():
        for line in HERMES_ENV.read_text().splitlines():
            if line.startswith("OLLAMA_API_KEY="):
                return line.split("=", 1)[1].strip()
    raise RuntimeError("OLLAMA_API_KEY not found in env or ~/.hermes/.env")


@dataclass
class Config:
    base_url: str = "https://ollama.com/v1"
    api_key: str = field(default_factory=_load_ollama_key)
    # Model roles. Extraction favors long-context comprehension; lean_gen favors
    # code models; repair needs fast iteration on compiler errors.
    extract_model: str = os.environ.get("D2FS_EXTRACT_MODEL", "gpt-oss:120b")
    lean_model: str = os.environ.get("D2FS_LEAN_MODEL", "qwen3-coder:480b")
    repair_model: str = os.environ.get("D2FS_REPAIR_MODEL", "qwen3-coder:480b")
    review_model: str = os.environ.get("D2FS_REVIEW_MODEL", "gpt-oss:120b")
    temperature: float = 0.1
    max_retries: int = 3
    request_timeout: float = 300.0

    project_root: Path = Path(__file__).resolve().parents[2]

    @property
    def lean_dir(self) -> Path:
        return self.project_root / "lean"

    @property
    def outputs_dir(self) -> Path:
        return self.project_root / "outputs"
