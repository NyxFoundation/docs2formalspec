"""Minimal OpenAI-compatible chat client for Ollama Cloud with retry + JSON mode."""

from __future__ import annotations

import json
import re
import time

import httpx

from .config import Config


class LLMError(RuntimeError):
    pass


class LLM:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self._client = httpx.Client(
            base_url=cfg.base_url,
            headers={"Authorization": f"Bearer {cfg.api_key}"},
            timeout=cfg.request_timeout,
        )

    def chat(
        self,
        model: str,
        system: str,
        user: str,
        temperature: float | None = None,
        max_tokens: int | None = None,
    ) -> str:
        payload: dict = {
            "model": model,
            "messages": [
                {"role": "system", "content": system},
                {"role": "user", "content": user},
            ],
            "temperature": self.cfg.temperature if temperature is None else temperature,
        }
        if max_tokens:
            payload["max_tokens"] = max_tokens
        last_err: Exception | None = None
        for attempt in range(self.cfg.max_retries):
            try:
                r = self._client.post("/chat/completions", json=payload)
                if r.status_code >= 500 or r.status_code == 429:
                    raise LLMError(f"HTTP {r.status_code}: {r.text[:300]}")
                r.raise_for_status()
                data = r.json()
                content = data["choices"][0]["message"]["content"]
                if not content or not content.strip():
                    raise LLMError("empty completion")
                return content
            except (httpx.HTTPError, LLMError, KeyError) as e:  # noqa: PERF203
                last_err = e
                time.sleep(2**attempt * 3)
        raise LLMError(f"chat failed after {self.cfg.max_retries} attempts: {last_err}")

    def chat_json(self, model: str, system: str, user: str, **kw) -> dict | list:
        """Chat expecting a JSON object/array; strips code fences and reasoning preambles."""
        text = self.chat(model, system, user, **kw)
        return extract_json(text)


def extract_json(text: str) -> dict | list:
    # strip <think> blocks emitted by reasoning models
    text = re.sub(r"<think>.*?</think>", "", text, flags=re.S)
    # prefer fenced json blocks
    fence = re.findall(r"```(?:json)?\s*(.*?)```", text, flags=re.S)
    candidates = fence + [text]
    for cand in candidates:
        cand = cand.strip()
        # find first { or [ and try progressively
        for start_ch, end_ch in (("{", "}"), ("[", "]")):
            i = cand.find(start_ch)
            j = cand.rfind(end_ch)
            if i != -1 and j > i:
                try:
                    return json.loads(cand[i : j + 1])
                except json.JSONDecodeError:
                    continue
    raise LLMError(f"no parseable JSON in completion: {text[:400]}")
