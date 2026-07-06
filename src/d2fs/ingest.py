"""Ingest documentation sources (URLs or local paths) into clean markdown chunks."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import httpx
import trafilatura

UA = "Mozilla/5.0 (X11; Linux x86_64) docs2formalspec/0.1"


@dataclass
class SourceDoc:
    source: str  # original URL or path
    title: str
    markdown: str


def ingest(sources: list[str]) -> list[SourceDoc]:
    docs = []
    for s in sources:
        if s.startswith("http://") or s.startswith("https://"):
            docs.append(_ingest_url(s))
        else:
            docs.append(_ingest_file(Path(s)))
    return [d for d in docs if d and d.markdown.strip()]


def _ingest_url(url: str) -> SourceDoc | None:
    r = httpx.get(url, headers={"User-Agent": UA}, follow_redirects=True, timeout=60)
    r.raise_for_status()
    ctype = r.headers.get("content-type", "")
    # Sites like docs.apyx.fi serve pages as raw markdown at *.md URLs.
    if url.endswith(".md") or "text/markdown" in ctype or "text/plain" in ctype:
        return SourceDoc(source=url, title=_md_title(r.text) or url, markdown=r.text)
    html = r.text
    md = trafilatura.extract(
        html, output_format="markdown", include_tables=True, include_links=False
    )
    if not md:
        md = html  # fall back to raw; LLM extraction is tolerant
    title = trafilatura.extract_metadata(html).title if md else url
    return SourceDoc(source=url, title=title or url, markdown=md)


def _md_title(text: str) -> str | None:
    for line in text.splitlines():
        if line.startswith("# "):
            return line[2:].strip()
    return None


def _ingest_file(path: Path) -> SourceDoc | None:
    text = path.read_text(errors="replace")
    return SourceDoc(source=str(path), title=path.name, markdown=text)
