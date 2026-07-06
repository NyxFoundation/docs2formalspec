"""Stage 1-2: extract normative requirements from docs and assemble an RFC2119 spec."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field

from .config import Config
from .ingest import SourceDoc
from .llm import LLM

EXTRACT_SYSTEM = """\
You are a requirements engineer producing normative specifications from product \
documentation. You extract precise, testable requirements and express each one as a \
single RFC 2119 sentence (MUST / MUST NOT / SHALL / SHOULD / SHOULD NOT / MAY). \
You never invent behavior not grounded in the source text. Output JSON only."""

EXTRACT_USER_TMPL = """\
Source document ({source}):

<document>
{markdown}
</document>

Extract every normative requirement about the system's behavior (state changes, \
arithmetic, access control, fees, limits, invariants, failure conditions). Ignore \
marketing, tutorials, UI walkthroughs.

Return a JSON array of objects:
- "id": short slug (e.g. "deposit-mint-shares")
- "category": one of ["state", "arithmetic", "access-control", "economic", "temporal", "failure"]
- "statement": one RFC 2119 sentence, subject = the system component
- "rationale": <=1 sentence, why the source implies this
- "source_quote": the exact supporting sentence(s) copied from the document
- "formalizable": true ONLY if the requirement can be stated as a predicate over an \
on-chain state-transition model (state variables, operation guards/effects, arithmetic \
relations). Off-chain duties (custody, attestations, legal/jurisdiction checks, \
frontend behavior, business processes) are NOT formalizable.
"""

MERGE_SYSTEM = """\
You deduplicate and reconcile requirement lists extracted from multiple documents of \
the same system. Merge near-duplicates (keep the strongest phrasing), drop vacuous \
items, keep ids stable and unique, and flag contradictions. Output JSON only."""


@dataclass
class Requirement:
    id: str
    category: str
    statement: str
    rationale: str
    source_quote: str
    formalizable: bool
    sources: list[str] = field(default_factory=list)


def extract_requirements(llm: LLM, cfg: Config, docs: list[SourceDoc]) -> list[Requirement]:
    per_doc: list[dict] = []
    for d in docs:
        items = llm.chat_json(
            cfg.extract_model,
            EXTRACT_SYSTEM,
            EXTRACT_USER_TMPL.format(source=d.source, markdown=d.markdown[:60_000]),
        )
        if isinstance(items, dict):
            items = items.get("requirements", [])
        for it in items:
            it["sources"] = [d.source]
        per_doc.extend(items)

    if len(docs) > 1:
        merged = llm.chat_json(
            cfg.extract_model,
            MERGE_SYSTEM,
            "Requirement lists to merge:\n" + json.dumps(per_doc, ensure_ascii=False)
            + '\n\nReturn JSON: {"requirements": [...same schema, with "sources" as the union...], "contradictions": ["..."]}',
        )
        if isinstance(merged, dict):
            per_doc = merged.get("requirements", per_doc)

    reqs = []
    for it in per_doc:
        try:
            reqs.append(Requirement(**{k: it.get(k) for k in Requirement.__dataclass_fields__}))
        except TypeError:
            continue
    return reqs


SPEC_SYSTEM = """\
You are a standards editor writing a complete RFC-2119-conformant specification \
document in markdown. Structure: Title, Status, 1. Introduction (system purpose, \
scope), 2. Terminology (RFC 2119 boilerplate + domain terms), 3. System Model \
(actors, state variables, operations), then one numbered section per requirement \
category, each requirement as its own numbered clause "REQ-<ID>" quoting its RFC 2119 \
statement followed by a short elaboration. End with Security Considerations and \
References (the source URLs). Do not invent requirements beyond the given list."""


def render_spec(llm: LLM, cfg: Config, system_name: str, reqs: list[Requirement], sources: list[str]) -> str:
    return llm.chat(
        cfg.extract_model,
        SPEC_SYSTEM,
        f"System: {system_name}\nSource documents: {sources}\n\nRequirements JSON:\n"
        + json.dumps([asdict(r) for r in reqs], ensure_ascii=False, indent=1),
        max_tokens=16_000,
    )
