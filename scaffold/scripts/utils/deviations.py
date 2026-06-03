"""Global deviation register.

A *deviation* is a documented mismatch between the lecture notes' literal
definition of an object and the Lean encoding we built for it. The
register lives at ``leanification/deviations.json`` -- one global file
that every chapter reads, since foundational types (CDMG, walks,
marginalization, etc.) are reused across chapters.

Each entry is a structured record describing the deviation at the
*property level*, not the consumer level: it states what mathematical
property the LN says holds that our encoding does not (or vice versa),
plus a pattern that downstream consumers can pattern-match against to
decide whether they're at risk.

Schema::

    {
      "id":                "<unique-snake-case-id>",
      "introduced_by_ref": "def_3_14",
      "introduced_at":     "2026-05-29",
      "breaks":            "<one-line property the LN says holds, ours doesn't>",
      "preserves":         "<one-line property that still holds>",
      "at_risk_pattern":   "<pattern downstream proofs should grep against>",
      "tags":              ["marginalization", "disjoint_EL"],
      "notes":             "<free-form context / link to design block>"
    }

The register is append-only via this module's API; entries are never
modified or removed automatically (a human can edit the JSON if needed).
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path

# .../scaffold/scripts/utils/<this file> -> repo root is three levels up.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
DEVIATIONS_PATH = REPO_ROOT / "leanification" / "deviations.json"

# Fields every entry must have for the helpers to behave predictably.
_REQUIRED_FIELDS = (
    "id", "introduced_by_ref", "breaks", "preserves",
    "at_risk_pattern", "tags",
)


def load_register(include_resolved: bool = False) -> list[dict]:
    """Return deviation entries in insertion order. Missing file or
    empty file is treated as an empty register.

    By default, entries tagged with a ``resolved_at`` field (added by
    :func:`mark_resolved` after a refactor superseded the deviation)
    are filtered out -- consumers like :func:`find_at_risk_for_claim`
    should not surface stale warnings. Pass ``include_resolved=True``
    to get the raw list, e.g., for audit/reporting tools.
    """
    if not DEVIATIONS_PATH.exists():
        return []
    try:
        data = json.loads(DEVIATIONS_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []
    if not isinstance(data, list):
        return []
    if include_resolved:
        return data
    return [e for e in data if not e.get("resolved_at")]


def save_register(entries: list[dict]) -> None:
    """Overwrite the register with the given list. Pretty-printed,
    UTF-8, with a trailing newline so editors play nicely."""
    DEVIATIONS_PATH.parent.mkdir(parents=True, exist_ok=True)
    DEVIATIONS_PATH.write_text(
        json.dumps(entries, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def register_deviation(entry: dict) -> dict:
    """Append a single deviation entry. Backfills:

    - ``introduced_at`` -- today's date in ISO ``YYYY-MM-DD`` (if missing).
    - ``tags``           -- empty list (if missing).
    - ``notes``          -- empty string (if missing).

    Raises ``ValueError`` if any required field besides those is missing,
    or if the entry's ``id`` collides with an existing entry (the
    register is append-only -- to update a recorded deviation, edit the
    JSON by hand).
    """
    entry = dict(entry)
    entry.setdefault("introduced_at",
                     datetime.now(timezone.utc).date().isoformat())
    entry.setdefault("tags", [])
    entry.setdefault("notes", "")
    missing = [f for f in _REQUIRED_FIELDS if not entry.get(f)]
    if missing:
        raise ValueError(
            f"deviation entry missing required field(s): {missing}; got "
            f"{sorted(entry.keys())}")
    # Collision check looks at the FULL register (including resolved
    # entries) -- a previously-resolved deviation's id is still taken.
    existing = load_register(include_resolved=True)
    if any(e.get("id") == entry["id"] for e in existing):
        raise ValueError(
            f"deviation id {entry['id']!r} already in the register; "
            f"edit the JSON by hand if you really want to overwrite")
    existing.append(entry)
    save_register(existing)
    return entry


def mark_resolved(entry_id: str, resolved_by_refactor: str,
                  resolved_at: str | None = None) -> dict:
    """Tag the entry whose ``id`` matches ``entry_id`` as resolved by a
    completed refactor. The entry stays in the register (history is
    preserved) but :func:`load_register` filters it from the default
    list. Adds two fields:

    - ``resolved_at`` -- ISO date (defaults to today's UTC date).
    - ``resolved_by_refactor`` -- the refactor name (free-form label
      identifying which refactor superseded the deviation).

    Idempotent: re-resolving an already-resolved entry overwrites
    these two fields (useful if a later refactor re-resolves something
    a previous one only partly addressed).

    Raises ``KeyError`` if no entry has the given id.
    """
    entries = load_register(include_resolved=True)
    for e in entries:
        if e.get("id") == entry_id:
            e["resolved_at"] = (resolved_at
                                or datetime.now(timezone.utc).date().isoformat())
            e["resolved_by_refactor"] = resolved_by_refactor
            save_register(entries)
            return e
    raise KeyError(
        f"no deviation entry with id {entry_id!r} in the register"
    )


def find_relevant(ref: str | None = None,
                  tags: list[str] | None = None,
                  introduced_by_ref: str | None = None,
                  include_resolved: bool = False,
                  ) -> list[dict]:
    """Filter the register by any combination of:

    - ``introduced_by_ref`` -- exact match.
    - ``tags`` -- entries whose ``tags`` intersect the given list.
    - ``ref`` -- entries whose ``introduced_by_ref`` equals ``ref``
      OR whose ``id`` mentions ``ref`` (a coarse string match).

    Filters compose with AND. Empty / ``None`` filters are skipped.

    ``include_resolved`` (default ``False``) controls whether entries
    tagged via :func:`mark_resolved` are considered. The
    default-skip is intentional: a resolved deviation no longer
    applies to downstream consumers.
    """
    entries = load_register(include_resolved=include_resolved)
    out: list[dict] = []
    for e in entries:
        if introduced_by_ref and e.get("introduced_by_ref") != introduced_by_ref:
            continue
        if tags:
            if not set(tags) & set(e.get("tags", [])):
                continue
        if ref:
            if (e.get("introduced_by_ref") != ref
                    and ref not in e.get("id", "")):
                continue
        out.append(e)
    return out


def find_at_risk_for_claim(claim_body_text: str,
                           defs_cited: list[str] | None = None,
                           ) -> list[dict]:
    """Heuristic: given a claim's body text (e.g. its tex_block, or the
    concatenated tex proof) and optionally the list of def refs it
    cites, return deviation entries the claim might be at risk of.

    Match strategy:
    - Any entry whose ``introduced_by_ref`` is in ``defs_cited`` is
      automatically relevant (the claim directly uses the deviated def).
    - For other entries, do a simple substring search of each entry's
      ``at_risk_pattern`` keywords (tokenised on whitespace, dropping
      common words) against the claim body. Coarse but conservative.

    Returns the matching entries; callers decide what to surface to
    the manager.
    """
    out: list[dict] = []
    defs_cited_set = set(defs_cited or [])
    body_lower = claim_body_text.lower() if claim_body_text else ""
    for e in load_register():
        if e.get("introduced_by_ref") in defs_cited_set:
            out.append(e)
            continue
        pattern = (e.get("at_risk_pattern") or "").lower()
        # Take the longer words of the pattern as keywords; if any of
        # them appears in the claim body, flag it.
        keywords = [w for w in pattern.split() if len(w) >= 5]
        if any(k in body_lower for k in keywords):
            out.append(e)
    return out


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "list":
        for e in load_register():
            print(f"  [{e.get('id')}]  (introduced by {e.get('introduced_by_ref')}, "
                  f"tags={e.get('tags')})")
            print(f"    breaks:          {e.get('breaks')}")
            print(f"    preserves:       {e.get('preserves')}")
            print(f"    at_risk_pattern: {e.get('at_risk_pattern')}")
            print()
    else:
        print(f"deviations register: {DEVIATIONS_PATH}")
        print(f"  entry count: {len(load_register())}")
        print("usage: python scaffold/scripts/utils/deviations.py list")
