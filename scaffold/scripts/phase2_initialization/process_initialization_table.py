"""Process the human-filled initialization decision table.

Reads ``leanification/Chapter{N}_*/initialization_table.md`` (filled
in by the human), extracts each subtlety's **Decision** plus the
**Additional notes (global)** section, and folds the result into
``data.json`` under each row's ``addition_to_the_LN`` field.

Per-subtlety decisions are attached to the row that *observed* the
subtlety (``observed_by_ref`` in the register entry). Global notes
are appended to every row's ``addition_to_the_LN`` with a `[global]`
prefix.

Decision values:

- ``NONE`` (case-insensitive) — no addition for this subtlety; the
  row's ``addition_to_the_LN`` is left unchanged on its behalf.
- Anything else — treated as the clarifying clause; appended to the
  observed row's ``addition_to_the_LN`` (one paragraph per subtlety,
  prefixed with the subtlety id for traceability).

The script is idempotent: re-running it overwrites the
``addition_to_the_LN`` field with the latest table contents. To
preserve hand-edited content in data.json, edit the table instead and
re-run.

Workflow position::

    [...] --> generate_initialization_table --> [HUMAN fills in table]
        --> process_initialization_table --> data.json

Usage::

    python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter 3
    python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter 3 --dry-run
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# .../scaffold/scripts/phase2_initialization/<this file>
SCRIPT_DIR = Path(__file__).resolve().parent
SCAFFOLD_DIR = SCRIPT_DIR.parent.parent                            # scaffold/
REPO_ROOT = SCAFFOLD_DIR.parent
LEANIFICATION = REPO_ROOT / "leanification"

sys.path.insert(0, str(SCRIPT_DIR.parent))
import _path_setup                                                # noqa: F401, E402
from subtlety_register import load_register                       # noqa: E402


# Match one decision block:
#   ### N. `<id>`
#   - **Observed by row:** `<ref>`
#   ... explanation ...
#   **Decision** (replace `TODO` ...):
#   ```
#   <decision body, possibly multi-line>
#   ```
_DECISION_RE = re.compile(
    r"^###\s+\d+\.\s+`(?P<id>[^`]+)`\s*\n"
    r"(?P<between>.*?)"
    r"\*\*Decision\*\*[^\n]*\n+"
    r"```\s*\n(?P<decision>.*?)\n```",
    re.DOTALL | re.MULTILINE,
)

# Match the global notes section: everything after `### Notes` up to
# the next top-level heading or end-of-file.
_GLOBAL_NOTES_RE = re.compile(
    r"###\s+Notes\s*\n+(?P<body>.*?)(?:\n##\s|\Z)",
    re.DOTALL,
)

# Stripped from the global notes body (the html comment in the template).
_TEMPLATE_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)


def _find_chapter_folder(chapter: int) -> Path:
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child
    raise FileNotFoundError(
        f"no leanification folder for chapter {chapter}")


def _parse_decisions(text: str) -> dict[str, str]:
    """Return ``{subtlety_id: decision_text}``. ``decision_text`` is
    stripped; the literal value ``"TODO"`` is treated as unfilled and
    omitted from the result."""
    out: dict[str, str] = {}
    for m in _DECISION_RE.finditer(text):
        sid = m.group("id").strip()
        decision = m.group("decision").strip()
        if not decision or decision.upper() == "TODO":
            continue
        out[sid] = decision
    return out


def _parse_global_notes(text: str) -> str:
    """Return the body of the 'Additional notes (global)' section
    with the template comment stripped. Empty string if absent."""
    m = _GLOBAL_NOTES_RE.search(text)
    if not m:
        return ""
    body = _TEMPLATE_COMMENT_RE.sub("", m.group("body")).strip()
    return body


def _build_row_addition(global_notes: str,
                        per_row_clauses: list[tuple[str, str]]) -> str:
    """Compose the ``addition_to_the_LN`` text for a single row.

    ``per_row_clauses`` is a list of ``(subtlety_id, decision_text)``
    pairs whose ``observed_by_ref`` is this row. Each becomes one
    paragraph prefixed with ``[<subtlety_id>]``. ``global_notes`` (if
    non-empty) is appended with a ``[global]`` prefix.
    """
    parts: list[str] = []
    for sid, decision in per_row_clauses:
        if decision.upper() == "NONE":
            continue
        parts.append(f"[{sid}] {decision.strip()}")
    if global_notes:
        parts.append(f"[global] {global_notes.strip()}")
    return "\n\n".join(parts)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Process the filled-in initialization decision "
                    "table into data.json's addition_to_the_LN column.")
    parser.add_argument("--chapter", type=int, required=True,
                        help="chapter number, e.g. 3")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the resulting per-row additions but "
                             "do not modify data.json")
    args = parser.parse_args(argv)

    chapter_folder = _find_chapter_folder(args.chapter)
    table_path = chapter_folder / "initialization_table.md"
    data_path = chapter_folder / "data.json"
    if not table_path.exists():
        print(f"ERROR: {table_path} not found. Run "
              f"`generate_initialization_table.py --chapter {args.chapter}` "
              f"first.", file=sys.stderr)
        return 1
    if not data_path.exists():
        print(f"ERROR: {data_path} not found.", file=sys.stderr)
        return 1

    table_text = table_path.read_text(encoding="utf-8")
    decisions = _parse_decisions(table_text)
    global_notes = _parse_global_notes(table_text)
    register = load_register("initial")
    id_to_ref: dict[str, str] = {
        e.get("id"): e.get("observed_by_ref")
        for e in register if e.get("id")
    }

    # Group decisions by observed_by_ref.
    by_ref: dict[str, list[tuple[str, str]]] = {}
    unattributed: list[str] = []
    for sid, decision in decisions.items():
        ref = id_to_ref.get(sid)
        if ref is None:
            unattributed.append(sid)
            continue
        by_ref.setdefault(ref, []).append((sid, decision))

    if unattributed:
        print(f"WARNING: {len(unattributed)} decision id(s) have no "
              f"matching register entry (the register has been changed "
              f"since the table was generated?): {unattributed}",
              file=sys.stderr)

    print(f"[process_initialization_table] chapter={args.chapter}, "
          f"{len(decisions)} per-row decision(s), "
          f"{'global notes present' if global_notes else 'no global notes'}",
          file=sys.stderr)

    data = json.loads(data_path.read_text(encoding="utf-8"))
    rows = data.get("rows", [])
    columns = list(data.get("columns") or [])
    if "addition_to_the_LN" not in columns:
        columns.append("addition_to_the_LN")
    data["columns"] = columns

    changed = 0
    for row in rows:
        ref = row.get("ref")
        if not ref:
            continue
        per_row = by_ref.get(ref, [])
        addition = _build_row_addition(global_notes, per_row)
        if row.get("addition_to_the_LN") != addition:
            row["addition_to_the_LN"] = addition
            changed += 1
            if args.dry_run:
                print(f"  [{ref}] would set addition_to_the_LN to:\n"
                      f"    {addition!r}", file=sys.stderr)

    if args.dry_run:
        print(f"[process_initialization_table] DRY RUN: would update "
              f"{changed} row(s). No write performed.", file=sys.stderr)
        return 0

    data_path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"[process_initialization_table] wrote {data_path} "
          f"({changed} row(s) updated)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
