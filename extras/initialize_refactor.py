#!/usr/bin/env python3
"""Create the ``refactor_data.json`` for a Phase 5 refactor table.

Given a root row (the def or claim being refactored) and a list of
consumer refs (from ``extras/find_dependents.py``), this script builds
``leanification/Chapter{N}_*/Refactor_{name}/refactor_data.json`` whose
rows mirror the originals with:

- ``refactor: true`` (the orchestrator surfaces the refactor briefing
  in the manager's row context, and blocks the ``refactor`` action),
- ``solved: "no"``, ``formalized: "no"``, ``proven: "n/a"`` (the
  refactor is solved from scratch via the same-file marker convention),
- a ``tips`` line pointing the manager at the original (which lives at
  the same ``main_lean_file`` / ``tex_file`` paths),
- cleared ``agent_registry``, ``actions_tracking`` counters, and
  ``time_needed_to_solve``.

The rows are sorted by (chapter number, original row index in chapter's
data.json) so that the root is typically first and dependents follow in
the order they appear in the LN -- matching how a normal chapter solve
walks bottom-up through dependencies.

The refactor table can then be driven to completion via::

    python scaffold/solve_chapter.py --data-path \
        leanification/Chapter{N}_*/Refactor_{name}/refactor_data.json

Once every row in the table is solved, run
``extras/apply_refactor_cleanup.py`` to swap originals for replacements
atomically.

Usage::

    python extras/initialize_refactor.py \
        --root-chapter 3 --root-ref def_3_1 --name CDMG_NoDisjointEL \
        --dependents-json /tmp/cdmg_dependents.json

    # or include extra refs by hand:
    python extras/initialize_refactor.py \
        --root-chapter 3 --root-ref def_3_14 --name Marginalize \
        --dependents-json /tmp/marginalize_deps.json \
        --extra-refs claim_3_25,claim_3_27
"""

from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEANIFICATION = REPO_ROOT / "leanification"


def _find_chapter_folder(chapter: int) -> Path:
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child
    raise FileNotFoundError(
        f"no leanification folder for chapter {chapter}"
    )


def _load_all_chapter_data() -> dict[str, dict]:
    """Walk every ``leanification/Chapter*/data.json`` (NOT refactor
    tables) and return ``{ref -> {row, chapter, row_index, data_path}}``.
    """
    out: dict[str, dict] = {}
    chap_re = re.compile(r"^Chapter(\d+)_")
    for dj in sorted(LEANIFICATION.glob("Chapter*/data.json")):
        m = chap_re.match(dj.parent.name)
        if not m:
            continue
        chapter = int(m.group(1))
        try:
            data = json.loads(dj.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        for idx, row in enumerate(data.get("rows", [])):
            ref = row.get("ref")
            if ref:
                out[ref] = {
                    "row":       row,
                    "chapter":   chapter,
                    "row_index": idx,
                    "data_path": dj,
                }
    return out


def _make_refactor_row(original: dict, root_ref: str,
                       refactor_name: str) -> dict:
    """Deep-copy the original row and reset the fields that need to be
    re-derived during the refactor solve. The Lean / tex paths are kept
    identical because refactor work edits the existing files in-place
    via the marker convention."""
    row = copy.deepcopy(original)
    row["refactor"] = True
    row["solved"] = "no"
    # Definitions: ``formalized`` resets so the manager re-formalizes
    # the new shape. Claims: ``formalized`` tracks "Lean statement
    # exists"; reset it too so the refactor re-states (the LN block
    # is unchanged but the underlying types may have changed).
    row["formalized"] = "no"
    row["proven"] = "n/a"
    row["date_solved"] = None
    row["time_needed_to_solve"] = 0
    row["agent_registry"] = []
    if "actions_tracking" in row and isinstance(row["actions_tracking"], dict):
        row["actions_tracking"] = {k: 0 for k in row["actions_tracking"]}
    tip_addition = (
        f"REFACTOR row (part of refactor `{refactor_name}`, root "
        f"`{root_ref}`). The original declaration and tex block live "
        f"at the same `main_lean_file` / `tex_file` paths as this row "
        f"points at -- read them first as inspiration. Use the same-"
        f"file marker convention from manager.md (## Refactor rows) "
        f"to add the replacement alongside the original; the cleanup "
        f"script will swap them atomically at the end of the table."
    )
    existing = (row.get("tips") or "").strip()
    row["tips"] = ((existing + "\n\n" + tip_addition).strip()
                   if existing else tip_addition)
    return row


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Generate a refactor_data.json table for the given "
                    "root ref + its consumers.",
    )
    parser.add_argument("--root-chapter", type=int, required=True,
                        help="chapter number of the root row being refactored")
    parser.add_argument("--root-ref", type=str, required=True,
                        help="ref of the root row (e.g. def_3_1)")
    parser.add_argument("--name", type=str, required=True,
                        help="refactor name -- becomes the Refactor_{name}/ "
                             "folder. Use a descriptive PascalCase or "
                             "snake_case label (e.g. CDMG_NoDisjointEL).")
    parser.add_argument("--dependents-json", type=Path, required=True,
                        help="path to find_dependents.py output JSON; the "
                             "`consumer_refs` field seeds the table")
    parser.add_argument("--extra-refs", type=str, default="",
                        help="comma-separated additional refs to include "
                             "beyond what find_dependents detected (use "
                             "when manual inspection found a consumer the "
                             "scanner missed)")
    parser.add_argument("--exclude-refs", type=str, default="",
                        help="comma-separated refs to drop from the "
                             "dependents list (false positives)")
    parser.add_argument("--force", action="store_true",
                        help="overwrite Refactor_{name}/refactor_data.json "
                             "if it already exists")
    args = parser.parse_args(argv)

    # ----- Load and combine ref lists --------------------------------
    try:
        deps = json.loads(args.dependents_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: cannot read dependents JSON {args.dependents_json}: {e}",
              file=sys.stderr)
        return 1
    consumer_refs: set[str] = set(deps.get("consumer_refs", []))
    for r in args.extra_refs.split(","):
        r = r.strip()
        if r:
            consumer_refs.add(r)
    for r in args.exclude_refs.split(","):
        r = r.strip()
        if r:
            consumer_refs.discard(r)
    consumer_refs.discard(args.root_ref)         # root is added separately

    print(f"[initialize_refactor] root={args.root_ref}, "
          f"{len(consumer_refs)} consumer(s)", file=sys.stderr, flush=True)

    # ----- Resolve refs to rows --------------------------------------
    index = _load_all_chapter_data()
    if args.root_ref not in index:
        print(f"ERROR: root ref {args.root_ref!r} not in any data.json",
              file=sys.stderr)
        return 1
    refs_to_include = [args.root_ref] + sorted(consumer_refs)
    items: list[dict] = []
    missing: list[str] = []
    for ref in refs_to_include:
        if ref in index:
            items.append(index[ref])
        else:
            missing.append(ref)
    if missing:
        print(f"WARNING: {len(missing)} ref(s) not found in any data.json "
              f"and will be DROPPED: {missing}", file=sys.stderr)
    if not items:
        print("ERROR: no refs to include in the refactor table", file=sys.stderr)
        return 1

    # ----- Sort: root FIRST, then others by (chapter, row_index) -----
    # The root must be solved first so consumers can validate their
    # refactored proofs against the new shape. Without this guarantee,
    # a consumer whose data.json row_index < the root's would otherwise
    # be solved first (its proof would have to use the OLD root, then
    # at cleanup the rename would silently swap to the NEW root --
    # discovered the hard way on def_3_14_no_L_exclusion where
    # claim_3_12 at index 23 preceded def_3_14 at index 28).
    items.sort(key=lambda x: (
        0 if x["row"]["ref"] == args.root_ref else 1,
        x["chapter"],
        x["row_index"],
    ))

    # ----- Build refactor rows ---------------------------------------
    refactor_rows = [
        _make_refactor_row(item["row"], args.root_ref, args.name)
        for item in items
    ]

    # Columns: take the union from the root chapter's data.json, plus
    # the `refactor` column we just added.
    root_data = json.loads(items[0]["data_path"].read_text(encoding="utf-8"))
    columns = list(root_data.get("columns") or [])
    if "refactor" not in columns:
        columns.append("refactor")

    refactor_data = {
        "chapter":         args.root_chapter,
        "title":           f"Refactor: {args.name} (root: {args.root_ref})",
        "refactor":        True,
        "refactor_name":   args.name,
        "refactor_root":   args.root_ref,
        "created_at":      datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "columns":         columns,
        "rows":            refactor_rows,
    }

    # ----- Write -----------------------------------------------------
    try:
        chapter_folder = _find_chapter_folder(args.root_chapter)
    except FileNotFoundError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1
    refactor_folder = chapter_folder / f"Refactor_{args.name}"
    out_path = refactor_folder / "refactor_data.json"
    if out_path.exists() and not args.force:
        print(f"ERROR: {out_path} already exists; pass --force to overwrite",
              file=sys.stderr)
        return 1
    refactor_folder.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(refactor_data, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(f"[initialize_refactor] wrote {out_path}", file=sys.stderr)
    print(f"[initialize_refactor]   - {len(refactor_rows)} refactor row(s)",
          file=sys.stderr)
    chap_counts: dict[int, int] = {}
    for it in items:
        chap_counts[it["chapter"]] = chap_counts.get(it["chapter"], 0) + 1
    for ch, n in sorted(chap_counts.items()):
        print(f"[initialize_refactor]   - chapter {ch}: {n} row(s)",
              file=sys.stderr)
    print(f"\nNext step: drive the table with\n"
          f"  python scaffold/solve_chapter.py --data-path {out_path.relative_to(REPO_ROOT)}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
