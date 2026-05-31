#!/usr/bin/env python3
"""Create the ``refactor_data.json`` for a Phase 5 refactor table.

Given one or more *root* refs (the def(s) or claim(s) being refactored)
and the consumers each root affects (from ``extras/find_dependents.py``),
this script builds
``leanification/Chapter{N}_*/Refactor_{name}/refactor_data.json`` whose
rows mirror the originals with:

- ``refactor: true`` (the orchestrator surfaces the refactor briefing
  in the manager's row context, and blocks the ``refactor`` action),
- ``refactor_role`` is ``"root"`` for the root rows and ``"dependent"``
  otherwise,
- ``caused_by_roots`` lists the root ref(s) that introduced the row
  into the table (a row touched by multiple roots is deduped to one
  row and carries all causes),
- ``solved: "no"``, ``formalized: "no"``, ``proven: "n/a"`` (the
  refactor is solved from scratch via the same-file marker convention),
- a ``tips`` line pointing the manager at the original (which lives at
  the same ``main_lean_file`` / ``tex_file`` paths),
- cleared ``agent_registry``, ``actions_tracking`` counters, and
  ``time_needed_to_solve``.

Rows are sorted by ``(chapter, row_index)`` -- data.json natural order
-- because the LN's ordering already guarantees every def/claim
depends only on earlier rows, so roots naturally precede their
dependents. No root-first bias.

The refactor table can then be driven to completion via::

    python scaffold/solve_chapter.py --data-path \\
        leanification/Chapter{N}_*/Refactor_{name}/refactor_data.json

Once every row in the table is solved, run
``extras/apply_refactor_cleanup.py`` to swap originals for replacements
atomically.

Usage::

    # Single-root (back-compat: --root-ref is a deprecated alias):
    python extras/initialize_refactor.py \\
        --root-chapter 3 --root-refs def_3_1 --name CDMG_NoDisjointEL \\
        --dependents-json /tmp/cdmg_dependents.json

    # Multi-root in one go:
    python extras/initialize_refactor.py \\
        --root-chapter 3 \\
        --root-refs def_3_1,def_3_4 \\
        --name ch3_disjoint_EL_and_collider_loose \\
        --dependents-json /tmp/combined_deps.json

The ``--dependents-json`` payload supports two shapes:

1. **Legacy single-root**::

       {"consumer_refs": ["claim_3_16", ...]}

   Used only when exactly one root is supplied.

2. **Multi-root (combined)**::

       {"per_root": {
            "def_3_1": {"consumer_refs": [...]},
            "def_3_4": {"consumer_refs": [...]}
        }}

   Each root's consumers are tracked separately so the provenance
   (``caused_by_roots``) can be assembled accurately.
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


def _make_refactor_row(original: dict, refactor_name: str,
                       roots: list[str], role: str,
                       caused_by_roots: list[str]) -> dict:
    """Deep-copy the original row and reset the fields that need to be
    re-derived during the refactor solve. The Lean / tex paths are kept
    identical because refactor work edits the existing files in-place
    via the marker convention.

    ``role`` is ``"root"`` if this row is itself a refactor root, else
    ``"dependent"``. ``caused_by_roots`` is the deduped, sorted list of
    roots that pulled this row into the table.
    """
    row = copy.deepcopy(original)
    row["refactor"] = True
    row["refactor_role"] = role
    row["caused_by_roots"] = sorted(caused_by_roots)
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
    cause_str = ", ".join(f"`{r}`" for r in sorted(caused_by_roots))
    if role == "root":
        why = (f"This row is a refactor ROOT in `{refactor_name}` "
               f"(roots: {', '.join(f'`{r}`' for r in roots)}).")
    else:
        why = (f"This row is a DEPENDENT in refactor `{refactor_name}`; "
               f"it was pulled in because root(s) {cause_str} changed "
               f"underneath it.")
    tip_addition = (
        f"REFACTOR row. {why} The original declaration and tex block "
        f"live at the same `main_lean_file` / `tex_file` paths as this "
        f"row points at -- read them first as inspiration. Use the "
        f"same-file marker convention from manager.md (## Refactor "
        f"rows) to add the replacement alongside the original; the "
        f"cleanup script will swap them atomically at the end of the "
        f"table."
    )
    existing = (row.get("tips") or "").strip()
    row["tips"] = ((existing + "\n\n" + tip_addition).strip()
                   if existing else tip_addition)
    return row


def _parse_root_refs(args: argparse.Namespace) -> list[str]:
    """Resolve the root-ref list from CLI args. Accepts the new
    ``--root-refs`` (comma-separated) and the legacy ``--root-ref``
    (single ref) as a deprecated alias. Returns the deduped list in
    input order."""
    raw: list[str] = []
    if args.root_refs:
        raw.extend(r.strip() for r in args.root_refs.split(",") if r.strip())
    if args.root_ref:
        print("[initialize_refactor] WARNING: --root-ref is deprecated; "
              "use --root-refs (comma-separated) instead. Accepted as "
              "a single-element list for back-compat.", file=sys.stderr)
        raw.append(args.root_ref.strip())
    seen: set[str] = set()
    out: list[str] = []
    for r in raw:
        if r and r not in seen:
            seen.add(r)
            out.append(r)
    return out


def _parse_dependents_json(path: Path, roots: list[str]
                           ) -> dict[str, set[str]]:
    """Return ``{root_ref: set(consumer_refs)}``. Supports both the
    legacy single-root shape (``{"consumer_refs": [...]}``) and the
    new multi-root shape (``{"per_root": {root: {"consumer_refs": [...]}}}``).
    """
    try:
        deps = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        raise SystemExit(
            f"ERROR: cannot read dependents JSON {path}: {e}")
    if "per_root" in deps:
        per_root = deps["per_root"]
        if not isinstance(per_root, dict):
            raise SystemExit(
                f"ERROR: {path}: `per_root` must be an object, got "
                f"{type(per_root).__name__}")
        out: dict[str, set[str]] = {}
        for root in roots:
            entry = per_root.get(root) or {}
            out[root] = set(entry.get("consumer_refs") or [])
        unknown = set(per_root.keys()) - set(roots)
        if unknown:
            print(f"[initialize_refactor] WARNING: dependents JSON has "
                  f"entries for non-root ref(s) {sorted(unknown)}; "
                  f"ignored.", file=sys.stderr)
        return out
    # Legacy shape: single root, top-level consumer_refs.
    if len(roots) != 1:
        raise SystemExit(
            f"ERROR: {path} uses the legacy single-root shape "
            f"(`consumer_refs` at top level) but {len(roots)} roots "
            f"were supplied. Combine the per-root scans into a "
            f"`per_root` object first.")
    return {roots[0]: set(deps.get("consumer_refs") or [])}


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Generate a refactor_data.json table for one or more "
                    "root refs plus their consumers.",
    )
    parser.add_argument("--root-chapter", type=int, required=True,
                        help="chapter number used to locate the "
                             "Refactor_<name>/ output folder (the refactor "
                             "table lives under this chapter even if roots "
                             "span chapters)")
    parser.add_argument("--root-refs", type=str, default="",
                        help="comma-separated root refs being refactored "
                             "(e.g. `def_3_1,def_3_4`)")
    parser.add_argument("--root-ref", type=str, default="",
                        help="[DEPRECATED] single root ref; use --root-refs "
                             "instead. Kept as an alias.")
    parser.add_argument("--name", type=str, required=True,
                        help="refactor name -- becomes the Refactor_{name}/ "
                             "folder. Use a descriptive PascalCase or "
                             "snake_case label that captures the bundle "
                             "(e.g. ch3_disjoint_EL_and_collider_loose).")
    parser.add_argument("--dependents-json", type=Path, required=True,
                        help="path to dependents JSON; either the legacy "
                             "single-root shape (`{\"consumer_refs\": "
                             "[...]}`) when one root is supplied, or the "
                             "multi-root shape (`{\"per_root\": {<root>: "
                             "{\"consumer_refs\": [...]}, ...}}`)")
    parser.add_argument("--extra-refs", type=str, default="",
                        help="comma-separated additional refs to include "
                             "beyond what find_dependents detected (use "
                             "when manual inspection found a consumer the "
                             "scanner missed; attributed to all roots)")
    parser.add_argument("--exclude-refs", type=str, default="",
                        help="comma-separated refs to drop from the "
                             "dependents list (false positives)")
    parser.add_argument("--force", action="store_true",
                        help="overwrite Refactor_{name}/refactor_data.json "
                             "if it already exists")
    args = parser.parse_args(argv)

    # ----- Resolve root list -----------------------------------------
    roots = _parse_root_refs(args)
    if not roots:
        print("ERROR: no roots supplied (use --root-refs)", file=sys.stderr)
        return 1

    # ----- Load index + validate roots exist -------------------------
    index = _load_all_chapter_data()
    missing_roots = [r for r in roots if r not in index]
    if missing_roots:
        print(f"ERROR: root ref(s) {missing_roots} not in any data.json",
              file=sys.stderr)
        return 1

    # ----- Parse + merge dependents ----------------------------------
    per_root_consumers = _parse_dependents_json(args.dependents_json, roots)

    # Manual overrides apply uniformly: extras are credited to all roots
    # (we don't know which root introduced them), excludes drop from
    # every root's set.
    extras = {r.strip() for r in args.extra_refs.split(",") if r.strip()}
    excludes = {r.strip() for r in args.exclude_refs.split(",") if r.strip()}
    for root in roots:
        per_root_consumers[root] |= extras
        per_root_consumers[root] -= excludes
        # A root is never its own consumer.
        per_root_consumers[root].discard(root)

    # ----- Config-error: is any root a dependent of another root? ----
    roots_set = set(roots)
    for root in roots:
        cross = per_root_consumers[root] & roots_set
        if cross:
            offenders = sorted(cross)
            print(f"ERROR: root {root!r} has root(s) {offenders} in its "
                  f"dependents list -- one of these is the parent of "
                  f"another. Multi-root refactors require independent "
                  f"roots; drop the dependent root from --root-refs and "
                  f"it will be picked up as a regular dependent.",
                  file=sys.stderr)
            return 1

    # ----- Invert: ref -> set of roots that pulled it in -------------
    caused_by: dict[str, set[str]] = {r: {r} for r in roots}
    for root, consumers in per_root_consumers.items():
        for ref in consumers:
            caused_by.setdefault(ref, set()).add(root)

    # ----- Resolve every ref to a chapter row ------------------------
    all_refs = sorted(caused_by.keys())
    items: list[dict] = []
    dropped: list[str] = []
    for ref in all_refs:
        if ref in index:
            entry = dict(index[ref])
            entry["caused_by_roots"] = sorted(caused_by[ref])
            items.append(entry)
        else:
            dropped.append(ref)
    if dropped:
        print(f"WARNING: {len(dropped)} ref(s) not found in any data.json "
              f"and will be DROPPED: {dropped}", file=sys.stderr)
    if not items:
        print("ERROR: no refs to include in the refactor table",
              file=sys.stderr)
        return 1

    # ----- Sort by data.json natural order (chapter, row_index) ------
    # The LN's data.json ordering ensures every claim/def depends only
    # on earlier rows, so roots naturally land before their dependents.
    # No root-first bias.
    items.sort(key=lambda x: (x["chapter"], x["row_index"]))

    # ----- Build refactor rows ---------------------------------------
    refactor_rows = [
        _make_refactor_row(
            it["row"], args.name, roots,
            role=("root" if it["row"]["ref"] in roots_set else "dependent"),
            caused_by_roots=it["caused_by_roots"],
        )
        for it in items
    ]

    # Columns: take the union from any chapter's data.json the items
    # came from (use the first), plus the new fields we just added.
    src_data = json.loads(items[0]["data_path"].read_text(encoding="utf-8"))
    columns = list(src_data.get("columns") or [])
    for new_col in ("refactor", "refactor_role", "caused_by_roots"):
        if new_col not in columns:
            columns.append(new_col)

    refactor_data = {
        "chapter":         args.root_chapter,
        "title":           (f"Refactor: {args.name} "
                            f"(roots: {', '.join(roots)})"),
        "refactor":        True,
        "refactor_name":   args.name,
        "refactor_roots":  roots,
        "refactor_root":   roots[0],   # legacy alias
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
    print(f"[initialize_refactor]   - {len(refactor_rows)} refactor row(s) "
          f"across {len(roots)} root(s): {roots}", file=sys.stderr)
    n_roots_in_table = sum(1 for r in refactor_rows
                           if r.get("refactor_role") == "root")
    n_deps = len(refactor_rows) - n_roots_in_table
    print(f"[initialize_refactor]   - {n_roots_in_table} root row(s), "
          f"{n_deps} dependent row(s)", file=sys.stderr)
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
