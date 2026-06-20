#!/usr/bin/env python3
"""Build a per-row x per-iteration time table for Chapter 3.

By default it covers Sections 3.1, 3.2 and 3.3 (pass other sections on
the command line, e.g. `python3 extract_section3_refactor_times.py 3.1
3.2`).

Each ROW of the output is a def/claim in one of the chosen sections,
listed in lecture-notes order. Each COLUMN is an iteration:

    iteration 0 : initial solve (before any refactor)
    iteration k : the k-th refactor (chronological by `created_at`)

Each CELL is `time_needed_to_solve` (seconds) for that row in that
iteration; blank if the row was not (re-)solved in that iteration.

------------------------------------------------------------------
How the numbers are sourced (verified 2026-06-20)
------------------------------------------------------------------
`time_needed_to_solve` semantics:

  * A refactor's `refactor_data.json` row holds a FRESH re-solve time:
    `extras/initialize_refactor.py` resets it to 0 at refactor start, so
    the value is the wall-clock spent re-solving that row DURING that
    refactor.
  * `extras/apply_refactor_cleanup.py` (Phase 7d) OVERWRITES the main
    `data.json` row's `time_needed_to_solve` with the refactor value on a
    successful sync, and archives the previous main-data value in that
    refactor's `pre_refactor_rows.json` -> `pre_sync_row`. Hence a
    refactor's `pre_sync` value = the result of the PREVIOUS iteration
    for that row.

This chaining was verified to be internally consistent across 3.1-3.3:
for every row touched by more than one sync-aware refactor, each later
refactor's `pre_sync` equals the earlier refactor's result.

Two facts specific to Chapter 3:

  * `Refactor_total_order_helper_DONE_2026-06-07` predates the
    cleanup-sync mechanism: it has NO `pre_refactor_rows.json` and its
    re-solve times (def_3_8=2561, claim_3_2=2927, def_3_9=2355) were
    never written back into the main `data.json`. So they appear only in
    this refactor's own column, never as anyone's `pre_sync`, and the
    "initial" values of those rows are recovered cleanly from the cdmg
    refactor's `pre_sync` (which equals the genuine first-solve time).
  * `Refactor_cdmg_typed_edges_BUILDFAIL_2026-06-19` (the Lean build
    failed, but its data cleanup WAS synced) touched essentially all of
    3.1-3.3; current main-data values equal its refactor_data values.

Per-row "initial" rule:
  * if the row was touched by any refactor -> the earliest available
    `pre_sync` for that row;
  * otherwise (never refactored) -> the current main `data.json` value.
"""

import csv
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CH3 = REPO / "leanification" / "Chapter3_GraphTheory"
DATA = CH3 / "data.json"


def load_json(p: Path):
    return json.loads(p.read_text(encoding="utf-8"))


def main(sections) -> None:
    main_data = load_json(DATA)
    rows = [r for r in main_data["rows"] if r.get("section") in sections]
    sec_refs = [r["ref"] for r in rows]
    section_of = {r["ref"]: r.get("section") for r in rows}
    current = {r["ref"]: r.get("time_needed_to_solve") for r in rows}

    # ---- discover refactor folders, ordered chronologically -----------
    refactors = []
    for folder in sorted(CH3.glob("Refactor_*")):
        rd_path = folder / "refactor_data.json"
        if not rd_path.exists():
            continue
        rd = load_json(rd_path)
        label = rd.get("refactor_name") or folder.name
        result_map = {row["ref"]: row.get("time_needed_to_solve")
                      for row in rd.get("rows", [])}
        pre_path = folder / "pre_refactor_rows.json"
        pre_map = {}
        if pre_path.exists():
            for entry in load_json(pre_path):
                pre_map[entry.get("ref")] = \
                    entry.get("pre_sync_row", {}).get("time_needed_to_solve")
        refactors.append({
            "created_at": rd.get("created_at", ""),
            "folder": folder.name,
            "label": label,
            "results": result_map,
            "pre_sync": pre_map,
        })
    refactors.sort(key=lambda r: r["created_at"])

    # ---- initial (iteration 0) time per row ---------------------------
    initial = {}
    for ref in sec_refs:
        val = None
        for rf in refactors:  # chronological
            if rf["pre_sync"].get(ref) is not None:
                val = rf["pre_sync"][ref]
                break
        if val is None:
            # never refactored -> the current value IS the first solve
            val = current[ref]
        initial[ref] = val

    # ---- assemble table -----------------------------------------------
    labels = [rf["label"] for rf in refactors]
    table = []
    for ref in sec_refs:
        row = {"ref": ref, "section": section_of[ref],
               "initial": initial.get(ref)}
        for rf in refactors:
            row[rf["label"]] = rf["results"].get(ref)
        table.append(row)

    secs_tag = "_".join(s.replace(".", "_") for s in sorted(sections))
    out_csv = REPO / "results" / f"section{secs_tag}_refactor_times.csv"
    out_md = REPO / "results" / f"section{secs_tag}_refactor_times.md"

    # ---- CSV ----------------------------------------------------------
    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["ref", "section", "initial"] + labels)
        for row in table:
            w.writerow([row["ref"], row["section"]]
                       + [("" if row.get(c) is None else row.get(c))
                          for c in ["initial"] + labels])

    # ---- Markdown -----------------------------------------------------
    def cell(v):
        return "" if v is None else str(v)

    hdr = ["ref", "section", "iter 0<br>initial"]
    for i, rf in enumerate(refactors, start=1):
        hdr.append(f"iter {i}<br>{rf['label']}<br>{rf['created_at'][:10]}")

    lines = [
        f"# Sections {', '.join(sorted(sections))} — "
        "time needed to solve, per refactor iteration",
        "",
        "Cell = `time_needed_to_solve` in seconds for that row in that "
        "iteration. Blank = the row was not (re-)solved in that iteration. "
        "Iteration 0 is the initial solve; later columns are refactors in "
        "chronological order. See `extract_section3_refactor_times.py` for "
        "exactly how each number is sourced.",
        "",
        "| " + " | ".join(hdr) + " |",
        "|" + "|".join(["---"] * len(hdr)) + "|",
    ]
    for row in table:
        cells = [row["ref"], row["section"], cell(row.get("initial"))]
        for rf in refactors:
            cells.append(cell(row.get(rf["label"])))
        lines.append("| " + " | ".join(cells) + " |")

    lines += ["", "## Refactor iterations (chronological)", "",
              "| iter | refactor | created_at | folder |",
              "|---|---|---|---|",
              "| 0 | (initial solve) | — | — |"]
    for i, rf in enumerate(refactors, start=1):
        lines.append(f"| {i} | {rf['label']} | {rf['created_at']} | "
                     f"{rf['folder']} |")
    lines.append("")

    out_md.write_text("\n".join(lines), encoding="utf-8")

    print("\n".join(lines))
    print(f"\nWrote: {out_csv}")
    print(f"Wrote: {out_md}")


if __name__ == "__main__":
    secs = set(sys.argv[1:]) or {"3.1", "3.2", "3.3"}
    main(secs)
