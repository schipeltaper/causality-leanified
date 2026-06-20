#!/usr/bin/env python3
"""Build the Section 3.1 refactor-iteration time table.

Each ROW of the output is a Section 3.1 def/claim.
Each COLUMN is an iteration:

    iteration 0 : initial solve (before any refactor)
    iteration k : the k-th refactor (chronological by `created_at`)

Each CELL is `time_needed_to_solve` (seconds) for that row in that
iteration; blank if the row was not (re-)solved in that iteration.

------------------------------------------------------------------
How the numbers are sourced (verified 2026-06-20)
------------------------------------------------------------------
`time_needed_to_solve` semantics:

  * A refactor's `refactor_data.json` row holds a FRESH re-solve time:
    `extras/initialize_refactor.py` resets it to 0 at refactor start,
    so the value is the wall-clock spent re-solving that row DURING
    that refactor.
  * `extras/apply_refactor_cleanup.py` (Phase 7d) OVERWRITES the main
    `data.json` row's `time_needed_to_solve` with the refactor value
    on a successful sync, and archives the previous main-data value in
    that refactor's `pre_refactor_rows.json` -> `pre_sync_row`.
  * Hence a refactor's `pre_sync` value = the result of the PREVIOUS
    iteration for that row.

Two facts specific to Chapter 3 that this script relies on:

  * `Refactor_total_order_helper_DONE_2026-06-07` predates the
    cleanup-sync mechanism: it has NO `pre_refactor_rows.json` and its
    re-solve times (def_3_8=2561, claim_3_2=2927, def_3_9=2355) were
    never written back into the main `data.json`. So they show up only
    in this refactor's own column, never as anyone's `pre_sync`.
  * `Refactor_cdmg_typed_edges_BUILDFAIL_2026-06-19` is the only
    refactor that touched Section 3.1, and its cleanup WAS synced
    (current main-data values == its refactor_data values). Its
    `pre_sync` values are therefore the TRUE INITIAL solve times for
    every Section 3.1 row (total_order never overwrote them).

Consequence: the "initial" column for each row is taken from the
earliest available `pre_sync` for that row (which, for Section 3.1, is
always the cdmg refactor's `pre_sync`).
"""

import csv
import json
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CH3 = REPO / "leanification" / "Chapter3_GraphTheory"
DATA = CH3 / "data.json"
OUT_CSV = REPO / "results" / "section3_1_refactor_times.csv"
OUT_MD = REPO / "results" / "section3_1_refactor_times.md"


def load_json(p: Path):
    return json.loads(p.read_text(encoding="utf-8"))


def main() -> None:
    main_data = load_json(DATA)
    sec31_refs = [r["ref"] for r in main_data["rows"] if r.get("section") == "3.1"]

    # ---- discover refactor folders, ordered chronologically -----------
    refactors = []  # (created_at, label, refactor_data, pre_sync_map)
    for folder in sorted(CH3.glob("Refactor_*")):
        rd_path = folder / "refactor_data.json"
        if not rd_path.exists():
            continue
        rd = load_json(rd_path)
        # short label = the refactor_name without the folder date suffix
        label = rd.get("refactor_name") or folder.name

        result_map = {row["ref"]: row.get("time_needed_to_solve")
                      for row in rd.get("rows", [])}

        pre_path = folder / "pre_refactor_rows.json"
        pre_map = {}
        if pre_path.exists():
            for entry in load_json(pre_path):
                ref = entry.get("ref")
                psr = entry.get("pre_sync_row", {})
                pre_map[ref] = psr.get("time_needed_to_solve")

        refactors.append({
            "created_at": rd.get("created_at", ""),
            "folder": folder.name,
            "label": label,
            "results": result_map,
            "pre_sync": pre_map,
        })

    refactors.sort(key=lambda r: r["created_at"])

    # ---- initial (iteration 0) time per row ---------------------------
    # earliest available pre_sync for the row across all refactors
    initial = {}
    for ref in sec31_refs:
        for rf in refactors:  # already chronological
            if ref in rf["pre_sync"] and rf["pre_sync"][ref] is not None:
                initial[ref] = rf["pre_sync"][ref]
                break

    # ---- assemble column headers --------------------------------------
    columns = ["initial"] + [rf["label"] for rf in refactors]

    # ---- assemble rows ------------------------------------------------
    table = []
    for ref in sec31_refs:
        row = {"ref": ref, "initial": initial.get(ref)}
        for rf in refactors:
            row[rf["label"]] = rf["results"].get(ref)
        table.append(row)

    # ---- write CSV ----------------------------------------------------
    with OUT_CSV.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["ref"] + columns)
        for row in table:
            w.writerow([row["ref"]] + [row.get(c) if row.get(c) is not None
                                       else "" for c in columns])

    # ---- write Markdown ----------------------------------------------
    def cell(v):
        return str(v) if v is not None else ""

    # human-friendly column headers with iteration index + date
    hdr_cells = ["ref", "iter 0<br>initial"]
    for i, rf in enumerate(refactors, start=1):
        date = rf["created_at"][:10]
        hdr_cells.append(f"iter {i}<br>{rf['label']}<br>{date}")

    lines = []
    lines.append("# Section 3.1 — time needed to solve, per refactor iteration")
    lines.append("")
    lines.append("Cell = `time_needed_to_solve` in seconds for that row in that "
                 "iteration. Blank = the row was not (re-)solved in that "
                 "iteration. See `extract_section3_1_refactor_times.py` for "
                 "exactly how each number is sourced.")
    lines.append("")
    lines.append("| " + " | ".join(hdr_cells) + " |")
    lines.append("|" + "|".join(["---"] * len(hdr_cells)) + "|")
    for row in table:
        cells = [row["ref"], cell(row.get("initial"))]
        for rf in refactors:
            cells.append(cell(row.get(rf["label"])))
        lines.append("| " + " | ".join(cells) + " |")
    lines.append("")
    lines.append("## Refactor iterations (chronological)")
    lines.append("")
    lines.append("| iter | refactor | created_at | folder |")
    lines.append("|---|---|---|---|")
    lines.append("| 0 | (initial solve) | — | — |")
    for i, rf in enumerate(refactors, start=1):
        lines.append(f"| {i} | {rf['label']} | {rf['created_at']} | "
                     f"{rf['folder']} |")
    lines.append("")

    OUT_MD.write_text("\n".join(lines), encoding="utf-8")

    # ---- echo to stdout ----------------------------------------------
    print("Section 3.1 refactor-iteration times (seconds):\n")
    print(OUT_MD.read_text(encoding="utf-8"))
    print(f"\nWrote: {OUT_CSV}")
    print(f"Wrote: {OUT_MD}")


if __name__ == "__main__":
    main()
