#!/usr/bin/env python3
"""Re-run the produce_for_website worker over a contiguous range of rows.

Usage:
    python extras/run_for_website_batch.py <chapter> <start_row> <end_row>

Bounds are inclusive on both ends and follow data.json order.

The script just loops -- ``run_for_website_worker`` already falls back
to the mechanical extractor on per-row failures, so a single hung worker
doesn't kill the rest of the batch. Each row's elapsed time is logged.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scaffold"))

from solve_chapter import (                             # type: ignore
    find_chapter_data_path,
    load_data,
    ensure_subsection_folder,
    run_for_website_worker,
)


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print("usage: run_for_website_batch.py <chapter> <start_row> <end_row>",
              file=sys.stderr)
        return 1
    chapter = int(argv[1])
    start = int(argv[2])
    end = int(argv[3])

    data_path = find_chapter_data_path(chapter)
    data = load_data(data_path)
    n_rows = len(data["rows"])
    if not (0 <= start <= end < n_rows):
        print(f"range [{start}, {end}] invalid; chapter {chapter} has "
              f"{n_rows} rows.", file=sys.stderr)
        return 2

    batch_t0 = time.monotonic()
    for i in range(start, end + 1):
        row = data["rows"][i]
        section = row.get("section")
        if not section:
            print(f"[batch] skip row {i} ({row.get('ref')}): no section",
                  flush=True)
            continue
        ss = ensure_subsection_folder(data_path.parent, section)
        print(f"\n[batch] === row {i}/{end}: {row['ref']} "
              f"({row.get('title')}, sec {section}, "
              f"{row.get('def_or_claim')}) ===", flush=True)
        t0 = time.monotonic()
        run_for_website_worker(row, ss, register_on_row=False)
        print(f"[batch] row {row['ref']} done in "
              f"{time.monotonic() - t0:.0f}s "
              f"(batch elapsed {(time.monotonic()-batch_t0)/60:.1f} min)",
              flush=True)
    print(f"\n[batch] DONE: rows {start}..{end} processed in "
          f"{(time.monotonic()-batch_t0)/60:.1f} min",
          flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
