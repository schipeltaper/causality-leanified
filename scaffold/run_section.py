"""Loop solve_current_row until the given section is fully solved.

Usage:
    python scaffold/run_section.py <section>

Example:
    python scaffold/run_section.py 3.3      # solve every row of section 3.3

Stops as soon as no unsolved rows in ``<section>`` remain -- i.e. the
chapter's first-unsolved row sits in a different section, or the
chapter is fully solved. Also stops on a no-progress iteration so a
stuck row doesn't busy-loop the driver.
"""

from __future__ import annotations

import sys
from pathlib import Path

SCAFFOLD = Path(__file__).resolve().parent
sys.path.insert(0, str(SCAFFOLD))

from solve_chapter import (                                # type: ignore
    read_current_chapter,
    find_chapter_data_path,
    load_data,
    solve_current_row,
    first_unsolved_row_index,
)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: run_section.py <section>   (e.g. 3.3)", file=sys.stderr)
        return 1
    target_section = argv[1]

    chapter = read_current_chapter()
    data_path = find_chapter_data_path(chapter)

    iteration = 0
    while True:
        iteration += 1
        data = load_data(data_path)
        try:
            idx = first_unsolved_row_index(data)
        except RuntimeError:
            print(f"[run_section] chapter {chapter} complete; nothing left "
                  f"to do.", flush=True)
            return 0

        first_unsolved = data["rows"][idx]
        if first_unsolved.get("section") != target_section:
            print(f"[run_section] section {target_section} fully solved; "
                  f"first unsolved is now {first_unsolved['ref']} in section "
                  f"{first_unsolved.get('section')}. Stopping as requested.",
                  flush=True)
            return 0

        print(f"\n[run_section] === iteration {iteration}: solving "
              f"{first_unsolved['ref']} (section "
              f"{first_unsolved.get('section')}, "
              f"{first_unsolved.get('def_or_claim')}) ===", flush=True)

        try:
            solve_current_row()
        except Exception as e:                          # noqa: BLE001
            print(f"[run_section] solve_current_row raised: {e}", flush=True)
            return 1

        # No-progress safety: if the row we just attempted is still
        # unsolved, stop -- the next invocation can retry, and we don't
        # want to busy-loop on a stuck row.
        data_after = load_data(data_path)
        if data_after["rows"][idx].get("solved") != "yes":
            print(f"[run_section] no progress on {first_unsolved['ref']}; "
                  f"stopping cleanly so a future invocation can pick it up.",
                  flush=True)
            return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
