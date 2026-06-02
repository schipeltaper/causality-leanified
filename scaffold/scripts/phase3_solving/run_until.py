"""One-off driver: loop ``solve_current_row`` until a target ref is solved
AND the next first-unsolved row is past it. Stops as soon as either
condition is hit.

Usage:
    python scaffold/scripts/phase3_solving/run_until.py <target_ref>

The target_ref must exist in the current chapter's data.json. The script
keeps solving the first unsolved row (the same behavior as plain
solve_chapter), but quits as soon as the target row is solved and the
loop has moved on to a later row.

Used by the user to drive partial solving runs (e.g. "finish section 3.2
+ the first row of 3.3, then stop").
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import _path_setup                                         # noqa: F401, E402

from solve_chapter import (  # noqa: E402
    read_current_chapter,
    find_chapter_data_path,
    load_data,
    solve_current_row,
    first_unsolved_row_index,
)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: run_until.py <target_ref>", file=sys.stderr)
        return 1
    target_ref = argv[1]

    chapter = read_current_chapter()
    data_path = find_chapter_data_path(chapter)

    iteration = 0
    while True:
        iteration += 1
        data = load_data(data_path)
        target_row = next(
            (r for r in data["rows"] if r.get("ref") == target_ref), None
        )
        if target_row is None:
            print(f"[run_until] target ref {target_ref!r} not found in chapter "
                  f"{chapter}; aborting.", flush=True)
            return 2

        try:
            idx = first_unsolved_row_index(data)
        except RuntimeError:
            print("[run_until] chapter complete; nothing left to do.", flush=True)
            return 0

        first_unsolved = data["rows"][idx]
        # Stop condition: target already solved AND first unsolved is past it.
        if (target_row.get("solved") == "yes"
                and first_unsolved["ref"] != target_ref):
            print(f"[run_until] target {target_ref} is solved; first unsolved "
                  f"is now {first_unsolved['ref']} (section "
                  f"{first_unsolved.get('section')}). Stopping as requested.",
                  flush=True)
            return 0

        print(f"\n[run_until] === iteration {iteration}: solving "
              f"{first_unsolved['ref']} (section "
              f"{first_unsolved.get('section')}, "
              f"{first_unsolved.get('def_or_claim')}) ===", flush=True)

        try:
            solve_current_row()
        except Exception as e:  # noqa: BLE001
            print(f"[run_until] solve_current_row raised: {e}", flush=True)
            return 1

        # No-progress safety: stop if the *same* row is still the chapter's
        # first unsolved. Comparing by `ref` so a `reorder` action that
        # bumps this row to a later position still counts as progress.
        data_after = load_data(data_path)
        try:
            idx_after = first_unsolved_row_index(data_after)
        except RuntimeError:
            continue
        new_first_ref = data_after["rows"][idx_after].get("ref")
        if new_first_ref == first_unsolved.get("ref"):
            print(f"[run_until] no progress on {first_unsolved['ref']} "
                  f"(still first unsolved); stopping cleanly.",
                  flush=True)
            return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
