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

----------------------------------------------------------------------
SAFE STOP SIGNAL — operators driving via a monitor / live tail
----------------------------------------------------------------------

After each iteration's ``solve_current_row()`` returns, this driver emits:

    [run_until] === iteration <N> complete: <ref> ... — safe to stop now ===

That line is the **only guaranteed safe point** to interrupt a
``run_until.py`` batch. By the time it prints, the orchestrator has:

  - written ``solved=yes`` to data.json (if applicable),
  - regenerated the chapter aggregator + section main.tex,
  - cleaned the row's workspace + agent_registry,
  - compiled the row's tex files,
  - dispatched the for_website worker,
  - flushed data.json + time tracker,
  - run ``build_and_commit.sh`` (lake build → git commit → git push),

so no Lean / tex / git operation is in-flight. Killing here is clean.

The earlier ``[orchestrator] <ref> marked solved (...)`` log line is
NOT a safe stop point — ``commit_solved_row`` runs *after* it. A
SIGPIPE / kill caught between "marked solved" and the
"iteration complete" line will interrupt the commit step, leaving
``data.json`` updated but the row uncommitted (recoverable by re-
running ``scaffold/build_and_commit.sh "<message>"`` once).
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

        # Safe-to-stop signal — see the module docstring at the top of this
        # file for the rationale. By the time this prints, the orchestrator's
        # commit_solved_row has either succeeded or fully failed-and-logged;
        # no subprocess is in flight and the working tree is in a known state.
        print(f"[run_until] === iteration {iteration} complete: "
              f"{first_unsolved['ref']} (section "
              f"{first_unsolved.get('section')}, "
              f"{first_unsolved.get('def_or_claim')}) — safe to stop now ===",
              flush=True)

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
