"""Generate the human-decision table for the initialization phase.

Reads ``leanification/initial_subtlety_register.json`` and writes a
markdown table at
``leanification/Chapter{N}_*/initialization_table.md``. For each
subtlety the human is asked to decide: should the LN encoding adopt
an additional clarification / constraint when this row is formalized?
If yes, write the addition. If no, mark it as "no addition needed".

The table ends with an **"Additional notes (global)"** section where
the human can add any project-wide additions to the LN that don't
correspond to a specific subtlety -- e.g. "every CDMG is assumed to
have a finite vertex set". These are merged into every row's
``addition_to_the_LN`` field when the table is processed.

Workflow position::

    initialize_chapter --> initial_subtlety_checker --> generate_initialization_table
        --> [HUMAN fills in the table] --> process_initialization_table --> data.json

Usage::

    python scaffold/scripts/phase2_initialization/generate_initialization_table.py --chapter 3
"""

from __future__ import annotations

import argparse
import json
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


HEADER = """\
# Initialization decision table — Chapter {chapter}

**Date generated:** {today}
**Source register:** `leanification/initial_subtlety_register.json` \
({n_entries} entry/entries)

Each row below corresponds to one subtlety the `check_ln_wording`
worker surfaced. For each, fill in the **Decision** column with one of:

- `NONE` — no addition to the LN needed. The formalizer should treat
  the literal LN reading as authoritative.
- A free-form clarifying clause that should be appended to the LN's
  meaning when this row (and any downstream row that depends on it)
  is formalized. The clause is a *strengthening or disambiguation* of
  the LN -- it is conjoined with the literal reading. Be precise; the
  equivalence-checker workers will treat your text as authoritative.

Examples of useful additions:

> "Only bidirected hinges count; backward-E edges as n=1 bifurcations \
are excluded."

> "A bifurcation between v and w requires both endnodes to have \
exactly one arrowhead pointing toward them (this rules out the \
degenerate n=1 backward-E case)."

> "L is treated as a symmetric subset of `V × V` with the irreflexivity \
constraint, not as a quotient set."

When done, save the file and run::

    python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter {chapter}

"""

ADDITIONAL_NOTES_SECTION = """\
---

## Additional notes (global)

Anything below the next heading is treated as a **global** addition
to the LN -- merged into every row's `addition_to_the_LN` field
(prefixed with `[global]`). Use this for project-wide assumptions
that don't correspond to a specific subtlety -- e.g. "every CDMG is
assumed to have a finite vertex set", or "interventions are always
hard interventions unless otherwise specified".

Format: write one assumption per paragraph. Leave the section empty
if no global additions apply.

### Notes

<!-- write your global LN additions below this line; one paragraph per assumption -->


"""


def _find_chapter_folder(chapter: int) -> Path:
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child
    raise FileNotFoundError(
        f"no leanification folder for chapter {chapter}")


def _format_entry(idx: int, entry: dict) -> str:
    """Render one entry as a markdown subsection with a Decision field."""
    return (
        f"### {idx}. `{entry.get('id', '?')}`\n\n"
        f"- **Observed by row:** `{entry.get('observed_by_ref', '?')}`\n\n"
        f"**Explanation (from the wording-check worker):**\n\n"
        f"{entry.get('explanation', '').strip()}\n\n"
        f"**Decision** (replace `TODO` with `NONE` or your clarifying clause):\n\n"
        f"```\nTODO\n```\n"
    )


def main(argv: list[str]) -> int:
    from datetime import datetime, timezone
    parser = argparse.ArgumentParser(
        description="Generate the per-chapter initialization decision "
                    "table from the initial subtlety register.")
    parser.add_argument("--chapter", type=int, required=True,
                        help="chapter number, e.g. 3")
    parser.add_argument("--overwrite", action="store_true",
                        help="overwrite an existing initialization_table.md")
    args = parser.parse_args(argv)

    chapter_folder = _find_chapter_folder(args.chapter)
    out_path = chapter_folder / "initialization_table.md"
    if out_path.exists() and not args.overwrite:
        print(f"ERROR: {out_path} already exists. Pass --overwrite to "
              f"replace it (your prior decisions will be lost).",
              file=sys.stderr)
        return 1

    entries = load_register("initial")
    # Filter to entries observed by rows that live in this chapter. We
    # could be more precise (require the row's chapter to match), but
    # in practice the initial_subtlety_checker is run per-chapter, so
    # all entries are this chapter's.
    print(f"[generate_initialization_table] chapter={args.chapter}, "
          f"{len(entries)} entry(s) in initial register",
          file=sys.stderr)

    body_parts: list[str] = [
        HEADER.format(
            chapter=args.chapter,
            today=datetime.now(timezone.utc).date().isoformat(),
            n_entries=len(entries),
        )
    ]
    if not entries:
        body_parts.append(
            "_No subtleties were registered. The table is empty; you may "
            "still fill in global additional notes below._\n\n"
        )
    else:
        for idx, entry in enumerate(entries, start=1):
            body_parts.append(_format_entry(idx, entry))
            body_parts.append("\n")
    body_parts.append(ADDITIONAL_NOTES_SECTION)

    out_path.write_text("".join(body_parts), encoding="utf-8")
    print(f"[generate_initialization_table] wrote {out_path}",
          file=sys.stderr)
    print(f"\nNext step: open {out_path.relative_to(REPO_ROOT)} in your "
          f"editor, replace each `TODO` with `NONE` or your clarifying "
          f"clause, add any global notes at the end, save, and run\n"
          f"  python scaffold/scripts/phase2_initialization/process_initialization_table.py "
          f"--chapter {args.chapter}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
