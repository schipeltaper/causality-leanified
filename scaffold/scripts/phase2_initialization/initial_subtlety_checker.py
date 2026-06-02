"""Initial-phase subtlety check.

Given a chapter's ``data.json``, spawns the ``check_ln_wording`` worker
on every row's LN tex block (in order), parses the worker's
``SUBTLETY: ... END_SUBTLETY`` blocks, and appends each one to
``leanification/initial_subtlety_register.json``.

The register is informational. After this script finishes, run
``scaffold/scripts/phase2_initialization/generate_initialization_table.py`` to produce the
human-facing decision table; the human fills in answers per subtlety
(plus any additional global notes); then
``scaffold/scripts/phase2_initialization/process_initialization_table.py`` folds the human's
answers into ``data.json`` under the new ``addition_to_the_LN``
column.

Idempotent: a row that already has its subtleties recorded (matched
by ``observed_by_ref`` already present in the register) is skipped on
re-run. Pass ``--force`` to re-check every row.

Usage::

    python scaffold/scripts/phase2_initialization/initial_subtlety_checker.py --chapter 3
    python scaffold/scripts/phase2_initialization/initial_subtlety_checker.py --chapter 3 --force
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
WORDING_CHECK_PROMPT = (SCAFFOLD_DIR / "claude_prompts"
                        / "phase2_initialization" / "check_ln_wording.md")

# Make sibling phase folders + utils/ importable.
sys.path.insert(0, str(SCRIPT_DIR.parent))
import _path_setup                                                # noqa: F401, E402

from subtlety_register import (                                  # noqa: E402
    load_register, register_subtlety, mangle_id,
)
from solve_chapter import read_tex_block, run_claude             # noqa: E402


_SUBTLETY_RE = re.compile(
    r"SUBTLETY:\s*\n"
    r"\s*id\s*:\s*(?P<id>\S+)\s*\n"
    r"\s*explanation\s*:\s*(?P<expl>.*?)\n\s*END_SUBTLETY",
    re.DOTALL | re.IGNORECASE,
)


def _find_chapter_data(chapter: int) -> Path:
    """Locate ``leanification/Chapter{N}_*/data.json`` for the given chapter."""
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            dj = child / "data.json"
            if dj.exists():
                return dj
    raise FileNotFoundError(
        f"no leanification folder + data.json for chapter {chapter}")


def _parse_worker_output(text: str) -> list[dict]:
    """Pull every (id, explanation) pair out of the worker's response."""
    entries: list[dict] = []
    for m in _SUBTLETY_RE.finditer(text):
        entries.append({
            "id":          m.group("id").strip(),
            "explanation": m.group("expl").strip(),
        })
    return entries


def _row_already_processed(ref: str) -> bool:
    """A row is "already processed" if any existing entry was observed
    by it. Used for idempotent re-runs without --force."""
    return any(
        e.get("observed_by_ref") == ref
        for e in load_register("initial")
    )


def _check_one_row(row: dict, prompt_body: str) -> int:
    """Run the wording-check worker on a single row, write any results
    to the initial register. Returns the number of new entries written."""
    ref = row["ref"]
    try:
        tex_block = read_tex_block(row["tex_file"], ref)
    except Exception as e:                                       # noqa: BLE001
        print(f"  [{ref}] could not read tex_block ({e}); skipping",
              file=sys.stderr)
        return 0
    prompt = (
        f"{prompt_body}\n\n"
        f"## Current row\n"
        f"- ref: {ref}\n"
        f"- kind: {row.get('def_or_claim', '?')}\n"
        f"- title: {row.get('title', '')}\n"
        f"- tex_file: {row.get('tex_file', '?')}\n"
        f"\n## Tex block to audit\n"
        f"```latex\n{tex_block}\n```\n"
    )
    print(f"  [{ref}] running wording check ...", file=sys.stderr, flush=True)
    text, _sess = run_claude(prompt, label=f"initial_wording_check_{ref}")
    entries = _parse_worker_output(text)
    if not entries:
        # Either NO_SUBTLETIES or the worker failed to use the format.
        # Either way nothing to write.
        if "NO_SUBTLETIES" in text:
            print(f"    -> NO_SUBTLETIES", file=sys.stderr)
        else:
            print(f"    -> no parseable SUBTLETY blocks in worker output "
                  f"({len(text)} chars)", file=sys.stderr)
        return 0
    written = 0
    for entry in entries:
        entry["observed_by_ref"] = ref
        proposed_id = entry["id"]
        # Auto-mangle on collision (init phase is non-interactive --
        # no nudge cycle; just keep a stable history).
        final_id = mangle_id("initial", proposed_id)
        if final_id != proposed_id:
            print(f"    -> id collision: {proposed_id!r} -> {final_id!r}",
                  file=sys.stderr)
        entry["id"] = final_id
        try:
            register_subtlety("initial", entry)
            written += 1
            print(f"    -> registered {final_id!r}", file=sys.stderr)
        except (ValueError, KeyError) as e:
            print(f"    -> WARNING: failed to register {final_id!r}: {e}",
                  file=sys.stderr)
    return written


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Run the LN wording-check worker on every row of a "
                    "chapter's data.json; collect subtleties into the "
                    "initial_subtlety_register.")
    parser.add_argument("--chapter", type=int, required=True,
                        help="chapter number, e.g. 3")
    parser.add_argument("--force", action="store_true",
                        help="re-check every row, even those whose subtleties "
                             "are already on file")
    parser.add_argument("--only-refs", type=str, default="",
                        help="optional comma-separated list of refs to check "
                             "(default: every row)")
    args = parser.parse_args(argv)

    data_path = _find_chapter_data(args.chapter)
    data = json.loads(data_path.read_text(encoding="utf-8"))
    rows = data.get("rows", [])
    if not rows:
        print(f"ERROR: chapter {args.chapter} has no rows in data.json",
              file=sys.stderr)
        return 1

    only_refs = {r.strip() for r in args.only_refs.split(",") if r.strip()}

    worker_path = WORDING_CHECK_PROMPT
    if not worker_path.exists():
        print(f"ERROR: worker prompt missing: {worker_path}",
              file=sys.stderr)
        return 1
    prompt_body = worker_path.read_text(encoding="utf-8")

    print(f"[initial_subtlety_checker] chapter={args.chapter}, "
          f"{len(rows)} row(s), force={args.force}",
          file=sys.stderr, flush=True)
    total_written = 0
    total_skipped = 0
    for row in rows:
        ref = row.get("ref")
        if not ref:
            continue
        if only_refs and ref not in only_refs:
            continue
        if not args.force and _row_already_processed(ref):
            print(f"  [{ref}] already processed; skipping (pass --force "
                  f"to re-check)", file=sys.stderr)
            total_skipped += 1
            continue
        n = _check_one_row(row, prompt_body)
        total_written += n

    print(f"\n[initial_subtlety_checker] done: {total_written} new "
          f"entry(s) written, {total_skipped} row(s) skipped (already "
          f"processed). Next step: review the entries via\n"
          f"  python scaffold/scripts/utils/subtlety_register.py initial\n"
          f"then generate the human-decision table with\n"
          f"  python scaffold/scripts/phase2_initialization/generate_initialization_table.py "
          f"--chapter {args.chapter}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
