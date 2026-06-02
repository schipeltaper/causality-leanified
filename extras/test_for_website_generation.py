#!/usr/bin/env python3
"""Exercise the `produce_for_website` worker on a single row, without
touching the running orchestrator.

Usage:
    python extras/test_for_website_generation.py <chapter> <row_index>

Example:
    python extras/test_for_website_generation.py 3 0    # first row of chapter 3 (def_3_1)
    python extras/test_for_website_generation.py 3 1    # second row (def_3_2)

The script:
  1. Loads ``leanification/Chapter<N>_*/data.json``.
  2. Picks the row at the given index.
  3. Builds the worker prompt via ``build_for_website_prompt``.
  4. Spawns ``claude -p`` (via ``run_claude``) -- *not* a sub-shell of the
     orchestrator, so this is safe to run while solve_chapter is paused.
  5. Verifies the JSON file landed at
     ``leanification/.../tex/<ref>_for_website.json``.
  6. Pretty-prints the resulting fields so you can eyeball quality.

Test runs deliberately set ``register_on_row=False`` so the row's
agent_registry isn't polluted by a one-off test session.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scaffold" / "scripts"))
import _path_setup                                       # noqa: F401, E402

from solve_chapter import (                             # type: ignore  # noqa: E402
    find_chapter_data_path,
    load_data,
    ensure_subsection_folder,
    run_for_website_worker,
)


def _pretty_print(out_path: Path) -> None:
    """Render the JSON's structure + first chunk of every field so a
    human can sanity-check the worker output."""
    with out_path.open(encoding="utf-8") as fh:
        d = json.load(fh)
    print(f"\n=== {out_path.relative_to(Path('/home/11716061/repo_scaffold2'))} ===")
    for k in ("ref", "title", "type", "def_or_claim", "section",
              "lean_file_path"):
        print(f"  {k}: {d.get(k)!r}")
    # Code panels
    for k in ("lean_code_with_comments", "lean_code_without_comments"):
        v = d.get(k, "") or ""
        n_lines = len(v.splitlines())
        print(f"  {k}: {len(v)} chars, {n_lines} lines; first 200:")
        print("    " + (v[:200].replace("\n", "\n    ") or "(empty)"))
    # Prose
    for k in ("lean_explanation", "design_choices"):
        v = d.get(k, "") or ""
        print(f"  {k}: {len(v)} chars; first 200:")
        print("    " + (v[:200].replace("\n", "\n    ") or "(empty)"))
    # URL list
    urls = d.get("lean_source_urls")
    if isinstance(urls, list):
        print(f"  lean_source_urls: list with {len(urls)} entry/-ies")
        for i, u in enumerate(urls):
            if isinstance(u, dict):
                print(f"    [{i}] {u.get('title')!r} -> {u.get('url')}")
            else:
                print(f"    [{i}] (malformed) {u!r}")
    else:
        print(f"  lean_source_urls: NOT A LIST -- got {type(urls).__name__}")


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print("usage: test_for_website_generation.py <chapter> <row_index>",
              file=sys.stderr)
        return 1
    try:
        chapter = int(argv[1])
        row_index = int(argv[2])
    except ValueError:
        print("chapter and row_index must be integers", file=sys.stderr)
        return 1

    data_path = find_chapter_data_path(chapter)
    data = load_data(data_path)
    if not (0 <= row_index < len(data["rows"])):
        print(f"row_index {row_index} out of range; chapter {chapter} has "
              f"{len(data['rows'])} rows.", file=sys.stderr)
        return 2
    row = data["rows"][row_index]
    section = row.get("section")
    if not section:
        print(f"row {row.get('ref')} has no section; nowhere to write the "
              f"JSON.", file=sys.stderr)
        return 2

    ss = ensure_subsection_folder(data_path.parent, section)
    out_path = ss / "tex" / f"{row['ref']}_for_website.json"

    print(f"[test] dispatching for_website worker for {row['ref']} "
          f"({row.get('title')}, section {section}, "
          f"def_or_claim={row.get('def_or_claim')})", flush=True)
    print(f"[test] expected output: {out_path}", flush=True)

    run_for_website_worker(row, ss, register_on_row=False)

    if out_path.exists():
        _pretty_print(out_path)
        return 0
    print(f"[test] FAILED: {out_path} was not produced.", file=sys.stderr)
    return 3


if __name__ == "__main__":
    sys.exit(main(sys.argv))
