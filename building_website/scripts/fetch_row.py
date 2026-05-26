#!/usr/bin/env python3
"""Fetch rendering inputs for one row from its `<ref>_for_website.json`.

The orchestrator's worker writes a per-row JSON at solve-time (see
`temp_website_builder_handoff.md` at repo root). The v3 schema this
script consumes:

  ref, title, type, def_or_claim, section,
  lean_file_path,
  lean_code_with_comments,      ← Lean code (comments preserved)
  lean_code_without_comments,   ← same code, comments stripped (toggle)
  lean_explanation,             ← polished Markdown article
  design_choices,               ← polished Markdown article
  lean_source_urls              ← [{"title": "X.lean", "url": "github…#Lxxx-Lyyy"}]

This script:
  1. reads `<ref>_for_website.json`,
  2. renders the sibling per-row `.tex` files through `tex_to_html.py`,
  3. derives status (the JSON only exists for solved rows),
  4. writes `building_website/website/data/<ref>.json`.

A row whose JSON is still on an older schema (no
`lean_code_with_comments` field) is reported and skipped.

Usage:
    python3 building_website/scripts/fetch_row.py def_3_1
    python3 building_website/scripts/fetch_row.py claim_3_4 --stdout
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Make the scripts/ folder importable when run as `python3 fetch_row.py`.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from tex_to_html import tex_to_html, tex_body_to_html, strip_subfiles_wrapper  # noqa: E402


REPO_ROOT    = Path(__file__).resolve().parents[2]
WEBSITE_DATA = REPO_ROOT / "building_website" / "website" / "data"
REF_RE       = re.compile(r"^(def|claim)_(\d+)_(\d+)$")


def find_for_website(ref: str) -> Path | None:
    """Locate `<ref>_for_website.json` under leanification/."""
    matches = sorted(
        (REPO_ROOT / "leanification").glob(
            f"Chapter*/Section*/tex/{ref}_for_website.json"
        )
    )
    return matches[0] if matches else None


def _render_tex(path: Path, *, whole_file: bool):
    """Render a per-row .tex file to HTML.

    `whole_file=False`  → statement file: peel the outer theorem env.
    `whole_file=True`   → proof file: render the whole stripped body."""
    if not path.exists():
        return {
            "raw": None, "html": None, "env": None, "env_title": None,
            "source_path": str(path.relative_to(REPO_ROOT)), "missing": True,
        }
    raw = path.read_text(encoding="utf-8")
    if whole_file:
        return {
            "raw": raw,
            "html": tex_body_to_html(strip_subfiles_wrapper(raw)),
            "source_path": str(path.relative_to(REPO_ROOT)),
        }
    block = tex_to_html(raw)
    return {
        "raw": raw,
        "html": block.body_html,
        "env": block.env,
        "env_title": block.title,
        "source_path": str(path.relative_to(REPO_ROOT)),
    }


def fetch_row(ref: str) -> dict:
    if not REF_RE.match(ref):
        sys.exit(f"error: malformed ref {ref!r}; expected def_<ch>_<n> or claim_<ch>_<n>")

    fw_path = find_for_website(ref)
    if fw_path is None:
        sys.exit(
            f"error: no <ref>_for_website.json found for {ref!r}\n"
            f"  (row not solved yet, or hasn't been processed by the v3 worker)"
        )
    fw = json.loads(fw_path.read_text(encoding="utf-8"))

    if "lean_code_with_comments" not in fw:
        sys.exit(
            f"error: {ref}'s for_website JSON is on an older schema "
            f"(no `lean_code_with_comments` field); re-run the v3 worker first"
        )

    tex_dir = fw_path.parent
    title   = fw["title"]
    kind    = fw["def_or_claim"]

    # --- TeX statement / proof (unchanged pipeline) ---
    if kind == "def":
        tex_statement = _render_tex(tex_dir / f"{ref}_{title}.tex", whole_file=False)
    else:
        tex_statement = _render_tex(
            tex_dir / f"{ref}_statement_{title}.tex", whole_file=False
        )

    tex_proof = None
    if kind == "claim":
        tex_proof = _render_tex(
            tex_dir / f"{ref}_proof_{title}.tex", whole_file=True
        )

    status = {
        "formalized": "yes",
        "proven":     "yes" if kind == "claim" else "n/a",
        "solved":     "yes",
    }

    return {
        "ref":                        fw["ref"],
        "kind":                       kind,
        "section":                    fw["section"],
        "title":                      title,
        "type":                       fw["type"],
        "status":                     status,
        "tex_statement":              tex_statement,
        "tex_proof":                  tex_proof,
        "lean_code_with_comments":    fw["lean_code_with_comments"],
        "lean_code_without_comments": fw["lean_code_without_comments"],
        "lean_source_urls":           fw["lean_source_urls"],
        "lean_explanation":           fw["lean_explanation"],
        "design_choices":             fw["design_choices"],
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("ref", help="row identifier, e.g. def_3_1, claim_3_4")
    ap.add_argument("--out", type=Path, help="output JSON path (default: website/data/<ref>.json)")
    ap.add_argument("--stdout", action="store_true", help="print to stdout instead of writing")
    args = ap.parse_args()

    payload = fetch_row(args.ref)
    serialized = json.dumps(payload, indent=2, ensure_ascii=False)

    if args.stdout:
        print(serialized)
        return
    out = args.out or (WEBSITE_DATA / f"{args.ref}.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(serialized + "\n", encoding="utf-8")
    print(f"wrote {out.relative_to(REPO_ROOT)}", file=sys.stderr)


if __name__ == "__main__":
    main()
