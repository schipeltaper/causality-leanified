#!/usr/bin/env python3
"""Fetch rendering inputs for one row from its `<ref>_for_website.json`.

Since the website-builder migration (see
`extras/temp_for_website_builder.md`), the orchestrator writes a
per-row JSON at solve-time:

    leanification/Chapter*/Section*/tex/<ref>_for_website.json

carrying the curated Lean statement list and publication-ready prose
(`lean_explanation`, `design_choices`). This script reads that file,
renders the per-row TeX statement/proof through `tex_to_html`, and
emits `building_website/website/data/<ref>.json` for the website.

The Lean side no longer needs walking/marker-parsing/LLM-processing —
`lean_statement` is already the curated, source-ordered list of
`{name, kind, code}`. The TeX side is unchanged: the per-row `.tex`
files under `tex/` are still rendered with `tex_to_html.py`.

Usage:
    python3 building_website/scripts/fetch_row.py def_3_1
    python3 building_website/scripts/fetch_row.py claim_3_4 --stdout
    python3 building_website/scripts/fetch_row.py def_3_1 --out tmp.json

Default output path: building_website/website/data/<ref>.json
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
    """Read a per-row .tex file and render it to HTML.

    `whole_file=False`  → statement file: peel the outer theorem env,
                          return the labelled body (the website renders
                          its own header from `env`/`env_title`).
    `whole_file=True`   → proof file: render the entire stripped body
                          (restated statement env + \\begin{proof}…)."""
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
            f"  (the orchestrator writes it at solve-time; the row may not be\n"
            f"   solved yet, or chapter 3 needs re-running through the worker)"
        )
    fw = json.loads(fw_path.read_text(encoding="utf-8"))
    tex_dir = fw_path.parent          # the section's tex/ folder
    title   = fw["title"]
    kind    = fw["def_or_claim"]      # "def" | "claim"

    # --- TeX statement (rendered via tex_to_html, unchanged pipeline) ---
    if kind == "def":
        tex_statement = _render_tex(tex_dir / f"{ref}_{title}.tex", whole_file=False)
    else:
        tex_statement = _render_tex(
            tex_dir / f"{ref}_statement_{title}.tex", whole_file=False
        )

    # --- TeX proof (claims only) — the whole proof file is rendered ---
    tex_proof = None
    if kind == "claim":
        tex_proof = _render_tex(
            tex_dir / f"{ref}_proof_{title}.tex", whole_file=True
        )

    # --- Status. `<ref>_for_website.json` only exists for SOLVED rows, so
    #     a definition is "formalised, no proof" and a claim is
    #     "formalised, proven". No data.json lookup needed. ---
    status = {
        "formalized": "yes",
        "proven":     "yes" if kind == "claim" else "n/a",
        "solved":     "yes",
    }

    return {
        "ref":              fw["ref"],
        "kind":             kind,
        "section":          fw["section"],
        "title":            title,
        "type":             fw["type"],
        "status":           status,
        "tex_statement":    tex_statement,
        "tex_proof":        tex_proof,
        # `lean` is the curated per-part list straight from the
        # orchestrator: one {name, kind, code} object per LN-level
        # sub-statement, in source order, helpers already filtered.
        "lean":             fw["lean_statement"],
        "lean_file_path":   fw["lean_file_path"],
        "lean_explanation": fw["lean_explanation"],
        "design_choices":   fw["design_choices"],
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
