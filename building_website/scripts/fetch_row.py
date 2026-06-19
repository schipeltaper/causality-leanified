#!/usr/bin/env python3
"""Fetch rendering inputs for one row, per the recipe in
`temp_for_website_builder.md`.

For a given `ref` (e.g. `def_3_1`):

1. Look up the row in `leanification/Chapter*/data.json`.
2. Render its per-row `.tex` statement (and, for claims, proof) through
   `tex_to_html.py` — unchanged pipeline.
3. Extract the row's Lean code from the `main_lean_file` by slicing
   blocks bracketed with the workers' marker comments:

     -- <ref> -- start statement
     …declaration…
     -- <ref> -- end statement

   and the parallel helper form (three dashes instead of two):

     -- <ref> --- start helper
     …declaration…
     -- <ref> --- end helper

   Multi-item rows have multiple statement blocks; helpers are
   typically in the same file but may live in any of `lean_files`.
4. Emit `building_website/website/data/<ref>.json` with:
     - tex_statement / tex_proof (rendered HTML)
     - lean_code_with_comments    (helpers + main statements, raw)
     - lean_code_without_comments (same, stripped of `--` and `/- -/`)
     - lean_source_url            (GitHub blob URL of `main_lean_file`)
     - lean_file_path             (repo-relative path)
     - addition_to_the_LN         (free-text operator notes)
     - status                     (from data.json's solved/proven)
     - design_choices             (empty; populated by process_design_choices.py)

A row whose `main_lean_file` is empty (not solved yet), or whose Lean
file has no markers for this ref, errors out clearly.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from tex_to_html import tex_to_html, tex_body_to_html, strip_subfiles_wrapper  # noqa: E402

REPO_ROOT    = Path(__file__).resolve().parents[2]
WEBSITE_DATA = REPO_ROOT / "building_website" / "website" / "data"
REPO_URL     = "https://github.com/schipeltaper/causality-leanified"
REPO_BRANCH  = "main"
REF_RE       = re.compile(r"^(def|claim)_(\d+)_(\d+)$")


# --------------------------------------------------------------------------- #
#  data.json lookup                                                           #
# --------------------------------------------------------------------------- #

def find_row(ref: str) -> tuple[dict, Path]:
    """Return (row, chapter_folder) for the given ref. Raises SystemExit
    with a readable message if the ref isn't found."""
    if not REF_RE.match(ref):
        sys.exit(f"error: malformed ref {ref!r}; expected def_<ch>_<n> or claim_<ch>_<n>")
    chapter_n = int(ref.split("_")[1])
    matches = list((REPO_ROOT / "leanification").glob(f"Chapter{chapter_n}_*"))
    if not matches:
        sys.exit(f"error: no leanification/Chapter{chapter_n}_*/ folder found")
    chapter_folder = matches[0]
    data = json.loads((chapter_folder / "data.json").read_text(encoding="utf-8"))
    for row in data.get("rows", []):
        if row.get("ref") == ref:
            return row, chapter_folder
    sys.exit(f"error: ref {ref!r} not in {chapter_folder.name}/data.json")


# --------------------------------------------------------------------------- #
#  TeX paths + rendering                                                      #
# --------------------------------------------------------------------------- #

def _section_folder(chapter_folder: Path, section: str) -> Path:
    return chapter_folder / f"Section{section.replace('.', '_')}"


def tex_statement_path(row: dict, chapter_folder: Path) -> Path:
    sec = _section_folder(chapter_folder, row["section"])
    if row["def_or_claim"] == "def":
        return sec / "tex" / f"{row['ref']}_{row['title']}.tex"
    return sec / "tex" / f"{row['ref']}_statement_{row['title']}.tex"


def tex_proof_path(row: dict, chapter_folder: Path) -> Path | None:
    if row["def_or_claim"] != "claim":
        return None
    sec = _section_folder(chapter_folder, row["section"])
    return sec / "tex" / f"{row['ref']}_proof_{row['title']}.tex"


def _render_tex(path: Path, *, whole_file: bool) -> dict:
    if not path.exists():
        return {
            "raw": None, "html": None, "env": None, "env_title": None,
            "source_path": str(path.relative_to(REPO_ROOT)), "missing": True,
        }
    raw = path.read_text(encoding="utf-8")
    if whole_file:
        return {
            "raw":  raw,
            "html": tex_body_to_html(strip_subfiles_wrapper(raw)),
            "source_path": str(path.relative_to(REPO_ROOT)),
        }
    block = tex_to_html(raw)
    return {
        "raw":  raw,
        "html": block.body_html,
        "env":  block.env,
        "env_title": block.title,
        "source_path": str(path.relative_to(REPO_ROOT)),
    }


# --------------------------------------------------------------------------- #
#  Lean marker extraction                                                     #
# --------------------------------------------------------------------------- #

def _marker_blocks(text: str, ref: str, dashes: str, kind: str) -> list[str]:
    """Return the bodies of every `-- <ref> <dashes> start <kind>` /
    `-- <ref> <dashes> end <kind>` block, in source order. `dashes` is
    "--" (statement) or "---" (helper)."""
    pat = re.compile(
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+" + re.escape(dashes)
        + r"[ \t]+start[ \t]+" + re.escape(kind) + r"[ \t]*\n"
        r"(?P<body>.*?)"
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+" + re.escape(dashes)
        + r"[ \t]+end[ \t]+" + re.escape(kind) + r"[ \t]*$",
        re.DOTALL | re.MULTILINE,
    )
    return [m.group("body").rstrip("\n") for m in pat.finditer(text)]


def extract_lean_statement(lean_path: Path, ref: str) -> list[str]:
    return _marker_blocks(lean_path.read_text(encoding="utf-8"), ref, "--", "statement")


def extract_lean_helpers(lean_path: Path, ref: str) -> list[str]:
    return _marker_blocks(lean_path.read_text(encoding="utf-8"), ref, "---", "helper")


def strip_lean_comments(code: str) -> str:
    """Strip every `--` line comment, `/- … -/` block comment, and
    `/-- … -/` doc-comment from a Lean code blob. Used to populate the
    `lean_code_without_comments` half of the toggle."""
    code = re.sub(r"/-.*?-/", "", code, flags=re.DOTALL)
    code = re.sub(r"(?m)--.*$", "", code)
    # Drop blank lines that the stripping leaves behind so structure
    # bodies don't end up with a blank between every two fields.
    return "\n".join(line for line in code.split("\n") if line.strip())


# --------------------------------------------------------------------------- #
#  Assemble                                                                   #
# --------------------------------------------------------------------------- #

def fetch_row(ref: str) -> dict:
    row, chapter_folder = find_row(ref)

    main_lean_rel = row.get("main_lean_file") or ""
    solved        = (row.get("solved") or "no") == "yes"
    formalized    = (row.get("formalized") or "no") == "yes"
    # "User-forced" row: the operator marked `solved: yes` even though
    # the row was never formalized into Lean (`formalized: no`, no
    # `main_lean_file`).  We still surface the LN-tex statement, but
    # the Lean pane carries a static placeholder string instead of
    # extracted code blocks, and we don't try to render the
    # auto-generated proof stub either.
    user_skipped_formalization = solved and not formalized

    if not user_skipped_formalization:
        if not main_lean_rel:
            sys.exit(
                f"error: {ref}'s data.json row has no `main_lean_file`\n"
                f"  (row is unsolved or final-gate worker hasn't run yet)"
            )
        main_lean_path = REPO_ROOT / main_lean_rel
        if not main_lean_path.exists():
            sys.exit(f"error: main_lean_file does not exist on disk: {main_lean_rel}")
    else:
        main_lean_path = None

    # --- TeX statement / proof — unchanged pipeline ---
    tex_statement = _render_tex(tex_statement_path(row, chapter_folder), whole_file=False)
    tex_proof = None
    if not user_skipped_formalization:
        pp = tex_proof_path(row, chapter_folder)
        if pp is not None:
            tex_proof = _render_tex(pp, whole_file=True)

    # --- Lean code blocks.  Empty for user-skipped rows; otherwise
    #     each marker-wrapped region is one block; `kind` distinguishes
    #     the main statement(s) from helpers. ---
    if user_skipped_formalization:
        lean_blocks: list[dict] = []
    else:
        main_codes = extract_lean_statement(main_lean_path, ref)
        helper_blocks: list[dict] = []
        seen_files: set[str] = set()
        # First: walk the row's declared files (main + `lean_files`).
        for path_rel in [main_lean_rel, *row.get("lean_files", [])]:
            if path_rel in seen_files:
                continue
            seen_files.add(path_rel)
            p = REPO_ROOT / path_rel
            if not p.exists():
                continue
            for code in extract_lean_helpers(p, ref):
                helper_blocks.append({"kind": "helper", "code": code})
        # Then: also scan every other `.lean` file in the same section
        # folder for a helper marker carrying this row's ref.  The marker
        # `-- <ref> --- start helper` is ref-specific, so picking up
        # cross-file helpers this way is safe and explicit (the file
        # author opted in by writing the marker).  Catches helpers the
        # `data.json` row hasn't yet been updated to list — e.g. a
        # `Walk.length` helper for `def_3_6` in `Walks.lean`.
        section_dir = (REPO_ROOT / main_lean_rel).parent
        for p in sorted(section_dir.glob("*.lean")):
            rel = str(p.relative_to(REPO_ROOT))
            if rel in seen_files:
                continue
            seen_files.add(rel)
            for code in extract_lean_helpers(p, ref):
                helper_blocks.append({"kind": "helper", "code": code})

        if not main_codes:
            sys.exit(
                f"error: no `-- {ref} -- start statement` / `-- {ref} -- end statement`\n"
                f"  marker pair found in {main_lean_rel}"
            )

        lean_blocks = helper_blocks + [{"kind": "main", "code": c} for c in main_codes]

    # --- Original LN tex excerpt (row.tex_block in data.json) rendered to
    #     HTML once. The website shows this by default and lets the user
    #     toggle to the orchestrator's unambiguous version. ---
    tex_block_html = ""
    raw_tex_block = (row.get("tex_block") or "").strip()
    if raw_tex_block:
        block = tex_to_html(raw_tex_block)
        tex_block_html = block.body_html

    # --- Source URL: a single link to main_lean_file on the repo.
    #     Empty for user-skipped rows so the website hides the
    #     "View Lean source" button. ---
    if user_skipped_formalization:
        lean_source_url = ""
    else:
        lean_source_url = f"{REPO_URL}/blob/{REPO_BRANCH}/{main_lean_rel}"

    # --- Status, derived from data.json. ---
    status = {
        "formalized": row.get("formalized") or "no",
        "proven":     row.get("proven")     or "n/a",
        "solved":     row.get("solved")     or "no",
    }

    # Preserve previously-generated LLM prose so re-running fetch_row
    # doesn't wipe the LLM-step output. Per-block fields
    # (`explanation`, `code_annotated`) are matched on the block's
    # `code` so a re-formalized row with rearranged blocks just loses
    # the now-stale annotations and we regenerate them.
    prior_dc:    str | None = None
    prior_by_code: dict[str, dict] = {}
    out_path = WEBSITE_DATA / f"{ref}.json"
    if out_path.exists():
        try:
            prior = json.loads(out_path.read_text(encoding="utf-8"))
            prior_dc = prior.get("design_choices")
            for pb in prior.get("lean_blocks") or []:
                if pb.get("code"):
                    prior_by_code[pb["code"]] = pb
        except json.JSONDecodeError:
            pass
    for blk in lean_blocks:
        prev = prior_by_code.get(blk["code"]) or {}
        blk["explanation"]    = prev.get("explanation") or ""
        blk["code_annotated"] = prev.get("code_annotated") or ""

    return {
        "ref":                ref,
        "kind":               row["def_or_claim"],
        "section":            row["section"],
        "title":              row.get("title", ""),
        "type":               row.get("type", ""),
        "status":             status,
        "tex_block_html":     tex_block_html,
        "tex_statement":      tex_statement,
        "tex_proof":          tex_proof,
        "lean_blocks":        lean_blocks,
        "lean_source_url":    lean_source_url,
        "lean_file_path":     ("" if user_skipped_formalization else main_lean_rel),
        "addition_to_the_LN": row.get("addition_to_the_LN", ""),
        "design_choices":     prior_dc or "",
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("ref")
    ap.add_argument("--out", type=Path)
    ap.add_argument("--stdout", action="store_true")
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
