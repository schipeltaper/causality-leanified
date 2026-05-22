#!/usr/bin/env python3
"""find_by_ref.py -- locate the TeX statement and Lean statement(s) for a
given row `ref`.

Usage:
    python extras/find_by_ref.py <ref>

Examples:
    python extras/find_by_ref.py def_3_1
    python extras/find_by_ref.py claim_3_4

The script:
  1. Parses the ref to figure out which chapter it belongs to.
  2. Loads that chapter's `data.json` and finds the row.
  3. Prints the row's TeX statement file (path + contents).
  4. Prints the Lean statement(s), extracted from the row's
     `main_lean_file` (and any other `lean_files`). Proof bodies are
     trimmed -- only the signature up through `:= by` is shown.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEANIFICATION = REPO_ROOT / "leanification"

# A ref looks like `def_3_4` or `claim_5_12`.
REF_RE = re.compile(r"^(def|claim)_(\d+)_(\d+)$")


def find_row(ref: str) -> tuple[Path, dict]:
    """Return (chapter_data_path, row) for the given ref.

    Searches `leanification/Chapter<N>_*/data.json` -- the chapter number is
    parsed out of the ref. Raises ValueError on malformed ref,
    LookupError if no matching row is found.
    """
    m = REF_RE.match(ref)
    if not m:
        raise ValueError(
            f"malformed ref {ref!r}; expected def_<chapter>_<n> or "
            f"claim_<chapter>_<n>"
        )
    chapter = int(m.group(2))
    for child in sorted(LEANIFICATION.iterdir()):
        if not child.is_dir() or not child.name.startswith(f"Chapter{chapter}_"):
            continue
        dp = child / "data.json"
        if not dp.exists():
            continue
        data = json.loads(dp.read_text(encoding="utf-8"))
        for row in data["rows"]:
            if row.get("ref") == ref:
                return dp, row
    raise LookupError(f"ref {ref!r} not found in any chapter's data.json")


def tex_statement_path(data_path: Path, row: dict) -> Path | None:
    """Return the path to the row's TeX *statement* file (not the proof).

    Layout:
      <chapter_folder>/<Section>/tex/def_<X>_<Y>_<title>.tex            (def)
      <chapter_folder>/<Section>/tex/claim_<X>_<Y>_statement_<title>.tex (claim)

    None if the row has no `section` (pre-subsection rows live at the
    chapter root and don't have a per-row tex file).
    """
    section = row.get("section", "")
    if not section:
        return None
    sec_folder = "Section" + section.replace(".", "_")
    title = row.get("title") or "Untitled"
    tex_dir = data_path.parent / sec_folder / "tex"
    if row["def_or_claim"] == "def":
        return tex_dir / f"{row['ref']}_{title}.tex"
    return tex_dir / f"{row['ref']}_statement_{title}.tex"


# A marker line in Lean looks like:
#   -- claim_3_4
#   -- def_3_10
#   -- claim_3_1 (part 2/3)
LEAN_REF_MARKER_RE = re.compile(
    r"^--\s+(?P<ref>(?:def|claim)_\d+_\d+)(?:\s+\(part\s+\d+/\d+\))?\s*$"
)

# Lines that open a Lean declaration.
DECL_OPENER_RE = re.compile(
    r"^(theorem|lemma|example|def|abbrev|structure|class|instance|inductive)\b"
)
# Body-opener for theorem/lemma/example: the `:= by` (or `:= by ...`) line
# that starts the proof.  We keep this line in the extracted statement so
# the reader can see "...and here is where the proof begins".
PROOF_OPENER_RE = re.compile(r":=\s*by(\s|$)")


def extract_lean_statement(lean_path: Path, ref: str) -> list[tuple[int, list[str]]]:
    """Find every `-- <ref>` block in ``lean_path`` and extract the
    *statement* portion. Returns one (start_line, lines) pair per block
    (a multi-part claim has several).

    Heuristic for "statement":
      - the block starts at the `-- <ref>` marker line;
      - it ends at the next marker line (any ref) or EOF;
      - within that, for theorem/lemma/example declarations, the proof
        body is trimmed -- we keep the line containing `:= by` and drop
        the tactic lines after it.
    """
    lines = lean_path.read_text(encoding="utf-8").splitlines()
    markers: list[tuple[int, str]] = []
    for i, ln in enumerate(lines):
        m = LEAN_REF_MARKER_RE.match(ln)
        if m:
            markers.append((i, m.group("ref")))
    blocks: list[tuple[int, list[str]]] = []
    for idx, (start, mref) in enumerate(markers):
        if mref != ref:
            continue
        end = markers[idx + 1][0] if idx + 1 < len(markers) else len(lines)
        block = lines[start:end]
        cut = len(block)
        is_thm = False
        for j, ln in enumerate(block):
            m_decl = DECL_OPENER_RE.match(ln)
            if m_decl:
                kind = m_decl.group(1)
                is_thm = kind in {"theorem", "lemma", "example"}
                if not is_thm:
                    break       # structure/def/etc: keep the whole block
            if is_thm and PROOF_OPENER_RE.search(ln):
                cut = j + 1     # keep `:= by`, drop the tactics
                break
        # Strip trailing blank lines for tidier output.
        while cut > 0 and not block[cut - 1].strip():
            cut -= 1
        blocks.append((start + 1, block[:cut]))   # 1-indexed start line
    return blocks


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: find_by_ref.py <ref>   (e.g. claim_3_4)", file=sys.stderr)
        return 1
    ref = argv[1]
    try:
        data_path, row = find_row(ref)
    except (ValueError, LookupError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    print(f"# ref: {ref}")
    print(f"  title:   {row.get('title')}")
    print(f"  section: {row.get('section')}")
    print(f"  type:    {row.get('type')}  ({row.get('def_or_claim')})")
    print(f"  solved:  {row.get('solved')}")
    print()

    # ---- LaTeX statement ---------------------------------------------------
    tex = tex_statement_path(data_path, row)
    print("## TeX statement file")
    if tex is None:
        print("  (row has no section; no per-row tex file)")
    elif not tex.exists():
        print(f"  {tex.relative_to(REPO_ROOT)}  (MISSING -- row may be unsolved)")
    else:
        print(f"  path: {tex.relative_to(REPO_ROOT)}")
        print("  ---")
        for ln in tex.read_text(encoding="utf-8").splitlines():
            print(f"  {ln}")
    print()

    # ---- Lean statement ----------------------------------------------------
    print("## Lean statement(s)")
    lean_files = row.get("lean_files") or []
    main_lean = row.get("main_lean_file")
    seen: set[str] = set()
    ordered: list[str] = []
    for lf in ([main_lean] if main_lean else []) + lean_files:
        if lf and lf not in seen:
            seen.add(lf)
            ordered.append(lf)
    if not ordered:
        print("  (no lean_files recorded -- row likely unsolved)")
        return 0
    for lf in ordered:
        lp = REPO_ROOT / lf
        if not lp.exists():
            print(f"  {lf}: MISSING")
            continue
        blocks = extract_lean_statement(lp, ref)
        if not blocks:
            print(f"  {lf}: no `-- {ref}` marker found")
            continue
        for start, block in blocks:
            print(f"  --- {lf}:{start} ---")
            for ln in block:
                print(f"  {ln}")
            print()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
