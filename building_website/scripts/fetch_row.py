#!/usr/bin/env python3
"""Fetch all rendering inputs for one row of a chapter's data.json.

Given a ref (e.g. `def_3_1`, `claim_3_4`), this script locates:

  1. the row in `leanification/Chapter*/data.json`,
  2. the row's per-row TeX statement file (and proof file for claims),
  3. every Lean block tagged with the ref's marker comments,

and emits a single JSON file that the website consumes. The shape:

    {
      "ref":         "def_3_1",
      "kind":        "def",                    # "def" | "claim"
      "section":     "3.1",
      "title":       "CDMG",
      "type":        "definition",
      "status": {
        "formalized": "yes",
        "proven":     "n/a",
        "solved":     "yes"
      },

      "tex_statement": {
        "raw":     "<verbatim TeX body>",      # body of \\begin{Def}…\\end{Def}
        "html":    "<HTML rendering>",         # ready for KaTeX
        "env":     "Def",
        "env_title": "Conditional directed mixed graphs (CDMG)",
        "source_path": "leanification/.../def_3_1_CDMG.tex"
      },

      "tex_proof": null | {                    # claims only
        "raw":  "...",
        "html": "...",
        "source_path": "..."
      },

      "lean": [                                # one entry per part
        {
          "part":      null | "1/3",           # multi-part claims only
          "title":     "CDMG",
          "comments":  "<rich `--`-prefixed comment block above the decl>",
          "statement": "structure CDMG (α : Type*) where ...",
          "proof":     null | "have h ...\\n  ...",
          "source_path": "leanification/.../CDMG.lean",
          "source_line": 119
        },
        ...
      ]
    }

Usage:

    python3 building_website/scripts/fetch_row.py def_3_1
    python3 building_website/scripts/fetch_row.py claim_3_4 --out tmp.json
    python3 building_website/scripts/fetch_row.py def_3_1 --stdout

The default output path is
`building_website/website/data/<ref>.json`.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Make the scripts/ folder importable when run as `python3 fetch_row.py`.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from tex_to_html import tex_to_html, tex_body_to_html  # noqa: E402


REPO_ROOT = Path(__file__).resolve().parents[2]
WEBSITE_DATA = REPO_ROOT / "building_website" / "website" / "data"
REF_RE = re.compile(r"^(def|claim)_(\d+)_(\d+)$")


# --------------------------------------------------------------------------- #
#  data.json lookup                                                           #
# --------------------------------------------------------------------------- #

def find_row(ref: str) -> tuple[Path, dict]:
    """Locate the row across every chapter's data.json. Returns (path, row)."""
    if not REF_RE.match(ref):
        sys.exit(
            f"error: malformed ref {ref!r}; expected def_<ch>_<n> or claim_<ch>_<n>"
        )
    for data_path in sorted((REPO_ROOT / "leanification").glob("Chapter*/data.json")):
        data = json.loads(data_path.read_text(encoding="utf-8"))
        for row in data.get("rows", []):
            if row.get("ref") == ref:
                return data_path, row
    sys.exit(f"error: ref {ref!r} not found in any chapter's data.json")


# --------------------------------------------------------------------------- #
#  TeX file paths                                                             #
# --------------------------------------------------------------------------- #

def _section_folder(section: str) -> str:
    return "Section" + section.replace(".", "_")


def tex_statement_path(data_path: Path, row: dict) -> Path:
    """Return the absolute path of the per-row TeX statement file."""
    chapter_dir = data_path.parent
    sec_dir = chapter_dir / _section_folder(row["section"]) / "tex"
    ref, title = row["ref"], row["title"]
    if row["def_or_claim"] == "def":
        return sec_dir / f"{ref}_{title}.tex"
    return sec_dir / f"{ref}_statement_{title}.tex"


def tex_proof_path(data_path: Path, row: dict) -> Path | None:
    """Claims have a separate proof TeX file; defs don't."""
    if row["def_or_claim"] != "claim":
        return None
    chapter_dir = data_path.parent
    sec_dir = chapter_dir / _section_folder(row["section"]) / "tex"
    return sec_dir / f"{row['ref']}_proof_{row['title']}.tex"


# --------------------------------------------------------------------------- #
#  Lean extraction                                                            #
# --------------------------------------------------------------------------- #

# Ref-marker comments at column 0. Examples:
#   "-- def_3_1"
#   "-- claim_3_1 (part 2/3)"
LEAN_MARKER_RE = re.compile(
    r"^--\s+(?P<ref>(def|claim)_\d+_\d+)(?:\s+\(part\s+(?P<part>\d+/\d+)\))?\s*$"
)
LEAN_TITLE_RE = re.compile(r"^--\s+title:\s*(?P<title>.+?)\s*$")
LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+|protected\s+|private\s+)?"
    r"(structure|def|abbrev|class|instance|inductive|theorem|lemma|example)\b"
)


def _slice_blocks(lines: list[str], target_ref: str) -> list[tuple[int, list[str]]]:
    """Walk a Lean file and slice the section attached to each marker matching
    `target_ref`. A section spans from the marker line up to (but not
    including) the next marker for any ref, or end-of-file, or a top-level
    `end` line (defensive)."""
    markers: list[tuple[int, str | None]] = []  # (line_idx, part or None)
    for i, line in enumerate(lines):
        m = LEAN_MARKER_RE.match(line)
        if m and m.group("ref") == target_ref:
            markers.append((i, m.group("part")))
        elif m:
            markers.append((i, None))  # other-ref marker, used only for boundaries

    # Sort by line and walk; for each target-ref marker, find the next marker
    # (of any ref) to bound the block.
    all_markers = sorted({i for i, _ in markers})
    blocks: list[tuple[int, list[str]]] = []
    for i, part in markers:
        if part is None:
            continue
        # 'part' is set only for target-ref markers in our tagging above
        # (mis-modelled — fix: re-detect target match).
        pass

    # Re-derive cleanly:
    blocks = []
    target_markers = []
    other_markers = []
    for i, line in enumerate(lines):
        m = LEAN_MARKER_RE.match(line)
        if not m:
            continue
        (target_markers if m.group("ref") == target_ref else other_markers).append(i)
    all_marker_lines = sorted(set(target_markers + other_markers))
    for start in target_markers:
        end_candidates = [j for j in all_marker_lines if j > start]
        end = end_candidates[0] if end_candidates else len(lines)
        blocks.append((start, lines[start:end]))
    return blocks


def _split_block(block_lines: list[str]) -> dict:
    """Given a Lean block starting at a marker, split it into the four
    pieces the website renders: title, comments, statement, proof."""
    title = None
    # Drill until we find the declaration line.
    comment_lines: list[str] = []
    decl_start: int | None = None
    for i, line in enumerate(block_lines):
        if i == 0 and LEAN_MARKER_RE.match(line):
            continue  # skip the marker line itself
        t = LEAN_TITLE_RE.match(line)
        if t:
            title = t.group("title")
            continue
        if LEAN_DECL_RE.match(line):
            decl_start = i
            break
        comment_lines.append(line)
    if decl_start is None:
        # No declaration found — return the whole block as comments.
        return {
            "title": title,
            "comments": "\n".join(comment_lines).rstrip(),
            "statement": "",
            "proof": None,
        }

    # Statement / proof split. For theorem/lemma/example, the proof body is
    # everything after the first ":= by" or ":=" (term-mode). For
    # structure/def/abbrev/class/instance/inductive, there is no proof — keep
    # the whole block as the statement.
    kind_match = LEAN_DECL_RE.match(block_lines[decl_start])
    kind = kind_match.group(1) if kind_match else ""
    body = block_lines[decl_start:]

    # Drop trailing `end <ns>` lines and blank lines — they belong to the file
    # epilogue, not to this declaration.
    while body and re.match(r"^\s*(end\b|$)", body[-1]):
        body.pop()

    if kind in {"theorem", "lemma", "example"}:
        joined = "\n".join(body)
        m = re.search(r":=\s*(by\b)?", joined)
        if m:
            statement = joined[: m.end()]
            proof_text = joined[m.end():]
            # Trim leading newline of proof and remove trailing whitespace.
            proof = proof_text.lstrip("\n").rstrip() or None
            statement_text = statement.rstrip()
        else:
            statement_text = joined.rstrip()
            proof = None
    else:
        statement_text = "\n".join(body).rstrip()
        proof = None

    return {
        "title": title,
        "comments": "\n".join(comment_lines).rstrip(),
        "statement": statement_text,
        "proof": proof,
    }


def extract_lean(lean_paths: list[Path], ref: str) -> list[dict]:
    """Walk every lean file, collect every block tagged with `ref`."""
    out: list[dict] = []
    seen: set[tuple[str, int]] = set()
    for p in lean_paths:
        if not p.exists():
            continue
        text = p.read_text(encoding="utf-8")
        lines = text.splitlines()
        for start_idx, block in _slice_blocks(lines, ref):
            key = (str(p), start_idx)
            if key in seen:
                continue
            seen.add(key)
            split = _split_block(block)
            # Extract `(part N/M)` from the marker line for ordering.
            m = LEAN_MARKER_RE.match(block[0])
            part = m.group("part") if m else None
            out.append(
                {
                    "part": part,
                    "title": split["title"],
                    "comments": split["comments"],
                    "statement": split["statement"],
                    "proof": split["proof"],
                    "source_path": str(p.relative_to(REPO_ROOT)),
                    "source_line": start_idx + 1,
                }
            )
    # Stable order: by source_path then by source_line.
    out.sort(key=lambda b: (b["source_path"], b["source_line"]))
    return out


# --------------------------------------------------------------------------- #
#  Assemble                                                                   #
# --------------------------------------------------------------------------- #

def fetch_row(ref: str) -> dict:
    data_path, row = find_row(ref)

    # --- TeX statement ---
    tex_stmt_path = tex_statement_path(data_path, row)
    if tex_stmt_path.exists():
        raw = tex_stmt_path.read_text(encoding="utf-8")
        block = tex_to_html(raw)
        tex_statement = {
            "raw": raw,
            "html": block.body_html,
            "env": block.env,
            "env_title": block.title,
            "source_path": str(tex_stmt_path.relative_to(REPO_ROOT)),
        }
    else:
        tex_statement = {
            "raw": None,
            "html": None,
            "env": None,
            "env_title": None,
            "source_path": str(tex_stmt_path.relative_to(REPO_ROOT)),
            "missing": True,
        }

    # --- TeX proof (claims only) ---
    tex_proof = None
    proof_path = tex_proof_path(data_path, row)
    if proof_path is not None and proof_path.exists():
        raw = proof_path.read_text(encoding="utf-8")
        # Strip the outer wrappers and extract just the \begin{proof}…\end{proof}.
        from tex_to_html import strip_subfiles_wrapper  # local import to keep header clean
        stripped = strip_subfiles_wrapper(raw)
        m = re.search(r"\\begin\{proof\}(.*?)\\end\{proof\}", stripped, re.DOTALL)
        proof_body = m.group(1) if m else stripped
        tex_proof = {
            "raw": raw,
            "html": tex_body_to_html(proof_body),
            "source_path": str(proof_path.relative_to(REPO_ROOT)),
        }
    elif proof_path is not None:
        tex_proof = {
            "raw": None,
            "html": None,
            "source_path": str(proof_path.relative_to(REPO_ROOT)),
            "missing": True,
        }

    # --- Lean ---
    lean_rel = [row["main_lean_file"], *row.get("lean_files", [])]
    lean_abs = [REPO_ROOT / p for p in dict.fromkeys(lean_rel)]  # dedup, preserve order
    lean_blocks = extract_lean(lean_abs, ref)

    return {
        "ref": ref,
        "kind": row["def_or_claim"],
        "section": row["section"],
        "title": row["title"],
        "type": row["type"],
        "status": {
            "formalized": row.get("formalized"),
            "proven":     row.get("proven"),
            "solved":     row.get("solved"),
        },
        "tex_statement": tex_statement,
        "tex_proof":     tex_proof,
        "lean":          lean_blocks,
    }


# --------------------------------------------------------------------------- #
#  CLI                                                                         #
# --------------------------------------------------------------------------- #

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
