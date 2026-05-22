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

def _item_sort_key(part: str | None) -> tuple:
    """Numeric sort key extracted from the marker's part text.

    Examples of `part` we encounter:

      "item 1"                          → (1, 0)
      "items 2-4"                       → (2, 0)
      "item 6, witness structure"       → (6, 0)
      "part 1/3"                        → (1, 0)
      "part 2/3"                        → (2, 0)
      None / unrecognised               → (inf, 0)   (sorts last)

    Ties on the primary key are broken later by source_path + line, so
    sub-blocks of "item 6" stay in file order."""
    if not part:
        return (float("inf"),)
    m = re.match(r"items?\s+(\d+)", part, re.IGNORECASE)
    if m:
        return (int(m.group(1)),)
    m = re.match(r"part\s+(\d+)\s*/\s*\d+", part, re.IGNORECASE)
    if m:
        return (int(m.group(1)),)
    return (float("inf"),)


# Ref-marker comments at column 0. Examples:
#   "-- def_3_1"
#   "-- claim_3_1 (part 2/3)"
#   "-- def_3_2 (item 1)"
#   "-- def_3_2 (items 2-4) -- the three primitive edge relations"
#   "-- def_3_4 (item 1, length) [helper]"     ← optional visibility tag
# Anything in parens after the ref is captured as `part`; an optional
# `[primary]` / `[helper]` tag right before the end of line controls
# visibility; a trailing `-- …` annotation on the marker line is
# tolerated and discarded.
LEAN_MARKER_RE = re.compile(
    r"^--\s+(?P<ref>(def|claim)_\d+_\d+)"
    r"(?:\s+\((?P<part>[^)]*)\))?"
    r"(?:\s+\[(?P<tag>primary|helper)\])?"
    r"(?:\s+--.*)?"
    r"\s*$"
)
LEAN_TITLE_RE = re.compile(r"^--\s+title:\s*(?P<title>.+?)\s*$")
LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+|protected\s+|private\s+)?"
    r"(structure|def|abbrev|class|instance|inductive|theorem|lemma|example)\b"
)


def strip_lean_comments(code: str) -> str:
    """Remove every Lean comment from a code block.

    Strips `/- … -/` block comments (including doc-comment form `/-- … -/`)
    and trailing `--` line comments, then drops every now-blank line so
    structure bodies don't end up with a blank line between every two
    fields where the doc-comments used to be.

    This is for *display*; the source file is unchanged. Doc-comments
    attached to fields/decls are visually noise next to the rendered
    LaTeX statement, so they go to the website's `comments` channel and
    the LLM-generated explanation panels instead."""
    code = re.sub(r"/-.*?-/", "", code, flags=re.DOTALL)
    code = re.sub(r"(?m)--.*$", "", code)
    # Drop pure-whitespace lines. We lose any intentional blank-line
    # paragraphing inside proofs, but the dense form is fine for display
    # and the lossy bit is bounded to display only.
    return "\n".join(line for line in code.split("\n") if line.strip())



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
    pieces the website renders: title, comments, statement, proof.

    We have to track whether we're inside a `/- … -/` block comment so a
    `def 3.8, …` line in a verbatim-LaTeX comment block isn't mistaken
    for a `def` declaration."""
    title = None
    comment_lines: list[str] = []
    decl_start: int | None = None
    in_block = False  # inside /- … -/ (Lean 4 block comments don't nest in practice for our scaffold)
    for i, line in enumerate(block_lines):
        if i == 0 and LEAN_MARKER_RE.match(line):
            continue

        # Maintain `in_block` state. Done character-wise so multiple
        # opens/closes on the same line collapse correctly.
        if in_block:
            comment_lines.append(line)
            if "-/" in line:
                in_block = False
            continue
        # We're outside a block comment at the start of this line.
        # An opening `/-` (incl. `/--`) without a matching `-/` on the
        # same line puts us inside one.
        open_idx = line.find("/-")
        if open_idx != -1:
            close_idx = line.find("-/", open_idx + 2)
            comment_lines.append(line)
            if close_idx == -1:
                in_block = True
            continue

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

    # Drop trailing bookkeeping lines that belong to the file or to the
    # NEXT declaration, not to this one — blanks, `end <ns>`, `namespace
    # <ns>`, `variable …`, `open …`, `section …`. Without this trim the
    # `namespace WalkStep` + `variable {G : CDMG α}` lines sitting
    # between the `inductive Walk` (item 1 of def_3_4) and the next
    # marker were getting attributed to `Walk` and showing up in the
    # right pane.
    _BOOKKEEPING_RE = re.compile(
        r"^\s*(end\b|namespace\b|variable\b|open\b|section\b|$)"
    )
    while body and _BOOKKEEPING_RE.match(body[-1]):
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

    # Strip Lean comments from what we display — they're surfaced via the
    # generated `lean_explanation` / `design_choices` panels instead.
    statement_clean = strip_lean_comments(statement_text)
    proof_clean = strip_lean_comments(proof) if proof else None

    return {
        "title": title,
        "comments": "\n".join(comment_lines).rstrip(),
        "statement": statement_clean,
        "proof": proof_clean,
    }


def extract_lean(
    lean_paths: list[Path], ref: str, file_order: list[str] | None = None,
) -> list[dict]:
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
            m = LEAN_MARKER_RE.match(block[0])
            part = m.group("part") if m else None
            tag  = m.group("tag")  if m else None  # "primary" | "helper" | None
            out.append(
                {
                    "part": part,
                    "tag":  tag,
                    "title": split["title"],
                    "comments": split["comments"],
                    "statement": split["statement"],
                    "proof": split["proof"],
                    "source_path": str(p.relative_to(REPO_ROOT)),
                    "source_line": start_idx + 1,
                }
            )

    # Primary sort: parsed item number from the marker (so def_3_4's
    # item 6 in Bifurcation.lean doesn't outrank items 1-5 in Walks.lean
    # just because of alphabetical filename order).
    # Secondary: position in `lean_files` from data.json, which is the
    # author's dependency order (defining file before users of the def).
    # Tertiary: source_line within a file.
    file_index = {p: i for i, p in enumerate(file_order or [])} if file_order else {}
    out.sort(key=lambda b: (
        _item_sort_key(b["part"]),
        file_index.get(b["source_path"], len(file_index)),
        b["source_line"],
    ))
    return out


# --------------------------------------------------------------------------- #
#  Curation — per-row visibility override                                     #
# --------------------------------------------------------------------------- #

CURATION_PATH = Path(__file__).resolve().parent / "curation.json"


def _curation() -> dict:
    """Read `scripts/curation.json`; per-row override controlling which Lean
    blocks the website shows."""
    if not CURATION_PATH.exists():
        return {}
    try:
        return json.loads(CURATION_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _curate_blocks(ref: str, blocks: list[dict]) -> list[dict]:
    """Apply the visibility convention to a row's Lean blocks.

    Resolution order:
      1. A marker tag of `[helper]` always hides a block; `[primary]`
         always keeps it. These travel with the source file so they're
         the canonical way to flag visibility.
      2. For refs listed in `curation.json` with a `primary` list, only
         blocks whose `part` matches an entry survive (in the list's
         order). This is the bridge while we add in-file `[…]` tags.
      3. With no marker tags and no curation entry, every block is kept
         — current behaviour, backward compatible for the rows that
         don't need filtering.
    """
    # 1) Always hide blocks tagged `[helper]`.
    blocks = [b for b in blocks if b.get("tag") != "helper"]

    primary = _curation().get(ref, {}).get("primary")
    if not primary:
        return blocks

    # 2) Take only blocks whose `part` appears in the curated list,
    #    in that order. Blocks tagged `[primary]` in the source are
    #    appended even if they're not in the list (one-off override).
    by_part: dict[str, dict] = {b.get("part") or "": b for b in blocks}
    ordered: list[dict] = []
    seen_ids: set[int] = set()
    for p in primary:
        b = by_part.get(p)
        if b is not None and id(b) not in seen_ids:
            ordered.append(b)
            seen_ids.add(id(b))
    for b in blocks:
        if b.get("tag") == "primary" and id(b) not in seen_ids:
            ordered.append(b)
            seen_ids.add(id(b))
    return ordered


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
    #
    # The proof page rendered on the site is the WHOLE proof file (a
    # restated `\begin{Lem|Rem|…}` block followed by a `\begin{proof}`
    # block), so we don't extract just the proof body — we hand the
    # full stripped TeX to `tex_body_to_html`, which knows how to render
    # both theorem-like envs and the proof env.
    tex_proof = None
    proof_path = tex_proof_path(data_path, row)
    if proof_path is not None and proof_path.exists():
        raw = proof_path.read_text(encoding="utf-8")
        from tex_to_html import strip_subfiles_wrapper  # local import
        stripped = strip_subfiles_wrapper(raw)
        tex_proof = {
            "raw": raw,
            "html": tex_body_to_html(stripped),
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
    lean_rel = list(dict.fromkeys([row["main_lean_file"], *row.get("lean_files", [])]))
    lean_abs = [REPO_ROOT / p for p in lean_rel]
    lean_blocks = extract_lean(lean_abs, ref, file_order=lean_rel)
    lean_blocks = _curate_blocks(ref, lean_blocks)

    # Preserve any prior LLM-generated prose so re-running fetch_row.py
    # doesn't wipe the panels — process_lean_comments.py owns these
    # fields. The fields stay null until the LLM step has populated them.
    out_path = WEBSITE_DATA / f"{ref}.json"
    prior_lean_expl: str | None = None
    prior_design: str | None = None
    if out_path.exists():
        try:
            prior = json.loads(out_path.read_text(encoding="utf-8"))
            prior_lean_expl = prior.get("lean_explanation")
            prior_design = prior.get("design_choices")
        except json.JSONDecodeError:
            pass

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
        "tex_statement":    tex_statement,
        "tex_proof":        tex_proof,
        "lean":             lean_blocks,
        "lean_explanation": prior_lean_expl,
        "design_choices":   prior_design,
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
