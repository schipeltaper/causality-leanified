import json
import re
from pathlib import Path

from create_data import fill_data
from solve_chapter import (
    regenerate_subsection_main_tex,
    ensure_request_from_human_file,
    pick_title_for_row,
)

# Load global variables from the JSON data file.
GLOBAL_VARS_PATH = Path(__file__).parent / "global_vars.json"
with open(GLOBAL_VARS_PATH) as f:
    global_vars = json.load(f)

current_chapter = global_vars["current_chapter"]

# The lecture notes live one directory up from the scaffold.
SCAFFOLD_DIR = Path(__file__).resolve().parent
LECTURE_NOTES_DIR = SCAFFOLD_DIR.parent / "lecture-notes" / "lecture_notes"
MAIN_TEX_PATH = LECTURE_NOTES_DIR / "main.tex"

# Where each chapter is formalized: leanification/Chapter{N}_{PascalCaseTitle}/
LEANIFICATION_DIR = SCAFFOLD_DIR.parent / "leanification"
LAKEFILE_PATH = SCAFFOLD_DIR.parent / "lakefile.toml"
CAUSALITY_LEAN_PATH = LEANIFICATION_DIR / "Causality.lean"

# Initialize current chapter
#
# NOTE: this assumes `scaffold/prep_chapter.py` has already been run for this
# chapter -- the lecture-notes `.tex` file must already contain the
# `\begin{defmark}`/`\begin{claimmark}` markers. If you skip that step, the
# fill_data call below will return 0 rows.
def initialize():
    # Get title_chapter and tex_file_chapter
    (title_chapter, tex_file_chapter) = get_title_and_tex_file_chapter(current_chapter)

    chapter_folder = create_folder(current_chapter, title_chapter)
    chapter_module = chapter_folder.name        # e.g. "Chapter3_GraphTheory"

    # Create empty data file in {current_chapter}_{title_chapter} folder
    data_path = create_data(current_chapter, title_chapter)

    # Wire the chapter into the Lean build:
    #   - stub aggregator file `leanification/<ChapterModule>.lean`
    #   - lakefile globs so Lake registers the module + its subsection submodules
    #   - `import <ChapterModule>` line in `leanification/Causality.lean`
    ensure_chapter_aggregator_stub(chapter_module)
    ensure_lakefile_globs_for_chapter(chapter_module)
    ensure_causality_imports_chapter(chapter_module)

    # run create data script (parses the marks left by `prep_chapter.py`).
    fill_data(current_chapter, tex_file_chapter, data_path)

    # Walk every row whose title wasn't auto-extractable from the LN's
    # `\begin{Env}[...]` argument and spawn a per-row title-picker agent.
    # This is slow on a fresh chapter (one claude call per empty row) but
    # only happens once and is essential -- the title is used in every
    # per-row filename.
    refreshed = json.loads(data_path.read_text(encoding="utf-8"))
    untitled = [r for r in refreshed["rows"] if not r.get("title")]
    if untitled:
        print(f"[init] picking titles for {len(untitled)} rows ...", flush=True)
        for r in untitled:
            r["title"] = pick_title_for_row(r)
            print(f"[init]   {r['ref']} -> {r['title']}", flush=True)
        data_path.write_text(
            json.dumps(refreshed, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

    # Write one `main.tex` per subsection that has rows in it (statements
    # only -- proofs live in their own per-row `_proof_` files). Future
    # manager agents read this to get the full subsection context.
    for section in sorted({r.get("section", "") for r in refreshed["rows"]
                           if r.get("section")}):
        regenerate_subsection_main_tex(data_path, refreshed, section)

    # Drop the chapter-level request-from-human file so it exists from the
    # start; the `request_from_human` action appends into it.
    ensure_request_from_human_file(LEANIFICATION_DIR / chapter_module)

    return tex_file_chapter


def ensure_chapter_aggregator_stub(chapter_module: str) -> Path:
    """Create ``leanification/<ChapterModule>.lean`` with an empty aggregator
    body, if it doesn't already exist. ``solve_chapter.py`` rewrites
    this file every time a row in the chapter is marked solved.
    """
    path = LEANIFICATION_DIR / f"{chapter_module}.lean"
    if path.exists():
        return path
    path.write_text(
        f"-- Aggregator for chapter folder `{chapter_module}`.\n"
        f"-- Auto-managed by scaffold/solve_chapter.py; do not edit by hand.\n",
        encoding="utf-8",
    )
    return path


def ensure_lakefile_globs_for_chapter(chapter_module: str) -> None:
    """Idempotently add ``"<ChapterModule>"`` and ``"<ChapterModule>.+"`` to
    the ``Causality`` lib's ``globs`` array so Lake registers the chapter's
    aggregator and every subsection submodule.

    Skips the edit silently if both entries are already present. We keep the
    edit string-based so we don't need a TOML parser dependency.
    """
    text = LAKEFILE_PATH.read_text(encoding="utf-8")
    entry = f'"{chapter_module}"'
    deep_entry = f'"{chapter_module}.+"'
    if entry in text and deep_entry in text:
        return

    # Insert before the closing `]` of the globs list. Locate it by finding
    # the first `]` that follows `globs = [`.
    start = text.find("globs = [")
    if start < 0:
        raise RuntimeError("lakefile.toml is missing a `globs = [...]` list")
    end = text.find("]", start)
    if end < 0:
        raise RuntimeError("lakefile.toml `globs = [` is not closed")

    additions = []
    if entry not in text:
        additions.append(f"  {entry},\n")
    if deep_entry not in text:
        additions.append(f"  {deep_entry},\n")
    LAKEFILE_PATH.write_text(
        text[:end] + "".join(additions) + text[end:],
        encoding="utf-8",
    )


def ensure_causality_imports_chapter(chapter_module: str) -> None:
    """Append ``import <ChapterModule>`` to ``leanification/Causality.lean``
    if it isn't already there."""
    line = f"import {chapter_module}"
    text = CAUSALITY_LEAN_PATH.read_text(encoding="utf-8")
    if line in text.splitlines():
        return
    if not text.endswith("\n"):
        text += "\n"
    CAUSALITY_LEAN_PATH.write_text(text + line + "\n", encoding="utf-8")


# Create empty data file in {current_chapter}_{title_chapter} within leanification folder
# It will represent a large table. Each row will be a claim or def from the lecture notes.
# Column titles: 
#   def or claim, 
#   checkmark solved or not, 
#   reference to the tex in the form ref[def/claim]_[chapter]_[nth item in this chapter],
#   Type (like definition, theorem, note, remark, lemma, corollary, etc.)
#   Date solved
#   Tips (like, the proof is at the end of this chapter in the lecture notes!)
#   Which tex file it is in
#   Lean file path (of the formalization of the statement)  
#   Actions_tracking (a new table that tracks how often each action is called for this row)
def create_data(current_chapter, title_chapter):
    """Create an empty data file for a chapter and return its Path.

    Writes ``data.json`` into the chapter's leanification folder. Each future
    row is one definition or claim from the lecture notes; this lays down the
    schema with an empty ``rows`` list. An existing data file is left as is,
    so tracked progress is never overwritten.
    """
    chapter_folder = create_folder(current_chapter, title_chapter)
    data_path = chapter_folder / "data.json"
    if data_path.exists():
        return data_path

    dataset = {
        "chapter": current_chapter,
        "title": title_chapter,
        "columns": [
            "def_or_claim",
            "ref",
            "section",
            "title",
            "type",
            "formalized",
            "proven",
            "solved",
            "date_solved",
            "tips",
            "tex_file",
            "main_lean_file",   # file containing the canonical statement
            "lean_files",       # every Lean file the row produced
            "actions_tracking",
            "tex_block",
            "agent_registry",   # session ids of agents the manager can resume
            "time_needed_to_solve",   # cumulative seconds the orchestrator
                                      # has spent on this row across runs;
                                      # only ticks while solve_chapter is
                                      # actively working on it (sleeping
                                      # during usage-limit pauses counts).
        ],
        "rows": [],
    }
    with open(data_path, "w", encoding="utf-8") as f:
        json.dump(dataset, f, indent=2, ensure_ascii=False)
    return data_path


# Chapter folder in leanification/: Chapter{N}_{PascalCaseTitle}
def create_folder(current_chapter, title_chapter):
    """Create the leanification folder for a chapter and return its Path.

    The folder is named ``Chapter{N}_{PascalCaseTitle}`` inside
    LEANIFICATION_DIR. The pattern is chosen so the folder name doubles as a
    valid Lean module path segment -- a file at
    ``leanification/Chapter{N}_{PascalCaseTitle}/Section{N}_{M}/<X>.lean``
    becomes module ``Chapter{N}_{PascalCaseTitle}.Section{N}_{M}.<X>``.
    Safe to call repeatedly: an existing folder is left untouched.
    """
    folder_name = f"Chapter{current_chapter}_{_to_lean_module_segment(title_chapter)}"
    chapter_folder = LEANIFICATION_DIR / folder_name
    chapter_folder.mkdir(parents=True, exist_ok=True)
    return chapter_folder


def _to_lean_module_segment(name):
    """Turn a chapter title into a valid Lean module path segment.

    Lean module names are dot-separated identifiers matching
    ``[A-Za-z_][A-Za-z0-9_]*``. This drops LaTeX escapes and punctuation,
    PascalCases the word parts, and joins them with no spaces.
    """
    name = re.sub(r"\\([&%_#${}])", r"\1", name)   # \& -> &, \% -> %, ...
    name = re.sub(r"[^\w\s]", "", name)            # drop remaining punctuation
    parts = name.split()
    return "".join(p[0].upper() + p[1:] for p in parts if p)


def get_title_and_tex_file_chapter(current_chapter):
    """Return (title, tex_file) for chapter number `current_chapter` (1-indexed).

    A "chapter" is a numbered \\section in the lecture notes. main.tex is the
    entry point: this walks its \\input chain in order and, for every
    \\section, records its title and the .tex file it appears in. Returns the
    `current_chapter`-th pair as (title_chapter, tex_file_chapter).
    """
    main_tex = _read_tex(MAIN_TEX_PATH)

    chapters = []  # (title, tex_file) for each numbered section, in order
    for name in _chapter_input_files(main_tex):
        tex_file = f"{name}.tex"
        tex_path = LECTURE_NOTES_DIR / tex_file
        if tex_path.exists():
            for title in _section_titles(_read_tex(tex_path)):
                chapters.append((title, tex_file))

    if not 1 <= current_chapter <= len(chapters):
        raise ValueError(
            f"current_chapter={current_chapter} is out of range; "
            f"the lecture notes contain {len(chapters)} chapters."
        )
    return chapters[current_chapter - 1]

def _strip_tex_comments(text):
    """Remove LaTeX comments: everything after an unescaped '%' on each line."""
    return "\n".join(
        re.sub(r"(?<!\\)%.*", "", line) for line in text.splitlines()
    )


def _read_tex(path):
    """Read a .tex file (lecture notes are latin-1 encoded), comments stripped."""
    return _strip_tex_comments(path.read_text(encoding="latin-1"))


def _chapter_input_files(main_tex):
    """Ordered list of files \\input by main.tex within the document body."""
    body = main_tex.split(r"\begin{document}", 1)[-1]
    return re.findall(r"\\input\{([^}]+)\}", body)


def _balanced_braces(text, start):
    """Content of a brace group whose first inner character is at index `start`."""
    depth = 1
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start:i].strip()
    return text[start:].strip()  # unbalanced braces: return whatever remains


def _section_titles(tex):
    """Titles of every numbered \\section{...} in `tex`, in document order.

    Starred sections (\\section*{...}, such as the foreword) are unnumbered,
    so they are not counted as chapters.
    """
    return [
        _balanced_braces(tex, m.end())
        for m in re.finditer(r"\\section\s*\{", tex)
    ]




if __name__ == "__main__":
    initialize()
