"""Populate a chapter's data.json with its definitions and claims.

A "def" is a ``\\begin{defmark}...\\end{defmark}`` block and a "claim" is a
``\\begin{claimmark}...\\end{claimmark}`` block in the lecture notes. They are
collected in render order -- when a .tex file ``\\input``s another, that file
is descended into in place -- and each block is also tagged in the .tex source
with a non-rendering ``% <ref>`` comment so an agent can locate it later.
"""
import json
import re
from pathlib import Path

LECTURE_NOTES_DIR = (
    Path(__file__).resolve().parent.parent / "lecture-notes" / "lecture_notes"
)

# LaTeX theorem environments (from thm.tex) -> the `type` recorded for an
# entry. An environment not listed here falls back to "note".
ENV_TYPES = {
    "Thm": "theorem",
    "DefThm": "definition/theorem",
    "Lem": "lemma",
    "Prp": "proposition",
    "Cor": "corollary",
    "Con": "conjecture",
    "Fct": "facts",
    "Prn": "principle",
    "Construction": "construction",
    "Alg": "algorithm",
    "Def": "definition",
    "DefLem": "definition/lemma",
    "NotLem": "notation/lemma",
    "Axm": "axiom",
    "Not": "notation",
    "Rem": "remark",
    "Cau": "caution",
    "Eg": "example",
    "Tho": "thoughts",
    "Exc": "exercise",
    "Ques": "question",
    "Expl": "explanation",
    "Disc": "discussion",
    "Conclusion": "conclusion",
    "Motivation": "motivation",
    "Step": "step",
    "Ass": "assumption",
}

# Action types an agent can take while solving a row -- see process_output in
# solving_current_chapter.py. A row's actions_tracking counts how often each
# of these was used; keep this list in sync with process_output's branches.
ACTIONS = [
    "Write proof",
    "Write proof in more detail",
    "solved",
    "add or delete rows",
    "refactor",
    "make plan",
    "decompose",
    "spawn_agent_sub_task",
    "reaching context limit",
    "re-order",
    "reset",  # When we want a fresh start
    "help",
    "mistake",
    "no_action",
]

# The marker environments and the kind of entry each one denotes.
_MARK_KINDS = {"defmark": "def", "claimmark": "claim"}

# A ref comment already inserted by this script (used to stay idempotent).
_REF_COMMENT = re.compile(r"^\s*%\s*(?:def|claim)_\d+_\d+\s*$")


def _read_raw(path):
    """Read a .tex file as text without translating its line endings.

    The lecture notes are latin-1 encoded (see main.tex); latin-1 also makes
    the read/write round-trip byte-exact.
    """
    with open(path, "r", encoding="latin-1", newline="") as f:
        return f.read()


def _code(line):
    """The line with any LaTeX comment (unescaped % to end of line) removed."""
    return re.sub(r"(?<!\\)%.*", "", line)


def _detect_type(lines, start, mark_env):
    """`type` of the entry whose \\begin{mark_env} sits on line `start`.

    Returns the first known theorem environment found inside the block, or
    "note" if none appears before \\end{mark_env}.
    """
    closing = rf"\end{{{mark_env}}}"
    for line in lines[start:]:
        code = _code(line)
        for m in re.finditer(r"\\begin\{(\w+)\}", code):
            if m.group(1) in ENV_TYPES:
                return ENV_TYPES[m.group(1)]
        if closing in code:
            break
    return "note"


def _scan(tex_file, marks, seen):
    """Collect def/claim marks from `tex_file` (recursively), in render order.

    Appends a dict {kind, type, tex_file, line} per mark to `marks`, and
    descends into \\input'd files where they are included.
    """
    if tex_file in seen:
        return
    seen.add(tex_file)
    path = LECTURE_NOTES_DIR / tex_file
    if not path.exists():
        return

    lines = _read_raw(path).splitlines()
    for i, line in enumerate(lines):
        code = _code(line)
        for env, kind in _MARK_KINDS.items():
            if rf"\begin{{{env}}}" in code:
                marks.append({
                    "kind": kind,
                    "type": _detect_type(lines, i, env),
                    "tex_file": tex_file,
                    "line": i,
                })
        inp = re.search(r"\\input\{([^}]+)\}", code)
        if inp:
            name = inp.group(1)
            if not name.endswith(".tex"):
                name += ".tex"
            _scan(name, marks, seen)


def _insert_ref_markers(marks):
    """Tag each mark in its .tex file with a non-rendering ``% <ref>`` line.

    The comment is placed on its own line directly above the mark's \\begin.
    Edits are grouped per file and applied bottom-up so line numbers stay
    valid; an already tagged mark is skipped, so this is safe to re-run.
    """
    by_file = {}
    for mark in marks:
        by_file.setdefault(mark["tex_file"], []).append(mark)

    for tex_file, file_marks in by_file.items():
        path = LECTURE_NOTES_DIR / tex_file
        lines = _read_raw(path).splitlines(keepends=True)
        for mark in sorted(file_marks, key=lambda m: m["line"], reverse=True):
            i = mark["line"]
            if i > 0 and _REF_COMMENT.match(lines[i - 1]):
                continue  # already tagged
            ending = "\r\n" if lines[i].endswith("\r\n") else "\n"
            indent = lines[i][: len(lines[i]) - len(lines[i].lstrip())]
            lines.insert(i, f"{indent}% {mark['ref']}{ending}")
        with open(path, "w", encoding="latin-1", newline="") as f:
            f.write("".join(lines))


def fill_data(chapter, tex_file, data_path):
    """Populate `data_path` (a chapter's data.json) with its defs and claims.

    Scans `tex_file` -- descending into \\input'd files -- for defmark and
    claimmark blocks, writes one row per block (in render order) into the data
    file, and tags each block in the .tex source with a ``% <ref>`` comment.

    Idempotent: if the data file already has rows, nothing happens, so a
    re-run never overwrites tracked progress nor duplicates the .tex markers.
    Returns the data file's Path.
    """
    data_path = Path(data_path)
    data = json.loads(data_path.read_text(encoding="utf-8"))
    if data.get("rows"):
        return data_path  # already populated

    marks = []
    _scan(tex_file, marks, set())

    # Number the refs per chapter and per kind, in render order.
    counts = {"def": 0, "claim": 0}
    rows = []
    for mark in marks:
        counts[mark["kind"]] += 1
        mark["ref"] = f"{mark['kind']}_{chapter}_{counts[mark['kind']]}"
        rows.append({
            "def_or_claim": mark["kind"],
            "solved": "no",
            "ref": mark["ref"],
            "type": mark["type"],
            "date_solved": "",
            "tips": "",
            "tex_file": mark["tex_file"],
            "lean_file": "",
            "actions_tracking": {action: 0 for action in ACTIONS},
        })

    _insert_ref_markers(marks)

    data["rows"] = rows
    with open(data_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    return data_path
