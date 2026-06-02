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
    # --- tex proof manipulation -------------------------------------------
    "expand_proof",          # add detail to an existing tex proof's specific step
    "correct_tex_proof",     # rewrite a tex proof after leanification revealed a mistake
    "verify_tex_proof",      # independent check that a tex proof is complete and correct
    # --- formalization review chain (statement-level) ---------------------
    "review_design",         # full-LN-context review of whether the Lean shape is natural
    "verify_equivalence",    # focused (friendly) check that the Lean statement matches the LN
    "verify_equivalence_strict",  # adversarial, default-strict equivalence (CONTENT vs PRESENTATION)
    "verify_with_examples",  # property-based equivalence check via concrete Lean instances
    "add_design_choice_comments",  # after equivalence PASS: enrich the Lean comments with WHY
    # --- proof review (after Lean proof closes) ---------------------------
    "simplify_proof",        # check if the Lean proof is over-complex; propose simpler if any
    # --- terminal / dispatch / control flow -------------------------------
    "solved",                # signal that the whole row is done (triggers row verifier)
    "refactor",
    "make_plan",
    "decompose",
    "spawn_agent_sub_task",
    "continue_agent",        # resume an earlier-spawned agent by session id (registry)
    "new_manager",           # hand off to a fresh manager to keep context small
    "reorder",               # propose `<refs> should be solved before this row` (auto-applies on verify)
    "reset",
    "request_from_human",    # rare last resort -- gated by repeat-attempt threshold
    "mistake",       # switch from prove-the-claim to disprove-the-claim mode
    "unmistake",     # flip back: reconsider, the claim might be provable after all
    "accept_deviation",  # record a CONTENT deviation in the register + bypass the next strict-equivalence solved-gate
    "register_ln_subtlety",  # record a subtlety in the LN wording itself in the working register (informational; never halts)
    "no_action",
]

# The marker environments and the kind of entry each one denotes.
_MARK_KINDS = {"defmark": "def", "claimmark": "claim"}

# A ref comment already inserted by this script (used to stay idempotent).
_REF_COMMENT = re.compile(r"^\s*%\s*(?:def|claim)_\d+_\d+\s*$")


def _extract_title(tex_block):
    """Short PascalCase title for filenames, lifted from a defmark/claimmark.

    Looks at the optional `\\begin{Env}[...]` argument of the first theorem
    environment inside the block. Preference order:
      1. A trailing parenthesized acronym -- ``[A long name (CDMG)]`` -> ``CDMG``
      2. The first 1-3 alphanumeric words, PascalCased
    Returns ``""`` if no bracketed title is found; the orchestrator can ask
    an agent to fill one in at row start.
    """
    m = re.search(r"\\begin\{\w+\}\[([^\]]+)\]", tex_block, flags=re.DOTALL)
    if not m:
        return ""
    raw = m.group(1).strip()
    acro = re.search(r"\(([A-Z][A-Za-z0-9]{1,15})\)\s*$", raw)
    if acro:
        return acro.group(1)
    words = re.findall(r"[A-Za-z0-9]+", raw)[:3]
    return "".join(w[0].upper() + w[1:] for w in words)


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


def _extract_block(lines, start, mark_env):
    """Verbatim text from ``\\begin{mark_env}`` (on line ``start``) through
    its matching ``\\end{mark_env}``, joined with ``"\\n"``. Includes both
    delimiter lines. If the closing tag is missing we return the rest of the
    file so the row still gets some content rather than crashing.
    """
    closing = rf"\end{{{mark_env}}}"
    for j in range(start, len(lines)):
        if closing in lines[j]:
            return "\n".join(lines[start:j + 1])
    return "\n".join(lines[start:])


def _scan(tex_file, marks, seen, state, chapter):
    """Collect def/claim marks from `tex_file` (recursively), in render order.

    Appends a dict {kind, type, tex_file, line, section} per mark to `marks`,
    and descends into \\input'd files where they are included. `state` is a
    mutable dict carrying the running ``\\subsection`` count so the section
    numbering continues across recursive \\input calls. `section` is
    formatted as ``"{chapter}.{idx}"``; marks that appear before the first
    ``\\subsection`` get ``""``.
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
        # \subsection{...} bumps the section counter; \subsection*{...} doesn't.
        if re.search(r"\\subsection\{", code):
            state["section_idx"] += 1
        for env, kind in _MARK_KINDS.items():
            if rf"\begin{{{env}}}" in code:
                idx = state["section_idx"]
                marks.append({
                    "kind": kind,
                    "type": _detect_type(lines, i, env),
                    "tex_file": tex_file,
                    "line": i,
                    "section": f"{chapter}.{idx}" if idx else "",
                    "tex_block": _extract_block(lines, i, env),
                })
        inp = re.search(r"\\input\{([^}]+)\}", code)
        if inp:
            name = inp.group(1)
            if not name.endswith(".tex"):
                name += ".tex"
            _scan(name, marks, seen, state, chapter)


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
    _scan(tex_file, marks, set(), {"section_idx": 0}, chapter)

    # Number the refs per chapter and per kind, in render order.
    counts = {"def": 0, "claim": 0}
    rows = []
    for mark in marks:
        counts[mark["kind"]] += 1
        mark["ref"] = f"{mark['kind']}_{chapter}_{counts[mark['kind']]}"
        is_claim = mark["kind"] == "claim"
        rows.append({
            "def_or_claim": mark["kind"],
            "ref": mark["ref"],
            "section": mark["section"],
            # Short PascalCase title used in filenames (def_<ref>_<title>.tex
            # etc.). Auto-extracted from `\begin{Env}[...]` in the tex_block
            # where possible; an empty value triggers the orchestrator to
            # pick one at row start.
            "title": _extract_title(mark["tex_block"]),
            "type": mark["type"],
            # Solve-state is split in two so we can track progress separately.
            # `solved` is the overall checkmark: a def is solved when
            # formalized; a claim is solved when formalized AND proven is
            # either "proven" or "disproven" (a counter-example also counts).
            "formalized": "no",                              # "no" | "yes"
            "proven": "not proven" if is_claim else "n/a",   # claims: "not proven"|"proven"|"disproven"; defs: "n/a"
            "solved": "no",                                  # "no" | "yes"
            "date_solved": "",
            "tips": "",
            "tex_file": mark["tex_file"],
            # The canonical Lean file for the row's main statement
            # (verifier reports it as MAIN_LEAN_FILE on PASS).
            "main_lean_file": "",
            # A row may produce multiple Lean files (e.g. a "definition"
            # row that is actually a notation list with several entries).
            # The verifier reports them all and mark_solved writes the list.
            "lean_files": [],
            "actions_tracking": {action: 0 for action in ACTIONS},
            # Verbatim contents of the defmark/claimmark block, so agents
            # have the canonical source without re-reading the .tex file.
            "tex_block": mark["tex_block"],
            # Session IDs (and metadata) of every Claude agent spawned for
            # this row -- the manager can ask the orchestrator to resume
            # any of them via the `continue_agent` action.
            "agent_registry": [],
            # Cumulative seconds the orchestrator has spent on this row
            # across all sessions. Only advances while solve_chapter is
            # actively working on it (sleeping during usage-limit pauses
            # counts as "active"). Persisted by solve_chapter every turn
            # so an interrupted run resumes from the right baseline.
            "time_needed_to_solve": 0,
            # Human-authored strengthening / disambiguation of the LN's
            # literal text, written by process_initialization_table.py
            # from the operator's answers to the wording-check decision
            # table. The equivalence-checker workers (verify_equivalence,
            # verify_equivalence_strict, verify_with_examples) treat this
            # as PART OF THE LN -- the formalization must satisfy LN +
            # this addition. Empty string when no addition applies.
            "addition_to_the_LN": "",
        })

    _insert_ref_markers(marks)

    data["rows"] = rows
    with open(data_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    return data_path
