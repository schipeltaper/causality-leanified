"""Orchestrate solving the first unsolved row of the current chapter.

High-level flow
---------------
1. Read the current chapter number from ``global_vars.json``.
2. Load that chapter's ``data.json`` and pick the first row with ``solved="no"``.
3. Spawn a *manager* Claude Code agent with the ``manager.md`` prompt and the
   row's context. The manager replies with exactly one action tag of the form::

       BEGIN[<action_name>]
       <body -- a brief for the next agent>
       END[<action_name>]

4. Parse the action tag, increment the row's ``actions_tracking[action]``
   counter, and dispatch:

   - **Worker actions** (``write_proof``, ``expand_proof``, ``refactor``,
     ``make_plan``, ``decompose``, ``mistake``, ``spawn_agent_sub_task``):
     spawn a worker Claude agent with the matching prompt under
     ``claude_prompts/row_workers/`` and feed its output back to the manager.
   - ``solved``: dispatch the ``verify_row_solved`` worker as an independent
     checker. If it passes, mark the row solved in ``data.json`` and exit.
   - ``new_manager``: discard the running manager's accumulated context and
     start a fresh manager with the body as a handoff dossier.
   - ``reset``: discard all history and start a fresh manager from scratch.
   - ``help`` / ``no_action``: stop and let the human take over.

5. Loop until the row is solved, the human is needed, or the 20-hour budget is
   used up.

The manager itself does no file I/O -- it is a pure reasoner. Workers do the
labour (editing Lean files, building, etc.). Python keeps the state.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths and configuration
# ---------------------------------------------------------------------------

SCAFFOLD_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCAFFOLD_DIR.parent
LEANIFICATION_DIR = REPO_ROOT / "leanification"
LECTURE_NOTES_DIR = REPO_ROOT / "lecture-notes" / "lecture_notes"
PROMPTS_DIR = SCAFFOLD_DIR / "claude_prompts"
WORKERS_DIR = PROMPTS_DIR / "row_workers"
TEX_TEMPLATES_DIR = SCAFFOLD_DIR / "tex_templates"

GLOBAL_VARS_PATH = SCAFFOLD_DIR / "global_vars.json"

# Hardcoded git branch where normal row-solving happens. Kept in sync
# with the same constant in ``extras/do_refactor.py`` -- the manager's
# ``refactor`` action prints a "switch to this branch then run
# do_refactor.py init" message and we want both to agree on the name.
SERVER_BRANCH = "server_setting_up_scaffold"

# Every Claude subprocess uses the strongest model available -- Opus 4.7 (1M
# context) with the maximum effort level. Cost is justified: each turn does
# serious mathematical work.
CLAUDE_MODEL = "claude-opus-4-7[1m]"
CLAUDE_EFFORT = "max"

# When the manager calls `request_from_human` we make it earn it: the first
# few attempts get a "are you sure you've tried everything?" nudge back; only
# at the threshold do we actually write the request to disk and stop. The
# counter is kept in the row's `actions_tracking["request_from_human"]`.
HUMAN_REQUEST_THRESHOLD = 3

# Total wall-clock budget. The loop stops once this is exhausted.
MAX_RUNTIME_SECONDS = 20 * 60 * 60         # 20 hours

# Per-subprocess timeout. A single agent should not run longer than this.
PER_CALL_TIMEOUT_SECONDS = 2 * 60 * 60         # 2 hours

# Maximum number of manager turns before we bail out, just in case the loop
# is stuck producing the same no-op action over and over.
MAX_TURNS = 200

# Each manager action maps either to a worker prompt file (under WORKERS_DIR)
# or to a control-flow signal handled directly in Python. ``None`` means the
# body of the action tag is itself the prompt for a freshly-spawned worker.
ACTION_TO_WORKER: dict[str, str | None] = {
    "expand_proof":              "expand_tex_proof.md",
    "correct_tex_proof":         "correct_tex_proof.md",
    "add_design_choice_comments": "add_design_choice_comments.md",
    "make_plan":                 "plan_subtasks.md",
    "decompose":                 "plan_subtasks.md",
    "spawn_agent_sub_task":      None,   # body is the prompt
    # `mistake` and `refactor` are intentionally NOT here -- both are
    # inline-handled. `mistake` is a state signal that flips the eventual
    # verdict to disproven; `refactor` dispatches the heavy redesign-planner
    # worker and then exits the row run so the next iteration picks up
    # the now-earlier first-unsolved row. (The lighter code-level refactor
    # worker `refactor_lean_code.md` is still available to the manager via
    # `spawn_agent_sub_task` for non-design-change cleanups.)
}

# Verifier-style actions: spawn a worker, parse `VERDICT: PASS/FAIL`, feed
# back to the manager. They never mutate row state directly.
VERIFIER_ACTIONS: dict[str, tuple[str, str]] = {
    # action_name -> (worker_prompt_filename, label_suffix)
    "verify_tex_proof":          ("verify_tex_proof.md",          "tex_proof_verifier"),
    "review_design":             ("review_design.md",             "design_reviewer"),
    "verify_equivalence":        ("verify_equivalence.md",        "equivalence_verifier"),
    "verify_equivalence_strict": ("verify_equivalence_strict.md", "strict_eq_verifier"),
    "verify_with_examples":      ("verify_with_examples.md",      "examples_verifier"),
    "simplify_proof":            ("simplify_proof.md",            "simplifier"),
}

# Regex that pulls the (action_name, body) out of a manager message. The
# action name must use the same identifier in BEGIN and END, and there must
# be no trailing text after END[...].
ACTION_TAG_RE = re.compile(
    r"BEGIN\[(?P<name>[A-Za-z_]+)\]\s*\n(?P<body>.*?)\n\s*END\[(?P=name)\]\s*\Z",
    re.DOTALL,
)


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class TurnRecord:
    """One iteration of the orchestration loop.

    Kept around so the next manager turn knows what was tried and how it went.
    """
    turn_index: int
    action: str
    body: str
    worker_summary: str = ""   # short result from the dispatched worker


@dataclass
class OrchestrationState:
    """Everything we carry across iterations of the loop."""
    chapter: int
    data_path: Path
    row_index: int
    row: dict
    history: list[TurnRecord] = field(default_factory=list)
    started_at: float = field(default_factory=time.monotonic)
    # Two-stage `mistake` sweep gate. Set to True after each stage has
    # been completed (run AND any findings presented to the manager).
    # Both must be True for a `mistake` action to be honored. Resets
    # per row run (fresh OrchestrationState).
    mistake_stage1_done: bool = False
    mistake_stage2_done: bool = False
    # Strict-equivalence solved-gate bypass. Flipped True when the
    # manager emits `accept_deviation` -- the next `solved` attempt's
    # strict-equivalence check is then skipped (the manager has
    # explicitly accepted the deviation and recorded it in the register).
    # Resets per row run.
    deviation_accepted: bool = False

    @property
    def elapsed_seconds(self) -> float:
        return time.monotonic() - self.started_at

    @property
    def ref(self) -> str:
        return self.row["ref"]


# ---------------------------------------------------------------------------
# Small helpers (one job each)
# ---------------------------------------------------------------------------

def read_current_chapter() -> int:
    """Get the chapter number we are working on from global_vars.json."""
    return json.loads(GLOBAL_VARS_PATH.read_text(encoding="utf-8"))["current_chapter"]


def find_chapter_data_path(chapter: int) -> Path:
    """Locate the chapter's data.json by matching the ``Chapter{N}_`` prefix
    used by ``initialize_chapter.create_folder``."""
    for child in sorted(LEANIFICATION_DIR.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child / "data.json"
    raise FileNotFoundError(
        f"No leanification folder found for chapter {chapter}."
    )


# Match the chapter folder prefix anywhere in a data.json path. Used to
# infer the chapter number when the orchestrator is invoked with an
# explicit ``--data-path`` (e.g., for refactor-table runs whose data.json
# lives under ``leanification/Chapter3_GraphTheory/Refactor_X/...``).
_CHAPTER_FOLDER_RE = re.compile(r"^Chapter(\d+)_")


def _infer_chapter_from_path(data_path: Path) -> int:
    """Walk the path's parts looking for a ``ChapterN_*`` folder; return
    ``N``. Returns ``0`` if no such part is found -- callers can decide
    whether to error or carry on with a "no chapter" sentinel.

    Used so that ``state.chapter`` (a display field rendered in row
    context) stays meaningful even when the orchestrator was invoked
    with ``--data-path`` instead of a chapter number.
    """
    for part in data_path.parts:
        m = _CHAPTER_FOLDER_RE.match(part)
        if m:
            return int(m.group(1))
    return 0


def _chapter_folder_for(data_path: Path) -> Path:
    """Walk up from ``data_path`` until we hit a ``ChapterN_*`` directory;
    return that directory. Falls back to ``data_path.parent`` if no such
    ancestor exists.

    Why this matters: a normal chapter's data.json lives directly inside
    the chapter folder, so ``data_path.parent`` IS the chapter folder.
    But a refactor table's data.json lives one level deeper (under
    ``leanification/Chapter3_GraphTheory/Refactor_<name>/refactor_data.json``).
    For path math that should target the chapter -- in particular, the
    section subfolders like ``Section3_1/`` where the Lean files live --
    we want the chapter folder, not the refactor folder.
    """
    p = data_path.parent.resolve()
    while p != p.parent:
        if _CHAPTER_FOLDER_RE.match(p.name):
            return p
        p = p.parent
    # Fallback: behave exactly as the old code did.
    return data_path.parent


def load_data(data_path: Path) -> dict:
    return json.loads(data_path.read_text(encoding="utf-8"))


def save_data(data_path: Path, data: dict) -> None:
    """Write the data back to disk pretty-printed and UTF-8 -- the format the
    rest of the scaffold expects."""
    data_path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def first_unsolved_row_index(data: dict) -> int:
    """Return the index of the first row whose ``solved`` field is not "yes",
    or raise if the chapter is fully done."""
    for i, row in enumerate(data["rows"]):
        if row.get("solved") != "yes":
            return i
    raise RuntimeError("All rows in this chapter are already solved.")


def section_folder_name(section: str) -> str:
    """Map a row's ``section`` value (e.g. ``"3.1"``) to the subsection
    folder name (``"Section3_1"``). Returns ``""`` for rows whose mark sits
    before any ``\\subsection`` in the tex file -- callers should fall back
    to the chapter folder itself in that case.
    """
    if not section:
        return ""
    return f"Section{section.replace('.', '_')}"


def ensure_subsection_folder(chapter_folder: Path, section: str) -> Path:
    """Create the subsection folder if missing and return its path.

    Falls back to the chapter folder when the row has no ``section`` so a
    pre-subsection mark still has somewhere to land.
    """
    name = section_folder_name(section)
    target = chapter_folder / name if name else chapter_folder
    target.mkdir(parents=True, exist_ok=True)
    return target


def _row_lean_files(row: dict) -> list[str]:
    """Return the row's ``lean_files`` list, tolerating an older single
    ``lean_file`` string (which gets wrapped in a single-element list)."""
    files = row.get("lean_files")
    if isinstance(files, list):
        return [f for f in files if f]
    legacy = row.get("lean_file", "")
    return [legacy] if legacy else []


def regenerate_chapter_aggregator(data_path: Path, data: dict) -> None:
    """(Re)write ``leanification/<ChapterFolder>.lean`` so it imports every
    Lean file mentioned by a solved row. Called after every ``mark_solved``
    so the next ``lake build`` walks the chapter.
    """
    chapter_folder = data_path.parent
    chapter_name = chapter_folder.name                        # e.g. "Chapter3_GraphTheory"
    aggregator_path = chapter_folder.parent / f"{chapter_name}.lean"

    imports: list[str] = []
    for row in data["rows"]:
        if row.get("solved") != "yes":
            continue
        for lf in _row_lean_files(row):
            parts = Path(lf).parts
            # Expected shape: ('leanification', '<Chapter>', '<Section>', '<File>.lean')
            if parts[0] != "leanification" or len(parts) < 3:
                continue
            imports.append(".".join(parts[1:-1] + (Path(parts[-1]).stem,)))

    aggregator_path.write_text(
        f"-- Aggregator for chapter folder `{chapter_name}`.\n"
        f"-- Auto-managed by scaffold/solve_chapter.py; do not edit by hand.\n\n"
        + "".join(f"import {m}\n" for m in imports),
        encoding="utf-8",
    )


def _strip_mark_wrapper(tex_block: str) -> str:
    """Drop the ``\\begin{defmark}/\\begin{claimmark}`` outer wrapping and
    return only the inner content. The mark wrapper is a scaffolding
    annotation; standalone subfiles render the inner theorem env directly.
    """
    m = re.search(
        r"\\begin\{(defmark|claimmark)\}\n?(.*?)\n?\\end\{\1\}",
        tex_block, flags=re.DOTALL,
    )
    return m.group(2) if m else tex_block


# Map data.json ``type`` column to the amsthm env declared in the preamble.
# This is used both when generating fresh stubs (so the env name matches the
# row's type) and when backfilling existing files (so the env name agrees
# with what the `refprefix` theoremstyle will render as the header).
TYPE_TO_ENV: dict[str, str] = {
    "definition":         "Def",
    "definition/theorem": "DefThm",
    "definition/lemma":   "DefLem",
    "notation/lemma":     "NotLem",
    "theorem":            "Thm",
    "lemma":              "Lem",
    "proposition":        "Prp",
    "corollary":          "Cor",
    "remark":             "Rem",
    "note":               "Note",
    "notation":           "Not",
    "example":            "Eg",
    "construction":       "Construction",
    "algorithm":          "Alg",
    "exercise":           "Exc",
    "thoughts":           "Tho",
    "conjecture":         "Con",
    "facts":              "Fct",
    "principle":          "Prn",
    "assumption":         "Ass",
    "axiom":              "Axm",
    "question":           "Ques",
    "explanation":        "Expl",
    "discussion":         "Disc",
    "conclusion":         "Conclusion",
    "motivation":         "Motivation",
    "caution":            "Cau",
    "step":               "Step",
}


def _env_for_type(t: str) -> str:
    """Return the amsthm env name for a row's ``type``. Falls back to ``Rem``
    so an unfamiliar type still produces a valid (if generic) header rather
    than an unknown-env build error.
    """
    return TYPE_TO_ENV.get((t or "").strip().lower(), "Rem")


def _rewrite_env_to_type(body: str, row_type: str) -> str:
    """If ``body`` starts with a single ``\\begin{X}...\\end{X}`` block, rename
    the env to whatever the row's ``type`` dictates. Bodies that do not start
    with a theorem env (free-flowing text, multiple envs, etc.) are returned
    unchanged; the backfill / worker is responsible for those.
    """
    target = _env_for_type(row_type)
    m = re.match(
        r"\A\s*\\begin\{([A-Za-z*]+)\}(.*)\\end\{\1\}\s*\Z",
        body, flags=re.DOTALL,
    )
    if not m or m.group(1) == target:
        return body
    inner = m.group(2)
    return f"\\begin{{{target}}}{inner}\\end{{{target}}}"


# Envs whose header should display a title via the refprefix theoremstyle.
# Used when injecting the row's data.json title into a bare \begin{Env}.
_TITLED_ENVS = set(TYPE_TO_ENV.values()) | {"Rem", "Note"}

_BARE_ENV_OPENER_RE = re.compile(
    r"\\begin\{(?P<name>[A-Za-z*]+)\}(?!\s*\[)"
)


def _inject_title_into_bare_env(body: str, title: str) -> str:
    """Inject ``[<title>]`` into the first bare ``\\begin{X}`` whose env is
    in ``_TITLED_ENVS`` (theorem-like envs declared in the preamble).
    Non-theorem envs (``document``, ``itemize``, ``proof``, ...) are
    skipped so we don't pollute generic block openers.
    """
    if not title:
        return body
    for m in _BARE_ENV_OPENER_RE.finditer(body):
        if m.group("name") in _TITLED_ENVS:
            i = m.end()
            return body[:i] + f"[{title}]" + body[i:]
    return body


def _render_template(name: str, **values: str) -> str:
    """Substitute ``__KEY__`` placeholders in
    ``scaffold/tex_templates/<name>.tex.template``. Missing keys are left
    intact so the artifact still hints at what's not yet filled.
    """
    raw = (TEX_TEMPLATES_DIR / f"{name}.tex.template").read_text(encoding="utf-8")
    for k, v in values.items():
        raw = raw.replace(f"__{k}__", v)
    return raw


def _file_basename(row: dict, kind_suffix: str | None = None) -> str:
    """Build the subfile filename for a row.

    - For a def row:    ``<ref>_<title>.tex``                  (kind_suffix=None)
    - For a claim row, ``kind_suffix`` is one of:
        - ``"statement"`` : ``<ref>_statement_<title>.tex``
        - ``"proof"``     : ``<ref>_proof_<title>.tex`` (prove the claim)
        - ``"disproof"``  : ``<ref>_disproof_<title>.tex`` (prove the negation;
          only created/used when the manager switches to disprove mode via
          the `mistake` action)
    """
    ref = row["ref"]
    title = row.get("title") or "Untitled"
    if row["def_or_claim"] == "def":
        return f"{ref}_{title}.tex"
    assert kind_suffix in ("statement", "proof", "disproof"), \
        "claim rows need kind_suffix 'statement' / 'proof' / 'disproof'"
    return f"{ref}_{kind_suffix}_{title}.tex"


def disprove_lean_filename(row: dict) -> str:
    """Conventional Lean filename for a claim row's disprove-direction
    work: ``<Title>Disproof.lean`` -- a sibling of the prove file
    (``<Title>.lean``) inside the subsection folder. The two coexist on
    disk so the manager can toggle between `mistake` and `unmistake`
    without overwriting either side's progress.
    """
    title = row.get("title") or "Untitled"
    return f"{title}Disproof.lean"


def _refactor_proof_basename(row: dict) -> str | None:
    """Conventional filename for the *refactor twin* of a claim row's
    proof subfile: ``refactor_<ref>_proof_<title>.tex``. Returns ``None``
    for non-claim rows (def refactors don't need a tex twin -- the def's
    LN block doesn't change in a refactor; only the Lean encoding does).

    The twin lives alongside the original ``<ref>_proof_<title>.tex`` in
    the same section's ``tex/`` folder. The refactor's manager writes
    the new proof into the twin; the original stays untouched until
    Phase 7 cleanup, which renames the twin over the original.
    """
    if row.get("def_or_claim") != "claim":
        return None
    return "refactor_" + _file_basename(row, "proof")


def _row_subfile_paths(row: dict, subsection_folder: Path) -> list[Path]:
    """Every subfile path a row contributes to (1 for a def, 2 for a
    claim). The disprove-side tex (`_disproof_`) is intentionally *not*
    included here -- it's created lazily on the first `mistake` action,
    not at row stub creation, because most rows never enter disprove
    mode.

    All per-row tex files live under ``<subsection_folder>/tex/`` so the
    subsection folder itself stays tidy.
    """
    tex_dir = subsection_folder / "tex"
    if row["def_or_claim"] == "def":
        return [tex_dir / _file_basename(row)]
    return [
        tex_dir / _file_basename(row, "statement"),
        tex_dir / _file_basename(row, "proof"),
    ]


def ensure_preamble_at_leanification() -> Path:
    """Copy ``scaffold/tex_templates/preamble.tex`` to
    ``leanification/preamble.tex`` if it's missing or stale. Idempotent.
    Returns the destination path.
    """
    src = TEX_TEMPLATES_DIR / "preamble.tex"
    dst = LEANIFICATION_DIR / "preamble.tex"
    if (not dst.exists()
            or dst.stat().st_mtime < src.stat().st_mtime):
        dst.write_text(src.read_text(encoding="latin-1"), encoding="latin-1")
    return dst


def ensure_row_subfiles(row: dict, subsection_folder: Path) -> list[Path]:
    """Create stub subfile(s) for a row from the templates if they don't
    already exist. Returns the list of subfile paths in render order.

    Files land in ``<subsection_folder>/tex/``. Bodies of freshly-created
    stubs:
      - def: the inner content of the row's ``tex_block`` (no defmark wrap)
      - claim statement: same, for the claimmark
      - claim proof: the statement (verbatim from ``tex_block``) followed by
        an empty ``\\begin{proof}`` body so the file renders on its own and
        the proof-writing worker can read the claim it is proving without
        opening a second file
    """
    paths = _row_subfile_paths(row, subsection_folder)
    if paths:
        paths[0].parent.mkdir(parents=True, exist_ok=True)
    body_from_block = _strip_mark_wrapper(row.get("tex_block", "")).strip()
    # Align the theorem env in the LN tex_block with the row's `type`
    # column (e.g. a "lemma" row goes into a \begin{Lem} regardless of what
    # the LN happened to use). The refprefix theoremstyle in the preamble
    # then renders the header as "<ref> <ThmName> -- <title>".
    body_from_block = _rewrite_env_to_type(body_from_block, row.get("type", ""))
    # If the env opener has no [<arg>] optional argument, inject the row's
    # data.json title there so every rendered header has a name.
    body_from_block = _inject_title_into_bare_env(
        body_from_block, row.get("title", ""))
    # `REF` (catcode-8 underscores) is fine inside \label / \refrow because
    # hyperref stores labels as opaque strings; but \rowref expands in text
    # mode, so its `_` chars must be escaped. `REF_TEXT` is the
    # display-friendly variant for \def\rowref{...}.
    ref = row["ref"]
    ref_text = ref.replace("_", r"\_")
    for p in paths:
        if p.exists():
            continue
        if row["def_or_claim"] == "def":
            content = _render_template(
                "def",
                REF=ref,
                REF_TEXT=ref_text,
                TITLE=row.get("title", ""),
                BODY=body_from_block,
            )
        elif "_statement_" in p.name:
            content = _render_template(
                "claim_statement",
                REF=ref,
                REF_TEXT=ref_text,
                TITLE=row.get("title", ""),
                BODY=body_from_block,
            )
        else:
            content = _render_template(
                "claim_proof",
                REF=ref,
                REF_TEXT=ref_text,
                TITLE=row.get("title", ""),
                STATEMENT_BODY=body_from_block,
                BODY="% TODO: write the proof body.",
            )
        p.write_text(content, encoding="utf-8")
    return paths


def ensure_disprove_stubs(row: dict, subsection_folder: Path) -> None:
    """Create the disprove-side tex stub for a claim row, lazily on the
    first ``mistake`` action. Mirrors ``ensure_row_subfiles`` but only
    creates ``tex/<ref>_disproof_<title>.tex`` (uses the same
    ``claim_proof.tex.template``; the body slot starts as a
    ``% TODO: write a proof of NOT-<claim>`` placeholder, with the
    NEGATED statement restated above the proof env).

    Idempotent: if the disprove tex already exists, nothing happens.
    The disprove-side Lean file (``<Title>Disproof.lean``) is *not*
    created here -- the leanification worker writes it on first need,
    keeping the orchestrator out of the business of fabricating empty
    Lean stubs.
    """
    if row.get("def_or_claim") != "claim":
        return
    tex_dir = subsection_folder / "tex"
    tex_dir.mkdir(parents=True, exist_ok=True)
    out = tex_dir / _file_basename(row, "disproof")
    if out.exists():
        return
    # Restate the (positive) claim above the disprove proof so the file
    # renders self-contained; the proof body is left as a TODO that the
    # disprove-side worker fills in with a proof of NOT-claim.
    body_from_block = _strip_mark_wrapper(row.get("tex_block", "")).strip()
    body_from_block = _rewrite_env_to_type(body_from_block, row.get("type", ""))
    body_from_block = _inject_title_into_bare_env(
        body_from_block, row.get("title", ""))
    ref = row["ref"]
    ref_text = ref.replace("_", r"\_")
    content = _render_template(
        "claim_proof",
        REF=ref,
        REF_TEXT=ref_text,
        TITLE=row.get("title", ""),
        STATEMENT_BODY=body_from_block,
        BODY=("% TODO: write a proof of the NEGATION of the above "
              "statement.\n% Disprove-mode: the manager judged the claim "
              "false and is constructing a counter-example or proof of "
              "\\lnot<claim>."),
    )
    out.write_text(content, encoding="utf-8")
    print(f"[orchestrator] created disprove-side tex stub: {out.name}",
          flush=True)


def cleanup_row_artefacts(row: dict, subsection_folder: Path) -> None:
    """Remove transient artefacts once a row is marked solved.

    Always:
    - ``workspace_<ref>.md`` -- the manager's scratchpad. Anything worth
      keeping should have been moved into Lean comments by the workers.
    - ``agent_registry`` -- cleared; past sessions are no longer needed.

    Claim-specific cleanup (only when both prove- and disprove-side
    files might exist):
    - ``proven=proven``: delete the disprove-side tex
      (``<ref>_disproof_<title>.tex``) and the disprove-side Lean
      (``<Title>Disproof.lean``) if present. Remove the disprove Lean
      file from ``row['lean_files']``.
    - ``proven=disproven``: delete the prove-side tex
      (``<ref>_proof_<title>.tex``) and the prove-side Lean (the
      original ``<Title>.lean``). Rewrite ``row['main_lean_file']`` to
      the disprove Lean if applicable, and drop the prove Lean from
      ``row['lean_files']``. The statement tex (``_statement_``) stays
      either way -- it represents the LN-side statement of the row and
      is mode-agnostic.

    The caller must ``save_data()`` after this to persist the cleared
    ``agent_registry`` and the (possibly rewritten) Lean file pointers.
    """
    wp = workspace_path_for_row(row, subsection_folder)
    if wp.exists():
        wp.unlink()
    row["agent_registry"] = []

    if row.get("def_or_claim") != "claim":
        return
    verdict = row.get("proven")
    if verdict not in ("proven", "disproven"):
        return

    tex_dir = subsection_folder / "tex"
    prove_tex   = tex_dir / _file_basename(row, "proof")
    disprove_tex = tex_dir / _file_basename(row, "disproof")
    title = row.get("title") or "Untitled"
    disprove_lean_path = subsection_folder / disprove_lean_filename(row)
    prove_lean_path = subsection_folder / f"{title}.lean"

    # Repo-relative form used by data.json's lean_files list.
    def _rel(p: Path) -> str:
        try:
            return str(p.relative_to(REPO_ROOT))
        except ValueError:
            return str(p)

    def _drop_path(paths: list, dead: str) -> list:
        return [p for p in paths if p != dead]

    if verdict == "proven":
        for p in (disprove_tex, disprove_lean_path):
            if p.exists():
                p.unlink()
                print(f"[orchestrator] cleanup: deleted {p.name} "
                      f"(verdict=proven; disprove side irrelevant)",
                      flush=True)
        dead = _rel(disprove_lean_path)
        if row.get("lean_files"):
            row["lean_files"] = _drop_path(row["lean_files"], dead)
        if row.get("main_lean_file") == dead:
            # Defensive: main_lean_file should never be the disprove
            # file when verdict=proven, but if some worker mis-pointed
            # it, repoint to whatever survives in lean_files.
            row["main_lean_file"] = (row.get("lean_files") or [""])[0]

    elif verdict == "disproven":
        for p in (prove_tex, prove_lean_path):
            if p.exists():
                p.unlink()
                print(f"[orchestrator] cleanup: deleted {p.name} "
                      f"(verdict=disproven; prove side irrelevant)",
                      flush=True)
        dead = _rel(prove_lean_path)
        if row.get("lean_files"):
            row["lean_files"] = _drop_path(row["lean_files"], dead)
        # Point main_lean_file at the surviving disprove Lean if it was
        # the prove file (the verifier reports whichever it confirmed;
        # repoint defensively in case it didn't).
        if row.get("main_lean_file") == dead:
            row["main_lean_file"] = _rel(disprove_lean_path)


def append_unsolved_run_summary(state: "OrchestrationState", reason: str) -> None:
    """Append a structured run-summary section to ``workspace_<ref>.md``
    so the *next* manager that picks this row up can see what was tried.

    Called from every exit path where the row was NOT marked solved (budget
    exhausted, MAX_TURNS hit, action-parse failure exhausted, request_from_human
    threshold). The summary records the action sequence, the row's current
    state, and which past agent sessions are resumable (from the registry).
    """
    section = state.row.get("section", "")
    if not section:
        return
    subsection_folder = ensure_subsection_folder(state.data_path.parent, section)
    wp = workspace_path_for_row(state.row, subsection_folder)

    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    elapsed_min = state.elapsed_seconds / 60

    # Compact action sequence -- one line per turn.
    if state.history:
        action_seq = "\n".join(
            f"  {t.turn_index:3d}. {t.action:24s}  "
            f"{summarise(t.worker_summary, 200) or '(no worker summary)'}"
            for t in state.history
        )
    else:
        action_seq = "  (no turns recorded -- exited before the first manager turn?)"

    # Latest verifier verdicts pulled from action history.
    verdicts = []
    for t in reversed(state.history):
        if t.action in VERIFIER_ACTIONS or t.action == "solved":
            v = re.search(r"VERDICT:\s*(PASS|FAIL)\b", t.worker_summary or "",
                          re.IGNORECASE)
            if v:
                verdicts.append(f"  {t.action} -> {v.group(1).upper()} (turn {t.turn_index})")
            if len(verdicts) >= 5:
                break
    verdicts_block = "\n".join(reversed(verdicts)) if verdicts else "  (none captured)"

    # The agent registry (caps to last 10 entries for readability).
    registry = state.row.get("agent_registry", []) or []
    if registry:
        reg_lines = "\n".join(
            f"  - {e['kind']:24s}  id={e['session_id']}  last={e.get('last_used','?')}"
            for e in registry[-10:]
        )
    else:
        reg_lines = "  (empty)"

    block = (
        f"\n---\n"
        f"## Run summary -- {stamp}\n"
        f"**Reason for stop:** {reason}\n"
        f"**Turns this run:** {len(state.history)}\n"
        f"**Elapsed:** {elapsed_min:.1f} min\n"
        f"**Row state at exit:** formalized={state.row.get('formalized')} "
        f"proven={state.row.get('proven')} solved={state.row.get('solved')}\n"
        f"\n### Action sequence\n{action_seq}\n"
        f"\n### Latest verifier verdicts\n{verdicts_block}\n"
        f"\n### Resumable past agents (most recent 10)\n{reg_lines}\n"
        f"\n### What the next manager should NOT repeat\n"
        f"_(Auto-recorded section. The next manager may overwrite this with a\n"
        f"sharper diagnosis once it has read above. The bullets below are a\n"
        f"heuristic from the action sequence -- treat them as hypotheses, not facts.)_\n"
        f"- Actions emitted this run, in order, are listed above. Re-running the\n"
        f"  same sequence is unlikely to help -- pick a different angle.\n"
        f"- If a verifier last reported FAIL, the feedback was inside its\n"
        f"  `BEGIN[feedback]…END[feedback]` block; read your history before\n"
        f"  dispatching the same verifier again.\n"
        f"- If you want to talk to a specific past agent, use `continue_agent`\n"
        f"  with one of the session ids above instead of spawning fresh.\n"
    )

    # Create the workspace file if it doesn't exist (defensive); then append.
    if not wp.exists():
        ensure_row_workspace(state.row, subsection_folder)
    wp.write_text(wp.read_text(encoding="utf-8") + block, encoding="utf-8")
    print(f"[orchestrator] run summary appended to "
          f"{wp.relative_to(state.data_path.parent.parent.parent)}",
          flush=True)


def regenerate_subsection_main_tex(data_path: Path, data: dict,
                                   section: str) -> None:
    """Rewrite ``<chapter_folder>/<Section>/tex/main.tex`` from the template,
    listing every row's subfile(s) in lecture-notes order via ``\\subfile``.

    All tex files (the aggregator main.tex AND every per-row subfile) live
    side-by-side in the ``tex/`` subfolder. That keeps the section root
    tidy (just Lean files + tex/) and makes both compile modes (the
    aggregate main.tex AND a standalone subfile) share the same
    pdflatex working directory, so relative-path includes (``\\input``)
    resolve consistently.

    For claim rows: only the ``_proof_`` subfile is included in main.tex --
    the ``_statement_`` subfile is excluded because the proof file already
    restates the statement at the top, and including both would duplicate.
    The standalone statement file remains on disk for grep / standalone
    rendering.

    Per-row subfile stubs are created on the fly if they don't yet exist.
    Rows whose ``title`` is empty are skipped here -- the orchestrator
    pre-fills the title for the *active* row at row start.
    """
    if not section:
        return
    ensure_preamble_at_leanification()
    subsection_folder = ensure_subsection_folder(data_path.parent, section)
    tex_dir = subsection_folder / "tex"
    tex_dir.mkdir(parents=True, exist_ok=True)
    includes: list[str] = []
    for row in data["rows"]:
        if row.get("section") != section or not row.get("title"):
            continue
        for p in ensure_row_subfiles(row, subsection_folder):
            # Skip claim _statement_ files: the corresponding _proof_ file
            # restates the statement above the proof, so including both
            # would duplicate inside main.pdf.
            if "_statement_" in p.name:
                continue
            # main.tex now lives inside tex/, so subfiles are siblings --
            # the \subfile path is just the bare stem.
            includes.append(f"\\subfile{{{p.stem}}}")
    chapter_title = data.get("title", "")
    main_tex = _render_template(
        "main",
        SECTION=section,
        SECTION_TITLE=chapter_title,
        SUBFILE_INCLUDES="\n".join(includes) + ("\n" if includes else ""),
    )
    (tex_dir / "main.tex").write_text(main_tex, encoding="utf-8")


# ---------------------------------------------------------------------------
# pdflatex builds (post-solve sanity checks)
# ---------------------------------------------------------------------------

# Timeout for a single latexmk invocation. TeX can hang on a pathological
# input; we cap it so a bad subfile cannot wedge the orchestrator.
LATEXMK_TIMEOUT_SECONDS = 120


def _latexmk_build(tex_file: Path) -> tuple[bool, str]:
    """Run ``latexmk -pdf`` on ``tex_file`` (cwd = its parent so relative
    ``\\input`` paths resolve). Returns ``(success, tail)``: ``success`` is
    True iff latexmk exited 0 AND a sibling ``<stem>.pdf`` exists, and
    ``tail`` is the last few lines of the build log (handy for diagnostics).
    Never raises -- a build is a best-effort cleanup-phase artefact.
    """
    try:
        result = subprocess.run(
            ["latexmk", "-pdf", "-interaction=nonstopmode",
             "-halt-on-error", tex_file.name],
            cwd=tex_file.parent,
            capture_output=True, text=True,
            timeout=LATEXMK_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return False, f"latexmk timed out after {LATEXMK_TIMEOUT_SECONDS}s"
    except FileNotFoundError:
        return False, "latexmk not found on PATH"
    pdf_path = tex_file.with_suffix(".pdf")
    ok = (result.returncode == 0) and pdf_path.exists()
    log_tail = "\n".join(
        (result.stdout + result.stderr).splitlines()[-12:]
    ) or "(empty latexmk output)"
    return ok, log_tail


def build_row_tex(row: dict, subsection_folder: Path) -> None:
    """Compile every per-row tex file (def: 1, claim: statement + proof) so
    that the row's PDFs are up-to-date as soon as the row is marked solved.
    Best-effort: a failing build is logged but does NOT block the orchestrator.
    """
    paths = _row_subfile_paths(row, subsection_folder)
    for p in paths:
        if not p.exists():
            print(f"[orchestrator] skip latexmk on missing {p.name}", flush=True)
            continue
        ok, tail = _latexmk_build(p)
        status = "ok" if ok else "FAILED"
        print(f"[orchestrator] latexmk {status}: {p.name}", flush=True)
        if not ok:
            print(f"    log tail:\n{tail}", flush=True)


def subsection_is_complete(data: dict, section: str) -> bool:
    """True iff at least one row in ``data`` belongs to ``section`` AND every
    such row has ``solved == "yes"``. Used to decide whether the subsection's
    aggregate ``main.tex`` should be rebuilt as a "you just finished a
    subsection" milestone.
    """
    if not section:
        return False
    rows = [r for r in data["rows"] if r.get("section") == section]
    return bool(rows) and all(r.get("solved") == "yes" for r in rows)


def build_subsection_main_tex(subsection_folder: Path) -> None:
    """Compile ``<subsection_folder>/tex/main.tex`` (the aggregator). Called
    when the last row of a subsection just got solved -- useful to confirm
    that all subfiles compose into a single document end-to-end. Best-effort.
    """
    main_tex = subsection_folder / "tex" / "main.tex"
    if not main_tex.exists():
        print(f"[orchestrator] no main.tex at {main_tex}, skipping subsection "
              f"build", flush=True)
        return
    ok, tail = _latexmk_build(main_tex)
    status = "ok" if ok else "FAILED"
    print(f"[orchestrator] subsection latexmk {status}: "
          f"{main_tex.parent.parent.name}/tex/main.tex", flush=True)
    if not ok:
        print(f"    log tail:\n{tail}", flush=True)


# ---------------------------------------------------------------------------
# per-row JSON for the website builder
# ---------------------------------------------------------------------------

# Lean declaration openers we care about when slicing the statement out
# of a ref-marker block.
_DECL_OPENER_RE = re.compile(
    r"^(theorem|lemma|example|def|abbrev|structure|class|instance|inductive)\b"
)
# `:= by` opener for theorem/lemma proofs. We trim the proof body at the
# first occurrence so the JSON's lean_statement is signature-only.
_PROOF_OPENER_RE = re.compile(r":=\s*by(\s|$)")
# Markdown-ish section header we use inside Lean docstrings to split the
# explanation from the design-choice rationale. Case-insensitive.
_DESIGN_HEADER_RE = re.compile(r"^\s*--+\s*##+\s*Design choice", re.IGNORECASE)


def _ref_marker_re(ref: str) -> re.Pattern[str]:
    """Compile a regex matching `-- <ref>`, `-- <ref> (part X/Y)`, or
    `-- <ref> (item N, ...)` -- all three patterns are emitted by the
    Lean-side workers when a row contributes more than one declaration.
    """
    return re.compile(
        r"^--\s+" + re.escape(ref) +
        r"(\s+\((part\s+\d+/\d+|item\s+\d+[^)]*)\))?\s*$"
    )


# Strict pattern matching the *next* ref marker for ANY ref (used to
# bound a slice when we don't know what ref comes next).
_ANY_REF_MARKER_RE = re.compile(
    r"^--\s+(def|claim)_\d+_\d+(\s+\([^)]+\))?\s*$"
)


# Declaration-head pattern that pulls the name out, e.g.
# `theorem foo` / `structure CDMG (α : Type*) where` / `def length`.
_DECL_HEAD_NAME_RE = re.compile(
    r"^(?P<kind>theorem|lemma|example|def|abbrev|structure|class|instance|inductive)"
    r"\s+(?P<name>[\w\u00A0-\uFFFF.]+)"
)


def _strip_lean_comment_markers(text: str) -> str:
    """Reduce a chunk of Lean source comments to plain prose.

    - drops `-- ` / `--` line prefixes,
    - removes `/-` and `-/` block markers (keeps the content between),
    - collapses runs of blank lines to a single blank line,
    - trims trailing whitespace.

    Lean code inside the chunk (rare in pre-declaration comments) is
    left as-is since stripping it would corrupt examples.
    """
    out: list[str] = []
    for ln in text.splitlines():
        s = ln
        s = re.sub(r"^/-+\s?", "", s)
        s = re.sub(r"\s?-/$", "", s)
        if s.startswith("--"):
            s = s[2:]
            if s.startswith(" "):
                s = s[1:]
        out.append(s.rstrip())
    # Collapse triple+ blank runs.
    collapsed: list[str] = []
    prev_blank = False
    for ln in out:
        is_blank = not ln.strip()
        if is_blank and prev_blank:
            continue
        collapsed.append(ln)
        prev_blank = is_blank
    return "\n".join(collapsed).strip()


def _split_explanation_design(comment_lines: list[str]
                              ) -> tuple[str, str]:
    """Split the pre-declaration comment block at the `## Design choice`
    header. Lines before the header become the explanation; lines after
    become the design-choices section. Either may be empty.
    """
    split_at = next(
        (i for i, ln in enumerate(comment_lines) if _DESIGN_HEADER_RE.search(ln)),
        None,
    )
    if split_at is None:
        return _strip_lean_comment_markers("\n".join(comment_lines)), ""
    explanation = _strip_lean_comment_markers(
        "\n".join(comment_lines[:split_at]))
    design = _strip_lean_comment_markers(
        "\n".join(comment_lines[split_at + 1 :]))
    return explanation, design


def build_for_website_prompt(row: dict, subsection_folder: Path) -> str:
    """Compose the one-shot prompt that asks a fresh worker to write
    ``<subsection_folder>/tex/<ref>_for_website.json``. Takes a bare row
    dict (not the full ``OrchestrationState``) so test scripts can drive
    the worker without a live orchestration session."""
    ref = row["ref"]
    tex_dir = subsection_folder / "tex"
    out_path = tex_dir / f"{ref}_for_website.json"
    title = row.get("title") or "Untitled"
    tex_stmt_path = (tex_dir
                     / (f"{ref}_{title}.tex"
                        if row["def_or_claim"] == "def"
                        else f"{ref}_statement_{title}.tex"))
    tex_proof_path = (
        tex_dir / f"{ref}_proof_{title}.tex"
        if row["def_or_claim"] == "claim" else None
    )
    context = (
        f"# Row context (orchestrator-supplied)\n"
        f"- ref:              {ref}\n"
        f"- title:            {row.get('title')}\n"
        f"- type:             {row.get('type')}\n"
        f"- def_or_claim:     {row.get('def_or_claim')}\n"
        f"- section:          {row.get('section')}\n"
        f"- main_lean_file:   {row.get('main_lean_file')}\n"
        f"- lean_files:       {row.get('lean_files')}\n"
        f"- tex statement:    {tex_stmt_path}\n"
        f"- tex proof:        {tex_proof_path or '(n/a)'}\n"
        f"- output path:      {out_path}\n"
    )
    return (
        f"{read_worker_prompt('produce_for_website.md')}\n\n"
        f"{context}\n"
    )


def run_for_website_worker(row: dict, subsection_folder: Path,
                           *, register_on_row: bool = True) -> None:
    """Two-stage post-solve dispatcher:

    1. **Stage B**: spawn the ``produce_for_website`` worker. The worker
       writes a *draft* JSON at the output path containing only
       ``{lean_explanation, design_choices, source_anchors}``.
    2. **Stage C**: read the draft, slice each anchor's Lean lines,
       concatenate into ``lean_code_with_comments``, strip comments to
       produce ``lean_code_without_comments``, bucket anchors by file
       to build ``lean_source_urls``, and overwrite the file with the
       full v3 JSON.

    Falls back to ``generate_for_website`` (mechanical) if the worker
    times out, fails to launch, doesn't write a parseable draft, or
    omits any of the three required draft fields.

    ``register_on_row=False`` skips appending to ``row['agent_registry']``
    -- useful for one-off test runs.
    """
    ref = row["ref"]
    out_path = subsection_folder / "tex" / f"{ref}_for_website.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    label = f"for_website_{ref}"

    # --- Stage B: spawn the worker ----------------------------------------
    try:
        _, sess = run_claude(
            build_for_website_prompt(row, subsection_folder),
            label=label,
        )
    except WorkerTimeoutError as e:
        print(f"[orchestrator] for_website worker timed out: {e}; "
              f"falling back to mechanical extractor.", flush=True)
        generate_for_website(row, subsection_folder)
        return
    except Exception as e:                # noqa: BLE001 -- best effort
        print(f"[orchestrator] for_website worker failed to launch: {e}; "
              f"falling back to mechanical extractor.", flush=True)
        generate_for_website(row, subsection_folder)
        return
    if register_on_row:
        _register_agent(row, kind="for_website", session_id=sess)

    if not out_path.exists():
        print(f"[orchestrator] worker didn't write {out_path.name}; "
              f"falling back to mechanical extractor.", flush=True)
        generate_for_website(row, subsection_folder)
        return

    # --- Stage C: post-process the draft ---------------------------------
    try:
        with open(out_path, encoding="utf-8") as fh:
            draft = json.load(fh)
    except (json.JSONDecodeError, OSError) as e:
        print(f"[orchestrator] worker draft JSON invalid ({e}); "
              f"falling back to mechanical extractor.", flush=True)
        generate_for_website(row, subsection_folder)
        return

    anchors = draft.get("source_anchors")
    explanation = draft.get("lean_explanation", "")
    design = draft.get("design_choices", "")
    if not isinstance(anchors, list) or not anchors:
        print(f"[orchestrator] worker draft missing source_anchors; "
              f"falling back to mechanical extractor.", flush=True)
        generate_for_website(row, subsection_folder)
        return
    if not isinstance(explanation, str) or not isinstance(design, str):
        print(f"[orchestrator] worker draft missing prose strings; "
              f"falling back to mechanical extractor.", flush=True)
        generate_for_website(row, subsection_folder)
        return

    payload = _v3_assemble(row, anchors, explanation, design)
    out_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"[orchestrator] for_website JSON written by worker: "
          f"{out_path.name} ({len(anchors)} anchors, "
          f"{len(payload['lean_source_urls'])} url(s))", flush=True)


def _code_lines_mask(text: str) -> list[bool]:
    """Parallel mask of ``text.splitlines()``: ``True`` iff the line
    *starts* outside any ``/- ... -/`` block comment. Lines whose only
    content is a ``--`` line-comment are still ``True`` because they're
    at depth zero -- ref-marker comments are flagged ``True`` and the
    declaration-head regex naturally won't match them.
    """
    lines = text.splitlines()
    mask: list[bool] = []
    depth = 0
    for ln in lines:
        mask.append(depth == 0)
        i = 0
        n = len(ln)
        while i < n:
            if ln.startswith("/-", i):
                depth += 1
                i += 2
            elif ln.startswith("-/", i) and depth > 0:
                depth -= 1
                i += 2
            elif depth == 0 and ln.startswith("--", i):
                break          # rest of line is a line comment
            else:
                i += 1
    return mask


def _find_all_marker_blocks(text: str, ref: str
                            ) -> list[tuple[int, int, int]]:
    """Return ``[(marker_idx, decl_idx, end_idx), ...]`` for every
    ``-- <ref>`` marker (any sub-form: bare, `(part X/Y)`, `(item N, ...)`)
    in ``text``. ``end_idx`` is the line where the slice should stop
    (the next marker for any ref, or end of file).

    Declaration heads inside ``/- ... -/`` block comments are ignored,
    so prose like ``def 3.4 item 1:`` embedded in a docstring doesn't
    masquerade as a Lean declaration.
    """
    lines = text.splitlines()
    code = _code_lines_mask(text)
    marker = _ref_marker_re(ref)
    blocks: list[tuple[int, int, int]] = []
    marker_idxs = [i for i, ln in enumerate(lines) if marker.match(ln)]
    for m_idx in marker_idxs:
        decl_idx = None
        for j in range(m_idx + 1, len(lines)):
            if code[j] and _DECL_OPENER_RE.match(lines[j]):
                decl_idx = j
                break
            if _ANY_REF_MARKER_RE.match(lines[j]) and j != m_idx:
                break
        if decl_idx is None:
            continue
        end_idx = len(lines)
        for j in range(decl_idx + 1, len(lines)):
            if _ANY_REF_MARKER_RE.match(lines[j]):
                end_idx = j
                break
        blocks.append((m_idx, decl_idx, end_idx))
    return blocks


def _trim_statement(lines: list[str], decl_idx: int, end_idx: int) -> str:
    """Take the declaration starting at ``decl_idx`` and trim:
    - theorem / lemma / example: stop at the line containing ``:= by``
      (kept), drop the tactic block;
    - structure / def / abbrev / class / instance / inductive: keep
      everything up to ``end_idx``.
    """
    head = _DECL_OPENER_RE.match(lines[decl_idx])
    kind = head.group(1) if head else ""
    is_thm = kind in {"theorem", "lemma", "example"}
    out: list[str] = []
    for j in range(decl_idx, end_idx):
        out.append(lines[j])
        if is_thm and _PROOF_OPENER_RE.search(lines[j]):
            break
    return "\n".join(out).rstrip()


def _parse_decl_head(line: str) -> tuple[str, str]:
    """Extract ``(kind, name)`` from a declaration head line. Returns
    ``("", "")`` if the line isn't a recognised declaration."""
    m = _DECL_HEAD_NAME_RE.match(line)
    return (m.group("kind"), m.group("name")) if m else ("", "")


# ---------------------------------------------------------------------------
# Stage A / D helpers for the v3 for-website pipeline
# ---------------------------------------------------------------------------

def strip_lean_comments(text: str) -> str:
    """Stage D: drop every Lean comment from ``text``.

    Handles:
    - ``--`` line comments (outside any block; rest of line dropped).
    - ``/- ... -/`` block comments (Lean 4 allows nesting; depth counted).
    - ``/-- ... -/`` doc comments (treated identically to ``/- -/`` --
      they're still comments, just with a different opener).

    After the pass, collapses runs of 3+ blank lines into one blank
    line and trims trailing whitespace per line.
    """
    out_chars: list[str] = []
    depth = 0
    i, n = 0, len(text)
    while i < n:
        # Block-comment openers (/- and /-- both add depth 1).
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        # Line-comment outside any block.
        if text.startswith("--", i):
            nl = text.find("\n", i)
            i = nl if nl != -1 else n
            continue
        out_chars.append(text[i])
        i += 1
    stripped = "".join(out_chars)
    # Collapse blank-line runs and trim trailing whitespace per line.
    lines = [ln.rstrip() for ln in stripped.splitlines()]
    cleaned: list[str] = []
    blank_run = 0
    for ln in lines:
        if ln == "":
            blank_run += 1
            if blank_run > 1:
                continue
        else:
            blank_run = 0
        cleaned.append(ln)
    # Trim leading/trailing blank lines.
    while cleaned and cleaned[0] == "":
        cleaned.pop(0)
    while cleaned and cleaned[-1] == "":
        cleaned.pop()
    return "\n".join(cleaned)


_GITHUB_URL_TEMPLATE_CACHE: str | None = None


def github_url_template() -> str:
    """Stage A: build (and cache) the GitHub blob-URL template for the
    current repo + branch. Returns a string with ``{path}``, ``{start}``,
    ``{end}`` placeholders ready for ``.format(...)``.

    Output shape::

        https://github.com/<slug>/blob/<branch>/{path}#L{start}-L{end}

    Falls back to a no-op template if git isn't reachable -- callers
    write the JSON anyway with file-relative paths that are still useful.
    """
    global _GITHUB_URL_TEMPLATE_CACHE
    if _GITHUB_URL_TEMPLATE_CACHE is not None:
        return _GITHUB_URL_TEMPLATE_CACHE
    try:
        remote = subprocess.check_output(
            ["git", "remote", "get-url", "origin"],
            cwd=str(REPO_ROOT), text=True,
        ).strip()
        m = (re.match(r"git@github\.com:(.+?)(?:\.git)?$", remote)
             or re.match(r"https://github\.com/(.+?)(?:\.git)?$", remote))
        slug = m.group(1) if m else "unknown/unknown"
        branch = subprocess.check_output(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=str(REPO_ROOT), text=True,
        ).strip() or "main"
    except Exception:                            # noqa: BLE001
        slug, branch = "unknown/unknown", "main"
    _GITHUB_URL_TEMPLATE_CACHE = (
        f"https://github.com/{slug}/blob/{branch}/{{path}}#L{{start}}-L{{end}}"
    )
    return _GITHUB_URL_TEMPLATE_CACHE


def _doc_comment_start(lines: list[str], decl_idx: int) -> int:
    """If a ``/-- ... -/`` doc comment immediately precedes the line at
    ``decl_idx`` (no intervening blank lines), return the index of its
    opening ``/--`` line. Otherwise return ``decl_idx`` unchanged.

    The doc comment may span one line (``/-- foo -/``) or several
    (``/-- foo\\n bar -/``). We walk backwards looking for the line that
    opens it.
    """
    j = decl_idx - 1
    if j < 0 or not lines[j].rstrip():
        return decl_idx
    # The line immediately above must end the doc comment.
    if "-/" not in lines[j]:
        return decl_idx
    # Walk up until we find the opener.
    while j >= 0:
        if "/--" in lines[j]:
            return j
        if "/-" in lines[j] and "/--" not in lines[j]:
            # It's a regular block comment, not a doc comment -- skip.
            return decl_idx
        j -= 1
    return decl_idx


def _anchor_end_line(lines: list[str], decl_idx: int, end_idx: int) -> int:
    """Compute a tight 1-indexed end-line for the declaration at
    ``decl_idx``, bounded by ``end_idx`` (the line where the next
    ref-marker begins).

    Trims trailing blank lines from the slice -- they're not part of
    the declaration body.
    """
    last = end_idx - 1
    while last > decl_idx and not lines[last].strip():
        last -= 1
    return last + 1                              # 1-indexed inclusive


def _anchors_from_marker_blocks(text: str, main_lean_file: str, ref: str
                                ) -> list[dict]:
    """Mechanical fallback for ``source_anchors``: scan ``text`` for
    ``-- <ref>`` markers (any sub-form), turn each into a v3 anchor with
    a doc-comment-extended ``line_start`` and a tight ``line_end``.
    """
    lines = text.splitlines()
    out: list[dict] = []
    for _marker_idx, decl_idx, end_idx in _find_all_marker_blocks(text, ref):
        start_idx = _doc_comment_start(lines, decl_idx)
        kind, name = _parse_decl_head(lines[decl_idx])
        title = name or kind or "(decl)"
        out.append({
            "title":          title,
            "lean_file_path": main_lean_file,
            "line_start":     start_idx + 1,     # 1-indexed
            "line_end":       _anchor_end_line(lines, decl_idx, end_idx),
        })
    return out


def _v3_assemble(row: dict, anchors: list[dict],
                 lean_explanation: str, design_choices: str,
                 ) -> dict:
    """Stage C: assemble the final for-website JSON from the LLM's
    (or mechanical fallback's) outputs.

    - ``lean_code_with_comments`` = each anchor's slice, joined by ``\\n\\n``.
    - ``lean_code_without_comments`` = the above through ``strip_lean_comments``.
    - ``lean_source_urls`` = list of ``{title, url}``, one per unique
      ``lean_file_path``, with title = file basename and URL covering
      ``[min line_start, max line_end]`` across anchors in that file.
    """
    tmpl = github_url_template()

    # 1) Slice + concat. Anchors that point outside the file are clamped.
    code_chunks: list[str] = []
    by_file: dict[str, list[dict]] = {}
    for a in anchors:
        path = a.get("lean_file_path") or ""
        abs_path = REPO_ROOT / path
        if not abs_path.exists():
            print(f"[for_website] anchor file missing: {path}; skipping "
                  f"this anchor.", flush=True)
            continue
        flines = abs_path.read_text(encoding="utf-8").splitlines()
        s = max(1, int(a.get("line_start") or 1))
        e = min(len(flines), int(a.get("line_end") or len(flines)))
        if e < s:
            print(f"[for_website] anchor {a.get('title')!r} has bad range "
                  f"{s}..{e}; skipping.", flush=True)
            continue
        code_chunks.append("\n".join(flines[s - 1 : e]))
        # Normalize the anchor's stored range for URL bucketing below.
        a["_resolved_path"]  = path
        a["_resolved_start"] = s
        a["_resolved_end"]   = e
        by_file.setdefault(path, []).append(a)

    lean_code_with_comments = "\n\n".join(code_chunks)
    lean_code_without_comments = strip_lean_comments(lean_code_with_comments)

    # 2) Build the URL list -- one entry per unique file, in first-
    # appearance order, title = basename, range = union of anchors.
    url_list: list[dict] = []
    for path, group in by_file.items():
        start = min(a["_resolved_start"] for a in group)
        end   = max(a["_resolved_end"]   for a in group)
        url_list.append({
            "title": Path(path).name,
            "url":   tmpl.format(path=path, start=start, end=end),
        })

    return {
        "ref":              row["ref"],
        "title":            row.get("title", ""),
        "type":             row.get("type", ""),
        "def_or_claim":     row.get("def_or_claim", ""),
        "section":          row.get("section", ""),
        "lean_file_path":   row.get("main_lean_file", ""),
        "lean_code_with_comments":    lean_code_with_comments,
        "lean_code_without_comments": lean_code_without_comments,
        "lean_explanation": lean_explanation,
        "design_choices":   design_choices,
        "lean_source_urls": url_list,
    }


def generate_for_website(row: dict, subsection_folder: Path) -> None:
    """**Fallback** post-solve helper: write
    ``<subsection_folder>/tex/<ref>_for_website.json`` using mechanical
    extraction only -- no LLM. Used when the worker times out, fails to
    launch, or emits invalid JSON.

    Anchors are derived from the in-file ``-- <ref>`` markers in
    ``main_lean_file``. Each anchor's ``line_start`` extends back over
    any ``/-- ... -/`` doc comment immediately above the declaration;
    its ``line_end`` is the last non-blank line before the next
    ref-marker.

    Prose fields (``lean_explanation`` and ``design_choices``) are
    populated from the raw pre-declaration comment text -- the
    ``## Design choice`` block splits explanation from design choices.
    Prose is therefore *raw* rather than polished; the user can
    regenerate the row via the worker later to upgrade prose quality.
    """
    main_lean = row.get("main_lean_file") or ""
    ref = row["ref"]
    tex_dir = subsection_folder / "tex"
    out_path = tex_dir / f"{ref}_for_website.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)

    anchors: list[dict] = []
    explanation = design = ""

    if main_lean:
        lean_abs = REPO_ROOT / main_lean
        if lean_abs.exists():
            text = lean_abs.read_text(encoding="utf-8")
            anchors = _anchors_from_marker_blocks(text, main_lean, ref)
            # Aggregate comment text between markers and declarations
            # for raw prose. Splits at the `## Design choice` header.
            lines = text.splitlines()
            all_comments: list[str] = []
            for marker_idx, decl_idx, _end_idx in (
                    _find_all_marker_blocks(text, ref)):
                comments = lines[marker_idx + 1 : decl_idx]
                if comments and re.match(r"^--\s*title:", comments[0]):
                    comments = comments[1:]
                all_comments.extend(comments)
                all_comments.append("")
            explanation, design = _split_explanation_design(all_comments)

    payload = _v3_assemble(row, anchors, explanation, design)
    out_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"[orchestrator] wrote for-website JSON (fallback): "
          f"{out_path.name} ({len(anchors)} anchors)", flush=True)


# ---------------------------------------------------------------------------
# Hard sorry-check before mark_solved
# ---------------------------------------------------------------------------

# Generous cap for the lake-build invocation inside check_no_sorry --
# Mathlib + the whole leanification together can take several minutes
# on a cold cache. If it exceeds this, we skip the build-side check
# (a fast file-grep still ran first) and let the orchestrator continue
# rather than wedge.
SORRY_CHECK_BUILD_TIMEOUT_SECONDS = 15 * 60

# Source positions that look like *real* sorry usage (not comment text
# documenting historical sorry presence). A line-anchored regex with a
# `\bsorry\b` boundary and excluding lines that are entirely a comment.
# Matches: `:= sorry`, `by sorry`, `· sorry`, bare `sorry` on its own
# line, `sorry` followed by `;` or whitespace, etc. Does NOT match: any
# occurrence inside a `--` line comment or a `/- … -/` block comment
# (we use Stage D's depth-aware stripper to elide comments first).
_SORRY_TOKEN_RE = re.compile(r"\bsorry\b")


def _file_has_sorry(lean_path: Path) -> bool:
    """Return True iff the Lean file at ``lean_path`` contains a
    ``sorry`` token OUTSIDE any comment. Uses ``strip_lean_comments``
    (the Stage D state-machine that respects nested ``/- -/``, ``/-- -/``,
    and line ``--`` comments) to elide comment text before searching,
    so design-block prose like ``-- Body = sorry`` does not trip it.
    """
    try:
        text = lean_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return False                  # can't read = can't be sure; defer to build
    code_only = strip_lean_comments(text)
    return bool(_SORRY_TOKEN_RE.search(code_only))


def check_no_sorry(lean_files: list[str]) -> str | None:
    """Hard pre-`mark_solved` gate: confirm none of the row's Lean
    files admits via sorry. Two-stage check:

    1. **Fast file-grep**: read each Lean file, strip comments, search
       for a `sorry` token. Catches the common case (worker accidentally
       leaves a `sorry` in the body) without needing to invoke `lake`.
    2. **`lake build` warning scan**: run `lake build` from the repo
       root, parse the output for `declaration uses 'sorry'` warnings
       attributed to any of the row's Lean files. Catches the harder
       case where a theorem transitively depends on a sorry that isn't
       in its own body (a `def` returning sorry that the theorem then
       uses, etc.).

    Returns ``None`` on clean (proceed with mark_solved); otherwise a
    short multi-line string describing what was found, suitable for the
    manager's ``extra_note``.

    Deliberately *narrow*: only checks the one thing that is absolutely
    forbidden (sorry / admit). Does not warn about style, deprecations,
    user-introduced axioms, etc. -- those are for the manager / verifier
    to judge, not the orchestrator to block on.
    """
    # --- Stage 1: file-grep -------------------------------------------
    grep_hits: list[str] = []
    for lf in lean_files:
        p = REPO_ROOT / lf
        if not p.exists():
            continue
        if _file_has_sorry(p):
            grep_hits.append(lf)
    if grep_hits:
        return (
            "Hard sorry-check FAILED: the verifier said PASS but "
            "Python grep'd a `sorry` token (outside any comment) in:\n"
            + "\n".join(f"  - {h}" for h in grep_hits)
            + "\nA solved row must have NO `sorry` in any proof body. "
            "Discharge it (or `mistake`/`unmistake` to switch direction) "
            "before re-emitting `solved`."
        )

    # --- Stage 2: lake build warning scan -----------------------------
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=str(REPO_ROOT),
            capture_output=True, text=True,
            timeout=SORRY_CHECK_BUILD_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        # Build is slow but file-grep already passed; let it through with
        # a log note rather than block the solve indefinitely.
        print(f"[orchestrator] sorry-check `lake build` timed out after "
              f"{SORRY_CHECK_BUILD_TIMEOUT_SECONDS}s; relying on file-grep "
              f"clean.", flush=True)
        return None
    except FileNotFoundError:
        print("[orchestrator] sorry-check: `lake` not on PATH; relying on "
              "file-grep clean.", flush=True)
        return None

    blob = (result.stdout or "") + (result.stderr or "")
    if result.returncode != 0:
        # Build broke entirely. The verifier should never have PASSed.
        # Surface the tail to the manager.
        tail = "\n".join(blob.splitlines()[-15:]) or "(empty)"
        return (
            f"Hard sorry-check FAILED: `lake build` exited "
            f"{result.returncode} -- the verifier said PASS but the "
            f"repo doesn't compile. Tail:\n{tail}"
        )

    # Find every "declaration uses 'sorry'" warning + the file it refers
    # to. Lake's format: `warning: ./path/to/File.lean:LINE:COL: ...`.
    sorry_warning_re = re.compile(
        r"(?:warning|error):\s+\.?/?(\S+\.lean):\d+:\d+:.*sorry",
        re.IGNORECASE,
    )
    row_files = {lf.lstrip("./") for lf in lean_files}
    bad: list[str] = []
    for line in blob.splitlines():
        m = sorry_warning_re.search(line)
        if not m:
            continue
        hit_path = m.group(1).lstrip("./")
        if any(hit_path.endswith(rf) or hit_path == rf for rf in row_files):
            bad.append(line.strip())
    if bad:
        return (
            "Hard sorry-check FAILED: `lake build` succeeded but emitted "
            "`uses 'sorry'` warnings on this row's files:\n"
            + "\n".join(f"  - {b}" for b in bad[:10])
            + ("\n  ... (truncated)" if len(bad) > 10 else "")
            + "\nDischarge the sorry (or `mistake`/`unmistake` to switch "
            "direction) before re-emitting `solved`."
        )
    return None


# ---------------------------------------------------------------------------
# Strict-equivalence solved-gate
# ---------------------------------------------------------------------------
#
# After the friendly `verify_row_solved` worker PASSes and the hard
# sorry-check is clean, we run the adversarial, default-strict
# equivalence checker against the row's main Lean file vs the LN
# tex_block. This is the production-loop counterpart to
# `extras/audit_chapter.py`'s offline sweep -- it catches the
# disjoint_EL -> marginalize -> claim_3_25 style CONTENT deviation that
# the friendly checker missed on the way in.
#
# On EXAMPLE_GENERATION verdict, the property-based example verifier is
# auto-chained (the strict checker explicitly defers to instances for
# new operators / structures). The combined verdict gates `mark_solved`.
#
# Bypassed when the manager has just emitted `accept_deviation`
# (manager has explicitly registered the deviation and acknowledged the
# tradeoff). Worker errors propagate as "let through with a log line" --
# a flaky worker should not permanently freeze a row's solve.

def _run_solved_gate_strict_check(state: "OrchestrationState",
                                  row_for_check: dict) -> str | None:
    """Return an ``extra_note`` string for the manager if the strict
    check (and, if applicable, the chained example verifier) flagged a
    CONTENT deviation that should block `mark_solved`. Return ``None``
    when the gate is clear (PASS / PRESENTATION / EXAMPLE_GENERATION+PASS,
    or worker ERROR/MISSING which we let through).

    ``row_for_check`` is a copy of ``state.row`` with `lean_files` and
    `main_lean_file` synced to what the verifier just reported (the
    persisted row hasn't been updated by `mark_solved` yet).
    """
    # Local imports: keep audit_helpers off the cold-import path for the
    # rest of solve_chapter (this code only runs on `solved` attempts).
    from audit_helpers import (                              # type: ignore
        run_strict_equivalence_checker, run_example_verifier,
    )

    ref = row_for_check.get("ref")
    print(f"[orchestrator] strict-equivalence gate: running on {ref} ...",
          flush=True)
    # Retry-once on ERROR/MISSING: a single transient subprocess
    # hiccup or a verdict-format wobble shouldn't decide whether a
    # CONTENT deviation slips through. After two attempts we still
    # fall through (default-permissive) -- a persistently broken
    # worker is logged so the audit script can flag the row offline.
    strict = run_strict_equivalence_checker(row_for_check)
    v = strict.get("verdict")
    if v in ("MISSING", "ERROR"):
        print(f"[orchestrator] strict-equivalence verdict={v} on first "
              f"try; retrying once.", flush=True)
        strict = run_strict_equivalence_checker(row_for_check)
        v = strict.get("verdict")
    dc = strict.get("deviation_class")
    print(f"[orchestrator] strict-equivalence verdict: {v} "
          f"(deviation_class={dc})", flush=True)

    if v == "PASS":
        # Includes both DEVIATION_CLASS=NONE and =PRESENTATION. The
        # strict checker has already judged the deviation harmless.
        return None
    if v in ("MISSING", "ERROR"):
        print(f"[orchestrator] strict-equivalence worker returned {v} "
              f"after retry; letting the solve through (default-"
              f"permissive on worker failure -- the audit script will "
              f"re-run this row offline).", flush=True)
        return None
    if v == "EXAMPLE_GENERATION":
        print(f"[orchestrator] strict-equivalence requested examples; "
              f"dispatching verify_with_examples worker.", flush=True)
        examples = run_example_verifier(
            row_for_check, strict_reason=strict.get("feedback") or "")
        ev = examples.get("verdict")
        if ev in ("MISSING", "ERROR"):
            print(f"[orchestrator] example-verifier verdict={ev} on first "
                  f"try; retrying once.", flush=True)
            examples = run_example_verifier(
                row_for_check, strict_reason=strict.get("feedback") or "")
            ev = examples.get("verdict")
        print(f"[orchestrator] example-verifier verdict: {ev} "
              f"(instances_checked={examples.get('instances_checked')})",
              flush=True)
        if ev == "PASS":
            return None
        if ev in ("MISSING", "ERROR"):
            print(f"[orchestrator] example-verifier returned {ev} after "
                  f"retry; letting the solve through (default-permissive "
                  f"on worker failure).", flush=True)
            return None
        # ev == "FAIL"
        return _format_strict_gate_failure(strict, examples)

    # v == "FAIL"
    return _format_strict_gate_failure(strict, None)


def _format_strict_gate_failure(strict: dict, examples: dict | None
                                ) -> str:
    """Render the strict-checker (and optional example-verifier)
    findings into an extra_note block telling the manager what was
    detected and what to do about it."""
    lines = [
        "**Strict-equivalence solved-gate FAILED.**",
        "",
        "After `verify_row_solved` PASSed and the sorry-check was clean, "
        "the orchestrator ran the *adversarial, default-strict* "
        "equivalence checker on this row's Lean encoding vs the LN "
        "`tex_block`. It found a CONTENT deviation -- the Lean encoding "
        "states different mathematics than the LN does (not just a "
        "different syntactic packaging).",
        "",
        f"**Strict checker verdict**: {strict.get('verdict')} "
        f"(deviation_class={strict.get('deviation_class')}"
        + (f", root_cause={strict.get('root_cause')}"
           if strict.get('root_cause') else "")
        + ")",
        "",
        "**Strict checker feedback:**",
        strict.get("feedback") or "(no feedback body)",
    ]
    if examples is not None:
        lines += [
            "",
            f"**Example verifier was auto-chained and verdict was**: "
            f"{examples.get('verdict')} "
            f"(instances_checked={examples.get('instances_checked')})",
            "",
            "**Example verifier feedback:**",
            examples.get("feedback") or "(no feedback body)",
        ]
    lines += [
        "",
        "**Your options on the next turn:**",
        "",
        "- **Fix the encoding** (preferred). Re-dispatch the formalizer / "
        "leanifier with the strict-checker's feedback so the Lean shape "
        "matches the LN's. After fix, re-emit `solved` -- the strict gate "
        "will re-run.",
        "- **Accept the deviation** (only if you're sure the deviation "
        "is intentional and the LN's literal form is impractical / "
        "unnatural in Lean). Use the new `accept_deviation` action; the "
        "body should describe the deviation in register-entry form "
        "(see manager.md). The orchestrator will write it to "
        "`leanification/deviations.json` and bypass the strict gate on "
        "your *next* `solved` attempt. **Do not** abuse this -- "
        "registered deviations propagate to every consumer.",
        "- If the root_cause is `upstream:<ref>` the right move is "
        "almost certainly `refactor <upstream_ref>` rather than accepting "
        "the deviation here. (A registered deviation in an upstream type "
        "leaks into every downstream consumer; refactoring the upstream "
        "is what closes the leak.)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# accept_deviation body parser
# ---------------------------------------------------------------------------

# Keys recognised in an `accept_deviation` action body. Matched
# case-insensitively, one per line. `notes` is special: everything from
# the `notes:` line to end-of-body is captured (so multi-line notes
# work without escaping).
_ACCEPT_DEVIATION_KEYS = (
    "id", "introduced_by_ref", "breaks", "preserves",
    "at_risk_pattern", "tags",
)


def _parse_accept_deviation_body(body: str, default_ref: str) -> dict:
    """Parse the manager's `accept_deviation` body into a register entry
    dict. Required keys: ``id``, ``breaks``, ``preserves``,
    ``at_risk_pattern``. Optional: ``introduced_by_ref`` (defaults to
    ``default_ref``), ``tags`` (comma-separated -> list), ``notes`` (last
    block, runs to end of body).

    Raises ``ValueError`` if any required key is missing or empty.
    """
    if not body or not body.strip():
        raise ValueError("body is empty")
    lines = body.splitlines()
    entry: dict = {}
    notes_start: int | None = None
    # First pass: per-line key/value scrape; spot the start of the
    # `notes` block.
    for i, raw in enumerate(lines):
        line = raw.rstrip()
        m = re.match(r"^\s*([A-Za-z_][A-Za-z_0-9]*)\s*:\s*(.*)$", line)
        if not m:
            continue
        key = m.group(1).lower()
        val = m.group(2).strip()
        if key == "notes":
            notes_start = i
            break  # everything after this is the notes blob
        if key in _ACCEPT_DEVIATION_KEYS:
            entry[key] = val
    # Notes blob: everything after the `notes:` line, joined verbatim.
    if notes_start is not None:
        first_line = lines[notes_start].split(":", 1)[1].lstrip()
        rest_lines = lines[notes_start + 1:]
        # Footgun guard: if any of the other recognised keys appears as
        # a "key:" line INSIDE the notes blob, it would be silently
        # consumed and never parsed -- so the manager would think they
        # set `tags:` but the entry would have none. Refuse and tell
        # them to put `notes:` last.
        stray_re = re.compile(
            r"^\s*("
            + "|".join(k for k in _ACCEPT_DEVIATION_KEYS if k != "notes")
            + r")\s*:",
            re.IGNORECASE,
        )
        for j, l in enumerate(rest_lines, start=notes_start + 2):
            if stray_re.match(l):
                raise ValueError(
                    f"line {j} of the body contains a recognised key "
                    f"({stray_re.match(l).group(1)!r}) inside the `notes` "
                    f"blob -- `notes:` must be the LAST recognised key, "
                    f"because everything after it is captured verbatim. "
                    f"Move the stray key above the `notes:` line."
                )
        rest = "\n".join(rest_lines).rstrip()
        entry["notes"] = (first_line + ("\n" + rest if rest else "")).strip()
    # Backfills + type coercions.
    entry.setdefault("introduced_by_ref", default_ref)
    tags_raw = entry.get("tags", "")
    if isinstance(tags_raw, str):
        entry["tags"] = [t.strip() for t in tags_raw.split(",") if t.strip()]
    # Always add the source tag so the human can grep for manager-
    # accepted entries later.
    entry["tags"] = list(entry.get("tags") or []) + ["manager-accepted"]
    # Validate required fields.
    required = ("id", "breaks", "preserves", "at_risk_pattern")
    missing = [k for k in required if not entry.get(k)]
    if missing:
        raise ValueError(
            f"body missing required key(s): {missing}; got "
            f"{sorted(entry.keys())}")
    return entry


# ---------------------------------------------------------------------------
# Mistake sweep: two-stage gate before honoring a `mistake` action
# ---------------------------------------------------------------------------
#
# The lesson from claim_3_25: a manager that emits `mistake` is more
# often pointing at an encoding deviation than at a genuinely false
# LN claim. Before the orchestrator commits the row to disprove mode
# (which is sticky and expensive to undo), it walks the manager through
# two checks:
#
#   Stage 1 (deterministic, free): scan the deviation register for any
#     entry whose `introduced_by_ref` is a def the claim cites, or
#     whose `at_risk_pattern` keywords syntactically match the claim's
#     tex body. If matches: surface to manager; do NOT honor.
#
#   Stage 2 (LLM worker, slower): dispatch the
#     `verify_no_undocumented_deviation` worker against the claim and
#     its cited defs. If it reports an undocumented CONTENT deviation
#     in any cited def: surface to manager; do NOT honor.
#
# After each surfaced finding the manager's next turn decides what to
# do; if they re-emit `mistake`, the orchestrator moves to the next
# stage (or honors the mistake if both stages have already been done).
# The manager is NEVER permanently blocked -- both stages are one-shot
# per row run.

# Refs cited in a claim's tex are written either as `\refrow{def_X_Y}`
# (modern style) or `\refrow{claim_X_Y}`, or just mentioned as bare
# `def_X_Y` / `claim_X_Y` strings in escaped-underscore form. Match all
# of those so Stage 1's heuristic doesn't miss citations.
_CITED_REF_RE = re.compile(
    r"\\refrow\{((?:def|claim)_\d+_\d+)\}"
    r"|(?<![A-Za-z0-9_\\])"
    r"((?:def|claim)\\?_\d+\\?_\d+)"
    r"(?![A-Za-z0-9_])"
)


def _extract_cited_refs(text: str) -> list[str]:
    """Return the de-duplicated list of refs (`def_X_Y` / `claim_X_Y`)
    mentioned in ``text``. Handles both ``\\refrow{ref}`` and bare
    `def_3_10` / `claim\\_3\\_4` mentions."""
    out: list[str] = []
    seen: set[str] = set()
    for m in _CITED_REF_RE.finditer(text or ""):
        raw = m.group(1) or m.group(2) or ""
        ref = raw.replace("\\_", "_")
        if ref and ref not in seen:
            seen.add(ref)
            out.append(ref)
    return out


def _gather_claim_body_text(row: dict, subsection_folder: Path) -> str:
    """Concatenate the row's `tex_block` (statement) and the row's
    current tex proof / disproof file contents. Stage 1 scans this
    combined text for citations and deviation-register keyword hits."""
    parts: list[str] = [row.get("tex_block") or ""]
    if row.get("def_or_claim") == "claim":
        title = row.get("title") or "Untitled"
        for suffix in ("proof", "disproof"):
            p = subsection_folder / "tex" / f"{row['ref']}_{suffix}_{title}.tex"
            if p.exists():
                try:
                    parts.append(p.read_text(encoding="utf-8"))
                except (OSError, UnicodeDecodeError):
                    pass
    return "\n".join(parts)


def mistake_stage1_register_scan(row: dict, subsection_folder: Path
                                 ) -> list[dict]:
    """Stage 1: scan the deviation register for entries relevant to
    this row's claim. Returns the matching register entries (possibly
    empty). Deterministic, no LLM call.

    Relevance is computed by two heuristics:

    - **Citation match**: any entry whose ``introduced_by_ref`` is a def
      ref the claim's tex cites (via `\\refrow{def_X_Y}` or a bare
      mention).
    - **Pattern keyword match**: any entry whose ``at_risk_pattern``
      contains keywords (length >= 5) that appear in the claim's tex
      body. Coarse but conservative -- prefers false positives over
      false negatives.
    """
    # Local import to avoid bootstrap cycle (deviations.py imports nothing
    # from solve_chapter, but importing solve_chapter from elsewhere
    # shouldn't drag deviations in unless this function is called).
    from deviations import find_at_risk_for_claim
    body = _gather_claim_body_text(row, subsection_folder)
    cited = _extract_cited_refs(body)
    return find_at_risk_for_claim(body, defs_cited=cited)


def _format_stage1_findings(findings: list[dict]) -> str:
    """Render Stage 1's register matches into a human-readable extra_note
    block for the manager. Doesn't tell the manager what to decide --
    just surfaces the evidence."""
    lines = [
        "**Stage 1 (register scan) of the mistake-sweep surfaced these "
        "recorded upstream deviations as potentially explaining why your "
        "proof attempt failed.** Before the orchestrator commits this "
        "row to disprove mode, take a moment to consider whether the "
        "*encoding* is the culprit rather than the LN claim:",
        "",
    ]
    for e in findings:
        lines.append(
            f"- **{e.get('id')}** (introduced by `{e.get('introduced_by_ref')}`):\n"
            f"  - **breaks**: {e.get('breaks')}\n"
            f"  - **preserves**: {e.get('preserves')}\n"
            f"  - **at-risk pattern**: {e.get('at_risk_pattern')}\n"
        )
    lines += [
        "",
        "**Your options on the next turn**:",
        "- If one of these deviations really does explain the apparent falsity, "
        "the right action is `refactor <ref>` on the offending upstream def "
        "(not `mistake` on this claim).",
        "- If you've reviewed the deviations and you're confident they don't "
        "apply to this proof, re-emit `mistake` with a one-paragraph rationale "
        "explaining why. The orchestrator will then proceed to Stage 2 "
        "(an LLM sweep for undocumented deviations). After Stage 2 the "
        "mistake will be honored unless Stage 2 itself surfaces new "
        "findings -- in which case you'll be asked again. **Re-emitting "
        "`mistake` is the explicitly correct way to push through this gate.**",
    ]
    return "\n".join(lines)


def mistake_stage2_sweep(state: "OrchestrationState",
                         data: dict,
                         subsection_folder: Path,
                         mistake_body: str) -> dict:
    """Stage 2: dispatch the ``verify_no_undocumented_deviation`` worker
    to look for CONTENT deviations in cited defs that the register
    hasn't captured yet. Returns a dict::

        {verdict: CLEAN | DEVIATION_FOUND | ERROR | MISSING,
         suspect_defs: [...],
         feedback: "...",
         raw_tail: "..."}
    """
    from deviations import load_register
    body = _gather_claim_body_text(state.row, subsection_folder)
    cited = _extract_cited_refs(body)
    cited_def_rows = [
        r for r in data["rows"]
        if r.get("ref") in cited and r.get("def_or_claim") == "def"
    ]

    # Build the worker prompt. Inline the claim's row, the cited defs'
    # tex_blocks + Lean files, the current register, and the manager's
    # mistake rationale.
    parts = [read_worker_prompt("verify_no_undocumented_deviation.md"), ""]
    parts.append("# Claim under disprove consideration\n")
    parts.append(f"- ref:        {state.row['ref']}")
    parts.append(f"- title:      {state.row.get('title')}")
    parts.append(f"- type:       {state.row.get('type')}")
    parts.append(f"- section:    {state.row.get('section')}")
    parts.append(f"- main_lean:  {state.row.get('main_lean_file')}")
    parts.append("\n## LN tex block of the claim (verbatim)\n"
                 f"```latex\n{state.row.get('tex_block') or ''}\n```")
    if state.row.get("main_lean_file"):
        try:
            t = (REPO_ROOT / state.row["main_lean_file"]).read_text(
                encoding="utf-8")
            # Truncate to fit argv budget (same approach as audit_helpers).
            if len(t) > 55_000:
                t = t[:40_000] + "\n-- ...[truncated]...\n" + t[-15_000:]
            parts.append(f"\n## Lean file for the claim\n```lean\n{t}\n```")
        except (OSError, UnicodeDecodeError):
            pass
    parts.append(f"\n## Manager's mistake rationale (body of the "
                 f"`mistake` action)\n```\n{mistake_body}\n```")
    parts.append("\n# Cited defs (upstream of the claim)\n")
    if not cited_def_rows:
        parts.append("(none found via citation scan; sweep cited def list "
                     "is empty)\n")
    for dr in cited_def_rows:
        parts.append(f"\n## {dr['ref']} -- {dr.get('title')}\n")
        parts.append(f"### LN tex_block\n```latex\n{dr.get('tex_block') or ''}\n```")
        if dr.get("main_lean_file"):
            try:
                t = (REPO_ROOT / dr["main_lean_file"]).read_text(encoding="utf-8")
                if len(t) > 40_000:
                    t = t[:30_000] + "\n-- ...[truncated]...\n" + t[-10_000:]
                parts.append(f"### Lean file: {dr['main_lean_file']}\n"
                             f"```lean\n{t}\n```")
            except (OSError, UnicodeDecodeError):
                pass
    # Inline the register so the worker can de-dupe.
    reg = load_register()
    parts.append("\n# Deviation register (already-known deviations -- do NOT re-flag)\n")
    if not reg:
        parts.append("(empty)")
    for e in reg:
        parts.append(
            f"- **{e.get('id')}** (introduced by `{e.get('introduced_by_ref')}`):\n"
            f"  - breaks: {e.get('breaks')}\n"
            f"  - preserves: {e.get('preserves')}\n"
            f"  - at_risk_pattern: {e.get('at_risk_pattern')}\n"
        )

    prompt = "\n".join(parts)
    label = f"mistake_stage2_{state.ref}"
    try:
        reply, _sess = run_claude(prompt, label=label)
    except WorkerTimeoutError as e:
        return {"verdict": "ERROR", "suspect_defs": [],
                "feedback": f"worker timed out: {e}", "raw_tail": ""}
    except Exception as e:                              # noqa: BLE001
        return {"verdict": "ERROR", "suspect_defs": [],
                "feedback": f"worker errored: {e}", "raw_tail": ""}

    m_v = re.search(r"^VERDICT:\s*(CLEAN|DEVIATION_FOUND)\s*$",
                    reply, re.MULTILINE)
    m_s = re.search(r"^SUSPECT_DEFS:\s*(.+?)\s*$", reply, re.MULTILINE)
    m_f = re.search(r"BEGIN\[feedback\]\s*\n(.*?)\n\s*END\[feedback\]",
                    reply, re.DOTALL)
    suspects: list[str] = []
    if m_s:
        suspects = [s.strip() for s in m_s.group(1).split(",") if s.strip()]
    return {
        "verdict":      m_v.group(1) if m_v else "MISSING",
        "suspect_defs": suspects,
        "feedback":     m_f.group(1).strip() if m_f else "",
        "raw_tail":     reply[-1200:],
    }


def _format_stage2_findings(stage2: dict) -> str:
    """Render Stage 2's worker findings into an extra_note block."""
    lines = [
        "**Stage 2 (LLM equivalence sweep of cited defs) found at least "
        "one undocumented deviation that could plausibly explain why "
        "your proof attempt failed.**",
        "",
    ]
    if stage2.get("suspect_defs"):
        lines.append("**Suspect defs**: " + ", ".join(
            f"`{r}`" for r in stage2["suspect_defs"]))
        lines.append("")
    lines.append("**Worker's findings:**")
    lines.append(stage2.get("feedback") or "(no feedback body)")
    lines += [
        "",
        "**Your options on the next turn**:",
        "- If a suspect def is genuinely at fault, `refactor <suspect_def_ref>` "
        "is likely the right action -- the LN claim may well be true under a "
        "corrected encoding.",
        "- If you've reviewed the worker's findings and you're confident "
        "they don't apply to *this* claim, re-emit `mistake` with a one-line "
        "acknowledgement. The orchestrator will then honor the disprove flow.",
        "",
        "(Stage 1's register-scan already ran for this row; you've now also "
        "been shown Stage 2's findings. Re-emitting `mistake` proceeds "
        "directly to disprove mode.)",
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# per-row commit on solve
# ---------------------------------------------------------------------------

# Generous cap for `scaffold/build_and_commit.sh` -- it runs `lake build`
# from the repo root before committing, which on a cold Mathlib cache or
# after a Mathlib bump can take several minutes. Anything over this cap
# is almost certainly stuck; we abandon the commit (the row stays
# uncommitted) and continue to the next row rather than crash.
COMMIT_SCRIPT_TIMEOUT_SECONDS = 15 * 60


def commit_solved_row(state: "OrchestrationState") -> None:
    """Invoke ``scaffold/build_and_commit.sh`` with a per-row message so
    each solve becomes its own commit on the working branch.

    Non-fatal: if `lake build` fails, the script exits non-zero and we
    log + continue. The row's `solved=yes` flag is already persisted in
    `data.json` (which we just saved); the next row's eventual commit
    will sweep the uncommitted changes in via `git add -A`.

    Time spent here counts toward ``time_needed_to_solve`` only by way
    of the closure's persist on the next loop iteration / finally --
    i.e. usually a minute or two of commit time becomes part of the
    row's recorded total. That's small enough to ignore vs the hours a
    proof takes.
    """
    row = state.row
    verdict = row.get("proven", "n/a")
    if verdict == "n/a":
        verdict = "formalized"          # def rows
    time_s = int(row.get("time_needed_to_solve") or 0)
    minutes = max(1, round(time_s / 60))
    n_turns = len(state.history)
    title = row.get("title", "") or "Untitled"
    msg = (f"{row['ref']}: {title} ({verdict}, {minutes}min, "
           f"turns={n_turns})")

    script = SCAFFOLD_DIR / "build_and_commit.sh"
    if not script.exists():
        print(f"[orchestrator] {script} missing; skipping auto-commit.",
              flush=True)
        return
    print(f"[orchestrator] committing: {msg}", flush=True)
    try:
        result = subprocess.run(
            ["bash", str(script), msg],
            cwd=str(REPO_ROOT),
            capture_output=True, text=True,
            timeout=COMMIT_SCRIPT_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        print(f"[orchestrator] commit script timed out after "
              f"{COMMIT_SCRIPT_TIMEOUT_SECONDS//60} min; row stays "
              f"uncommitted, continuing.", flush=True)
        return
    except Exception as e:                 # noqa: BLE001 - best effort
        print(f"[orchestrator] commit script failed to launch: {e}; "
              f"row stays uncommitted, continuing.", flush=True)
        return

    if result.returncode != 0:
        tail = "\n".join(
            (result.stdout + result.stderr).splitlines()[-15:]
        ) or "(empty)"
        print(f"[orchestrator] commit script exit {result.returncode}; "
              f"row stays uncommitted, continuing.\n"
              f"    log tail:\n{tail}", flush=True)
        return
    print(f"[orchestrator] commit + push OK.", flush=True)


def pick_title_for_row(row: dict) -> str:
    """Spawn a one-shot claude -p call to pick a short PascalCase title for
    a row whose ``title`` is empty. The response is sanitised to alphanumerics
    so it's filesystem-safe. Falls back to ``"Untitled"`` on a bad reply.
    """
    prompt = (
        "You are a tiny utility tool. Pick a short (1-3 words) PascalCase "
        "identifier suitable as a filename for the following lecture-notes "
        "block. Respond with ONLY the identifier -- no spaces, no punctuation, "
        "no quotes, no markdown, no commentary. Match the LN's terminology. "
        "Examples of good answers: CDMG, EdgeRelations, "
        "AcyclicIffTopologicalOrder, HardIntervention.\n\n"
        f"Ref: {row['ref']}\n"
        f"Kind: {row['def_or_claim']}\n"
        f"Source block:\n{row.get('tex_block', '')}\n"
    )
    reply, _session = run_claude(prompt, label=f"title_picker_{row['ref']}")
    first_line = (reply.strip().splitlines() or [""])[0].strip()
    cleaned = re.sub(r"[^A-Za-z0-9]", "", first_line)
    return cleaned or "Untitled"


def read_tex_block(tex_file: str, ref: str) -> str:
    """Return the defmark/claimmark block matching ``ref``.

    ``ref`` is e.g. ``"def_3_5"`` or ``"claim_3_12"``; the trailing integer is
    the 1-based index of the block within its kind in the chapter. We extract
    every matching environment from the file (in source order, which matches
    the numbering used by ``create_data.py``) and return the indexed one.
    """
    m = re.match(r"(def|claim)_\d+_(\d+)$", ref)
    if not m:
        return f"<bad ref: {ref}>"
    kind, n_str = m.group(1), m.group(2)
    idx = int(n_str) - 1                                       # to 0-based

    path = LECTURE_NOTES_DIR / tex_file
    if not path.exists():
        return f"<{tex_file} not found>"
    text = path.read_text(encoding="latin-1")
    env = "defmark" if kind == "def" else "claimmark"
    blocks = re.findall(
        rf"\\begin\{{{env}\}}.*?\\end\{{{env}\}}",
        text,
        flags=re.DOTALL,
    )
    if not blocks:
        return f"<no {env} blocks found in {tex_file}>"
    return blocks[idx] if 0 <= idx < len(blocks) else blocks[-1]


# ---------------------------------------------------------------------------
# Spawning a Claude agent
# ---------------------------------------------------------------------------

_USAGE_LIMIT_HINTS = ("usage limit", "rate limit", "rate_limit_error",
                      "5-hour limit", "weekly limit", "session limit")


def _parse_usage_limit_wait(stderr: str, stdout: str) -> int | None:
    """If the claude CLI's error output looks like a usage-limit message,
    return how many seconds to sleep before retrying. Returns ``None`` if
    the error isn't a usage limit.

    Best-effort parsing of phrases like "try again in 1 hour 23 minutes"
    or "in 3600 seconds". On a positive match with no parseable duration,
    defaults to 1h (3600s) -- long enough for a typical 5-hour-window reset
    to elapse on the next retry batch.
    """
    blob = (stderr + "\n" + stdout).lower()
    if not any(hint in blob for hint in _USAGE_LIMIT_HINTS):
        return None
    secs = 0
    if m := re.search(r"(\d+)\s*hour", blob):
        secs += int(m.group(1)) * 3600
    if m := re.search(r"(\d+)\s*minute", blob):
        secs += int(m.group(1)) * 60
    if m := re.search(r"(\d+)\s*second", blob):
        secs += int(m.group(1))
    return secs if secs > 0 else 3600


class WorkerTimeoutError(RuntimeError):
    """Raised by run_claude when the per-call wallclock cap fires before the
    `claude -p` subprocess returns.

    Distinct from generic ``RuntimeError`` (which run_claude raises on
    exhausted retries) so callers can decide whether a timeout is fatal
    (manager turn) or recoverable by telling the manager (worker turn).
    """


# Module-level hook so run_claude can notify the active row time-tracker
# (set by solve_current_row) when a usage-limit sleep is about to start /
# has just ended. The tracker uses these to *exclude* the sleep duration
# from time_needed_to_solve. ``None`` means no active tracker (e.g. when
# pick_title_for_row runs before the tracker is installed).
_ACTIVE_TRACKER_SLEEP_CB: "callable | None" = None


def run_claude(prompt: str, label: str,
               *, resume_session: str | None = None,
               retries: int = 2,
               on_usage_limit_sleep: "callable | None" = None,
               ) -> tuple[str, str | None]:
    """Run ``claude -p`` non-interactively and return ``(text, session_id)``.

    - The model is locked to Opus 4.7 with effort=max.
    - ``--output-format json`` so we can capture the conversation's session
      id; the manager can later resume any past agent via ``continue_agent``.
    - ``--dangerously-skip-permissions`` is on so workers can edit files.
    - If ``resume_session`` is given, we pass ``-r <id>`` so claude continues
      that previous conversation instead of starting a new one.
    - ``retries`` controls how many times a generic non-zero exit is retried.
      The CLI occasionally exits 1 with empty stderr -- a transient API
      hiccup; we swallow the first one or two.
    - **Usage-limit handling.** If the error output mentions a usage limit,
      we sleep until the parsed reset time (default 1h) and retry
      indefinitely. The total wall clock spent on the row is still capped by
      ``MAX_RUNTIME_SECONDS`` -- the row's elapsed clock advances during
      the sleep, so a long limit pause can still trigger a clean exit.
    - ``on_usage_limit_sleep`` is an optional callable ``(phase, seconds)``
      invoked as ``("pause", wait)`` immediately before each usage-limit
      sleep and ``("resume", wait)`` immediately after. Used by the row
      time-tracker to *exclude* the sleep duration from
      ``time_needed_to_solve`` (otherwise a multi-hour quota wait would
      inflate the row's "active" time).

    Raises ``WorkerTimeoutError`` if the per-call timeout fires, or
    ``RuntimeError`` when generic retries are exhausted.
    """
    # Pass the prompt via STDIN, not as a `-p PROMPT` argv element.
    # The Linux argv limit is ~128 KB; refactor-row prompts that inline
    # multiple large Lean files + the deviation register routinely
    # cross that threshold (caught on claim_3_27 during the
    # claim_3_2_no_finite refactor: OSError "Argument list too long").
    # `claude -p --output-format json` reads its prompt from stdin
    # when no positional argument is supplied -- no other behavior
    # change versus the prior argv-based call.
    cmd = ["claude", "-p", "--dangerously-skip-permissions",
           "--model", CLAUDE_MODEL,
           "--effort", CLAUDE_EFFORT,
           "--output-format", "json"]
    if resume_session:
        cmd += ["-r", resume_session]

    attempt = 0
    last_error = ""
    while True:
        attempt += 1
        try:
            result = subprocess.run(
                cmd, input=prompt,
                capture_output=True, text=True,
                timeout=PER_CALL_TIMEOUT_SECONDS, check=False,
            )
        except subprocess.TimeoutExpired as e:
            raise WorkerTimeoutError(
                f"claude call '{label}' timed out after "
                f"{PER_CALL_TIMEOUT_SECONDS//60} min (attempt {attempt})"
            ) from e

        if result.returncode == 0:
            break

        # Usage-limit pauses don't count against generic retries.
        wait = _parse_usage_limit_wait(result.stderr or "", result.stdout or "")
        if wait is not None:
            print(f"[run_claude] '{label}' hit a usage limit; sleeping "
                  f"{wait}s before retrying...", flush=True)
            cb = on_usage_limit_sleep or _ACTIVE_TRACKER_SLEEP_CB
            if cb is not None:
                cb("pause", wait)
            time.sleep(wait)
            if cb is not None:
                cb("resume", wait)
            attempt -= 1   # this attempt is "free"
            continue

        last_error = (result.stderr or "")[:500]
        if attempt > retries:
            raise RuntimeError(
                f"claude call '{label}' exited {result.returncode} after "
                f"{attempt} attempt(s): {last_error}"
            )
        # Short backoff so a transient CLI / API hiccup has a chance to
        # clear before we hammer the next attempt. Capped to avoid
        # stealing too much wall clock from the row's budget.
        backoff = min(60, 15 * attempt)
        print(f"[run_claude] '{label}' exited {result.returncode} on attempt "
              f"{attempt}; sleeping {backoff}s before retry...", flush=True)
        time.sleep(backoff)

    # Parse the JSON envelope. Fields we care about:
    #   result  -> the assistant's text reply
    #   session_id -> the conversation's id, used to resume later
    try:
        envelope = json.loads(result.stdout)
        text = envelope.get("result") or envelope.get("response") or ""
        session_id = envelope.get("session_id")
    except json.JSONDecodeError:
        # Older versions / unexpected output: degrade gracefully.
        text = result.stdout
        session_id = None
    return text, session_id


def _register_agent(row: dict, *, kind: str, session_id: str | None,
                    spawned_by: str = "manager") -> None:
    """Append an entry to the row's ``agent_registry`` if we got a session id.
    The manager can later resume this agent via ``continue_agent``.
    """
    if not session_id:
        return
    registry = row.setdefault("agent_registry", [])
    # If the same session id already exists, just bump last_used.
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    for entry in registry:
        if entry.get("session_id") == session_id:
            entry["last_used"] = now
            return
    registry.append({
        "kind": kind,
        "spawned_by": spawned_by,
        "session_id": session_id,
        "first_seen": now,
        "last_used": now,
    })


# ---------------------------------------------------------------------------
# Workspace / per-row scratch file
# ---------------------------------------------------------------------------

def workspace_path_for_row(row: dict, subsection_folder: Path) -> Path:
    """Return the markdown scratchpad path for a row -- the manager owns this
    file and uses it to track plans, attempts, and notes across turns.
    """
    return subsection_folder / f"workspace_{row['ref']}.md"


def ensure_row_workspace(row: dict, subsection_folder: Path) -> Path:
    """Create the per-row workspace markdown file if missing. Idempotent.
    The manager and workers are encouraged to write plans / tried-and-failed
    notes here so the next turn (or a `new_manager` handoff) has continuity.
    """
    wp = workspace_path_for_row(row, subsection_folder)
    if not wp.exists():
        wp.write_text(
            f"# Workspace for {row['ref']} — {row.get('title') or 'Untitled'}\n\n"
            f"This file is the manager's scratchpad for this row. Use it for:\n\n"
            f"- The plan (output of `make_plan` worker)\n"
            f"- A running list of what has been tried and why it didn't work\n"
            f"- Notes for the next manager (if you `new_manager`-handoff or\n"
            f"  the run ends and a future invocation picks this row up again)\n\n"
            f"It is YAML-untyped markdown — feel free to add sections.\n",
            encoding="utf-8",
        )
    return wp


# ---------------------------------------------------------------------------
# Per-chapter human-request file
# ---------------------------------------------------------------------------

def request_from_human_path(chapter_folder: Path) -> Path:
    return chapter_folder / "request_from_human.tex"


def ensure_request_from_human_file(chapter_folder: Path) -> Path:
    """Create ``request_from_human.tex`` at the chapter root if missing. The
    `request_from_human` action appends to its "Requests" section; the human
    answers in the "Answers" section.
    """
    p = request_from_human_path(chapter_folder)
    if not p.exists():
        tpl_path = TEX_TEMPLATES_DIR / "request_from_human.tex.template"
        if tpl_path.exists():
            p.write_text(
                tpl_path.read_text(encoding="utf-8")
                    .replace("__CHAPTER__", chapter_folder.name),
                encoding="utf-8",
            )
        else:
            p.write_text(
                f"% Communication channel between the agent swarm and the human\n"
                f"% for chapter {chapter_folder.name}. Agents append to "
                f"% \"Requests\"; the human writes back in \"Answers\".\n\n"
                f"\\section*{{Requests from the swarm}}\n\n"
                f"\\section*{{Answers from the human}}\n",
                encoding="utf-8",
            )
    return p


# ---------------------------------------------------------------------------
# Action handlers that need helpers
# ---------------------------------------------------------------------------

def _handle_request_from_human(state: "OrchestrationState", body: str,
                               data: dict) -> dict:
    """The `request_from_human` action is gated. The first
    ``HUMAN_REQUEST_THRESHOLD - 1`` consecutive attempts get a nudge back;
    only the threshold-th call writes the request to disk and stops the run.
    """
    history = state.history
    consecutive = 0
    for h in reversed(history):
        if h.action == "request_from_human":
            consecutive += 1
        else:
            break
    consecutive += 1                # include this attempt

    if consecutive < HUMAN_REQUEST_THRESHOLD:
        encouragement = (
            f"You've called `request_from_human` {consecutive} time(s) in a "
            "row. Are you SURE you've tried everything? You have a swarm of "
            "agents at your disposal — try `decompose`/`make_plan` to break "
            "the problem down further, or `new_manager` for a fresh "
            "perspective, or revisit the LN for a related lemma you might "
            "have missed. Only after several genuine attempts does the human "
            "want to be pulled in. Try again with a different action."
        )
        return {
            "summary": (f"Request-from-human attempt {consecutive}/"
                        f"{HUMAN_REQUEST_THRESHOLD}; nudged back."),
            "should_stop": False,
            "feedback_for_manager": encouragement,
        }

    # Threshold reached: write the request to the chapter file and stop.
    chapter_folder = state.data_path.parent
    req_path = ensure_request_from_human_file(chapter_folder)
    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    block = (
        f"\n\\subsection*{{{state.ref} — {stamp}}}\n"
        f"{body.strip()}\n"
    )
    text = req_path.read_text(encoding="utf-8")
    # Append into the Requests section if we can find it; else append at end.
    marker = "\\section*{Requests from the swarm}"
    if marker in text:
        text = text.replace(marker, marker + block, 1)
    else:
        text += block
    req_path.write_text(text, encoding="utf-8")
    print(f"[orchestrator] request_from_human appended to "
          f"{req_path.relative_to(state.data_path.parent.parent.parent)}",
          flush=True)
    return {
        "summary": f"Request written to {req_path.name}; stopping run.",
        "should_stop": True,
        "feedback_for_manager": "",
    }


def _continue_agent_from_body(state: "OrchestrationState", body: str,
                              turn: int) -> dict:
    """Resume a previously-spawned agent identified by ``AGENT_ID: <id>`` in
    ``body``. The rest of the body is sent as the follow-up message.
    """
    m = re.search(r"^AGENT_ID:\s*(\S+)\s*$", body, re.MULTILINE)
    if not m:
        return {
            "summary": "continue_agent body had no AGENT_ID line.",
            "feedback_for_manager": (
                "Your `continue_agent` body did not contain an "
                "`AGENT_ID: <id>` line. The agent registry is in your row "
                "context; pick a session id from there and try again."),
        }
    session_id = m.group(1).strip()
    follow_up = re.sub(r"^AGENT_ID:.*\n", "", body, count=1, flags=re.MULTILINE)
    reply, new_session = run_claude(
        follow_up,
        label=f"t{turn:03d}_continue_{session_id[:8]}",
        resume_session=session_id,
    )
    # Same agent: should keep its session id but bump last_used. The "new"
    # session id from --resume is usually the same one, but if claude forks
    # we record the new id too.
    _register_agent(state.row, kind="resumed", session_id=new_session or session_id)
    return {
        "summary": (f"Resumed session {session_id[:8]}…; reply: "
                    + summarise(reply, n=400)),
        "feedback_for_manager": (
            f"Reply from resumed agent {session_id[:8]}…:\n\n"
            f"{summarise(reply, n=1500)}\n\n"
            "Decide the next action."),
    }


def _apply_reorder_if_verified(state: "OrchestrationState", data: dict,
                               body: str, turn: int) -> dict:
    """The manager's `reorder` body must contain a `PRECEDES:` line listing
    ref(s) that should be solved before the current row. We dispatch a
    verifier; on PASS we move those refs up, clear this row's Lean state,
    save any progress notes into ``tips``, and signal the caller to end the
    run.
    """
    m = re.search(r"^PRECEDES:\s*(.+?)\s*$", body, re.MULTILINE)
    if not m:
        return {
            "applied": False,
            "summary": "reorder body had no PRECEDES line.",
            "feedback_for_manager": (
                "Your `reorder` body did not contain a `PRECEDES: "
                "<ref>, <ref>, ...` line. Try again with the precise list of "
                "refs that should be solved before this row."),
        }
    refs = [r.strip() for r in m.group(1).split(",") if r.strip()]
    # Build the verifier prompt inline -- this is a lightweight specialised
    # verifier rather than a full worker prompt file.
    verifier_prompt = (
        "You are an independent verifier. The manager working on a row has "
        "proposed that the following refs should be solved before the "
        "current row, and the current row deferred:\n\n"
        f"  PRECEDES: {', '.join(refs)}\n\n"
        f"Current row: {state.ref} (section {state.row.get('section')})\n"
        f"Manager's rationale:\n{body}\n\n"
        "Read the chapter's `data.json`, the LN tex_block for each listed "
        "ref, and the current row's tex_block. Decide whether the proposed "
        "ordering is genuinely needed for solving the current row. End your "
        "reply with `VERDICT: PASS` (apply the reorder) or `VERDICT: FAIL` "
        "(reject it; wrap your actionable feedback in BEGIN[feedback]/END[feedback]).\n"
    )
    reply, sess = run_claude(verifier_prompt,
                             label=f"t{turn:03d}_reorder_verifier")
    _register_agent(state.row, kind="verify_reorder", session_id=sess)
    v = re.search(r"^VERDICT:\s*(PASS|FAIL)\b", reply,
                  re.MULTILINE | re.IGNORECASE)
    verdict = v.group(1).upper() if v else "MISSING"
    if verdict != "PASS":
        fb = re.search(r"BEGIN\[feedback\]\s*\n(.*?)\n\s*END\[feedback\]",
                       reply, re.DOTALL)
        feedback = (f"\nVerifier feedback:\n{fb.group(1).strip()}\n"
                    if fb else "")
        return {
            "applied": False,
            "summary": f"reorder verifier verdict: {verdict}",
            "feedback_for_manager": (
                f"`reorder` was REJECTED (verdict={verdict}).{feedback}"
                "Continue solving the current row -- the proposed reorder "
                "isn't justified."),
        }

    # PASS: move listed refs ahead of the current row, clear current Lean
    # state, stash any progress notes in tips.
    rows = data["rows"]
    cur_idx = state.row_index
    moved = []
    for ref in refs:
        for j, r in enumerate(rows):
            if r["ref"] == ref and j > cur_idx:
                rows.pop(j)
                rows.insert(cur_idx, r)
                moved.append(ref)
                cur_idx += 1  # shift current row down
                break
    state.row_index = cur_idx
    # Stash a note into `tips` for when this row is picked up again.
    tip = (
        f"reorder applied @ {datetime.now(timezone.utc).date().isoformat()}: "
        f"deferred behind {', '.join(moved)}. Manager's rationale:\n"
        f"{body.strip()[:1500]}"
    )
    state.row["tips"] = (
        (state.row.get("tips", "") + "\n\n" if state.row.get("tips") else "")
        + tip
    )
    # Clear any partial Lean work and the row's agent registry: the row
    # should be approached with a clean slate when it comes up again.
    for lf in state.row.get("lean_files", []):
        p = REPO_ROOT / lf
        if p.exists():
            p.unlink()
    state.row["lean_files"] = []
    state.row["main_lean_file"] = ""
    state.row["formalized"] = "no"
    if state.row["def_or_claim"] == "claim":
        state.row["proven"] = "not proven"
    state.row["solved"] = "no"
    state.row["date_solved"] = ""
    state.row["agent_registry"] = []
    return {
        "applied": True,
        "summary": (f"reorder applied: moved {moved} ahead of "
                    f"{state.ref}; row reset."),
        "feedback_for_manager": "",
    }


# ---------------------------------------------------------------------------
# Manager / worker prompt assembly
# ---------------------------------------------------------------------------

def read_manager_prompt() -> str:
    return (PROMPTS_DIR / "manager.md").read_text(encoding="utf-8")


def read_worker_prompt(filename: str) -> str:
    return (WORKERS_DIR / filename).read_text(encoding="utf-8")


def render_row_context(state: OrchestrationState) -> str:
    """Compact briefing about which row the manager is solving."""
    row = state.row
    tex_block = read_tex_block(row["tex_file"], row["ref"])
    # For refactor rows the data.json lives in a sibling Refactor_<name>/
    # folder, but the Lean / tex subfiles live in the chapter's normal
    # section folders (the refactor edits the existing files in-place
    # via marker blocks). Always derive target_dir from the chapter
    # folder, which is data_path.parent for normal data.json and the
    # parent-of-refactor-folder for refactor tables.
    target_dir = ensure_subsection_folder(_chapter_folder_for(state.data_path),
                                          row.get("section", ""))
    workspace = workspace_path_for_row(row, target_dir)
    registry = row.get("agent_registry", [])
    if registry:
        registry_lines = "\n".join(
            f"  - {e['kind']:24s}  id={e['session_id']}  last={e['last_used']}"
            for e in registry[-15:]                # cap to last 15 to keep prompt small
        )
        registry_block = (
            "\n## Agent registry (for `continue_agent`)\n"
            "Each line is a past agent you can address by `AGENT_ID:`:\n"
            f"{registry_lines}\n"
        )
    else:
        registry_block = ""
    tips = row.get("tips", "")
    tips_block = f"\n## Carried-over tips for this row\n{tips}\n" if tips else ""
    refactor_block = _render_refactor_block(row) if row.get("refactor") else ""
    return (
        f"## Row context\n"
        f"- chapter: {state.chapter}\n"
        f"- ref: {row['ref']}\n"
        f"- title: {row.get('title', '')}\n"
        f"- kind: {row['def_or_claim']}\n"
        f"- section: {row.get('section', '')}\n"
        f"- type: {row.get('type', '')}\n"
        f"- tex_file: {row['tex_file']}\n"
        f"- refactor: {bool(row.get('refactor'))}\n"
        f"- chapter folder (data.json + request_from_human.tex live here): "
        f"{state.data_path.parent}\n"
        f"- target subsection folder (put Lean files + tex files here): "
        f"{target_dir}\n"
        f"- workspace scratchpad (yours to write plans/notes in): {workspace}\n"
        f"- current state: formalized={row['formalized']} "
        f"proven={row['proven']} solved={row['solved']}\n"
        f"\n## Source block from the lecture notes\n"
        f"```latex\n{tex_block}\n```\n"
        f"{tips_block}{refactor_block}{registry_block}"
    )


def _render_refactor_block(row: dict) -> str:
    """Render the manager-facing "this is a refactor row" briefing.

    Refactor rows live in a separate ``refactor_data.json`` (one per
    refactor target + its transitive consumers). The refactor produces
    *replacement* artefacts that live ALONGSIDE the originals until
    Phase 7 cleanup; nothing is deleted before then. Two parallel
    conventions:

    - **Lean: same-file marker blocks.** The replacement declaration
      ``refactor_<Name>`` lives in the same file as the original
      ``<Name>``, delimited by marker comments the cleanup script
      greps for.
    - **Tex (claim rows only, proof subfiles): prefix-named twin
      file.** The replacement proof is written to
      ``tex/refactor_<ref>_proof_<title>.tex``; the original
      ``tex/<ref>_proof_<title>.tex`` is left untouched.

    The cleanup script (``extras/apply_refactor_cleanup.py``) does the
    atomic swap of both: deletes Lean ORIGINAL blocks + renames
    ``refactor_X`` -> ``X``, AND renames each ``refactor_<ref>_proof_*``
    over the original.
    """
    main_lean = row.get("main_lean_file") or "(see `lean_files` in your row data)"
    # The row's `title` is the PascalCase label used for file names
    # and is OFTEN but not always the actual Lean declaration name
    # (e.g., a row titled `AcyclicIffTopologicalOrder` may have its
    # Lean theorem named `isAcyclic_iff_hasTopologicalOrder`). The
    # manager must use the ACTUAL declaration name in the marker
    # blocks. We surface the row's title as a STARTING guess and
    # warn the manager to verify by opening the file.
    original_decl_name = row.get("title") or "<Title>"
    refactor_decl_name = f"refactor_{original_decl_name}"
    is_claim = row.get("def_or_claim") == "claim"
    proof_twin = _refactor_proof_basename(row) if is_claim else None
    proof_orig = _file_basename(row, "proof") if is_claim else None

    tex_section = ""
    if is_claim:
        tex_section = (
            "\n"
            "**Tex proof twin (claim rows only).** Don't edit the original\n"
            f"proof tex subfile `tex/{proof_orig}` -- it stays untouched\n"
            "until cleanup. Instead, write the new proof into the *twin*\n"
            f"file `tex/{proof_twin}`. Create it (or have the\n"
            "tex-writer worker create it) and target every subsequent\n"
            "`write_tex_proof` / `expand_proof` / `verify_tex_proof`\n"
            "worker at the twin. The cleanup script will rename the twin\n"
            "over the original at Phase 7. (No tex twin for def rows --\n"
            "definitions' LN block doesn't change in a refactor; only\n"
            "the Lean encoding does.)\n"
        )

    return (
        "\n## Refactor-row briefing -- READ FIRST\n"
        "**This row is part of a refactor.** Your goal is to produce\n"
        "*replacement* artefacts that live alongside the originals --\n"
        "nothing is deleted before Phase 7 cleanup.\n"
        "\n"
        "**Where the original lives:** the original declaration and its\n"
        "tex block are in the same files your `main_lean_file` /\n"
        f"`tex_file` already point at (`{main_lean}` / `{row.get('tex_file', '?')}`).\n"
        "Read the original first -- sometimes the refactor is a small\n"
        "tweak to one field, sometimes it needs a drastically different\n"
        "shape. Use the original as inspiration, not as scripture.\n"
        "\n"
        "**Lean: same-file marker convention.** Wrap the original block\n"
        "and the replacement block with the exact marker pairs below.\n"
        "**IMPORTANT**: the name after the colon must be the *actual*\n"
        "Lean declaration name (the identifier on the `def` / `theorem`\n"
        "/ `lemma` line of the original), NOT necessarily this row's\n"
        f"`title` (the title `{original_decl_name}` shown below is a\n"
        "STARTING GUESS; open the original Lean file and verify the\n"
        "real declaration name -- e.g. a row titled\n"
        "`AcyclicIffTopologicalOrder` may have its theorem named\n"
        "`isAcyclic_iff_hasTopologicalOrder`). If they differ, use the\n"
        "Lean name in the marker and as the `refactor_<name>` prefix:\n"
        "```lean\n"
        f"-- REFACTOR-BLOCK-ORIGINAL-BEGIN: {original_decl_name}\n"
        f"def {original_decl_name} := … -- (the existing definition; unchanged)\n"
        f"-- REFACTOR-BLOCK-ORIGINAL-END: {original_decl_name}\n"
        "\n"
        f"-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: {original_decl_name} (was: {refactor_decl_name})\n"
        f"def {refactor_decl_name} := … -- (your new version)\n"
        f"-- REFACTOR-BLOCK-REPLACEMENT-END: {original_decl_name}\n"
        "```\n"
        "Phase 7's cleanup script greps for these markers, deletes the\n"
        "ORIGINAL block, and renames every occurrence of\n"
        f"`refactor_<FinalName>` -> `<FinalName>` across all affected\n"
        "files. **Use the exact marker format above** -- a typo in a\n"
        "marker means the cleanup misses your block. **And use the\n"
        "actual Lean declaration name** -- the rename is whole-word, so\n"
        "if your marker says `Foo` but the declaration is `fooBar`, the\n"
        "cleanup won't find anything to rename.\n"
        "\n"
        "**Net-new helpers also need REPLACEMENT markers.** If you add\n"
        "a brand-new theorem / def / lemma that didn't exist before --\n"
        "for example a `refactor_helper_lemma` you build to support the\n"
        "replacement -- it ALSO needs a REPLACEMENT marker block (an\n"
        "ORIGINAL pair is NOT required for net-new declarations). Use\n"
        "this form:\n"
        "```lean\n"
        "-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: helper_lemma (was: refactor_helper_lemma)\n"
        "theorem refactor_helper_lemma : ... := by ...\n"
        "-- REFACTOR-BLOCK-REPLACEMENT-END: helper_lemma\n"
        "```\n"
        "**The cleanup script REFUSES** if it finds a top-level\n"
        "`refactor_*` declaration that isn't inside any REPLACEMENT\n"
        "marker -- otherwise the `refactor_` prefix would silently\n"
        "survive cleanup. So: every `refactor_*` declaration you write,\n"
        "wrap it. (You can pass `--auto-rename-strays` at finalize to\n"
        "override that refusal, but it's a last resort -- the right\n"
        "fix is to add the marker block here, now.)\n"
        f"{tex_section}"
        "\n"
        "**Don't delete the original yourself.** Don't rename anything\n"
        "yourself. The build stays green because consumers keep seeing\n"
        f"the old `{original_decl_name}`; your `{refactor_decl_name}` is\n"
        "an additional declaration the strict-equivalence solved-gate\n"
        "validates against the LN.\n"
        "\n"
        "**The `refactor` action is BLOCKED inside refactor rows.** If\n"
        "you discover a nested refactor need, abort and surface it via\n"
        "`request_from_human` -- the orchestrator will halt cleanly.\n"
    )


def render_history(state: OrchestrationState) -> str:
    """Compact transcript of previous turns, for the manager to read."""
    if not state.history:
        return "## History\n_(this is your first turn for this row)_\n"
    lines = ["## History"]
    for t in state.history:
        lines.append(f"\n### Turn {t.turn_index}: action `{t.action}`")
        lines.append(f"**Body you emitted:**\n{t.body.strip()[:1500]}")
        if t.worker_summary:
            lines.append(f"\n**Result from the dispatched agent:**\n"
                         f"{t.worker_summary.strip()[:1500]}")
    return "\n".join(lines)


def build_manager_prompt(state: OrchestrationState,
                         extra_note: str | None = None) -> str:
    """Combine the manager.md instructions, the row context, the running
    history, and any one-off note (e.g. verifier verdict) into a single
    prompt to send to claude -p."""
    parts = [
        read_manager_prompt(),
        render_row_context(state),
        render_history(state),
    ]
    if extra_note:
        parts.append(f"## Note from the orchestrator\n{extra_note}\n")
    parts.append(
        "## Your turn\n"
        "Decide the **single next action**. End your message with exactly "
        "one `BEGIN[<action_name>] ... END[<action_name>]` block and "
        "nothing after it."
    )
    return "\n\n".join(parts)


def build_worker_prompt(action: str, body: str, state: OrchestrationState) -> str:
    """Compose the prompt for the worker that handles ``action``.

    For named actions we prepend the matching worker prompt; for
    ``spawn_agent_sub_task`` the body itself is the entire prompt.
    """
    worker_file = ACTION_TO_WORKER.get(action)
    row_ctx = render_row_context(state)
    if worker_file is None:                                 # spawn_agent_sub_task
        return f"{row_ctx}\n## Task from the manager\n{body}\n"
    return (
        f"{read_worker_prompt(worker_file)}\n\n"
        f"{row_ctx}\n"
        f"## Task from the manager\n{body}\n"
    )


def build_verifier_prompt(state: OrchestrationState, body: str) -> str:
    return (
        f"{read_worker_prompt('verify_row_solved.md')}\n\n"
        f"{render_row_context(state)}\n"
        f"## Manager's summary of what was done\n{body}\n"
    )


def build_verifier_action_prompt(action: str, state: OrchestrationState,
                                 body: str) -> str:
    """Compose the prompt for one of the ``VERIFIER_ACTIONS`` -- the
    matching worker prompt + the row context + the manager's claim.

    For the strict equivalence checker and the example verifier, the
    worker prompt explicitly requires the actual Lean source (not just
    paths) and the current deviation register. ``render_row_context``
    inlines `tex_block` but only lists Lean file *paths*; the audit-
    helper context block inlines the file *contents* (head+tail-
    truncated for argv-budget). We splice that block in for those two
    actions so manager-invoked use matches the solved-gate's quality of
    input. (For the other verifiers, the path list is enough.)
    """
    worker_file, _ = VERIFIER_ACTIONS[action]
    parts = [
        f"{read_worker_prompt(worker_file)}\n",
        f"{render_row_context(state)}\n",
    ]
    if action in ("verify_equivalence_strict", "verify_with_examples"):
        # Local import to keep audit_helpers off the hot import path.
        from audit_helpers import (                          # type: ignore
            _row_context_block, _deviation_register_block,
        )
        parts.append(
            "\n## Lean source + deviation register "
            "(auto-inlined for strict verifiers)\n"
            f"{_row_context_block(state.row, include_lean=True, include_tex_block=False)}\n"
            f"{_deviation_register_block()}\n"
        )
    parts.append(f"\n## Manager's claim\n{body}\n")
    return "".join(parts)


# ---------------------------------------------------------------------------
# Parsing and bookkeeping
# ---------------------------------------------------------------------------

def parse_action_tag(text: str) -> tuple[str, str]:
    """Extract (action_name, body) from the manager's reply.

    The reply must end with a single ``BEGIN[name]...END[name]`` block. The
    regex is anchored to the end of the string so trailing prose is rejected.
    """
    m = ACTION_TAG_RE.search(text.strip())
    if not m:
        raise ValueError(
            "Manager output did not end with a valid action tag. Last 800 "
            "chars:\n" + text[-800:]
        )
    return m.group("name"), m.group("body")


def increment_action_count(row: dict, action: str) -> None:
    """Add 1 to ``row['actions_tracking'][action]``, tolerating unknown keys
    (they get created with value 1) so a new action name doesn't crash mid-run.
    """
    at = row.setdefault("actions_tracking", {})
    at[action] = at.get(action, 0) + 1


def mark_solved(row: dict, kind: str,
                lean_files: list[str] | None = None,
                main_lean_file: str | None = None,
                verdict: str = "proven") -> None:
    """Flip the row's status fields to indicate completion.

    ``verdict`` is ``"proven"`` for a normal solve or ``"disproven"`` if a
    counter-example was the outcome. Definitions ignore ``verdict``.
    ``lean_files`` is the list of repo-relative paths the verifier reported;
    ``main_lean_file`` is the file containing the canonical statement
    (defaults to ``lean_files[0]`` if not given).
    """
    row["formalized"] = "yes"
    if kind == "claim":
        row["proven"] = verdict
    row["solved"] = "yes"
    row["date_solved"] = datetime.now(timezone.utc).date().isoformat()
    if lean_files:
        row["lean_files"] = lean_files
    if main_lean_file:
        row["main_lean_file"] = main_lean_file
    elif lean_files and not row.get("main_lean_file"):
        row["main_lean_file"] = lean_files[0]


def summarise(text: str, n: int = 800) -> str:
    """First ``n`` chars of a (possibly long) agent response, for the history."""
    text = text.strip()
    return text if len(text) <= n else text[: n - 3] + "..."


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------

def solve_current_row(data_path: Path | None = None) -> None:
    """Drive the first unsolved row of the current data.json to ``solved``.

    By default uses the current chapter (as recorded in ``global_vars.json``);
    pass an explicit ``data_path`` to operate on a different data.json --
    e.g. a refactor table at
    ``leanification/Chapter3_GraphTheory/Refactor_X/refactor_data.json``.

    Stops on any of: row reaches a terminal state, 20-hour budget exhausted,
    or MAX_TURNS reached. The data.json is saved after every meaningful state
    change so an interrupted run leaves a recoverable trail.

    Per-row wall-clock is accumulated in ``row["time_needed_to_solve"]``
    (seconds). The counter only advances while *this* function is on the
    stack -- across-session waits don't count, but in-session sleeps
    (usage-limit pauses, subprocess work) do. A ``try / finally`` around
    the loop guarantees that every exit path persists the partial time so
    the next invocation resumes from the right baseline.
    """
    if data_path is None:
        chapter = read_current_chapter()
        data_path = find_chapter_data_path(chapter)
    else:
        chapter = _infer_chapter_from_path(data_path)
    data = load_data(data_path)
    row_index = first_unsolved_row_index(data)
    state = OrchestrationState(
        chapter=chapter,
        data_path=data_path,
        row_index=row_index,
        row=data["rows"][row_index],
    )
    # Ensure the time counter exists (older rows may not have it).
    state.row.setdefault("time_needed_to_solve", 0)
    prior_seconds = int(state.row["time_needed_to_solve"])

    # Resume-from-previous-session signals: a non-empty workspace, a
    # populated agent_registry, or a non-zero accumulated time all mean
    # the row was already being worked on. Surface this loud + clear.
    section_at_start = state.row.get("section", "")
    workspace_exists = False
    if section_at_start:
        ss = ensure_subsection_folder(state.data_path.parent, section_at_start)
        workspace_exists = workspace_path_for_row(state.row, ss).exists()
    n_registry = len(state.row.get("agent_registry", []) or [])
    resume_signals = []
    if prior_seconds:
        resume_signals.append(
            f"{prior_seconds//60}m{prior_seconds%60:02d}s already spent")
    if workspace_exists:
        resume_signals.append("workspace markdown present")
    if n_registry:
        resume_signals.append(f"{n_registry} resumable agent session(s)")

    print(f"[orchestrator] solving {state.ref} "
          f"({state.row['def_or_claim']}, section {state.row.get('section')}) "
          f"from {data_path.name}", flush=True)
    if resume_signals:
        print(f"[orchestrator] RESUMING from prior session(s): "
              f"{'; '.join(resume_signals)}", flush=True)
    else:
        print(f"[orchestrator] fresh start (no prior session artefacts).",
              flush=True)

    # Pre-flight setup before the manager loop starts:
    #   1. If the row's title is empty, run a quick claude -p call to pick a
    #      short PascalCase identifier (used in subfile names).
    #   2. Make sure the subsection folder + per-row template subfiles exist.
    #   3. Regenerate the subsection's `main.tex` aggregator so the new
    #      subfiles appear in the build.
    # The manager then walks into a workspace where every artefact it might
    # need already has a placeholder file -- it only has to fill in bodies.
    if not state.row.get("title"):
        picked = pick_title_for_row(state.row)
        state.row["title"] = picked
        save_data(state.data_path, data)
        print(f"[orchestrator] picked title: {picked}", flush=True)
    section = state.row.get("section", "")
    if section:
        regenerate_subsection_main_tex(state.data_path, data, section)
        ensure_row_workspace(
            state.row,
            ensure_subsection_folder(state.data_path.parent, section),
        )
    # The chapter-level "request from human" file is created here too so the
    # manager can be told (and the human can pre-seed answers to old requests).
    ensure_request_from_human_file(state.data_path.parent)

    # Per-turn wall-clock accumulator. `time_mark` is updated each time we
    # persist; `persist_time` flushes the delta into `time_needed_to_solve`
    # and re-saves data.json so the value survives interruption.
    time_mark = time.monotonic()

    def persist_time() -> None:
        nonlocal time_mark
        now = time.monotonic()
        delta = now - time_mark
        if delta <= 0:
            return
        state.row["time_needed_to_solve"] = round(
            state.row.get("time_needed_to_solve", 0) + delta
        )
        save_data(state.data_path, data)
        time_mark = now

    def on_usage_limit_sleep(phase: str, _seconds: int) -> None:
        """Pause/resume the time tracker around usage-limit sleeps so the
        sleep duration doesn't inflate the row's ``time_needed_to_solve``.
        ``pause`` flushes the pre-sleep delta; ``resume`` resets the
        baseline to "now" so the sleep itself is never counted.
        """
        nonlocal time_mark
        if phase == "pause":
            persist_time()
        elif phase == "resume":
            time_mark = time.monotonic()

    # Install the module-level hook so run_claude (and helpers that call it)
    # find our pause/resume callback without needing it as an explicit kwarg.
    global _ACTIVE_TRACKER_SLEEP_CB
    _ACTIVE_TRACKER_SLEEP_CB = on_usage_limit_sleep

    extra_note: str | None = None

    try:
      for turn in range(1, MAX_TURNS + 1):
        # --- Budget check --------------------------------------------------
        if state.elapsed_seconds > MAX_RUNTIME_SECONDS:
            print(f"[orchestrator] 20-hour budget exhausted after {turn-1} "
                  f"turns; stopping.", flush=True)
            append_unsolved_run_summary(
                state,
                reason=f"20-hour budget exhausted after {turn-1} turns",
            )
            return

        # --- Manager turn --------------------------------------------------
        print(f"\n[orchestrator] === turn {turn} === "
              f"(elapsed {state.elapsed_seconds/60:.1f} min)", flush=True)
        manager_prompt = build_manager_prompt(state, extra_note=extra_note)
        extra_note = None
        # Manager-call timeout: retry a few times before giving up. A
        # repeated hang here means the LLM service or auth is broken and
        # the orchestrator can't make progress; we exit cleanly so a
        # future invocation picks up where we left off.
        for mgr_attempt in range(1, 4):
            try:
                manager_reply, manager_session = run_claude(
                    manager_prompt, label=f"t{turn:03d}_manager")
                break
            except WorkerTimeoutError as e:
                print(f"[orchestrator] manager call timed out "
                      f"(attempt {mgr_attempt}/3): {e}", flush=True)
                if mgr_attempt == 3:
                    append_unsolved_run_summary(
                        state,
                        reason=f"manager timed out 3x at turn {turn}",
                    )
                    return
            except RuntimeError as e:
                # Generic non-zero exit from the CLI -- often a transient
                # API hiccup. Backoff + retry same as the timeout path.
                print(f"[orchestrator] manager call errored "
                      f"(attempt {mgr_attempt}/3): {e}", flush=True)
                if mgr_attempt == 3:
                    append_unsolved_run_summary(
                        state,
                        reason=f"manager errored 3x at turn {turn}",
                    )
                    return
        _register_agent(state.row, kind="manager",
                        session_id=manager_session)
        try:
            action, body = parse_action_tag(manager_reply)
        except ValueError as e:
            # Hand the manager a corrective note and try again. Repeat the
            # full action list so the manager can't excuse forgetting.
            from create_data import ACTIONS                    # local import to avoid cycle
            extra_note = (
                "Your previous reply did NOT end with a valid action tag. "
                "Remember: end with EXACTLY one block of the form\n"
                "  BEGIN[<action_name>]\n"
                "  <body>\n"
                "  END[<action_name>]\n"
                "and NOTHING after it. Valid action names are: "
                + ", ".join(ACTIONS)
                + ".\nParse error was: " + str(e)[:300]
            )
            continue

        print(f"[orchestrator] manager chose action: {action}", flush=True)
        increment_action_count(state.row, action)

        # --- Dispatch ------------------------------------------------------
        worker_summary = ""

        if action == "solved":
            # Independent verifier checks the row before we flip the flag.
            try:
                verifier_reply, sess = run_claude(
                    build_verifier_prompt(state, body),
                    label=f"t{turn:03d}_verifier",
                )
            except (WorkerTimeoutError, RuntimeError) as e:
                kind = ("timed out"
                        if isinstance(e, WorkerTimeoutError) else "errored")
                print(f"[orchestrator] solved-verifier {kind}: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER {kind.upper()}: {e}"))
                extra_note = (
                    f"The `verify_row_solved` worker {kind} on subprocess "
                    f"call (after the orchestrator's built-in retries). "
                    f"Files should still be in the state your previous "
                    f"workers left them. Decide the next action -- you can "
                    f"retry `solved`, hand off to a fresh manager, or "
                    f"dispatch a cleanup."
                )
                save_data(state.data_path, data)
                persist_time()
                continue
            _register_agent(state.row, kind="verify_row_solved", session_id=sess)
            worker_summary = summarise(verifier_reply)
            state.history.append(TurnRecord(turn, action, body, worker_summary))

            # The verifier MUST end its message with `VERDICT: PASS` or
            # `VERDICT: FAIL` -- see `row_workers/verify_row_solved.md`. We
            # scan anywhere in the message; a missing/ambiguous verdict is
            # treated as a fail.
            verdict_match = re.search(r"^VERDICT:\s*(PASS|FAIL)\b",
                                      verifier_reply,
                                      re.MULTILINE | re.IGNORECASE)
            verdict = (verdict_match.group(1).upper()
                       if verdict_match else "MISSING")
            print(f"[orchestrator] verifier verdict: {verdict}", flush=True)

            if verdict == "PASS":
                # Verifier reports the file(s) via `LEAN_FILES:` lines
                # (comma-separated, or repeated) and a single `MAIN_LEAN_FILE:`
                # line for the canonical statement. See the contract in
                # `row_workers/verify_row_solved.md`.
                lean_files: list[str] = []
                for lf_match in re.finditer(
                        r"^LEAN_FILES?:\s*(.+?)\s*$",
                        verifier_reply, re.MULTILINE):
                    for path in lf_match.group(1).split(","):
                        path = path.strip()
                        if path:
                            lean_files.append(path)
                main_match = re.search(
                    r"^MAIN_LEAN_FILE:\s*(.+?)\s*$",
                    verifier_reply, re.MULTILINE)
                main_lean_file = main_match.group(1).strip() if main_match else None

                kind = state.row["def_or_claim"]
                # Scan history backward: the LAST mistake/unmistake action
                # determines the verdict. Lets the manager freely toggle
                # between prove and disprove modes during the row run.
                proven = "proven"
                for h in reversed(state.history):
                    if h.action == "mistake":
                        proven = "disproven"
                        break
                    if h.action == "unmistake":
                        proven = "proven"
                        break

                # Hard sorry-check: independent of the verifier LLM, run
                # a deterministic grep + lake-build scan to confirm none
                # of the row's Lean files admits via `sorry`. If the
                # check fails, we DO NOT mark the row solved -- we feed
                # the finding back to the manager and continue the loop.
                # This is the only programmatic backstop against a
                # verifier hallucinating PASS over a real sorry.
                sorry_complaint = check_no_sorry(lean_files)
                if sorry_complaint is not None:
                    print(f"[orchestrator] sorry-check tripped for "
                          f"{state.ref}; bouncing back to manager.\n"
                          f"    {sorry_complaint.splitlines()[0]}",
                          flush=True)
                    state.history.append(TurnRecord(
                        turn, action, body,
                        f"SORRY-CHECK FAILED: {sorry_complaint[:300]}"))
                    extra_note = sorry_complaint
                    save_data(state.data_path, data)
                    persist_time()
                    continue

                # Strict-equivalence solved-gate. Cheap insurance against
                # the friendly `verify_equivalence` letting through a
                # CONTENT deviation (as it did with the disjoint_EL ->
                # marginalize cascade). The strict checker compares the
                # Lean encoding to the LN tex_block under set-theoretic
                # default-strict rules; on EXAMPLE_GENERATION verdict we
                # auto-chain the property-based example verifier.
                #
                # Bypassed when the manager has just emitted
                # `accept_deviation` (the manager has explicitly
                # acknowledged the deviation and added it to the
                # register). Worker errors (timeout, parse failure)
                # don't block -- we don't want a flaky worker to freeze
                # the manager out of solving.
                #
                # The row needs at least a main_lean_file (or one entry
                # in lean_files) for the check to make sense. Rows
                # without any Lean files (very rare; shouldn't reach
                # `solved` anyway) skip the gate.
                if state.deviation_accepted:
                    print(f"[orchestrator] strict-equivalence gate "
                          f"skipped for {state.ref} (manager emitted "
                          f"`accept_deviation`).", flush=True)
                    # One-shot consumption: clear the flag now that the
                    # bypass has been applied. If this `solved` attempt
                    # bounces on something downstream (e.g., the
                    # for-website worker errors) and the manager re-
                    # emits `solved`, the strict gate runs again -- the
                    # bypass is per-attempt, not per-row-run. The
                    # manager must re-emit `accept_deviation` to bypass
                    # again. (Idempotent: a second `accept_deviation`
                    # with the same id is treated as acknowledgement.)
                    state.deviation_accepted = False
                elif not lean_files and not main_lean_file:
                    print(f"[orchestrator] strict-equivalence gate "
                          f"skipped for {state.ref} (no Lean files "
                          f"reported by verifier).", flush=True)
                else:
                    # Build a temporary row-shaped dict with the
                    # just-reported lean_files (the row's persisted
                    # lean_files may be stale or empty at this point --
                    # they're written by mark_solved below).
                    row_for_check = dict(state.row)
                    row_for_check["lean_files"] = lean_files
                    row_for_check["main_lean_file"] = (
                        main_lean_file or (lean_files[0] if lean_files else None))
                    # For claims, mirror the live verdict (last
                    # mistake/unmistake) so the strict checker compares
                    # against the negation in disprove mode.
                    if state.row.get("def_or_claim") == "claim":
                        row_for_check["proven"] = proven
                    bounce_note = _run_solved_gate_strict_check(
                        state, row_for_check)
                    if bounce_note is not None:
                        print(f"[orchestrator] strict-equivalence gate "
                              f"tripped for {state.ref}; bouncing back "
                              f"to manager.", flush=True)
                        state.history.append(TurnRecord(
                            turn, action, body,
                            "STRICT-EQUIVALENCE GATE FAILED "
                            "(see extra_note for details)"))
                        extra_note = bounce_note
                        save_data(state.data_path, data)
                        persist_time()
                        continue

                mark_solved(state.row, kind, lean_files=lean_files,
                            main_lean_file=main_lean_file, verdict=proven)
                # Refactor rows edit the existing Lean files in-place via
                # marker blocks; they don't add new subfiles or change the
                # aggregator structure. Skip the aggregator regenerators,
                # the for-website worker, and the disprove-side cleanup
                # for refactor rows. Phase 7's cleanup script does the
                # final swap-and-rename pass at the end of the whole
                # refactor table.
                if state.row.get("refactor"):
                    print(f"[orchestrator] refactor row {state.ref} "
                          f"marked solved; skipping aggregator + "
                          f"for-website regeneration (handled at Phase "
                          f"7 cleanup).", flush=True)
                else:
                    regenerate_chapter_aggregator(state.data_path, data)
                    regenerate_subsection_main_tex(
                        state.data_path, data, state.row.get("section", ""))
                    # Drop the per-row scratchpad + clear the now-stale
                    # agent_registry; anything worth keeping should already
                    # be in the Lean comments. Then compile the row's tex
                    # files (and, if this was the final row of the subsection,
                    # the aggregate main.tex) as a sanity check.
                    section = state.row.get("section", "")
                    if section:
                        subsection_folder = ensure_subsection_folder(
                            state.data_path.parent, section)
                        cleanup_row_artefacts(state.row, subsection_folder)
                        build_row_tex(state.row, subsection_folder)
                        # Dispatch a one-shot worker to produce the for-website
                        # JSON (Lean statement + polished explanation + design
                        # choices). Falls back to a mechanical extractor on
                        # worker failure. Done BEFORE commit so the JSON lands
                        # in the same commit as the rest of the row.
                        run_for_website_worker(state.row, subsection_folder)
                        if subsection_is_complete(data, section):
                            print(f"[orchestrator] section {section} now fully "
                                  f"solved -- building aggregate main.tex",
                                  flush=True)
                            build_subsection_main_tex(subsection_folder)
                # Save AFTER cleanup so the cleared agent_registry is persisted.
                save_data(state.data_path, data)
                # Flush the row time BEFORE the commit so the recorded
                # time_needed_to_solve reflects solving, not commit overhead.
                persist_time()
                print(f"[orchestrator] {state.ref} marked solved "
                      f"({proven}); lean_files={lean_files or '(unreported)'}",
                      flush=True)
                # Per-row commit via the sanctioned script (runs lake build
                # then `git commit && git push`). Non-fatal on failure.
                commit_solved_row(state)
                return

            # Verifier said FAIL (or no verdict). Surface the verifier's
            # tagged feedback (if present) to the manager so it knows what
            # to fix; the manager keeps trying until the budget is gone.
            fb = re.search(
                r"BEGIN\[feedback\]\s*\n(.*?)\n\s*END\[feedback\]",
                verifier_reply, re.DOTALL,
            )
            feedback = (
                f"\nVerifier feedback:\n{fb.group(1).strip()}\n"
                if fb else ""
            )
            extra_note = (
                f"`verify_row_solved` verdict: {verdict}.{feedback}"
                "Re-read its report (in your history above), address what "
                "failed, and pick the next action."
            )

        elif action == "no_action":
            # The manager couldn't decide. Nudge it to pick a concrete action.
            state.history.append(TurnRecord(turn, action, body, ""))
            extra_note = (
                "You emitted `no_action`. Please pick one of the concrete "
                "actions from the table in manager.md."
            )

        elif action == "refactor":
            # Guard: nested refactor is not supported. If the manager of
            # a refactor row asks for another refactor, halt cleanly so a
            # human can review. (The simplest design: don't auto-anything
            # recursive; the human decides whether to extend the current
            # refactor's problem list, spin a new refactor branch, or
            # abandon.)
            if state.row.get("refactor"):
                print(f"[orchestrator] nested refactor requested for "
                      f"{state.ref} (inside a refactor row); aborting "
                      f"run for human review.", flush=True)
                state.history.append(TurnRecord(
                    turn, action, body,
                    "(rejected: nested refactor; aborting for human review)"))
                save_data(state.data_path, data)
                append_unsolved_run_summary(
                    state,
                    reason=(
                        "NESTED REFACTOR REQUESTED -- the manager of "
                        "this refactor row asked for a refactor. "
                        "Orchestrator halted for human review. The "
                        "manager's rationale is the action body in the "
                        "last history entry; decide whether to extend "
                        "the current refactor's problem list, spin a "
                        "new refactor branch, or abandon this row."
                    ),
                )
                return
            # Advisory refactor: the (rewritten) `plan_refactor.md`
            # worker is NON-DESTRUCTIVE -- it just writes a markdown
            # plan to `leanification/refactors/refactor_<name>.md` and
            # emits a RECOMMENDED_INVOCATION line. No rows are reset,
            # no Lean files deleted; the original chapter's data.json
            # is untouched. The human reviews the plan and launches
            # the actual refactor pipeline via
            # `extras/do_refactor.py init` (which creates the
            # refactor_<name> git branch off server_setting_up_scaffold,
            # runs find_dependents.py + initialize_refactor.py, and
            # commits/pushes the refactor table). See the
            # 'Refactor rows' section of manager.md for the full
            # lifecycle (init -> solve -> finalize -> merge).
            worker_prompt = (
                read_worker_prompt("plan_refactor.md")
                + "\n\n"
                + render_row_context(state)
                + f"## Manager's refactor request\n{body}\n"
            )
            reply, sess = run_claude(
                worker_prompt, label=f"t{turn:03d}_refactor_planner"
            )
            _register_agent(state.row, kind="refactor", session_id=sess)
            state.history.append(TurnRecord(
                turn, action, body,
                summarise(reply, n=1200),
            ))
            # Try to extract the planner's structured tail so we can
            # surface the exact `do_refactor.py init` command.
            m_invoke = re.search(
                r"^RECOMMENDED_INVOCATION:\s*(.+?)\s*$",
                reply, re.MULTILINE)
            m_plan = re.search(
                r"^REFACTOR_PLAN_FILE:\s*(\S+)\s*$",
                reply, re.MULTILINE)
            invocation_line = (m_invoke.group(1)
                               if m_invoke
                               else "python extras/do_refactor.py init "
                                    "--chapter <N> --root-ref <ref> "
                                    "--name <name>   (planner did not "
                                    "emit a RECOMMENDED_INVOCATION; "
                                    "fill in by hand from the plan)")
            plan_line = (f"  plan markdown: {m_plan.group(1)}\n"
                         if m_plan else "")
            save_data(state.data_path, data)
            print(f"[orchestrator] refactor planner ran; halting row "
                  f"run for human review.", flush=True)
            print(f"[orchestrator]   next step (human):")
            print(f"[orchestrator]     1. git checkout {SERVER_BRANCH}")
            print(f"[orchestrator]     2. {invocation_line}", flush=True)
            append_unsolved_run_summary(
                state,
                reason=(
                    "REFACTOR REQUESTED -- the manager called the\n"
                    "(advisory) refactor planner. No rows were reset; "
                    "no Lean files deleted; the original chapter's\n"
                    "data.json is unchanged. To execute the refactor:\n"
                    f"{plan_line}"
                    f"  1. switch to the server branch:\n"
                    f"       git checkout {SERVER_BRANCH}\n"
                    f"  2. launch the refactor pipeline:\n"
                    f"       {invocation_line}\n"
                    "  3. drive the refactor table:\n"
                    "       python scaffold/solve_chapter.py --data-path "
                    "<refactor_data.json>\n"
                    "  4. once every refactor row is solved=yes, finalize:\n"
                    "       python extras/do_refactor.py finalize "
                    "--refactor-data <path>\n"
                    "  5. merge back into the server branch:\n"
                    "       python extras/do_refactor.py merge "
                    "--refactor-data <archived path> --push "
                    "--delete-remote-branch\n"
                ),
            )
            return

        elif action == "mistake":
            # Guard: `mistake` is a claim-only concept. A definition is
            # *formalised*, not *proven/disproven* -- there is no
            # "negation" to switch to. Refuse with a clear note and let
            # the manager pick a different action.
            if state.row.get("def_or_claim") != "claim":
                state.history.append(TurnRecord(
                    turn, action, body,
                    "(rejected: `mistake` is only valid on claim rows)"))
                print(f"[orchestrator] `mistake` rejected for "
                      f"{state.ref}: def_or_claim="
                      f"{state.row.get('def_or_claim')!r}", flush=True)
                extra_note = (
                    "`mistake` is not valid here -- this row is a "
                    "definition, not a claim. Definitions cannot be "
                    "'disproven'; they are formalised, not proven or "
                    "disproven. If the definition's Lean encoding is "
                    "wrong, dispatch a formalizer fix or `refactor`; "
                    "if you don't want to formalize this def at all, "
                    "that's a chapter-level decision outside this row "
                    "(use `request_from_human` if you're stuck)."
                )
                save_data(state.data_path, data)
                persist_time()
                continue
            # Two-stage gate before honoring the mistake (= switching to
            # disprove mode). The premise: by the time a manager calls
            # `mistake`, the claim has resisted multiple proof attempts.
            # Before we commit the verdict flip, we want one more pass to
            # check whether the *encoding* (not the LN claim) is the
            # culprit -- a "false LN claim" verdict is expensive to
            # later unwind.
            #
            # Stage 1 (deterministic, fast): scan the deviation register
            # for known upstream issues that touch this claim's cited
            # defs. If hits, surface them and ask the manager to
            # reconsider. Re-emitting `mistake` proceeds to Stage 2.
            #
            # Stage 2 (LLM worker, slower): dispatch
            # `verify_no_undocumented_deviation` to look adversarially
            # for CONTENT deviations in cited defs that the register has
            # not yet captured. If hits, surface and ask the manager to
            # reconsider. Re-emitting `mistake` proceeds to the honor.
            #
            # Both stages are one-shot per row run (tracked via
            # `state.mistake_stage{1,2}_done`). The manager is NEVER
            # permanently blocked -- after both stages have surfaced
            # their evidence, the next `mistake` is honored.
            subsection_folder = ensure_subsection_folder(
                state.data_path.parent, state.row.get("section", ""))

            # ----- Stage 1: deterministic register scan ----------------
            if not state.mistake_stage1_done:
                findings = mistake_stage1_register_scan(
                    state.row, subsection_folder)
                state.mistake_stage1_done = True
                if findings:
                    msg = (f"(mistake-sweep Stage 1 surfaced "
                           f"{len(findings)} register match(es); "
                           f"see extra_note)")
                    state.history.append(TurnRecord(turn, action, body, msg))
                    print(f"[orchestrator] mistake-sweep Stage 1 surfaced "
                          f"{len(findings)} register match(es) for "
                          f"{state.ref}; bouncing to manager.", flush=True)
                    extra_note = _format_stage1_findings(findings)
                    save_data(state.data_path, data)
                    persist_time()
                    continue
                print(f"[orchestrator] mistake-sweep Stage 1 clean for "
                      f"{state.ref}; proceeding to Stage 2.", flush=True)

            # ----- Stage 2: LLM equivalence sweep ----------------------
            if not state.mistake_stage2_done:
                print(f"[orchestrator] mistake-sweep Stage 2: dispatching "
                      f"verify_no_undocumented_deviation worker for "
                      f"{state.ref}.", flush=True)
                stage2 = mistake_stage2_sweep(
                    state, data, subsection_folder, body)
                state.mistake_stage2_done = True
                verdict2 = stage2.get("verdict")
                print(f"[orchestrator] mistake-sweep Stage 2 verdict: "
                      f"{verdict2}", flush=True)
                if verdict2 == "DEVIATION_FOUND":
                    msg = (f"(mistake-sweep Stage 2: DEVIATION_FOUND; "
                           f"suspects={stage2.get('suspect_defs')})")
                    state.history.append(TurnRecord(turn, action, body, msg))
                    extra_note = _format_stage2_findings(stage2)
                    save_data(state.data_path, data)
                    persist_time()
                    continue
                # CLEAN / ERROR / MISSING: fall through and honor the
                # mistake. ERROR/MISSING is logged but does NOT block --
                # we don't want a flaky worker to permanently freeze the
                # manager out of disprove mode.
                if verdict2 != "CLEAN":
                    print(f"[orchestrator] mistake-sweep Stage 2 returned "
                          f"{verdict2}; honoring `mistake` anyway "
                          f"(default-permissive on worker failure).",
                          flush=True)

            # ----- Both stages done: honor the mistake -----------------
            # State signal: the manager has concluded the claim is
            # genuinely false and is switching to the disprove flow. No
            # worker dispatch beyond the sweep; the signal lives in
            # state.history so that `mark_solved` later sees it (via
            # current_verdict_mode) and writes proven="disproven".
            #
            # Disprove-mode work goes to *parallel* files so toggling
            # back via `unmistake` doesn't lose prove-direction progress:
            #   - tex:  tex/claim_<ref>_disproof_<title>.tex
            #   - lean: Section<N>_<M>/<Title>Disproof.lean
            # Stubs are created lazily on first switch.
            ensure_disprove_stubs(state.row, subsection_folder)
            state.history.append(TurnRecord(turn, action, body,
                                            "(disprove flow engaged)"))
            disprove_tex = _file_basename(state.row, "disproof")
            disprove_lean = f"{state.row.get('title') or 'Untitled'}Disproof.lean"
            extra_note = (
                f"`mistake` recorded (mistake-sweep cleared) -- you're now "
                f"in DISPROVE mode. Proceed with the EXACT SAME workflow as "
                f"proving, but on the NEGATION. Workers should target the "
                f"*disprove-side* files (created for you):\n"
                f"  - tex: tex/{disprove_tex}\n"
                f"  - lean: {disprove_lean}\n"
                f"Prove-direction files are preserved and you can return to "
                f"them later via the `unmistake` action without losing work. "
                f"On `solved`, the row's verdict will be set to \"disproven\"."
            )

        elif action == "unmistake":
            # State signal: the manager has reconsidered -- the claim may
            # be provable after all. Flip back to prove mode. The
            # disprove-side files (tex + Lean) stay on disk so a future
            # `mistake` can pick them back up. Prove-direction files are
            # also intact (workers never touched them while in disprove
            # mode). `mark_solved` will read the LAST mistake/unmistake
            # in history -- this `unmistake` -- and write proven="proven".
            state.history.append(TurnRecord(turn, action, body,
                                            "(prove flow re-engaged)"))
            prove_tex = _file_basename(state.row, "proof")
            main_lean = state.row.get("main_lean_file") or "(see lean_files)"
            extra_note = (
                f"`unmistake` recorded -- you're back in PROVE mode. The "
                f"prove-direction files are exactly where the previous "
                f"prove-direction work left them:\n"
                f"  - tex: tex/{prove_tex}\n"
                f"  - lean: {main_lean}\n"
                f"The disprove-side files remain on disk too -- you can "
                f"flip back via `mistake` without losing that work either. "
                f"On `solved`, the row's verdict will be set to \"proven\"."
            )

        elif action == "accept_deviation":
            # Manager-driven write to the deviation register, paired
            # with a per-row bypass flag so the next `solved` attempt's
            # strict-equivalence gate is skipped. The manager uses this
            # when the strict-gate FAILed, the deviation is genuinely
            # intentional (LN form impractical / unnatural in Lean), and
            # the right move is to record + proceed rather than fix.
            #
            # Body format: lightly structured key/value lines. Required
            # keys (case-insensitive): `id`, `breaks`, `preserves`,
            # `at_risk_pattern`. Optional: `introduced_by_ref` (defaults
            # to the row's own ref), `tags` (comma-separated), `notes`
            # (free-form; everything after the last recognised key).
            #
            # On body-parse failure (missing required fields, stray
            # key after notes:, etc.) we bounce back to the manager
            # with the parse error so they can re-emit. On register
            # *collision* (id already in deviations.json -- common when
            # the auditor pre-drafted that entry, or when the manager
            # re-accepts after a non-strict-gate `solved` bounce) we
            # treat it as acknowledgement: no new write, flag still
            # flips, manager can proceed. Successful register write
            # also flips `state.deviation_accepted`, so the next
            # `solved` skips the strict gate.
            try:
                from deviations import (                              # type: ignore
                    register_deviation, load_register,
                )
                entry = _parse_accept_deviation_body(body, default_ref=state.ref)
            except (ValueError, KeyError) as e:
                state.history.append(TurnRecord(
                    turn, action, body,
                    f"accept_deviation body parse failed: {e}"))
                extra_note = (
                    f"`accept_deviation` could not be honored: {e}\n\n"
                    "The body must include these key/value lines "
                    "(case-insensitive, one per line):\n"
                    "  - id: <unique-snake-case-id>\n"
                    "  - breaks: <one-line property the LN says holds, ours doesn't>\n"
                    "  - preserves: <one-line property that still holds>\n"
                    "  - at_risk_pattern: <pattern downstream proofs grep against>\n"
                    "Optional:\n"
                    "  - introduced_by_ref: <ref>  (defaults to this row's ref)\n"
                    "  - tags: tag1, tag2\n"
                    "  - notes: free-form context (last; runs to end of body)\n"
                    "Re-emit `accept_deviation` with the body fixed."
                )
            else:
                existing_ids = {e.get("id") for e in load_register()}
                already_in_register = entry["id"] in existing_ids
                if already_in_register:
                    print(f"[orchestrator] accept_deviation: "
                          f"{entry['id']!r} already in register "
                          f"(acknowledging without duplicate write); "
                          f"strict-equivalence gate will be bypassed "
                          f"on the next `solved` attempt for "
                          f"{state.ref}.", flush=True)
                    state.deviation_accepted = True
                    state.history.append(TurnRecord(
                        turn, action, body,
                        f"(deviation {entry['id']!r} acknowledged -- "
                        f"already in register; strict gate will be "
                        f"bypassed on next `solved`)"))
                    extra_note = (
                        f"`accept_deviation` acknowledged: register "
                        f"entry `{entry['id']}` was already in "
                        f"`leanification/deviations.json` (likely "
                        f"drafted by the auditor or by a prior "
                        f"`accept_deviation`). No duplicate written. "
                        f"The strict-equivalence solved-gate will be "
                        f"BYPASSED on your next `solved` attempt for "
                        f"this row. Proceed to `solved` when ready."
                    )
                else:
                    try:
                        register_deviation(entry)
                    except (ValueError, KeyError) as e:
                        # Should not normally happen -- we just checked
                        # for collision and the body parsed. But guard
                        # in case `register_deviation` adds new
                        # validation in the future.
                        state.history.append(TurnRecord(
                            turn, action, body,
                            f"accept_deviation register write failed: {e}"))
                        extra_note = (
                            f"`accept_deviation` could not be honored: "
                            f"register write failed with {e}. Re-emit "
                            f"`accept_deviation` after fixing the body."
                        )
                    else:
                        state.deviation_accepted = True
                        state.history.append(TurnRecord(
                            turn, action, body,
                            f"(deviation {entry['id']!r} accepted + "
                            f"registered; strict gate will be bypassed "
                            f"on next `solved`)"))
                        print(f"[orchestrator] accept_deviation: "
                              f"registered {entry['id']}; strict-"
                              f"equivalence gate will be bypassed on "
                              f"the next `solved` attempt for "
                              f"{state.ref}.", flush=True)
                        extra_note = (
                            f"`accept_deviation` recorded: register "
                            f"entry `{entry['id']}` written to "
                            f"`leanification/deviations.json`. The "
                            f"strict-equivalence solved-gate will be "
                            f"BYPASSED on your next `solved` attempt "
                            f"for this row. Proceed to `solved` when "
                            f"ready. (Note: bypass is per-attempt; if "
                            f"this `solved` bounces on something other "
                            f"than the strict gate, you'll need to re-"
                            f"emit `accept_deviation` -- the same id "
                            f"works, since it's now in the register.)"
                        )

        elif action == "reset":
            # Drop the history and start the manager over from scratch.
            print("[orchestrator] manager requested reset; clearing history.",
                  flush=True)
            state.history.clear()

        elif action == "new_manager":
            # The body IS the handoff dossier. Replace history with a single
            # synthetic record so the next manager turn starts fresh but with
            # the dossier in view.
            print("[orchestrator] manager handed off to a fresh manager.",
                  flush=True)
            state.history = [TurnRecord(turn, "new_manager", body,
                                        "fresh manager taking over.")]

        elif action in VERIFIER_ACTIONS:
            # Generic verifier dispatch: spawn the matching worker, parse
            # `VERDICT: PASS/FAIL` from its reply, feed back to the manager.
            # No direct row-state changes here -- the manager decides what
            # to do based on the verdict.
            _, label_suffix = VERIFIER_ACTIONS[action]
            try:
                verifier_reply, sess = run_claude(
                    build_verifier_action_prompt(action, state, body),
                    label=f"t{turn:03d}_{label_suffix}",
                )
            except (WorkerTimeoutError, RuntimeError) as e:
                kind = ("timed out"
                        if isinstance(e, WorkerTimeoutError) else "errored")
                print(f"[orchestrator] {action} verifier {kind}: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER {kind.upper()}: {e}"))
                extra_note = (
                    f"The `{action}` verifier {kind} on subprocess call "
                    f"(after the orchestrator's built-in retries). Pick a "
                    f"different action or retry `{action}`."
                )
                save_data(state.data_path, data)
                persist_time()
                continue
            _register_agent(state.row, kind=action, session_id=sess)
            worker_summary = summarise(verifier_reply)
            state.history.append(TurnRecord(turn, action, body, worker_summary))
            # `verify_equivalence_strict` may legitimately return
            # EXAMPLE_GENERATION instead of PASS/FAIL -- the regex must
            # accept all three for that verdict to round-trip cleanly.
            v_match = re.search(
                r"^VERDICT:\s*(PASS|FAIL|EXAMPLE_GENERATION)\b",
                verifier_reply,
                re.MULTILINE | re.IGNORECASE,
            )
            verdict = v_match.group(1).upper() if v_match else "MISSING"
            print(f"[orchestrator] {action} verdict: {verdict}", flush=True)
            # If FAIL, the verifier prompt is asked to wrap its actionable
            # feedback in BEGIN[feedback]/END[feedback] -- surface it.
            fb = re.search(
                r"BEGIN\[feedback\]\s*\n(.*?)\n\s*END\[feedback\]",
                verifier_reply, re.DOTALL,
            )
            feedback = (
                f"\nVerifier feedback:\n{fb.group(1).strip()}\n"
                if fb else ""
            )
            # Auto-chain: a manager-invoked `verify_equivalence_strict`
            # returning EXAMPLE_GENERATION means the strict checker
            # explicitly deferred to property-based instances. Mirror
            # the solved-gate's behavior by dispatching
            # `verify_with_examples` immediately and combining results,
            # so the manager doesn't have to do the bookkeeping.
            if (action == "verify_equivalence_strict"
                    and verdict == "EXAMPLE_GENERATION"):
                print(f"[orchestrator] {action} returned "
                      f"EXAMPLE_GENERATION; auto-chaining "
                      f"verify_with_examples.", flush=True)
                # Count the auto-chained action toward the row's
                # actions_tracking so the run summary accurately
                # reflects what was dispatched (the chain happens
                # without an explicit manager `verify_with_examples`
                # action, so the top-of-turn counter would miss it).
                increment_action_count(state.row, "verify_with_examples")
                try:
                    ex_reply, ex_sess = run_claude(
                        build_verifier_action_prompt(
                            "verify_with_examples", state,
                            f"(auto-chained from verify_equivalence_strict's "
                            f"EXAMPLE_GENERATION verdict)\n\n"
                            f"Strict checker's reason:\n{feedback or '(none)'}"
                        ),
                        label=f"t{turn:03d}_examples_verifier_chain",
                    )
                    _register_agent(state.row, kind="verify_with_examples",
                                    session_id=ex_sess)
                    state.history.append(TurnRecord(
                        turn, "verify_with_examples",
                        "(auto-chained from verify_equivalence_strict)",
                        summarise(ex_reply)))
                    ex_v_match = re.search(
                        r"^VERDICT:\s*(PASS|FAIL)\b",
                        ex_reply, re.MULTILINE | re.IGNORECASE)
                    ex_verdict = (ex_v_match.group(1).upper()
                                  if ex_v_match else "MISSING")
                    ex_fb = re.search(
                        r"BEGIN\[feedback\]\s*\n(.*?)\n\s*END\[feedback\]",
                        ex_reply, re.DOTALL,
                    )
                    ex_feedback = (
                        f"\nExample-verifier feedback:\n"
                        f"{ex_fb.group(1).strip()}\n" if ex_fb else "")
                    print(f"[orchestrator] auto-chained "
                          f"verify_with_examples verdict: {ex_verdict}",
                          flush=True)
                    extra_note = (
                        f"`verify_equivalence_strict` returned "
                        f"EXAMPLE_GENERATION (the strict checker wanted "
                        f"property-based instances). Orchestrator auto-"
                        f"chained `verify_with_examples`, which returned "
                        f"`{ex_verdict}`.\n"
                        f"{feedback}{ex_feedback}"
                        "Decide the next action based on the chained "
                        "example-verifier result."
                    )
                except (WorkerTimeoutError, RuntimeError) as e:
                    kind = ("timed out"
                            if isinstance(e, WorkerTimeoutError) else "errored")
                    print(f"[orchestrator] auto-chained "
                          f"verify_with_examples {kind}: {e}", flush=True)
                    # Record the failed chain attempt in history so the
                    # next manager turn sees what was tried (and the
                    # run-summary post-mortem doesn't lose the trace).
                    state.history.append(TurnRecord(
                        turn, "verify_with_examples",
                        "(auto-chained from verify_equivalence_strict)",
                        f"WORKER {kind.upper()}: {e}"))
                    extra_note = (
                        f"`verify_equivalence_strict` returned "
                        f"EXAMPLE_GENERATION. The orchestrator tried to "
                        f"auto-chain `verify_with_examples` but it "
                        f"{kind}: {e}.{feedback}"
                        "Dispatch `verify_with_examples` yourself, or "
                        "pick another action."
                    )
            # `simplify_proof` has inverted semantics worth spelling out:
            # PASS = couldn't find a simpler proof, the existing one is fine;
            # FAIL = a concrete simpler alternative was proposed.
            elif action == "simplify_proof":
                if verdict == "PASS":
                    extra_note = (
                        "`simplify_proof` returned PASS: the verifier could "
                        "NOT find a simpler proof. The existing Lean proof "
                        "is therefore confirmed acceptable as-is -- keep it "
                        "and proceed to `solved`."
                    )
                else:
                    extra_note = (
                        f"`simplify_proof` returned {verdict}; a simpler "
                        f"alternative was proposed.{feedback}"
                        "Dispatch the prover (and `correct_tex_proof` first "
                        "if the TeX sketch needs to mirror) to apply it."
                    )
            else:
                extra_note = (
                    f"`{action}` verdict: {verdict}.{feedback}"
                    "Decide the next action."
                )

        elif action == "reorder":
            # Auto-applied with verification: a `verify_reorder` worker
            # judges whether the proposed dependencies should really precede
            # this row. On PASS we move them ahead, clear this row's Lean
            # state, copy any progress notes into `tips`, and exit so the
            # next invocation picks up the new first-unsolved row.
            outcome = _apply_reorder_if_verified(state, data, body, turn)
            state.history.append(TurnRecord(turn, action, body, outcome["summary"]))
            save_data(state.data_path, data)
            if outcome["applied"]:
                print(f"[orchestrator] reorder applied -- ending row run.",
                      flush=True)
                return
            extra_note = outcome["feedback_for_manager"]

        elif action == "continue_agent":
            # Body format:
            #   AGENT_ID: <session_id>
            #   <message to send to the resumed agent>
            try:
                outcome = _continue_agent_from_body(state, body, turn)
            except (WorkerTimeoutError, RuntimeError) as e:
                kind = ("timed out"
                        if isinstance(e, WorkerTimeoutError) else "errored")
                print(f"[orchestrator] continue_agent {kind}: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER {kind.upper()}: {e}"))
                extra_note = (
                    f"The resumed agent {kind} on subprocess call (after "
                    f"the orchestrator's built-in retries). Try a fresh "
                    f"spawn (`spawn_agent_sub_task`) instead, or hand off "
                    f"via `new_manager`."
                )
                save_data(state.data_path, data)
                persist_time()
                continue
            state.history.append(TurnRecord(turn, action, body,
                                            outcome["summary"]))
            extra_note = outcome["feedback_for_manager"]

        elif action == "request_from_human":
            # Gated: first few attempts get encouragement; only after
            # HUMAN_REQUEST_THRESHOLD consecutive calls do we actually write
            # the request to disk and stop.
            outcome = _handle_request_from_human(state, body, data)
            state.history.append(TurnRecord(turn, action, body,
                                            outcome["summary"]))
            save_data(state.data_path, data)
            if outcome["should_stop"]:
                append_unsolved_run_summary(
                    state, reason="request_from_human threshold reached -- "
                    "request written to chapter file, awaiting human reply",
                )
                return
            extra_note = outcome["feedback_for_manager"]

        elif action in ACTION_TO_WORKER:
            # Standard worker dispatch.
            worker_prompt = build_worker_prompt(action, body, state)
            try:
                worker_reply, sess = run_claude(
                    worker_prompt,
                    label=f"t{turn:03d}_worker_{action}",
                )
            except (WorkerTimeoutError, RuntimeError) as e:
                kind = ("timed out"
                        if isinstance(e, WorkerTimeoutError) else "errored")
                print(f"[orchestrator] worker `{action}` {kind}: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER {kind.upper()}: {e}"))
                extra_note = (
                    f"The dispatched worker for action `{action}` {kind} "
                    f"on subprocess call (after the orchestrator's built-in "
                    f"retries). Files this worker was editing may be left "
                    f"in a partial / inconsistent state. Decide how to "
                    f"proceed: re-dispatch `{action}` (same input), pick a "
                    f"different action, hand off to a fresh manager via "
                    f"`new_manager`, or dispatch a cleanup worker to "
                    f"inspect and revert the partial files."
                )
                save_data(state.data_path, data)
                persist_time()
                continue
            _register_agent(state.row, kind=action, session_id=sess)
            worker_summary = summarise(worker_reply)
            state.history.append(TurnRecord(turn, action, body, worker_summary))

        else:
            # An unrecognised action -- log it, tell the manager, keep going.
            state.history.append(TurnRecord(turn, action, body, ""))
            extra_note = (
                f"Unknown action `{action}`. Valid actions are listed in "
                "manager.md."
            )

        save_data(state.data_path, data)
        persist_time()

      print(f"[orchestrator] hit MAX_TURNS={MAX_TURNS}; stopping.", flush=True)
      append_unsolved_run_summary(
          state, reason=f"MAX_TURNS={MAX_TURNS} reached without solving",
      )
    finally:
        # Persist any unflushed wall-clock so an interrupted run resumes
        # from the right baseline next time. Also uninstall the module
        # hook so a future caller doesn't accidentally trip our stale
        # tracker on its own usage-limit sleeps.
        persist_time()
        _ACTIVE_TRACKER_SLEEP_CB = None


def solve_chapter(data_path: Path | None = None) -> None:
    """Iterate :func:`solve_current_row` over the given data.json until all
    rows are solved, or this run can't make progress.

    By default operates on the current chapter (as recorded in
    ``global_vars.json``); pass ``data_path`` to operate on a refactor
    table or any other data.json file in the same row-table format.

    Each iteration resolves at most one row (the first unsolved). The loop
    stops if:
      * the table has no unsolved rows left,
      * a single iteration solves nothing new (e.g. ``request_from_human``
        wrote a request and exited, or the row hit its turn cap / budget --
        in which case the next invocation will resume from where we left off),
      * or :func:`solve_current_row` raises (the orchestrator logs and
        bails so a future run can pick up the trail).

    `data.json` is the source of truth, so re-running this script after a
    stop just continues where the previous invocation left off -- no special
    resumption logic is needed.
    """
    if data_path is None:
        chapter = read_current_chapter()
        data_path = find_chapter_data_path(chapter)
    iteration = 0
    while True:
        iteration += 1
        data = load_data(data_path)
        solved_before = sum(1 for r in data["rows"] if r.get("solved") == "yes")
        unsolved = [r for r in data["rows"] if r.get("solved") != "yes"]
        print(f"[solve_chapter] iteration {iteration} "
              f"({data_path}): {solved_before}/{len(data['rows'])} solved, "
              f"{len(unsolved)} remaining", flush=True)
        if not unsolved:
            print(f"[solve_chapter] table complete: {data_path}", flush=True)
            return
        try:
            solve_current_row(data_path)
        except Exception as e:               # noqa: BLE001 - top-level guard
            print(f"[solve_chapter] solve_current_row raised: {e}",
                  flush=True)
            return
        # Detect "no progress" iterations and stop so we don't busy-loop --
        # the next invocation can retry.
        data_after = load_data(data_path)
        solved_after = sum(
            1 for r in data_after["rows"] if r.get("solved") == "yes"
        )
        if solved_after <= solved_before:
            print(f"[solve_chapter] no row solved this iteration "
                  f"(still {solved_after}/{len(data_after['rows'])}); "
                  f"stopping cleanly.", flush=True)
            return


# ---------------------------------------------------------------------------

def _parse_cli_args(argv: list[str]) -> argparse.Namespace:
    """Parse CLI args for the solve_chapter entrypoint.

    Three mutually-exclusive invocation modes:

    - ``solve_chapter.py`` (no args)            -- use current chapter from
                                                   ``global_vars.json``
                                                   (existing behavior).
    - ``solve_chapter.py --chapter N``          -- explicit chapter number;
                                                   does NOT touch
                                                   ``global_vars.json``.
    - ``solve_chapter.py --data-path PATH``     -- arbitrary data.json
                                                   (refactor table, etc.).
    """
    parser = argparse.ArgumentParser(
        description="Drive a row table (chapter data.json or refactor "
                    "table) to fully-solved via the manager/worker loop."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--chapter", type=int, default=None,
        help="explicit chapter number (defaults to current_chapter from "
             "global_vars.json)",
    )
    group.add_argument(
        "--data-path", type=Path, default=None,
        help="path to a data.json file (e.g., a refactor table); "
             "alternative to --chapter for non-default tables",
    )
    return parser.parse_args(argv)


if __name__ == "__main__":
    try:
        args = _parse_cli_args(sys.argv[1:])
        if args.data_path is not None:
            solve_chapter(args.data_path)
        elif args.chapter is not None:
            solve_chapter(find_chapter_data_path(args.chapter))
        else:
            solve_chapter()      # default: current chapter from global_vars
    except Exception as e:                 # noqa: BLE001 - top-level safety net
        print(f"[orchestrator] fatal: {e}", file=sys.stderr, flush=True)
        sys.exit(1)
