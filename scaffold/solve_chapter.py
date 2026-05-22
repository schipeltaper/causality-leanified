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

5. Loop until the row is solved, the human is needed, or the 8-hour budget is
   used up.

The manager itself does no file I/O -- it is a pure reasoner. Workers do the
labour (editing Lean files, building, etc.). Python keeps the state.
"""

from __future__ import annotations

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
MAX_RUNTIME_SECONDS = 8 * 60 * 60          # 8 hours

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
    "verify_tex_proof":    ("verify_tex_proof.md",    "tex_proof_verifier"),
    "review_design":       ("review_design.md",       "design_reviewer"),
    "verify_equivalence":  ("verify_equivalence.md",  "equivalence_verifier"),
    "simplify_proof":      ("simplify_proof.md",      "simplifier"),
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

    - For a def row: ``<ref>_<title>.tex``                  (kind_suffix=None)
    - For a claim row: ``<ref>_<statement|proof>_<title>.tex``
    """
    ref = row["ref"]
    title = row.get("title") or "Untitled"
    if row["def_or_claim"] == "def":
        return f"{ref}_{title}.tex"
    assert kind_suffix in ("statement", "proof"), \
        "claim rows need kind_suffix 'statement' or 'proof'"
    return f"{ref}_{kind_suffix}_{title}.tex"


def _row_subfile_paths(row: dict, subsection_folder: Path) -> list[Path]:
    """Every subfile path a row contributes to (1 for a def, 2 for a claim).

    All per-row tex files live under ``<subsection_folder>/tex/`` so the
    subsection folder itself stays tidy (only ``main.tex`` + Lean files +
    workspace markdown end up there).
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


def cleanup_row_artefacts(row: dict, subsection_folder: Path) -> None:
    """Remove transient artefacts once a row is marked solved.

    Anything that was only useful for *getting to* solved gets dropped:

    - ``workspace_<ref>.md`` -- the manager's scratchpad. Anything worth
      keeping should have been moved into Lean comments by the workers.
    - ``agent_registry`` -- the list of past Claude session ids the manager
      used during the active solving phase. With the row done, those
      sessions are no longer something anyone needs to resume.

    Tex stubs, Lean files, ``actions_tracking`` (kept as project-level
    analytics) and the formal status fields (``formalized``/``proven``/
    ``solved``/``lean_files``/``date_solved``) all stay.

    The caller must ``save_data()`` after this to persist the cleared
    ``agent_registry``.
    """
    wp = workspace_path_for_row(row, subsection_folder)
    if wp.exists():
        wp.unlink()
    row["agent_registry"] = []


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
               retries: int = 1,
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
    cmd = ["claude", "-p", prompt, "--dangerously-skip-permissions",
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
                cmd, capture_output=True, text=True,
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
        print(f"[run_claude] '{label}' exited {result.returncode} on attempt "
              f"{attempt}; retrying...", flush=True)

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
    target_dir = ensure_subsection_folder(state.data_path.parent,
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
    return (
        f"## Row context\n"
        f"- chapter: {state.chapter}\n"
        f"- ref: {row['ref']}\n"
        f"- title: {row.get('title', '')}\n"
        f"- kind: {row['def_or_claim']}\n"
        f"- section: {row.get('section', '')}\n"
        f"- type: {row.get('type', '')}\n"
        f"- tex_file: {row['tex_file']}\n"
        f"- chapter folder (data.json + request_from_human.tex live here): "
        f"{state.data_path.parent}\n"
        f"- target subsection folder (put Lean files + tex files here): "
        f"{target_dir}\n"
        f"- workspace scratchpad (yours to write plans/notes in): {workspace}\n"
        f"- current state: formalized={row['formalized']} "
        f"proven={row['proven']} solved={row['solved']}\n"
        f"\n## Source block from the lecture notes\n"
        f"```latex\n{tex_block}\n```\n"
        f"{tips_block}{registry_block}"
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
    matching worker prompt + the row context + the manager's claim."""
    worker_file, _ = VERIFIER_ACTIONS[action]
    return (
        f"{read_worker_prompt(worker_file)}\n\n"
        f"{render_row_context(state)}\n"
        f"## Manager's claim\n{body}\n"
    )


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

def solve_current_row() -> None:
    """Drive the first unsolved row of the current chapter to ``solved``.

    Stops on any of: row reaches a terminal state, 8-hour budget exhausted,
    or MAX_TURNS reached. The data.json is saved after every meaningful state
    change so an interrupted run leaves a recoverable trail.

    Per-row wall-clock is accumulated in ``row["time_needed_to_solve"]``
    (seconds). The counter only advances while *this* function is on the
    stack -- across-session waits don't count, but in-session sleeps
    (usage-limit pauses, subprocess work) do. A ``try / finally`` around
    the loop guarantees that every exit path persists the partial time so
    the next invocation resumes from the right baseline.
    """
    chapter = read_current_chapter()
    data_path = find_chapter_data_path(chapter)
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
            print(f"[orchestrator] 8-hour budget exhausted after {turn-1} "
                  f"turns; stopping.", flush=True)
            append_unsolved_run_summary(
                state,
                reason=f"8-hour budget exhausted after {turn-1} turns",
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
            except WorkerTimeoutError as e:
                print(f"[orchestrator] solved-verifier timed out: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER TIMED OUT: {e}"))
                extra_note = (
                    f"The `verify_row_solved` worker hit the per-call "
                    f"timeout ({PER_CALL_TIMEOUT_SECONDS//60} min) and was "
                    f"killed. Files may be in an inconsistent state. "
                    f"Decide the next action -- you can retry `solved`, "
                    f"hand off to a fresh manager, or dispatch a cleanup."
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
                proven = "disproven" if any(
                    h.action == "mistake" for h in state.history
                ) else "proven"
                mark_solved(state.row, kind, lean_files=lean_files,
                            main_lean_file=main_lean_file, verdict=proven)
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
                    if subsection_is_complete(data, section):
                        print(f"[orchestrator] section {section} now fully "
                              f"solved -- building aggregate main.tex",
                              flush=True)
                        build_subsection_main_tex(subsection_folder)
                # Save AFTER cleanup so the cleared agent_registry is persisted.
                save_data(state.data_path, data)
                print(f"[orchestrator] {state.ref} marked solved "
                      f"({proven}); lean_files={lean_files or '(unreported)'}",
                      flush=True)
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
            # Heavy redesign: dispatch the refactor-planner worker to
            # identify every affected ref across all chapter data.json files,
            # mark them unsolved with a refactor tip, delete their Lean
            # files, and write the plan to
            # `leanification/refactors/refactor_<title>.json`.
            #
            # After the worker returns we end this run -- the next
            # solve_chapter iteration will pick up the new first-unsolved
            # (typically the redesign target, which is earlier than this row).
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
            save_data(state.data_path, data)
            print(f"[orchestrator] refactor planner ran; ending row run so "
                  f"the next iteration picks up the new first-unsolved.",
                  flush=True)
            append_unsolved_run_summary(
                state,
                reason="refactor dispatched -- this row may have been "
                "marked unsolved by the planner; re-running solve_chapter "
                "will pick up the (possibly earlier) first-unsolved row.",
            )
            return

        elif action == "mistake":
            # `mistake` is a state signal: the manager has concluded the
            # claim is genuinely false and is switching to the disprove
            # flow. No worker dispatch; the signal lives in state.history
            # so that `mark_solved` later sees it and writes
            # proven="disproven". The manager now proceeds with the SAME
            # workflow as proving, just on the negation.
            state.history.append(TurnRecord(turn, action, body,
                                            "(disprove flow engaged)"))
            extra_note = (
                "`mistake` recorded -- you're now in disprove mode. "
                "Proceed with the EXACT SAME workflow as proving a claim, "
                "but on the NEGATION: spawn `write_tex_proof.md` to write a "
                "tex proof of NOT-claim, run `verify_tex_proof`, then "
                "spawn `prove_claim_in_lean.md` to leanify the negation, "
                "then `simplify_proof`, then `solved`. The orchestrator "
                "will set `proven=\"disproven\"` automatically when the "
                "row is marked solved."
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
            except WorkerTimeoutError as e:
                print(f"[orchestrator] {action} verifier timed out: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER TIMED OUT: {e}"))
                extra_note = (
                    f"The `{action}` verifier hit the per-call timeout "
                    f"({PER_CALL_TIMEOUT_SECONDS//60} min) and was killed. "
                    f"Pick a different action or retry `{action}`."
                )
                save_data(state.data_path, data)
                persist_time()
                continue
            _register_agent(state.row, kind=action, session_id=sess)
            worker_summary = summarise(verifier_reply)
            state.history.append(TurnRecord(turn, action, body, worker_summary))
            v_match = re.search(r"^VERDICT:\s*(PASS|FAIL)\b",
                                verifier_reply,
                                re.MULTILINE | re.IGNORECASE)
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
            # `simplify_proof` has inverted semantics worth spelling out:
            # PASS = couldn't find a simpler proof, the existing one is fine;
            # FAIL = a concrete simpler alternative was proposed.
            if action == "simplify_proof":
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
            except WorkerTimeoutError as e:
                print(f"[orchestrator] continue_agent timed out: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER TIMED OUT: {e}"))
                extra_note = (
                    f"The resumed agent hit the per-call timeout "
                    f"({PER_CALL_TIMEOUT_SECONDS//60} min) and was killed. "
                    f"Try a fresh spawn (`spawn_agent_sub_task`) instead, "
                    f"or hand off via `new_manager`."
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
            except WorkerTimeoutError as e:
                print(f"[orchestrator] worker `{action}` timed out: {e}",
                      flush=True)
                state.history.append(TurnRecord(
                    turn, action, body, f"WORKER TIMED OUT: {e}"))
                extra_note = (
                    f"The dispatched worker for action `{action}` hit the "
                    f"per-call timeout ({PER_CALL_TIMEOUT_SECONDS//60} min) "
                    f"and was killed. Files this worker was editing may be "
                    f"left in a partial / inconsistent state. Decide how to "
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


def solve_chapter() -> None:
    """Iterate :func:`solve_current_row` over the current chapter until all
    rows are solved, or this run can't make progress.

    Each iteration resolves at most one row (the first unsolved). The loop
    stops if:
      * the chapter has no unsolved rows left,
      * a single iteration solves nothing new (e.g. ``request_from_human``
        wrote a request and exited, or the row hit its turn cap / budget --
        in which case the next invocation will resume from where we left off),
      * or :func:`solve_current_row` raises (the orchestrator logs and
        bails so a future run can pick up the trail).

    `data.json` is the source of truth, so re-running this script after a
    stop just continues where the previous invocation left off -- no special
    resumption logic is needed.
    """
    chapter = read_current_chapter()
    data_path = find_chapter_data_path(chapter)
    iteration = 0
    while True:
        iteration += 1
        data = load_data(data_path)
        solved_before = sum(1 for r in data["rows"] if r.get("solved") == "yes")
        unsolved = [r for r in data["rows"] if r.get("solved") != "yes"]
        print(f"[solve_chapter] iteration {iteration}: "
              f"{solved_before}/{len(data['rows'])} solved, "
              f"{len(unsolved)} remaining", flush=True)
        if not unsolved:
            print("[solve_chapter] chapter complete.", flush=True)
            return
        try:
            solve_current_row()
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

if __name__ == "__main__":
    try:
        solve_chapter()
    except Exception as e:                 # noqa: BLE001 - top-level safety net
        print(f"[orchestrator] fatal: {e}", file=sys.stderr, flush=True)
        sys.exit(1)
