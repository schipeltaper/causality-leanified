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
    "expand_proof":          "expand_tex_proof.md",
    "correct_tex_proof":     "correct_tex_proof.md",
    "refactor":              "refactor_lean_code.md",
    "make_plan":             "plan_subtasks.md",
    "decompose":             "plan_subtasks.md",
    "mistake":               "document_counterexample.md",
    "spawn_agent_sub_task":  None,   # body is the prompt
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
        f"-- Auto-managed by scaffold/solving_current_row.py; do not edit by hand.\n\n"
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
    """Every subfile path a row contributes to (1 for a def, 2 for a claim)."""
    if row["def_or_claim"] == "def":
        return [subsection_folder / _file_basename(row)]
    return [
        subsection_folder / _file_basename(row, "statement"),
        subsection_folder / _file_basename(row, "proof"),
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

    The body of a freshly-created stub is:
      - def: the inner content of the row's ``tex_block`` (no defmark wrapping)
      - claim statement: same, for the claimmark
      - claim proof: a ``TODO`` placeholder -- the proof-writing worker fills it
    """
    paths = _row_subfile_paths(row, subsection_folder)
    body_from_block = _strip_mark_wrapper(row.get("tex_block", "")).strip()
    for p in paths:
        if p.exists():
            continue
        if row["def_or_claim"] == "def":
            template, body = "def", body_from_block
        elif "_statement_" in p.name:
            template, body = "claim_statement", body_from_block
        else:
            template, body = "claim_proof", "% TODO: write the proof body."
        content = _render_template(
            template,
            REF=row["ref"],
            TITLE=row.get("title", ""),
            BODY=body,
        )
        p.write_text(content, encoding="utf-8")
    return paths


def regenerate_subsection_main_tex(data_path: Path, data: dict,
                                   section: str) -> None:
    """Rewrite ``<chapter_folder>/<Section>/main.tex`` from the template,
    listing every row's subfile(s) in lecture-notes order via ``\\subfile``.

    Per-row subfile stubs are created on the fly if they don't yet exist.
    Rows whose ``title`` is empty are skipped here -- the orchestrator
    pre-fills the title for the *active* row at row start.
    """
    if not section:
        return
    ensure_preamble_at_leanification()
    subsection_folder = ensure_subsection_folder(data_path.parent, section)
    includes: list[str] = []
    for row in data["rows"]:
        if row.get("section") != section or not row.get("title"):
            continue
        for p in ensure_row_subfiles(row, subsection_folder):
            includes.append(f"\\subfile{{{p.stem}}}")
    chapter_title = data.get("title", "")
    main_tex = _render_template(
        "main",
        SECTION=section,
        SECTION_TITLE=chapter_title,
        SUBFILE_INCLUDES="\n".join(includes) + ("\n" if includes else ""),
    )
    (subsection_folder / "main.tex").write_text(main_tex, encoding="utf-8")


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

def run_claude(prompt: str, label: str,
               *, resume_session: str | None = None) -> tuple[str, str | None]:
    """Run ``claude -p`` non-interactively and return ``(text, session_id)``.

    - The model is locked to Opus 4.7 with effort=max.
    - ``--output-format json`` is used so we can capture the conversation's
      session id; the manager can then resume any past agent via the
      ``continue_agent`` action (see :func:`run_claude_resumed`).
    - ``--dangerously-skip-permissions`` is on so workers can edit files.
    - If ``resume_session`` is given, we pass ``-r <id>`` so claude continues
      that previous conversation instead of starting a new one. The prompt
      is then the follow-up message.

    Raises ``RuntimeError`` on non-zero exit or timeout.
    """
    cmd = ["claude", "-p", prompt, "--dangerously-skip-permissions",
           "--model", CLAUDE_MODEL,
           "--effort", CLAUDE_EFFORT,
           "--output-format", "json"]
    if resume_session:
        cmd += ["-r", resume_session]
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True,
            timeout=PER_CALL_TIMEOUT_SECONDS, check=False,
        )
    except subprocess.TimeoutExpired as e:
        raise RuntimeError(f"claude call '{label}' timed out") from e

    if result.returncode != 0:
        raise RuntimeError(
            f"claude call '{label}' exited {result.returncode}: "
            f"{(result.stderr or '')[:500]}"
        )

    # Parse the JSON envelope. Fields we care about:
    #   result  -> the assistant's text reply
    #   session_id -> the conversation's id, used to resume later
    try:
        envelope = json.loads(result.stdout)
        text = envelope.get("result") or envelope.get("response") or ""
        session_id = envelope.get("session_id")
    except json.JSONDecodeError:
        # Older versions / unexpected output: degrade gracefully
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
    print(f"[orchestrator] solving {state.ref} "
          f"({state.row['def_or_claim']}, section {state.row.get('section')}) "
          f"from {data_path.name}", flush=True)

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

    extra_note: str | None = None

    for turn in range(1, MAX_TURNS + 1):
        # --- Budget check --------------------------------------------------
        if state.elapsed_seconds > MAX_RUNTIME_SECONDS:
            print(f"[orchestrator] 8-hour budget exhausted after {turn-1} "
                  f"turns; stopping.", flush=True)
            return

        # --- Manager turn --------------------------------------------------
        print(f"\n[orchestrator] === turn {turn} === "
              f"(elapsed {state.elapsed_seconds/60:.1f} min)", flush=True)
        manager_prompt = build_manager_prompt(state, extra_note=extra_note)
        extra_note = None
        manager_reply, manager_session = run_claude(
            manager_prompt, label=f"t{turn:03d}_manager")
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
            verifier_reply, sess = run_claude(
                build_verifier_prompt(state, body),
                label=f"t{turn:03d}_verifier",
            )
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
                save_data(state.data_path, data)
                regenerate_chapter_aggregator(state.data_path, data)
                regenerate_subsection_main_tex(
                    state.data_path, data, state.row.get("section", ""))
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
            verifier_reply, sess = run_claude(
                build_verifier_action_prompt(action, state, body),
                label=f"t{turn:03d}_{label_suffix}",
            )
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
            outcome = _continue_agent_from_body(state, body, turn)
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
                return
            extra_note = outcome["feedback_for_manager"]

        elif action in ACTION_TO_WORKER:
            # Standard worker dispatch.
            worker_prompt = build_worker_prompt(action, body, state)
            worker_reply, sess = run_claude(
                worker_prompt,
                label=f"t{turn:03d}_worker_{action}",
            )
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

    print(f"[orchestrator] hit MAX_TURNS={MAX_TURNS}; stopping.", flush=True)


# ---------------------------------------------------------------------------

if __name__ == "__main__":
    try:
        solve_current_row()
    except Exception as e:                 # noqa: BLE001 - top-level safety net
        print(f"[orchestrator] fatal: {e}", file=sys.stderr, flush=True)
        sys.exit(1)
