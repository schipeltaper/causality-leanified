# Workflow explained — leanifying the causality lecture notes

This document explains, end to end, how the scaffold in this repo turns the lecture notes (`lecture-notes/lecture_notes/`) into Lean 4 formalizations under `leanification/`. It covers the data model, the two top-level workflows (chapter initialization and row solving), every action a manager agent can emit, every worker prompt, and the key Python functions involved — with file paths so you can jump to the code.

The intended reader is either a human contributor coming back to this project after a few weeks or a Claude agent loaded into the project for the first time.

---

## 1. The big picture

The project is a swarm of Claude Code agents, orchestrated by a small amount of Python in `scaffold/`. The work is structured around three persistent artefacts:

- **The lecture notes** — the source of truth, in `lecture-notes/lecture_notes/`. We do not change them beyond a few comment markers added by the `find_def_claim` agent at init.
- **`data.json` files** — one per chapter, under `leanification/Chapter<N>_<Title>/data.json`. Each row describes one definition or claim from the lecture notes and tracks its formalization status.
- **The Lean library** under `leanification/` — built by `lake build` from the repo root. Module structure mirrors chapter/subsection folders, so a file at `leanification/Chapter3_GraphTheory/Section3_1/CDMG.lean` has module name `Chapter3_GraphTheory.Section3_1.CDMG`.

The Python code in `scaffold/` is **not the formalizer**. It is a thin loop that:
- holds the state (`data.json`, on-disk files),
- spawns Claude agents via `claude -p` subprocesses to do focused units of work,
- parses each agent's reply for a structured action tag,
- dispatches the next agent based on that action.

Every spawned agent runs on **Opus 4.7 1M context window at `--effort max`** (`CLAUDE_MODEL` and `CLAUDE_EFFORT` in `scaffold/scripts/phase3_solving/solve_chapter.py`). Every subprocess call uses `--output-format json` so the orchestrator can capture each agent's session id and let the manager **resume past agents** by id (see §6 and §7).

```
┌───────────────────────────────────────────────────────────────────────────┐
│                       scaffold/ (Python orchestrator)                     │
│                                                                           │
│  global_vars.json    initialize_chapter.py    solve_chapter.py      │
│         │                    │                       │                    │
│         └────── current_chapter ───────────┐         │                    │
│                                            ▼         ▼                    │
│                                  leanification/Chapter<N>_<Title>/        │
│                                  ├── data.json     ← project state        │
│                                  ├── request_from_human.tex (per chapter) │
│                                  └── Section<N>_<M>/                      │
│                                      ├── main.tex  ← auto-generated      │
│                                      ├── workspace_<ref>.md (per row)     │
│                                      ├── def_<ref>_<title>.tex            │
│                                      ├── <ref>_statement_<title>.tex      │
│                                      ├── <ref>_proof_<title>.tex          │
│                                      └── <Title>.lean                     │
└───────────────────────────────────────────────────────────────────────────┘
         ▲                                                  │
         │                                                  ▼
         │           claude -p --model claude-opus-4-7[1m] --effort max
         │                       --output-format json
         │                                              │
         │                                              ▼
         │     ┌──────────────────────────────────────────────────────┐
         │     │  manager.md  +  row_workers/*.md                     │
         │     │  (per-turn prompt; agents read these to know what    │
         │     │  to do; their reply ends with BEGIN[action]/END)     │
         │     └──────────────────────────────────────────────────────┘
         │                                              │
         └──────── action tag + session_id (parsed) ◄───┘
```

---

## 2. The data model — one chapter, one `data.json`

Canonical column order (see `scaffold/scripts/phase2_initialization/initialize_chapter.py:create_data`):

| field | type | meaning |
| --- | --- | --- |
| `def_or_claim` | `"def"` or `"claim"` | what kind of LN object this row tracks |
| `ref` | string | unique identifier: `def_<ch>_<n>` or `claim_<ch>_<n>`, e.g. `claim_3_5` |
| `section` | string | the subsection number from the LN, e.g. `"3.1"`. Empty for marks before any `\subsection` |
| `title` | short PascalCase string | filename-safe label used in `def_<ref>_<title>.tex`, etc. Auto-extracted from `\begin{Env}[…]` where possible, otherwise filled by a per-row title-picker agent at init |
| `type` | string | the LaTeX environment kind: `definition`, `theorem`, `lemma`, `remark`, `notation`, … (see `ENV_TYPES` in `scaffold/scripts/phase2_initialization/create_data.py`) |
| `formalized` | `"yes"` / `"no"` | a Lean declaration matching the LN block exists |
| `proven` | `"proven"` / `"disproven"` / `"not proven"` / `"n/a"` | claims only; `"n/a"` for defs |
| `solved` | `"yes"` / `"no"` | overall checkmark: def → formalized; claim → formalized AND (proven OR disproven) |
| `date_solved` | ISO date string | populated when `solved` flips to `"yes"` |
| `tips` | string | accumulated free-form notes — populated by a successful `reorder` (preserves rationale + the deferred row's progress) |
| `tex_file` | string | the `.tex` file in the LN that contains this row's block (e.g. `graphs.tex`) |
| `main_lean_file` | string | the canonical Lean file containing the row's statement (verifier reports `MAIN_LEAN_FILE:` on PASS) |
| `lean_files` | list of strings | repo-relative paths to every Lean file the row produced; multi-item rows have multiple |
| `actions_tracking` | dict\<action, int\> | one counter per valid `ACTIONS` entry; incremented whenever the manager emits that action |
| `tex_block` | string | verbatim content of the row's `\begin{defmark}…\end{defmark}` or `\begin{claimmark}…\end{claimmark}` |
| `agent_registry` | list of {kind, spawned_by, session_id, first_seen, last_used} | every Claude agent spawned for this row. Manager addresses past agents via `continue_agent`. |

The `columns` list at the top of each `data.json` is a documentation mirror of the schema.

On-disk layout per chapter:

```
leanification/
├── preamble.tex                          shared TeX preamble (bundled from LN)
├── Causality.lean                        Lean lib root; imports each chapter aggregator
├── Chapter3_GraphTheory.lean             chapter aggregator; auto-managed, imports every solved row
└── Chapter3_GraphTheory/
    ├── data.json                         per-chapter state
    ├── request_from_human.tex            communication channel between swarm and human
    └── Section3_1/
        ├── main.tex                      auto-generated subsection aggregator
        ├── workspace_<ref>.md            per-row scratchpad (manager's notes/plan/history)
        ├── def_<ref>_<title>.tex         per def row
        ├── <ref>_statement_<title>.tex   per claim row (statement)
        ├── <ref>_proof_<title>.tex       per claim row (proof)
        └── CDMG.lean, ...                Lean declarations
```

`main.tex` per subsection and `<Chapter>.lean` aggregator are **auto-managed** — Python rewrites them. `workspace_<ref>.md` is created as a stub at row pre-flight; manager and workers append to it freely. `request_from_human.tex` is created once per chapter at init.

---

## 3. Chapter initialization

**Entry point:** `python3 scaffold/scripts/phase2_initialization/initialize_chapter.py` (calls `initialize()`).

Assumes `scaffold/global_vars.json` has the right `current_chapter` set.

| step | function | location | what it does |
| --- | --- | --- | --- |
| 1 | `get_title_and_tex_file_chapter(chapter)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | walks `lecture-notes/lecture_notes/main.tex`'s `\input` chain, counts `\section{...}` titles, returns `(title, tex_file)` for the chapter-th one |
| 2 | `create_folder(chapter, title)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | makes `leanification/Chapter<N>_<PascalCaseTitle>/` |
| 3 | `create_data(chapter, title)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | drops an empty `data.json` with the schema's `columns` list |
| 4 | `ensure_chapter_aggregator_stub(module)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | writes `leanification/Chapter<N>_<Title>.lean` (empty aggregator with header comment) |
| 5 | `ensure_lakefile_globs_for_chapter(module)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | idempotently adds `"Chapter<N>_<Title>"` and `"Chapter<N>_<Title>.+"` to the `Causality` lib's `globs` in `lakefile.toml` |
| 6 | `ensure_causality_imports_chapter(module)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | appends `import Chapter<N>_<Title>` to `leanification/Causality.lean` |
| 7 | `mark_defs_and_claims(chapter, tex_file)` | `scaffold/scripts/phase2_initialization/initialize_chapter.py` | spawns the `find_def_claim` agent (`scaffold/claude_prompts/phase1_pre_initialization/mark_definitions_and_claims_in_tex.md`); the agent edits the LN tex in place, wrapping every def with `\begin{defmark}` / `\end{defmark}` and every claim with `\begin{claimmark}` / `\end{claimmark}` |
| 8 | `fill_data(chapter, tex_file, data_path)` | `scaffold/scripts/phase2_initialization/create_data.py` | walks the marked tex file, extracts one row per mark in render order with `kind`, `type`, `section`, `tex_block`, and an auto-extracted `title` (via `_extract_title`). `_insert_ref_markers` also adds `% def_<n>` / `% claim_<n>` comment lines above each block so the row's location is greppable. |
| 9 | **title pass** | `scaffold/scripts/phase2_initialization/initialize_chapter.py:initialize` | for every row whose title is still empty (no `\begin{Env}[…]` argument in the LN), spawn `pick_title_for_row` (`scaffold/scripts/phase3_solving/solve_chapter.py`) — a one-shot claude call with a focused prompt that returns a short PascalCase identifier |
| 10 | `regenerate_subsection_main_tex(data_path, data, section)` | `scaffold/scripts/phase3_solving/solve_chapter.py` | for every section with rows, writes `Section<N>_<M>/main.tex` from the template and creates per-row subfile stubs via `ensure_row_subfiles` (def: tex_block content; claim_statement: tex_block content; claim_proof: `% TODO` placeholder) |
| 11 | `ensure_request_from_human_file(chapter_folder)` | `scaffold/scripts/phase3_solving/solve_chapter.py` | drops `leanification/Chapter<N>_<Title>/request_from_human.tex` from the template so the human-request channel exists from the start |

Result: chapter folder is wired up, `lake build` is green, the data file has one row per mark in lecture-notes order each with a meaningful title, every subsection has a `main.tex` aggregator and pre-populated tex stubs, and the human-request channel is ready.

---

## 4. Solving one row

**Entry point:** `python3 scaffold/scripts/phase3_solving/solve_chapter.py` (calls `solve_current_row()`).

Each invocation drives the first unsolved row to a terminal state (`solved="yes"`, or an applied `reorder`, or a written-out `request_from_human`). Re-invoke in a loop to walk through a whole chapter.

### 4.1 Pre-flight

Before the manager loop starts:

1. Read `current_chapter` from `scaffold/global_vars.json`.
2. Locate the chapter's `data.json` via `find_chapter_data_path` (matches the `Chapter<N>_` prefix).
3. Find the first row whose `solved` is not `"yes"` via `first_unsolved_row_index`.
4. If that row's `title` is empty, spawn `pick_title_for_row` and save the result.
5. `regenerate_subsection_main_tex(...)` for the row's section — copies `scaffold/tex_templates/preamble.tex` to `leanification/preamble.tex` if missing/stale, ensures the subsection folder exists, ensures every row's tex subfiles exist (filled from `tex_block` for def/statement; `% TODO` for proof), rewrites `Section<N>_<M>/main.tex` with `\subfile{…}` lines.
6. `ensure_row_workspace(...)` — creates `workspace_<ref>.md` in the subsection folder if missing (the manager's per-row scratchpad).
7. `ensure_request_from_human_file(...)` — drops the chapter's `request_from_human.tex` if it isn't there yet.

When the manager wakes up for turn 1, every artefact it might need already exists as a stub — it only has to fill in bodies and coordinate.

### 4.2 The manager loop

For each turn (up to `MAX_TURNS = 200`, capped by `MAX_RUNTIME_SECONDS = 8 hours`):

1. **Build the manager prompt** via `build_manager_prompt(state)`:
    - `scaffold/claude_prompts/phase3_solving/manager.md` (the full instructions),
    - the row context (`render_row_context`) — `ref`, `kind`, `section`, `title`, `tex_file`, subsection folder, **workspace path**, **agent registry** listing every past agent spawned for this row, the **carried-over tips**, current state of `formalized`/`proven`/`solved`, and the verbatim `tex_block`,
    - the running history of previous turns (`render_history`),
    - any one-off `extra_note` from the orchestrator (e.g. verifier feedback parsed from a `BEGIN[feedback]…END[feedback]` block).
2. **Spawn the manager** via `run_claude` — `subprocess.run(["claude", "-p", <prompt>, "--dangerously-skip-permissions", "--model", "claude-opus-4-7[1m]", "--effort", "max", "--output-format", "json"])`. The returned JSON envelope yields `(text, session_id)`. The session id is recorded in the row's `agent_registry`.
3. **Parse the action tag** with `parse_action_tag`. The manager's reply must end with `BEGIN[<action>]\n<body>\nEND[<action>]`. On parse failure, `extra_note` is set to a corrective note that **repeats the full action list** (pulled from `ACTIONS` in `scaffold/scripts/phase2_initialization/create_data.py`); next turn the manager tries again.
4. **Increment `actions_tracking[action]`** for the row (`increment_action_count`).
5. **Dispatch on action** (see §5). Most handlers either:
    - spawn a worker (`run_claude` with a worker prompt + the row context + the manager's body) — session id captured into registry,
    - spawn a verifier and parse `VERDICT: PASS/FAIL` and `BEGIN[feedback]…END[feedback]`,
    - mutate row state (`mark_solved`) on the `solved` action when the verifier passes,
    - or directly mutate state (`reorder`, `request_from_human`) — these can also end the run.
6. **Save `data.json`** after every turn. Interrupted runs are recoverable.

The loop ends when the row is marked solved, the manager triggers an approved `reorder`, the gated `request_from_human` actually fires, the budget/turn-cap expires, or a fatal error occurs.

### 4.3 What happens on `solved`

1. The orchestrator dispatches `verify_row_solved` as a final-gate check (`build_verifier_prompt`).
2. The reply is scanned for `VERDICT: PASS` / `VERDICT: FAIL` (anywhere). On PASS, also `LEAN_FILES:` (comma-separated or repeated) and `MAIN_LEAN_FILE:` are extracted.
3. On PASS: `mark_solved(row, kind, lean_files, main_lean_file, verdict)` writes the terminal fields. The chapter aggregator (`regenerate_chapter_aggregator`) and the subsection's `main.tex` (`regenerate_subsection_main_tex`) are refreshed. The loop returns.
4. On FAIL: the verifier's tagged feedback (between `BEGIN[feedback]` and `END[feedback]`) is surfaced to the manager as `extra_note`. The manager tries again — there is no auto-escalation; the loop keeps going until the row solves or the budget/turn-cap runs out. (If the manager wants to escalate to the human anyway, it has `request_from_human` — gated by repeated-attempts.)

---

## 5. The action set

The list lives in `scaffold/scripts/phase2_initialization/create_data.py` (`ACTIONS`) — that is the single source of truth. Adding a new action means appending there (so the row's `actions_tracking` counter exists) and wiring it into one of the dispatch maps in `scaffold/scripts/phase3_solving/solve_chapter.py`.

Three dispatch tables in the orchestrator:

- **`ACTION_TO_WORKER`** — actions that spawn a single worker. Key → worker prompt filename under `row_workers/`. `None` value means the manager's body itself is the worker's prompt (used by `spawn_agent_sub_task`).
- **`VERIFIER_ACTIONS`** — actions that spawn a verifier-style worker and parse `VERDICT: PASS/FAIL` (+ `BEGIN[feedback]…END[feedback]` on FAIL). Key → (prompt filename, log-label suffix).
- **Inline handlers** — `solved`, `reorder`, `continue_agent`, `request_from_human`, `no_action`, `reset`, `new_manager`, and the catch-all "unknown action" branch are handled directly inside `solve_current_row`.

### 5.1 Worker actions (dispatch a single worker)

| action | worker prompt | what the worker does |
| --- | --- | --- |
| `spawn_agent_sub_task` | (the manager's body is the prompt) | catch-all dispatch. The manager pastes the worker's prompt + context inline. Used for `formalize_definition_in_lean`, `formalize_claim_in_lean`, `write_tex_proof`, `prove_claim_in_lean`, etc. |
| `expand_proof` | `row_workers/expand_tex_proof.md` | expand one specific too-sketchy step in an existing tex proof, without rewriting the rest |
| `correct_tex_proof` | `row_workers/correct_tex_proof.md` | rewrite a tex proof to fix a *mistake* surfaced by the leanifier |
| `make_plan` / `decompose` | `row_workers/plan_subtasks.md` | break a chunky job into ordered subtasks; returns a plan (worker writes it into the row's `workspace_<ref>.md`) |
| `refactor` | `row_workers/refactor_lean_code.md` | structural cleanup of Lean code in the subsection |
| `mistake` | `row_workers/document_counterexample.md` | when a claim is genuinely false: construct a counter-example in Lean and document the LN mistake |

### 5.2 Verifier actions (dispatch + parse `VERDICT:`)

| action | worker prompt | scope |
| --- | --- | --- |
| `review_design` | `row_workers/review_design.md` | reads the **whole lecture notes**, judges whether the Lean *shape* (def, structure, class, …) is natural and composes well with downstream chapters |
| `verify_equivalence` | `row_workers/verify_equivalence.md` | focused check: every LN hypothesis present in Lean, every LN conclusion matched, no quiet drops |
| `verify_tex_proof` | `row_workers/verify_tex_proof.md` | independent check that a standalone tex proof is complete: file exists, ref prefix, no `sorry`/"omitted", citations valid, LN paradigm |
| `simplify_proof` | `row_workers/simplify_proof.md` | reads the **whole lecture notes**, asks "is this Lean proof unnecessarily complex?" Semantics: **PASS = couldn't find a simpler proof, keep the existing one**; FAIL = a concrete simpler alternative was proposed |

All four: their reply contains `VERDICT: PASS` or `VERDICT: FAIL`. On FAIL the verifier wraps its actionable feedback in `BEGIN[feedback]…END[feedback]`; the orchestrator extracts and feeds it to the manager.

### 5.3 Inline-handled actions

| action | effect |
| --- | --- |
| `solved` | dispatches `verify_row_solved` as the final gate. On PASS, parses `LEAN_FILES:` + `MAIN_LEAN_FILE:` and flips the row to `solved="yes"`. On FAIL, surfaces tagged feedback to the manager. |
| `continue_agent` | resumes a past agent by `AGENT_ID: <session_id>` (pulled from the row's `agent_registry`). The rest of the body is sent to that agent via `claude -p -r <id>`. Used when the manager wants to give the *original* tex writer (or leanifier, or any past worker) new feedback without starting over. |
| `reorder` | the body's `PRECEDES: <ref>, <ref>, ...` line names refs that should be solved before the current row. The orchestrator dispatches a verifier inline; on PASS it moves those refs ahead of the current row, **clears this row's Lean state** (deletes its `lean_files`, resets `formalized`/`proven`/`solved`), preserves the rationale in `tips`, and exits the run so the next invocation picks up the new first-unsolved row. |
| `new_manager` | clears the manager's running history; the next turn starts fresh with the manager's body as a handoff dossier. Used at natural phase boundaries (tex proof done → leanify) or when context gets large. |
| `reset` | clears history and restarts the manager from scratch (no dossier preserved). |
| `request_from_human` | **last resort, gated.** The first `HUMAN_REQUEST_THRESHOLD - 1` consecutive attempts get a nudge back ("are you sure you've tried everything?"); only the threshold-th call actually appends the request to `leanification/Chapter<N>_<Title>/request_from_human.tex` and stops the run. The human writes their answer in the Answers section of that file; the next row run picks it up. |
| `no_action` | the manager couldn't decide; orchestrator nudges it to pick a real action next turn. |
| (unknown action) | logged, manager is told the action is invalid and the full list of valid actions is repeated; loop continues. |

---

## 6. The agent registry — resuming past agents

Every Claude subprocess call uses `--output-format json`. The JSON envelope returns `{"result": "<text>", "session_id": "<uuid>"}`. The orchestrator captures the session id and appends an entry to the current row's `agent_registry`:

```json
{
  "kind": "write_tex_proof",
  "spawned_by": "manager",
  "session_id": "session-abc-123-...",
  "first_seen": "2026-05-19T11:00:32",
  "last_used": "2026-05-19T11:00:32"
}
```

The manager sees this registry in its row context (the most recent ~15 entries). When it wants to talk back to a specific past agent — e.g. the tex writer the leanifier just refuted — it emits:

```
BEGIN[continue_agent]
AGENT_ID: session-abc-123-...
<message to send to the resumed agent>
END[continue_agent]
```

The orchestrator's handler (`_continue_agent_from_body`) parses the agent id, runs `claude -p <message> -r <session_id>` which resumes the original conversation, and surfaces the reply to the manager. This is **cheaper than re-spawning** (the agent has its full prior context) and lets you correct a chain of decisions without restarting from scratch.

---

## 7. Typical flows

### 7.1 A definition row

```
manager turn 1 → spawn_agent_sub_task → formalize_definition_in_lean.md
   ↳ worker writes Lean file(s); fills in body of def_<ref>_<title>.tex
manager turn 2 → review_design (full LN context)
   ↳ PASS → continue;  FAIL → feedback surfaced via BEGIN[feedback]/END[feedback];
                       manager re-dispatches the formalizer with the feedback
manager turn 3 → verify_equivalence
   ↳ PASS → continue;  FAIL → same pattern
manager turn 4 → solved → orchestrator dispatches verify_row_solved
   ↳ PASS → mark_solved writes formalized="yes", solved="yes",
            lean_files=[...], main_lean_file=<canonical>
   ↳ FAIL → feedback to manager; loop continues until budget runs out
```

### 7.2 A claim row — two managers (statement, then the whole proof)

A claim row passes through **exactly two manager agents**: one handles the statement, then a single fresh manager handles the *whole* proof (TeX + Lean) — there is no third manager.

**Manager A — statement only:**

```
manager A → spawn_agent_sub_task → formalize_claim_in_lean.md
manager A → review_design       (statement-level, full LN context)
manager A → verify_equivalence
manager A → new_manager
   ↳ body is the handoff dossier (ref, statement, file paths, verifiers passed)
   ↳ history clears; manager B picks up
```

**Manager B — the proof, both TeX and Lean:**

```
manager B → spawn_agent_sub_task → write_tex_proof.md
   ↳ worker first searches the LN for an existing \begin{proof}; copies if found
manager B → verify_tex_proof
   ↳ FAIL feedback (tagged) → expand_proof on flagged step → verify_tex_proof again
manager B → spawn_agent_sub_task → prove_claim_in_lean.md
   ↳ if leanifier finds a *real* mistake in the tex proof:
        manager B → correct_tex_proof → verify_tex_proof → re-dispatch prover
        OR: manager B → continue_agent (AGENT_ID: original-tex-writer's-id)
                        to give that exact agent the leanifier's report
manager B → simplify_proof   (full LN context)
   ↳ PASS = "couldn't find a simpler proof" → keep the existing proof and go on
   ↳ FAIL with alternative (tagged) → re-dispatch prover with simpler proof
manager B → solved → verify_row_solved (final gate)
   ↳ PASS → mark_solved writes formalized="yes", proven="proven", solved="yes",
            lean_files=[...], main_lean_file=<canonical>
```

### 7.3 A claim that's actually false

```
manager → mistake → document_counterexample.md
manager → solved → verify_row_solved
   ↳ PASS → mark_solved writes formalized="yes", proven="disproven", solved="yes"
```

### 7.4 Hitting a dependency that should come first

```
manager → reorder
   body: "PRECEDES: claim_3_3
          we need claim_3_3 to be proven before this row -- the proof
          here uses it as a key lemma."
   ↳ orchestrator dispatches a reorder verifier
   ↳ PASS → claim_3_3 (etc.) moved ahead of this row;
            this row's Lean state cleared; rationale saved in `tips`;
            run exits. Next invocation picks up claim_3_3.
   ↳ FAIL → feedback to manager; row continues as before
```

### 7.5 Genuinely stuck (rare)

```
manager → request_from_human (attempt 1)
   ↳ orchestrator nudges: "Are you sure you've tried everything? Try
     decompose / new_manager / re-reading LN ..."
manager → make_plan ... new_manager ... etc.
... (genuine effort)
manager → request_from_human (attempt 2)
   ↳ same nudge
manager → request_from_human (attempt 3 == HUMAN_REQUEST_THRESHOLD)
   ↳ orchestrator appends request to leanification/Chapter<N>/request_from_human.tex
   ↳ run exits. Human writes answer in the Answers section of that file.
   ↳ Next invocation picks up the row again; manager reads the answer (which is
     in the row's file tree, accessible via Read).
```

---

## 8. Build & commit

The only sanctioned path to a commit is `scaffold/build_and_commit.sh "<msg>"` from the repo root:

1. `git add -A` — auto-stages everything in the working tree.
2. `lake build` from `/home/11716061/repo_scaffold2/` — must be clean.
3. `git commit` with the supplied message, `git config pack.packSizeLimit 50m`, `git push`.

Hard rules (in `claude.md`):
- Only the manager commits. Workers don't.
- Never raw `git commit` / `git push` / `--amend` / `--no-verify`.
- Never edit the build script to skip `lake build`.
- If the script fails, roll back and report — don't retry by issuing the commands manually.

---

## 9. Key functions, by file

### `scaffold/scripts/phase3_solving/solve_chapter.py`

- `solve_current_row()` — the main loop. Pre-flight (title, workspace, template subfiles, request-from-human file), manager loop, terminates on `solved`/applied-`reorder`/threshold-`request_from_human`/budget.
- `run_claude(prompt, label, *, resume_session=None)` — wraps `subprocess.run(["claude", "-p", ..., "--model", CLAUDE_MODEL, "--effort", CLAUDE_EFFORT, "--output-format", "json"])`. Returns `(text, session_id)`. With `resume_session` set, passes `-r <id>` so claude continues that conversation.
- `_register_agent(row, *, kind, session_id, spawned_by)` — appends to `row["agent_registry"]` (or bumps `last_used` if the id already exists).
- `parse_action_tag(text)` — regex anchored to end-of-message. On parse failure, the loop's `extra_note` repeats the full `ACTIONS` list.
- `build_manager_prompt`, `render_row_context`, `render_history` — construct the prompt the manager sees each turn (including agent registry, tips, workspace path).
- `mark_solved(row, kind, lean_files, main_lean_file, verdict)` — flips terminal row state.
- `regenerate_chapter_aggregator(data_path, data)` — rewrites `leanification/<Chapter>.lean`.
- `regenerate_subsection_main_tex(data_path, data, section)` — rewrites `Section<N>_<M>/main.tex` and ensures every row's tex subfiles exist.
- `ensure_row_workspace(row, subsection_folder)` — creates `workspace_<ref>.md` if missing.
- `ensure_request_from_human_file(chapter_folder)` — creates `request_from_human.tex` from the template if missing.
- `pick_title_for_row(row)` — one-shot Claude call to pick a short PascalCase title.
- `_apply_reorder_if_verified(state, data, body, turn)` — parses `PRECEDES:`, dispatches verifier, on PASS reorders + clears row + saves tips.
- `_continue_agent_from_body(state, body, turn)` — parses `AGENT_ID:`, resumes the session, surfaces reply to manager.
- `_handle_request_from_human(state, body, data)` — gated by `HUMAN_REQUEST_THRESHOLD`; writes to `request_from_human.tex` once threshold is hit.

### `scaffold/scripts/phase2_initialization/initialize_chapter.py`

- `initialize()` — the chapter-init entry point. Now also: runs the title-picker post-pass over rows whose title is still empty after `_extract_title`; creates `request_from_human.tex`.
- `get_title_and_tex_file_chapter(chapter)` — resolves chapter number → (title, tex_file).
- `create_folder` / `create_data` — folder + empty `data.json` with the current schema's `columns`.
- `mark_defs_and_claims(chapter, tex_file)` — spawns the `find_def_claim` agent.
- `ensure_chapter_aggregator_stub`, `ensure_lakefile_globs_for_chapter`, `ensure_causality_imports_chapter` — wire a new chapter into the Lean build (idempotent).

### `scaffold/scripts/phase2_initialization/create_data.py`

- `fill_data(chapter, tex_file, data_path)` — main parser. One row per `defmark`/`claimmark`.
- `_extract_title(tex_block)` — first-pass title extraction from `\begin{Env}[…]`.
- `ACTIONS` — single source of truth for valid action names.

### `scaffold/build_and_commit.sh`

- The only sanctioned path to a commit. Auto-stages, runs `lake build`, commits, pushes.

### `scaffold/global_vars.json`

- Holds `current_chapter`. Set this before running `initialize_chapter.py` or `solve_chapter.py`.

---

## 10. Templates

Templates live in `scaffold/tex_templates/`:

- `preamble.tex` — bundled from the LN's preamble + `thm.tex` + `shorts.tex` + `shortsjoris.tex`. Self-contained. Copied to `leanification/preamble.tex` by `ensure_preamble_at_leanification`.
- `main.tex.template` — subsection aggregator. Sets `\documentclass`, `\input`s the preamble, loads `subfiles`, `\subfile`-includes every row's tex files.
- `def.tex.template` — definition subfile. Uses `\documentclass[main]{subfiles}` so it compiles standalone too.
- `claim_statement.tex.template` — claim statement subfile.
- `claim_proof.tex.template` — claim proof subfile; body starts as a `% TODO` placeholder.
- `request_from_human.tex.template` — chapter-level communication channel.

Substitution is placeholder-based: `__REF__`, `__TITLE__`, `__SECTION__`, `__SECTION_TITLE__`, `__BODY__`, `__SUBFILE_INCLUDES__`, `__CHAPTER__`. See `_render_template` in `scaffold/scripts/phase3_solving/solve_chapter.py`.

---

## 11. Configuration knobs

All in `scaffold/scripts/phase3_solving/solve_chapter.py` (top of the file):

| name | default | meaning |
| --- | --- | --- |
| `CLAUDE_MODEL` | `"claude-opus-4-7[1m]"` | passed to every `claude -p` call (`--model`) |
| `CLAUDE_EFFORT` | `"max"` | passed as `--effort` |
| `MAX_RUNTIME_SECONDS` | `8 * 60 * 60` | total wall-clock budget per row |
| `PER_CALL_TIMEOUT_SECONDS` | `2 * 60 * 60` | timeout per subprocess call |
| `MAX_TURNS` | `200` | safety cap on manager iterations |
| `HUMAN_REQUEST_THRESHOLD` | `3` | how many consecutive `request_from_human` attempts before the request is actually written to disk and the run stops |

And in `scaffold/global_vars.json`:

| name | meaning |
| --- | --- |
| `current_chapter` | which chapter the orchestrator works on. Bump this when starting a new chapter (then re-run `initialize_chapter.py`). |

---

## 12. What is auto-managed vs. hand-edited

| file / artefact | who writes it | when |
| --- | --- | --- |
| `data.json`'s columns + initial rows | `create_data.fill_data` | once, at chapter init |
| `data.json`'s `title` | `_extract_title` then `pick_title_for_row` post-pass | at init |
| `data.json`'s `formalized` / `proven` / `solved` / `date_solved` / `lean_files` / `main_lean_file` | `mark_solved` in the orchestrator | when `verify_row_solved` PASSes |
| `data.json`'s `actions_tracking` | `increment_action_count` | every manager turn |
| `data.json`'s `agent_registry` | `_register_agent` | every claude subprocess call |
| `data.json`'s `tips` | `_apply_reorder_if_verified` (and the manager can be asked to write to it) | when reorder applies |
| `leanification/Causality.lean` | `ensure_causality_imports_chapter` | once per chapter |
| `leanification/<Chapter>.lean` | `regenerate_chapter_aggregator` | after every row solved |
| `leanification/<Chapter>/<Section>/main.tex` | `regenerate_subsection_main_tex` | row pre-flight + after solved |
| `leanification/<Chapter>/<Section>/workspace_<ref>.md` | `ensure_row_workspace` (stub) + manager and workers (body) | row pre-flight; manager writes throughout |
| `leanification/<Chapter>/<Section>/def_*.tex`, `*_statement_*.tex`, `*_proof_*.tex` (stubs) | `ensure_row_subfiles` | row pre-flight |
| Subfile bodies | the workers (`formalize_*`, `write_tex_proof`, …) | during solving |
| `leanification/<Chapter>/<Section>/*.lean` | the formalization workers | during solving |
| `leanification/<Chapter>/request_from_human.tex` | `ensure_request_from_human_file` (stub) + `_handle_request_from_human` (appends requests) + the human (answers) | once at init; appended by gated action; human writes answers |
| `lakefile.toml` `globs` | `ensure_lakefile_globs_for_chapter` | once per chapter (idempotent) |
| `leanification/preamble.tex` | `ensure_preamble_at_leanification` | once, from `scaffold/tex_templates/preamble.tex` |
| `claude.md` | the human, with explicit approval | rarely |

---

## 13. Tips for debugging a stuck run

- The orchestrator prints `[orchestrator] === turn N === (elapsed M min)` at every turn and `[orchestrator] manager chose action: <action>` after parsing. Tail the background-task output file to see live progress.
- If the manager loops on the same action: check `extra_note` flow in the dispatch handler. Verifier feedback is now surfaced via `BEGIN[feedback]/END[feedback]` extraction — if a verifier omits the tag the manager won't get actionable feedback.
- The row's `agent_registry` in `data.json` is the history of every subprocess. If the manager keeps re-spawning the same kind of worker, it could `continue_agent` instead to give feedback to the existing session — encourage this in the manager's history.
- `workspace_<ref>.md` in the subsection folder is where the manager should be writing plans and "tried-and-failed" notes. If it's empty after several turns, the manager is not using its scratchpad effectively.
- `lake build` is the hard correctness gate. Run it from the repo root manually if a Lean file looks suspicious.

---

## 14. What is *not* yet automated

- After `find_def_claim` runs, there is no human-confirmation step on whether the marks are placed correctly. The `# Wait for human confirmation` comment in `initialize_chapter.py:initialize` is a TODO.
- The bundled preamble now compiles on the server: missing packages (`bbm`, `esvect`, `oubraces`) are commented out with `\mathbbm`/`\vv` fallbacks, and macro duplicates are deduped via `\providecommand`. Individual subfiles render cleanly to PDF (`pdflatex def_3_1_CDMG.tex` succeeds). Aggregate `main.tex` can still fail to compile end-to-end if an *agent* introduced bad TeX into a subfile body (e.g. backticks in math mode); that is a content-quality concern, not a server-config one, and does not affect `lake build`.
- The `simplify_proof` failure path triggers a re-prove; coordinating the matching `correct_tex_proof` rewrite to keep the tex sketch in sync is the manager's responsibility (not auto-applied).

---

That's the scaffold end to end. The actions list (`ACTIONS` in `scaffold/scripts/phase2_initialization/create_data.py`) is the system's vocabulary; the manager prompt is its grammar; the per-row workers + verifiers are its verbs. The agent registry, the workspace scratchpad, and the carried-over tips are the memory it uses to stay coherent across turns and runs.
