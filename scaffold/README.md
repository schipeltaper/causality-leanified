# `scaffold/` — the formalization workflow

This is the orchestration layer that drives a chapter from "LN tex" to "fully formalized Lean". The Lean artefacts themselves (per-chapter `data.json`, `Chapter<N>_<Title>/` folders, the registers) live in `leanification/` at the repo root. The scripts and prompts that *operate on* those artefacts live here.

The work is organised into **four phases per chapter**. The first three are driven by scripts in `scaffold/scripts/<phase>/`; the fourth happens outside the workflow.

Below, **[human]** = operator step; **[agent]** = orchestrator-driven step.

---

## Phase 1 — Pre-initialization (mark defs / claims in the LN, human-check)

**Goal:** Every definition and every claim (theorem, lemma, remark, paragraph-embedded note, …) in the chapter's LN tex file is wrapped with `\begin{defmark}...\end{defmark}` or `\begin{claimmark}...\end{claimmark}`. **End state:** the LN tex file is ready for Phase 2's row extraction.

### How

**[agent]** Spawn the marking agent:

```bash
python scaffold/scripts/phase1_pre_initialization/prep_chapter.py
```

This reads `current_chapter` from `scaffold/global_vars.json`, locates the chapter's tex file (via `lecture-notes/lecture_notes/main.tex` includes), and runs a Claude Code subprocess against the prompt at:

- `scaffold/claude_prompts/phase1_pre_initialization/mark_definitions_and_claims_in_tex.md`

The prompt instructs the agent to be exhaustive — every theorem, lemma, corollary, remark, plus any claim "hidden in a paragraph" or "inside a definition" gets a `\begin{claimmark}` wrapper. Defs likewise. The agent edits the tex file in place.

**[human]** Read the marked tex file. Verify:

- No def / claim was missed (especially small in-paragraph notes).
- No `defmark` / `claimmark` wraps something it shouldn't.
- Nested marks are correct (a claim inside a def is fine; the parser handles it).
- The LN as written matches what you actually mean. Subtle drift (commented-out constraints, ambiguous quantifiers, "if any" parentheticals) gets caught in Phase 2 too, but obvious drift you should fix now.

---

## Phase 2 — Initialization (build data.json + resolve subtleties)

**Goal:** A chapter `data.json` that has, for every row (def or claim), all the spec the row-solver needs: LN tex block, target lean / tex file paths, and `addition_to_the_LN` — a human-authored strengthening / disambiguation of the literal LN. **End state:** `data.json` ready to be solved.

### Step 2a — Build the row table

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/initialize_chapter.py
```

This:
- Resolves the chapter folder name (`Chapter<N>_<PascalCaseTitle>/`).
- Walks the marked tex file (and any `\input`'d sub-files), extracts every `defmark` / `claimmark` block in source order, and assigns refs (`def_<N>_<i>`, `claim_<N>_<j>`).
- Writes `leanification/Chapter<N>_<Title>/data.json` with one row per ref. Schema is defined in `scaffold/scripts/phase2_initialization/create_data.py` (search `"columns"`); `addition_to_the_LN` starts empty.
- Creates section subfolders, drops a per-row tex stub (the LN's `defmark` / `claimmark` body, pre-filled and wrapped in `\begin{Def}/\begin{Thm}/...` ready for the formalize-in-tex worker to rewrite in Phase 3), and inserts `% <ref>` comments in the LN tex so future agents can locate each block.
- Registers the chapter's globs in `lakefile.toml` and imports the chapter aggregator from `Causality.lean`.

### Step 2b — Initial subtlety check

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/initial_subtlety_checker.py --chapter <N>
```

For every row, spawns the `check_ln_wording` worker (prompt at `scaffold/claude_prompts/phase2_initialization/check_ln_wording.md`) on the row's LN tex block. The worker looks for **LN-internal** issues — ambiguity, unintended-looking corner cases admitted by the literal reading, internal inconsistencies, arbitrary or unclear phrasing. It is **not** doing any Lean-vs-LN comparison; only LN-itself sanity.

Findings are appended to `leanification/initial_subtlety_register.json` with `id`, `explanation`, `observed_by_ref`.

Idempotent: re-running skips rows whose subtleties are already on file. `--force` re-checks every row.

### Step 2c — Generate the decision table

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/generate_initialization_table.py --chapter <N>
```

Writes `leanification/Chapter<N>_<Title>/initialization_table.md` — one section per registered subtlety, each with a `Decision` block initialised to `TODO`. The file ends with two extra sections: **"Additional notes (global)"** for project-wide LN additions that aren't tied to a specific subtlety, and **"Row-specific additions"** for free-form strengthenings that apply to a single named row.

A moving HTML marker `<!-- --- processed until here --- -->` is inserted at the top — the processor in Step 2e walks decisions in order and stops at the first `TODO`, moving the marker just past every decision it processed. This lets the operator fill the table in batches.

### Step 2d — Human fills in the table

**[human]** Open the table. For each subtlety, replace `TODO` with one of:

- `NONE` — no addition recorded for this entry; the literal LN stands.
- A free-form clarifying clause — written in operator-style prose. Step 2e's agent translator will turn it into a formal self-contained clause before folding it into `addition_to_the_LN`.

Examples:

> "Only bidirected hinges count; backward-E edges as n=1 bifurcations are excluded."
>
> "A bifurcation between v and w requires both endnodes to have exactly one arrowhead pointing toward them."
>
> "L is treated as a symmetric subset of `V × V` with the irreflexivity constraint, not as a quotient set."

Under `### Additional notes (global)` write project-wide assumptions like "every CDMG is assumed to have a finite vertex set" — these merge into every row's `addition_to_the_LN` with a `[global]` prefix.

Under `### Row-specific additions` write `[<ref>] <text>` lines for strengthenings that apply to one specific row only — folded into that row alone, with a `[manual_<n>]` prefix.

### Step 2e — Process the table into data.json

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter <N>
```

For every decision between the start of the table and the first remaining `TODO`:
1. Reads the operator's casual prose.
2. Spawns the `interpret_subtlety_decision` worker (prompt at `scaffold/claude_prompts/phase2_initialization/interpret_subtlety_decision.md`), which translates the operator's prose into a formal, self-contained clarification clause that reads as an authoritative spec sentence.
3. Folds the translated clause into the observing row's `addition_to_the_LN`, prefixed with the subtlety id (e.g. `[bifurcation_endnode_arrowhead]`), `[global]`, or `[manual_<n>]` depending on the source.
4. Advances the `<!-- --- processed until here --- -->` marker so the next run picks up the next batch of decisions.

`NONE` decisions are recorded but no clause is added.

Flags:
- `--dry-run` — show what would change, write nothing.
- `--verbatim` — skip the agent translator and copy the operator's prose verbatim.
- `--reprocess-all` — strip existing translated clauses and re-translate every decision, regardless of marker position.

**End of Phase 2.** `data.json`'s `tex_block + addition_to_the_LN` columns together form the authoritative spec for Phase 3.

---

## Phase 3 — Solving the table (formalize every row)

**Goal:** Every row in the chapter's `data.json` has `solved=yes`, the row's Lean file is written and clean, the per-row tex subfiles are filled in and validated, and the row's `for_website.json` is produced. **End state:** chapter fully formalized.

### How

**[agent]** Three driver scripts, all routing through the same `solve_chapter.py` orchestrator under the hood:

```bash
python scaffold/scripts/phase3_solving/solve_chapter.py             # solve until exhausted or budget hit
python scaffold/scripts/phase3_solving/run_until.py <target_ref>    # solve until target ref is solved=yes
python scaffold/scripts/phase3_solving/run_section.py <section>     # solve every row of a section
```

The orchestrator picks the first unsolved row, spawns a **manager** agent (Opus 4.7, 1M-context, effort=max), the manager spawns workers, and the loop runs until the row passes the three-stage solved-gate.

The full row-solving workflow lives in `scaffold/claude_prompts/phase3_solving/manager.md`.

### The row-solving workflow (a chapter-3 row, from end to end)

A row's life:

```
            ┌─────────────────────────────────────────────────────────┐
            │  Statement formalization (Manager A for claims; the     │
            │  same flow for def rows ends here at `solved`)          │
            │                                                         │
   tex stub │  1. formalize_*_in_tex   → rewrites the canonical       │
   (from    │     statement tex so every addition_to_the_LN clause    │
   Phase 2) │     is folded in, every implicit quantifier is spelled  │
            │     out, visual notation is translated to set-theoretic │
            │     phrasing                                            │
            │  2. verify_tex_statement_only (structural)              │
            │  3. verify_tex_statement_equivalence (semantic, against │
            │     LN+addition) — GATE before any Lean                 │
            │  4. formalize_*_in_lean — Lean statement (def: body;    │
            │     claim: signature with `sorry`)                      │
            │  5. review_design + verify_equivalence                  │
            │     [+ verify_equivalence_strict / verify_with_examples │
            │      for defs introducing new operators / structures]   │
            │  6. add_design_choice_comments                          │
            │                                                         │
            │  def rows now jump to `solved`.                         │
            └────────────┬────────────────────────────────────────────┘
                         │  new_manager (claim rows only)
                         ▼
            ┌─────────────────────────────────────────────────────────┐
            │  Proof (Manager B for claims, prove mode)               │
            │                                                         │
            │  7. write_tex_proof — proof body into                   │
            │     <ref>_proof_<title>.tex                             │
            │  8. verify_tex_statement_plus_proof (structural)        │
            │  9. verify_tex_proof (mathematical correctness)         │
            │ 10. prove_claim_in_lean — replace the `sorry` in        │
            │     <Title>.lean with tactics                           │
            │ 11. `solved`                                            │
            └─────────────────────────────────────────────────────────┘
                         │
                         ▼
            ┌─────────────────────────────────────────────────────────┐
            │  Solved gate (orchestrator-driven; not a manager action)│
            │                                                         │
            │  a) verify_row_solved worker (LLM) — coherent solved    │
            │     state across data.json, Lean, tex.                  │
            │  b) Hard sorry-check (deterministic) — grep + lake      │
            │     build warning scan; any `sorry` in this row's Lean  │
            │     fails the gate.                                     │
            │  c) Strict-equivalence gate (LLM) — runs                │
            │     verify_equivalence_strict on the row's main Lean    │
            │     file vs LN+addition. If it returns                  │
            │     EXAMPLE_GENERATION, auto-chains                     │
            │     verify_with_examples.                               │
            │                                                         │
            │  All three must clear. On PASS: data.json updated       │
            │  (solved=yes, formalized=yes, proven=proven/n/a,        │
            │  lean_files, main_lean_file, time_needed_to_solve), the │
            │  chapter aggregator + section main.tex are regenerated, │
            │  produce_for_website runs to produce                    │
            │  <ref>_for_website.json, and the row is committed +     │
            │  pushed via build_and_commit.sh.                        │
            └─────────────────────────────────────────────────────────┘
```

### Disprove mode (for claims that turn out to be false)

If during the proof phase the manager concludes the LN claim is genuinely false, it emits `mistake`. This passes through a two-stage **mistake-sweep gate** (the orchestrator scans the deviation register for relevant upstream entries, then dispatches `verify_no_undocumented_deviation` to adversarially sweep cited defs for hidden encoding drift). Only after the sweep clears does the disprove flow engage.

The disprove flow **mirrors Manager B** step-for-step, applied to the negation. The disprove-side work goes to *separate* files so `unmistake` can flip back:

```
mistake → mistake-sweep clears
                                                             (DISPROVE)
   1. write_tex_proof          — replaces the orchestrator's
                                  NEGATION-PENDING placeholder at the
                                  top of <ref>_disproof_<title>.tex
                                  with a precise tex statement of the
                                  negation, then writes the proof of it
   2. verify_tex_statement_plus_proof   (structural)
   3. verify_tex_statement_equivalence  (the at-top statement ≡
                                         ¬(LN+addition))
   4. verify_tex_proof          — proof closes ¬claim
   5. prove_claim_in_lean       — writes new <Title>Disproof.lean with
                                  `theorem not_<original> : ¬ <claim>`
                                  (or an existential counter-example);
                                  <Title>.lean is NOT touched
   6. review_design             — shape of the negation theorem
   7. verify_equivalence        — Lean ≡ ¬(LN+addition)
   8. add_design_choice_comments on Disproof.lean
   9. `solved`
```

Every disprove-mode verifier brief MUST contain a clear `MODE: disprove` line — the worker prompts have explicit disprove-mode branches that activate on that signal. `verify_equivalence_strict` and `verify_with_examples` read disprove mode automatically from the row's `proven` field; the rest need the explicit signal.

The cleanup at solved-time, when `proven="disproven"`: deletes the prove-side `<ref>_proof_<title>.tex` + `<Title>.lean` and re-points `main_lean_file` to `<Title>Disproof.lean`.

If `unmistake` is emitted before `solved` PASSes, the reverse happens — the disprove side is the one deleted. Files persist across mistake / unmistake toggles until `solved`.

### Lean statement markers

Every Lean declaration that's part of a row's *statement formalization* is wrapped with line-comment markers the website-builder regex-extracts:

```lean
-- <ref> -- start statement
def / theorem / structure / ...
-- <ref> -- end statement
```

Helper declarations (`def` / `instance` / `notation`) the statement needs to type-check — and `variable` directives whose binders auto-bind into the wrapped statement — use a *triple*-dash variant:

```lean
-- <ref> --- start helper
variable {Node : Type*} [DecidableEq Node]
-- <ref> --- end helper

-- <ref> --- start helper
def <helper_name> := …
-- <ref> --- end helper
```

Markers must sit *immediately* adjacent to the declaration / directive — no blank lines, no comments, no docstrings between the start marker and the first line, or between the last line and the end marker. Design-choice docstrings go *above* the start marker. The extraction recipe is at `temp_for_website_builder.md` at the repo root.

### The action menu (manager → orchestrator)

Every manager turn ends with **exactly one** `BEGIN[<action>] … END[<action>]` block. The orchestrator pattern-matches the action name; valid names are listed in `scaffold/scripts/phase2_initialization/create_data.py` `ACTIONS`. The action table in `manager.md` is the canonical reference for what each does. Briefly:

- `spawn_agent_sub_task` — dispatch any focused unit of work (the body is the worker prompt + brief).
- `continue_agent` — resume a past worker by session id (cheaper than re-spawning).
- `expand_proof`, `correct_tex_proof` — tex proof manipulation.
- `verify_tex_proof`, `verify_tex_statement_only`, `verify_tex_statement_equivalence`, `verify_tex_statement_plus_proof` — tex-side verifiers.
- `review_design`, `verify_equivalence`, `verify_equivalence_strict`, `verify_with_examples` — Lean-side verifiers.
- `add_design_choice_comments` — enrich the comment block above each Lean declaration.
- `make_plan` / `decompose` — write a plan into the workspace (synonyms).
- `new_manager` — handoff to a fresh manager (used at Manager A → B for claims, or for context-budget reasons).
- `reorder` — propose this row's prerequisites should be solved first; an independent verifier judges.
- `mistake` / `unmistake` — toggle disprove mode (see above).
- `accept_deviation` — write a CONTENT deviation to the register + bypass the next strict-equivalence gate (use sparingly).
- `register_ln_subtlety` — paper-trail a wording oddity into the working subtlety register.
- `refactor` — heavy; see below.
- `request_from_human` — last-resort escape hatch, gated by a repeat-attempt threshold.
- `solved` — signal the row is done; triggers the solved gate.
- `reset`, `no_action` — rarely used.

### Two informational registers fill up during this phase

- **`leanification/deviations.json`** — written when a manager emits `accept_deviation` (a Lean encoding diverges from the LN's literal wording but the manager has decided the gap is acceptable; bypasses the next strict-equivalence gate). The deviation register IS load-bearing: `accept_deviation` is refused for any id the active refactor is meant to resolve.
- **`leanification/working_subtlety_register.json`** — written when a manager emits `register_ln_subtlety` (a wording oddity spotted during row-solving that wasn't surfaced by Phase 2). Informational only — never gates anything.

### Refactor — advisory, never destructive

If a row reveals that an upstream def's *shape* needs to change (not just the proof), the manager emits `refactor` with a rationale. The orchestrator dispatches the **advisory** `plan_refactor.md` worker, which writes a plan markdown to `leanification/refactors/refactor_<name>.md` (non-destructive — no rows reset, no Lean files deleted, no branches created), then **halts the row run** with a `Run summary` listing the next-step commands for the human:

```bash
git checkout server_setting_up_scaffold
python extras/do_refactor.py init --chapter <N> --root-refs <ref>[,<ref>...] --name <name>
python scaffold/scripts/phase3_solving/solve_chapter.py --data-path <refactor_data.json>
python extras/do_refactor.py finalize --refactor-data <path>
python extras/do_refactor.py merge --refactor-data <archived path> --push --delete-remote-branch
```

The human reads the plan markdown, confirms, and types the commands. Only then does the actual refactor pipeline run (branch creation, transitive consumer discovery, table generation). The system never auto-executes a refactor — every step from `init` onward requires explicit human invocation.

`do_refactor.py init` spawns a fresh `refactor_<name>` branch off `server_setting_up_scaffold`, runs `find_dependents.py` per root (each root gets its transitive consumer set computed via a destructive-but-restored rename probe), and builds a `Refactor_<name>/refactor_data.json` table covering root + every transitive consumer. The operator drives that table via `solve_chapter.py --data-path <refactor_data.json>`. `finalize` swaps replacement blocks over their originals via the same-file Lean marker convention, runs the post-rename `lake build`, syncs `data.json`, and archives the refactor folder. `merge` brings the refactored state back into the source branch.

**Inside a refactor row** (i.e. running `solve_chapter.py` on a `refactor_data.json`), emitting `refactor` *restarts the entire refactor* with an expanded root set (current roots + new ref). The current refactor branch is discarded; a fresh branch is spawned off the source branch. The rationale lives at `Refactor_<new_name>/extension_rationale.md` on the new branch. This is the one branch in the refactor flow that does NOT halt for human review — the implicit reasoning is that the operator already approved the parent refactor.

---

## Phase 4 — Verifying results (outside this workflow)

**Goal:** A human reads every solved row and confirms that the Lean statement / proof matches the LN's intent. **End state:** the human signs off; the chapter is considered fully formalized for downstream use.

This is **not** an orchestrator-driven phase — it's manual sanity-checking by you (or another mathematician). The orchestrator's strict-equivalence gate caught what it could; this phase catches what only a human reader can.

### Suggested checks per row

- **Statement equivalence.** Read the Lean declaration (`def` / `theorem` / `lemma`) and compare to the LN block. Same hypotheses? Same conclusion? Same quantifier order? Any silently-dropped sub-clause?
- **Addition consistency.** If `addition_to_the_LN` is non-empty, does the Lean encoding actually reflect it? (The strict-equivalence worker is supposed to enforce this, but verify.)
- **Tex-bridge vs Lean.** Open the rewritten canonical statement tex (`<ref>_statement_<title>.tex` for claims, `<ref>_<title>.tex` for defs). It is the verified intermediate the formalizer translated. If the Lean drifts from the tex bridge, that's a finding the strict equivalence checker may have missed.
- **Proof shape.** For claims: does the Lean proof structurally mirror the LN proof, or does it take a shortcut that loses the LN's intuition? (Shortcuts are fine if mathematically correct, but worth knowing.)
- **Deviations register.** Read `deviations.json`. Each entry documents a gap the system accepted; confirm each is genuinely acceptable.
- **Working subtleties register.** Read `working_subtlety_register.json`. Each entry is a wording oddity flagged during solving; decide whether any deserves a follow-up refactor.

Output of this phase is **not** a file in this repo — it's your signature on the chapter being ready. If you find issues, the right response is usually to file a refactor (Phase 3's refactor sub-workflow).

---

## `scaffold/` folder layout

The scaffold is organised so that every script and every prompt has a clear phase home. Per-phase Python scripts live in `scaffold/scripts/<phase>/`; per-phase agent prompts live in `scaffold/claude_prompts/<phase>/`. Cross-phase Python helpers live in `scaffold/scripts/utils/`. Top-level files in `scaffold/` are shared infrastructure (commit gate, current-chapter pointer, README, tex templates).

```
scaffold/
├── README.md                                       <- this file
├── build_and_commit.sh                             <- cross-phase commit gate (lake build + git push)
├── global_vars.json                                <- {"current_chapter": <N>}; read by Phases 1 + 2
├── tex_templates/                                  <- LaTeX templates used by Phases 2 + 3
│
├── claude_prompts/                                 <- agent prompts, organised by phase
│   ├── phase1_pre_initialization/
│   │   └── mark_definitions_and_claims_in_tex.md   <- prompt for the LN marking agent
│   ├── phase2_initialization/
│   │   ├── check_ln_wording.md                     <- the wording-check worker
│   │   │                                              (re-used in Phase 3 row-solving)
│   │   └── interpret_subtlety_decision.md          <- translates operator-prose decisions
│   │                                                  into formal clarification clauses
│   ├── phase3_solving/
│   │   ├── manager.md                              <- the per-row manager prompt
│   │   └── row_workers/                            <- worker prompts dispatched by the manager
│   │       │
│   │       │  Statement bridge (tex)
│   │       ├── formalize_definition_in_tex.md      <- def: rewrite canonical statement tex
│   │       ├── formalize_claim_in_tex.md           <- claim: rewrite canonical statement tex
│   │       ├── verify_tex_statement_only.md        <- structural: statement file is statement-only
│   │       ├── verify_tex_statement_equivalence.md <- semantic: tex ≡ LN+addition (or ¬spec)
│   │       │
│   │       │  Lean formalization
│   │       ├── formalize_definition_in_lean.md     <- def: translate canonical tex into Lean
│   │       ├── formalize_claim_in_lean.md          <- claim: write theorem signature with `sorry`
│   │       ├── prove_claim_in_lean.md              <- claim: leanify the verified tex proof
│   │       │                                          (or the disprove tex in disprove mode)
│   │       │
│   │       │  Tex proof
│   │       ├── write_tex_proof.md                  <- claim: write the proof body
│   │       │                                          (prove or disprove mode)
│   │       ├── verify_tex_statement_plus_proof.md  <- structural: file has statement + proof
│   │       ├── verify_tex_proof.md                 <- mathematical: proof closes the claim
│   │       │                                          (or the negation in disprove mode)
│   │       ├── correct_tex_proof.md                <- rewrite a tex proof after a leanifier
│   │       │                                          flagged a real flaw
│   │       ├── expand_tex_proof.md                 <- add detail to an under-specified step
│   │       │
│   │       │  Verifiers
│   │       ├── review_design.md                    <- full-LN-context design review
│   │       ├── verify_equivalence.md               <- focused Lean ↔ LN+addition equivalence
│   │       ├── verify_equivalence_strict.md        <- adversarial CONTENT-vs-PRESENTATION gate
│   │       ├── verify_with_examples.md             <- property-based check via instance computation
│   │       ├── verify_row_solved.md                <- final-gate verifier dispatched by `solved`
│   │       ├── verify_no_undocumented_deviation.md <- mistake-sweep Stage 2
│   │       │
│   │       │  Documentation / planning / post-solve
│   │       ├── add_design_choice_comments.md       <- enrich Lean comments with the "why"
│   │       ├── plan_subtasks.md                    <- writes a plan into workspace_<ref>.md
│   │       ├── plan_refactor.md                    <- writes an advisory refactor plan
│   │       │                                          (non-destructive; halts for human review)
│   │       ├── refactor_lean_code.md               <- light code-level cleanup (no design change)
│   │       ├── produce_for_website.md              <- post-solve: anchors + prose for the website
│   │       │
│   │       │  Legacy (kept for reference, not in the standard pipeline)
│   │       └── document_counterexample.md
│   │
│   └── phase4_verifying/                           <- (currently empty; Phase 4 is human-only)
│
└── scripts/                                        <- Python scripts, organised by phase
    ├── _path_setup.py                              <- shared sys.path helper (every per-phase
    │                                                  script imports this so cross-folder
    │                                                  imports like `from solve_chapter import …`
    │                                                  resolve regardless of caller location)
    ├── main.py                                     <- placeholder for a future top-level driver
    │
    ├── utils/                                      <- cross-phase Python helpers
    │   ├── subtlety_register.py                    <- read/write both subtlety registers
    │   ├── deviations.py                           <- read/write the deviation register
    │   └── audit_helpers.py                        <- shared dispatchers for the strict-
    │                                                  equivalence + example-verifier workers
    │
    ├── phase1_pre_initialization/
    │   └── prep_chapter.py                         <- runs the LN marking agent
    │
    ├── phase2_initialization/
    │   ├── initialize_chapter.py                   <- builds Chapter<N>_<Title>/data.json
    │   ├── create_data.py                          <- helper: walks tex for marks, makes rows
    │   ├── initial_subtlety_checker.py             <- runs check_ln_wording on every row
    │   ├── generate_initialization_table.py        <- writes initialization_table.md
    │   └── process_initialization_table.py         <- folds human answers into addition_to_the_LN
    │                                                  (via the interpret_subtlety_decision worker)
    │
    ├── phase3_solving/
    │   ├── solve_chapter.py                        <- the main row-solver orchestrator
    │   ├── run_section.py                          <- driver: solve every row of a section
    │   └── run_until.py                            <- driver: solve until a target ref is done
    │
    └── phase4_verifying/                           <- (currently empty; Phase 4 is human-only)
```

### How the per-phase Python scripts find each other

Each per-phase script has this preamble near the top:

```python
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import _path_setup  # noqa: F401
```

`_path_setup` adds every `scripts/<phase>/` folder and `scripts/utils/` to `sys.path`. After that, plain imports like `from solve_chapter import …` or `from subtlety_register import …` work regardless of which phase folder the importing script lives in. We deliberately don't use a real Python package (`__init__.py` + relative imports), because the scripts are invoked via `python scaffold/scripts/<phase>/foo.py` and we want to keep that interface.

`extras/` scripts (refactor lifecycle, audit) do the same `sys.path.insert(... / "scaffold" / "scripts")` + `import _path_setup` dance.

---

## `leanification/` folder layout (when populated)

```
leanification/
├── Causality.lean                              <- library root; imports chapter aggregators
├── Chapter<N>_<Title>.lean                     <- chapter aggregator (auto-managed by solve_chapter.py;
│                                                  imports every solved row's Lean file)
├── preamble.tex                                <- shared tex preamble
│
├── Chapter<N>_<Title>/
│   ├── data.json                               <- the spec (Phase 2 builds this)
│   ├── initialization_table.md                 <- human decision table (Phase 2c; filled in Phase 2d)
│   ├── request_from_human.tex                  <- agent → human escalation channel
│   │
│   └── Section<N>_<M>/                         <- one folder per LN subsection
│       ├── main.tex                            <- auto-managed aggregator (\subfile-includes
│       │                                          every row's tex)
│       ├── workspace_<ref>.md                  <- per-row manager scratchpad (cleared on solved)
│       ├── tex/
│       │   ├── <ref>_<title>.tex               <- def: canonical statement (rewritten by
│       │   │                                      formalize_definition_in_tex)
│       │   ├── <ref>_statement_<title>.tex     <- claim: canonical statement (rewritten by
│       │   │                                      formalize_claim_in_tex)
│       │   ├── <ref>_proof_<title>.tex         <- claim: statement + proof (prove mode)
│       │   ├── <ref>_disproof_<title>.tex      <- claim: negation statement + proof (disprove mode;
│       │   │                                      created lazily on first `mistake`)
│       │   └── <ref>_for_website.json          <- post-solve website-builder artefact
│       │
│       ├── <Title>.lean                        <- prove-side formalization
│       └── <Title>Disproof.lean                <- disprove-side formalization (only if the row
│                                                  was solved with proven="disproven")
│
├── deviations.json                             <- Lean-vs-LN deviations (Phase 3, accept_deviation)
├── initial_subtlety_register.json              <- LN-wording subtleties (Phase 2b)
├── working_subtlety_register.json              <- LN-wording subtleties (Phase 3, register_ln_subtlety)
└── refactors/
    └── refactor_<name>.md                      <- advisory refactor plans (written by
                                                    plan_refactor.md; halt for human review)
```

### The three registers, distinguished

| Register | Phase | Effect |
|---|---|---|
| `deviations.json` | Phase 3 (`accept_deviation`) | **Load-bearing.** Bypasses the strict-equivalence solved-gate on the next attempt; `accept_deviation` is refused for any id the active refactor is meant to resolve. |
| `initial_subtlety_register.json` | Phase 2b | **Transient.** Entries are resolved into `addition_to_the_LN` columns by Phase 2e. After Phase 2, the register is historical record. |
| `working_subtlety_register.json` | Phase 3 (`register_ln_subtlety`) | **Informational.** Never gates anything. Paper trail for future debuggers — grep here when an unexplained tension surfaces in a later row. |

---

## Related files at the repo root

- **`temp_for_website_builder.md`** — recipe for the downstream website-builder. For any solved row, extracts the five surface artefacts (tex statement, tex statement+proof, main Lean file path, Lean statement via markers, Lean helpers via markers). Documents the regex for both marker shapes (`-- <ref> -- start statement`, `-- <ref> --- start helper`) and the per-row payload assembly.
- **`extras/`** — refactor-lifecycle scripts (`do_refactor.py`, `find_dependents.py`, `initialize_refactor.py`, `apply_refactor_cleanup.py`) and the chapter audit driver.
- **`lecture-notes/`** — the LN source. Phase 1 marks it in place.
- **`archive/`** — pre-clean-slate snapshots. Not used by the workflow.
