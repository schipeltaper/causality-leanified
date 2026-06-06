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

**Goal:** A chapter `data.json` that has, for every row (def or claim), all the spec the row-solver needs: LN tex block, target lean / tex file paths, and `addition_to_the_LN` — a human-authored strengthening / disambiguation derived from the LN-wording check. **End state:** `data.json` ready to be solved.

### Step 2a — Build the row table

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/initialize_chapter.py
```

This:
- Resolves the chapter folder name (`Chapter<N>_<PascalCaseTitle>/`).
- Walks the marked tex file (and any `\input`'d sub-files), extracts every `defmark` / `claimmark` block in source order, and assigns refs (`def_<N>_<i>`, `claim_<N>_<j>`).
- Writes `leanification/Chapter<N>_<Title>/data.json` with one row per ref. Schema in `scaffold/scripts/phase2_initialization/initialize_chapter.py` (search `"columns"`); `addition_to_the_LN` starts empty.
- Creates section subfolders and inserts `% <ref>` comments in the LN tex so future agents can locate each block.
- Registers the chapter's globs in `lakefile.toml` and imports the chapter aggregator from `Causality.lean`.

### Step 2b — Initial subtlety check

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/initial_subtlety_checker.py --chapter <N>
```

For every row, spawns the `check_ln_wording` worker on the row's LN tex block. The worker looks for **LN-internal** issues — ambiguity, unintended-looking corner cases admitted by the literal reading, internal inconsistencies, arbitrary or unclear phrasing. It is **not** doing any Lean-vs-LN comparison; only LN-itself sanity.

Findings are appended to `leanification/initial_subtlety_register.json` with `id`, `explanation`, `observed_by_ref`.

Idempotent: re-running skips rows whose subtleties are already on file. `--force` re-checks every row.

### Step 2c — Generate the decision table

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/generate_initialization_table.py --chapter <N>
```

Writes `leanification/Chapter<N>_<Title>/initialization_table.md` — one section per registered subtlety, each with a `Decision` block initialised to `TODO`. The file ends with an **"Additional notes (global)"** section for project-wide LN additions that aren't tied to a specific subtlety.

### Step 2d — Human fills in the table

**[human]** Open the table. For each subtlety, replace `TODO` with one of:

- `NONE` — no addition needed; literal LN is authoritative on this point.
- A free-form clarifying clause — written as if it were an extra sentence appended to the LN. It is **conjoined** with the literal LN when equivalence-checker workers run.

Examples:

> "Only bidirected hinges count; backward-E edges as n=1 bifurcations are excluded."
>
> "A bifurcation between v and w requires both endnodes to have exactly one arrowhead pointing toward them."
>
> "L is treated as a symmetric subset of `V × V` with the irreflexivity constraint, not as a quotient set."

Under `### Notes`, write project-wide assumptions like "every CDMG is assumed to have a finite vertex set" — these merge into every row's addition with a `[global]` prefix.

### Step 2e — Process the table into data.json

**[agent]** Run

```bash
python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter <N>
```

Reads the filled-in table, folds each decision into the observing row's `addition_to_the_LN` field, and prefixes global notes onto every row.

**End of Phase 2.** `data.json`'s `tex_block + addition_to_the_LN` columns together form the authoritative spec for Phase 3.

---

## Phase 3 — Solving the table (formalize every row)

**Goal:** Every row in the chapter's `data.json` has `solved=yes`. Lean files are written, tex proof subfiles are written, design choices are commented, equivalence checkers pass. **End state:** chapter fully formalized.

### How

**[agent]** Run

```bash
python scaffold/scripts/phase3_solving/solve_chapter.py
```

The orchestrator picks the first unsolved row, spawns a manager (Opus 4.7 1M-context), the manager spawns workers (formalize, verify_equivalence, verify_tex_proof, …), the manager iterates until the row passes the three-stage solved-gate (sorry-check, friendly equivalence, strict equivalence). The full row-solving workflow lives in `scaffold/claude_prompts/phase3_solving/manager.md`.

The equivalence checkers (`verify_equivalence`, `verify_equivalence_strict`, `verify_with_examples`) treat **`tex_block + addition_to_the_LN`** as the authoritative spec — the formalization must satisfy the literal LN **AND** every clause in the addition.

### Two informational registers fill up during this phase

- **`leanification/deviations.json`** — written when a manager emits `accept_deviation` (a Lean encoding diverges from the LN's literal wording but the manager has decided the gap is acceptable; bypasses the next strict-equivalence gate). The deviation register IS load-bearing: `accept_deviation` is refused for any id the active refactor is meant to resolve.
- **`leanification/working_subtlety_register.json`** — written when a manager emits `register_ln_subtlety` (a wording oddity spotted during row-solving that wasn't surfaced by Phase 2). Informational only — never gates anything.

### Refactor happens inside Phase 3

If a row reveals that an upstream def's *shape* needs to change (not just the proof), the manager emits `refactor` (with rationale + the new root ref) and the operator runs:

```bash
python extras/do_refactor.py init --chapter <N> --root-refs <ref>[,<ref>...] --name <name>
```

This spawns a fresh `refactor_<name>` branch off `server_setting_up_scaffold`, runs `find_dependents.py` per root, builds a `Refactor_<name>/refactor_data.json` (the table of root + every transitive consumer), and the operator drives that table to completion via `solve_chapter.py --data-path <refactor table>`. When all refactor rows are `solved=yes`:

```bash
python extras/do_refactor.py finalize --refactor-data <refactor table>
python extras/do_refactor.py merge --refactor-data <archived table> --push --delete-remote-branch
```

Finalize swaps every `REFACTOR-BLOCK-REPLACEMENT` block over its `REFACTOR-BLOCK-ORIGINAL` counterpart, runs the post-rename `lake build`, syncs `data.json`, and archives the refactor folder. Merge brings the refactored state back into the source branch. The full refactor lifecycle is in `scaffold/claude_prompts/phase3_solving/manager.md` under "Refactor rows".

**Inside a refactor row**, the `refactor` action *restarts the entire refactor* with an expanded root set (current roots + new ref). The current refactor branch is discarded; a fresh branch is spawned off the source branch. The rationale lives at `Refactor_<new_name>/extension_rationale.md` on the new branch.

---

## Phase 4 — Verifying results (outside this workflow)

**Goal:** A human reads every solved row and confirms that the Lean statement / proof matches the LN's intent. **End state:** the human signs off; the chapter is considered fully formalized for downstream use.

This is **not** an orchestrator-driven phase — it's manual sanity-checking by you (or another mathematician). The orchestrator's strict-equivalence gate caught what it could; this phase catches what only a human reader can.

### Suggested checks per row

- **Statement equivalence.** Read the Lean declaration (`def` / `theorem` / `lemma`) and compare to the LN block. Same hypotheses? Same conclusion? Same quantifier order? Any silently-dropped sub-clause?
- **Addition consistency.** If `addition_to_the_LN` is non-empty, does the Lean encoding actually reflect it? (The strict-equivalence worker is supposed to enforce this, but verify.)
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
│   │   └── check_ln_wording.md                     <- prompt for the wording-check worker
│   │                                                  (also re-used in Phase 3 row-solving)
│   ├── phase3_solving/
│   │   ├── manager.md                              <- the per-row manager prompt
│   │   └── row_workers/                            <- worker prompts dispatched by the manager
│   │       ├── formalize_definition_in_lean.md
│   │       ├── formalize_claim_in_lean.md
│   │       ├── verify_equivalence.md
│   │       ├── verify_equivalence_strict.md
│   │       ├── verify_with_examples.md
│   │       ├── verify_tex_proof.md
│   │       ├── correct_tex_proof.md
│   │       ├── expand_tex_proof.md
│   │       ├── review_design.md
│   │       ├── add_design_choice_comments.md
│   │       ├── plan_subtasks.md
│   │       ├── plan_refactor.md
│   │       ├── refactor_lean_code.md
│   │       └── … (one per row-worker action)
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
    │   └── prep_chapter.py                         <- runs the LN marking agent (uses
    │                                                  claude_prompts/phase1_pre_initialization/)
    │
    ├── phase2_initialization/
    │   ├── initialize_chapter.py                   <- builds Chapter<N>_<Title>/data.json
    │   ├── create_data.py                          <- helper: walks tex for marks, makes rows
    │   ├── initial_subtlety_checker.py             <- runs check_ln_wording on every row
    │   ├── generate_initialization_table.py        <- writes initialization_table.md
    │   └── process_initialization_table.py         <- folds human answers into addition_to_the_LN
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
├── Causality.lean                       <- library root; imports chapter aggregators
├── Chapter<N>_<Title>.lean              <- chapter aggregator (auto-managed)
├── preamble.tex                         <- shared tex preamble
├── Chapter<N>_<Title>/
│   ├── data.json                        <- the spec (Phase 2 builds this)
│   ├── initialization_table.md          <- human decision table (Phase 2c, filled in Phase 2d)
│   ├── request_from_human.tex           <- agent → human escalation channel
│   └── Section<N>_<M>/                  <- one folder per LN subsection
│       ├── main.tex                     <- auto-managed aggregator
│       ├── tex/                         <- per-row tex subfiles
│       ├── workspace_<ref>.md           <- per-row manager scratchpad
│       └── <Title>.lean                 <- the formalization
├── deviations.json                      <- Lean-vs-LN deviations (Phase 3)
├── initial_subtlety_register.json       <- LN-wording subtleties (Phase 2b)
└── working_subtlety_register.json       <- LN-wording subtleties (Phase 3)
```

### The three registers, distinguished

| Register | Phase | Effect |
|---|---|---|
| `deviations.json` | Phase 3 (`accept_deviation`) | **Load-bearing.** Bypasses the strict-equivalence solved-gate on the next attempt; `accept_deviation` is refused for any id the active refactor is meant to resolve. |
| `initial_subtlety_register.json` | Phase 2b | **Transient.** Entries are resolved into `addition_to_the_LN` columns by Phase 2e. After Phase 2, the register is historical record. |
| `working_subtlety_register.json` | Phase 3 (`register_ln_subtlety`) | **Informational.** Never gates anything. Paper trail for future debuggers — grep here when an unexplained tension surfaces in a later row. |
