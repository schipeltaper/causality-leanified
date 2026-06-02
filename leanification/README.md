# `leanification/` — phases overview

This is the Lean-formalization workspace. The folder is currently **empty** (clean slate; the prior content is in `archive/2026-06-02-pre-clean-slate/leanification/`).

The project moves a chapter from "LN tex" to "fully formalized Lean" through several phases. **Initialization** runs once per chapter, top-to-bottom; **row-solving** runs many times, one row at a time, until every row is `solved=yes`.

Below is the canonical phase order. Operator-driven steps are marked **[human]**; orchestrator-driven steps are marked **[agent]**.

---

## Phase 0 — LN authoring (outside this folder)

**[human]** Author / edit `lecture-notes/lecture_notes/*.tex`. Wrap every definition in `\begin{defmark}...\end{defmark}` and every claim in `\begin{claimmark}...\end{claimmark}`. The orchestrator detects these marks to build the chapter's row list.

**[human]** Read your own LN once with fresh eyes. Convince yourself that what's written matches what you mean — at least at the level of "the wording you read this morning is the wording you'd write today". Subtle drift (`%commented-out` constraints, ambiguous quantifiers, "if any" parentheticals) is what later phases catch, but obvious drift you should catch now.

## Phase 1 — Chapter initialization

**[human / agent]** Run

```bash
python scaffold/initialize_chapter.py
```

This reads the LN, populates `leanification/Chapter<N>_<Title>/data.json` (one row per defmark / claimmark), creates the section folders, inserts `% <ref>` comments in the LN tex source (so an agent can locate each block later), and registers the chapter's globs in `lakefile.toml`.

Each `data.json` row has the columns listed in `scaffold/initialize_chapter.py` (search for `"columns"`). Most are filled at init; `addition_to_the_LN` (see Phase 3) is filled later.

## Phase 2 — Initial subtlety check

**[agent]** Run

```bash
python scaffold/initial_subtlety_checker.py --chapter <N>
```

For every row in this chapter's `data.json`, the orchestrator spawns the `check_ln_wording` worker on the row's LN tex block. The worker is told to look for *wording-internal* issues — ambiguity, unintended-looking corner cases admitted by the literal reading, internal inconsistencies, arbitrary or unclear phrases. It is **not** doing Lean-vs-LN equivalence; only LN-itself sanity.

Every subtlety it finds is appended to `leanification/initial_subtlety_register.json` with `id`, `explanation`, and `observed_by_ref` (the row that surfaced it).

Idempotent: re-running skips rows whose subtleties are already on file. Pass `--force` to re-check every row.

## Phase 3 — Human decides on each subtlety

**[agent]** Run

```bash
python scaffold/generate_initialization_table.py --chapter <N>
```

This writes `leanification/Chapter<N>_<Title>/initialization_table.md` — a markdown document with one section per entry in the initial register. Each section shows the subtlety's `id`, the observing row, the worker's `explanation`, and a `Decision` code-block initialised to `TODO`.

**[human]** Open the file. For each subtlety, replace `TODO` with **one** of:

- `NONE` — no addition to the LN needed; the formalizer should treat the literal LN reading as authoritative on this point.
- A free-form clarifying clause — written as if it were an extra sentence appended to the LN. It will be conjoined with the literal LN when an equivalence-checker worker runs.

Examples of useful additions:

> "Only bidirected hinges count; backward-E edges as n=1 bifurcations are excluded."
>
> "A bifurcation between v and w requires both endnodes to have exactly one arrowhead pointing toward them."
>
> "L is treated as a symmetric subset of `V × V` with the irreflexivity constraint, not as a quotient set."

At the bottom of the file is an **"Additional notes (global)"** section. Anything written under `### Notes` here is treated as a global addition merged into **every** row's `addition_to_the_LN` (prefixed with `[global]`). Use this for project-wide assumptions like "every CDMG is assumed to have a finite vertex set".

When you're done, save the file.

## Phase 4 — Process the table

**[agent]** Run

```bash
python scaffold/process_initialization_table.py --chapter <N>
```

This reads `initialization_table.md`, extracts each decision plus the global notes, and writes them to the corresponding rows' `addition_to_the_LN` field in `data.json` (one paragraph per decision, prefixed with the subtlety id; global notes appended with a `[global]` prefix).

After this, **initialization is complete**. `data.json` is the authoritative spec — its LN block (`tex_block`) plus `addition_to_the_LN` define what every formalization must satisfy.

## Phase 5 — Row solving

**[agent]** Run

```bash
python scaffold/solve_chapter.py
```

The orchestrator picks the first unsolved row, spawns a manager, the manager spawns workers, the manager iterates until `solved=yes`. Repeat for every row. The full workflow is documented in `scaffold/claude_prompts/manager.md`.

Two register files are written during this phase:

- **`leanification/deviations.json`** — recorded when a manager calls `accept_deviation` (a Lean encoding doesn't literally match the LN's wording but the manager has decided the gap is tolerable). Bypasses the strict-equivalence gate.

- **`leanification/working_subtlety_register.json`** — recorded when a manager calls `register_ln_subtlety` (a wording issue spotted *during* row-solving that wasn't surfaced at initialization). **Informational only — never halts, never bypasses, never gates.** Paper trail for future debuggers.

The equivalence-checker workers (`verify_equivalence`, `verify_equivalence_strict`, `verify_with_examples`) treat `tex_block + addition_to_the_LN` as the authoritative spec. The literal LN and the human-authored addition are conjoined; the Lean encoding must satisfy both.

## Phase 6 — Refactor (when needed)

If something is wrong at the encoding level (a definition's shape needs to change), use the refactor workflow. Documented in `scaffold/claude_prompts/manager.md` under "Refactor rows" and driven by `extras/do_refactor.py init / finalize / merge`. Refactors run on dedicated branches (`refactor_<name>`) off `server_setting_up_scaffold`.

---

## File / folder layout (when populated)

```
leanification/
├── README.md                            <- this file
├── Causality.lean                       <- library root; imports chapter aggregators
├── Chapter<N>_<Title>.lean              <- chapter aggregator (auto-managed)
├── preamble.tex                         <- shared tex preamble
├── Chapter<N>_<Title>/
│   ├── data.json                        <- per-chapter row table (the spec)
│   ├── initialization_table.md          <- human decision table (Phase 3)
│   ├── request_from_human.tex           <- agent → human escalation channel
│   └── Section<N>_<M>/                  <- one folder per LN subsection
│       ├── main.tex                     <- auto-managed aggregator
│       ├── tex/                         <- per-row tex subfiles
│       ├── workspace_<ref>.md           <- per-row manager scratchpad
│       └── <Title>.lean                 <- the formalization
├── deviations.json                      <- Lean-vs-LN deviations (Phase 5)
├── initial_subtlety_register.json       <- LN-wording subtleties from Phase 2
└── working_subtlety_register.json       <- LN-wording subtleties from Phase 5
```

The two subtlety registers are **distinct** by design:

- `initial_subtlety_register.json` is populated en bloc at chapter init and **resolved** into `addition_to_the_LN` columns by Phase 4. Once Phase 4 runs, these entries are historical record only.
- `working_subtlety_register.json` is populated incrementally during row-solving when a manager spots something the initial check missed. Entries here are never resolved automatically — they sit as a paper trail for later humans / managers to consult.

Both are informational. `deviations.json` is the only register whose entries have semantic effect on the orchestrator (bypassing the strict-equivalence gate when `accept_deviation` fires).
