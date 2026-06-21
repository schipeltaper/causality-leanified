# Causality Leanified

Lean 4 formalisation of causal-inference lecture notes, driven by a manager/worker swarm of Claude Code agents.

## How to use this workflow

### Solve the next unsolved row of a chapter

```bash
python scaffold/scripts/phase3_solving/solve_chapter.py --chapter 3
```

Picks the first row with `solved != "yes"` in `leanification/Chapter3_GraphTheory/data.json`, spawns a manager agent (with the contract at `scaffold/claude_prompts/phase3_solving/manager.md`), and drives it through the action loop until the row lands `solved="yes"` (or a budget runs out / the human is asked).

### Refactor a foundational definition (and its transitive consumers)

When a row's formalisation reveals an upstream encoding bug:

```bash
# Manager emits `refactor` during a normal row solve; a plan markdown
# is written to leanification/refactors/refactor_<name>.md.
# Then, on server_setting_up_scaffold:
python extras/do_refactor.py init --chapter N --root-refs def_X_Y,def_X_Z --name <name>
```

This creates `refactor_<name>` branch, runs `find_dependents.py` per root (transitive scan via rename + lake build), and builds `Refactor_<name>/refactor_data.json` (the refactor row table). Then drive the table end-to-end:

```bash
scaffold/scripts/run_refactor_pipeline.sh \
    leanification/ChapterN_*/Refactor_<name>/refactor_data.json
```

Chains **solve → finalize (apply_refactor_cleanup, 8 phases) → merge** back to `server_setting_up_scaffold`. Logs to `/tmp/refactor_pipeline_<name>.log`.

### Commit

Always via `scaffold/build_and_commit.sh "msg"` — the only sanctioned commit path. Runs `lake build` first, then `git add -A && git commit && git push`. The orchestrator uses this automatically per solved row.

## Where things live

### Content (`leanification/`)
- `Chapter<N>_<Title>/` — per-chapter Lean source, tex twins under `Section<N>_<M>/tex/`, and `data.json` (the row table)
- `Chapter<N>_<Title>/Refactor_<name>/` — active refactor tables (archived to `Refactor_<name>_DONE_<date>/` after finalize)
- `refactors/refactor_<name>.md` — refactor plan markdowns (one per refactor)
- `deviations.json` — register of documented deviations from the LN

### Source (`lecture-notes/`)
- Original course materials being formalised — read-only from the formalisation's perspective.

### Scaffold (`scaffold/`)
- `scripts/phase3_solving/solve_chapter.py` — row-solver entry point
- `scripts/run_refactor_pipeline.sh` — end-to-end refactor wrapper
- `claude_prompts/phase3_solving/manager.md` — agent contract (load-bearing)
- `claude_prompts/phase3_solving/row_workers/` — per-action worker prompts (one file per dispatchable worker)
- `build_and_commit.sh` — sanctioned commit path
- `tex_templates/` — tex stubs the orchestrator instantiates
- `global_vars.json` — current chapter number, etc.

### Refactor tooling (`extras/`)
- `do_refactor.py` — `init` / `finalize` / `merge` orchestration
- `apply_refactor_cleanup.py` — the 8-phase Phase 7 cleanup (Lean marker swap, lake build, tex twin swap, data.json sync, deviation register, stale-file cleanup, archive)
- `find_dependents.py` — transitive-consumer scan (rename + lake build to discover who depends on a given decl)
- `initialize_refactor.py` — builds the refactor row table from the dependency scan
- `audit_chapter.py` — chapter-wide consistency check

### Website (`building_website/`)
- Separate batch pipeline that consumes `Chapter*/Section*/tex/<ref>_for_website.json` payloads (auto-generated per row at solve-time) and renders the public site.

## Branches

- `main` — release branch (do not push directly)
- `server_setting_up_scaffold` — working trunk where rows are solved and refactors merge back
- `refactor_<name>` — one per active refactor, branched off `server_setting_up_scaffold`, merged back via `do_refactor.py merge`
- `website_builder` — separate website-builder track; merges into `main` via PR

## Conventions worth knowing

- **Marker convention** (Lean): refactor rows wrap pre-refactor decls in `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <Name>` / `END` and post-refactor twins in `REFACTOR-BLOCK-REPLACEMENT-BEGIN: <Name> (was: refactor_<Name>)` / `END`. Genuine deletions use `REFACTOR-BLOCK-DELETE-BEGIN/END: <Name>` (no replacement). See `scaffold/claude_prompts/phase3_solving/manager.md` § Refactor rows for the full rule set.

- **Statement marker** (Lean): each row's main `def`/`theorem` is wrapped in `-- <ref> -- start statement` / `end statement`. For record-literal defs (`def foo : T where { fields }`), the end marker sits AFTER the last `where` field, not after the type annotation.

- **Tex twins** (claim rows only): refactor proofs are written to `tex/refactor_<ref>_proof_<title>.tex`; cleanup renames over the original.
