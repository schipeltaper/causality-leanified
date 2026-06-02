# Refactor system — bug & update tracker

**Date opened:** 2026-05-31
**Branch:** `server_setting_up_scaffold`
**Scope:** defects in the refactor pipeline (`extras/do_refactor.py`,
`extras/initialize_refactor.py`, `extras/find_dependents.py`,
`extras/apply_refactor_cleanup.py`) and refactor-relevant code paths
inside `scaffold/solve_chapter.py`. We are about to drive
`def_3_1_no_disjoint_EL` (heavyweight, see `refactor_roadmap.md`); this
file collects every issue that should be triaged *before* we kick that
off, plus everything found during the audit that's worth fixing later.

Severity legend:
- **P0** — will break the next refactor; fix before invocation
- **P1** — likely to fire during the next refactor; should fix before
- **P2** — real but edge-case; fix when convenient
- **P3** — cleanup / nicety

---

## A. Verified bugs in the refactor pipeline (extras/)

### A1. [P1] `apply_refactor_cleanup.py` — phase 7b failure halts cleanup mid-way, no rollback

**Location:** `extras/apply_refactor_cleanup.py:660-664`

On `lake build` failure or timeout in phase 7b, the script returns 2
immediately. Phase 7a has already written swapped files to disk
(originals deleted, replacements stripped of markers, `refactor_<Name>`
→ `<Name>` renamed globally). Skipped: tex twin swap (7c), original
`data.json` sync (7d), deviation marking (7e), for-website cleanup
(7f), workspace cleanup (7g), and **folder archive (7h)**.

Re-running cleanup is awkward: 7a is a no-op (markers already gone),
7b runs again on the same broken state. The refactor folder still
exists with `solved=yes` rows; operator has to manually patch the Lean
error and re-invoke.

**Trigger:** any replacement that compiles in isolation but breaks a
downstream consumer after the global rename. Heavyweight refactors
like `def_3_1_no_disjoint_EL` make this much more likely (15-25 rows,
cross-file effects).

**Fix sketch:** either (a) make 7a record a per-file backup and revert
on 7b failure, or (b) at minimum on 7b failure still run 7h (archive
the folder) so re-runs can recover cleanly. (b) is the simpler change.

### A2. [P2] `apply_refactor_cleanup.py` + `do_refactor.py` — same-day finalize collision picks stale archive

**Location:** `extras/apply_refactor_cleanup.py:873-876` (skip) +
`extras/do_refactor.py:358-372` (`_find_archived_refactor_folder`
returns most-recent match)

If finalize runs twice on the same date (e.g., 7b failed, you patched,
re-ran), the second run hits an existing
`Refactor_<name>_DONE_<today>/` from the prior partial run, prints a
warning, skips the rename. The operator's mental model says "the
refactor is done"; in reality, the *current* `Refactor_<name>/` folder
still exists and the *old* DONE folder has stale data. Downstream
`do_refactor.py merge` reads from the stale folder.

**Fix sketch:** generate a unique suffix (e.g., `_v2`, `_HH-MM-SS`)
when the target exists, log it loudly. Alternatively: fail loudly so
the operator notices.

### A3. [P2] `apply_refactor_cleanup.py` — orphan `refactor_*` helpers survive cleanup

**Location:** `extras/apply_refactor_cleanup.py:246-253`

`rename_set = set(all_final_names) | set(local_names)` where
`local_names` only collects names declared in marker block headers
(`-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: <Name>`). If a manager writes a
helper `def refactor_Foo := …` inside a block named
`REPLACEMENT-BEGIN: Bar`, only `refactor_Bar` gets renamed;
`refactor_Foo` survives with its prefix intact. Lake build at 7b
catches this only if the helper is referenced from outside its block.

**Fix sketch:** after the marker swap, scan replacement bodies for any
identifier matching `refactor_[A-Z_]\w*` and either auto-add to the
rename set or refuse the cleanup with a clear error.

---

## B. Invalidated claims (kept for the record so we don't re-investigate)

| Claim | Reality |
|---|---|
| `do_refactor.py merge` doesn't detect conflicts and continues to push | `_git` defaults `check=True` and `sys.exit`s on non-zero. Conflict halts the script (no auto-rollback, but no false-success). |
| `include_resolved=True` snapshot corrupts the guard list | Benign — `accept_deviation` would never legitimately fire on an already-resolved id. |
| `manager-accepted` tag is never added, so 7e auto-resolve over-fires | Tag is added at `scaffold/solve_chapter.py:1928`. 7e filter works correctly. |
| `--root-ref` validated only after `find_dependents.py` lake build wastes time | `find_dependents.py:270-272` validates ref existence before any build runs. |

---

## C. `solve_chapter.py` audit findings

### C1. [P0] `reorder` deletes shared Lean files wholesale — wipes other rows' REPLACEMENT and ORIGINAL blocks

**Location:** `scaffold/solve_chapter.py:2784-2791`

```python
# Clear any partial Lean work and the row's agent registry: the row
# should be approached with a clean slate when it comes up again.
for lf in state.row.get("lean_files", []):
    p = REPO_ROOT / lf
    if p.exists():
        p.unlink()
state.row["lean_files"] = []
state.row["main_lean_file"] = ""
```

In normal mode `lean_files` is typically the row's own new file, so
unlinking is "reset this row's work". In refactor mode, the row's
REPLACEMENT block lives in a *shared* pre-existing Lean file alongside
(a) its own ORIGINAL block, (b) other refactor rows' REPLACEMENT /
ORIGINAL pairs, and (c) every unrelated declaration in that file.
`p.unlink()` obliterates the lot. There's no refactor guard.

**Trigger:** any refactor row whose manager emits `reorder`. Cluster A
touches ~13 files with many interdependencies — reorder is plausible.

**Suggested fix:** for `row["refactor"]`, do NOT unlink; instead strip
only this row's REFACTOR-BLOCK-REPLACEMENT blocks from each file in
`lean_files` and leave everything else intact. Or refuse `reorder` in
refactor mode entirely and surface a manager nudge.

### C2. [P1] `_handle_request_from_human` writes to wrong chapter folder under refactor

**Location:** `scaffold/solve_chapter.py:2632-2633`

```python
chapter_folder = state.data_path.parent
req_path = ensure_request_from_human_file(chapter_folder)
```

In refactor mode `data_path` is `…/Refactor_<name>/refactor_data.json`
so `.parent` is the refactor subfolder, not the chapter folder where
`request_from_human.tex` lives. The escalation block lands in the
wrong file; the human looking at the chapter's own
`request_from_human.tex` sees nothing. Symmetrical to C3 (same wrong
path used at setup time).

**Trigger:** any refactor row hitting the 3rd `request_from_human`
attempt (which raises `RequestFromHumanEscalated`).

**Suggested fix:** replace with `_chapter_folder_for(state.data_path)`.

### C3. [P1] `ensure_request_from_human_file` setup uses wrong parent under refactor

**Location:** `scaffold/solve_chapter.py:3258`

```python
ensure_request_from_human_file(state.data_path.parent)
```

Same `state.data_path.parent` bug as C2, this time at row setup. The
pre-seeded request file is created inside `Refactor_<name>/`, not the
chapter folder. The orchestrator and the human end up looking at
different files.

**Trigger:** every refactor row, at setup.

**Suggested fix:** replace with `_chapter_folder_for(state.data_path)`.

### C4. [P2] `_chapter_folder_for` silent fallback to `data_path.parent`

**Location:** `scaffold/solve_chapter.py:250-269`

```python
p = data_path.parent.resolve()
while p != p.parent:
    if _CHAPTER_FOLDER_RE.match(p.name):
        return p
    p = p.parent
# Fallback: behave exactly as the old code did.
return data_path.parent
```

If `data_path` has no `ChapterN_*` ancestor (misplaced refactor folder,
symlink chain, accidental call from a test directory) the function
silently falls back to `data_path.parent` — which is the very thing
this helper exists to *avoid*. Callers can't distinguish "found the
chapter" from "fell back". Files get created in the wrong place.

**Trigger:** any misplaced data_path; defensive concern, not a known
live failure.

**Suggested fix:** raise on fallback. The whole point of the helper is
that the caller is in a context where the chapter folder must exist.

### C5. [P2] `accept_deviation` guard reads `refactor_target_deviation_ids` once at init, no reload

**Location:** state loaded at `scaffold/solve_chapter.py:3189`; checked
at `:3914`.

The deviation-target snapshot is loaded once when the row starts and
never refreshed. If the operator hand-edits `.refactor_state.json` to
add a target id mid-run (e.g., after spotting another deviation while
the orchestrator is paused on a long verifier call), the guard never
sees it. Manager can `accept_deviation` on the newly added id.

**Trigger:** operator edits state file while solve_chapter is running.

**Suggested fix:** reload the snapshot each call (cheap), or document
that the state file is locked while the orchestrator runs.

### C6. [P2] `save_data` is not atomic — crash mid-write corrupts data.json

**Location:** `scaffold/solve_chapter.py:276-282`

`save_data` writes directly via `.write_text()`. A SIGKILL, OOM, or
node failure between truncation and full flush leaves a partial JSON
file. Next orchestrator invocation fails to load. Affects both
`data.json` and `refactor_data.json`. In Apptainer / shared-cluster
context this is a realistic failure mode.

**Trigger:** orchestrator killed mid-save.

**Suggested fix:** write to `data.json.tmp` then `os.replace()`.

### C7. [P3] Bare `except Exception:` swallows git failures in remote-URL detection

**Location:** `scaffold/solve_chapter.py:1372-1373`

`_github_url_template()` swallows any exception during git probing and
silently falls back to a template that may produce broken links. The
`# noqa: BLE001` acknowledges the swallow but doesn't justify it.

**Trigger:** unusual git state at orchestrator startup.

**Suggested fix:** log the exception so it surfaces in stderr.

### C8. [P3] No id-format validation on `accept_deviation`

**Location:** parser `scaffold/solve_chapter.py:1904-1918`; handler
`:3914, 3993-4007`.

Parser accepts any non-empty `id`. A typo or case-variant
(`Foo_Bar` vs `foo_bar`) registers as a fresh entry; the refactor
guard misses it; downstream tooling that expects snake_case may skip.

**Trigger:** manager mistypes the id.

**Suggested fix:** enforce a snake_case regex at parse time and bounce
non-conforming ids back to the manager.

---

## D. Categories audited and clean

- **Category 4 (`RequestFromHumanEscalated` propagation):** clean.
  Caught at `:4352` ahead of generic `Exception`, state saved before
  raise.
- **Category 5 (counter increments):** the threshold check uses
  `.get("actions_tracking", {}).get("request_from_human", 0)`,
  defensive against missing field. Counter increments persist across
  `new_manager`.
- **Category 6 (`solved` final gate under marker convention):** the
  strict-equivalence and sorry checks operate on
  `row["main_lean_file"]` which is the same file in refactor mode but
  the gate doesn't get confused by the ORIGINAL block presence (no
  evidence of false-positive sorry detection). Worth a re-check during
  actual refactor.
- **Category 7 (`mark_solved` leaks):** clean. Mutates in-memory
  `state.row` only; original `data.json` isn't touched until phase 7d.
- **Category 13 (concurrent-run protection):** none, but branch
  isolation (`refactor_<name>` separate from
  `server_setting_up_scaffold`) makes accidental overlap unlikely.

---

## E. Open follow-ups (not yet audited)

- Worker prompts: do they receive the refactor marker convention
  briefing when the parent row is a refactor row? (Manager prompt
  does, per spot-check at lines 2846, 2870–2983.)
- `mistake` / `unmistake` interactions inside a refactor row: design
  question — what does it mean to declare an LN claim a mistake while
  refactoring it?
- `git pull` behavior in `do_refactor.py merge` when source branch has
  diverged from origin since init.

---

## F. Priority order before invoking Cluster A + Cluster B together

With the multi-root feature (§G) the next invocation drives Cluster A
(`def_3_1_no_disjoint_EL`) **and** Cluster B
(`def_3_4_collider_loose_n1`) on one branch in one go. Multi-root
amplifies blast radius — A1 in particular becomes more important
because a single 7b failure halts a larger table.

1. **C1** (P0, `reorder` wipes shared files) — must fix; data loss.
   Higher chance of firing in multi-root because more rows share
   files.
2. **C2 + C3** (P1, request-from-human path) — fix together, same
   one-line replacement at two sites.
3. **A1** (P1, cleanup phase 7b failure leaves state half-applied) —
   at minimum, run 7h even on 7b failure. More important under
   multi-root (larger table to recover).
4. **§G multi-root feature** — implement per the G.5 order.
5. **C5** (P2, accept_deviation reload) — single-line cheap fix.
6. **C6** (P2, atomic save_data) — small, high value in shared-cluster.
7. Remaining P2/P3 can defer to a cleanup pass.
8. Run Cluster A + Cluster B together as the multi-root integration
   test (G.4 step 5).

---

# G. Feature: multi-root refactors

## G.0. Motivation and shape

Today a refactor has exactly one root ref. The two open clusters in
`refactor_roadmap.md` (Cluster A `def_3_1_no_disjoint_EL` and Cluster
B `def_3_4_collider_loose_n1`) are independent but unrelated work
streams; running them sequentially means two `init` → solve → finalize
→ merge cycles, two branches, two reviews. We want to drive both
(and arbitrarily many independent root changes) in **one** refactor
table on **one** branch in **one** invocation.

**Working assumptions** (challenge any of these and the plan
shifts):

- **A1. Overlapping dependents are deduped to a single row** with
  provenance tracked (`caused_by_roots: [list]`). A row that depends
  on both root A and root B appears once.
- **A2. Ordering follows data.json natural order; no root bias.**
  Sort key is simply `(chapter, row_index)`. The LN's data.json
  ordering ensures every claim/def depends only on earlier rows, so
  roots naturally precede their dependents and biasing roots to the
  top is unnecessary — and may actively cause trouble by inserting
  a root ahead of an unrelated row that should have been solved
  first. The previous failure that motivated the May 2026
  "root-first" fix in `initialize_refactor.py:209` traces to an
  unrelated bug, not to a genuine ordering inversion, so dropping
  the bias is safe. **Action:** delete the root-first sort key,
  revert to plain `(chapter, row_index)`.
- **A3. Each root's `find_dependents` scan runs against the pristine
  source branch state** (independent baselines). Otherwise the second
  scan would see the first root's rename as already-applied and miss
  legitimate dependents.
- **A4. Multi-root refactor is all-or-nothing at finalize time.** No
  per-root partial finalize. The marker convention's global rename in
  phase 7a bundles everything; splitting it would require redesigning
  the cleanup phases.
- **A5. One code path for any n ≥ 1.** Replace the existing
  single-root logic with multi-root logic; do not keep two
  implementations. n=1 is just `roots = [single_ref]`, exercising
  the same code. Keep `--root-ref` as a deprecated CLI alias that
  internally wraps the value in a one-element list, so existing
  runbooks and the roadmap's example command still work.
- **A6. Branch and folder naming uses the user-supplied `--name`** as
  today; no auto-derivation from root list. The name should
  semantically describe the bundle (e.g., `--name
  ch3_disjoint_EL_and_collider_loose`).

## G.1. Affected components and changes

### G.1.1. `extras/do_refactor.py`

**CLI change.** Replace `--root-ref <ref>` with `--root-refs <r1,r2,…>`
(comma-separated; accept one or many). Keep `--root-ref` as a
deprecated alias that maps to a single-element list, so existing
docs/runbooks don't break.

**Loop the scan.** Inside `cmd_init`, after the branch / folder
creation, loop over roots. For each root, invoke `find_dependents.py
--ref <root>` (each producing its own `dependents_scan_<root>.json`
inside the refactor folder). After all scans, write a combined
`dependents_scan.json` containing per-root tables plus a "union"
section.

**Each scan must be baseline-pristine.** Either: (a) run all scans
sequentially with explicit `git stash`/checkout to reset state between
each scan, or (b) run all scans in parallel worktrees off the
unmodified source branch. Option (a) is simpler; option (b) is faster
but adds complexity. Recommend (a) for now.

**Hand the combined dependents JSON to `initialize_refactor.py`** with
a new `--roots <r1,r2,…>` flag and a single `--combined-dependents
<path>` argument.

**`finalize` and `merge` unchanged at the CLI level** but state file
gains a `roots: [list]` field (see G.1.4).

### G.1.2. `extras/find_dependents.py`

**No code change required if invoked once per root from the outside.**
The function already takes one `--ref`. Each invocation runs `lake
build` once, which is the slow step. For 2 roots, that's 2× the
init cost; budget accordingly.

**Optional optimization:** add a `--multi-ref <r1,r2,…>` mode that
renames all roots simultaneously and does a single combined lake
build. This is cheaper but produces a noisier "what depends on what"
output — you can't tell whether row R was broken by root A or root B.
**Defer this optimization** until we know the slowdown is painful.

### G.1.3. `extras/initialize_refactor.py`

**Accept a list of roots.** New flags: `--root-refs <list>` (replaces
`--root-ref`) and `--combined-dependents <path>` (replaces
`--dependents-json`).

**Row construction.** For each ref in the union (roots ∪ all
dependents), build at most one refactor row. When the ref is a root,
mark it as such; when it's a dependent, attach the list of roots that
introduced it via a new field on the row:

```json
{
  "ref": "claim_3_16",
  "refactor": true,
  "refactor_role": "dependent",
  "caused_by_roots": ["def_3_1", "def_3_4"],
  …
}
```

For root rows, `refactor_role: "root"`. This metadata lets the
manager prompt explain *why* a row is being touched.

**Sorting (drop the root-first bias).** Sort key becomes
`(chapter, row_index)` — data.json natural order, no role bias. Per
A2, the LN ordering already guarantees that a row's dependencies
appear earlier, so roots land before their dependents automatically.
No additional validator needed; the previous failure that motivated
the May 2026 bias traces to an unrelated bug.

**Validate every root exists in some chapter's data.json** (per-root
loop calling the same logic at `initialize_refactor.py:182-185`).
Fail fast if any root is missing.

### G.1.4. `.refactor_state.json`

Add fields, all backwards compatible (single-root case still works):

```json
{
  "source_branch":  "server_setting_up_scaffold",
  "refactor_branch":"refactor_ch3_disjoint_EL_and_collider_loose",
  "roots":          ["def_3_1", "def_3_4"],
  "root_ref":       "def_3_1",
  "name":           "ch3_disjoint_EL_and_collider_loose",
  "chapter":        3,
  "init_date":      "2026-…",
  "deviations_to_resolve": [ … union over all roots' refs … ]
}
```

`root_ref` is retained as a legacy field (= `roots[0]`) so old
tooling that reads it still functions; new code prefers `roots`.

**Deviation snapshot generalizes:** `deviations_to_resolve` =
{e.id : e in load_register(include_resolved=False), e.introduced_by_ref
in refactor_refs}, where `refactor_refs` is the full row set
(roots + dependents). Same logic as today, just over a larger set.

### G.1.5. `extras/apply_refactor_cleanup.py`

**No structural change.** All eight phases (7a–7h) operate on the
refactor table as a whole; they don't care how many roots produced
the rows. Confirm by code reading:

- 7a marker swap iterates `_collect_affected_lean_files(refactor_data)`
  → already unions across all rows.
- 7d original `data.json` sync iterates `rows` → fine.
- 7e deviation surface uses `affected_devs = [introduced_by_ref in
  refactor_refs]` → fine, just a larger set.
- 7h archive renames the single folder → fine.

**The only visible change is the printed summary** — show which roots
were resolved at finalize time. One-line cosmetic update.

### G.1.6. `scaffold/solve_chapter.py`

**Per-row briefing.** The manager prompt for a row should include its
`refactor_role` and `caused_by_roots`. Concretely: a dependent row's
briefing should say "this row needs reformalization because root(s)
X, Y changed underneath it; the changes were …" so the manager can
plan accordingly.

**No structural change needed.** All refactor-mode branches (`if
row.get("refactor")`) already operate per-row. The `accept_deviation`
guard already loads `deviations_to_resolve` as a flat set from the
state file — it doesn't care that the set was computed from multiple
roots.

**Exception:** the `refactor` action block ("no nested refactors")
should still fire for any row in a multi-root table. No code change
required — current check is `if row.get("refactor")`.

### G.1.7. `find_dependents.py` baseline interaction

The baseline-then-diff approach (the May 2026 fix) compares pre-rename
build errors to post-rename build errors. For multi-root, each
root's scan needs its **own** baseline — i.e., one baseline per scan,
not a single shared baseline. This is already the case if we just
call `find_dependents.py` separately per root. Confirm during
implementation that the per-call baseline is fresh.

## G.2. Manager-prompt updates (`scaffold/claude_prompts/manager.md`)

Add a short section explaining the multi-root case so the manager
understands the briefing fields:

- `refactor_role`: "root" or "dependent"
- `caused_by_roots`: list of refs that triggered this row's
  reformalization
- Multi-root refactors are bundled for solving-efficiency only —
  treat each row's reformalization as independent unless the briefing
  explicitly says otherwise

This is the only prompt change. Worker prompts unchanged.

## G.3. Edge cases and what they mean

| Edge case | Behavior |
|---|---|
| One root only (n=1) | Code paths must produce identical output to today's single-root flow. Test by running an existing refactor (`claim_3_2_no_finite`-style) through the new code. |
| All roots in the same chapter | Normal case; no special handling. |
| Roots span chapters (e.g., one ref in Ch.3, one in Ch.4) | `--chapter` arg becomes either a list or is replaced by per-root chapter inference. Recommend: replace `--chapter` with auto-inference from each root's actual location in `data.json`. The chapter field on the state file becomes a list. |
| Two roots' dependency trees overlap completely | The dedupe in G.1.3 produces a single row per ref. `caused_by_roots` carries both. |
| One root has zero dependents (clean change) | Table still contains the root row + any other root + their dependents. Fine. |
| Two roots are themselves in a parent-child relationship (root B is a dependent of root A) | This is a config error — collapse to single-root A and treat B as a dependent. Detect at init: if root B appears in root A's dependents scan, error with a clear message asking the operator to drop B from the roots list. |

## G.4. Test plan

1. **n=1 regression**: re-run a completed refactor (e.g., reproduce
   `claim_3_2_no_finite` end-to-end in dry mode) and confirm identical
   refactor table shape and identical cleanup output.
2. **n=2 minimal**: invent two trivial roots in a scratch chapter with
   no overlap; confirm union table.
3. **n=2 with overlap**: invent two roots whose dependency trees share
   one row; confirm dedupe + `caused_by_roots` field.
4. **n=2 with config error**: pass two roots where root B is a
   dependent of root A; confirm clear error.
5. **n=2 real**: drive the actual Cluster A + Cluster B together
   under this branch (after C1/C2/C3 from §C are fixed). The
   intersection is small (collider classification doesn't pass through
   marginalization's L-membership predicates per the roadmap §"Order
   of operations"), so this is a clean test of the multi-root code
   path against a realistic load.

## G.5. Suggested implementation order

1. **G.1.4** state-file schema additions (small, foundational).
2. **G.1.3** `initialize_refactor.py` multi-root support (replaces
   single-root path; this is where most of the logic lives).
3. **G.1.1** `do_refactor.py` CLI + scan loop.
4. **G.2** manager prompt update.
5. **G.1.6** per-row briefing in `solve_chapter.py` (cosmetic but
   visible).
6. Test plan G.4 steps 1–4.
7. Fix the bugs in §A and §C in parallel (independent work).
8. Test plan G.4 step 5 (full Cluster A + B real run).

## G.6. Out-of-scope / explicit non-goals

- **Parallel solving of independent rows** within the same table. The
  current orchestrator is strictly sequential; multi-root just unions
  rows, it doesn't introduce parallelism. (Parallelism would be a
  separate, much larger change.)
- **Per-root partial finalize.** Per A4 above, this is rejected; if
  you want to ship only Cluster A, you'd run it as a single-root
  refactor and skip Cluster B.
- **Nested multi-root** (multi-root inside multi-root). The `refactor`
  action remains blocked regardless of root count.
- **Cross-chapter dependency resolution.** If a root in Ch.3 has a
  dependent in Ch.4, the dependent is included, but no special
  cross-chapter scaffolding is added.
