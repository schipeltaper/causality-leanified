# workspace_claim_3_27.md — REFACTOR ROW

**Row**: claim_3_27 / LabelRoman / `lem:replace_walk` (section 3.3)
**Refactor**: `claim_3_2_no_finite` (root: `claim_3_2`)
**Refactor concrete API change**: `[Finite α]` removed from
`isAcyclic_iff_hasTopologicalOrder` (now `refactor_…` via cleanup).

## Current state (read-in summary)

- Pre-refactor `theorem Walk.replace_walk` was already proven on
  the server branch (commit 773178e, 449min, 16 turns) and lives at
  `Section3_3/LabelRoman.lean` lines 306–2008 (~1700-line proof body),
  with three helper files:
  - `LabelRoman.lean` (2012 lines) — main theorem
  - `LabelRomanHelpers.lean` (1654 lines) — L1–L7 helpers
  - `WalkPrefixSuffix.lean` (475 lines) — prefix/suffix infra
- Tex proof at `Section3_3/tex/claim_3_27_proof_LabelRoman.tex`
  (also pre-existing from the server branch run).
- `lake build` on the refactor branch is **clean** (verified at
  start of this run).

## Why this row is a refactor no-op (API-level)

Searched all three Lean files for the changed APIs of the
`claim_3_2_no_finite` refactor:

  - `isAcyclic_iff_hasTopologicalOrder`  → **0 matches**
  - `HasTopologicalOrder`                 → **0 matches**
  - `IsAcyclic`                            → **0 matches**
  - `[Finite α]`                           → **0 matches**

The `replace_walk` proof operates purely on walk structure
(prefix/suffix decomposition, sigma-openness, collider blocking,
Sc-membership chasing) and never cites the acyclicity↔topological-order
equivalence or any finiteness instance. The refactor is therefore a
"rides-along" inclusion via transitive structural dependency, not an
actual API change at this row.

## Strategy

Because nothing about the *statement* of `replace_walk` changes, and
the existing proof is intact + builds clean, the refactor work for
this row is the bookkeeping step required by the marker convention:

1. **Wrap the existing `theorem replace_walk` declaration** (and its
   preceding LN-reference / informal-statement / design-choice comments,
   starting at line 57 — right after the `variable` declarations) with
   `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: replace_walk` / `-- END: replace_walk`
   markers. **Do not modify any existing content.** Just add the two
   marker lines.

2. **Add a `REFACTOR-BLOCK-REPLACEMENT` block** below the original,
   containing a verbatim copy of the entire `theorem replace_walk`
   declaration renamed to `theorem refactor_replace_walk`. The
   replacement reuses the same statement and the same ~1700-line proof
   body — only the identifier `replace_walk` becomes `refactor_replace_walk`
   (in exactly two places: the theorem header, and any internal
   self-reference, if any — checked: none in the proof body).
   - Doc-comments / LN-reference / design-choice blocks **may** be
     shortened in the replacement to a brief note "identical content
     to the ORIGINAL block above; the refactor is a no-op for this
     row." This avoids duplicating ~250 lines of prose without losing
     information (the original is right above).
   - The proof body itself **must be verbatim** — at cleanup, the
     ORIGINAL block is deleted and `refactor_replace_walk` is renamed
     globally to `replace_walk`, so the surviving proof needs to be
     standalone.

3. **Create the tex twin** `tex/refactor_claim_3_27_proof_LabelRoman.tex`
   as a **verbatim copy** of `tex/claim_3_27_proof_LabelRoman.tex`. The
   LN proof of `lem:replace_walk` does not change.

4. **`lake build`** must remain clean after the edits.

## Action sequence (planned)

- Turn 1 (this turn): `spawn_agent_sub_task` → a focused worker to do
  the mechanical wrap + duplicate edit in step 1–3 above. Build clean.
- Turn 2: `review_design` (the design is unchanged from the proven
  server-branch row, so should PASS quickly).
- Turn 3: `verify_equivalence` (statement vs LN tex_block — unchanged).
- Turn 4: `verify_equivalence_strict` (voluntary preflight before
  `solved`, since the solved-gate auto-runs it; catches deviations
  early).
- Turn 5: `solved` → orchestrator runs verify_row_solved + hard-sorry
  scan + strict-equivalence gate. All should PASS.

## Notes / surprises

- The `replace_walk` proof internally branches on whether the right
  edge at position `j` of the walk has an arrowhead at its source
  (`HasArrowheadAtSource`), packing LN cases (i) and (ii) into a single
  existential via `σ.IsDirected ∨ σ.reverse.IsDirected`. The
  "shortest" qualifier is unbundled into `IsPath` + all-nodes-in-Sc
  (the quantitative length-minimisation is dropped because the only
  live consumer — claim_3_23's 2 ⇒ 1 — needs the *qualitative*
  properties, not the minimum length). See lines 100–292 of
  `LabelRoman.lean` for the full design-choice block.
- `replace_walk` is the only top-level theorem in `LabelRoman.lean`
  (grep at line 306). All helpers live in `LabelRomanHelpers.lean`
  and `WalkPrefixSuffix.lean`. Marker wrapping is therefore local
  to this one theorem.
