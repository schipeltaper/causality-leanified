# Workspace for def_3_14 — MarginalizationAK (REFACTOR row, ROOT)

Refactor: `marginalize_loose_self_cycle` (this row is the only root).
Refactor plan: `leanification/refactors/refactor_marginalize_loose_self_cycle.md`.

## Goal (one sentence)

Drop the `(u = v → p.length ≥ 2)` conjunct from
`MarginalizationΦE` — make `def_3_14` read the LN literally so that
`G^{∖∅} = G` becomes an identity and `claim_3_17`
(`MarginalizationsCommute`) is true again.

## What changes / what doesn't

Changes (need REFACTOR-BLOCK markers; `refactor_` prefix on
replacement names):

- `MarginalizationΦE` → loose 3-conjunct form.
- `instDecidableMarginalizationΦE` (signature mentions
  `MarginalizationΦE`, so a parallel instance for the new
  predicate).
- `marginalize_hE_subset` (signature mentions
  `MarginalizationΦE` inside the `Finset.filter`).
- `marginalize` (the main def — its `E` field references
  `MarginalizationΦE` and `marginalize_hE_subset`).

Unchanged (no markers; reused by both original and
replacement `marginalize`):

- The `variable {Node : Type*} [DecidableEq Node]` block.
- `MarginalizationΦL` and `instDecidableMarginalizationΦL`.
- `marginalize_hJV_disj`.
- `marginalize_hL_subset`, `marginalize_hL_irrefl`,
  `marginalize_hL_symm`.

## addition_to_the_LN update (refactor_data.json)

The third paragraph of `addition_to_the_LN`
(beginning "Additionally, in clause (iii), a self-cycle …")
is the strict clause being dropped by this refactor. Drop the
paragraph from `refactor_data.json` so the equivalence
checkers (which read the addition) see the loose spec.
Keep paragraphs 1 and 2:

- `[bifurcation_index_boundary_excludes_natural_cases]` — independent (about Φ_L's index range).
- `[self_cycle_asymmetry_between_directed_and_bidirected]` (first paragraph only) — the `\ul{v} \neq \ol{v}` asymmetry remains real and load-bearing.

## Plan (ordered steps)

1. (manual, this turn) Edit `refactor_data.json` to drop the
   "Additionally …" paragraph from `addition_to_the_LN`.
2. `spawn_agent_sub_task` → `formalize_definition_in_tex`
   to surgically edit `tex/def_3_14_MarginalizationAK.tex`:
   drop clause (iii)(d), drop the footnote, drop the
   "Asymmetry … length $\ge 2$" caveat, keep the rest.
3. `verify_tex_statement_only` on the rewritten tex.
4. `verify_tex_statement_equivalence`.
5. `spawn_agent_sub_task` → `formalize_definition_in_lean`
   for the replacement Lean (REFACTOR-BLOCK-REPLACEMENT
   markers; `refactor_MarginalizationΦE`,
   `refactor_instDecidableMarginalizationΦE`,
   `refactor_marginalize_hE_subset`, `refactor_marginalize`).
   The original (strict) declarations get wrapped in
   REFACTOR-BLOCK-ORIGINAL markers; everything else stays
   as-is.
6. `review_design` (full LN context).
7. `verify_equivalence` (focused).
8. `verify_equivalence_strict` (recommended for this
   structural-change refactor).
9. `add_design_choice_comments` on the replacement
   declarations.  **Done** (2026-06-13): rewrote the four
   REPLACEMENT-block comment headers as forward-looking
   LN-faithful design blocks (no `pre-/post-refactor` framing,
   no ORIGINAL-block cross-references); `lake build
   Chapter3_GraphTheory` clean (only pre-existing
   `MargPreservesAncestors` linter warnings remain).
10. `solved`.

## Notes on consumers (read-only for me; their own row in the table)

- `claim_3_16` (`MargPreservesAncestors.lean`) — re-prove
  cleanly (the `by_cases hv₁_eq_m` workaround becomes dead
  code). Handled by its own refactor row.
- `claim_3_17` (`MarginalizationsCommute.lean`) — currently
  `sorry`'d at `:304`; under the loose def the LN proof goes
  through. Its own refactor row.
- `claim_3_18`, `claim_3_19` — no Lean yet; their first
  formalisation targets the loose def. Their own rows.

The chapter aggregator and `MarginalizationΦL` are not
touched.

## Marker-block layout produced by `formalize_definition_in_lean`

Actual Lean declaration name used for the main wrapped marker:
`marginalize` (verified from `noncomputable def marginalize` at
the original main-def line — confirms that the row's title
`MarginalizationAK` was indeed a starting guess; the real Lean
identifier is `marginalize`).

Four REFACTOR-BLOCK pairs added in `MarginalizationAK.lean`:

| ORIGINAL marker name           | REPLACEMENT marker name       | Replacement decl name                    | Kind                       |
|--------------------------------|-------------------------------|------------------------------------------|----------------------------|
| `MarginalizationΦE`            | `MarginalizationΦE`           | `refactor_MarginalizationΦE`             | `def` (helper, 3-dash)     |
| `instDecidableMarginalizationΦE` | `instDecidableMarginalizationΦE` | `refactor_instDecidableMarginalizationΦE` | `noncomputable instance`   |
| `marginalize_hE_subset`        | `marginalize_hE_subset`       | `refactor_marginalize_hE_subset`         | `private lemma`            |
| `marginalize`                  | `marginalize`                 | `refactor_marginalize`                   | `noncomputable def` (main, statement marker) |

- The replacement `refactor_MarginalizationΦE` drops the
  `(u = v → p.length ≥ 2)` conjunct (the strict 4th conjunct);
  the other 3 conjuncts (`Walk` witness + `IsDirectedWalk` +
  `length ≥ 1` + intermediates-in-`W`) are preserved verbatim.
- The other three replacements re-declare the strict
  versions with `refactor_MarginalizationΦE` substituted in
  for `MarginalizationΦE` in their bodies / type signatures;
  no other semantic changes.
- The `L^{∖W}` filter and all five proof-obligation lemmas
  except `marginalize_hE_subset` are untouched and reused
  verbatim by `refactor_marginalize`.

`lake build` is clean (errors-free).  One transient long-line
warning at the `instDecidableMarginalizationΦE` REPLACEMENT
marker (the marker itself is 116 chars due to the doubled-up
identifier); this will self-resolve at refactor cleanup when
the markers are removed.

Statement marker `-- def_3_14 -- start statement` /
`-- def_3_14 -- end statement` sits tight around the
`refactor_marginalize` declaration (inside the REPLACEMENT
marker block).  Helper markers `-- def_3_14 --- start helper` /
`-- def_3_14 --- end helper` sit tight around the
`refactor_MarginalizationΦE` def (inside its REPLACEMENT
marker block).  After cleanup the rename produces the
expected file shape with the loose-form `marginalize` def in
place.

**Step 1 executed (refactor_data.json + master data.json `addition_to_the_LN` strict paragraph dropped) — 2026-06-13**
- (turn N) Synced refactor_data.json def_3_14 addition_to_the_LN to master (1675→1227 chars; "Additionally" paragraph removed; verified via Python re-read).

## Manager turn — 2026-06-13 15:37 — addition_to_the_LN spec-sync (4th attempt)

Three prior worker dispatches (Turns 9, 11, 15) reported success but the edit
did not persist on `Refactor_marginalize_loose_self_cycle/refactor_data.json`.
This turn the manager ran the surgical Python edit directly:
- pre:  refactor field 1675 chars with "Additionally"; master 1227 chars loose
- post: refactor field 1227 chars without "Additionally"; ref == mas asserted
- file size 25134 -> 24675 bytes; trailing newline preserved
- Python atomic write via os.replace; mtime moved to 15:37:47

Open follow-up (verifier's lower-priority note): the master `data.json` was edited
on this refactor branch (it lost the strict paragraph already during the refactor).
The conventional Phase 7 sync direction is refactor -> master, so editing the master
pre-cleanup is unusual. Leaving as-is for now per the verifier's "fine for now"
qualifier; flag to the next manager / refactor-cleanup operator.
