# Workspace for def_3_4 — Walks (refactor ROOT in `cdmg_typed_edges`)

## Refactor plan (made 2026-06-17)

### Summary

`def_3_4` is the second root of `cdmg_typed_edges`. The original `Walks.lean`
is 1138 lines containing 18 declarations (helpers + statements). The refactor
turns `WalkStep` into a typed inductive (`.forwardE` / `.backwardE` / `.bidir`),
which moves the per-step channel from the body of an or-disjunction into a
constructor tag. The downstream cascade then re-expresses every walk predicate
as a pattern-match on the typed `WalkStep` instead of a destructure of a stored
`(a : Node × Node)`.

The math (LN + addition_to_the_LN) is unchanged. The tex
(`tex/def_3_4_Walks.tex`) is NOT modified.

The CDMG (`def_3_1`), CDMGNotation (`def_3_2`), and EdgeRelations (`def_3_3`)
refactors are all in place under `namespace refactor_CDMG` — see
`CDMG.lean:189`, `CDMGNotation.lean:500`, `EdgeRelations.lean:354`. So the
`refactor_CDMG`, `refactor_sus`, `refactor_intoE`, `refactor_intoL`,
`refactor_outOf` declarations this row will reference are all available.

### Recommendations on the 7 design decisions

1. **`Walk.edges` — DROP entirely.** Under typed `WalkStep`, there is no
   stored ordered pair to project. Option (b) "synthesise a canonical
   `(u, v)` per constructor" fails for `.bidir` because `s(u, v) = s(v, u)`
   in `Sym2` has no canonical representative. Option (c) sigma-typed
   `Walk.steps : List (Σ u v, WalkStep G u v)` is heavyweight and forces
   downstream consumers through `Sigma.fst`/`.snd` plumbing. Option (a) —
   drop — is cleanest: every existing `p.edges.getLast?` use site
   (`intoEnd`, `outOfEnd`) is rewritten to recurse on `Walk` structure
   directly. Channel + pair both come from the WalkStep constructor at the
   point of use; no intermediate `List` carrier is needed.

2. **End-node classifiers — STAY UNIFIED (one Prop each).** Keep
   `refactor_intoStart`, `refactor_outOfStart`, `refactor_intoEnd`,
   `refactor_outOfEnd` as four single Props pattern-matching on the
   `refactor_WalkStep` constructor. The contrast with `EdgeRelations.lean`'s
   `intoE` / `intoL` split (which was forced because L's *carrier type*
   changed from `Node × Node` to `Sym2 Node`, so a single `e : Node × Node`
   argument could no longer typecheck for both channels) does not apply at
   walk-step level: the typed `WalkStep` already absorbs all three channel
   cases into a unified inductive, so a single Prop on `Walk` consumes a
   single WalkStep argument through a uniform case-analysis. A channel-split
   here would double the predicate count without adding semantic content;
   the LN's "into / out of" language is channel-neutral.

3. **`intoEnd` / `outOfEnd` access path — direct `Walk` recursion.** Peel
   cons cells until the tail is `nil`, then read the WalkStep on the last
   `cons`. Mirrors `IsColliderRest`'s "match on the next cons" idiom that
   the original file already uses. A separate `refactor_lastStep` helper
   was considered (sigma-typed `Σ u', WalkStep G u' v`) but would force a
   wrapping/unwrapping pass and adds a net-new declaration with no
   downstream re-use; inline recursion is simpler and keeps the predicate
   self-contained.

4. **Bifurcation hinge — `.backwardE` for the directed hinge,
   `.bidir` for the bidirected hinge — CONFIRMED.** Original:
   `(a = (v, u) ∈ E) ∨ (a = (u, v) ∈ L)`. Mapping:
   - "directed hinge `(v, u) ∈ G.E`" → `.backwardE h` with
     `h : (v, u) ∈ G.E` (the WalkStep from `u` to `v` whose underlying
     edge points `v → u`).
   - "bidirected hinge `(u, v) ∈ G.L`" → `.bidir h` with
     `h : s(u, v) ∈ G.L`.
   The left-arm constraint "each edge `(v, u) ∈ E`" (LN clause (b)) maps
   to `.backwardE` at every step. The right-arm `p.IsDirectedWalk`
   constraint (LN clause (c)) maps to `.forwardE` at every step in the
   refactored `refactor_IsDirectedWalk`.

5. **`length` marker — keep `-- def_3_6 --- start helper` as-is in the
   refactor block.** `length` is conceptually a helper for `def_3_6`
   acyclicity (which counts non-trivial directed walks) but lives in
   `Walks.lean` because `Walk` must exist for `length` to typecheck.
   Since `Walk` changes shape, `length` MUST be refactored as part of the
   `def_3_4` root. But the LN-reference marker (the "this helper supports
   `def_3_6`" annotation) describes *concept ownership*, not refactor
   scope; we keep it. The REFACTOR-BLOCK-ORIGINAL / REPLACEMENT markers
   wrap *around* the inner `def_3_6 --- start/end helper` markers in both
   blocks.

6. **Decl naming — `refactor_<OriginalName>` for every replacement.**
   Replacement names: `refactor_WalkStep`, `refactor_Walk`,
   `refactor_length`, `refactor_vertices`, `refactor_intoStart`,
   `refactor_outOfStart`, `refactor_intoEnd`, `refactor_outOfEnd`,
   `refactor_IsDirectedWalk`, `refactor_IsBidirectedWalk`,
   `refactor_IsColliderRest`, `refactor_IsColliderWalk`,
   `refactor_IsPath`, `refactor_IsBifurcationWithSplit`,
   `refactor_IsBifurcation`, `refactor_IsBifurcationDirectedHingeWithSplit`,
   `refactor_IsBifurcationSource`. **Original `edges` has no replacement
   counterpart** (decision 1 — drop) — its ORIGINAL block stays wrapped so
   cleanup deletes it cleanly, but no `refactor_edges` exists. Phase 7
   cleanup will whole-word rename `refactor_<Name>` → `<Name>` globally.

7. **Namespace structure — `Causality > refactor_CDMG > refactor_Walk`.**
   The original lives under `namespace Causality > namespace CDMG >
   namespace Walk` (file `Walks.lean:5`, `:86`, `:253`). The refactor
   versions live under `namespace Causality > namespace refactor_CDMG >
   namespace refactor_Walk`, mirroring the precedent that
   `EdgeRelations.lean:354` sets for `namespace refactor_CDMG` (housing
   `refactor_adjacent`, `refactor_intoE`, etc.). Lean 4 accepts having
   `inductive refactor_Walk` AND `namespace refactor_Walk` (same name)
   in the same file — the original file already does this for `Walk`
   (`Walks.lean:247` then `:253`). The inductive lives directly under
   `refactor_CDMG`; the `Walk`-namespace declarations (length, vertices,
   etc.) live under the nested `refactor_Walk` namespace. Open the
   refactor block with `namespace refactor_CDMG`, then `namespace
   refactor_Walk` for everything past the inductive, and close both at
   the end of the file's refactor section.

### Same-file structural shape (cleanup-script-friendly)

```lean
import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations

namespace Causality

/-! [existing file docstring stays — describes the original design] -/

namespace CDMG
  variable {Node ...}
  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: WalkStep
  def WalkStep ...
  -- REFACTOR-BLOCK-ORIGINAL-END: WalkStep
  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk
  inductive Walk ...
  -- REFACTOR-BLOCK-ORIGINAL-END: Walk
  namespace Walk
    variable {G : CDMG Node}
    -- (all ORIGINAL helpers/predicates wrapped in REFACTOR-BLOCK-ORIGINAL markers)
    -- length, vertices, edges, intoStart, ..., IsBifurcationSource
  end Walk
end CDMG

namespace refactor_CDMG
  variable {Node ...}
  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: WalkStep (was: refactor_WalkStep)
  inductive refactor_WalkStep ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: WalkStep
  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk (was: refactor_Walk)
  inductive refactor_Walk ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: Walk
  namespace refactor_Walk
    variable {G : refactor_CDMG Node}
    -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: length (was: refactor_length)
    def refactor_length ...
    -- REFACTOR-BLOCK-REPLACEMENT-END: length
    -- (and so on — vertices, intoStart, ..., IsBifurcationSource)
    -- NOTE: no refactor_edges (decision 1)
  end refactor_Walk
end refactor_CDMG

end Causality
```

Cross-references:
- Marker shape + comprehensive design-comment blocks above replacements:
  `CDMG.lean:174-393` (root precedent).
- `namespace refactor_CDMG` + referencing `refactor_*` upstream from a
  downstream-of-root row: `EdgeRelations.lean:354-830`.
- `inductive` then same-named `namespace` co-existing: original
  `Walks.lean:247` then `:253`.
- Force-split because L's carrier type changed (precedent for keeping
  end-node classifiers UNIFIED in our case despite a different pressure
  here): `EdgeRelations.lean`'s `intoE` / `intoL` split (lines 447–703).

### 5-phase breakdown

Each phase is one focused worker dispatch via `refactor_lean_code`. After
each phase: `lake build` from `/home/11716061/repo_scaffold2/` must remain
green (the originals still compile because they're untouched; the new
`refactor_*` decls must typecheck on their own).

#### Phase A — Foundations: `WalkStep`, `Walk` (typed inductives)

ORIGINAL declarations to wrap (verify line numbers at dispatch time):
- `Walks.lean:166-168` — `def WalkStep` (currently in `-- def_3_4 --- start
  helper` markers).
- `Walks.lean:247-251` — `inductive Walk`.

New `refactor_*` declarations to add under `namespace refactor_CDMG` (NOT
yet under `refactor_Walk`):
- `refactor_WalkStep : refactor_CDMG Node → Node → Node → Type` — three
  constructors `.forwardE`, `.backwardE`, `.bidir` per the refactor plan.
  `.forwardE` and `.backwardE` carry `Node × Node`-membership in `G.E`;
  `.bidir` carries `Sym2 Node`-membership in `G.L` via `s(u, v) ∈ G.L`.
- `refactor_Walk : refactor_CDMG Node → Node → Node → Type` — `nil` and
  `cons`. `cons` no longer stores `a : Node × Node`; the WalkStep moves
  into the constructor data.

Design-decision touchpoints: (6) decl naming, (7) namespace structure.
The bulk of design-comment-block prose at each REPLACEMENT focuses on:
- Why a `Type`-level inductive WalkStep with three constructors (not the
  original `Prop`-level disjunction).
- Why drop `a : Node × Node` from `cons` — the endpoints come from the
  WalkStep's type indices and the channel comes from the constructor.
- Cross-reference to the driving rationale at
  `leanification/refactors/refactor_cdmg_typed_edges.md`.

Verification: `lake build`.

Risk: medium (foundational; if the inductive shape is wrong, all later
phases cascade).

#### Phase B — Structural helpers: `length`, `vertices`; DROP `edges`

ORIGINAL declarations to wrap:
- `Walks.lean:283-287` — `def length` (inside `def_3_6 --- start/end
  helper` markers — keep those markers verbatim).
- `Walks.lean:330-333` — `def vertices` (inside `def_3_4 --- start/end
  helper` markers).
- `Walks.lean:373-376` — `def edges` (inside `def_3_4 --- start/end
  helper` markers). **The ORIGINAL block is wrapped so cleanup deletes it,
  but no `refactor_edges` REPLACEMENT counterpart is created.**

New `refactor_*` declarations to add under `namespace refactor_CDMG >
namespace refactor_Walk` (open the inner namespace at the start of this
block):
- `refactor_length : refactor_Walk G u v → ℕ` (keep the `def_3_6 ---
  start/end helper` markers inside the REPLACEMENT block).
- `refactor_vertices : refactor_Walk G u v → List Node`.

Design-decision touchpoints: (1) drop-`edges` rationale (load-bearing —
the design-comment block above `refactor_vertices` should record WHY no
replacement for `edges` exists, so a future reader who greps for "where
did `edges` go" finds the answer); (5) `length` marker preservation.

Verification: `lake build`.

Risk: low (`length` and `vertices` are simple structural recursions;
their refactored forms are one-line ports modulo the cons-arg shape
change).

#### Phase C — End-node classifiers: `intoStart`, `outOfStart`,
                                       `intoEnd`, `outOfEnd`

ORIGINAL declarations to wrap:
- `Walks.lean:452-455` — `def intoStart`.
- `Walks.lean:478-481` — `def outOfStart`.
- `Walks.lean:517-521` — `def intoEnd`.
- `Walks.lean:539-543` — `def outOfEnd`.

New `refactor_*` declarations to add under the `refactor_Walk` namespace:
- `refactor_intoStart` — pattern-match on the `cons`-cell's WalkStep:
  `.forwardE _ => False` (the LN's "$a_0 = (v_0, v_1) \in E$" with arrow
  out of `v_0`, not into), `.backwardE _ => True` ($a_0 = (v_1, v_0) \in
  E$, arrow into `v_0`), `.bidir _ => True` ($a_0 = (v_0, v_1) \in L$,
  bidirected — into `v_0`). Pin against `refactor_intoE` / `refactor_intoL`
  semantics from `EdgeRelations.lean`.
- `refactor_outOfStart` — `.forwardE _ => True`, `.backwardE _ => False`,
  `.bidir _ => False`. Matches `refactor_outOf`'s E-only definition.
- `refactor_intoEnd` — direct recursion on `Walk`: peel cons cells until
  the tail is `nil`, then read the last WalkStep. Per decision (3).
- `refactor_outOfEnd` — same access pattern as `refactor_intoEnd`, with
  the dual constructor pattern.

Design-decision touchpoints: (2) stay-unified (load-bearing — design
comment must spell out why we don't split per-channel here despite the
`intoE` / `intoL` precedent next door); (3) direct-recursion access path
(replaces `getLast?`).

Verification: `lake build`.

Risk: medium (the recursion shape for `intoEnd` / `outOfEnd` is new
relative to the original `getLast?`-driven form; needs careful
pattern-matching on `cons _ (nil _)` vs `cons _ (cons …)` to bottom out
on the last edge).

#### Phase D — Walk-class predicates: `IsDirectedWalk`,
                                      `IsBidirectedWalk`,
                                      `IsColliderRest`,
                                      `IsColliderWalk`, `IsPath`

ORIGINAL declarations to wrap:
- `Walks.lean:601-604` — `def IsDirectedWalk`.
- `Walks.lean:634-637` — `def IsBidirectedWalk`.
- `Walks.lean:710-716` — `def IsColliderRest`.
- `Walks.lean:779-784` — `def IsColliderWalk`.
- `Walks.lean:829` — `def IsPath`.

New `refactor_*` declarations to add under `refactor_Walk`:
- `refactor_IsDirectedWalk` — pattern-match on the WalkStep constructor:
  every step must be `.forwardE _`. (Previously: stored-pair check
  `a = (u, v) ∧ a ∈ G.E`; now: structural.)
- `refactor_IsBidirectedWalk` — every step is `.bidir _`. (Previously:
  `a = (u, v) ∧ a ∈ G.L`.)
- `refactor_IsColliderRest` — same three-branch structure as the
  original (`nil`, `cons _ (nil _)`, `cons _ (cons …)`); the last-edge
  branch's disjunction `(a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)`
  becomes a constructor-level `WalkStep` case-split (`.backwardE _ \/
  .bidir _`, with `.forwardE` rejected).
- `refactor_IsColliderWalk` — same three-case `n = 0` / `n = 1` / `n ≥ 2`
  structure; `n = 1` branch becomes "the lone WalkStep is `.bidir _`";
  `n ≥ 2` branch becomes "first step is `.forwardE _ \/ .bidir _`" (the
  `\suh` "arrowhead at $v_1$" admits both forward-E and bidir but rejects
  backward-E), and the rest hands off to `refactor_IsColliderRest`.
- `refactor_IsPath` — one-liner over `refactor_vertices`, identical shape
  to the original (`p.vertices.Nodup`); no WalkStep change touches this.

Design-decision touchpoints: bifurcation hinge mapping (4) doesn't apply
yet — that's Phase E. The collider-walk constructor case-splits are the
analogue here. Add a design-comment cross-reference explaining how the
LN's stored-pair disjunctions map to constructor patterns.

Verification: `lake build`.

Risk: medium (the collider-walk encoding is the most intricate of the
walk-class predicates; the cases-on-`n` structure interacts with the
WalkStep constructor matching).

#### Phase E — Bifurcation predicates: `IsBifurcationWithSplit`,
                                       `IsBifurcation`,
                                       `IsBifurcationDirectedHingeWithSplit`,
                                       `IsBifurcationSource`

ORIGINAL declarations to wrap:
- `Walks.lean:924-931` — `def IsBifurcationWithSplit`.
- `Walks.lean:995-1000` — `def IsBifurcation`.
- `Walks.lean:1044-1051` — `def IsBifurcationDirectedHingeWithSplit`.
- `Walks.lean:1126-1131` — `def IsBifurcationSource`.

New `refactor_*` declarations to add under `refactor_Walk`:
- `refactor_IsBifurcationWithSplit` — four-branch recursion mirroring the
  original. Hinge mapping per decision (4):
  - `n = 1, k = 1` (`cons _ _ (.nil _ _), 0`): only `.bidir _` (the
    bidirected hinge survives the `[bifurcation_right_chain_trivial_is_
    just_directed_walk]` constraint).
  - `n ≥ 2, k = 1` (`cons _ _ (p@(.cons …)), 0`): `.backwardE _ \/
    .bidir _` (both directed-backward and bidirected hinges admissible)
    AND `p.refactor_IsDirectedWalk`.
  - left-arm step (`cons _ _ p, k + 1`): step is `.backwardE _` (LN's
    "$a_j = (v_{j+1}, v_j) \in E$" = backward-E in the cons direction).
- `refactor_IsBifurcation` — same four-conjunct shape (`u ≠ v`,
  vertex-uniqueness via `refactor_vertices.tail` / `.dropLast`,
  existential split index). No WalkStep change touches this directly —
  the constructor-level encoding is inherited through
  `refactor_IsBifurcationWithSplit`.
- `refactor_IsBifurcationDirectedHingeWithSplit` — same four-branch
  recursion with the hinge pinned to `.backwardE _` (excluding `.bidir`);
  the `n = 1` directed-hinge case stays `False` per the addition.
- `refactor_IsBifurcationSource` — same four-conjunct shape with the
  existential over `refactor_IsBifurcationDirectedHingeWithSplit` and
  the `refactor_vertices[i + 1]?` lookup.

Design-decision touchpoints: (4) hinge mapping — the design-comment
block above `refactor_IsBifurcationWithSplit` should walk through the
constructor-by-constructor correspondence with the LN clauses, so that
a downstream reader doesn't have to rebuild the mapping from scratch.

Verification: `lake build`.

Risk: medium-high (the most complex predicates in the file; many
branches; the `cons _ _ (p@(.cons …)), 0` middle-branch pattern under
the new WalkStep shape needs care to keep the case-coverage exhaustive).

### After all five phases — verification gates

1. `verify_equivalence` against the LN block + addition_to_the_LN
   (`tex/def_3_4_Walks.tex`).
2. `verify_equivalence_strict` (recommended — encoding changes
   substantively). Auto-chains to `verify_with_examples` if it returns
   EXAMPLE_GENERATION.
3. `add_design_choice_comments` polish pass — comprehensive per-decl
   design-comment blocks are required by the manager. The phase-by-phase
   workers each write a first-cut block; this pass harmonises them.
4. `solved` → strict-equivalence solved-gate (re-runs step 2) → mark
   solved.

### Blockers / open questions

- **Upstream refactors are in place.** `refactor_CDMG` (`CDMG.lean:383`),
  `refactor_sus` and friends (`CDMGNotation.lean:500+`), `refactor_intoE`,
  `refactor_intoL`, `refactor_outOf` (`EdgeRelations.lean:447, 580, 705`)
  are all defined. No upstream blockers.
- **`Walk.length`'s `def_3_6` marker is benign for the cleanup script.**
  Cleanup script's rename is whole-word on `refactor_<name>` →
  `<name>`. The `-- def_3_6 --- start helper` line is a documentation
  comment, not a declaration name; it survives the rename unmodified
  inside both the ORIGINAL (deleted) and REPLACEMENT (renamed) blocks.
- **`Walk.edges` is dropped — no consumer cross-references in Walks.lean
  itself remain to update.** The dropped accessors are
  `p.edges.getLast?` (used by `intoEnd` / `outOfEnd` originals, replaced
  in Phase C with direct `Walk` recursion). No other in-file consumer
  references `Walk.edges` after the refactor. *External* consumers
  (other §3.1, §3.2, §3.3 files) will be addressed by their own
  refactor rows — that's outside this row's scope.
- **No net-new helper declarations forecast.** Direct-recursion in
  Phase C avoids a `refactor_lastStep` helper. If during Phase C the
  recursion turns out to need extraction (e.g. Lean's structural-
  recursion checker complains), add a `refactor_lastStep` net-new
  declaration in a REFACTOR-BLOCK-REPLACEMENT block with no ORIGINAL
  counterpart (the briefing's net-new convention applies).
- **The file-top `/-! ... -/` docstring and pre-existing design-comment
  blocks above each ORIGINAL declaration stay put.** They describe the
  original design and will be processed by `polish_refactor_comments`
  at Phase 7 cleanup. Don't rewrite them during the per-phase worker
  dispatches.
- **Closing namespaces at file end:** the file currently ends with
  `end Walk`, `end CDMG`, `end Causality` (`Walks.lean:1133-1137`).
  After the refactor, the file must end with (a) the original closures
  in their existing positions, immediately followed by (b)
  `namespace refactor_CDMG` ... `namespace refactor_Walk` ... contents
  ... `end refactor_Walk`, `end refactor_CDMG`, then a single final
  `end Causality`. Easiest: move the existing `end Causality` to after
  the refactor namespace closures; everything else stays in place.

### Notes / history

_(plan first written 2026-06-17 by `plan_subtasks` worker)_
