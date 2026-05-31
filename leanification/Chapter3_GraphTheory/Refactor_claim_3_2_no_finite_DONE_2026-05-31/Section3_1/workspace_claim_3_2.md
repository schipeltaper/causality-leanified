# Workspace for claim_3_2 — AcyclicIffTopologicalOrder (refactor: no_finite)

## Refactor goal

Remove the `[Finite α]` instance hypothesis from
`theorem isAcyclic_iff_hasTopologicalOrder` in
`leanification/Chapter3_GraphTheory/Section3_1/AcyclicIffTopologicalOrder.lean`.

The current statement is
```
theorem isAcyclic_iff_hasTopologicalOrder
    [Finite α] (G : CDMG α) :
    G.IsAcyclic ↔ G.HasTopologicalOrder
```

The new (refactored) statement should be
```
theorem refactor_isAcyclic_iff_hasTopologicalOrder
    (G : CDMG α) :
    G.IsAcyclic ↔ G.HasTopologicalOrder
```

## Why this works without `[Finite α]`

The existing proof body **already does not use** `[Finite α]`. Both
directions are finiteness-free:

* (⇐): unchanged --- a non-trivial directed cycle would chain
  `parent_lt` + `trans` and contradict `irrefl` at the start node.
  Uses helper `topo_lt_of_directed_walk_pos` (file-local, unchanged).
* (⇒): uses Mathlib's `extend_partialOrder` (Szpilrajn's order-
  extension theorem) on the "reachable by a directed walk" preorder.
  Szpilrajn is `[IsPartialOrder α r] → ∃ s, IsLinearOrder α s ∧ r ≤ s`
  --- no finiteness needed (Zorn / choice only). Uses helper
  `directedWalk_append` (file-local, unchanged).

So the only change is dropping `[Finite α]` from the binder list.
The proof body is character-for-character identical to the existing
one. The import `Mathlib.Data.Finite.Defs` is unused after the
refactor and can be dropped (only `Mathlib.Order.Extension.Linear`
is needed by the proof).

## Cross-validation: claim_3_6 already foreshadows this

`Chapter3_GraphTheory/Section3_2/SplitTopologicalOrder.lean` lines
40--53 and 489--515 explicitly discuss that route (i) of
`isAcyclic_nodeSplittingOn` would "pull in `[Finite α]` for the `→`
half of claim_3_2" but they "kept both routes open by not adding
`[Finite α]`". Removing `[Finite α]` from claim_3_2 lets the
straightforward proof route (i) drop the finiteness baggage --- this
is exactly why the refactor table includes claim_3_6, _12, _16, _17,
_18, _19, _27, _23 as dependents to re-validate.

## Refactor mechanics

**Same-file Lean marker convention.** Wrap the existing
`theorem isAcyclic_iff_hasTopologicalOrder` (including its `-- claim_3_2`
header comments, `Verbatim from ...` block, and `## Design choice`
block --- everything from `-- claim_3_2` on line 168 down through
the `theorem ... := by ... exact hr.irrefl v hv h_rvv` ending at
line 400) with
```
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: isAcyclic_iff_hasTopologicalOrder
<existing block>
-- REFACTOR-BLOCK-ORIGINAL-END: isAcyclic_iff_hasTopologicalOrder
```
Below that, add the replacement:
```
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isAcyclic_iff_hasTopologicalOrder (was: refactor_isAcyclic_iff_hasTopologicalOrder)
-- claim_3_2 (refactored: no finiteness needed)
-- ... new comment block (see below)
theorem refactor_isAcyclic_iff_hasTopologicalOrder
    (G : CDMG α) :
    G.IsAcyclic ↔ G.HasTopologicalOrder := by
  <copy of existing proof body --- nothing structural to change,
   the proof never mentions `Finite α` anywhere>
-- REFACTOR-BLOCK-REPLACEMENT-END: isAcyclic_iff_hasTopologicalOrder
```

The helper lemmas `directedWalk_append` and
`topo_lt_of_directed_walk_pos` stay where they are (no markers
needed). They are file-private and shared by both old and new
theorem, which is fine.

The import `Mathlib.Data.Finite.Defs` stays for now (the ORIGINAL
block still references `[Finite α]`). Cleanup script removes the
ORIGINAL block at Phase 7; at that point a follow-up housekeeping
edit can drop the unused import, but that is not this row's
concern.

**TeX twin.** Write a new
`tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex`
mirroring the existing
`tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex` but with the
(⇒) direction rewritten to use Szpilrajn's order-extension theorem
(the route the Lean actually takes), and an opening sentence noting
that the lemma holds without any finiteness hypothesis on the
vertex set.

## Updated design-comment notes (for the REPLACEMENT block)

The current design block (lines 198--302 of the existing file)
spends most of its real estate justifying `[Finite α]`. The
replacement's design block should:

* **Drop** the bullets justifying `[Finite α]` (third bullet:
  "`[Finite α]` instance hypothesis", fourth bullet: "Why `[Finite α]`
  rather than `[Fintype α]`", fifth bullet: "Alternative finiteness
  phrasing"; also the second-to-last bullet's reference to
  `[Finite α]` placement).
* **Keep** the bullets on:
  - existential RHS `HasTopologicalOrder` vs relation-level
  - namespacing `Causality.CDMG.isAcyclic_iff_hasTopologicalOrder`
    with dot-projection
  - `α` implicit, `G` explicit
* **Add** a new bullet at the top: "**No `[Finite α]` hypothesis.**
  The LN states the lemma without any finiteness assumption on the
  vertex set, and the Szpilrajn route used here works for arbitrary
  `α`. The LN's *constructive* proof route (iterated parent-free-
  node extraction) does need finiteness, but our Lean proof takes a
  different path: the `reachable-by-a-directed-walk` preorder is
  partial-order under `IsAcyclic`, and `extend_partialOrder`
  produces a compatible total order without enumerating vertices.
  This makes the lemma applicable downstream to iSCMs and other
  settings where the vertex type is not assumed finite at the
  statement level." Plus a brief sentence noting which downstream
  rows (claim_3_6 part B, etc.) drop their own `[Finite α]` as a
  consequence.

## Plan of attack

1. **Dispatch a single formalize_claim worker** (refactor-aware) to:
   - Wrap the existing `theorem` block (lines 168--400) in
     `REFACTOR-BLOCK-ORIGINAL-...` markers.
   - Add a `REFACTOR-BLOCK-REPLACEMENT-...` block below with the new
     `theorem refactor_isAcyclic_iff_hasTopologicalOrder` (no
     `[Finite α]`), updated design-comment block (see above), and
     the full proof body copied verbatim from the original.
   - Run `lake build` from the repo root and confirm clean.
2. **`verify_equivalence`** on the new (no-`[Finite α]`) statement
   against the LN block.
3. **`review_design`** with full LN context to confirm the new
   shape is natural (it should be --- it is strictly more general
   than the original and removes an artificial hypothesis).
4. **`add_design_choice_comments`** as final polish (much of this
   the formalizer will have written; this pass just confirms /
   tightens).
5. **Write the tex twin** at
   `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex`
   --- Szpilrajn-based (⇒), unchanged (⇐), with opening note about
   the no-finiteness generality.
6. **`verify_tex_proof`** on the twin.
7. **`simplify_proof`** on the new Lean proof.
8. **`solved`** --- the gate should pass: equivalent statement,
   no `sorry`, strict-equivalence checker should see the new shape
   as strictly *more* faithful to the LN (which never mentioned
   finiteness either).

## Risks / things to watch

* The strict-equivalence solved-gate may flag the proof's
  divergence from the LN's iterative construction. But since the
  statement matches the LN verbatim (no `[Finite α]`), and the
  proof strategy difference is a presentation choice, this should
  be PRESENTATION-class at worst. If it flags as CONTENT, the
  formalizer's design block needs a note explaining the
  Szpilrajn-vs-iterative trade-off.
* Pre-existing comments in the file (file-level docstring lines
  98--104, and the `## References` block) talk about the LN proof
  needing finiteness. These are FILE-level (above the markers) and
  should be updated lightly to reflect the no-finiteness refactor
  --- but only the file-level docstring, not the ORIGINAL block's
  comments (those are part of the to-be-deleted block).
