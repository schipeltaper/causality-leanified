# Workspace for claim_3_7 — TwoDisjointNode (REFACTOR ROOT: eqViaNodeMap_injective)

## Refactor context

This row is the **ROOT** of refactor `eqViaNodeMap_injective` (see
`leanification/refactors/refactor_eqViaNodeMap_injective.md`).

**Why the refactor exists.** The current `eqViaNodeMap` predicate at
`TwoDisjointNode.lean:143` reads:

```lean
def eqViaNodeMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : CDMG α) (G' : CDMG β) (f : α → β) : Prop :=
  G.J.image f = G'.J
    ∧ G.V.image f = G'.V
    ∧ G.E.image (Prod.map f f) = G'.E
    ∧ G.L.image (Sym2.map f) = G'.L
```

`f : α → β` is unconstrained. `Finset.image` has set-semantics: a
many-to-one f can satisfy all four image-equality conjuncts while G
and G' are NOT isomorphic. So the predicate doesn't faithfully encode
"equal up to canonical bijection of carriers" — it relies on use-site
discipline. The plan adds a `Set.InjOn f (↑G.J ∪ ↑G.V)` first conjunct.

**Why `Set.InjOn` on `↑G.J ∪ ↑G.V`, not global `Function.Injective`.**
`flattenSplit : SplitNode (SplitNode Node) → SplitNode Node` is NOT
globally injective:
- `flattenSplit (.copy0 (.unsplit w)) = .copy0 w`
- `flattenSplit (.copy0 (.copy0 w))   = .copy0 w`   ← collide
- `flattenSplit (.copy0 (.copy1 w))   = .copy1 w`
- `flattenSplit (.copy1 (.unsplit w)) = .copy1 w`   ← collide

But it IS injective when restricted to the iterated split graph's
J ∪ V, because the colliding domain pairs never co-occur in that set
(by W₁/W₂ disjointness). So we need set-restricted injectivity, not
global.

E and L endpoints are constrained to `J ∪ V` by `def_3_1`'s subset
axioms (`hE_subset`, `hL_subset`), so InjOn on `J ∪ V` is enough.

## What needs to change in this row's files

### Lean file `TwoDisjointNode.lean`

- **`flattenSplit`** (lines 113-122) — UNCHANGED; no markers needed.
  It is the carrier-map function being passed; it stays as-is.
- **`eqViaNodeMap`** (lines 143-149) — wrap original in
  `ORIGINAL: eqViaNodeMap` markers; add a REPLACEMENT block with
  `refactor_eqViaNodeMap` that has the new InjOn conjunct as the first
  conjunct.
- **`image_unsplit_subset_nodeSplittingOn_V`** (lines 166-181) —
  UNCHANGED; no markers needed.
- **`twoDisjointNodeSplittingsCommute`** (lines 229-717) — wrap
  original in `ORIGINAL: twoDisjointNodeSplittingsCommute` markers;
  add REPLACEMENT block with `refactor_twoDisjointNodeSplittingsCommute`
  that uses `refactor_eqViaNodeMap` and discharges the new InjOn
  conjunct (twice, one for each iteration order).

- A new helper lemma showing `Set.InjOn flattenSplit ...` will likely
  be useful to factor out the shared injectivity argument; if added,
  it needs its own REPLACEMENT marker block.

### Tex twin `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex`

Copy the existing twin `tex/claim_3_7_proof_TwoDisjointNode.tex` as
the base. Insert a new paragraph (or sub-section) BEFORE the
componentwise CDMG-equality argument, justifying the carrier-map
injectivity on the iterated graph's `J ∪ V`: a case analysis on
the constructors of `SplitNode (SplitNode Node)` showing that within
`(G_{spl(W₁)})_{spl(W₂)}`'s J ∪ V, the `flattenSplit`-colliding pairs
do not co-occur (by W₁/W₂ disjointness).

## Plan / order of operations

1. **(this turn)** Dispatch `write_tex_proof` worker to create the
   tex proof twin at `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex`,
   using the existing `claim_3_7_proof_TwoDisjointNode.tex` as the
   base + adding the new InjOn paragraph(s).
2. **(next)** Dispatch `verify_tex_statement_plus_proof` (structural)
   on the twin.
3. **(next)** Dispatch `verify_tex_proof` (mathematical) on the twin.
4. **(next)** Dispatch a `spawn_agent_sub_task` to update the Lean
   file: wrap originals in ORIGINAL markers, write the
   `refactor_eqViaNodeMap` REPLACEMENT, write the
   `refactor_twoDisjointNodeSplittingsCommute` REPLACEMENT with the
   new InjOn proof body, ensure `lake build` clean.
5. **(next)** `review_design` and `verify_equivalence` on the new
   Lean shape.
6. **(next)** `verify_equivalence_strict` voluntarily, as a sanity
   check on the strengthened predicate.
7. **(next)** `add_design_choice_comments` documenting WHY the InjOn
   conjunct was added and WHY `Set.InjOn` on `J ∪ V` rather than
   global `Function.Injective`.
8. **(final)** `solved` → strict-equivalence gate → mark_solved.

## Files referenced

- Plan markdown: `leanification/refactors/refactor_eqViaNodeMap_injective.md`
- Original tex twin: `tex/claim_3_7_proof_TwoDisjointNode.tex`
- Canonical statement: `tex/claim_3_7_statement_TwoDisjointNode.tex`
- Lean file: `Section3_2/TwoDisjointNode.lean`
- Upstream defs: `Section3_1/CDMG.lean` (def_3_1),
  `Section3_2/NodeSplittingOn.lean` (def_3_11)

## Notes on the new InjOn paragraph for the tex twin

The carrier of `(G_{spl(W₁)})_{spl(W₂)}` is the disjoint union
`((V ∖ W₁) ⊔ W₁^0 ⊔ W₁^1) ∖ W₂.image .unsplit ⊔ (W₂.image .unsplit)^0 ⊔ (W₂.image .unsplit)^1`
embedded in `SplitNode (SplitNode Node)`.

The carrier-map `flattenSplit : SplitNode (SplitNode Node) → SplitNode Node`
acts by:
- `.unsplit x ↦ x` (untagged → untagged)
- `.copy0 (.unsplit w) ↦ .copy0 w` (outer .copy0 of inner unsplit)
- `.copy0 (.copy0 w)   ↦ .copy0 w` (outer .copy0 of inner .copy0)
- `.copy0 (.copy1 w)   ↦ .copy1 w`
- `.copy1 (.unsplit w) ↦ .copy1 w`
- `.copy1 (.copy0 w)   ↦ .copy0 w`
- `.copy1 (.copy1 w)   ↦ .copy1 w`

For InjOn on `J ∪ V` of the iterated graph: we need that distinct
elements x, y in `(J ∪ V)_{(G_{spl(W₁)})_{spl(W₂)}}` have distinct
`flattenSplit x`, `flattenSplit y`.

The seven possible cases (one for each cell of the disjoint union
that x can fall into) need to be considered, and disjointness
W₁ ∩ W₂ = ∅ ensures the collisions don't materialize.

The same argument applies symmetrically for the other iteration order
(W₂ first then W₁); the second InjOn obligation uses W₁/W₂ swap.

## Status

This is turn 1 of the manager for this row. No workers dispatched yet.
