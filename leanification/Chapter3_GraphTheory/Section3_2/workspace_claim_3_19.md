# Workspace for claim_3_19 — MarginalizingOutThe

## Plan (refactor `eqViaNodeMap_injective`, DEPENDENT row)

The existing `marginalize_swig_eq_doit` (in `MarginalizingOutThe.lean`)
uses the 4-conjunct `eqViaNodeMap` predicate with carrier map
`toCopy1 W : Node → SplitNode Node`.  The refactor strengthens
`eqViaNodeMap` to `refactor_eqViaNodeMap`, adding a 5th `Set.InjOn`
conjunct on `↑G.J ∪ ↑G.V` of the source graph.

### Step 1 — TeX twin
Write `tex/refactor_claim_3_19_proof_MarginalizingOutThe.tex` as the
twin of the existing `tex/claim_3_19_proof_MarginalizingOutThe.tex`,
adding ONE extra paragraph ("Injectivity of the carrier bijection on
the source CDMG's node set") that proves the canonical bijection
`phi : J_{do(W)} ∪ V_{do(W)} = J ∪ V → J ∪ W^i ∪ (V ∖ W)` defined by
the case-split `v ↦ v` on `J ∪ (V∖W)` and `w ↦ w^i` on `W` is
injective.  Three-cell partition `{J, V∖W, W}` of the source:
- Within-cell: identity on `J` and `V∖W`; `w ↦ w^i` injection on `W`
  by def_3_11's tagged-copy construction.
- Across-cell: cells `J` and `V∖W` both image-identity into the
  untagged piece `J ∪ (V∖W)` of the codomain — these two are
  disjoint by `J ∩ V = ∅` (def_3_1).  Cell `W` maps into `W^i`
  (the tagged input-copy piece), type-disjoint from the untagged
  piece by def_3_11/def_3_12.

Follow the pattern in `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex`:
the existing statement-restatement block + 4-clause proof body is
copied verbatim from the verified `claim_3_19_proof_*.tex`; the new
InjOn paragraph slots in just before the closing "Combining clauses
(a)–(d)..." sentence.

### Step 2 — Lean refactor port
Add to `MarginalizingOutThe.lean` (alongside the existing
`marginalize_swig_eq_doit`, wrapped in REFACTOR-BLOCK markers):

1. `REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_swig_eq_doit` … `END` —
   wraps the existing theorem (and its design-choice docstring) so
   the cleanup script can delete it at Phase 7.
2. `REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_swig_eq_doit (was: refactor_marginalize_swig_eq_doit)` …
   `END` — wraps the new `refactor_marginalize_swig_eq_doit` theorem
   using `refactor_eqViaNodeMap`.  Body strategy:
   ```
   obtain ⟨hJ, hV, hE, hL⟩ := marginalize_swig_eq_doit G hG W hW
   refine ⟨?_, hJ, hV, hE, hL⟩
   -- prove Set.InjOn (toCopy1 W) (↑(hardInterventionOn).J ∪ ↑(hardInterventionOn).V)
   ```
   The InjOn obligation: intro `x ∈ S, y ∈ S, h : toCopy1 W x = toCopy1 W y`;
   case-split on `x ∈ W` and `y ∈ W`; constructor cases close by
   injection or no-confusion.

No new top-level helper needed (the InjOn proof is short enough to
inline; if it grows, hoist out as a `private lemma` with
REFACTOR-BLOCK-REPLACEMENT markers — see `flattenSplit_injOn_of_disjoint`
in `TwoDisjointNode.lean` and `flattenIntExt_injOn_of_disjoint` in
`AddingInterventionNodes.lean` for the established pattern).

### Step 3 — Verifier chain
`verify_tex_statement_plus_proof`, `verify_tex_proof`,
`review_design`, `verify_equivalence`, `add_design_choice_comments`,
`solved` (which auto-runs strict-equivalence gate).
