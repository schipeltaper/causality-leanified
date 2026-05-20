# Workspace for claim_3_10 — TwoDisjointNode (SWIG version)

## Row context

- **ref:** `claim_3_10`
- **title:** `TwoDisjointNode`
- **LN source:** `lecture-notes/lecture_notes/graphs.tex` lines 627 -- 632 (statement)
  and lines 635 -- 660 (proof)
- **LN statement:**
  > Let $G=(J,V,E,L)$ be a CADMG and $W_1, W_2 \subseteq V$ two disjoint subsets
  > of the output nodes of $G$. Then
  > $\bigl(G_{\swig(W_1)}\bigr)_{\swig(W_2)} = \bigl(G_{\swig(W_2)}\bigr)_{\swig(W_1)}
  > = G_{\swig(W_1 \,\dot\cup\, W_2)}$.

This is the **SWIG mirror** of `claim_3_7` (which used `\spl`). The `\swig`
operator is `def_3_12 NodeSplittingHard`: it is `nodeSplittingOn` followed by
hard intervention on the freshly produced `W^i = range Sum.inr` copies.

## Existing infrastructure (no new design from scratch needed)

`TwoDisjointNodeSplittingsCommute.lean` (claim_3_7) already provides:

- **`CDMGEquiv G H`** -- 4-data-field equivalence between CDMGs over potentially
  different carriers. With groupoid laws `refl`, `symm`, `trans`.
- **`subset_nodeSplittingOn_V_of_subset_V`** -- bridging helper for the `\spl`
  inner precondition.
- **`fusionEquiv W₁ W₂ hdisj : α ⊕ ↑(W₁ ∪ W₂) ≃ (α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)`** --
  the canonical re-labeling bijection. The **same** bijection works for the SWIG
  case (the carrier shape is identical -- `swig W₁` produces `α ⊕ ↑W₁` just like
  `spl W₁` does).
- **`nodeSplittingOn_nodeSplittingOn_equiv`** -- the `\spl` fusion lemma.
- **`nodeSplittingOn_comm_equiv`** -- the `\spl` commute corollary.

`NodeSplittingHard.lean` (def_3_12) provides:

- **`nodeSplittingHardInterventionOn` / `swig`** -- defined as
  `(G.nodeSplittingOn W hW).hardInterventionOn (Set.range Sum.inr)`.
- Four `@[simp]` lemmas: `nodeSplittingHardInterventionOn_J/V`,
  `mem_nodeSplittingHardInterventionOn_E/L`.

## Plan

### Manager A (me, this manager) -- statement phase

1. **Formalize the statement.** New file:
   `leanification/Chapter3_GraphTheory/Section3_2/TwoDisjointSwigsCommute.lean`.

   Two `noncomputable def` declarations, body = `sorry`:

   - **Fusion lemma** `swig_swig_equiv`:
     ```
     CDMGEquiv
       ((G.swig W₁ hW₁).swig (Sum.inl '' W₂) (subset_swig_V_of_subset_V hW₂ hW₁))
       (G.swig (W₁ ∪ W₂) (Set.union_subset hW₁ hW₂))
     ```

   - **Commute corollary** `swig_comm_equiv`:
     ```
     CDMGEquiv
       ((G.swig W₁ hW₁).swig (Sum.inl '' W₂) ...)
       ((G.swig W₂ hW₂).swig (Sum.inl '' W₁) ...)
     ```

   - Also a bridging helper `subset_swig_V_of_subset_V`:
     `Sum.inl '' W₂ ⊆ (G.swig W₁ hW₁).V` (follows from
     `nodeSplittingHardInterventionOn_V` which gives `Sum.inl '' G.V` and from
     `hW₂ : W₂ ⊆ G.V`). Note: simpler than the `\spl` analogue because the
     SWIG output set is just `Sum.inl '' G.V` (the `range Sum.inr` piece is
     gone after HI).

   Imports: `Chapter3_GraphTheory.Section3_2.NodeSplittingHard` (for `.swig` and
   its simp lemmas) and
   `Chapter3_GraphTheory.Section3_2.TwoDisjointNodeSplittingsCommute` (for
   `CDMGEquiv`, `fusionEquiv`).

2. `review_design` (full-LN-context).
3. `verify_equivalence`.
4. `add_design_choice_comments`.
5. `new_manager` -- hand off to Manager B.

### Manager B -- proof phase

6. `write_tex_proof.md` -- fill
   `tex/claim_3_10_proof_TwoDisjointNode.tex`. LN proof at lines 635 -- 660
   is the structural mirror of claim_3_7's LN proof (lines 466 -- 493).
   Copy the LN proof, edit `\spl` → `\swig` and `^0/^1` → `^o/^i`.
7. `verify_tex_proof`.
8. `prove_claim_in_lean.md` -- translate. Likely structure: mirror
   `nodeSplittingOn_nodeSplittingOn_equiv`'s proof using SWIG simp lemmas in
   place of NS simp lemmas. The SWIG case should be **simpler** than the `\spl`
   case for V (just `Sum.inl '' G.V`, no `range Sum.inr`) and E (just one piece,
   the LN's `v_1^i → v_2^o` -- the split edges of the `\spl` case are killed by
   HI). The J case has the `range Sum.inr` piece.

   **Alternative strategy to consider** (if direct is too long): use
   `hardInterventionOn_nodeSplittingOn_comm` (claim_3_8) and
   `hardInterventionOn_comm` (claim_3_4) to reduce the SWIG fusion to the
   `\spl` fusion (`nodeSplittingOn_nodeSplittingOn_equiv`) + HI. Decide at the
   `write_tex_proof` step.
9. `simplify_proof`.
10. `solved` → `verify_row_solved`.

## Notes / pitfalls

- The existing claim_3_7 file (`TwoDisjointNodeSplittingsCommute.lean`)
  *anticipates* this row in its docstring (lines 60 -- 65) -- it explicitly
  flags `claim_3_10` as the second consumer that may need
  `CDMGEquiv`. The decision to keep `CDMGEquiv` local rather than promote to
  Section 3.1 still holds: per claim_3_7's design notes, **only a third
  consumer** should trigger `reorder` to promote to `Section3_1/`. Two
  consumers (claim_3_7 + claim_3_10) is not enough.
- Carrier alignment: `swig W₁` carrier = `α ⊕ ↑W₁` (same shape as `spl W₁`).
  So `fusionEquiv` reuses verbatim.
- `Disjoint W₁ W₂` is load-bearing in the same place as for `\spl`:
  consumed by `fusionEquiv`'s underlying `Equiv.Set.union`.
- The tex proof file `claim_3_7_proof_TwoDisjointNode.tex` currently has only a
  TODO stub even though claim_3_7 is marked solved -- not my problem to fix.

## Running log

### Manager A -- statement phase (complete)

- **T1 `spawn_agent_sub_task` → `formalize_claim_in_lean.md`:** created
  `TwoDisjointSwigsCommute.lean` with 3 declarations in namespace
  `Causality.CDMG`:
  - `subset_swig_V_of_subset_V` (bridging helper, proof = 2 lines, no `sorry`),
  - `swig_swig_equiv` (fusion lemma, body = `sorry`),
  - `swig_comm_equiv` (commute corollary, body = `sorry`).
  Added the new file to the aggregator `Chapter3_GraphTheory.lean`. Reuses
  `CDMGEquiv` / `fusionEquiv` / its groupoid laws verbatim from
  `TwoDisjointNodeSplittingsCommute.lean`. `lake build` clean (only the two
  expected `sorry` warnings on `swig_swig_equiv` and `swig_comm_equiv`).
- **T2 `review_design`:** **PASS.** Verifier confirmed `CDMGEquiv` is the only
  type-correct vehicle (iterated and merged carriers are not def-equal so
  literal `Eq` cannot type-check; same regime as the `\spl` sibling
  claim_3_7), `fusionEquiv` re-use is correct (SWIG inherits `α ⊕ ↑W` from
  `nodeSplittingOn`), and the bridging helper is structurally analogous to
  the `\spl` case. Downstream consumers (counterfactuals, identification)
  will compose cleanly via the `CDMGEquiv` groupoid.
- **T3 `verify_equivalence`:** **PASS.** Mechanical Lean-vs-LN check passed
  on hypotheses (`{G : CDMG α}`, `W₁ W₂ ⊆ V`, `Disjoint W₁ W₂`) and on the
  conclusion (`swig_swig_equiv` = fusion half, `swig_comm_equiv` = commute
  half; together they re-prove the chained equality `(G_W₁)_W₂ = (G_W₂)_W₁
  = G_{W₁⊔W₂}` modulo the canonical isomorphism `CDMGEquiv`). No silent
  strengthening / weakening / missing hypothesis spotted.
- **T4 `add_design_choice_comments`:** done. Comment blocks above all three
  declarations enriched with the **why** behind the design choice in the
  style of the sibling file's existing comments. `lake build` still clean
  (only the two expected `sorry` warnings).

**Lean file:**
`leanification/Chapter3_GraphTheory/Section3_2/TwoDisjointSwigsCommute.lean`
(post-design-comment) -- contains the three Lean declarations + the file
docstring + per-declaration design-rationale comment blocks.

**Aggregator:** `leanification/Chapter3_GraphTheory.lean` -- added
`import Chapter3_GraphTheory.Section3_2.TwoDisjointSwigsCommute`.

### Manager B handoff (next phase)

Manager B picks up here. The proof phase covers both the TeX proof and the
Lean proof, in one manager. The handoff dossier is in the `new_manager`
body of this manager's final turn -- summarised below for the workspace log:

- Empty TeX-proof stub lives at
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_10_proof_TwoDisjointNode.tex`
  (auto-created by the orchestrator; pre-populated with the restated Lem
  block at the top).
- LN proof is `graphs.tex` lines 635 -- 660. Structurally mirrors the
  claim_3_7 (`\spl`-only) proof at lines 466 -- 493 -- so the first action
  Manager B's `write_tex_proof.md` worker should take is to look at both
  the LN proof and at claim_3_7's tex proof file, then write the SWIG
  analogue. The high-level strategy choice (direct mirror vs. reduce to
  `\spl` fusion via claim_3_4/3_8) was deferred to the tex writer per
  plan step 8 above.
