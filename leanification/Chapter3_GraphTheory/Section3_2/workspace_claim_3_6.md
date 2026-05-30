# Workspace: claim_3_6 (SplitTopologicalOrder) — refactor `claim_3_2_no_finite`

## Context summary

- **Row**: `claim_3_6`, title `SplitTopologicalOrder`, claim, section 3.2.
- **LN block** (`graphs.tex` Rem ~lines 444–455): "For a CADMG $G$,
  also $G_{\spl(W)}$ is acyclic. If $<$ is any topological order of
  $G$... a topological order for $G_{\spl(W)}$ can be achieved by
  assigning $v_j^0$ index $j-1/3$ and $v_j^1$ index $j+1/3$ and
  ordering by index value."
- **Refactor goal**: this row is part of the `claim_3_2_no_finite`
  refactor (root claim_3_2 is now finiteness-free via Szpilrajn). The
  existing Lean file (`Section3_2/SplitTopologicalOrder.lean`) already
  declares both halves WITHOUT `[Finite α]`, but Part B's proof was
  done via route (ii) (direct walk-lifting; ~100 lines) *because*
  route (i) was finiteness-locked at the time. With claim_3_2's
  refactor live, route (i) is now finiteness-free, much shorter, and
  closer to the LN's reading.

## Current state of the original (read this first)

`leanification/Chapter3_GraphTheory/Section3_2/SplitTopologicalOrder.lean`
declares:

1. `splitOrder W r : (α ⊕ ↑W) → (α ⊕ ↑W) → Prop` (helper def; 4-case
   pattern match implementing the LN's $\pm 1/3$ interleave). **No
   refactor needed** — purely relational, no finiteness in sight.
2. `isTopologicalOrder_nodeSplittingOn` — Part A, the constructive
   half. Statement: given `hW : W ⊆ G.V` and `hr : G.IsTopologicalOrder
   r`, `splitOrder W r` is a topological order of `G.nodeSplittingOn
   W hW`. **No refactor needed** — already finiteness-free; proof uses
   only `IsTopologicalOrder` field-level case analysis + the
   `@[simp]` membership lemmas of `NodeSplittingOn.lean`.
3. `isAcyclic_nodeSplittingOn` — Part B. Statement: given `hW : W ⊆
   G.V` and `h : G.IsAcyclic`, `(G.nodeSplittingOn W hW).IsAcyclic`.
   Statement is already finiteness-free; **the proof is the
   refactor target.** Currently route (ii) (project the hypothetical
   cycle via `Sum.elim id Subtype.val`, compress split edges, derive
   contradiction in `G`). Long, intricate. Replacement: route (i),
   one-liner via the new `refactor_isAcyclic_iff_hasTopologicalOrder`
   + Part A.

## Refactor plan

### What stays untouched
- `splitOrder` (helper def, no markers).
- `isTopologicalOrder_nodeSplittingOn` (Part A, no markers).
- Original `isAcyclic_nodeSplittingOn` block (wrapped in
  `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: isAcyclic_nodeSplittingOn`).
- Original tex proof file (`tex/claim_3_6_proof_SplitTopologicalOrder.tex`,
  which is actually an empty stub — leave untouched until Phase 7).

### What gets added (replacement)
- `REFACTOR-BLOCK-REPLACEMENT-BEGIN: isAcyclic_nodeSplittingOn (was:
  refactor_isAcyclic_nodeSplittingOn)` wrapping a fresh
  `refactor_isAcyclic_nodeSplittingOn` declaration whose proof is:

  ```lean
  theorem refactor_isAcyclic_nodeSplittingOn
      {G : CDMG α} {W : Set α} (hW : W ⊆ G.V)
      (h : G.IsAcyclic) :
      (G.nodeSplittingOn W hW).IsAcyclic := by
    obtain ⟨r, hr⟩ := (refactor_isAcyclic_iff_hasTopologicalOrder G).mp h
    exact (refactor_isAcyclic_iff_hasTopologicalOrder _).mpr
      ⟨splitOrder W r, isTopologicalOrder_nodeSplittingOn hW hr⟩
  ```

  Plus updated design-choice comment block explaining: "route (i) is
  now finiteness-free thanks to the claim_3_2 refactor; this matches
  the LN's reading (which doesn't mention finiteness anywhere)."

- New tex twin
  `tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex` mirroring
  the new Lean proof: brief proof saying "by claim_3_2 (now
  finiteness-free), $G$ acyclic gives a topological order $r$; by the
  constructive half of this remark, $\splitOrder W r$ is a topological
  order of $G_{\spl(W)}$; by the converse of claim_3_2, the split
  graph is acyclic." Plus the LN's $\pm 1/3$ interleave description
  for the constructive half (which is exactly the LN remark's body).

## Workflow

This is a **proof-only refactor** — both statements stay unchanged
(no `review_design` / `verify_equivalence` needed at the statement
level; the originals already passed those gates). The remaining
workflow:

1. `spawn_agent_sub_task` → `write_tex_proof.md` targeting
   `tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex` (the
   twin). The worker writes a tex proof reflecting route (i).
2. `verify_tex_proof` on the twin.
3. `spawn_agent_sub_task` → `prove_claim_in_lean.md`. The worker:
   - wraps the existing `isAcyclic_nodeSplittingOn` in
     `REFACTOR-BLOCK-ORIGINAL-BEGIN/END` markers (no change to
     contents).
   - appends a `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END` block with the
     short route-(i) proof, named `refactor_isAcyclic_nodeSplittingOn`.
   - updates the design-choice comment block above the replacement to
     reflect the new (post-refactor) reasoning.
   - leaves `splitOrder`, `isTopologicalOrder_nodeSplittingOn`, and
     the file header alone.
4. `simplify_proof` on the replacement.
5. `solved` → final gate.

## Key file paths

- Original Lean (read for inspiration, then add markers around Part B):
  `leanification/Chapter3_GraphTheory/Section3_2/SplitTopologicalOrder.lean`
- Original tex proof (empty stub — DO NOT TOUCH):
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_6_proof_SplitTopologicalOrder.tex`
- Tex twin to create (this is the worker's target):
  `leanification/Chapter3_GraphTheory/Section3_2/tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex`
- Model for the marker convention + replacement style:
  `leanification/Chapter3_GraphTheory/Section3_1/AcyclicIffTopologicalOrder.lean`
  (just-solved sibling row in this same refactor table).
- LN source:
  `lecture-notes/lecture_notes/graphs.tex` (search for the Rem block
  following def_3_11 `nodeSplittingOn`).
