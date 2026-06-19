import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_1.AcyclicIffTopologicalOrder
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.SplitTopologicalOrder

namespace Causality

/-!
# SWIG acyclicity and topological order (`claim_3_9`)

This file formalises the LN remark `claim_3_9` (`SwigAcyclic` in
`graphs.tex`, section 3.2):

> For a CADMG `G = (J, V, E, L)`, also `G_{swig(W)}` is acyclic.  If
> `<` is any topological order of `G` given by enumerating
> `J ∪ V = {v_1 < v_2 < ⋯ < v_n}`, then a topological order for
> `G_{swig(W)}` can be achieved by assigning, for `v_j ∈ W`, the
> index `j - 1/3` to `v_j^o` and `j + 1/3` to `v_j^i`, and then
> ordering all nodes according to their index value.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_9_statement_SwigAcyclic.tex`,
verified equivalent to the LN block by `verify_tex_statement_only` and
`verify_tex_statement_equivalence`.  No `addition_to_the_LN` clauses
were attached; the rewrite folded the LN-critic's three working-phase
subtleties directly into the canonical tex as non-load-bearing
clarifications:

* `non_W_node_index_assignment_implicit` — the LN's literal text
  assigns indices only to the tagged copies `v_j^o`, `v_j^i` of split
  nodes `v_j ∈ W`, and is silent on the indices of unsplit nodes
  `v_j ∈ J ∪ (V ∖ W)`.  The canonical tex spec records the natural
  and only-consistent reading: unsplit nodes retain their original
  index `j`.
* `one_third_offset_is_load_bearing_not_arbitrary` — the `1/3`
  offset is not aesthetic: any `δ ∈ (0, 1/2)` would work but
  `δ = 1/2` already collides on consecutive split nodes.  Resolved
  *structurally* by the case-analysis-based `splOrder` reused from
  `SplitTopologicalOrder.lean` (no `ℚ`-arithmetic, no offset
  parameter — the lex order on `(base, tag)` makes the
  consecutive-`W` collision impossible).
* `topological_order_claim_unverified_relies_on_no_transfer_edges`
  — sub-claim (b)'s topological-order assertion is consistent with
  the SWIG construction only because `def_3_12` item iii omits the
  `w^o → w^i` transfer edge that `def_3_11` carries.  The
  no-transfer-edge property is *inherited* from
  `NodeSplittingHard.lean`'s edge-set definition and surfaces here
  via the absence of a transfer-edge case in the parent-precedence
  obligation of `swigTopologicalOrder`.

The remark bundles two sub-claims under one `\begin{Rem}`:

* (a) **Acyclicity preservation.** `G_{swig(W)}` is acyclic
  (`def_3_6`'s `IsAcyclic`).
* (b) **Explicit topological order on `G_{swig(W)}`.** For every
  topological order `<` of `G`, the relation `splOrder lt` on
  `SplitNode Node` (reused verbatim from
  `SplitTopologicalOrder.lean` — see the design block on
  `swigTopologicalOrder` below for why the *same* lex order applies
  to both spl and SWIG) is a topological order of
  `G_{swig(W)}` (`def_3_8`'s `IsTopologicalOrder`).

Both sub-claims share the same hypotheses (`G.IsCADMG` and
`W ⊆ G.V`); they are stated as **two separate theorems**
(`swigAcyclic` for (a) and `swigTopologicalOrder` for (b)),
mirroring the `claim_3_6` (`SplitTopologicalOrder`) split — see the
"single theorem vs.\ two separate theorems" design-choice bullet on
`swigTopologicalOrder` below for the rationale.

The proof bodies are filled in by `prove_claim_in_lean` (Manager B),
following the verified TeX proof at
`tex/claim_3_9_proof_SwigAcyclic.tex` (to be written).
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signature references `CDMG Node`
--   (`def_3_1`), `G.IsCADMG` (`def_3_7`),
--   `G.nodeSplittingHard hCADMG W hW` (`def_3_12`),
--   `(G.nodeSplittingHard hCADMG W hW).IsAcyclic` (`def_3_6`),
--   `G.IsTopologicalOrder lt` (`def_3_8`), and
--   `(G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder (splOrder lt)`
--   (which goes through the SWIG CDMG's
--   `Pa : SplitNode Node → Set (SplitNode Node)` from `def_3_5`, in
--   turn requiring `[DecidableEq (SplitNode Node)]` — provided
--   automatically by `def_3_11`'s `deriving DecidableEq` on the
--   tagged-sum inductive that `def_3_12` reuses).  Stronger instances
--   (`Fintype`, `LinearOrder`) are not needed at the statement level.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in `Section3_2/` (`HardInterventionOn.lean`,
--   `AcyclicPreservedUnderDo.lean`, `HardInterventionsCommute.lean`,
--   `BifurcationAlternative.lean`, `NodeSplittingOn.lean`,
--   `SplitTopologicalOrder.lean`, `NodeSplittingHard.lean`) and in
--   `Section3_1/`.  The two-dash marker is reserved for declarations
--   whose body is the formalised LN content of the row; this
--   `variable` line is statement-typing infrastructure binding the
--   implicit `Node` type and its `DecidableEq` instance that the
--   two main theorems both reference.
-- claim_3_9 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_9 --- end helper

-- ## Proof-only helpers (private; live above the theorems)
--
-- The lemmas below are infrastructure for the proofs of `swigAcyclic`
-- and `swigTopologicalOrder`.  They are deliberately private, carry no
-- marker comments, and do not appear in the rendered statement.  Most
-- mirror their analogs in `SplitTopologicalOrder.lean` (also private
-- there) and are re-derived here because Lean's `private` mechanism
-- makes file-scoped helpers invisible across files.  See
-- `tex/claim_3_9_proof_SwigAcyclic.tex` for the TeX proof these
-- helpers implement.
--
-- *`baseOf` / `tagOf`.*  Same case-analysis projection as in
--   `SplitTopologicalOrder.lean`: `baseOf` recovers the underlying base
--   node and `tagOf` records the constructor tag in `{0, 1, 2}` with
--   the convention `.copy0 ↦ 0 < .unsplit ↦ 1 < .copy1 ↦ 2`, matching
--   the lex orientation baked into `splOrder`.
--
-- *`splOrder_iff`.*  Lex characterisation of `splOrder` —
--   `splOrder lt x y ↔ lt (baseOf x) (baseOf y) ∨ (baseOf x = baseOf y
--   ∧ tagOf x < tagOf y)`.  Reduces the 9 / 27-way constructor case
--   analyses (trichotomy / transitivity) to plain lex reasoning over
--   the base/tag pair.
--
-- *`splitNode_ext`.*  Two `SplitNode Node` agreeing on base and tag
--   are equal — needed to extract `x = y` from a base/tag equality
--   inside the trichotomy proof.
--
-- *`baseOf_mem_swig`.*  Membership `x ∈ G.nodeSplittingHard hCADMG W
--   hW` projects to `baseOf x ∈ G`, via case analysis on the SWIG
--   carrier `(G.J ∪ W^i) ∪ ((G.V ∖ W) ∪ W^o)`.  Differs from
--   `SplitTopologicalOrder.lean`'s `baseOf_mem` because the SWIG
--   construction reclassifies `W.image .copy1` into `J` (item i of
--   `def_3_12`) rather than leaving both tagged copies in `V`.
--
-- *`splOrder_lifted_edge`.*  Parent-precedence for a lifted edge
--   `(toCopy1 W v_1, toCopy0 W v_2)` given `lt v_1 v_2`.  Same proof
--   as in `SplitTopologicalOrder.lean`; re-derived locally.  Note that
--   there is *no* analog of `splOrder_transfer_edge` here, because
--   `def_3_12` item iii omits the transfer-edge set-builder entirely
--   — see the design block on `swigTopologicalOrder` for the
--   structural reason.
--
-- *`aux_swigTopologicalOrder`.*  Shared workhorse — proves
--   `(G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder (splOrder
--   lt)` directly under the hypotheses of sub-claim (b), consumed by
--   both `swigTopologicalOrder` (as a one-liner wrapper) and
--   `swigAcyclic` (where the topological-order witness is fed to the
--   `⇐` direction of `claim_3_2` to derive acyclicity).  Mirrors
--   `SplitTopologicalOrder.lean`'s `aux_splTopologicalOrder` with one
--   structural simplification in the parent-precedence branch: only
--   the lifted-edge sub-case is present (the transfer-edge sub-case
--   of `aux_splTopologicalOrder` has no analog here).




end CDMG

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Both fixtures are
--   inherited from `def_3_1`'s refactor twin (`CDMG`).  The
--   refactor twin's signature references `CDMG Node`
--   (root `def_3_1`), `G.IsCADMG` (`def_3_7` refactor twin),
--   `G.nodeSplittingHard hCADMG W hW` (`def_3_12` refactor
--   twin), `(G.nodeSplittingHard hCADMG W hW).IsAcyclic`
--   (`def_3_6` refactor twin), `G.IsTopologicalOrder lt`
--   (`def_3_8` refactor twin), and
--   `(G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder
--    (splOrder lt)` (which goes through the SWIG CDMG's
--   `Pa` from `def_3_5` refactor twin, in turn requiring
--   `[DecidableEq (SplitNode Node)]` — provided automatically
--   by `def_3_11`'s refactor twin via `deriving DecidableEq` on the
--   tagged-sum inductive `SplitNode` that `def_3_12`'s
--   refactor twin reuses).  No new typeclasses are needed: the
--   mathematical content of this row is unchanged by the refactor —
--   the bidirected-edge set `L` plays no role in either sub-claim, so
--   the `Finset (Node × Node) → Finset (Sym2 Node)` retyping at root
--   `def_3_1` does not reach this row at all.
--
-- *Three-dash `--- start helper` marker.*  Same convention as the
--   pre-refactor block above and as every sibling refactor twin in
--   `Section3_1/` and `Section3_2/`.
-- claim_3_9 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_9 --- end helper

-- ## Proof-only helpers (private; live above the theorems)
--
-- The lemmas below are infrastructure for the proofs of
-- `swigAcyclic` and `swigTopologicalOrder`.  They
-- are deliberately private, carry no helper marker comments, and do
-- not appear in the rendered statement.  Most mirror their analogs in
-- `SplitTopologicalOrder.lean`'s refactor twin (also private there)
-- and are re-derived here because Lean's `private` mechanism makes
-- file-scoped helpers invisible across files.  Each is wrapped in its
-- own REPLACEMENT marker pair so the Phase 7 cleanup script renames
-- `refactor_<name>` → `<name>` across the codebase.  See
-- `tex/refactor_claim_3_9_proof_SwigAcyclic.tex` for the TeX proof
-- these helpers implement; the role of each helper is:
--
-- *`baseOf` / `tagOf`.*  Case-analysis projections
--   onto the underlying base node (`baseOf`) and onto the
--   constructor tag in `{0, 1, 2}` (`tagOf`) with the
--   convention `.copy0 ↦ 0 < .unsplit ↦ 1 < .copy1 ↦ 2`, matching
--   the lex orientation baked into `splOrder`.  Same shape
--   as in `SplitTopologicalOrder.lean`'s refactor twin; re-derived
--   here against `SplitNode Node`.  These two projections
--   are also where the LN-critic working-phase wording subtleties
--   `non_W_node_index_assignment_implicit` and
--   `one_third_offset_is_load_bearing_not_arbitrary` get *structurally*
--   resolved: (i) `baseOf (.unsplit u) = u` makes the LN's
--   implicit "unsplit nodes keep their original index `j`" explicit
--   — an `.unsplit` node's `splOrder`-position is literally
--   its base node's `lt`-position; (ii) no rational offset `δ ∈ ℚ`
--   appears in the encoding, the discrete `tagOf` secondary
--   key rules out consecutive-`W` collisions by construction.
--
-- *`splOrder_iff`.*  Lex characterisation of
--   `splOrder` —
--   `splOrder lt x y ↔ lt (baseOf x) (baseOf y)
--   ∨ (baseOf x = baseOf y ∧
--   tagOf x < tagOf y)`.  Reduces the 9 / 27-way
--   constructor case analyses (trichotomy / transitivity) to plain
--   lex reasoning over the base/tag pair.
--
-- *`splitNode_ext`.*  Two `SplitNode Node` agreeing
--   on base and tag are equal — needed to extract `x = y` from a
--   base/tag equality inside the trichotomy proof.
--
-- *`baseOf_mem_swig`.*  Membership
--   `x ∈ G.nodeSplittingHard hCADMG W hW` projects to
--   `baseOf x ∈ G`, via case analysis on the SWIG carrier
--   `(G.J ∪ W^i) ∪ ((G.V ∖ W) ∪ W^o)`.  Differs from
--   `SplitTopologicalOrder.lean`'s `baseOf_mem` because the
--   SWIG construction reclassifies `W.image .copy1` into `J` (item i
--   of `def_3_12`) rather than leaving both tagged copies in `V`.
--
-- *`splOrder_lifted_edge`.*  Parent-precedence for a lifted
--   edge `(toCopy1 W v_1, toCopy0 W v_2)` given
--   `lt v_1 v_2`.  Same proof as in `SplitTopologicalOrder.lean`'s
--   refactor twin; re-derived locally.  Note that there is *no*
--   analog of `splOrder_transfer_edge` here, because
--   `def_3_12` item iii omits the transfer-edge set-builder entirely
--   — see the design block on `swigTopologicalOrder` for
--   the structural reason.
--
-- *`aux_swigTopologicalOrder`.*  Shared workhorse — proves
--   `(G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder
--   (splOrder lt)` directly under the hypotheses of
--   sub-claim (b), consumed by both `swigTopologicalOrder`
--   (as a one-liner wrapper) and `swigAcyclic` (where the
--   topological-order witness is fed to the `⇐` direction of
--   `claim_3_2`'s refactor twin to derive acyclicity).  Mirrors
--   `SplitTopologicalOrder.lean`'s `aux_splTopologicalOrder`
--   with one structural simplification in the parent-precedence
--   branch: only the lifted-edge sub-case is present (the
--   transfer-edge sub-case of `aux_splTopologicalOrder` has
--   no analog here because `def_3_12` item iii omits the second
--   set-builder).  Litmus: removing any of the six other helpers
--   above would break this auxiliary lemma, and removing this
--   auxiliary lemma would break both top-level theorems.
--
-- *Independent of the bidirected-edge channel `L`.*  None of the
--   seven helpers above inspects the `L` field of any
--   `CDMG`; every helper reads only `J` / `V` / `E` or the
--   constructor tag of `SplitNode`.  The
--   `Finset (Sym2 Node)` retyping of `L` at root `def_3_1` does not
--   reach any helper, which is why the file-level refactor delta on
--   this row is purely a name-bump from `CDMG` / `SplitNode` / `Pa`
--   / ... to `CDMG` / `SplitNode` / `Pa`
--   / ... .

private def baseOf : SplitNode Node → Node
  | .unsplit u => u
  | .copy0 w => w
  | .copy1 w => w

private def tagOf : SplitNode Node → ℕ
  | .copy0 _ => 0
  | .unsplit _ => 1
  | .copy1 _ => 2

omit [DecidableEq Node] in
private lemma splOrder_iff (lt : Node → Node → Prop)
    (x y : SplitNode Node) :
    splOrder lt x y ↔
      lt (baseOf x) (baseOf y) ∨
        (baseOf x = baseOf y ∧
          tagOf x < tagOf y) := by
  cases x <;> cases y <;> simp [splOrder, baseOf, tagOf]

omit [DecidableEq Node] in
private lemma splitNode_ext {x y : SplitNode Node}
    (hbase : baseOf x = baseOf y)
    (htag : tagOf x = tagOf y) : x = y := by
  cases x <;> cases y <;> simp_all [baseOf, tagOf]

private lemma baseOf_mem_swig {G : CDMG Node}
    {hCADMG : G.IsCADMG} {W : Finset Node} {hW : W ⊆ G.V}
    {x : SplitNode Node}
    (hx : x ∈ G.nodeSplittingHard hCADMG W hW) :
    baseOf x ∈ G := by
  change baseOf x ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp hx with hJ | hV
  · -- `x ∈ J_{swig(W)} = G.J.image .unsplit ∪ W.image .copy1`
    rcases Finset.mem_union.mp hJ with hJuns | hC1
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJuns
      exact Finset.mem_union_left _ hj
    · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hC1
      exact Finset.mem_union_right _ (hW hwW)
  · -- `x ∈ V_{swig(W)} = (G.V \ W).image .unsplit ∪ W.image .copy0`
    rcases Finset.mem_union.mp hV with hVuns | hC0
    · obtain ⟨v, hvVW, rfl⟩ := Finset.mem_image.mp hVuns
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hvVW).1
    · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hC0
      exact Finset.mem_union_right _ (hW hwW)

private lemma splOrder_lifted_edge {lt : Node → Node → Prop}
    (W : Finset Node) {v1 v2 : Node} (h : lt v1 v2) :
    splOrder lt (toCopy1 W v1) (toCopy0 W v2) := by
  unfold toCopy0 toCopy1
  split_ifs <;> exact h

private lemma aux_swigTopologicalOrder (G : CDMG Node)
    (hCADMG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder
      (splOrder lt) := by
  obtain ⟨⟨h_irrefl, h_trans, h_tri⟩, h_pa⟩ := hlt
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Irreflexivity
    intro x hx hsplx
    rw [splOrder_iff] at hsplx
    rcases hsplx with hlt_xx | ⟨_, htag⟩
    · exact h_irrefl (baseOf x) (baseOf_mem_swig hx) hlt_xx
    · exact Nat.lt_irrefl _ htag
  · -- Transitivity
    intro x hx y hy z hz hxy hyz
    rw [splOrder_iff] at hxy hyz ⊢
    rcases hxy with hlt_xy | ⟨hbase_xy, htag_xy⟩
    · rcases hyz with hlt_yz | ⟨hbase_yz, _⟩
      · left
        exact h_trans (baseOf x) (baseOf_mem_swig hx)
          (baseOf y) (baseOf_mem_swig hy)
          (baseOf z) (baseOf_mem_swig hz) hlt_xy hlt_yz
      · left; rw [← hbase_yz]; exact hlt_xy
    · rcases hyz with hlt_yz | ⟨hbase_yz, htag_yz⟩
      · left; rw [hbase_xy]; exact hlt_yz
      · right
        exact ⟨hbase_xy.trans hbase_yz, htag_xy.trans htag_yz⟩
  · -- Trichotomy
    intro x hx y hy
    rcases h_tri (baseOf x) (baseOf_mem_swig hx)
      (baseOf y) (baseOf_mem_swig hy)
      with hlt_xy | hbase_eq | hlt_yx
    · left; rw [splOrder_iff]; left; exact hlt_xy
    · rcases Nat.lt_trichotomy (tagOf x) (tagOf y)
        with htag | htag | htag
      · left; rw [splOrder_iff]; right; exact ⟨hbase_eq, htag⟩
      · right; left; exact splitNode_ext hbase_eq htag
      · right; right; rw [splOrder_iff]; right
        exact ⟨hbase_eq.symm, htag⟩
    · right; right; rw [splOrder_iff]; left; exact hlt_yx
  · -- Parent precedence — single case (lifted edge); no transfer-edge case
    -- because `def_3_12` item iii omits the transfer-edge set-builder.
    intro u w h_pa_uw
    obtain ⟨_, h_uw_E⟩ := h_pa_uw
    -- (u, w) ∈ E_{swig(W)} = G.E.image (fun e => (toCopy1 W e.1,
    --                                              toCopy0 W e.2))
    obtain ⟨⟨v1, v2⟩, he_E, h_eq⟩ := Finset.mem_image.mp h_uw_E
    simp only [Prod.mk.injEq] at h_eq
    obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
    rw [← h_u_eq, ← h_w_eq]
    have hv1_in_G : v1 ∈ G := (G.hE_subset he_E).1
    have hlt_v1_v2 : lt v1 v2 := h_pa v1 v2 ⟨hv1_in_G, he_E⟩
    exact splOrder_lifted_edge W hlt_v1_v2

-- ref: claim_3_9 (sub-claim (a), acyclicity preservation)
--
-- For a CADMG `G` and `W ⊆ G.V`, the SWIG
-- `G.nodeSplittingHard hCADMG W hW` (`def_3_12`) is acyclic
-- in the sense of `def_3_6`'s `IsAcyclic`.
--
-- *Why the `IsCADMG` hypothesis is load-bearing.*  Without
-- it, the SWIG construction does NOT preserve acyclicity in general:
-- per the rewritten tex spec's "Role of the CADMG (acyclicity)
-- precondition" paragraph, two failure modes appear if `G` is allowed
-- to be cyclic.  (i) A directed cycle in `G` whose nodes lie entirely
-- in `V ∖ W` lifts under `def_3_12` item iii to a directed cycle of
-- the same length in `G_{swig(W)}` (the shorthand `v^i = v^o = v` for
-- `v ∉ W` makes each lifted edge coincide with the original).
-- (ii) A directed self-loop `(w, w) ∈ G.E` for `w ∈ W` lifts to the
-- directed edge `(w^i, w^o) = (.copy1 w, .copy0 w)`, which is *not* a
-- self-loop (different constructors) but whose endpoint indices
-- `φ(w^i) = j + 1/3 > j - 1/3 = φ(w^o)` *would* violate the
-- parent-precedence requirement of any topological order, so the
-- existence claim of sub-claim (b) fails on this graph — and by
-- `claim_3_2` (acyclic ⟺ topological-order-exists) that already
-- implies the SWIG is *not* acyclic.  `hCADMG` rules both modes out:
-- acyclicity of `G` forbids the `V ∖ W` cycle directly and forbids
-- directed self-loops on `V` (the `def_3_6` no-self-loop consequence),
-- hence forbids `(w, w) ∈ G.E` for any `w ∈ W ⊆ G.V`.  Note: unlike
-- `splAcyclic` (claim_3_6 sub-claim (a)), there is no
-- length-2 `w^o → w^i → w^o` cycle to worry about, because SWIG omits
-- the transfer edge `(w^o, w^i)` that `def_3_11` includes (cf.\
-- `NodeSplittingHard.lean`'s "Self-loops on `W` produce no cycles in
-- `G_{swig(W)}`" design bullet).
/-
LN tex (sub-claim (a), from the rewritten canonical statement for
`claim_3_9`):

  (a) `G_{swig(W)}` is acyclic.  The CDMG `G_{swig(W)}` is acyclic
      in the sense of def \ref{def-acylic}, i.e.\ for every
      `x ∈ J_{swig(W)} ∪ V_{swig(W)} = J ∪ (V ∖ W) ⊍ W^o ⊍ W^i`,
      there does not exist any non-trivial directed walk from `x` to
      itself in `G_{swig(W)}`.
-/
-- ## Design choice
--
-- *Single-theorem statement (sub-claim (a) only), separated from
--   sub-claim (b).*  See the shared "one theorem vs.\ two separate
--   theorems" bullet in the `swigTopologicalOrder` design
--   block below.  Briefly: `swigAcyclic` is the standalone
--   acyclicity-preservation fact that downstream consumers (the
--   do-calculus and counterfactual identification chapters that
--   build joint distributions over the SWIG) are expected to need
--   *on its own* (without dragging in the topological-order
--   construction); keeping it as its own theorem lets those
--   consumers state `G.swigAcyclic hCADMG W hW` without
--   ever mentioning `splOrder` or a chosen `lt`.  Matches
--   the `splAcyclic` / `splTopologicalOrder` split
--   in `SplitTopologicalOrder.lean` exactly.
--
-- *`IsCADMG`, not `IsAcyclic`.*  See the shared
--   bullet in the `swigTopologicalOrder` design block
--   below; the same choice applies here.  LN-faithful naming
--   (`def_3_7` item i) wins over the micro-simplification of
--   inlining the `IsAcyclic` alias.  In addition,
--   `nodeSplittingHard` (`def_3_12`) *requires*
--   `(hCADMG : G.IsCADMG)` in its own signature — so
--   taking `hCADMG` here lets us pass it through to
--   `nodeSplittingHard` without an extra
--   `IsCADMG`/`IsAcyclic` round-trip.
--
-- *Hypotheses ordered `(G, hCADMG, W, hW)`.*  Mirrors the LN reading
--   "For a CADMG `G` ... and `W ⊆ V`, ..." and matches the binder
--   ordering of `def_3_12` `nodeSplittingHard` exactly
--   (`(G) (hG := hCADMG) (W) (hW)`), so the conclusion's
--   `G.nodeSplittingHard hCADMG W hW` application reads
--   left-to-right with the binder block.
--
-- *Independent of the bidirected-edge channel `L`.*  None of
--   `IsCADMG`, `nodeSplittingHard`,
--   `IsAcyclic` consumes the `L` field of the underlying
--   CDMG record at the level of *this* statement: acyclicity is a
--   property of directed walks on the `E`-side alone.  The CDMG
--   record itself carries an `L`-channel (see `def_3_1`'s docstring
--   on `CDMG` for the `Finset (Sym2 Node)` encoding), and
--   `nodeSplittingHard` populates the SWIG's `L`-channel
--   via `Sym2.map (toCopy0 W)`, but acyclicity of the
--   result reads only the new `E`-side.  Sub-claim (a) is therefore
--   robust under any future change to the `L`-channel encoding.
-- claim_3_9 -- start statement
theorem swigAcyclic (G : CDMG Node) (hCADMG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V) :
    (G.nodeSplittingHard hCADMG W hW).IsAcyclic
-- claim_3_9 -- end statement
  := by
  have hAcyclic : G.IsAcyclic := hCADMG
  obtain ⟨lt, hlt⟩ := (acyclic_iff_topological_order G).mp hAcyclic
  exact (acyclic_iff_topological_order
      (G.nodeSplittingHard hCADMG W hW)).mpr
    ⟨splOrder lt,
      aux_swigTopologicalOrder G hCADMG W hW lt hlt⟩

-- ref: claim_3_9 (sub-claim (b), explicit topological-order construction)
--
-- For a CADMG `G`, a subset `W ⊆ G.V`, and any topological order
-- `lt` of `G` in the sense of `def_3_8`, the lifted relation
-- `splOrder lt` (reused verbatim from
-- `SplitTopologicalOrder.lean`'s refactor twin) is a topological
-- order of the SWIG `G.nodeSplittingHard hCADMG W hW`.
--
-- Unfolded,
-- `(G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder
--  (splOrder lt)` asserts (per `def_3_8`):
--
--   * `splOrder lt` is a strict total order on
--     `J_{swig(W)} ∪ V_{swig(W)}` (irreflexive, transitive,
--     trichotomous; via the nested `IsTotalOrder`
--     projection);
--   * for every parent–child pair
--     `v ∈ (G.nodeSplittingHard hCADMG W hW).Pa w`,
--     we have `splOrder lt v w`.
--
-- The parent-precedence clause is the load-bearing content of the
-- construction: every edge of `E_{swig(W)}` is a lifted edge
-- `(v_1^i, v_2^o) = (toCopy1 W v_1, toCopy0 W v_2)`
-- arising from `(v_1, v_2) ∈ G.E` — where parent-precedence under
-- `splOrder` follows from parent-precedence under `lt`
-- (which `hlt` provides) plus the lex-order layout of
-- `splOrder` on the resulting tagged pair (one of four
-- mixed-tag cases depending on whether `v_1` and `v_2` lie in `W`).
-- Crucially — and unlike `splTopologicalOrder` (claim_3_6
-- sub-claim (b)) — there is *no* transfer-edge case to discharge:
-- `def_3_12` item iii does not introduce `(w^o, w^i)` edges, so the
-- parent-precedence obligation has exactly one (lifted-edge)
-- sub-case.  See the
-- `topological_order_claim_unverified_relies_on_no_transfer_edges`
-- bullet in the file header for the LN-critic working-phase
-- subtlety this clean parent-precedence shape resolves.
/-
LN tex (sub-claim (b), from the rewritten canonical statement for
`claim_3_9`):

  (b) An explicit topological order on `G_{swig(W)}` obtained from
      any topological order on `G`.  For every topological order `<`
      of `G` ..., the binary relation `<_{swig}` on
      `J_{swig(W)} ∪ V_{swig(W)}` defined below is a topological
      order of `G_{swig(W)}` in the sense of
      def \ref{def-topological-order}.

      Index map.  Define `φ : J_{swig(W)} ∪ V_{swig(W)} → ℚ` by case
      analysis on the disjoint-union carrier
      `J ∪ (V ∖ W) ⊍ W^o ⊍ W^i`:
        · `φ(v_j) := j` for unsplit `v_j ∈ J ∪ (V ∖ W)`;
        · `φ(w^o) := j - 1/3`, `φ(w^i) := j + 1/3` for `w = v_j ∈ W`.

      Order from index map.  Define
        `x <_{swig} y :⇔ φ(x) < φ(y)`
      for `x, y ∈ J_{swig(W)} ∪ V_{swig(W)}`, where the right-hand
      inequality is the standard strict order on `ℚ`.
-/
-- ## Design choice
--
-- *One theorem vs.\ two separate theorems — picked TWO.*  The LN
--   bundles (a) and (b) inside one `\begin{Rem}`, but the two
--   sub-claims have *different downstream consumers*: the
--   do-calculus / counterfactual chapters typically consume only (a)
--   — the acyclicity / CADMG-ness of the SWIG — to lift the CDMG
--   return type to an `IsCADMG` graph and invoke chapter-4
--   / 5 CBN-shaped results.  Bundling (a) and (b) into a single
--   `swigAcyclic ∧ swigTopologicalOrder`-shaped
--   theorem would force every such consumer to take a topological-
--   order argument it does not use.  Splitting them keeps each
--   statement focused.  Matches the `splAcyclic` /
--   `splTopologicalOrder` split in
--   `SplitTopologicalOrder.lean` (claim_3_6) and the chapter
--   convention in `def_3_7`'s `IsCADMG`, `IsADMG`,
--   `IsDAG`, … (one atomic-condition predicate per
--   sub-statement).  The LN-faithful reading of "the remark holds"
--   is preserved because both theorems are stated under the same
--   `-- ref: claim_3_9 ...` heading and read as the two sub-claims
--   of one remark.
--
-- *Reuse `splOrder` from `SplitTopologicalOrder.lean`'s
--   refactor twin, do NOT introduce a parallel `refactor_swigOrder`.*
--   `splOrder` is defined as a pure case-analysis lex order
--   on `SplitNode Node` with the convention
--   `.copy0 < .unsplit < .copy1` per base node — its semantics
--   depends *only* on the constructor tag and the underlying `lt`,
--   NOT on whether we are in the spl or SWIG construction.
--   Concretely, the LN's two index assignments
--     · spl  : `v_j^0 ↦ j - 1/3`, `v_j^1 ↦ j + 1/3`
--              (so `.copy0 < .copy1` per base node)
--     · SWIG : `v_j^o ↦ j - 1/3`, `v_j^i ↦ j + 1/3`
--              (so `.copy0 < .copy1` per base node)
--   coincide on the nose, because in both cases `def_3_11` /
--   `def_3_12` identify `^0 / ^o ↔ .copy0` and `^1 / ^i ↔ .copy1`
--   (cf.\ `NodeSplittingHard.lean`'s design bullet (a): "the
--   convention `.copy0 ↔ ^o` (output side) and `.copy1 ↔ ^i` (input
--   side)").  So `splOrder lt` is literally the same
--   relation we'd write down for a freshly named
--   `refactor_swigOrder lt`; introducing a parallel
--   `refactor_swigOrder := splOrder` (or duplicating the
--   case-analysis) would be pure noise — it would (i) duplicate
--   every irreflexivity / transitivity / trichotomy lemma already
--   proven for `splOrder` in
--   `SplitTopologicalOrder.lean`, (ii) tempt future refactors to
--   diverge the two definitions, and (iii) hide the structural
--   identity that the same `SplitNode Node` carrier
--   supports both constructions with the same lex orientation.  This
--   is the "Build on what is already there" pattern called out in
--   the row-worker prompt.
--
-- *`IsCADMG`, not `IsAcyclic`.*  The LN reads
--   "For a CADMG `G`", referring explicitly to `def_3_7`'s named
--   attribute.  `IsCADMG` unfolds to `IsAcyclic`
--   (`def_3_7` item i — see `CDMGTypes.lean`), so the two would be
--   interchangeable at the *content* level.  We pick
--   `IsCADMG` to keep the Lean signature LN-faithful (a
--   reader greps `CADMG` from the LN and finds the matching Lean
--   hypothesis without a translation step).  In addition, `def_3_12
--   nodeSplittingHard`'s signature *requires*
--   `(hG : G.IsCADMG)`, so taking `hCADMG :
--   G.IsCADMG` here threads through the SWIG application
--   `G.nodeSplittingHard hCADMG W hW` directly without an
--   extra `IsCADMG ↔ IsAcyclic` round-trip.  See
--   `BifurcationAlternative.lean` and `SplitTopologicalOrder.lean`
--   for the matching chapter-3 precedents.
--
-- *`lt` and `hlt` as explicit positional arguments, not bundled
--   into an inner `∀ lt, …` quantifier.*  The LN's "for every
--   topological order `<` of `G`" is universal over `lt`, but
--   encoding it as an *outer* binder on the theorem is equivalent
--   and substantially more ergonomic at the call site.  Matches the
--   chapter convention of carrying universal-quantifier inputs as
--   outermost positional arguments (cf.\
--   `splTopologicalOrder` in the sibling
--   `SplitTopologicalOrder.lean`).
--
-- *`lt` typed as a bare `Node → Node → Prop`, not as a
--   `[LinearOrder Node]` / `[StrictTotalOrder Node]` / `[LT Node]`
--   typeclass instance.*  The LN's "for any topological order `<`
--   of `G`" universally quantifies over an arbitrary binary
--   relation that *happens* to satisfy `IsTopologicalOrder`
--   (`def_3_8`); it does NOT presume `Node` carries a canonical,
--   typeclass-resolved order.  Encoding `lt` as a positional
--   `Node → Node → Prop` argument matches that reading exactly.
--   Matches the convention spelled out in
--   `SplitTopologicalOrder.lean`'s `splTopologicalOrder`
--   design block.
--
-- *Conclusion `IsTopologicalOrder (splOrder lt)`,
--   not a fresh indexed-order predicate.*  We reuse `def_3_8`'s
--   `IsTopologicalOrder` *verbatim* against the *SWIG*
--   CDMG: every ingredient is already in place because
--   `G.nodeSplittingHard hCADMG W hW` is a
--   `CDMG (SplitNode Node)` (per `def_3_12`'s
--   return type) and `IsTopologicalOrder` is polymorphic
--   in the node type.
--
-- *Hypotheses ordered `(G, hCADMG, W, hW, lt, hlt)`.*  Matches the
--   `swigAcyclic` ordering, then adds `(lt, hlt)` at the
--   end (the *additional* hypotheses sub-claim (b) needs over (a)).
--
-- *No transfer-edge sub-case in the parent-precedence obligation.*
--   In `splTopologicalOrder`, the parent-precedence proof
--   case-splits on whether an edge of `E_{spl(W)}` is a *lifted*
--   edge or a *transfer* edge `(.copy0 w, .copy1 w)`.  In
--   `swigTopologicalOrder`, the second case is absent:
--   `def_3_12` item iii has *no* transfer-edge sub-builder.  Every
--   edge of `E_{swig(W)}` comes from the lifted set-builder
--   `G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))`
--   alone.  This is a structural simplification, not a content
--   change.  Resolves the LN-critic working-phase wording subtlety
--   `topological_order_claim_unverified_relies_on_no_transfer_edges`
--   by surfacing the dependency on `def_3_12` item iii at the type
--   level: there is exactly one (lifted-edge) sub-case in the proof,
--   and the absence of a transfer-edge sub-case is visible in the
--   `aux_swigTopologicalOrder` body (no
--   `splOrder_transfer_edge` helper exists in this file, contrast
--   with `SplitTopologicalOrder.lean`).
--
-- *Structural resolution of the remaining two LN-critic wording
--   subtleties.*  The reused lex-based `splOrder` also
--   resolves the other two subtleties flagged in the working-phase
--   critic report (the file header lists all three).
--   (i) `one_third_offset_is_load_bearing_not_arbitrary` — the
--   LN's literal `φ : J_{swig(W)} ∪ V_{swig(W)} → ℚ` with `±1/3`
--   offsets on `w^o`, `w^i` is replaced by a *structural*
--   `(baseOf, tagOf)` lex order on the tagged-sum
--   carrier `SplitNode Node`; no rational offset appears
--   in the encoding at all, so the LN's "any `δ ∈ (0, 1/2)` would
--   also have worked" degree of freedom is collapsed into a single
--   canonical discrete tag ordering, and the consecutive-`W`
--   collision that would occur at `δ = 1/2` is *impossible by
--   construction* (the `tagOf` secondary key only resolves
--   ties on the same base node).  (ii)
--   `non_W_node_index_assignment_implicit` — the LN states `φ`
--   only on the tagged copies `v_j^o`, `v_j^i` for `v_j ∈ W` and
--   leaves the index of unsplit `v_j ∈ J ∪ (V ∖ W)` implicit.  The
--   Lean encoding makes the implicit reading explicit by routing
--   `.unsplit u` through `baseOf .unsplit u = u`: an
--   unsplit node's `splOrder`-position is *literally* its
--   `lt`-position on the underlying base node.  No fresh index
--   assignment is needed because the carrier `SplitNode`
--   has a structural `.unsplit` constructor that the original
--   topological order `lt` already covers.  Both resolutions are
--   inherited verbatim from `SplitTopologicalOrder.lean`'s twin
--   (the design block on `splOrder` there spells the
--   structural reasoning in full).
--
-- *Independent of the bidirected-edge channel `L`.*
--   `IsTopologicalOrder` only inspects
--   `IsTotalOrder` (totality conditions on `J ∪ V`) and
--   `Pa` (parent set from `G.E` alone) — both
--   `(J, V, E)`-skeleton facts.  `splOrder` reads only the
--   constructor tag of `SplitNode` and the underlying
--   `lt`, so it likewise does not touch `L`.  See `def_3_1`'s
--   docstring on `CDMG` for the canonical `L`-channel
--   design; none of that detail reaches this theorem.
-- claim_3_9 -- start statement
theorem swigTopologicalOrder (G : CDMG Node)
    (hCADMG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.nodeSplittingHard hCADMG W hW).IsTopologicalOrder
      (splOrder lt)
-- claim_3_9 -- end statement
  := by
  exact aux_swigTopologicalOrder G hCADMG W hW lt hlt

end CDMG

end Causality
