import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_2.HardInterventionOn

namespace Causality

/-!
# Bifurcation alternative (`claim_3_5`)

This file formalises the LN proposition `claim_3_5`
(`\label{prp:bifurcations_alternative}` in `graphs.tex`,
section 3.2):

> Let `G = (J, V, E, L)` be a CDMG.  For `v, w, c ∈ V ∪ J`:
> there exists a bifurcation between `v` and `w` in `G` with source
> `c` if and only if `v ≠ w` and `c ∈ Anc^{G_{do(w)}}(v) ∖ {v}` and
> `c ∈ Anc^{G_{do(v)}}(w) ∖ {w}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_5_statement_BifurcationAlternative.tex`, verified equivalent
to the LN block by `verify_tex_statement_only` and
`verify_tex_statement_equivalence`.  The rewritten tex spells out:

* the three universal quantifiers on `v, w, c ∈ J ∪ V`
  (rendered here as the three explicit membership hypotheses
  `hv : v ∈ G`, `hw : w ∈ G`, `hc : c ∈ G`, via the
  `Membership Node (CDMG Node)` instance of `def_3_2`);
* the singleton-set reading of the LN's `do(w)` / `do(v)` shorthand
  — `G_{do(w)}` is `G.hardInterventionOn ({w} : Finset Node) hw`
  in the sense of `def_3_10` (`HardInterventionOn.lean`);
* the literal set-difference shape `Anc^{...}(v) ∖ {v}` rather than
  the equivalent conjunction `c ∈ Anc ∧ c ≠ v`, matching the LN's
  notation verbatim;
* the LN-critic resolution
  `source_at_endpoint_w_when_right_arm_trivial`: under our
  `def_3_4` encoding's chapter-init addition
  `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
  `IsBifurcationSource p c` already commits to the interior-source
  convention (the LN-critic's `k = n` directed-hinge corner case is
  excluded by `Walk.IsBifurcationDirectedHingeWithSplit`'s
  `.cons _ _ _ (.nil _ _), 0 => False` branch).  Consequently
  this proposition is provable as-stated, and no
  `addition_to_the_LN` clause was needed for `claim_3_5`
  (see `workspace_claim_3_5.md` and the comment block above the
  `\begin{Prp}` in the rewritten tex spec).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the verified TeX proof at
`tex/claim_3_5_proof_BifurcationAlternative.tex`.

TeX proof: `claim_3_5_proof_BifurcationAlternative.tex`.

## Proof status

The TeX proof was verified by `verify_tex_statement_plus_proof` and
`verify_tex_proof`, and the Lean translation is complete.  The
walk-level infrastructure built up in the helper block of this file
(subtasks 1–7 of the planned dispatch) supplies:

* a walk concatenation `Walk.comp` (subtask 2; mirrored from
  `AcyclicIffTopologicalOrder.lean`),
* a walk lift `Walk.liftFromHardIntervention` (subtask 1) and its
  converse `Walk.liftTo_hardInterventionOn` (subtask 3) between `G`
  and `G_{do(W)}`,
* a `Walk.truncateAtFirst` truncation function plus the
  minimum-length-walk existence `exists_directed_walk_v_not_in_dropLast`
  (subtask 4) used by the (⇐) direction's clause (e) bookkeeping,
* a `mkBifurcation` constructor that combines two directed arms into
  a bifurcation walk (subtask 5) and the associated
  `isBifurcationDirectedHinge_mkBifurcation` realisation (subtask 6),
* an arm-extraction lemma `exists_arms_of_bifurcation_directed_hinge`
  (subtask 7) that turns an `IsBifurcationDirectedHingeWithSplit p i`
  hypothesis into directed walks `L : Walk G c v` and `R : Walk G c w`
  whose vertices lie inside `p.vertices.dropLast` / `p.vertices.tail`.

The main theorem body (subtask 8) glues these helpers together
following the verified TeX proof step-by-step in both directions.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signature references `CDMG Node`,
--   `Walk G v w` (`def_3_4`), `Walk.IsBifurcationSource` (`def_3_4`),
--   `G.Anc` (`def_3_5`), and `G.hardInterventionOn` (`def_3_10`); each
--   of these depends on `[DecidableEq Node]` through the `Finset`-backed
--   membership and filter operations on `G.J ∪ G.V`, `G.E`, and `G.L`,
--   and through the `Membership Node (CDMG Node)` instance from
--   `def_3_2` driving the `v ∈ G` membership hypotheses below.
--   Stronger instances (`Fintype`, `LinearOrder`) are not needed at
--   the statement level and are deferred to the proof body's use
--   sites.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in this folder (`HardInterventionOn.lean`,
--   `AcyclicPreservedUnderDo.lean`, `HardInterventionsCommute.lean`)
--   and in the upstream `Section3_1/` files.  The two-dash marker is
--   reserved for declarations whose body is the formalised LN content
--   of the row; this `variable` line is statement-typing
--   infrastructure binding the implicit `Node` type and its
--   `DecidableEq` instance that the theorem's signature references.
-- claim_3_5 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_5 --- end helper

-- ## Private helpers — `HardInterventionOn` walk-lift infrastructure
--
-- Subtask 1 of the proof of `claim_3_5` builds the `G_{do(W)} → G`
-- walk-lift infrastructure that the (⇐) direction of the proof uses
-- to upgrade the minimum-length directed walks `q_v : Walk
-- (G.hardInterventionOn {w} _) c v` and `q_w : Walk
-- (G.hardInterventionOn {v} _) c w` to walks in the ambient CDMG `G`
-- before assembling them into a candidate bifurcation walk.
--
-- The first five helpers below mirror `claim_3_3`'s
-- `AcyclicPreservedUnderDo.lean` lines 104–177 verbatim; the sixth,
-- `Walk.vertices_liftFromHardIntervention`, is new infrastructure
-- needed for the (⇐) direction's clause~(a) end-node-uniqueness
-- bookkeeping in step 5 of the TeX proof (the lift preserves the
-- underlying vertex list because each `cons` cell keeps its vertex
-- data verbatim).
--
-- ## Design choice
--
-- *Localised verbatim copy rather than cross-file `import`.*  The
--   sibling `AcyclicPreservedUnderDo.lean` already declares these
--   five lemmas `private`, so they are not accessible from this
--   file.  Re-declaring `private` here matches the explicit
--   workspace plan instruction ("the previous private mirrors are
--   TEMPLATES, not imports") and the chapter precedent of localising
--   walk-level plumbing to the consuming row.  A future chapter-wide
--   refactor can hoist these into `Walks.lean`; until then, the
--   local copy keeps the consuming file self-contained.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: mem_of_mem_hardInterventionOn
/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V`: every node of the intervened
CDMG is a node of `G`.  Consumes `hW : W ⊆ G.J ∪ G.V` to fold the
`W`-half of the left disjunct into `G.J ∪ G.V`.  Verbatim copy of
`AcyclicPreservedUnderDo.lean`'s lemma of the same name; localised
here because the sibling copy is `private`. -/
private lemma mem_of_mem_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} {v : Node}
    (h : v ∈ G.hardInterventionOn W hW) : v ∈ G := by
  -- `v ∈ G.hardInterventionOn W hW` reduces by the `Membership`
  -- instance from `def_3_2` to `v ∈ (G.J ∪ W) ∪ (G.V \ W)`.
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJW | hVW
  · rcases Finset.mem_union.mp hJW with hJ | hWmem
    · exact Finset.mem_union_left _ hJ
    · exact hW hWmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1
-- REFACTOR-BLOCK-ORIGINAL-END: mem_of_mem_hardInterventionOn

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.liftWalkStep_of_hardInterventionOn
/-- Per-edge content of the (⇐) direction's walk lift: any walk-step
in `G.hardInterventionOn W hW` is also a walk-step in `G`.  Both
`E_{do(W)} ⊆ E` and `L_{do(W)} ⊆ L` follow from `Finset.filter_subset`,
applied pointwise.  Verbatim copy of `AcyclicPreservedUnderDo.lean`'s
lemma of the same name. -/
private lemma Walk.liftWalkStep_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {u v : Node} {a : Node × Node}
    (h : (G.hardInterventionOn W hW).WalkStep u a v) :
    G.WalkStep u a v := by
  rcases h with ⟨ha, hELor⟩ | ⟨ha, hE⟩
  · refine Or.inl ⟨ha, ?_⟩
    rcases hELor with hE | hL
    · exact Or.inl (Finset.mem_filter.mp hE).1
    · exact Or.inr (Finset.mem_filter.mp hL).1
  · exact Or.inr ⟨ha, (Finset.mem_filter.mp hE).1⟩
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.liftWalkStep_of_hardInterventionOn

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.liftFromHardIntervention
/-- The walk-lift, as a recursive function on `Walk`s: a walk in the
intervened CDMG `G.hardInterventionOn W hW` is *the same tuple*
viewed as a walk in `G`.  Each `cons` cell keeps its vertex `v` and
its edge `a`; only the `WalkStep` witness is replaced by its lift
through `Walk.liftWalkStep_of_hardInterventionOn`. -/
private def Walk.liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}, Walk (G.hardInterventionOn W hW) u v → Walk G u v
  | _, _, .nil w hw =>
      Walk.nil w (mem_of_mem_hardInterventionOn hw)
  | _, _, .cons vMid a h p =>
      Walk.cons vMid a
        (Walk.liftWalkStep_of_hardInterventionOn h)
        (Walk.liftFromHardIntervention p)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.liftFromHardIntervention

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isDirectedWalk_liftFromHardIntervention
/-- The walk-lift preserves `IsDirectedWalk`: the per-edge constraint
`a = (u, v) ∧ a ∈ G.E` from `def_3_4` item ii survives the lift
because `(G.hardInterventionOn W hW).E ⊆ G.E` by
`Finset.mem_filter`. -/
private lemma Walk.isDirectedWalk_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk →
        (Walk.liftFromHardIntervention (hW := hW) p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ _ _ p, hp => by
      obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp
      refine ⟨ha_eq, (Finset.mem_filter.mp ha_E).1, ?_⟩
      exact isDirectedWalk_liftFromHardIntervention p hp_dir
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isDirectedWalk_liftFromHardIntervention

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_liftFromHardIntervention
/-- The walk-lift preserves `length`: each `cons` cell of the input
walk produces exactly one `cons` cell of the output walk, with the
same vertex / edge data. -/
private lemma Walk.length_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.liftFromHardIntervention (hW := hW) p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p =>
      congrArg (· + 1) (length_liftFromHardIntervention p)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_liftFromHardIntervention

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_liftFromHardIntervention
/-- **New (subtask 1 of `claim_3_5`):** the walk-lift preserves the
underlying `vertices` list.  Each `cons` cell of the input keeps its
vertex data verbatim under the lift, so the induced list of vertices
is byte-identical.  The `nil` case reduces to `[v] = [v]` definitionally;
the `cons` case is `u :: (lift p).vertices = u :: p.vertices` via
`congrArg (u :: ·) ih`.  Used by the (⇐) direction's clause~(a) /
clause~(e) end-node-uniqueness bookkeeping when lifting the minimum-
length directed arms `q_v`, `q_w` back to `G`. -/
private lemma Walk.vertices_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.liftFromHardIntervention (hW := hW) p).vertices = p.vertices
  | _, _, .nil _ _ => rfl
  | u, _, .cons _ _ _ p =>
      congrArg (u :: ·) (vertices_liftFromHardIntervention p)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_liftFromHardIntervention

-- ## Private helpers — `Walk` concatenation infrastructure
--
-- Subtask 2 of the proof of `claim_3_5` builds the `Walk.comp`
-- concatenation primitive that the (⇐) direction of the proof uses to
-- assemble the candidate bifurcation walk from its two arms.  The
-- first three helpers below mirror `claim_3_2`'s
-- `AcyclicIffTopologicalOrder.lean` lines 96–116 verbatim; the fourth,
-- `Walk.vertices_comp`, is new infrastructure needed for the (⇐)
-- direction's clause~(a) end-node-uniqueness bookkeeping in step 5 of
-- the TeX proof (the concatenated walk's vertex list factors as
-- `p.vertices.dropLast ++ q.vertices`).  An auxiliary
-- `Walk.vertices_ne_nil` lemma is added to discharge the
-- `List.dropLast_cons_of_ne_nil` side condition in the `cons` case.
--
-- ## Design choice
--
-- *Localised verbatim copy rather than cross-file `import`.*  The
--   sibling `AcyclicIffTopologicalOrder.lean` already declares these
--   three lemmas `private`, so they are not accessible from this file.
--   Re-declaring `private` here matches the chapter precedent of
--   localising walk-level plumbing to the consuming row (same
--   rationale as for the `liftFromHardIntervention` cluster in subtask
--   1).  A future chapter-wide refactor can hoist these into
--   `Walks.lean`; until then, the local copy keeps the consuming file
--   self-contained.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.comp
/-- Concatenate two walks `p : Walk G u v` and `q : Walk G v w` into a
walk `Walk G u w`.  The `nil` case forwards `q` unchanged; the `cons`
case recurses on the tail and re-attaches the head edge.  Verbatim copy
of `AcyclicIffTopologicalOrder.lean`'s `private Walk.comp`; re-declared
locally because the sibling copy is `private`. -/
private def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v a h p, q => .cons v a h (p.comp q)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.comp

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_comp
/-- `Walk.comp` is additive on lengths: the number of edges of the
concatenation equals the sum of the two arms' edge counts.  Verbatim
copy of the same-named `private` lemma in
`AcyclicIffTopologicalOrder.lean`. -/
private lemma Walk.length_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).length = p.length + q.length
  | _, _, _, .nil _ _, q => by
      simp [Walk.comp, Walk.length]
  | _, _, _, .cons _ _ _ p, q => by
      simp [Walk.comp, Walk.length, Walk.length_comp p q,
            Nat.add_comm, Nat.add_left_comm]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_comp

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isDirectedWalk_comp
/-- `Walk.comp` preserves `IsDirectedWalk` when both arms are directed:
the per-edge `def_3_4` item~ii constraint `a = (u, v) ∧ a ∈ G.E` is
preserved cell-by-cell along the recursion.  Verbatim copy of the
same-named `private` lemma in `AcyclicIffTopologicalOrder.lean`. -/
private lemma Walk.isDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsDirectedWalk → q.IsDirectedWalk → (p.comp q).IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ _ _ p, q, hp, hq => by
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨h1, h2, Walk.isDirectedWalk_comp p q h3 hq⟩
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isDirectedWalk_comp

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_ne_nil
/-- Auxiliary: every walk's `vertices` list is non-empty.  The `nil`
walk gives `[v]`; every `cons` cell prepends a new head vertex.  Needed
by `Walk.vertices_comp`'s `cons` case to discharge the side condition
of `List.dropLast_cons_of_ne_nil`. -/
private lemma Walk.vertices_ne_nil {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ _ => by simp [Walk.vertices]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_ne_nil

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_comp
/-- **New (subtask 2 of `claim_3_5`):** `Walk.comp` interacts with
`vertices` by dropping the last vertex of the left arm and
concatenating with the full vertex list of the right arm.  This is the
load-bearing bookkeeping lemma for the (⇐) direction: the candidate
bifurcation walk built from `(reverse q_v).comp q_w` has vertex list
`(reverse q_v).vertices.dropLast ++ q_w.vertices`, and end-node /
interior-membership conditions like `v ∉ p.vertices.tail` or
`v ∈ p.vertices` reduce to per-arm membership statements via this
equation.

The `nil` case closes by `rfl`: `[v].dropLast = []` and `[] ++ _ = _`
are both definitionally true.  The `cons` case applies the inductive
hypothesis and uses `List.dropLast_cons_of_ne_nil
(Walk.vertices_ne_nil p)` to unfold `(u :: p.vertices).dropLast`. -/
private lemma Walk.vertices_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).vertices = p.vertices.dropLast ++ q.vertices
  | _, _, _, .nil _ _, _ => rfl
  | _, _, _, .cons _ _ _ p, q => by
      have hne : p.vertices ≠ [] := Walk.vertices_ne_nil p
      simp [Walk.comp, Walk.vertices, Walk.vertices_comp p q,
            List.dropLast_cons_of_ne_nil hne]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_comp

-- ## Private helpers — `G → G_{do(W)}` walk-lift infrastructure
--
-- Subtask 3 of the proof of `claim_3_5` builds the reverse-direction
-- walk-lift infrastructure that the (⇒) direction of the proof uses
-- to transport the directed bifurcation arms `qL : Walk G c v` and
-- `qR : Walk G c w` from the ambient CDMG `G` to the intervened CDMGs
-- `G.hardInterventionOn {w} _` / `G.hardInterventionOn {v} _` after
-- verifying that no internal vertex of each arm coincides with the
-- opposite end-node (via the bifurcation walk's clause~(a)
-- end-node-uniqueness).
--
-- The three load-bearing declarations are:
--
-- * `Walk.vertices_directed_avoid_of_hardInterventionOn` — every
--   directed walk in `G.hardInterventionOn W hW` automatically avoids
--   `W` on all non-source positions, because `def_3_10` item iii
--   deletes every edge whose head is in `W` (the `e.2 ∉ W` clause of
--   the `Finset.filter`).  Mirror of the dual fact used by subtask 1's
--   `liftFromHardIntervention` direction, but read off the *intervened*
--   walks rather than the *ambient* ones.
--
-- * `Walk.liftTo_hardInterventionOn` — the converse of subtask 1's
--   `Walk.liftFromHardIntervention`.  Given a directed walk in `G`
--   whose source belongs to the intervention and whose non-source
--   vertices avoid `W`, rebuild the walk cell-by-cell in
--   `G.hardInterventionOn W hW`, witnessing each `cons` step's edge
--   via `Finset.mem_filter.mpr`-style packaging of the `e.2 ∉ W`
--   clause.
--
-- * `Walk.isDirectedWalk_liftTo_hardInterventionOn` — the lift
--   preserves `IsDirectedWalk`.  Each `cons` step retains the
--   `a = (u, v) ∧ a ∈ G.E` constraints of `def_3_4` item ii, with
--   the second conjunct upgraded through the filter membership.
--
-- Two small auxiliaries support the recursion:
-- `Walk.head_mem_vertices` (the source of a walk lies in its vertex
-- list, used to extract `vMid ∉ W` from the cons-walk's tail-avoidance
-- hypothesis) and `Walk.vertices_eq_head_cons_tail` (every walk's
-- vertex list factors as `source :: tail`, used to split `x ∈ p.vertices`
-- into "x equals the source" / "x lies in the strict tail" branches).
--
-- ## Design choice
--
-- *Source-membership hypothesis `hu : u ∈ G.hardInterventionOn W hW`
--   as an explicit argument.*  The `Walk.nil` base case has no edge
--   from which to recover the source's `J ∪ V`-membership in the
--   intervened CDMG (in subtask 1's reverse direction this is solved
--   by `mem_of_mem_hardInterventionOn` extracting `G`-membership from
--   `G_{do(W)}`-membership via a subset relation; we go the other
--   direction here, and the source's `J ∪ V`-membership is precisely
--   what the `nil` constructor needs).  For `n ≥ 1`, each cons cell
--   propagates the new source's membership through the directed-walk
--   constraint `a ∈ G.E` (`G.hE_subset` extracts `a.2 ∈ G.V` from
--   this) plus the avoidance hypothesis (`a.2 ∉ W` puts `a.2` in the
--   `G.V ∖ W` right-disjunct of the intervention's `J ∪ V` carrier),
--   so no further input is needed downstream.
--
-- *Avoidance hypothesis on `.vertices.tail`, not the full
--   `.vertices`.*  The source `u = u_0` is unconstrained — the LN's
--   "$\Anc^{G_{\doit(w)}}(v) \sm \{v\}$" reading places no restriction
--   on `v` itself, only on its strict ancestors.  Only the *heads* of
--   the edges (positions `1, 2, …, n` of `vertices`) must avoid `W`,
--   because `(u_i, u_{i+1}) ∈ E_{do(W)}` forces `u_{i+1} ∉ W` via the
--   `filter`-clause of `def_3_10` item iii.  The `.tail` carve-out is
--   the load-bearing book-keeping that lets the (⇒) direction's
--   `mkBifurcation`-based candidate walk reuse the LN's
--   `Anc^{G_{do(w)}}` ancestor sets verbatim.
--
-- *`isDirectedWalk_liftTo_hardInterventionOn` re-derives the
--   intermediate values used inside `liftTo_hardInterventionOn`'s
--   cons-case recursive call.*  The cons-case RHS of
--   `liftTo_hardInterventionOn` computes specific proof terms
--   (`hvMid_inHard`, `hp'_avoid`) inside its body and threads them
--   into the recursive call; the IH of the directedness lemma must
--   unify with that recursive call, so the lemma's proof reproduces
--   those `have`-bindings verbatim.  Proof-irrelevance bridges any
--   syntactic differences in how the proofs are written, but
--   reproducing the bindings keeps the unification local and robust.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.head_mem_vertices
/-- Auxiliary: the source `u` of a walk `p : Walk G u v` is the head of
`p.vertices`, hence lies in `p.vertices`.  The `nil` case unfolds to
`u ∈ [u]`; the `cons` case unfolds to `u ∈ u :: rest`; both close by
`simp [Walk.vertices]`.  Used by `liftTo_hardInterventionOn`'s `cons`
recursion to extract `vMid ∉ W` from the cons-walk's `vertices.tail`-
avoidance hypothesis (the cons-walk's `.vertices.tail` definitionally
equals `p'.vertices`, whose head is `vMid`). -/
private lemma Walk.head_mem_vertices {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), u ∈ p.vertices
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ _ => by simp [Walk.vertices]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.head_mem_vertices

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_eq_head_cons_tail
/-- Auxiliary: every walk's vertex list factors as `source :: tail`.
The `nil` case: `[u].tail = []` and `u :: [] = [u]`, so the equality is
definitional.  The `cons` case: `(u :: p'.vertices).tail = p'.vertices`,
so `u :: ((cons _ _ _ p').vertices.tail) = u :: p'.vertices = (cons _ _ _ p').vertices`,
again definitional.  Used by `vertices_directed_avoid_of_hardInterventionOn`'s
`cons` case to split `x ∈ p'.vertices` into "x equals the source vertex
`vMid`" / "x lies in `p'.vertices.tail`" via `List.mem_cons`. -/
private lemma Walk.vertices_eq_head_cons_tail {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices = u :: p.vertices.tail
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ _ => rfl
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_eq_head_cons_tail

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_directed_avoid_of_hardInterventionOn
/-- **Subtask 3a:** every vertex of a *directed* walk in
`G.hardInterventionOn W hW`, except the source, avoids `W`.

The `.tail` carve-out is load-bearing: the source `u = u_0` is
unconstrained — it may or may not be in `W`.  Only the heads of the
edges (positions `1, 2, …, n` of `vertices`) must avoid `W`, because
`(u_i, u_{i+1}) ∈ E_{do(W)}` forces `u_{i+1} ∉ W` via the `e.2 ∉ W`
clause of `def_3_10` item iii's `Finset.filter`.

Proof: induction on `p`.  The `nil` case is vacuous
(`(.nil v _).vertices.tail = []`).  The `cons` case obtains
`a ∈ (G.hardInterventionOn W hW).E` from the `IsDirectedWalk`
conjunct, extracts `vMid ∉ W` via `Finset.mem_filter.mp` and the
`ha_eq : a = (u, vMid)` head identification, then splits the membership
`x ∈ p'.vertices` into "x = vMid" (closed by the just-extracted
`vMid ∉ W`) and "x ∈ p'.vertices.tail" (closed by the IH applied to
`p'` and its directedness hypothesis). -/
private lemma Walk.vertices_directed_avoid_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk → ∀ x ∈ p.vertices.tail, x ∉ W
  | _, _, .nil _ _, _, _, hx => by simp [Walk.vertices] at hx
  | _, _, .cons vMid a _ p', hp_dir, x, hx => by
      change x ∈ p'.vertices at hx
      obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir
      have hvMid_notW : vMid ∉ W := by
        have hh := (Finset.mem_filter.mp ha_E).2
        rw [ha_eq] at hh
        exact hh
      rw [Walk.vertices_eq_head_cons_tail p'] at hx
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · exact hvMid_notW
      · exact Walk.vertices_directed_avoid_of_hardInterventionOn p'
          hp'_dir x hx_tail
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_directed_avoid_of_hardInterventionOn

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.liftTo_hardInterventionOn
/-- **Subtask 3b:** rebuild a directed walk `p : Walk G u v` in the
intervened CDMG `G.hardInterventionOn W hW`, provided the source `u`
is itself a node of the intervention and every non-source vertex of
`p` avoids `W`.

Cell-by-cell: each `cons` step's `WalkStep` witness is built from the
`def_3_4`-item-ii data `a = (u, vMid) ∧ a ∈ G.E` (extracted from
`hp_dir`) together with `vMid ∉ W` (extracted from `hp_avoid` applied
to the head of the tail walk's vertex list, via
`Walk.head_mem_vertices`).  The recursive call's source-membership
hypothesis `hvMid_inHard` is re-derived in the `cons` case from
`G.hE_subset` applied to `a ∈ G.E` (giving `a.2 ∈ G.V`, hence
`vMid ∈ G.V`) and `vMid ∉ W` (placing `vMid` in the `G.V ∖ W`
right-disjunct of the intervention's `J ∪ V` carrier). -/
private def Walk.liftTo_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk G u v),
      u ∈ G.hardInterventionOn W hW →
      p.IsDirectedWalk →
      (∀ x ∈ p.vertices.tail, x ∉ W) →
      Walk (G.hardInterventionOn W hW) u v
  | _, _, .nil v _, hu, _, _ => Walk.nil v hu
  | u, _, .cons vMid a _ p', _, hp_dir, hp_avoid =>
      have hvMid_notW : vMid ∉ W :=
        hp_avoid vMid (Walk.head_mem_vertices p')
      have hvMid_V : vMid ∈ G.V := by
        have hh := (G.hE_subset hp_dir.2.1).2
        rw [hp_dir.1] at hh
        exact hh
      have hvMid_inHard : vMid ∈ G.hardInterventionOn W hW := by
        change vMid ∈ (G.J ∪ W) ∪ (G.V \ W)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvMid_V, hvMid_notW⟩)
      have hStepNew : (G.hardInterventionOn W hW).WalkStep u a vMid := by
        refine Or.inl ⟨hp_dir.1, Or.inl ?_⟩
        refine Finset.mem_filter.mpr ⟨hp_dir.2.1, ?_⟩
        rw [hp_dir.1]
        exact hvMid_notW
      have hp'_avoid : ∀ x ∈ p'.vertices.tail, x ∉ W := fun y hy =>
        hp_avoid y (List.mem_of_mem_tail hy)
      Walk.cons vMid a hStepNew
        (Walk.liftTo_hardInterventionOn p' hvMid_inHard hp_dir.2.2 hp'_avoid)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.liftTo_hardInterventionOn

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isDirectedWalk_liftTo_hardInterventionOn
/-- **Subtask 3c:** the `liftTo_hardInterventionOn` lift preserves
`IsDirectedWalk`.

The `nil` case is `trivial` (`(Walk.nil v _).IsDirectedWalk = True`).
The `cons` case reduces by the equation compiler to
`(Walk.cons vMid a hStepNew (p'.liftTo_hardInterventionOn …)).IsDirectedWalk`,
which by the `cons` clause of `IsDirectedWalk` decomposes as the
conjunction of (a) `a = (u, vMid)` from `hp_dir`, (b)
`a ∈ (G.hardInterventionOn W hW).E` from `Finset.mem_filter.mpr`
packaging of `hp_dir.2.1` and the head-avoidance `vMid ∉ W`, and (c)
`(p'.liftTo…).IsDirectedWalk` from the IH applied to `p'` and the
re-derived recursive-call hypotheses. -/
private lemma Walk.isDirectedWalk_liftTo_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk G u v) (hu : u ∈ G.hardInterventionOn W hW)
      (hp_dir : p.IsDirectedWalk)
      (hp_avoid : ∀ x ∈ p.vertices.tail, x ∉ W),
      (Walk.liftTo_hardInterventionOn (hW := hW) p hu hp_dir hp_avoid).IsDirectedWalk
  | _, _, .nil _ _, _, _, _ => trivial
  | _, _, .cons vMid a _ p', _, hp_dir, hp_avoid => by
      have hvMid_notW : vMid ∉ W :=
        hp_avoid vMid (Walk.head_mem_vertices p')
      have hvMid_V : vMid ∈ G.V := by
        have hh := (G.hE_subset hp_dir.2.1).2
        rw [hp_dir.1] at hh
        exact hh
      have hvMid_inHard : vMid ∈ G.hardInterventionOn W hW := by
        change vMid ∈ (G.J ∪ W) ∪ (G.V \ W)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvMid_V, hvMid_notW⟩)
      have hp'_avoid : ∀ x ∈ p'.vertices.tail, x ∉ W := fun y hy =>
        hp_avoid y (List.mem_of_mem_tail hy)
      refine ⟨hp_dir.1, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨hp_dir.2.1, ?_⟩
        rw [hp_dir.1]
        exact hvMid_notW
      · exact Walk.isDirectedWalk_liftTo_hardInterventionOn p'
          hvMid_inHard hp_dir.2.2 hp'_avoid
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isDirectedWalk_liftTo_hardInterventionOn

-- ## Private helpers — `Walk.truncateAtFirst` + minimum-length walk
--
-- Subtask 4 of the proof of `claim_3_5` builds the truncation /
-- minimum-length-walk infrastructure that the (⇐) direction of the
-- proof uses to upgrade an arbitrary directed walk from `c` to `v`
-- into a *minimum-length* one whose target vertex `v` does not appear
-- inside its `vertices.dropLast`.  Concretely:
--
-- * `Walk.truncateAtFirst p t h` truncates a walk `p : Walk G u v`
--   at the *first* occurrence of `t` in `p.vertices`, returning a
--   `Σ' (v' : Node), Walk G u v'` whose target `v'` equals `t`
--   (Shape A; the equality is exposed as
--   `Walk.truncateAtFirst_target_eq`).
-- * `Walk.length_truncateAtFirst_le` and
--   `Walk.isDirectedWalk_truncateAtFirst` carry length / directedness
--   through the truncation.
-- * `Walk.length_truncateAtFirst_lt_of_mem_dropLast` is the
--   load-bearing strict-inequality: when `t` appears in
--   `p.vertices.dropLast` (i.e.\ at any non-terminal position), the
--   truncation drops at least one cell, so its length is strictly
--   smaller than `p.length`.
-- * `exists_directed_walk_v_not_in_dropLast` uses `Nat.find` to pick
--   a *minimum-length* directed walk from `c` to `v`; its minimality
--   then forces `v ∉ p.vertices.dropLast` (otherwise, truncating at
--   `v`'s first occurrence would yield a strictly shorter directed
--   walk from `c` to `v`, contradicting `Nat.find_min`).
--
-- Step 1 of the (⇐) direction of the TeX proof exhibits a *minimum-
-- length* directed walk `q_v : Walk (G.hardInterventionOn {w} _) c v`
-- and uses its minimality to argue that `v` does not appear in
-- `q_v.vertices.dropLast` (Step 3.2 of the TeX proof; analogously for
-- `q_w`).  This package translates that argument into Lean once and
-- for all, decoupling the "minimum length" extraction from the
-- consuming proof.
--
-- ## Design choice
--
-- *Shape A (`Σ' (v' : Node), Walk G u v'`) rather than Shape B
--   (`Walk G u t`).*  Shape B would tie the truncated walk's target
--   index to `t` at the type level, eliminating the
--   `Walk.truncateAtFirst_target_eq` bookkeeping at consumer sites
--   but forcing an `Eq.rec` / `subst`-style cast in the `nil` arm of
--   the recursion and in the `t = u` branch of the `cons` arm (both
--   produce a `Walk.nil _ _` whose type indices need re-indexing).
--   The cast pollutes the equation lemmas Lean auto-generates for
--   the function, breaking `simp`-based reductions in the
--   `length_truncateAtFirst_le` / `isDirectedWalk_truncateAtFirst`
--   proofs.  Shape A keeps the function body cast-free and relies on
--   `Walk.truncateAtFirst_target_eq` plus a single `subst h_target`
--   step at the consumer (`exists_directed_walk_v_not_in_dropLast`)
--   to recover the `Walk G c v` shape — net less bookkeeping.
--
-- *Per-`WalkStep` source-membership helper `WalkStep.source_mem`.*
--   The `t = u` branch of the `cons` arm needs `Walk.nil u h_u_in_G`
--   for the truncated walk, but the `cons`-pattern data does not
--   carry `u ∈ G` directly (only `Walk.nil` has that field — see
--   `Walks.lean`'s design block on the `nil`/`cons` membership-
--   witness asymmetry).  We extract it from `hStep : G.WalkStep u a
--   vMid`: a `WalkStep` is either a forward `E`-edge, a forward
--   `L`-edge, or a backward `E`-edge, and in all three cases `u`'s
--   membership in `G.J ∪ G.V` follows from `G.hE_subset` /
--   `G.hL_subset`.  Factoring this out into one lemma keeps the
--   `truncateAtFirst` body terse.
--
-- *`Nat.find` over a (classically) decidable existential, not
--   `Classical.byContradiction` + size-induction.*  The (⇐) direction
--   needs *minimum length*, not just any walk.  `Nat.find` with
--   `Classical.dec` (auto-instantiated via `classical`) over the
--   predicate "there exists a directed walk from `c` to `v` of length
--   `n`" gives the cleanest minimum extraction.  An alternative
--   `Classical.choose` + `WellFounded.min` approach was rejected as
--   more verbose; `Nat.find_spec` and `Nat.find_min` package the
--   exact two pieces we need (the witness at the minimum and the
--   contradiction with any smaller walk).
--
-- *`exists_directed_walk_v_not_in_dropLast` takes `c ≠ v` as a
--   hypothesis even though `Anc`'s body admits the trivial length-0
--   walk `Walk.nil c hc` (giving `c ∈ G.Anc c` unconditionally).*
--   The dropLast clause `v ∉ p.vertices.dropLast` is vacuous when
--   `p` is the trivial walk (`p.vertices.dropLast = []` for
--   `p = Walk.nil c _` when `c = v`), so technically the lemma is
--   true even without `hcv`.  We carry `hcv` because the (⇐)
--   direction's consumer always has `c ≠ v` available (from the LN's
--   `c ∈ Anc^{G_{do(w)}}(v) \ {v}` clause's `\ {v}` part) and the
--   hypothesis sharpens the lemma's statement: the produced walk has
--   length ≥ 1, so its `vertices.dropLast` is non-empty in an
--   informative way.  Downstream `mkBifurcation` constructions also
--   require length ≥ 1 to assemble the bifurcation's left arm.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: WalkStep.source_mem
/-- Auxiliary: the source vertex of a `WalkStep` lies in `G`.  Used by
`Walk.truncateAtFirst`'s `t = u` branch in the `cons` arm to recover
`u ∈ G` from `hStep : G.WalkStep u a vMid` — the `cons`-pattern data
does not carry `u ∈ G` directly (only `Walk.nil` has that field).
The proof case-splits `WalkStep` into its three disjuncts (forward
`E`, forward `L`, backward `E`) and reads off `u`'s membership from
the appropriate `G.hE_subset` / `G.hL_subset` projection. -/
private lemma WalkStep.source_mem {G : CDMG Node} {u v : Node}
    {a : Node × Node} (h : G.WalkStep u a v) : u ∈ G := by
  change u ∈ G.J ∪ G.V
  rcases h with ⟨ha_eq, ha_or⟩ | ⟨ha_eq, ha_E⟩
  · rcases ha_or with ha_E | ha_L
    · have h1 := (G.hE_subset ha_E).1
      rw [ha_eq] at h1
      exact h1
    · have h1 := (G.hL_subset ha_L).1
      rw [ha_eq] at h1
      exact Finset.mem_union_right _ h1
  · have h1 := (G.hE_subset ha_E).2
    rw [ha_eq] at h1
    exact Finset.mem_union_right _ h1
-- REFACTOR-BLOCK-ORIGINAL-END: WalkStep.source_mem

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.truncateAtFirst
/-- **Subtask 4a:** truncate `p : Walk G u v` at the *first* occurrence
of `t` in `p.vertices`, returning a `Σ' (v' : Node), Walk G u v'`
whose target `v'` equals `t` (the equality is the content of
`Walk.truncateAtFirst_target_eq` immediately below).

* `nil` arm: `p.vertices = [v]`, so `h : t ∈ [v]` forces `t = v`;
  the truncation is the trivial walk `⟨v, .nil v hv⟩`.  The Sigma
  fst is `v`, which equals `t` via `List.mem_singleton`.
* `cons` arm: `p = .cons vMid a hStep p'`, `p.vertices = u ::
  p'.vertices`.  Case-split on `t = u`:
    * If `t = u`: the *first* occurrence of `t` is at position 0 of
      `p.vertices`, so the truncated walk is `⟨u, .nil u _⟩`.  The
      needed `u ∈ G` is extracted from `hStep` via
      `WalkStep.source_mem`.
    * If `t ≠ u`: the first occurrence of `t` lies in
      `p'.vertices`; recurse on `p'` and re-prepend the head edge
      with `Walk.cons`.

Structural recursion terminates on the `cons` arm's `p'` (a strict
subterm of `.cons vMid a hStep p'`). -/
private def Walk.truncateAtFirst {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node) (_h : t ∈ p.vertices),
      Σ' (v' : Node), Walk G u v'
  | _, _, .nil w hw, _, _ => ⟨w, .nil w hw⟩
  | u, _, .cons vMid a hStep p', t, h =>
      if h_eq : t = u then
        ⟨u, .nil u (WalkStep.source_mem hStep)⟩
      else
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        let res := Walk.truncateAtFirst p' t h_in_p'
        ⟨res.1, .cons vMid a hStep res.2⟩
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.truncateAtFirst

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.truncateAtFirst_target_eq
/-- **Subtask 4b:** the truncated walk's target (`Σ'.fst`) equals `t`.
This is the Shape-A bookkeeping that consumers use to convert the
`Walk G u (truncate p t h).1` into a `Walk G u t` (via `subst` on the
fst-equality).  Proved by structural recursion mirroring
`Walk.truncateAtFirst`'s shape:

* `nil` arm: the fst is `w` (the trivial walk's source), and
  `t = w` follows from `h : t ∈ [w]` via `List.mem_singleton`.
* `cons` arm: case-split on `t = u`.  If `t = u`, fst is `u = t`;
  if `t ≠ u`, fst is `(truncate p' t _).1`, which equals `t` by
  the inductive hypothesis. -/
private lemma Walk.truncateAtFirst_target_eq {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node) (h : t ∈ p.vertices),
      (Walk.truncateAtFirst p t h).1 = t
  | _, _, .nil _ _, _, h => (List.mem_singleton.mp h).symm
  | u, _, .cons _ _ _ p', t, h => by
      simp only [Walk.truncateAtFirst]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        exact h_eq.symm
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        exact Walk.truncateAtFirst_target_eq p' t h_in_p'
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.truncateAtFirst_target_eq

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_truncateAtFirst_le
/-- **Subtask 4c:** the truncated walk's length is bounded by the
original walk's length.  Both endpoints (`≤`) are attained: a `nil`
input gives a `nil` output of the same length 0; a `cons` input whose
truncation does not drop any cell (only possible when `t` equals the
walk's final vertex and never appears earlier) yields equality.  The
strict-inequality version
`Walk.length_truncateAtFirst_lt_of_mem_dropLast` strengthens this
under the `t ∈ p.vertices.dropLast` hypothesis. -/
private lemma Walk.length_truncateAtFirst_le {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node) (h : t ∈ p.vertices),
      (Walk.truncateAtFirst p t h).2.length ≤ p.length
  | _, _, .nil _ _, _, _ => by
      simp only [Walk.truncateAtFirst, Walk.length, le_refl]
  | u, _, .cons _ _ _ p', t, h => by
      simp only [Walk.truncateAtFirst, Walk.length]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        simp [Walk.length]
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        have ih := Walk.length_truncateAtFirst_le p' t h_in_p'
        change (Walk.truncateAtFirst p' t h_in_p').2.length + 1 ≤ p'.length + 1
        omega
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_truncateAtFirst_le

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isDirectedWalk_truncateAtFirst
/-- **Subtask 4d:** the truncated walk inherits `IsDirectedWalk` from
the original walk.  The `nil` arm produces a `.nil` walk, which is
directed vacuously.  The `cons` arm's `t = u` branch also produces a
`.nil` (trivially directed); the `t ≠ u` branch re-prepends the head
edge `a = (u, vMid)` (extracted from `p.IsDirectedWalk`'s first
conjunct), with the `IsDirectedWalk` of the recursive tail provided by
the inductive hypothesis. -/
private lemma Walk.isDirectedWalk_truncateAtFirst {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node) (h : t ∈ p.vertices),
      p.IsDirectedWalk → (Walk.truncateAtFirst p t h).2.IsDirectedWalk
  | _, _, .nil _ _, _, _, _ => by
      simp only [Walk.truncateAtFirst]
      trivial
  | u, _, .cons _ _ _ p', t, h, hp_dir => by
      simp only [Walk.truncateAtFirst]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        trivial
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir
        refine ⟨ha_eq, ha_E, ?_⟩
        exact Walk.isDirectedWalk_truncateAtFirst p' t h_in_p' hp'_dir
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isDirectedWalk_truncateAtFirst

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.mem_vertices_of_mem_dropLast
/-- Auxiliary: every `t ∈ p.vertices.dropLast` automatically lies in
the full `p.vertices`.  Direct application of mathlib's
`List.mem_of_mem_dropLast`.  Used by
`Walk.length_truncateAtFirst_lt_of_mem_dropLast` and
`exists_directed_walk_v_not_in_dropLast` to feed a `dropLast`
membership into `Walk.truncateAtFirst`'s `p.vertices`-membership
hypothesis. -/
private lemma Walk.mem_vertices_of_mem_dropLast {G : CDMG Node}
    {u v : Node} {p : Walk G u v} {t : Node}
    (h : t ∈ p.vertices.dropLast) : t ∈ p.vertices :=
  List.mem_of_mem_dropLast h
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.mem_vertices_of_mem_dropLast

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_truncateAtFirst_lt_of_mem_dropLast
/-- **Subtask 4e:** the load-bearing *strict* inequality.  When `t`
appears in `p.vertices.dropLast` (i.e.\ at some non-terminal position
in the walk's vertex list), the truncation drops at least one `cons`
cell, so its length is strictly smaller than `p.length`.

The `nil` case is vacuous: `(.nil v _).vertices.dropLast = [].dropLast
= []`, so no `t` can satisfy the hypothesis.

The `cons` case unfolds `(u :: p'.vertices).dropLast = u ::
p'.vertices.dropLast` (using `Walk.vertices_ne_nil` from subtask 2)
and case-splits `t ∈ u :: p'.vertices.dropLast`:
* If `t = u`: truncation returns the trivial walk `⟨u, .nil u _⟩`
  of length 0, strictly less than the original `p.length ≥ 1` (since
  the cons walk has at least one edge).
* If `t ∈ p'.vertices.dropLast`: recurse on `p'` via the inductive
  hypothesis, getting `(truncate p' t _).2.length < p'.length`;
  adding 1 to both sides (the `cons` cell that the outer truncation
  re-prepends) gives `< p'.length + 1 = p.length`. -/
private lemma Walk.length_truncateAtFirst_lt_of_mem_dropLast {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node)
      (h_in_dropLast : t ∈ p.vertices.dropLast),
      (Walk.truncateAtFirst p t
          (Walk.mem_vertices_of_mem_dropLast h_in_dropLast)).2.length < p.length
  | _, _, .nil _ _, _, h => by
      -- (.nil _ _).vertices.dropLast = [_].dropLast = []
      simp [Walk.vertices] at h
  | u, _, .cons _ _ _ p', t, h_in_dropLast => by
      have hne : p'.vertices ≠ [] := Walk.vertices_ne_nil p'
      -- Unfold (cons …).vertices.dropLast = u :: p'.vertices.dropLast.
      change t ∈ (u :: p'.vertices).dropLast at h_in_dropLast
      rw [List.dropLast_cons_of_ne_nil hne] at h_in_dropLast
      -- h_in_dropLast : t ∈ u :: p'.vertices.dropLast.
      simp only [Walk.truncateAtFirst, Walk.length]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        simp [Walk.length]
      · rw [dif_neg h_eq]
        have h_in_p'_drop : t ∈ p'.vertices.dropLast := by
          rcases List.mem_cons.mp h_in_dropLast with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        have ih := Walk.length_truncateAtFirst_lt_of_mem_dropLast p' t h_in_p'_drop
        change (Walk.truncateAtFirst p' t _).2.length + 1 < p'.length + 1
        omega
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_truncateAtFirst_lt_of_mem_dropLast

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: exists_directed_walk_v_not_in_dropLast
/-- **Subtask 4f:** the (⇐) direction's load-bearing existence lemma.
Given any ancestor `c ∈ G.Anc v` with `c ≠ v`, there exists a
*minimum-length* directed walk from `c` to `v` whose target `v` does
not appear in its `vertices.dropLast` (i.e.\ `v` occurs *only* at the
walk's final position).

Proof strategy (per the design block above):

1.  Extract an initial directed walk `p₀ : Walk G c v` from `c ∈ G.Anc
    v` (`Anc`'s body unfolds to `c ∈ G ∧ ∃ p : Walk G c v,
    p.IsDirectedWalk`).
2.  Define `P n := ∃ p : Walk G c v, p.IsDirectedWalk ∧ p.length = n`.
    `p₀` shows `P p₀.length`, so the set `{n | P n}` is non-empty.
3.  Let `n₀ := Nat.find hP_nonempty`; `Nat.find_spec` gives a walk
    `p_min` of length `n₀` with `p_min.IsDirectedWalk`.
4.  Suppose `v ∈ p_min.vertices.dropLast` for contradiction.
    Truncate `p_min` at `v`'s first occurrence; by
    `Walk.length_truncateAtFirst_lt_of_mem_dropLast` the resulting
    walk has length strictly less than `p_min.length = n₀`.  The
    truncated walk's target equals `v` (by
    `Walk.truncateAtFirst_target_eq`), so after `subst`-ing the
    target equality we get a `Walk G c v` of length `< n₀` with
    `IsDirectedWalk` (by `Walk.isDirectedWalk_truncateAtFirst`).
    This contradicts `Nat.find_min`.

The `hcv : c ≠ v` hypothesis is not strictly needed (the dropLast
clause is vacuously true when the minimum-length walk is trivial
`Walk.nil c hc`, which only happens when `c = v`), but consumers
always have it available and it sharpens the produced walk's content
— see the design block above. -/
private lemma exists_directed_walk_v_not_in_dropLast
    {G : CDMG Node} {c v : Node}
    (hc_anc : c ∈ G.Anc v) (hcv : c ≠ v) :
    ∃ (p : Walk G c v), p.IsDirectedWalk ∧ v ∉ p.vertices.dropLast := by
  classical
  -- Step 1: extract initial walk from c ∈ Anc v.
  -- `Anc`'s body: `c ∈ G ∧ ∃ p : Walk G c v, p.IsDirectedWalk`.
  obtain ⟨_hc_in, p₀, hp₀_dir⟩ := hc_anc
  -- Step 2: predicate "exists directed c→v walk of length n", and witness.
  let P : ℕ → Prop :=
    fun n => ∃ (p : Walk G c v), p.IsDirectedWalk ∧ p.length = n
  have hP_nonempty : ∃ n, P n := ⟨p₀.length, p₀, hp₀_dir, rfl⟩
  -- Step 3: minimum length witness via Nat.find.
  obtain ⟨p_min, hp_min_dir, hp_min_len⟩ :
      P (Nat.find hP_nonempty) := Nat.find_spec hP_nonempty
  refine ⟨p_min, hp_min_dir, ?_⟩
  -- Step 4: contradiction with minimality.
  intro hv_drop
  -- Promote dropLast-membership to full vertices-membership.
  have h_v_in : v ∈ p_min.vertices :=
    Walk.mem_vertices_of_mem_dropLast hv_drop
  -- Bundle the truncation's outputs (target, directedness, length-lt)
  -- and `subst` the target equality to land at `Walk G c v`.
  obtain ⟨v', p_short, h_target, h_dir, h_lt⟩ :
      ∃ (v' : Node) (p_short : Walk G c v'),
        v' = v ∧ p_short.IsDirectedWalk ∧ p_short.length < p_min.length := by
    refine ⟨(Walk.truncateAtFirst p_min v h_v_in).1,
            (Walk.truncateAtFirst p_min v h_v_in).2, ?_, ?_, ?_⟩
    · exact Walk.truncateAtFirst_target_eq p_min v h_v_in
    · exact Walk.isDirectedWalk_truncateAtFirst p_min v h_v_in hp_min_dir
    · exact Walk.length_truncateAtFirst_lt_of_mem_dropLast p_min v hv_drop
  subst h_target
  -- p_short : Walk G c v; contradict Nat.find_min.
  have h_lt_n₀ : p_short.length < Nat.find hP_nonempty :=
    hp_min_len ▸ h_lt
  exact Nat.find_min hP_nonempty h_lt_n₀ ⟨p_short, h_dir, rfl⟩
-- REFACTOR-BLOCK-ORIGINAL-END: exists_directed_walk_v_not_in_dropLast

-- ## Private helpers — `Walk.reverseDirected` + `Walk.mkBifurcation`
--
-- Subtask 5 of the proof of `claim_3_5` builds the bifurcation-walk
-- *constructor* that the (⇐) direction of the proof uses to assemble
-- the candidate bifurcation walk from its two directed arms.  See the
-- workspace `Section3_2/workspace_claim_3_5.md` (lines 385–440) for the
-- subtask spec.
--
-- The TeX proof's Step 4 of (⇐) writes the candidate as
--   `p := (reverse q_v) ⌢ q_w  : Walk G v w`
-- where `reverse q_v` reads the left arm `q_v : Walk G c v` from `v`
-- back to `c` along the same edges traversed in reverse (each cell of
-- `reverse q_v` uses the *backward* `WalkStep` constructor, the
-- `Or.inr` disjunct of `WalkStep`'s definition).  The middle vertex
-- is the common source `c`; the split index of the bifurcation is
-- `k = q_v.length`; the source of the bifurcation is `c`.
--
-- The two-step factoring (per the workspace plan):
--
-- * `Walk.reverseDirected qv hqv_dir : Walk G v c` — auxiliary that
--   reverses a directed walk `qv : Walk G c v`.  Defined by
--   structural recursion on `qv`: the cons case appends the recursive
--   reverse to a length-1 backward-edge walk via subtask 2's
--   `Walk.comp`.
--
-- * `Walk.mkBifurcation qv hqv_dir hqv_pos qw : Walk G v w` — defined
--   as `(Walk.reverseDirected qv hqv_dir).comp qw`.  The
--   `hqv_pos : qv.length ≥ 1` hypothesis is carried through but is
--   not used by the definition itself; it is needed in subtask 6
--   (which realises `IsBifurcationDirectedHingeWithSplit` on the
--   produced walk) to exclude the trivial-left-arm case from the
--   bifurcation predicate.
--
-- Both `length` and `vertices` for `mkBifurcation` factor through
-- subtask 2's `length_comp` / `vertices_comp` plus this subtask's
-- `length_reverseDirected` / `vertices_reverseDirected`.
--
-- ## Design choice
--
-- *Two-step factoring (define `reverseDirected` first, then
--   `mkBifurcation` as a one-line composition).*  An alternative
--   would inline the reverse-and-concatenate in a single recursive
--   definition of `mkBifurcation`, recursing on `qv` from the front
--   and *prepending* a backward edge to a partially-built bifurcation
--   walk at each step.  But the partial walk's type indices change
--   as we peel forward cells (the source index migrates), which
--   forces awkward cast bookkeeping.  Factoring via `reverseDirected`
--   delegates the type-index dance to a cast-free structurally-
--   recursive function returning `Walk G v c` at every step, then
--   re-uses subtask 2's `Walk.comp` to attach `qw` at `c`.
--
-- *`reverseDirected`'s cons case uses `Walk.comp` to append a
--   length-1 backward-edge walk, rather than directly constructing
--   a single `Walk.cons` from the recursion.*  Our `Walk` inductive
--   (`Walks.lean:247`) only has `nil` and `cons` constructors and
--   `cons` only *prepends* an edge.  Recursing into `qv'` gives a
--   `Walk G v vMid`, and we need to append the backward edge
--   `vMid → c`.  Without a `snoc`-style constructor (or a custom
--   parallel recursion), the cleanest route is `Walk.comp` with a
--   length-1 walk on the right.  The length / vertices arithmetic
--   factors transparently through `length_comp` / `vertices_comp`,
--   so the cost is one extra `comp` application per `cons` cell.
--
-- *No standalone `isDirectedWalk_reverseDirected` lemma.*  The
--   reversed walk is *not* a directed walk in the standard
--   "forward edges only" sense (`IsDirectedWalk` requires every cell
--   to use the *forward* `WalkStep` disjunct
--   `a = (u, v) ∧ a ∈ G.E`).  Each cell of `reverseDirected qv` uses
--   the *backward* `WalkStep` disjunct (`Or.inr ⟨ha_eq, ha_E⟩`,
--   i.e.\ `a = (v, u) ∧ a ∈ G.E`).  The correct correctness property
--   is per-cell "every cell is backward", which has no clean named
--   predicate in `Walks.lean` and is subtask-6-specific (subtask 6
--   needs it inline when realising
--   `IsBifurcationDirectedHingeWithSplit` on `mkBifurcation`'s
--   output, where the left-arm `cons` clauses
--   `a = (v, u) ∧ a ∈ G.E ∧ p.IsBifurcationDirectedHingeWithSplit k`
--   match the backward `WalkStep` shape directly).  Per the
--   workspace plan's recommendation, we skip this standalone lemma
--   here and let subtask 6 build the per-cell fact directly.
--
-- *`hqv_pos : qv.length ≥ 1` is carried on `mkBifurcation` even
--   though the definition does not consume it.*  Subtask 6 needs
--   `qv.length ≥ 1` to (i) split the
--   `IsBifurcationDirectedHingeWithSplit` recursion at the hinge
--   (which is `qv`'s first cell traversed backward, present only
--   when `qv.length ≥ 1`) and (ii) exclude the `k = 0`
--   `cons _ _ _ (.nil _ _)` branch of
--   `IsBifurcationDirectedHingeWithSplit` (`Walks.lean:1044` returns
--   `False`).  Threading `hqv_pos` through `mkBifurcation`'s
--   signature keeps the downstream subtask 6 / 8 API uniform.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.reverseDirected
/-- **Subtask 5a:** reverse a *directed* walk `qv : Walk G c v` into a
walk `Walk G v c`.  Every cell of the result uses the *backward*
`WalkStep` disjunct (`Or.inr`), re-using the same edges as `qv`
traversed in reverse.

Structural recursion on `qv`:
* `nil` case (`qv = .nil w hw`, forcing `c = v = w`): return the
  trivial walk `Walk.nil w hw`.
* `cons` case (`qv = .cons vMid a hStep qv'`, with
  `qv' : Walk G vMid v` and
  `hqv_dir = ⟨a = (c, vMid), a ∈ G.E, qv'.IsDirectedWalk⟩`): recurse
  on `qv'` to get `qv'_rev : Walk G v vMid`; build a length-1
  backward-edge walk `Walk G vMid c` by
  `Walk.cons c a backStep (Walk.nil c h_c)`, where
  `backStep : G.WalkStep vMid a c` is `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩`
  (packaging the original edge `a = (c, vMid) ∈ G.E` into the
  *backward* `WalkStep` disjunct `a = (v, u) ∧ a ∈ G.E` with
  `(u, v) := (vMid, c)`); compose via subtask 2's `Walk.comp`. -/
private def Walk.reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v), qv.IsDirectedWalk → Walk G v c
  | _, _, .nil w hw, _ => Walk.nil w hw
  | c, _, .cons _ a hStep qv', hqv_dir =>
      (Walk.reverseDirected qv' hqv_dir.2.2).comp
        (Walk.cons c a (Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩)
          (Walk.nil c (WalkStep.source_mem hStep)))
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.reverseDirected

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_reverseDirected
/-- **Subtask 5b:** `reverseDirected` preserves length.  Each cell of
the input produces one cell in the recursion (length-summed via
`length_comp`) plus one cell in the length-1 backward-edge walk, so
the total length is `qv'.length + 1 = qv.length`. -/
private lemma Walk.length_reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).length = qv.length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ _ qv', hqv_dir => by
      change ((Walk.reverseDirected qv' hqv_dir.2.2).comp _).length
            = qv'.length + 1
      rw [Walk.length_comp, Walk.length_reverseDirected qv' hqv_dir.2.2]
      rfl
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_reverseDirected

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_reverseDirected
/-- **Subtask 5c:** `reverseDirected` reverses the vertex list.

The `nil` case is `rfl`: `[w].reverse = [w]` by definitional
reduction.

The `cons` case combines `vertices_comp` + IH + the head-of-walk fact
(`qv'.vertices = vMid :: qv'.vertices.tail` from subtask 3's
`vertices_eq_head_cons_tail`).  Concretely, after `vertices_comp` and
IH the goal is
  `qv'.vertices.reverse.dropLast ++ [vMid, c] = (c :: qv'.vertices).reverse`,
which equals
  `qv'.vertices.tail.reverse ++ [vMid, c] = qv'.vertices.tail.reverse ++ [vMid, c]`
after rewriting `qv'.vertices` to `vMid :: qv'.vertices.tail` on both
sides — closed by `simp [Walk.vertices, List.reverse_cons]`. -/
private lemma Walk.vertices_reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).vertices = qv.vertices.reverse
  | _, _, .nil _ _, _ => rfl
  | c, _, .cons vMid _ _ qv', hqv_dir => by
      have ih := Walk.vertices_reverseDirected qv' hqv_dir.2.2
      have h_head : qv'.vertices = vMid :: qv'.vertices.tail :=
        Walk.vertices_eq_head_cons_tail qv'
      change ((Walk.reverseDirected qv' hqv_dir.2.2).comp _).vertices
            = (c :: qv'.vertices).reverse
      rw [Walk.vertices_comp, ih]
      conv_lhs => rw [h_head]
      conv_rhs => rw [h_head]
      simp [Walk.vertices, List.reverse_cons]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_reverseDirected

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.mkBifurcation
/-- **Subtask 5d:** the bifurcation-walk constructor.  Given a directed
*left arm* `qv : Walk G c v` (`c → v`, length ≥ 1) and a *right arm*
`qw : Walk G c w` (`c → w`, no directedness constraint at this stage),
assemble the candidate bifurcation walk
`(reverse qv) ⌢ qw : Walk G v w` whose middle vertex is `c` (the
common source of the two arms).

The `hqv_pos` hypothesis is unused at the definition level but is
required downstream (subtask 6) to realise the LN's `1 ≤ k ≤ n`
interior-source constraint on the split index — see the design block
above. -/
private def Walk.mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (_hqv_pos : qv.length ≥ 1) (qw : Walk G c w) : Walk G v w :=
  (Walk.reverseDirected qv hqv_dir).comp qw
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.mkBifurcation

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_mkBifurcation
/-- **Subtask 5e:** the bifurcation walk's length is
`qv.length + qw.length`.  Direct from `length_comp` +
`length_reverseDirected`. -/
private lemma Walk.length_mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).length
      = qv.length + qw.length := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).length
        = qv.length + qw.length
  rw [Walk.length_comp, Walk.length_reverseDirected qv hqv_dir]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_mkBifurcation

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_mkBifurcation
/-- **Subtask 5f:** the bifurcation walk's vertex list is
`qv.vertices.reverse.dropLast ++ qw.vertices`.  Direct from
`vertices_comp` + `vertices_reverseDirected`.

This is the load-bearing splitting formula for the (⇐) direction's
clause~(a) end-node-uniqueness bookkeeping in Step 5 of the TeX
proof: the candidate bifurcation walk's vertex list factors as the
*reverse of the left arm without its source* (`qv.vertices.reverse.dropLast`,
i.e.\ `[v, …, vMid_1]` reading from `v` to the vertex just before
`c`) followed by the *full right arm* (`qw.vertices`, i.e.\
`[c, …, w]`).  The end-node constraints `v ≠ w`,
`v ∉ p.vertices.tail`, `w ∉ p.vertices.dropLast` then reduce to
per-arm vertex-membership statements via this equation. -/
private lemma Walk.vertices_mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
      = qv.vertices.reverse.dropLast ++ qw.vertices := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).vertices
        = qv.vertices.reverse.dropLast ++ qw.vertices
  rw [Walk.vertices_comp, Walk.vertices_reverseDirected qv hqv_dir]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_mkBifurcation

-- ## Private helpers — `mkBifurcation` realises the directed-hinge predicate
--
-- Subtask 6 of the proof of `claim_3_5` connects subtask 5's
-- `Walk.mkBifurcation` constructor to the
-- `Walk.IsBifurcationDirectedHingeWithSplit` predicate from
-- `Section3_1/Walks.lean:1042-1049`.  The (⇐) direction's Step 5
-- (TeX proof) needs all five clauses (a)–(e) of `def_3_4` item~vi to
-- hold on the constructed walk at index `k = qv.length - 1`; the
-- directed-hinge predicate covers clauses (b), (c), (d) — the
-- chained backward-`E` edges of the left arm followed by the
-- forward-`E` edges of the right arm, with a directed hinge at the
-- source vertex `c`.  Clauses (a) (end-node uniqueness) and (e)
-- (`1 ≤ k ≤ n - 1`) are handled separately by subtask 8 using
-- `vertices_mkBifurcation` from subtask 5.
--
-- Three helpers are added:
--
-- * `Walk.comp_assoc` — an auxiliary `(p.comp q).comp r = p.comp (q.comp r)`
--   that the inductive step of Helper 2 needs to re-associate the
--   factorisation `reverseDirected (cons _ _ _ qv') = (reverseDirected
--   qv').comp single-back-edge` with the trailing right-arm `qw`.
--   Mathlib's walk concatenation does provide a `comp_assoc`, but our
--   `Walk.comp` is a locally-`private` re-declaration (subtask 2),
--   so the associativity lemma is also localised here.
--
-- * `Walk.isBifurcationDirectedHinge_cons_backward_of_directed` —
--   the *base case* of the induction.  A single backward `E`-edge
--   `(v, u)` followed by a non-trivial directed walk `p : Walk G v w`
--   realises the directed-hinge predicate at index 0.  Discharges the
--   third clause of `IsBifurcationDirectedHingeWithSplit`'s recursion
--   (`u, _, .cons v a _ (p@(.cons _ _ _ _)), 0` returning
--   `a = (v, u) ∧ a ∈ G.E ∧ p.IsDirectedWalk`).  The `hp_nonempty`
--   hypothesis is *load-bearing*: without it, the predicate's second
--   clause (`cons _ _ _ (.nil _ _), 0` returning `False`) would fire
--   instead.  Downstream this corresponds to the `qw.length ≥ 1`
--   constraint that the (⇐) direction obtains from `c ≠ w`.
--
-- * `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux` —
--   the *parametrised inductive step*: prepending the
--   `reverseDirected qv` backward chain (of length `qv.length`) to
--   any walk `rest` that already realises the directed-hinge
--   predicate at index `k` shifts the index by `qv.length`.  This
--   parametrised formulation (with `rest` and `k` as extra arguments)
--   is necessary to make the structural induction on `qv` go through:
--   the natural induction is on `qv`'s *outermost* cons cell, but
--   `reverseDirected`'s definition places the new cell at the
--   *rightmost* position of the recursion (via the `comp` factoring
--   `(reverseDirected qv').comp single-back-edge`), so the IH must
--   re-associate the trailing chain through `Walk.comp_assoc` and
--   apply itself to the smaller `qv'` with an *enriched* `rest`
--   (the original `rest` prepended with one more backward edge).
--
-- * `Walk.isBifurcationDirectedHinge_mkBifurcation` — the
--   consumer-facing wrapper.  Combines the base case (Helper 1) with
--   the inductive auxiliary (Helper 2) by decomposing `qv` once and
--   applying the auxiliary to its tail `qv'`.
--
-- ## Design choice
--
-- *Parametrised auxiliary with `rest` + `k` arguments, rather than the
--   plan-sketch's `qw`-only form.*  The plan's sketch parametrises
--   only on `qv` and uses `qw` as the right arm directly, with
--   conclusion `IsBifurcationDirectedHingeWithSplit (qv.length - 1)`.
--   That signature does not have a workable IH: the natural induction
--   on `qv`'s outermost cons cell needs to thread an extra backward
--   edge into the `rest` walk, but the original signature's `rest = qw`
--   is fixed.  Generalising to `rest : Walk G c w` and arbitrary `k`
--   (with conclusion `IsBifurcationDirectedHingeWithSplit (qv.length
--   + k)`) makes the IH applicable to the strictly smaller `qv'` with
--   `rest' = cons c a backStep rest` and `k' = k + 1`.  The wrapper
--   (Helper 3) then instantiates `rest := qw`, `k := 0` and uses
--   Helper 1 to satisfy the `rest.IsBifurcationDirectedHingeWithSplit
--   0` precondition.
--
-- *`hqw_dir : qw.IsDirectedWalk` is required (not in the plan
--   sketch).*  The third clause of `IsBifurcationDirectedHingeWithSplit`
--   (the `cons _ _ _ (cons _), 0` case) requires `p.IsDirectedWalk`
--   on the tail, which becomes `qw.IsDirectedWalk` at the base case
--   of Helper 3.  The plan sketch omitted this hypothesis; we add it
--   here.  Downstream (subtask 8) `qw.IsDirectedWalk` is guaranteed by
--   the (⇐) direction's construction: `qw` is built as a directed
--   walk in the do-on-`{v}` intervened CDMG, then lifted to `G` via
--   subtask 1's `Walk.liftFromHardIntervention` (which preserves
--   `IsDirectedWalk`).

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.comp_assoc
/-- Auxiliary: `Walk.comp` is associative.  Verbatim structural induction
on the first argument: the `nil` case reduces by definition
(`nil.comp q = q`, so `(nil.comp q).comp r = q.comp r = nil.comp (q.comp r)`),
and the `cons` case unfolds `comp` once on each side, exposing the IH on
the tail.  Needed by `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux`'s
inductive step to re-associate
`((reverseDirected qv').comp single-back-edge).comp rest` into the form
`(reverseDirected qv').comp (single-back-edge.comp rest)` that the IH
matches. -/
private lemma Walk.comp_assoc {G : CDMG Node} :
    ∀ {u₁ u₂ u₃ u₄ : Node} (p : Walk G u₁ u₂) (q : Walk G u₂ u₃)
      (r : Walk G u₃ u₄),
      (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ a hStep p, q, r => by
      change Walk.cons _ a hStep ((p.comp q).comp r)
            = Walk.cons _ a hStep (p.comp (q.comp r))
      rw [Walk.comp_assoc p q r]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.comp_assoc

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isBifurcationDirectedHinge_cons_backward_of_directed
/-- **Subtask 6a (base case):** a single backward `E`-edge `(v, u)`
followed by a non-trivial directed walk `p : Walk G v w` realises the
directed-hinge predicate at index 0.

Matches the third clause of `IsBifurcationDirectedHingeWithSplit`'s
recursion (`Walks.lean:1045-1046`: `u, _, .cons v a _ (p@(.cons _ _ _ _)),
0 => a = (v, u) ∧ a ∈ G.E ∧ p.IsDirectedWalk`).  The `hp_nonempty`
hypothesis rules out the second clause (`cons _ _ _ (.nil _ _), 0 =>
False`) — a degenerate single-edge "bifurcation" with no right arm.

Proof: case-split on `p`.  The `nil` branch contradicts `hp_nonempty`
(`(.nil _ _).length = 0`).  The `cons` branch lands in the third
predicate clause; the triple `⟨ha_eq, ha_mem, hp_dir⟩` is the data
itself. -/
private lemma Walk.isBifurcationDirectedHinge_cons_backward_of_directed
    {G : CDMG Node} {u v w : Node}
    (a : Node × Node) (h : G.WalkStep u a v) (p : Walk G v w)
    (hp_dir : p.IsDirectedWalk) (ha_eq : a = (v, u)) (ha_mem : a ∈ G.E)
    (hp_nonempty : p.length ≥ 1) :
    (Walk.cons v a h p).IsBifurcationDirectedHingeWithSplit 0 := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_nonempty
  | cons _ _ _ _ => exact ⟨ha_eq, ha_mem, hp_dir⟩
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isBifurcationDirectedHinge_cons_backward_of_directed

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
/-- **Subtask 6b (parametrised inductive step):** prepending the
`reverseDirected qv` backward-edge chain (of length `qv.length`) in
front of any walk `rest` that already realises the directed-hinge
predicate at index `k` shifts the index by `qv.length`.

The parametrisation by `rest` and `k` is what makes the structural
induction on `qv` go through.  The natural induction is on `qv`'s
outermost cons cell, but `reverseDirected`'s definition places the
new edge at the *rightmost* position of the recursion via
`(reverseDirected qv').comp single-back-edge`.  So the IH on `qv'`
must apply with an enriched `rest' = cons c a backStep rest` and
shifted index `k' = k + 1`.

Proof: structural recursion on `qv`.
* `nil` case (`qv.length = 0`, `reverseDirected (nil w hw) = nil w hw`):
  `(nil w hw).comp rest = rest` (by `Walk.comp`'s `nil` clause), so
  the goal reduces to `rest.IsBifurcationDirectedHingeWithSplit
  (0 + k) = rest.IsBifurcationDirectedHingeWithSplit k`, which is
  exactly `hrest`.
* `cons vMid a hStep qv'` case (`qv.length = qv'.length + 1`):
  - Form the backward `WalkStep` witness `backStep : G.WalkStep vMid
    a c` from `hqv_dir`'s `a = (c, vMid) ∧ a ∈ G.E` data (the same
    packaging used inside `reverseDirected`'s `cons` clause).
  - Form the enriched right-arm `Walk.cons c a backStep rest` and its
    directed-hinge witness at index `k + 1`: the predicate's `k + 1`
    clause (`Walks.lean:1047-1048`) gives
    `a = (c, vMid) ∧ a ∈ G.E ∧ rest.IsBifurcationDirectedHingeWithSplit k`,
    each conjunct supplied by `hqv_dir` / `hrest`.
  - Apply the IH to `qv'` with `rest' := cons c a backStep rest`,
    `k' := k + 1`.  The IH conclusion is
    `((reverseDirected qv').comp (cons c a backStep rest))
       .IsBifurcationDirectedHingeWithSplit (qv'.length + (k + 1))`.
  - Re-associate the LHS via `Walk.comp_assoc`: the original goal
    `(((reverseDirected qv').comp single-back-edge).comp rest)` becomes
    `((reverseDirected qv').comp (single-back-edge.comp rest))`.
    Since `single-back-edge = cons c a backStep (nil c _)` and
    `(nil c _).comp rest = rest` (by `Walk.comp`'s `nil` clause),
    we have `single-back-edge.comp rest = cons c a backStep rest`
    definitionally, matching the IH's LHS.
  - Arithmetic: `qv'.length + 1 + k = qv'.length + (k + 1)`. -/
private lemma Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
      {w : Node} (rest : Walk G c w) (k : ℕ)
      (_hrest : rest.IsBifurcationDirectedHingeWithSplit k),
      Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv hqv_dir).comp rest) (qv.length + k)
  | _, _, .nil w hw, _, _, rest, k, hrest => by
      simp only [Walk.reverseDirected, Walk.comp, Walk.length, Nat.zero_add]
      exact hrest
  | c, _, .cons vMid a hStep qv', hqv_dir, _, rest, k, hrest => by
      have backStep : G.WalkStep vMid a c :=
        Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩
      have h_cons : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c a backStep rest) (k + 1) := by
        simp only [Walk.IsBifurcationDirectedHingeWithSplit]
        exact ⟨hqv_dir.1, hqv_dir.2.1, hrest⟩
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir.2.2 (Walk.cons c a backStep rest) (k + 1) h_cons
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir.2.2).comp
            (Walk.cons c a backStep
              (Walk.nil c (WalkStep.source_mem hStep)))).comp rest)
        (qv'.length + 1 + k)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir.2.2).comp
          (Walk.cons c a backStep rest))
        (qv'.length + 1 + k)
      have hidx : qv'.length + 1 + k = qv'.length + (k + 1) := by omega
      rw [hidx]
      exact ih
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isBifurcationDirectedHinge_mkBifurcation
/-- **Subtask 6c (consumer-facing wrapper):** the `mkBifurcation`-shaped
output of subtask 5 realises the directed-hinge predicate at the
intended split index `qv.length - 1`.

The proof decomposes `qv` once: the `nil` branch contradicts
`hqv_pos`; the `cons vMid a hStep qv'` branch invokes Helper 1 to
build `(cons c a backStep qw).IsBifurcationDirectedHingeWithSplit 0`
(needing `qw.IsDirectedWalk` and `qw.length ≥ 1`), then applies
Helper 2 with `rest := cons c a backStep qw`, `k := 0` on the
smaller arm `qv'`.  The composed walk
`(reverseDirected qv).comp qw` rewrites — via the `Walk.comp_assoc`
+ `Walk.comp`-on-`nil` chain inside Helper 2 — to
`(reverseDirected qv').comp (cons c a backStep qw)`, matching
Helper 2's LHS.

The index arithmetic `qv.length - 1 = qv'.length` (in the `cons`
branch, since `qv.length = qv'.length + 1 ≥ 1`) is discharged by
`omega` after the conversion. -/
private lemma Walk.isBifurcationDirectedHinge_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_dir : qw.IsDirectedWalk)
    (hqw_pos : qw.length ≥ 1) :
    Walk.IsBifurcationDirectedHingeWithSplit
      (Walk.mkBifurcation qv hqv_dir hqv_pos qw) (qv.length - 1) := by
  change Walk.IsBifurcationDirectedHingeWithSplit
    ((Walk.reverseDirected qv hqv_dir).comp qw) (qv.length - 1)
  match qv, hqv_dir, hqv_pos with
  | .nil _ _, _, hpos => simp [Walk.length] at hpos
  | .cons vMid a hStep qv', hqv_dir, _ =>
      have backStep : G.WalkStep vMid a c :=
        Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩
      have h_base : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c a backStep qw) 0 :=
        Walk.isBifurcationDirectedHinge_cons_backward_of_directed
          a backStep qw hqw_dir hqv_dir.1 hqv_dir.2.1 hqw_pos
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir.2.2 (Walk.cons c a backStep qw) 0 h_base
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir.2.2).comp
            (Walk.cons c a backStep
              (Walk.nil c (WalkStep.source_mem hStep)))).comp qw)
        (qv'.length + 1 - 1)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir.2.2).comp
          (Walk.cons c a backStep qw))
        (qv'.length + 1 - 1)
      have hidx : qv'.length + 1 - 1 = qv'.length + 0 := by omega
      rw [hidx]
      exact ih
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isBifurcationDirectedHinge_mkBifurcation

-- ## Private helpers — arm extraction from a directed-hinge bifurcation
--
-- Subtask 7 of the proof of `claim_3_5` builds the *inverse* of
-- subtask 5's `mkBifurcation` constructor: given a bifurcation walk
-- `p : Walk G v w` realising
-- `Walk.IsBifurcationDirectedHingeWithSplit i`, extract the source
-- vertex `c = p.vertices[i + 1]`, the *left arm* `L : Walk G c v` (a
-- directed walk consisting of the bifurcation's first `i + 1` edges
-- read backwards), and the *right arm* `R : Walk G c w` (a directed
-- walk consisting of the bifurcation's remaining `n - (i + 1)` edges
-- read forwards).
--
-- The (⇒) direction of the TeX proof (lines 170–250 of
-- `tex/claim_3_5_proof_BifurcationAlternative.tex`) is exactly this
-- decomposition: the bifurcation's structure at the directed hinge
-- splits the walk into two directed arms that each land in the
-- appropriate intervened CDMG via subtask 3's
-- `Walk.liftTo_hardInterventionOn` (after subtask 8 combines this
-- lemma's vertex-containment clauses with the bifurcation walk's
-- clause~(a) end-node-uniqueness to discharge the avoidance
-- hypothesis).
--
-- The lemma is delivered in a single *unified* form:
--
-- * the source vertex `c` (paired with the `vertices[i + 1]?`
--   identification),
-- * a directed walk `L : Walk G c v` of length `≥ 1`,
-- * a directed walk `R : Walk G c w` of length `≥ 1`,
-- * vertex-containment clauses `L.vertices ⊆ p.vertices.dropLast`
--   and `R.vertices ⊆ p.vertices.tail`.
--
-- The vertex-containment shape is the load-bearing one: combined with
-- `IsBifurcationSource`'s `w ∉ p.vertices.dropLast` and
-- `v ∉ p.vertices.tail` clauses (from `Walks.lean:1127-1128`), it
-- yields `w ∉ L.vertices` and `v ∉ R.vertices`, exactly the avoidance
-- hypotheses subtask 8 feeds into `liftTo_hardInterventionOn`.
--
-- ## Design choice
--
-- *Unified single-lemma form (rather than the workspace plan's
--   fallback three-lemma split).*  The arm extraction is a single
--   structural recursion on `p` (case-splitting on `i` and the inner
--   walk inside each cons branch), and the L / R / source data are
--   built simultaneously in each clause.  Splitting into three lemmas
--   ("extract source", "extract L", "extract R") would duplicate the
--   case analysis three times with no real win — the per-case L /
--   R / source constructions interlock at exactly the same case
--   junctures.  If a future consumer wants only one piece, the
--   `obtain` at the call site discards the others for free.
--
-- *Vertex-containment via `.dropLast` / `.tail` set-membership (not
--   exact equality `L.vertices = p.vertices.take (i + 2).reverse`).*
--   The exact-equality shape `L.vertices = (p.vertices.take (i + 2)).reverse`
--   and `R.vertices = p.vertices.drop (i + 1)` would be slightly
--   stronger but would force every consumer to derive set-membership
--   facts from the equation.  Subtask 8 needs exactly the
--   set-membership shape (to discharge `liftTo_hardInterventionOn`'s
--   avoidance hypothesis), and the equations would also force fiddly
--   `List.take` / `List.drop` arithmetic at every consumer site that
--   the set-membership form sidesteps.  The `.dropLast` / `.tail`
--   choice exactly matches `IsBifurcationSource`'s clause shape
--   (`u ∉ vertices.tail` / `v ∉ vertices.dropLast`), giving subtask 8
--   a one-step set-membership transport rather than an
--   `.take` / `.drop` / `.reverse` chain.
--
-- *Induction on `p` (structurally) with `i` generalised, then
--   nested case-analysis on `i` and the inner walk `p'`.*  The
--   `IsBifurcationDirectedHingeWithSplit` predicate recurses
--   simultaneously on `p` and `i` (`Walks.lean:1042-1048`), and
--   the four clauses (`nil`, `cons _ _ _ (.nil _ _), 0`,
--   `cons _ _ _ (cons _ _ _ _), 0`, `cons _ _ _ _, k+1`) split
--   the proof into four cases.  The outer `induction p generalizing i`
--   handles the recursion on `p`; the inner `match i, p', h_hinge`
--   case-splits on the four clauses.  An alternative (Plan B in the
--   workspace: induct on `i` first, then case on `p` inside) was
--   considered but produces extra bookkeeping at the `i + 1` /
--   `p = nil` case (which is dispatched here via a direct `h_rec.elim`
--   on the inner walk's nil pattern), since the IH on `i` does not
--   structurally decrease the walk.  The chosen Plan A's IH on `p`
--   directly decreases the walk, matching the predicate's recursion
--   shape one-for-one.
--
-- *Length-≥1 conjuncts kept on both arms even though only the
--   `L.length ≥ 1` clause carries non-trivial content (R's length is
--   inherited from the IH or the base-case `cons` pattern).*  Subtask
--   8 needs both length conjuncts to derive `c ≠ v` (from
--   `L.length ≥ 1` + `L` going from `c` to `v`) and `c ≠ w` (from
--   `R.length ≥ 1` + `R` going from `c` to `w`).  Pinning both
--   conjuncts here keeps the API self-contained — the consumer reads
--   `c ≠ v` and `c ≠ w` off the lemma without re-extracting from the
--   walks' shapes.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.exists_arms_of_bifurcation_directed_hinge
/-- **Subtask 7 of `claim_3_5` (the arm extractor):** given a
bifurcation walk `p : Walk G v w` together with a directed-hinge
witness `p.IsBifurcationDirectedHingeWithSplit i`, extract:

* the *source vertex* `c = p.vertices[i + 1]`,
* the *left arm* `L : Walk G c v` — a directed walk of length `≥ 1`
  whose vertices are all in `p.vertices.dropLast` (equivalently,
  every vertex of `L` appears among the first `n` of the bifurcation
  walk, where `n = p.length`);
* the *right arm* `R : Walk G c w` — a directed walk of length
  `≥ 1` whose vertices are all in `p.vertices.tail` (equivalently,
  every vertex of `R` appears among the last `n` of the bifurcation
  walk).

The two `vertices.dropLast` / `vertices.tail` containment clauses are
load-bearing for the (⇒) direction's lift step: combined with
`Walk.IsBifurcationSource`'s `v ∉ p.vertices.tail` and
`w ∉ p.vertices.dropLast` clauses (from `Walks.lean:1127-1128`), they
yield `w ∉ L.vertices` and `v ∉ R.vertices` — the avoidance
hypotheses required by `liftTo_hardInterventionOn` (subtask 3) to lift
`L` into `G_{do({w})}` and `R` into `G_{do({v})}`.

The source identification `p.vertices[i + 1]? = some c` lets subtask
8's `IsBifurcationSource` unfolding cross-match the lemma's returned
`c` against the externally-given source.

Proof: outer `induction p generalizing i`, then for the `cons` case,
inner `cases i` and `cases p'` (with `obtain` on the predicate data).
Four leaf cases:

* `(nil _ _), i`: predicate is `False`, contradiction.
* `(cons _ _ _ (.nil _ _)), 0`: predicate is `False`, contradiction.
* `(cons vMid a hStep (.cons vMid' a' hStep' p'')), 0`: base case;
  `L = .cons v a forwardStep (.nil v hv)` (a single forward edge from
  `vMid` to `v`, using the directed alternative `a = (vMid, v) ∧ a ∈ G.E`),
  `R = .cons vMid' a' hStep' p''` (the tail), `c = vMid`.
* `(cons vMid a hStep p'), k+1`: inner `cases p'`:
    * `p' = nil _ _`: predicate's `h_rec` is `False`, contradiction.
    * `p' = cons vMid' a' hStep' p''`: recursive case; apply IH to
      get `(c, L', R)` from `p'`, then build the new `L = L'.comp
      (single forward edge from vMid to v)` and keep `R` unchanged.

Vertex-containment in the recursive case uses `Walk.vertices_comp`
(subtask 2) to compute `L.vertices = L'.vertices.dropLast ++ [vMid, v]`,
and dispatches each element of `L.vertices` to `L'.vertices.dropLast`
(via the IH's containment) or to the literal `vMid` / `v` cases (both
of which lie in `p.vertices.dropLast = v :: vMid :: p''.vertices.dropLast`
after unfolding via `List.dropLast_cons_of_ne_nil` and
`Walk.vertices_ne_nil`). -/
private lemma Walk.exists_arms_of_bifurcation_directed_hinge
    {G : CDMG Node} {v w : Node} (p : Walk G v w) :
    ∀ (i : ℕ), p.IsBifurcationDirectedHingeWithSplit i →
      ∃ (c : Node) (L : Walk G c v) (R : Walk G c w),
        L.IsDirectedWalk ∧ R.IsDirectedWalk ∧
        L.length ≥ 1 ∧ R.length ≥ 1 ∧
        p.vertices[i + 1]? = some c ∧
        (∀ x ∈ L.vertices, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ R.vertices, x ∈ p.vertices.tail) := by
  induction p with
  | nil v hv =>
      intro i h_hinge
      exact h_hinge.elim
  | @cons u w vMid a hStep p' ih =>
      intro i h_hinge
      cases i with
      | zero =>
          cases p' with
          | nil v_p' h_p' =>
              -- Predicate's second clause: cons _ _ _ (.nil _ _), 0 => False.
              exact h_hinge.elim
          | cons vMid' a' hStep' p'' =>
              -- Predicate's third clause: cons _ _ _ (cons _ _ _ _), 0 =>
              -- a = (vMid, u) ∧ a ∈ G.E ∧ tail.IsDirectedWalk.
              have h_unfold :
                  a = (vMid, u) ∧ a ∈ G.E ∧
                    (Walk.cons vMid' a' hStep' p'').IsDirectedWalk :=
                h_hinge
              obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := h_unfold
              -- Base case: source c = vMid; L = single forward edge
              -- from vMid to u; R = the tail.
              have hu_in_G : u ∈ G := WalkStep.source_mem hStep
              let forwardStep : G.WalkStep vMid a u :=
                Or.inl ⟨ha_eq, Or.inl ha_mem⟩
              refine ⟨vMid,
                      Walk.cons u a forwardStep (Walk.nil u hu_in_G),
                      Walk.cons vMid' a' hStep' p'',
                      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- L.IsDirectedWalk
                exact ⟨ha_eq, ha_mem, trivial⟩
              · -- R.IsDirectedWalk
                exact hp'_dir
              · -- L.length ≥ 1
                change 0 + 1 ≥ 1
                exact Nat.le_refl 1
              · -- R.length ≥ 1
                change p''.length + 1 ≥ 1
                exact Nat.succ_le_succ (Nat.zero_le _)
              · -- p.vertices[1]? = some vMid
                rfl
              · -- ∀ x ∈ L.vertices, x ∈ p.vertices.dropLast
                intro x hx
                -- L.vertices = [vMid, u].
                have hxv : x = vMid ∨ x = u := by
                  rcases List.mem_cons.mp hx with rfl | hx2
                  · exact Or.inl rfl
                  · rcases List.mem_cons.mp hx2 with rfl | hx3
                    · exact Or.inr rfl
                    · simp at hx3
                -- p.vertices.dropLast = u :: vMid :: p''.vertices.dropLast.
                have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
                  Walk.vertices_ne_nil _
                have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp'_ne]
                change x ∈ u :: (vMid :: p''.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp''_ne]
                rcases hxv with rfl | rfl
                · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                · exact List.mem_cons_self
              · -- ∀ x ∈ R.vertices, x ∈ p.vertices.tail
                intro x hx
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
                exact hx
      | succ k =>
          -- The predicate at (cons vMid a hStep p', k+1) needs p' to be
          -- concrete before it reduces (the second predicate clause's
          -- match on `cons _ _ _ (.nil _ _)` blocks reduction otherwise).
          -- Case-split p' first; in each branch the predicate match fires
          -- and we can extract the three conjuncts via `obtain` directly.
          cases p' with
          | nil vNil hNil =>
              -- h_hinge unfolds to ⟨_, _, False⟩; the False is in the
              -- third conjunct via `(nil _ _).IsBifurcationDirectedHingeWithSplit k = False`.
              obtain ⟨_, _, h_rec⟩ := h_hinge
              exact h_rec.elim
          | cons vMid' a' hStep' p'' =>
              -- h_hinge unfolds to a = (vMid, u) ∧ a ∈ G.E ∧
              -- (cons vMid' a' hStep' p'').IsBifurcationDirectedHingeWithSplit k.
              obtain ⟨ha_eq, ha_mem, h_rec⟩ := h_hinge
              -- Apply IH to p' (= cons vMid' a' hStep' p'') and k.
              obtain ⟨c, L', R, hL'_dir, hR_dir, _hL'_pos, hR_pos, h_idx_p',
                      hL'_sub, hR_sub⟩ :=
                ih k h_rec
              -- Build L_new : Walk G c u by composing L' with a single
              -- forward edge from vMid to u.
              have hu_in_G : u ∈ G := WalkStep.source_mem hStep
              let forwardStep : G.WalkStep vMid a u :=
                Or.inl ⟨ha_eq, Or.inl ha_mem⟩
              let single : Walk G vMid u :=
                Walk.cons u a forwardStep (Walk.nil u hu_in_G)
              have hsingle_dir : single.IsDirectedWalk :=
                ⟨ha_eq, ha_mem, trivial⟩
              refine ⟨c, L'.comp single, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- (L'.comp single).IsDirectedWalk
                exact Walk.isDirectedWalk_comp L' single hL'_dir hsingle_dir
              · -- R.IsDirectedWalk
                exact hR_dir
              · -- (L'.comp single).length ≥ 1
                rw [Walk.length_comp]
                change L'.length + 1 ≥ 1
                exact Nat.succ_le_succ (Nat.zero_le _)
              · -- R.length ≥ 1
                exact hR_pos
              · -- p.vertices[(k+1) + 1]? = some c
                -- p.vertices = u :: p'.vertices = u :: vMid :: p''.vertices,
                -- so p.vertices[k+2]? = p'.vertices[k+1]?.
                -- IH gives p'.vertices[k+1]? = some c.
                change (u :: (Walk.cons vMid' a' hStep' p'').vertices)[k + 1 + 1]?
                      = some c
                simpa using h_idx_p'
              · -- ∀ x ∈ (L'.comp single).vertices, x ∈ p.vertices.dropLast
                intro x hx
                -- (L'.comp single).vertices = L'.vertices.dropLast ++ single.vertices
                --                            = L'.vertices.dropLast ++ [vMid, u].
                have hL_new_vs : (L'.comp single).vertices
                    = L'.vertices.dropLast ++ [vMid, u] := by
                  rw [Walk.vertices_comp]
                  rfl
                rw [hL_new_vs] at hx
                -- p.vertices.dropLast = u :: vMid :: p''.vertices.dropLast.
                have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
                  Walk.vertices_ne_nil _
                have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp'_ne]
                change x ∈ u :: (vMid :: p''.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp''_ne]
                rcases List.mem_append.mp hx with hL'drop | h_in_tail
                · -- x ∈ L'.vertices.dropLast: x ∈ L'.vertices via mem_of_mem_dropLast,
                  -- then x ∈ p'.vertices.dropLast via hL'_sub.
                  have hx_L'_vertices : x ∈ L'.vertices :=
                    List.mem_of_mem_dropLast hL'drop
                  have hx_p'_drop : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.dropLast :=
                    hL'_sub x hx_L'_vertices
                  -- p'.vertices.dropLast = (vMid :: p''.vertices).dropLast
                  --                      = vMid :: p''.vertices.dropLast.
                  have hx_in : x ∈ (vMid :: p''.vertices).dropLast := by
                    have h_eq : (Walk.cons vMid' a' hStep' p'').vertices.dropLast
                        = (vMid :: p''.vertices).dropLast := by
                      rfl
                    rw [h_eq] at hx_p'_drop
                    exact hx_p'_drop
                  rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_in
                  exact List.mem_cons.mpr (Or.inr hx_in)
                · -- x ∈ [vMid, u]
                  rcases List.mem_cons.mp h_in_tail with rfl | hx_in2
                  · -- x = vMid
                    exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                  · rcases List.mem_cons.mp hx_in2 with rfl | hx_empty
                    · -- x = u
                      exact List.mem_cons_self
                    · simp at hx_empty
              · -- ∀ x ∈ R.vertices, x ∈ p.vertices.tail
                intro x hx
                have hx_p'_tail : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.tail :=
                  hR_sub x hx
                have hx_p' : x ∈ (Walk.cons vMid' a' hStep' p'').vertices :=
                  List.mem_of_mem_tail hx_p'_tail
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
                exact hx_p'
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.exists_arms_of_bifurcation_directed_hinge

-- ref: claim_3_5
-- For any CDMG `G : CDMG Node` and any three (not necessarily
-- distinct) nodes `v, w, c ∈ G` (i.e. `v, w, c ∈ G.J ∪ G.V`), the
-- following are equivalent:
--
-- (a) *Existence of a bifurcation between `v` and `w` with source
--     `c`.*  There exists a walk `p : Walk G v w` such that
--     `p.IsBifurcationSource c` (in the sense of `def_3_4`'s
--     trailing `IsBifurcationSource` predicate).  This single
--     existential packages both the LN's "`p` is a bifurcation
--     between `v` and `w`" (clauses (a)–(e) of `def_3_4` item~vi,
--     including the `v ≠ w` first-half of clause (a) and the
--     end-node-uniqueness clause), and the LN's "the bifurcation
--     has source `c`" (the closing paragraph of `def_3_4`
--     item~vi).  Under our `def_3_4` encoding's chapter-init
--     addition `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
--     `IsBifurcationSource p c` automatically commits to the
--     interior-source convention `1 ≤ k ≤ n - 1` (`0 ≤ i ≤ n - 2`
--     in the Lean encoding), so `c ≠ v` and `c ≠ w` are
--     consequences of (a), not extra hypotheses.
--
-- (b) *Set-theoretic ancestral characterisation.*
--     The conjunction of:
--       (i)   `v ≠ w`;
--       (ii)  `c ∈ (G.hardInterventionOn {w} _).Anc v \ {v}`,
--             i.e. `c` is an ancestor of `v` in the
--             do-on-`{w}` intervened CDMG (`def_3_10` +
--             `def_3_5`'s `Anc`), and `c ≠ v`;
--       (iii) `c ∈ (G.hardInterventionOn {v} _).Anc w \ {w}`,
--             i.e. `c` is an ancestor of `w` in the
--             do-on-`{v}` intervened CDMG, and `c ≠ w`.
--
-- The `_` in (ii) and (iii) is the singleton-subset witness
-- `{w} ⊆ G.J ∪ G.V` / `{v} ⊆ G.J ∪ G.V`, supplied here by
-- `Finset.singleton_subset_iff.mpr hw` / `… hv` (recovering the
-- LN's "the lowercase `w` / `v` inside the `do(·)` slot is
-- shorthand for the singleton sets `{w}` / `{v}`" reading of
-- `def_3_10`'s `W` argument).
/-
LN tex (verbatim, from `graphs.tex`,
`\label{prp:bifurcations_alternative}`):

  \begin{Prp}\label{prp:bifurcations_alternative}
    Let $G = \lt J, V, E, L \rt$ be a CDMG.  For $v, w, c \in V
    \cup J$: there exists a bifurcation between $v$ and $w$ in
    $G$ with source $c$ if and only if $v \ne w$ and $c \in
    \Anc^{G_{\doit(w)}}(v) \sm \{v\}$ and $c \in
    \Anc^{G_{\doit(v)}}(w) \sm \{w\}$.
  \end{Prp}

Rewritten canonical tex (`claim_3_5_statement_BifurcationAlternative.tex`,
sketch):

  Universal quantification over `(G, v, w, c)` with
  `v, w, c ∈ J ∪ V`.  Equivalence:
    (a) ∃ walk `p` from `v` to `w` in `G` with split index `k`
        (`1 ≤ k ≤ n`) such that `p` is a bifurcation between
        `v` and `w` at `k` and `c` is the source (directed
        hinge, `c = v_k`).  Clause (e) of `def_3_4` item~vi
        forces `1 ≤ k ≤ n - 1`, so `c ≠ v ≠ w`.
    (b) `v ≠ w` ∧ `c ∈ Anc^{G_{do({w})}}(v) ∖ {v}`
              ∧ `c ∈ Anc^{G_{do({v})}}(w) ∖ {w}`,
        with the singleton-set reading of `do(·)` made explicit.
-/
-- ## Design choice
--
-- *One theorem, biconditional `↔` between (a) and (b).*  The LN
--   block writes a single "if and only if" between two propositions;
--   the rewritten tex preserves that single-statement shape; we
--   render it as one Lean `theorem` returning an `Iff`.  Splitting
--   into two named theorems (forward / backward) was rejected
--   because (i) the LN treats this as one proposition with a single
--   reference label `\label{prp:bifurcations_alternative}`, and
--   (ii) downstream consumers wanting either direction reach `.mp` /
--   `.mpr` on the `Iff` for free.
--
-- *Binder shape `(G : CDMG Node) (v w c : Node) (hv hw hc : … ∈ G)`,
--   in that order.*  Mirrors `def_3_10`'s `(G : CDMG Node) (W : …)
--   (hW : W ⊆ G.J ∪ G.V)` shape (graph first, then the relevant
--   nodes/sets, then the membership/subset preconditions).  The
--   three membership hypotheses are explicit, matching the rewritten
--   tex's `v, w, c ∈ J ∪ V` quantifier scope (rendered via the
--   `Membership Node (CDMG Node)` instance of `def_3_2`).  `hc` is
--   technically not needed to type-check the RHS (the `c ∈ Anc …`
--   conjunct already requires `c ∈ G` via `def_3_5`'s `Anc` body),
--   but we carry it explicitly to match the LN's literal universal
--   scope and to keep the binder block parallel to `hv` / `hw`.
--
-- *LHS as `∃ p : Walk G v w, p.IsBifurcationSource c`.*  The
--   rewritten tex spec decomposes the LN's "exists a bifurcation
--   between `v` and `w` with source `c`" into:
--     (1) a walk `p` from `v` to `w`,
--     (2) `p` is a bifurcation between `v` and `w` at some index `k`,
--     (3) `c` is the source of this bifurcation.
--   Our `Walk.IsBifurcationSource p c` (in
--   `Section3_1/Walks.lean`) is a single `Prop` packaging all three
--   ingredients — it requires (i) `u ≠ v` (the LN's "v ≠ w"
--   conjunct at clause (a) first-half), (ii) `u ∉ p.vertices.tail`
--   and `v ∉ p.vertices.dropLast` (the end-node uniqueness clause
--   (a) second-half), and (iii) `∃ i,
--   p.IsBifurcationDirectedHingeWithSplit i ∧
--   p.vertices[i + 1]? = some c` (the bifurcation split and
--   directed-hinge source identification).  Existential
--   quantification over the index `k` (here `i`) is internal to
--   `IsBifurcationSource`, so the outer existential is over `p`
--   alone, matching the LN's surface reading "there exists a
--   bifurcation (which is a walk) ...".  Building the LHS via an
--   ad-hoc tuple type `(p, k, h_bif, h_src)` was rejected because
--   it would duplicate the `def_3_4`-encoded constraints at the
--   theorem boundary, lose the LN-faithful "exists a bifurcation"
--   surface phrasing, and force every downstream consumer to
--   re-derive what `def_3_4` has already packaged.
--
-- *RHS as a three-way conjunction `v ≠ w ∧ … ∧ …`, mirroring the
--   LN's literal `v ≠ w and … and …` reading.*  The LN writes the
--   right-hand side as three separate conjuncts joined by "and";
--   we follow the LN literally rather than collapsing into, say,
--   `v ≠ w ∧ c ∈ A ∩ B \ {v, w}` (which would obscure the
--   `def_3_10` singleton interventions and the asymmetry between
--   `\ {v}` and `\ {w}`).  Conjunction order matches the LN.
--
-- *Asymmetric pairing `Anc^{G_{do(w)}}(v) \ {v}` and
--   `Anc^{G_{do(v)}}(w) \ {w}` preserved verbatim (not the
--   "natural-looking" alternatives).*  The LN pairs each
--   *intervention end-node* with the *opposite ancestor target* —
--   the source `c` is an ancestor of `v` in the graph where the
--   other end-node `w` has been do-intervened, and vice versa.
--   This pairing encodes the "bifurcation arms avoid the opposite
--   end-node" semantic content: by `def_3_10` items iii.–iv. the
--   `do` cuts all incoming edges to the intervened node, so any
--   ancestor path from `c` to `v` in `G_{do(w)}` automatically
--   avoids `w` — exactly the directed-walk-to-`v` arm of the
--   bifurcation (`def_3_4` item~vi.(b)).  The natural-looking
--   "matched" alternative `Anc^{G_{do(v)}}(v) \ {v}` is vacuously
--   empty (the intervened node has no incoming edges, so
--   `Anc^{G_{do(v)}}(v) = {v}` and the set-minus is `∅`); the
--   uninterventioned alternative `Anc^G(v) ∩ Anc^G(w)` would
--   conflate "common ancestor" with "bifurcation source" and lose
--   the "arms avoid the opposite end" content.  Preserving the LN's
--   exact orientation is load-bearing for downstream rows: chapter
--   4+ d-separation, identification, and the do-calculus rules all
--   pattern-match `claim_3_5` in this orientation, so any
--   rearrangement here would force every consumer to re-derive the
--   equivalence under permuted conjuncts.
--
-- *`G.hardInterventionOn ({w} : Finset Node)
--   (Finset.singleton_subset_iff.mpr hw)`*, with the singleton
--   subset proof inlined.  The LN writes `G_{do(w)}` with a
--   bare `w` inside `do(·)`; the rewritten tex makes the
--   singleton-set reading explicit ("`G_{do(w)}` is shorthand
--   for `G_{do({w})}`").  We inline the proof
--   `Finset.singleton_subset_iff.mpr hw` (one-liner taking
--   `w ∈ G.J ∪ G.V` to `{w} ⊆ G.J ∪ G.V`, where `hw : w ∈ G` is
--   definitionally `w ∈ G.J ∪ G.V` via the `Membership Node
--   (CDMG Node)` instance of `def_3_2`).  A named helper lemma
--   was rejected as overkill — the inline form is a single mathlib
--   call and adds no friction at the statement level; if a
--   downstream row finds itself repeating this pattern, the helper
--   can be promoted later.
--
-- *Set-difference shape `\ {v}` (`Set.diff` with a singleton
--   `Set Node`), not the equivalent conjunction `… ∧ c ≠ v`.*
--   The rewritten tex spec preserves the LN's literal `\ {v}` /
--   `\ {w}` notation; we mirror that in Lean.  `Anc` returns
--   `Set Node`, so `\ {v}` elaborates as `Set.diff (G.Anc v) ({v}
--   : Set Node)` and `c ∈ … \ {v}` unfolds to `c ∈ … ∧ c ∉ {v}`
--   i.e. `c ∈ … ∧ c ≠ v`.  Writing `c ∈ … ∧ c ≠ v` directly
--   would be content-equivalent but diverge stylistically from
--   the rewritten tex.  The set-difference reading also makes
--   downstream lemmas about ancestor sets transport directly
--   (`Set.mem_diff`, `Set.mem_singleton_iff`).
--
-- *Universal `c ∈ G` is carried even though the LN-faithful (b)
--   already implies it via `Anc`'s body.*  The rewritten tex's
--   quantifier scope is `v, w, c ∈ J ∪ V`; if we dropped `hc`,
--   the theorem would still be true (the RHS's `Anc` conjunct
--   would force `c ∈ G` whenever (b) holds; the LHS's
--   `IsBifurcationSource p c` would force `c ∈ G` via
--   `p.vertices[i + 1]? = some c` and the walk's vertex
--   membership in `G`), but the statement would no longer
--   literally mirror the LN's universal scope.  Carrying `hc`
--   keeps the contract LN-faithful and gives the proof a free
--   `c ∈ G` to start from.
--
-- *No additional `IsBifurcation`-vs-`IsBifurcationSource`
--   disambiguation hypothesis.*  Subtle point: the LN's "exists
--   a bifurcation between `v` and `w` with source `c`" is *one*
--   existential; the LN-critic's `source_at_endpoint_w_when_right_arm_trivial`
--   wording check flagged that a literal reading of `def 3.4`
--   would let the source coincide with `w` in the degenerate
--   `k = n` case.  Our `def_3_4` encoding's `IsBifurcationSource`
--   predicate already excludes that case (via
--   `IsBifurcationDirectedHingeWithSplit`'s
--   `.cons _ _ _ (.nil _ _), 0 => False` branch implementing the
--   chapter-init addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`),
--   so no extra hypothesis or disjunct is needed here.  See the
--   long comment block above `\begin{Prp}` in the rewritten tex
--   spec and the workspace note in
--   `workspace_claim_3_5.md` for the full LN-critic resolution.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: bifurcationAlternative
-- claim_3_5 -- start statement
theorem bifurcationAlternative (G : CDMG Node) (v w c : Node)
    (hv : v ∈ G) (hw : w ∈ G) (hc : c ∈ G) :
    (∃ p : Walk G v w, p.IsBifurcationSource c)
      ↔
        v ≠ w
      ∧ c ∈ (G.hardInterventionOn {w}
              (Finset.singleton_subset_iff.mpr hw)).Anc v \ {v}
      ∧ c ∈ (G.hardInterventionOn {v}
              (Finset.singleton_subset_iff.mpr hv)).Anc w \ {w}
-- claim_3_5 -- end statement
  := by
  -- `hc` is part of the universal scope `v, w, c ∈ J ∪ V` per
  -- `def_3_2`; the RHS's `Anc` conjunct independently forces
  -- `c ∈ G`, but we carry `hc` for LN-faithfulness of the binder
  -- block (see the "Universal `c ∈ G` is carried …" design-choice
  -- bullet above).  The `let _` pin mirrors the unused-LN-faithful
  -- convention used in `HardInterventionOn.lean`'s `hardInterventionOn`
  -- definition.
  let _ := hc
  constructor
  · -- (⇒) direction: from the bifurcation walk extract the two
    -- directed arms (subtask 7), then lift each arm into the
    -- appropriate intervened CDMG (subtask 3).
    rintro ⟨p, h_bif⟩
    obtain ⟨huv_ne, hu_tail, hv_drop, i, h_hinge, h_src⟩ := h_bif
    obtain ⟨c', L, R, hL_dir, hR_dir, hL_pos, hR_pos, hc_idx, hL_sub, hR_sub⟩ :=
      Walk.exists_arms_of_bifurcation_directed_hinge p i h_hinge
    -- Identify `c' = c` using the source-index identification.  We
    -- keep both names alive (rather than `subst`-ing) so the theorem's
    -- universally-quantified `c` stays visible to the final
    -- `refine`'s LN-faithful conjuncts.
    have hc'_eq_c : c' = c := by
      rw [hc_idx] at h_src
      exact Option.some.inj h_src
    -- `c'` lies in `p.vertices.dropLast` (head of `L`'s vertices, all
    -- of which are in `p.vertices.dropLast` by `hL_sub`), and in
    -- `p.vertices.tail` (head of `R`'s vertices, all in
    -- `p.vertices.tail` by `hR_sub`).  Combined with the
    -- end-node-uniqueness clauses of `IsBifurcationSource`, this gives
    -- `c' ≠ v` and `c' ≠ w`, hence `c ≠ v` and `c ≠ w` via
    -- `hc'_eq_c`.
    have hc'_in_drop : c' ∈ p.vertices.dropLast :=
      hL_sub c' (Walk.head_mem_vertices L)
    have hc'_in_tail : c' ∈ p.vertices.tail :=
      hR_sub c' (Walk.head_mem_vertices R)
    have hc_ne_v : c ≠ v := by
      intro h
      apply hu_tail
      have heq : c' = v := hc'_eq_c.trans h
      exact heq ▸ hc'_in_tail
    have hc_ne_w : c ≠ w := by
      intro h
      apply hv_drop
      have heq : c' = w := hc'_eq_c.trans h
      exact heq ▸ hc'_in_drop
    -- `c ∈ G_{do(w)}`: from `c ∈ G` (which is `c ∈ G.J ∪ G.V`) plus
    -- `c ≠ w`, we conclude `c ∈ (G.J ∪ {w}) ∪ (G.V \ {w})`.
    have hc_in_Gdow :
        c ∈ G.hardInterventionOn {w} (Finset.singleton_subset_iff.mpr hw) := by
      change c ∈ (G.J ∪ {w}) ∪ (G.V \ {w})
      rcases Finset.mem_union.mp hc with hJ | hV
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        rw [Finset.mem_singleton]
        exact hc_ne_w
    have hc_in_Gdov :
        c ∈ G.hardInterventionOn {v} (Finset.singleton_subset_iff.mpr hv) := by
      change c ∈ (G.J ∪ {v}) ∪ (G.V \ {v})
      rcases Finset.mem_union.mp hc with hJ | hV
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        rw [Finset.mem_singleton]
        exact hc_ne_v
    -- Transfer `c ∈ G_{do(w)}` to `c' ∈ G_{do(w)}` (and similarly for
    -- `c' ∈ G_{do(v)}`) so the lift consumer accepts `L : Walk G c' v`
    -- / `R : Walk G c' w` directly.
    have hc'_in_Gdow :
        c' ∈ G.hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw) := hc'_eq_c ▸ hc_in_Gdow
    have hc'_in_Gdov :
        c' ∈ G.hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv) := hc'_eq_c ▸ hc_in_Gdov
    -- Avoidance hypotheses for the lift: every tail-vertex of the
    -- left arm avoids `{w}`, and every tail-vertex of the right arm
    -- avoids `{v}`.  Both follow from `hL_sub` / `hR_sub` plus the
    -- end-node uniqueness clauses.
    have hL_avoid_w : ∀ x ∈ L.vertices.tail, x ∉ ({w} : Finset Node) := by
      intro x hx hxw
      rw [Finset.mem_singleton] at hxw
      exact hv_drop (hxw ▸ hL_sub x (List.mem_of_mem_tail hx))
    have hR_avoid_v : ∀ x ∈ R.vertices.tail, x ∉ ({v} : Finset Node) := by
      intro x hx hxv
      rw [Finset.mem_singleton] at hxv
      exact hu_tail (hxv ▸ hR_sub x (List.mem_of_mem_tail hx))
    refine ⟨huv_ne, ?_, ?_⟩
    · -- `c ∈ Anc^{G_{do(w)}}(v) \ {v}`.  Build at `c'` first, then
      -- transport via `hc'_eq_c`.
      refine ⟨hc'_eq_c ▸ ⟨hc'_in_Gdow,
              Walk.liftTo_hardInterventionOn L hc'_in_Gdow hL_dir hL_avoid_w,
              Walk.isDirectedWalk_liftTo_hardInterventionOn
                L hc'_in_Gdow hL_dir hL_avoid_w⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hc_ne_v
    · -- `c ∈ Anc^{G_{do(v)}}(w) \ {w}`.
      refine ⟨hc'_eq_c ▸ ⟨hc'_in_Gdov,
              Walk.liftTo_hardInterventionOn R hc'_in_Gdov hR_dir hR_avoid_v,
              Walk.isDirectedWalk_liftTo_hardInterventionOn
                R hc'_in_Gdov hR_dir hR_avoid_v⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hc_ne_w
  · -- (⇐) direction: extract minimum-length directed walks in each
    -- intervened CDMG (subtask 4), lift them back to `G` (subtask 1),
    -- assemble the bifurcation walk (subtask 5), and verify
    -- `IsBifurcationSource` (subtask 6 plus vertex bookkeeping).
    rintro ⟨hvw_ne, hc_anc_v_full, hc_anc_w_full⟩
    have hc_ne_v : c ≠ v := fun h =>
      hc_anc_v_full.2 (Set.mem_singleton_iff.mpr h)
    have hc_ne_w : c ≠ w := fun h =>
      hc_anc_w_full.2 (Set.mem_singleton_iff.mpr h)
    have hc_in_Gdow_anc :
        c ∈ (G.hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw)).Anc v := hc_anc_v_full.1
    have hc_in_Gdov_anc :
        c ∈ (G.hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv)).Anc w := hc_anc_w_full.1
    obtain ⟨q_v_Gdow, hq_v_Gdow_dir, hq_v_Gdow_drop⟩ :=
      exists_directed_walk_v_not_in_dropLast hc_in_Gdow_anc hc_ne_v
    obtain ⟨q_w_Gdov, hq_w_Gdov_dir, hq_w_Gdov_drop⟩ :=
      exists_directed_walk_v_not_in_dropLast hc_in_Gdov_anc hc_ne_w
    -- Inline structural-walk-length identity: `q.vertices.length = q.length + 1`
    -- (used downstream to derive `q.vertices.tail ≠ []` from `q.length ≥ 1`).
    have hvert_len_succ :
        ∀ {G' : CDMG Node} {u₁ u₂ : Node} (q : Walk G' u₁ u₂),
          q.vertices.length = q.length + 1 := by
      intro G' u₁ u₂ q
      induction q with
      | nil _ _ => rfl
      | cons _ _ _ q' ih =>
        change q'.vertices.length + 1 = q'.length + 1 + 1
        omega
    -- The two source walks have length `≥ 1`: a length-`0` walk would be
    -- `Walk.nil`, forcing `c = v` (resp. `c = w`) and contradicting
    -- `hc_ne_v` (resp. `hc_ne_w`).
    have hq_v_Gdow_pos : q_v_Gdow.length ≥ 1 := by
      cases q_v_Gdow with
      | nil _ _ => exact (hc_ne_v rfl).elim
      | cons _ _ _ _ =>
        change _ + 1 ≥ 1
        exact Nat.succ_le_succ (Nat.zero_le _)
    have hq_w_Gdov_pos : q_w_Gdov.length ≥ 1 := by
      cases q_w_Gdov with
      | nil _ _ => exact (hc_ne_w rfl).elim
      | cons _ _ _ _ =>
        change _ + 1 ≥ 1
        exact Nat.succ_le_succ (Nat.zero_le _)
    -- Tail-vertices of `q_v_Gdow` / `q_w_Gdov` avoid `{w}` / `{v}`
    -- by the head-of-edge argument of `def_3_10` item iii (subtask 3a).
    have hq_v_Gdow_avoid :
        ∀ x ∈ q_v_Gdow.vertices.tail, x ∉ ({w} : Finset Node) :=
      Walk.vertices_directed_avoid_of_hardInterventionOn
        q_v_Gdow hq_v_Gdow_dir
    have hq_w_Gdov_avoid :
        ∀ x ∈ q_w_Gdov.vertices.tail, x ∉ ({v} : Finset Node) :=
      Walk.vertices_directed_avoid_of_hardInterventionOn
        q_w_Gdov hq_w_Gdov_dir
    -- Abbreviations for the lifted walks in `G`.
    set qv := Walk.liftFromHardIntervention q_v_Gdow with hqv_def
    set qw := Walk.liftFromHardIntervention q_w_Gdov with hqw_def
    have hqv_dir : qv.IsDirectedWalk :=
      Walk.isDirectedWalk_liftFromHardIntervention q_v_Gdow hq_v_Gdow_dir
    have hqw_dir : qw.IsDirectedWalk :=
      Walk.isDirectedWalk_liftFromHardIntervention q_w_Gdov hq_w_Gdov_dir
    have hqv_verts : qv.vertices = q_v_Gdow.vertices :=
      Walk.vertices_liftFromHardIntervention q_v_Gdow
    have hqw_verts : qw.vertices = q_w_Gdov.vertices :=
      Walk.vertices_liftFromHardIntervention q_w_Gdov
    have hqv_len : qv.length = q_v_Gdow.length :=
      Walk.length_liftFromHardIntervention q_v_Gdow
    have hqw_len : qw.length = q_w_Gdov.length :=
      Walk.length_liftFromHardIntervention q_w_Gdov
    have hqv_pos : qv.length ≥ 1 := by rw [hqv_len]; exact hq_v_Gdow_pos
    have hqw_pos : qw.length ≥ 1 := by rw [hqw_len]; exact hq_w_Gdov_pos
    have hqv_head : qv.vertices = c :: qv.vertices.tail :=
      Walk.vertices_eq_head_cons_tail qv
    have hqw_head : qw.vertices = c :: qw.vertices.tail :=
      Walk.vertices_eq_head_cons_tail qw
    have hqv_vs_len : qv.vertices.length = qv.length + 1 := hvert_len_succ qv
    have hqw_vs_len : qw.vertices.length = qw.length + 1 := hvert_len_succ qw
    have hqv_tail_ne_nil : qv.vertices.tail ≠ [] := by
      intro h
      have h1 : qv.vertices.length = 1 := by rw [hqv_head]; simp [h]
      omega
    have hqw_tail_ne_nil : qw.vertices.tail ≠ [] := by
      intro h
      have h1 : qw.vertices.length = 1 := by rw [hqw_head]; simp [h]
      omega
    have hqv_tail_rev_ne_nil : qv.vertices.tail.reverse ≠ [] :=
      fun h => hqv_tail_ne_nil (List.reverse_eq_nil_iff.mp h)
    -- Tail-vertex avoidance, transferred from the intervened to lifted form.
    have hqv_avoid_w : ∀ x ∈ qv.vertices.tail, x ≠ w := by
      intro x hx hxw
      have hx_Gdow : x ∈ q_v_Gdow.vertices.tail := by
        rw [hqv_verts] at hx; exact hx
      exact hq_v_Gdow_avoid x hx_Gdow (by
        rw [Finset.mem_singleton]; exact hxw)
    have hqw_avoid_v : ∀ x ∈ qw.vertices.tail, x ≠ v := by
      intro x hx hxv
      have hx_Gdov : x ∈ q_w_Gdov.vertices.tail := by
        rw [hqw_verts] at hx; exact hx
      exact hq_w_Gdov_avoid x hx_Gdov (by
        rw [Finset.mem_singleton]; exact hxv)
    -- Minimum-length dropLast clauses transferred.
    have hqv_drop_v : v ∉ qv.vertices.dropLast := by
      rw [hqv_verts]; exact hq_v_Gdow_drop
    have hqw_drop_w : w ∉ qw.vertices.dropLast := by
      rw [hqw_verts]; exact hq_w_Gdov_drop
    -- Cross-arm non-memberships: `v ∉ qw.vertices` and `w ∉ qv.vertices`.
    have hv_notin_qw : v ∉ qw.vertices := by
      rw [hqw_head]
      intro hv_in
      rcases List.mem_cons.mp hv_in with hv_eq_c | hv_in_tail
      · exact hc_ne_v hv_eq_c.symm
      · exact hqw_avoid_v v hv_in_tail rfl
    have hw_notin_qv : w ∉ qv.vertices := by
      rw [hqv_head]
      intro hw_in
      rcases List.mem_cons.mp hw_in with hw_eq_c | hw_in_tail
      · exact hc_ne_w hw_eq_c.symm
      · exact hqv_avoid_w w hw_in_tail rfl
    -- The vertex list of the bifurcation walk:
    --   p.vertices = qv.vertices.reverse.dropLast ++ qw.vertices
    --              = qv.vertices.tail.reverse ++ qw.vertices.
    have hp_verts :
        (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
          = qv.vertices.tail.reverse ++ qw.vertices := by
      rw [Walk.vertices_mkBifurcation qv hqv_dir hqv_pos qw]
      -- Only rewrite the LHS to avoid touching `qv.vertices.tail` on the RHS.
      conv_lhs => rw [hqv_head, List.reverse_cons, List.dropLast_concat]
    -- Index arithmetic: `qv.length - 1 + 1 = qv.length` and
    -- `qv.vertices.tail.reverse.length = qv.length`.
    have hidx_succ : qv.length - 1 + 1 = qv.length := by omega
    have hqv_tail_rev_len : qv.vertices.tail.reverse.length = qv.length := by
      rw [List.length_reverse]
      have hlen : qv.vertices.tail.length + 1 = qv.vertices.length := by
        rw [hqv_head]; simp
      omega
    -- Construct the bifurcation walk and discharge each clause of
    -- `IsBifurcationSource`.
    refine ⟨Walk.mkBifurcation qv hqv_dir hqv_pos qw,
            hvw_ne, ?_, ?_, qv.length - 1, ?_, ?_⟩
    · -- (1) `v ∉ p.vertices.tail`.
      rw [hp_verts, List.tail_append_of_ne_nil hqv_tail_rev_ne_nil]
      intro hv_in
      rcases List.mem_append.mp hv_in with hv_left | hv_right
      · -- `v ∈ qv.vertices.tail.reverse.tail`.
        rw [List.tail_reverse, List.mem_reverse] at hv_left
        -- `v ∈ qv.vertices.tail.dropLast → v ∈ qv.vertices.dropLast`
        -- (since `qv.vertices.dropLast = c :: qv.vertices.tail.dropLast`).
        apply hqv_drop_v
        rw [hqv_head, List.dropLast_cons_of_ne_nil hqv_tail_ne_nil]
        exact List.mem_cons.mpr (Or.inr hv_left)
      · exact hv_notin_qw hv_right
    · -- (2) `w ∉ p.vertices.dropLast`.
      rw [hp_verts, List.dropLast_append_of_ne_nil
              (l := qw.vertices) (l' := qv.vertices.tail.reverse)
              (Walk.vertices_ne_nil qw)]
      intro hw_in
      rcases List.mem_append.mp hw_in with hw_left | hw_right
      · -- `w ∈ qv.vertices.tail.reverse → w ∈ qv.vertices.tail → w ∈ qv.vertices`.
        rw [List.mem_reverse] at hw_left
        apply hw_notin_qv
        rw [hqv_head]
        exact List.mem_cons.mpr (Or.inr hw_left)
      · exact hqw_drop_w hw_right
    · -- (3) `IsBifurcationDirectedHingeWithSplit (qv.length - 1)`.
      exact Walk.isBifurcationDirectedHinge_mkBifurcation
        qv hqv_dir hqv_pos qw hqw_dir hqw_pos
    · -- (4) `p.vertices[qv.length - 1 + 1]? = some c`.
      rw [hidx_succ, hp_verts,
          List.getElem?_append_right (hqv_tail_rev_len ▸ Nat.le_refl _)]
      rw [hqv_tail_rev_len, Nat.sub_self]
      rw [hqw_head]
      rfl
-- REFACTOR-BLOCK-ORIGINAL-END: bifurcationAlternative

end CDMG

namespace refactor_CDMG

-- ## Design choice — statement context (refactor twin)
--
-- Three-dash `--- start helper` markers match the convention used
-- across `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
-- `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
-- `CDMGTypes.lean`, `TopologicalOrder.lean`, and
-- `FamilyRelationships.lean` for the `variable` line that binds the
-- implicit parameters into the proof-only helpers and the main
-- theorem wrapped below.  Both `Node : Type*` and `[DecidableEq Node]`
-- are inherited verbatim from `def_3_1`'s refactor twin
-- (`refactor_CDMG`): the `Membership Node (refactor_CDMG Node)`
-- instance from `def_3_2`'s refactor twin (`refactor_instMembership`
-- in `CDMGNotation.lean`) reduces to `Finset.mem` on `G.J ∪ G.V` and
-- so needs `DecidableEq Node`; the `refactor_Walk` recursion in the
-- four walk-class helpers, the `refactor_IsDirectedWalk` /
-- `refactor_IsBifurcationSource` Props in the main theorem body, and
-- the `G.refactor_Anc v` set-builder all transitively rely on
-- `DecidableEq Node` for their `Finset` / `Sym2`-typed membership
-- checks.
-- claim_3_5 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_5 --- end helper

-- ## Proof-only helpers — `HardInterventionOn` walk-lift infrastructure (refactor twins)
--
-- Subtask 1 of the refactor port: the six private helpers below are
-- refactor twins of `mem_of_mem_hardInterventionOn`,
-- `Walk.liftWalkStep_of_hardInterventionOn`,
-- `Walk.liftFromHardIntervention`,
-- `Walk.isDirectedWalk_liftFromHardIntervention`,
-- `Walk.length_liftFromHardIntervention`, and
-- `Walk.vertices_liftFromHardIntervention` (the original `namespace
-- CDMG` block above).  The first five are verbatim copies of the
-- already-solved twins in `AcyclicPreservedUnderDo.lean`'s REPLACEMENT
-- block; the sixth (`refactor_vertices_liftFromHardIntervention`) is
-- new to this row and mirrors the original lemma with the cons-cell
-- pattern shrunk from four args to three.
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the same
-- lemmas as the originals; the refactor only swaps the upstream
-- `CDMG` / `Walk` / `WalkStep` shapes the helpers consume.
-- `refactor_CDMG.L` is retyped to `Finset (Sym2 Node)` (no
-- `hL_symm`), and `refactor_WalkStep` becomes a typed inductive
-- (`.forwardE` / `.backwardE` / `.bidir`) instead of the Prop-valued
-- disjunction.  But step~(0)'s edge-inclusion argument
-- (`E_{do(W)} ⊆ E` and `L_{do(W)} ⊆ L` follow from
-- `Finset.mem_filter`) is structurally unchanged, and so is the
-- walk-lift that uses it.

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: mem_of_mem_hardInterventionOn (was: refactor_mem_of_mem_hardInterventionOn)
/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V` from the TeX statement block:
every node of the intervened CDMG is a node of `G`.  Consumes
`hW : W ⊆ G.J ∪ G.V` to fold the `W`-half of the left disjunct into
`G.J ∪ G.V`.  Body identical to the original — `G.J / G.V / W` are
unchanged by the `cdmg_typed_edges` refactor (only `L`'s type
changed), so the carrier-matching computation reads verbatim. -/
private lemma refactor_mem_of_mem_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {v : Node}
    (h : v ∈ G.refactor_hardInterventionOn W hW) : v ∈ G := by
  -- `v ∈ G.refactor_hardInterventionOn W hW` reduces by the
  -- `refactor_instMembership` instance (`def_3_2`'s refactor twin,
  -- `CDMGNotation.lean`) to `v ∈ (G.J ∪ W) ∪ (G.V \ W)`.
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJW | hVW
  · rcases Finset.mem_union.mp hJW with hJ | hWmem
    · exact Finset.mem_union_left _ hJ
    · exact hW hWmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1
-- REFACTOR-BLOCK-REPLACEMENT-END: mem_of_mem_hardInterventionOn

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.liftWalkStep_of_hardInterventionOn (was: refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn)
/-- Per-edge content of step~(0): any typed `refactor_WalkStep` in
`G.refactor_hardInterventionOn W hW` is also a typed `refactor_WalkStep`
in `G`.  Under the refactor, `refactor_WalkStep` is a `Type _`-valued
inductive rather than a `Prop`, so this is a `def` (not a `lemma`)
that translates each constructor by stripping the `Finset.filter`
predicate via `Finset.mem_filter.mp`.

* `.forwardE h` and `.backwardE h` strip the `e.2 ∉ W` clause from
  the directed-edge filter and re-emit the same constructor.
* `.bidir h` strips the `∀ v ∈ s, v ∉ W` clause from the bidirected-
  edge filter and re-emits `.bidir`.  Under the `Sym2` encoding of
  `refactor_CDMG.L`, no symmetrisation step is needed — `s(u, v) =
  s(v, u)` is definitional, so the constructor preserves the
  unordered-pair identity verbatim. -/
private def refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {u v : Node} :
    refactor_WalkStep (G.refactor_hardInterventionOn W hW) u v →
      refactor_WalkStep G u v
  | .forwardE h  => .forwardE  ((Finset.mem_filter.mp h).1)
  | .backwardE h => .backwardE ((Finset.mem_filter.mp h).1)
  | .bidir h     => .bidir     ((Finset.mem_filter.mp h).1)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.liftWalkStep_of_hardInterventionOn

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.liftFromHardIntervention (was: refactor_Walk.refactor_liftFromHardIntervention)
/-- Step~(0)'s walk-lift, as a recursive function on `refactor_Walk`s:
a walk in the intervened CDMG `G.refactor_hardInterventionOn W hW`
is *the same tuple* viewed as a walk in `G`.  Each `cons` cell keeps
its middle vertex `v`; the typed WalkStep witness is replaced by its
lift through `refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn`.

The cons-cell signature change is structural: under
`refactor_Walk.cons` the cons cell takes three explicit args
(`v`, `s`, `p`) rather than the original four (`v`, `a`, `h`, `p`).
The `a : Node × Node` is gone (the WalkStep carries its endpoints in
its type indices), and the Prop witness `h` is replaced by the typed
data `s : refactor_WalkStep G u v`. -/
private def refactor_Walk.refactor_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node},
      refactor_Walk (G.refactor_hardInterventionOn W hW) u v →
        refactor_Walk G u v
  | _, _, .nil w hw =>
      refactor_Walk.nil w (refactor_mem_of_mem_hardInterventionOn hw)
  | _, _, .cons vMid s p =>
      refactor_Walk.cons vMid
        (refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn
          (hW := hW) s)
        (refactor_Walk.refactor_liftFromHardIntervention p)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.liftFromHardIntervention

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isDirectedWalk_liftFromHardIntervention (was: refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention)
/-- The walk-lift preserves `refactor_IsDirectedWalk`.

Under the refactor, `refactor_IsDirectedWalk` pattern-matches on the
typed WalkStep constructor: a `.forwardE` step advances the recursion
on the tail, while `.backwardE` and `.bidir` reduce to `False`
definitionally.  Consequently the proof simplifies from the
original's `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp` triple-conjunction
to a structural case-split on the typed step — the `.forwardE` case
recurses with no rewrite, and the other two close by `hp.elim`
(since `hp : False` for those constructors). -/
private lemma refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : refactor_Walk (G.refactor_hardInterventionOn W hW) u v),
      p.refactor_IsDirectedWalk →
        (refactor_Walk.refactor_liftFromHardIntervention
          (hW := hW) p).refactor_IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, hp =>
      refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention p hp
  | _, _, .cons _ (.backwardE _) _, hp => hp.elim
  | _, _, .cons _ (.bidir _) _, hp => hp.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isDirectedWalk_liftFromHardIntervention

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_liftFromHardIntervention (was: refactor_Walk.refactor_length_liftFromHardIntervention)
/-- The walk-lift preserves `refactor_length`: each `cons` cell of
the input walk produces exactly one `cons` cell of the output walk,
with the same middle vertex / typed WalkStep data.  Body is the
original with the cons-cell pattern shrunk from four args to three
(the `a : Node × Node` is gone — see the design block on
`refactor_Walk.cons` in `Walks.lean`). -/
private lemma refactor_Walk.refactor_length_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : refactor_Walk (G.refactor_hardInterventionOn W hW) u v),
      (refactor_Walk.refactor_liftFromHardIntervention
        (hW := hW) p).refactor_length = p.refactor_length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p =>
      congrArg (· + 1)
        (refactor_Walk.refactor_length_liftFromHardIntervention p)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_liftFromHardIntervention

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_liftFromHardIntervention (was: refactor_Walk.refactor_vertices_liftFromHardIntervention)
/-- The walk-lift preserves the underlying `refactor_vertices` list.
Each `cons` cell of the input keeps its middle vertex `v` verbatim
under the lift, so the induced list of vertices is byte-identical.
The `nil` case reduces to `[v] = [v]` definitionally; the `cons` case
is `u :: (lift p).refactor_vertices = u :: p.refactor_vertices` via
`congrArg (u :: ·) ih`.

Refactor port: structurally identical to the original
`Walk.vertices_liftFromHardIntervention` in the `namespace CDMG`
block above, modulo the cons-cell pattern shrinking from four args
(`vMid a h p`) to three (`vMid s p`) — see the design block on
`refactor_Walk.cons` in `Walks.lean`.  Used by the (⇐) direction's
clause~(a) / clause~(e) end-node-uniqueness bookkeeping when lifting
the minimum-length directed arms `q_v`, `q_w` back to `G`. -/
private lemma refactor_Walk.refactor_vertices_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : refactor_Walk (G.refactor_hardInterventionOn W hW) u v),
      (refactor_Walk.refactor_liftFromHardIntervention
        (hW := hW) p).refactor_vertices = p.refactor_vertices
  | _, _, .nil _ _ => rfl
  | u, _, .cons _ _ p =>
      congrArg (u :: ·)
        (refactor_Walk.refactor_vertices_liftFromHardIntervention p)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_liftFromHardIntervention

-- ## Proof-only helpers — Walk concatenation infrastructure (refactor twins)
--
-- Subtask 2 of the refactor port: the five private helpers below are
-- refactor twins of `Walk.comp`, `Walk.length_comp`,
-- `Walk.isDirectedWalk_comp`, `Walk.vertices_ne_nil`, and
-- `Walk.vertices_comp` (the original `namespace CDMG` block above).
-- The first three are verbatim copies of the already-solved twins in
-- `AcyclicIffTopologicalOrder.lean`'s REPLACEMENT block; the last two
-- (`refactor_vertices_ne_nil`, `refactor_vertices_comp`) are new to
-- this row and mirror the originals with the cons-cell pattern shrunk
-- from four args to three.
--
-- *Mathematical content unchanged (TL;DR).*  Concatenation does not
-- inspect the channel — it threads the typed `refactor_WalkStep`
-- through the recursion verbatim — so the structural recursion shape
-- of the original `Walk.comp` / `length_comp` / `vertices_comp` is
-- preserved.  Only `Walk.isDirectedWalk_comp` simplifies: the
-- original's `obtain ⟨_, _, hp_dir⟩` triple-conjunction is replaced
-- by a structural case-split on the typed step, with `.backwardE`
-- and `.bidir` closed by `hp.elim` since `refactor_IsDirectedWalk`
-- returns `False` on those constructors definitionally.

-- *Why this helper exists.*  The (⇐) direction's `mkBifurcation`
-- candidate walk is built as `(reverseDirected q_v).comp q_w` — a
-- concatenation of the reversed left arm and the right arm.
-- `comp_assoc` (subtask 6a) re-associates the resulting walks for
-- predicate matching.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Concatenation does
-- not inspect the channel, so the cons recursion passes the typed
-- `s` through verbatim — one-for-one field rename `a, h ↦ s`, body
-- otherwise identical to the original.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.comp (was: refactor_Walk.refactor_comp)
/-- Concatenate two `refactor_Walk`s `p : u → v` and `q : v → w` into
a walk `u → w`.  The `nil` case forwards `q` unchanged; the `cons`
case recurses on the tail and re-attaches the head step. -/
private def refactor_Walk.refactor_comp {G : refactor_CDMG Node} :
    ∀ {u v w : Node}, refactor_Walk G u v → refactor_Walk G v w →
      refactor_Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v s p, q => .cons v s (p.refactor_comp q)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.comp

-- *Why this helper exists.*  Length arithmetic on the candidate
-- bifurcation walk and the truncated directed arms is the main
-- consumer of this lemma — `refactor_length_mkBifurcation` chains
-- this with `refactor_length_reverseDirected` to express the
-- candidate's length as `q_v.refactor_length + q_w.refactor_length`.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the walk spine plus `Nat` arithmetic — the typed
-- step never enters the case split.  Body is the original with
-- `length` / `comp` swapped for `refactor_length` / `refactor_comp`.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_comp (was: refactor_Walk.refactor_length_comp)
/-- The `refactor_length` of `p.refactor_comp q` is `p.refactor_length
+ q.refactor_length`. -/
private lemma refactor_Walk.refactor_length_comp {G : refactor_CDMG Node} :
    ∀ {u v w : Node} (p : refactor_Walk G u v) (q : refactor_Walk G v w),
      (p.refactor_comp q).refactor_length =
        p.refactor_length + q.refactor_length
  | _, _, _, .nil _ _, q => by
      simp [refactor_Walk.refactor_comp, refactor_Walk.refactor_length]
  | _, _, _, .cons _ _ p, q => by
      simp [refactor_Walk.refactor_comp, refactor_Walk.refactor_length,
            refactor_Walk.refactor_length_comp p q,
            Nat.add_comm, Nat.add_left_comm]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_comp

-- *Why this helper exists.*  The (⇐) direction's right-arm of the
-- candidate bifurcation is the concatenation `q_v.comp q_w` of two
-- directed arms (after one is reversed for the directed-hinge
-- backbone).  Without this lemma, directedness of each individual
-- arm would not transfer to the concatenated walk.
--
-- *Typed-WalkStep shape: simplifies.*  The original's
-- `obtain ⟨ha_eq, ha_E, hq_dir⟩ := hp` plus `⟨h1, h2, recurse⟩`
-- reassembly is replaced by a structural recursion on the typed
-- step `s`: `.forwardE _` recurses on the tail's witness, while
-- `.backwardE _` / `.bidir _` close by `hp.elim` (their
-- `refactor_IsDirectedWalk` is `False` definitionally — discharged
-- by structural impossibility, not by hand).
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isDirectedWalk_comp (was: refactor_Walk.refactor_isDirectedWalk_comp)
/-- Directedness is preserved under `refactor_comp`: concatenating
two directed walks produces a directed walk. -/
private lemma refactor_Walk.refactor_isDirectedWalk_comp {G : refactor_CDMG Node} :
    ∀ {u v w : Node} (p : refactor_Walk G u v) (q : refactor_Walk G v w),
      p.refactor_IsDirectedWalk → q.refactor_IsDirectedWalk →
        (p.refactor_comp q).refactor_IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ (.forwardE _) p, q, hp, hq =>
      refactor_Walk.refactor_isDirectedWalk_comp p q hp hq
  | _, _, _, .cons _ (.backwardE _) _, _, hp, _ => hp.elim
  | _, _, _, .cons _ (.bidir _) _, _, hp, _ => hp.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isDirectedWalk_comp

-- *Why this helper exists.*  `refactor_vertices_comp`'s `cons` case
-- needs `(u :: p.refactor_vertices).dropLast = u ::
-- p.refactor_vertices.dropLast`, which requires
-- `p.refactor_vertices ≠ []` to apply
-- `List.dropLast_cons_of_ne_nil`.  This lemma supplies the witness
-- structurally — every walk has at least its source vertex.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Both arms reduce by
-- `simp [refactor_vertices]` — the `nil` arm to `[v] ≠ []`, the
-- `cons` arm to `u :: rest ≠ []` — neither inspects the typed step.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_ne_nil (was: refactor_Walk.refactor_vertices_ne_nil)
/-- Auxiliary: every walk's `refactor_vertices` list is non-empty.
The `nil` walk gives `[v]`; every `cons` cell prepends a new head
vertex. -/
private lemma refactor_Walk.refactor_vertices_ne_nil {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v), p.refactor_vertices ≠ []
  | _, _, .nil _ _ => by simp [refactor_Walk.refactor_vertices]
  | _, _, .cons _ _ _ => by simp [refactor_Walk.refactor_vertices]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_ne_nil

-- *Why this helper exists.*  The (⇐) direction's end-node /
-- interior-membership reasoning on `mkBifurcation`'s candidate walk
-- (predicates like `v ∉ p.refactor_vertices.tail` or `v ∈
-- p.refactor_vertices`) reduces to per-arm membership statements
-- via this equation.  Without it, vertex-list bookkeeping on the
-- concatenated walk would not factor through the constituent arms'
-- bookkeeping.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the walk spine plus `List` lemmas.  Body is the
-- original with `vertices` / `comp` / `vertices_ne_nil` swapped for
-- `refactor_vertices` / `refactor_comp` /
-- `refactor_vertices_ne_nil`, and the cons-cell pattern shrunk
-- from four args (`vMid a h p`) to three (`vMid s p`).
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_comp (was: refactor_Walk.refactor_vertices_comp)
/-- `refactor_comp` interacts with `refactor_vertices` by dropping
the last vertex of the left arm and concatenating with the full
vertex list of the right arm.  The `nil` case closes by `rfl`
(`[v].dropLast = []` and `[] ++ _ = _` are both definitionally
true); the `cons` case applies the inductive hypothesis and uses
`List.dropLast_cons_of_ne_nil
(refactor_Walk.refactor_vertices_ne_nil p)` to unfold
`(u :: p.refactor_vertices).dropLast`. -/
private lemma refactor_Walk.refactor_vertices_comp {G : refactor_CDMG Node} :
    ∀ {u v w : Node} (p : refactor_Walk G u v) (q : refactor_Walk G v w),
      (p.refactor_comp q).refactor_vertices =
        p.refactor_vertices.dropLast ++ q.refactor_vertices
  | _, _, _, .nil _ _, _ => rfl
  | _, _, _, .cons _ _ p, q => by
      have hne : p.refactor_vertices ≠ [] :=
        refactor_Walk.refactor_vertices_ne_nil p
      simp [refactor_Walk.refactor_comp, refactor_Walk.refactor_vertices,
            refactor_Walk.refactor_vertices_comp p q,
            List.dropLast_cons_of_ne_nil hne]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_comp

-- ## Proof-only helpers — `HardInterventionOn` walk-lift infrastructure (subtask 3, refactor twins)
--
-- Subtask 3 of the refactor port: the five private helpers below are
-- refactor twins of `Walk.head_mem_vertices`,
-- `Walk.vertices_eq_head_cons_tail`,
-- `Walk.vertices_directed_avoid_of_hardInterventionOn`,
-- `Walk.liftTo_hardInterventionOn`, and
-- `Walk.isDirectedWalk_liftTo_hardInterventionOn` (the original
-- `namespace CDMG` block above).  They complete the directional
-- counterpart of subtask 1's `liftFromHardIntervention` family:
-- *upgrade* a directed walk `p : refactor_Walk G u v` (in the
-- un-intervened CDMG) to a directed walk in
-- `G.refactor_hardInterventionOn W hW`, provided every non-source
-- vertex of `p` avoids `W`.  Consumed by the (⇐) direction's
-- candidate-bifurcation construction in
-- `refactor_bifurcationAlternative`.
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the same
-- lemmas as the originals; the refactor only swaps the upstream
-- `CDMG` / `Walk` / `WalkStep` shapes the helpers consume.  Two
-- structural simplifications fall out of the typed-step encoding:
--
-- * The cons-cell now takes three explicit args (`vMid`, `s`, `p'`)
--   rather than four (`vMid`, `a`, `h`, `p'`) — the `a : Node × Node`
--   is gone (endpoints live in the WalkStep's type indices).
-- * `refactor_IsDirectedWalk` returns `False` on `.backwardE` /
--   `.bidir` steps definitionally, so the original's
--   `obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` triple-conjunction is
--   replaced by a structural case-split on the typed WalkStep: the
--   `.forwardE` arm advances the recursion (and reads the underlying
--   `(u, vMid) ∈ G.E` witness directly from the constructor argument
--   `h_E`), while `.backwardE` and `.bidir` close by `hp_dir.elim`
--   (since `hp_dir : False` on those constructors).
-- * The `(u, vMid) ∈ (G.refactor_hardInterventionOn W hW).E` predicate
--   directly equals `(u, vMid) ∈ G.E ∧ (u, vMid).2 ∉ W` via
--   `Finset.mem_filter`, so `vMid ∉ W` reads off
--   `(Finset.mem_filter.mp h).2` without an intermediate
--   `rw [ha_eq]` step.

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.head_mem_vertices (was: refactor_Walk.refactor_head_mem_vertices)
/-- Auxiliary: the source `u` of a walk `p : refactor_Walk G u v` is
the head of `p.refactor_vertices`, hence lies in `p.refactor_vertices`.
The `nil` case unfolds to `u ∈ [u]`; the `cons` case unfolds to
`u ∈ u :: rest`; both close by `simp [refactor_Walk.refactor_vertices]`.
Used by `refactor_liftTo_hardInterventionOn`'s `cons` recursion to
extract `vMid ∉ W` from the cons-walk's `refactor_vertices.tail`-
avoidance hypothesis (the cons-walk's `.refactor_vertices.tail`
definitionally equals `p'.refactor_vertices`, whose head is `vMid`).

Refactor port: structurally identical to the original
`Walk.head_mem_vertices`, modulo the cons-cell pattern shrinking from
four args (`vMid a h p`) to three (`vMid s p`) — see the design block
on `refactor_Walk.cons` in `Walks.lean`. -/
private lemma refactor_Walk.refactor_head_mem_vertices {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v), u ∈ p.refactor_vertices
  | _, _, .nil _ _ => by simp [refactor_Walk.refactor_vertices]
  | _, _, .cons _ _ _ => by simp [refactor_Walk.refactor_vertices]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.head_mem_vertices

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_eq_head_cons_tail (was: refactor_Walk.refactor_vertices_eq_head_cons_tail)
/-- Auxiliary: every walk's `refactor_vertices` list factors as
`source :: tail`.  The `nil` case: `[u].tail = []` and `u :: [] = [u]`,
so the equality is definitional.  The `cons` case:
`(u :: p'.refactor_vertices).tail = p'.refactor_vertices`, so
`u :: ((cons _ _ p').refactor_vertices.tail) = u :: p'.refactor_vertices
= (cons _ _ p').refactor_vertices`, again definitional.  Used by
`refactor_vertices_directed_avoid_of_hardInterventionOn`'s `cons`
case to split `x ∈ p'.refactor_vertices` into "x equals the source
vertex `vMid`" / "x lies in `p'.refactor_vertices.tail`" via
`List.mem_cons`.

Refactor port: structurally identical to the original
`Walk.vertices_eq_head_cons_tail`, modulo the cons-cell pattern
shrinking from four args to three. -/
private lemma refactor_Walk.refactor_vertices_eq_head_cons_tail {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v),
      p.refactor_vertices = u :: p.refactor_vertices.tail
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ => rfl
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_eq_head_cons_tail

-- *Why this helper exists.*  Subtask 3a: every vertex of a *directed*
-- walk in `G.refactor_hardInterventionOn W hW`, except the source,
-- avoids `W`.  The `.tail` carve-out is load-bearing: the source `u =
-- u_0` is unconstrained — it may or may not be in `W`.  Only the
-- heads of the edges (positions `1, 2, …, n` of `refactor_vertices`)
-- must avoid `W`, because `(u_i, u_{i+1}) ∈ E_{do(W)}` forces
-- `u_{i+1} ∉ W` via the `e.2 ∉ W` clause of `def_3_10` item iii's
-- `Finset.filter`.  Consumed by the (⇒) direction's avoidance check
-- when lifting the minimum-length directed arms back through the
-- intervention's filter.
--
-- *Typed-WalkStep shape: simplifies.*  The original obtains the
-- conjunction `⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` and reads `vMid ∉ W`
-- off `(Finset.mem_filter.mp ha_E).2` after `rw [ha_eq]` rewrites
-- `a` to `(u, vMid)`.  Under the typed `refactor_WalkStep`, only
-- `.forwardE h` survives `refactor_IsDirectedWalk`; the constructor
-- argument `h : (u, vMid) ∈ (G.refactor_hardInterventionOn W hW).E`
-- already filters on `e.2 ∉ W`, so `(Finset.mem_filter.mp h).2`
-- directly reads `vMid ∉ W` with no intermediate `rw [ha_eq]` step.
-- The other two constructors close by `hp_dir.elim` (the
-- `refactor_IsDirectedWalk` clauses for `.backwardE` and `.bidir`
-- reduce to `False` definitionally).
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_directed_avoid_of_hardInterventionOn (was: refactor_Walk.refactor_vertices_directed_avoid_of_hardInterventionOn)
/-- **Subtask 3a:** every vertex of a *directed* walk in
`G.refactor_hardInterventionOn W hW`, except the source, avoids `W`.
Proof: induction on `p` with a structural case-split on the typed
WalkStep.  See the design block above for the simplification vs the
original. -/
private lemma refactor_Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : refactor_Walk (G.refactor_hardInterventionOn W hW) u v),
      p.refactor_IsDirectedWalk → ∀ x ∈ p.refactor_vertices.tail, x ∉ W
  | _, _, .nil _ _, _, _, hx => by simp [refactor_Walk.refactor_vertices] at hx
  | _, _, .cons vMid (.forwardE h) p', hp_dir, x, hx => by
      change x ∈ p'.refactor_vertices at hx
      have hvMid_notW : vMid ∉ W := (Finset.mem_filter.mp h).2
      rw [refactor_Walk.refactor_vertices_eq_head_cons_tail p'] at hx
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · exact hvMid_notW
      · exact refactor_Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
          p' hp_dir x hx_tail
  | _, _, .cons _ (.backwardE _) _, hp_dir, _, _ => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, hp_dir, _, _ => hp_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_directed_avoid_of_hardInterventionOn

-- *Why this helper exists.*  Subtask 3b: rebuild a directed walk
-- `p : refactor_Walk G u v` in the intervened CDMG
-- `G.refactor_hardInterventionOn W hW`, provided the source `u` is
-- itself a node of the intervention and every non-source vertex of
-- `p` avoids `W`.  Consumed by the (⇒) direction's final-arm
-- transport in `refactor_bifurcationAlternative`'s reverse direction.
--
-- *Typed-WalkStep shape: simplifies.*  The original built the
-- `WalkStep` witness via the disjunctive
-- `Or.inl ⟨hp_dir.1, Or.inl (Finset.mem_filter.mpr ⟨hp_dir.2.1, _⟩)⟩`
-- shape against the Prop-valued ordered-pair disjunction
-- `(a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∨ (a = (v, u) ∧ a ∈ G.E)`.
-- Under the typed `refactor_WalkStep`, the cons-cell carries
-- `s : refactor_WalkStep G u vMid` directly.  Only `.forwardE h_E`
-- with `h_E : (u, vMid) ∈ G.E` survives `refactor_IsDirectedWalk`
-- (the other two close by `hp_dir.elim`), and the intervened-edge
-- witness becomes `.forwardE (Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩)`
-- — a direct constructor call with no `Or.inl` / `rw [ha_eq]`
-- packaging.  Helper computations `hvMid_V`, `hvMid_inHard`,
-- `hp'_avoid` carry over verbatim modulo the rename
-- `hp_dir.2.1 ↦ h_E` (the typed constructor's argument).
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.liftTo_hardInterventionOn (was: refactor_Walk.refactor_liftTo_hardInterventionOn)
/-- **Subtask 3b:** rebuild a directed walk `p : refactor_Walk G u v`
in the intervened CDMG `G.refactor_hardInterventionOn W hW`, provided
the source `u` is itself a node of the intervention and every
non-source vertex of `p` avoids `W`.

Cell-by-cell: each `cons` step's typed WalkStep is built from the
`.forwardE`-extracted edge witness `h_E : (u, vMid) ∈ G.E` (the only
constructor compatible with `refactor_IsDirectedWalk`) and the
head-of-tail-avoidance `vMid ∉ W` (extracted from `hp_avoid` via
`refactor_head_mem_vertices`).  These two facts package into
`Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩ : (u, vMid) ∈
(G.refactor_hardInterventionOn W hW).E`, which is the argument to
the `.forwardE` constructor of the new typed WalkStep. -/
private def refactor_Walk.refactor_liftTo_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : refactor_Walk G u v),
      u ∈ G.refactor_hardInterventionOn W hW →
      p.refactor_IsDirectedWalk →
      (∀ x ∈ p.refactor_vertices.tail, x ∉ W) →
      refactor_Walk (G.refactor_hardInterventionOn W hW) u v
  | _, _, .nil v _, hu, _, _ => refactor_Walk.nil v hu
  | u, _, .cons vMid (.forwardE h_E) p', _, hp_dir, hp_avoid =>
      have hvMid_notW : vMid ∉ W :=
        hp_avoid vMid (refactor_Walk.refactor_head_mem_vertices p')
      have hvMid_V : vMid ∈ G.V := (G.hE_subset h_E).2
      have hvMid_inHard : vMid ∈ G.refactor_hardInterventionOn W hW := by
        change vMid ∈ (G.J ∪ W) ∪ (G.V \ W)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvMid_V, hvMid_notW⟩)
      have hStepFiltered : (u, vMid) ∈ (G.refactor_hardInterventionOn W hW).E :=
        Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩
      have hp'_avoid : ∀ x ∈ p'.refactor_vertices.tail, x ∉ W := fun y hy =>
        hp_avoid y (List.mem_of_mem_tail hy)
      refactor_Walk.cons vMid (.forwardE hStepFiltered)
        (refactor_Walk.refactor_liftTo_hardInterventionOn p'
          hvMid_inHard hp_dir hp'_avoid)
  | _, _, .cons _ (.backwardE _) _, _, hp_dir, _ => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, _, hp_dir, _ => hp_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.liftTo_hardInterventionOn

-- *Why this helper exists.*  Subtask 3c: the
-- `refactor_liftTo_hardInterventionOn` lift preserves
-- `refactor_IsDirectedWalk`.  Consumed by the (⇒) direction's
-- final-arm transport, paired with the lift itself.
--
-- *Typed-WalkStep shape: simplifies.*  The original discharged the
-- three-conjunct goal `⟨a = (u, vMid), a ∈ E_intervened,
-- (lift_tail).IsDirectedWalk⟩` via
-- `refine ⟨hp_dir.1, ?_, ?_⟩` + per-conjunct sub-proofs.  Under the
-- typed refactor, the new cons cell is
-- `.cons vMid (.forwardE hStepFiltered) (lift p')`, whose
-- `refactor_IsDirectedWalk` reduces definitionally to
-- `(lift p').refactor_IsDirectedWalk` — a single goal, discharged by
-- the recursive IH on `p'`.  The `.backwardE` / `.bidir` cases close
-- by `hp_dir.elim`.
--
-- *Reproduction of `liftTo`'s `have` bindings.*  Per the cross-helper
-- design note at L420–427 of this file, the IH of this lemma must
-- unify with the recursive call inside `refactor_liftTo`'s body, so
-- the proof reproduces the same `have hvMid_notW`, `have hvMid_V`,
-- `have hvMid_inHard`, `have hp'_avoid` bindings verbatim.  Proof
-- irrelevance bridges any syntactic differences in how the proofs
-- are written, but reproducing the bindings keeps the unification
-- local and robust.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isDirectedWalk_liftTo_hardInterventionOn (was: refactor_Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn)
/-- **Subtask 3c:** the `refactor_liftTo_hardInterventionOn` lift
preserves `refactor_IsDirectedWalk`. -/
private lemma refactor_Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : refactor_Walk G u v)
      (hu : u ∈ G.refactor_hardInterventionOn W hW)
      (hp_dir : p.refactor_IsDirectedWalk)
      (hp_avoid : ∀ x ∈ p.refactor_vertices.tail, x ∉ W),
      (refactor_Walk.refactor_liftTo_hardInterventionOn
        (hW := hW) p hu hp_dir hp_avoid).refactor_IsDirectedWalk
  | _, _, .nil _ _, _, _, _ => trivial
  | _, _, .cons vMid (.forwardE h_E) p', _, hp_dir, hp_avoid => by
      have hvMid_notW : vMid ∉ W :=
        hp_avoid vMid (refactor_Walk.refactor_head_mem_vertices p')
      have hvMid_V : vMid ∈ G.V := (G.hE_subset h_E).2
      have hvMid_inHard : vMid ∈ G.refactor_hardInterventionOn W hW := by
        change vMid ∈ (G.J ∪ W) ∪ (G.V \ W)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvMid_V, hvMid_notW⟩)
      have hp'_avoid : ∀ x ∈ p'.refactor_vertices.tail, x ∉ W := fun y hy =>
        hp_avoid y (List.mem_of_mem_tail hy)
      exact refactor_Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
        p' hvMid_inHard hp_dir hp'_avoid
  | _, _, .cons _ (.backwardE _) _, _, hp_dir, _ => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, _, hp_dir, _ => hp_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isDirectedWalk_liftTo_hardInterventionOn

-- ## Proof-only helpers — `Walk.truncateAtFirst` infrastructure (subtask 4, refactor twins)
--
-- Subtask 4 of the refactor port: the eight private helpers below are
-- refactor twins of `WalkStep.source_mem`, `Walk.truncateAtFirst`,
-- `Walk.truncateAtFirst_target_eq`, `Walk.length_truncateAtFirst_le`,
-- `Walk.isDirectedWalk_truncateAtFirst`,
-- `Walk.mem_vertices_of_mem_dropLast`,
-- `Walk.length_truncateAtFirst_lt_of_mem_dropLast`, and
-- `exists_directed_walk_v_not_in_dropLast` (the original `namespace
-- CDMG` block above).  They build the minimum-length-directed-walk
-- truncation machinery consumed by the (⇐) direction of
-- `refactor_bifurcationAlternative`.
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the same
-- lemmas as the originals; the refactor swaps the upstream `CDMG` /
-- `Walk` / `WalkStep` shapes the helpers consume.  Three structural
-- simplifications fall out of the typed-step encoding:
--
-- * `refactor_WalkStep.refactor_source_mem` case-splits the typed
--   constructor `s : refactor_WalkStep G u v` into `.forwardE` /
--   `.backwardE` / `.bidir`.  The `.forwardE h_E` arm reads `u ∈ G.J ∪
--   G.V` off `(G.hE_subset h_E).1` directly (no `rw [ha_eq]`).  The
--   `.backwardE h_E` arm reads `u ∈ G.V` off `(G.hE_subset h_E).2` and
--   coerces via `Finset.mem_union_right`.  The `.bidir h_L` arm — with
--   `h_L : s(u, v) ∈ G.L` — invokes `G.hL_subset h_L (Sym2.mem_mk_left
--   u v) : u ∈ G.V` (the canonical Mathlib name for "the first slot of
--   `s(u, v)` is a member of `s(u, v)`"), then `Finset.mem_union_right`.
--   The `Sym2.Mem`-based shape of `refactor_CDMG.hL_subset`
--   (`∀ s ∈ L, ∀ v ∈ s, v ∈ V`) lines up with `Sym2.mem_mk_left u v`
--   one-step rather than the pre-refactor `(G.hL_subset ha_L).1` plus
--   `rw [ha_eq]` two-step.
--
-- * The cons-cell pattern shrinks from four args (`vMid a hStep p'`)
--   to three (`vMid s p'`) — the `a : Node × Node` is gone (endpoints
--   live in the typed WalkStep's type indices).  All five truncation
--   helpers consume `s` instead of `(a, hStep)`.
--
-- * `refactor_IsDirectedWalk` returns `False` on `.backwardE` /
--   `.bidir` steps definitionally, so the original's
--   `obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` triple-conjunction is
--   replaced in `refactor_isDirectedWalk_truncateAtFirst` by a
--   structural case-split on `s`: the `.forwardE` arm advances the
--   recursion (and the cons-cell's `refactor_IsDirectedWalk` reduces
--   definitionally to `p'.refactor_IsDirectedWalk`, supplying the
--   IH's hypothesis without an `obtain`), while `.backwardE` and
--   `.bidir` close by `hp_dir.elim`.

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: WalkStep.source_mem (was: refactor_WalkStep.refactor_source_mem)
/-- Auxiliary: the source vertex of a `refactor_WalkStep` lies in `G`.
Used by `refactor_Walk.refactor_truncateAtFirst`'s `t = u` branch in
the `cons` arm to recover `u ∈ G` from `s : refactor_WalkStep G u
vMid` — the `cons`-pattern data does not carry `u ∈ G` directly (only
`refactor_Walk.nil` has that field).  The proof pattern-matches `s`
against its three constructors and reads off `u`'s membership from the
appropriate `G.hE_subset` / `G.hL_subset` projection.
* `.forwardE h_E`: `h_E : (u, vMid) ∈ G.E`, so `(G.hE_subset h_E).1 :
  u ∈ G.J ∪ G.V` lands in `u ∈ G` directly.
* `.backwardE h_E`: `h_E : (vMid, u) ∈ G.E`, so `(G.hE_subset h_E).2 :
  u ∈ G.V` lifts to `u ∈ G.J ∪ G.V` via `Finset.mem_union_right`.
* `.bidir h_L`: `h_L : s(u, vMid) ∈ G.L`; `G.hL_subset h_L : ∀ ⦃x⦄,
  x ∈ s(u, vMid) → x ∈ G.V`, applied to `Sym2.mem_mk_left u vMid : u ∈
  s(u, vMid)`, gives `u ∈ G.V`, then `Finset.mem_union_right`. -/
private lemma refactor_WalkStep.refactor_source_mem {G : refactor_CDMG Node}
    {u v : Node} (h : refactor_WalkStep G u v) : u ∈ G := by
  change u ∈ G.J ∪ G.V
  match h with
  | .forwardE h_E => exact (G.hE_subset h_E).1
  | .backwardE h_E => exact Finset.mem_union_right _ (G.hE_subset h_E).2
  | .bidir h_L =>
      exact Finset.mem_union_right _ (G.hL_subset h_L (Sym2.mem_mk_left u v))
-- REFACTOR-BLOCK-REPLACEMENT-END: WalkStep.source_mem

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.truncateAtFirst (was: refactor_Walk.refactor_truncateAtFirst)
/-- **Subtask 4a:** truncate `p : refactor_Walk G u v` at the *first*
occurrence of `t` in `p.refactor_vertices`, returning a `Σ' (v' :
Node), refactor_Walk G u v'` whose target `v'` equals `t` (the equality
is the content of `refactor_truncateAtFirst_target_eq` immediately
below).

* `nil` arm: `p.refactor_vertices = [v]`, so `h : t ∈ [v]` forces
  `t = v`; the truncation is the trivial walk `⟨v, .nil v hv⟩`.
* `cons` arm: `p = .cons vMid s p'`, `p.refactor_vertices = u ::
  p'.refactor_vertices`.  Case-split on `t = u`:
    * If `t = u`: the truncated walk is `⟨u, .nil u _⟩`; the needed
      `u ∈ G` is extracted from `s` via
      `refactor_WalkStep.refactor_source_mem`.
    * If `t ≠ u`: recurse on `p'` and re-prepend the head step with
      `refactor_Walk.cons`.

Refactor port: cons-cell pattern shrinks from four args to three
(`vMid s p'` not `vMid a hStep p'`); the WalkStep witness `s` threads
through the `cons` re-build directly instead of the pair
`(a, hStep)`. -/
private def refactor_Walk.refactor_truncateAtFirst {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v) (t : Node)
      (_h : t ∈ p.refactor_vertices),
      Σ' (v' : Node), refactor_Walk G u v'
  | _, _, .nil w hw, _, _ => ⟨w, .nil w hw⟩
  | u, _, .cons vMid s p', t, h =>
      if h_eq : t = u then
        ⟨u, .nil u (refactor_WalkStep.refactor_source_mem s)⟩
      else
        have h_in_p' : t ∈ p'.refactor_vertices := by
          have h' : t ∈ u :: p'.refactor_vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        let res := refactor_Walk.refactor_truncateAtFirst p' t h_in_p'
        ⟨res.1, .cons vMid s res.2⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.truncateAtFirst

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.truncateAtFirst_target_eq (was: refactor_Walk.refactor_truncateAtFirst_target_eq)
/-- **Subtask 4b:** the truncated walk's target (`Σ'.fst`) equals `t`.
Consumers use this equality to convert the
`refactor_Walk G u (refactor_truncateAtFirst p t h).1` into a
`refactor_Walk G u t` (via `subst` on the fst-equality).  Proved by
structural recursion mirroring `refactor_truncateAtFirst`'s shape:
`nil` closes by `List.mem_singleton`; the `cons` case-splits on
`t = u` and recurses on `p'` in the `t ≠ u` branch.  Cons-cell
pattern shrinks from four args to three. -/
private lemma refactor_Walk.refactor_truncateAtFirst_target_eq {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v) (t : Node)
      (h : t ∈ p.refactor_vertices),
      (refactor_Walk.refactor_truncateAtFirst p t h).1 = t
  | _, _, .nil _ _, _, h => (List.mem_singleton.mp h).symm
  | u, _, .cons _ _ p', t, h => by
      simp only [refactor_Walk.refactor_truncateAtFirst]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        exact h_eq.symm
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.refactor_vertices := by
          have h' : t ∈ u :: p'.refactor_vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        exact refactor_Walk.refactor_truncateAtFirst_target_eq p' t h_in_p'
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.truncateAtFirst_target_eq

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_truncateAtFirst_le (was: refactor_Walk.refactor_length_truncateAtFirst_le)
/-- **Subtask 4c:** the truncated walk's length is bounded by the
original walk's length.  Both endpoints (`≤`) are attained: a `nil`
input gives a `nil` output of the same length 0; a `cons` input whose
truncation does not drop any cell yields equality.  The strict-
inequality version `refactor_length_truncateAtFirst_lt_of_mem_dropLast`
strengthens this under the `t ∈ p.refactor_vertices.dropLast`
hypothesis.  Mechanical refactor port: rename `length →
refactor_length`, `vertices → refactor_vertices`, `truncateAtFirst →
refactor_truncateAtFirst`; cons-cell pattern shrinks from four args to
three. -/
private lemma refactor_Walk.refactor_length_truncateAtFirst_le {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v) (t : Node)
      (h : t ∈ p.refactor_vertices),
      (refactor_Walk.refactor_truncateAtFirst p t h).2.refactor_length ≤ p.refactor_length
  | _, _, .nil _ _, _, _ => by
      simp only [refactor_Walk.refactor_truncateAtFirst,
                 refactor_Walk.refactor_length, le_refl]
  | u, _, .cons _ _ p', t, h => by
      simp only [refactor_Walk.refactor_truncateAtFirst,
                 refactor_Walk.refactor_length]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        simp [refactor_Walk.refactor_length]
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.refactor_vertices := by
          have h' : t ∈ u :: p'.refactor_vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        have ih := refactor_Walk.refactor_length_truncateAtFirst_le p' t h_in_p'
        change (refactor_Walk.refactor_truncateAtFirst p' t h_in_p').2.refactor_length
            + 1 ≤ p'.refactor_length + 1
        omega
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_truncateAtFirst_le

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isDirectedWalk_truncateAtFirst (was: refactor_Walk.refactor_isDirectedWalk_truncateAtFirst)
/-- **Subtask 4d:** the truncated walk inherits `refactor_IsDirectedWalk`
from the original walk.  The `nil` arm produces a `.nil` walk
(trivially directed).  The `cons` arm case-splits the typed WalkStep:
* `.forwardE h_E`: the `t = u` branch produces a `.nil` walk
  (trivially directed); the `t ≠ u` branch recurses on `p'`, whose
  `refactor_IsDirectedWalk` is `hp_dir` directly (the `.cons _
  (.forwardE _) p` clause of `refactor_IsDirectedWalk` reduces
  definitionally to `p.refactor_IsDirectedWalk`, so no `obtain` of the
  old triple-conjunction is needed).
* `.backwardE _` / `.bidir _`: close by `hp_dir.elim` since
  `refactor_IsDirectedWalk` returns `False` on these. -/
private lemma refactor_Walk.refactor_isDirectedWalk_truncateAtFirst
    {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v) (t : Node)
      (h : t ∈ p.refactor_vertices),
      p.refactor_IsDirectedWalk →
        (refactor_Walk.refactor_truncateAtFirst p t h).2.refactor_IsDirectedWalk
  | _, _, .nil _ _, _, _, _ => by
      simp only [refactor_Walk.refactor_truncateAtFirst]
      trivial
  | u, _, .cons _ (.forwardE _) p', t, h, hp_dir => by
      simp only [refactor_Walk.refactor_truncateAtFirst]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        trivial
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.refactor_vertices := by
          have h' : t ∈ u :: p'.refactor_vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        exact refactor_Walk.refactor_isDirectedWalk_truncateAtFirst
          p' t h_in_p' hp_dir
  | _, _, .cons _ (.backwardE _) _, _, _, hp_dir => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, _, _, hp_dir => hp_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isDirectedWalk_truncateAtFirst

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.mem_vertices_of_mem_dropLast (was: refactor_Walk.refactor_mem_vertices_of_mem_dropLast)
/-- Auxiliary: every `t ∈ p.refactor_vertices.dropLast` automatically
lies in the full `p.refactor_vertices`.  Direct application of
mathlib's `List.mem_of_mem_dropLast`.  Used by
`refactor_length_truncateAtFirst_lt_of_mem_dropLast` and
`refactor_exists_directed_walk_v_not_in_dropLast` to feed a `dropLast`
membership into `refactor_truncateAtFirst`'s `p.refactor_vertices`-
membership hypothesis.  Mechanical refactor port. -/
private lemma refactor_Walk.refactor_mem_vertices_of_mem_dropLast
    {G : refactor_CDMG Node} {u v : Node} {p : refactor_Walk G u v} {t : Node}
    (h : t ∈ p.refactor_vertices.dropLast) : t ∈ p.refactor_vertices :=
  List.mem_of_mem_dropLast h
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.mem_vertices_of_mem_dropLast

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_truncateAtFirst_lt_of_mem_dropLast (was: refactor_Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast)
/-- **Subtask 4e:** the load-bearing *strict* inequality.  When `t`
appears in `p.refactor_vertices.dropLast` (some non-terminal position
in the walk's vertex list), the truncation drops at least one `cons`
cell, so its length is strictly smaller than `p.refactor_length`.

The `nil` case is vacuous: `(.nil v _).refactor_vertices.dropLast =
[v].dropLast = []`.

The `cons` case unfolds `(u :: p'.refactor_vertices).dropLast =
u :: p'.refactor_vertices.dropLast` via `List.dropLast_cons_of_ne_nil`
(using `refactor_vertices_ne_nil` from subtask 2) and case-splits
`t ∈ u :: p'.refactor_vertices.dropLast`.  `t = u`: trivial walk of
length 0 < cons walk's length ≥ 1.  `t ∈
p'.refactor_vertices.dropLast`: recurse on `p'` via the inductive
hypothesis; `omega` closes the +1/+1 step.  Mechanical refactor port:
cons-cell pattern shrinks from four args to three; `vertices` /
`length` / `vertices_ne_nil` / `truncateAtFirst` all gain
`refactor_` prefix. -/
private lemma refactor_Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast
    {G : refactor_CDMG Node} :
    ∀ {u v : Node} (p : refactor_Walk G u v) (t : Node)
      (h_in_dropLast : t ∈ p.refactor_vertices.dropLast),
      (refactor_Walk.refactor_truncateAtFirst p t
          (refactor_Walk.refactor_mem_vertices_of_mem_dropLast
            h_in_dropLast)).2.refactor_length < p.refactor_length
  | _, _, .nil _ _, _, h => by
      simp [refactor_Walk.refactor_vertices] at h
  | u, _, .cons _ _ p', t, h_in_dropLast => by
      have hne : p'.refactor_vertices ≠ [] :=
        refactor_Walk.refactor_vertices_ne_nil p'
      change t ∈ (u :: p'.refactor_vertices).dropLast at h_in_dropLast
      rw [List.dropLast_cons_of_ne_nil hne] at h_in_dropLast
      simp only [refactor_Walk.refactor_truncateAtFirst,
                 refactor_Walk.refactor_length]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        simp [refactor_Walk.refactor_length]
      · rw [dif_neg h_eq]
        have h_in_p'_drop : t ∈ p'.refactor_vertices.dropLast := by
          rcases List.mem_cons.mp h_in_dropLast with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        have ih :=
          refactor_Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast
            p' t h_in_p'_drop
        change (refactor_Walk.refactor_truncateAtFirst p' t _).2.refactor_length
            + 1 < p'.refactor_length + 1
        omega
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_truncateAtFirst_lt_of_mem_dropLast

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: exists_directed_walk_v_not_in_dropLast (was: refactor_exists_directed_walk_v_not_in_dropLast)
/-- **Subtask 4f:** the (⇐) direction's load-bearing existence lemma.
Given any ancestor `c ∈ G.refactor_Anc v` with `c ≠ v`, there exists a
*minimum-length* directed walk from `c` to `v` whose target `v` does
not appear in its `refactor_vertices.dropLast` (i.e. `v` occurs *only*
at the walk's final position).

Proof strategy: extract initial directed walk from `c ∈ G.refactor_Anc
v`; define `P n` as "exists directed `c → v` walk of length `n`";
witness non-emptiness of `{n | P n}` via `p₀`; let `n₀ := Nat.find` and
use `Nat.find_spec` to get a minimum-length walk `p_min`.  Contradict
`Nat.find_min` by truncating `p_min` at `v`'s first occurrence — the
truncated walk has strictly smaller length (via
`refactor_length_truncateAtFirst_lt_of_mem_dropLast`), targets `v`
(via `refactor_truncateAtFirst_target_eq`), and inherits directedness
(via `refactor_isDirectedWalk_truncateAtFirst`).

Mechanical refactor port: `Walk → refactor_Walk`, `IsDirectedWalk →
refactor_IsDirectedWalk`, `length → refactor_length`, `vertices →
refactor_vertices`, `Anc → refactor_Anc`, and all four truncation
helpers gain `refactor_` prefix.  The `Nat.find` / `Nat.find_spec` /
`Nat.find_min` machinery is structure-agnostic. -/
private lemma refactor_exists_directed_walk_v_not_in_dropLast
    {G : refactor_CDMG Node} {c v : Node}
    (hc_anc : c ∈ G.refactor_Anc v) (hcv : c ≠ v) :
    ∃ (p : refactor_Walk G c v), p.refactor_IsDirectedWalk
      ∧ v ∉ p.refactor_vertices.dropLast := by
  classical
  -- Step 1: extract initial walk from c ∈ refactor_Anc v.
  obtain ⟨_hc_in, p₀, hp₀_dir⟩ := hc_anc
  -- Step 2: predicate "exists directed c→v walk of length n", and witness.
  let P : ℕ → Prop :=
    fun n => ∃ (p : refactor_Walk G c v),
      p.refactor_IsDirectedWalk ∧ p.refactor_length = n
  have hP_nonempty : ∃ n, P n := ⟨p₀.refactor_length, p₀, hp₀_dir, rfl⟩
  -- Step 3: minimum length witness via Nat.find.
  obtain ⟨p_min, hp_min_dir, hp_min_len⟩ :
      P (Nat.find hP_nonempty) := Nat.find_spec hP_nonempty
  refine ⟨p_min, hp_min_dir, ?_⟩
  -- Step 4: contradiction with minimality.
  intro hv_drop
  have h_v_in : v ∈ p_min.refactor_vertices :=
    refactor_Walk.refactor_mem_vertices_of_mem_dropLast hv_drop
  obtain ⟨v', p_short, h_target, h_dir, h_lt⟩ :
      ∃ (v' : Node) (p_short : refactor_Walk G c v'),
        v' = v ∧ p_short.refactor_IsDirectedWalk
          ∧ p_short.refactor_length < p_min.refactor_length := by
    refine ⟨(refactor_Walk.refactor_truncateAtFirst p_min v h_v_in).1,
            (refactor_Walk.refactor_truncateAtFirst p_min v h_v_in).2,
            ?_, ?_, ?_⟩
    · exact refactor_Walk.refactor_truncateAtFirst_target_eq p_min v h_v_in
    · exact refactor_Walk.refactor_isDirectedWalk_truncateAtFirst
        p_min v h_v_in hp_min_dir
    · exact refactor_Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast
        p_min v hv_drop
  subst h_target
  have h_lt_n₀ : p_short.refactor_length < Nat.find hP_nonempty :=
    hp_min_len ▸ h_lt
  exact Nat.find_min hP_nonempty h_lt_n₀ ⟨p_short, h_dir, rfl⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: exists_directed_walk_v_not_in_dropLast

-- ## Proof-only helpers — bifurcation walk construction (subtask 5, refactor twins)
--
-- Subtask 5 of the refactor port: assemble the candidate bifurcation
-- walk for the (⇐) direction.  Given two directed arms `q_v : c → v`
-- and `q_w : c → w`, `refactor_mkBifurcation` produces the walk
-- `(reverse q_v) ⌢ q_w : refactor_Walk G v w` whose middle vertex is
-- `c`.  Subtask 6 (next) connects this to the directed-hinge
-- predicate so the resulting walk realises `IsBifurcationSource`.
--
-- *Mathematical content unchanged.*  Same shortest-walk reversal +
-- concatenation as the OLD `Walk.mkBifurcation`; the refactor only
-- swaps the upstream `CDMG` / `Walk` / `WalkStep` encodings.
--
-- *Typed-WalkStep shape: the endpoint-flip is a no-op on the
-- witness.*  This is the load-bearing simplification for subtask 5a.
-- Under the OLD propositional `WalkStep`, the reverse step's witness
-- was `Or.inr ⟨a = (c, vMid), a ∈ G.E⟩` — a re-packaging of the
-- forward step's `(a = (c, vMid), a ∈ G.E)` data into the "backward"
-- disjunct of the two-clause definition.  Under the refactor's typed
-- inductive `refactor_WalkStep`, the same proof term `h_E :
-- (c, vMid) ∈ G.E` carried by `.forwardE h_E` is *exactly* the
-- witness `.backwardE` expects for the reverse step, with no
-- repackaging.  See `refactor_reverseDirected` below for the
-- precise constructor swap.

-- *Why this helper exists.*  The (⇐) direction's candidate
-- bifurcation walk (subtask 5d's `refactor_mkBifurcation`) is built
-- by reversing the directed left arm `q_v : c → v` and concatenating
-- with the right arm `q_w : c → w`.  This primitive performs the
-- reversal.
--
-- *Typed-WalkStep shape: same `h_E`, different constructor wrap.*
-- The original step `.forwardE h_E : refactor_WalkStep G c vMid`
-- carries `h_E : (c, vMid) ∈ G.E`.  The reverse step
-- `refactor_WalkStep G vMid c` is constructed via `.backwardE h_E`:
-- the `.backwardE` constructor takes `h : (v, u) ∈ G.E`, which on
-- `(u, v) := (vMid, c)` reads `(c, vMid) ∈ G.E = h_E`.  So the same
-- proof term `h_E` lands in both constructors, distinguished only by
-- the constructor tag.  This is the central structural simplification
-- delivered by the typed-step encoding for this subtask (the OLD
-- propositional `WalkStep` had to re-package `h_E` through
-- `Or.inr ⟨_, _⟩`).
--
-- *Composition via the localised `refactor_comp`.*  The recursion
-- shape `reverse (cons s p) = reverse p ⌢ singleton (back s)`
-- threads through subtask 2's `refactor_comp` without introducing a
-- new global walk-reverse operator.  The two non-`.forwardE`
-- constructor branches close by `hqv_dir.elim` (since
-- `refactor_IsDirectedWalk` returns `False` on `.backwardE` /
-- `.bidir` definitionally — no `obtain` of an OLD-style triple
-- conjunction).
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.reverseDirected (was: refactor_Walk.refactor_reverseDirected)
/-- **Subtask 5a:** reverse a directed walk
`qv : refactor_Walk G c v` into a walk `refactor_Walk G v c`.  Each
cell of the result uses the *backward* `refactor_WalkStep`
constructor `.backwardE`, re-using the same `h_E : (c, vMid) ∈ G.E`
witness extracted from the input's `.forwardE h_E` cell.

Structural recursion on `qv`:
* `nil` case: return the trivial walk `.nil w hw`.
* `cons _ (.forwardE h_E) qv'` case: recurse on `qv'` to get
  `qv'_rev : refactor_Walk G v vMid`; assemble the length-1
  backward-edge walk `refactor_Walk G vMid c` as
  `.cons c (.backwardE h_E) (.nil c _)` (with the nil's `c ∈ G`
  witness extracted from the original step via
  `refactor_WalkStep.refactor_source_mem`); compose via
  `refactor_comp`.
* `.backwardE _` / `.bidir _` cases: closed by `hqv_dir.elim`
  (`refactor_IsDirectedWalk` returns `False` definitionally). -/
private def refactor_Walk.refactor_reverseDirected {G : refactor_CDMG Node} :
    ∀ {c v : Node} (qv : refactor_Walk G c v),
      qv.refactor_IsDirectedWalk → refactor_Walk G v c
  | _, _, .nil w hw, _ => .nil w hw
  | c, _, .cons _ (.forwardE h_E) qv', hqv_dir =>
      (refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp
        (.cons c (.backwardE h_E)
          (.nil c (refactor_WalkStep.refactor_source_mem (.forwardE h_E))))
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.reverseDirected

-- *Why this helper exists.*  Length arithmetic on the candidate
-- bifurcation walk (subtask 5e's `refactor_length_mkBifurcation`)
-- chains this lemma with `refactor_length_comp` to express the
-- candidate's length as `q_v.refactor_length + q_w.refactor_length`.
--
-- *Typed-WalkStep shape: structure-agnostic body.*  Each cell of
-- the input produces one cell in the recursive reversal plus one
-- cell in the length-1 backward-edge walk, so the total length
-- comes out to `qv'.refactor_length + 1 = qv.refactor_length`.  The
-- `cons` branch is the OLD's body with `length` / `comp` / `IsDirectedWalk`
-- swapped for their `refactor_`-prefixed twins and the cons-cell
-- pattern shrunk from four args (`vMid a h p`) to three (`vMid s p`);
-- the `.backwardE` / `.bidir` cases close by `hqv_dir.elim`.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_reverseDirected (was: refactor_Walk.refactor_length_reverseDirected)
/-- **Subtask 5b:** `refactor_reverseDirected` preserves
`refactor_length`. -/
private lemma refactor_Walk.refactor_length_reverseDirected
    {G : refactor_CDMG Node} :
    ∀ {c v : Node} (qv : refactor_Walk G c v)
      (hqv_dir : qv.refactor_IsDirectedWalk),
      (refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_length
        = qv.refactor_length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ (.forwardE _) qv', hqv_dir => by
      change ((refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp _).refactor_length
            = qv'.refactor_length + 1
      rw [refactor_Walk.refactor_length_comp,
          refactor_Walk.refactor_length_reverseDirected qv' hqv_dir]
      rfl
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_reverseDirected

-- *Why this helper exists.*  Subtask 5f's
-- `refactor_vertices_mkBifurcation` factors the candidate
-- bifurcation walk's vertex list as
-- `q_v.refactor_vertices.reverse.dropLast ++ q_w.refactor_vertices`,
-- which in turn feeds the (⇐) direction's end-node / interior-
-- membership bookkeeping (clauses (a)/(c) of `def_3_4`).  This
-- intermediate result on the reverse alone is the key step.
--
-- *Typed-WalkStep shape: structure-agnostic body.*  The proof is the
-- OLD's body with `vertices` / `comp` / `vertices_eq_head_cons_tail`
-- swapped for their `refactor_`-prefixed twins and the cons-cell
-- pattern shrunk from four args to three; the `.backwardE` / `.bidir`
-- cases close by `hqv_dir.elim`.  The closing `simp` lemma set is
-- identical (`refactor_vertices`, `List.reverse_cons`) — the
-- `dropLast` of a reversed-cons list is handled by mathlib's
-- general-purpose simp lemmas.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_reverseDirected (was: refactor_Walk.refactor_vertices_reverseDirected)
/-- **Subtask 5c:** `refactor_reverseDirected` reverses the
`refactor_vertices` list. -/
private lemma refactor_Walk.refactor_vertices_reverseDirected
    {G : refactor_CDMG Node} :
    ∀ {c v : Node} (qv : refactor_Walk G c v)
      (hqv_dir : qv.refactor_IsDirectedWalk),
      (refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_vertices
        = qv.refactor_vertices.reverse
  | _, _, .nil _ _, _ => rfl
  | c, _, .cons vMid (.forwardE _) qv', hqv_dir => by
      have ih := refactor_Walk.refactor_vertices_reverseDirected qv' hqv_dir
      have h_head : qv'.refactor_vertices = vMid :: qv'.refactor_vertices.tail :=
        refactor_Walk.refactor_vertices_eq_head_cons_tail qv'
      change ((refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp _).refactor_vertices
            = (c :: qv'.refactor_vertices).reverse
      rw [refactor_Walk.refactor_vertices_comp, ih]
      conv_lhs => rw [h_head]
      conv_rhs => rw [h_head]
      simp [refactor_Walk.refactor_vertices, List.reverse_cons]
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_reverseDirected

-- *Why this helper exists.*  The constructor for the candidate
-- bifurcation walk consumed by the (⇐) direction of
-- `refactor_bifurcationAlternative`.  Built by reversing the left
-- arm `q_v` (subtask 5a) and concatenating with the right arm `q_w`
-- (subtask 2).
--
-- *`_hqv_pos` carried but unused at the definition level.*  Subtask
-- 6 needs `q_v.refactor_length ≥ 1` to realise the
-- `refactor_IsBifurcationDirectedHingeWithSplit` predicate on the
-- output (splitting at the hinge index `q_v.refactor_length - 1`,
-- which requires the index to be a valid `ℕ`).  Threading
-- `_hqv_pos` through the signature here keeps the downstream
-- subtask-6/8 API uniform — see the OLD's identical signature on
-- `Walk.mkBifurcation`.
--
-- *Typed-WalkStep shape: irrelevant here.*  This is a pure
-- concatenation of two walks; the typed step never enters.  Body is
-- one-for-one identical to the OLD modulo refactor-prefix renames.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.mkBifurcation (was: refactor_Walk.refactor_mkBifurcation)
/-- **Subtask 5d:** the bifurcation-walk constructor.  Given a
directed left arm `qv : refactor_Walk G c v` of length ≥ 1 and a
right arm `qw : refactor_Walk G c w`, assemble the candidate
bifurcation walk
`(refactor_reverseDirected qv hqv_dir).refactor_comp qw :
refactor_Walk G v w` whose middle vertex is `c`. -/
private def refactor_Walk.refactor_mkBifurcation {G : refactor_CDMG Node}
    {c v w : Node}
    (qv : refactor_Walk G c v) (hqv_dir : qv.refactor_IsDirectedWalk)
    (_hqv_pos : qv.refactor_length ≥ 1) (qw : refactor_Walk G c w) :
    refactor_Walk G v w :=
  (refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_comp qw
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.mkBifurcation

-- *Why this helper exists.*  Length bookkeeping on the candidate
-- bifurcation walk feeds clause (e) of `def_3_4` item~vi
-- (`1 ≤ k ≤ n - 1`, where `n = qv.refactor_length + qw.refactor_length`
-- is the candidate's total length and `k = qv.refactor_length - 1` is
-- the hinge index).
--
-- *Typed-WalkStep shape: irrelevant here.*  Direct from
-- `refactor_length_comp` + `refactor_length_reverseDirected`.  Body
-- is one-for-one identical to the OLD modulo refactor-prefix
-- renames.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_mkBifurcation (was: refactor_Walk.refactor_length_mkBifurcation)
/-- **Subtask 5e:** the bifurcation walk's `refactor_length` is
`qv.refactor_length + qw.refactor_length`. -/
private lemma refactor_Walk.refactor_length_mkBifurcation
    {G : refactor_CDMG Node} {c v w : Node}
    (qv : refactor_Walk G c v) (hqv_dir : qv.refactor_IsDirectedWalk)
    (hqv_pos : qv.refactor_length ≥ 1) (qw : refactor_Walk G c w) :
    (refactor_Walk.refactor_mkBifurcation qv hqv_dir hqv_pos qw).refactor_length
      = qv.refactor_length + qw.refactor_length := by
  change ((refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_comp qw).refactor_length
        = qv.refactor_length + qw.refactor_length
  rw [refactor_Walk.refactor_length_comp,
      refactor_Walk.refactor_length_reverseDirected qv hqv_dir]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_mkBifurcation

-- *Why this helper exists.*  The vertex-list factorisation
-- `qv.refactor_vertices.reverse.dropLast ++ qw.refactor_vertices`
-- is the load-bearing splitting formula for the (⇐) direction's
-- clause~(a)/(c) end-node-uniqueness bookkeeping in Step 5 of the
-- TeX proof: the candidate bifurcation walk's vertex list factors
-- as *reverse of the left arm without its source* followed by
-- *full right arm*.  The end-node constraints `v ≠ w`,
-- `v ∉ p.refactor_vertices.tail`,
-- `w ∉ p.refactor_vertices.dropLast` then reduce to per-arm
-- vertex-membership statements via this equation.
--
-- *Typed-WalkStep shape: irrelevant here.*  Direct from
-- `refactor_vertices_comp` + `refactor_vertices_reverseDirected`.
-- Body is one-for-one identical to the OLD modulo refactor-prefix
-- renames.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.vertices_mkBifurcation (was: refactor_Walk.refactor_vertices_mkBifurcation)
/-- **Subtask 5f:** the bifurcation walk's `refactor_vertices` list
factors as `qv.refactor_vertices.reverse.dropLast ++
qw.refactor_vertices`. -/
private lemma refactor_Walk.refactor_vertices_mkBifurcation
    {G : refactor_CDMG Node} {c v w : Node}
    (qv : refactor_Walk G c v) (hqv_dir : qv.refactor_IsDirectedWalk)
    (hqv_pos : qv.refactor_length ≥ 1) (qw : refactor_Walk G c w) :
    (refactor_Walk.refactor_mkBifurcation qv hqv_dir hqv_pos qw).refactor_vertices
      = qv.refactor_vertices.reverse.dropLast ++ qw.refactor_vertices := by
  change ((refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_comp qw).refactor_vertices
        = qv.refactor_vertices.reverse.dropLast ++ qw.refactor_vertices
  rw [refactor_Walk.refactor_vertices_comp,
      refactor_Walk.refactor_vertices_reverseDirected qv hqv_dir]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.vertices_mkBifurcation

-- ## Proof-only helpers — `mkBifurcation` realises the directed-hinge predicate (subtask 6, refactor twins)
--
-- Subtask 6 of the refactor port: the four private helpers below are
-- refactor twins of `Walk.comp_assoc`,
-- `Walk.isBifurcationDirectedHinge_cons_backward_of_directed`,
-- `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux`, and
-- `Walk.isBifurcationDirectedHinge_mkBifurcation` (the `namespace
-- CDMG` ORIGINAL block above).  They connect subtask 5's
-- `refactor_mkBifurcation` constructor to the
-- `refactor_IsBifurcationDirectedHingeWithSplit` predicate (`Walks.lean`
-- REPLACEMENT block):  the (⇐) direction's Step 5 (TeX proof) needs
-- all five clauses (a)–(e) of `def_3_4` item~vi to hold on the
-- constructed walk at index `k = qv.refactor_length - 1`; the
-- directed-hinge predicate covers clauses (b), (c), (d) — chained
-- backward-`E` edges of the left arm followed by forward-`E` edges of
-- the right arm, with a directed hinge at the source vertex `c`.
--
-- The same three-step structure as the original carries over:
-- `refactor_comp_assoc` re-associates the composition produced by
-- `refactor_reverseDirected`'s `cons` case;
-- `refactor_isBifurcationDirectedHinge_cons_backward_of_directed`
-- (base case) handles a single backward edge followed by a non-trivial
-- directed walk; and
-- `refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux`
-- (parametrised inductive step) shifts the predicate's index by
-- `qv.refactor_length` when prepending the backward-edge chain
-- `refactor_reverseDirected qv`.  The consumer-facing wrapper
-- `refactor_isBifurcationDirectedHinge_mkBifurcation` decomposes `qv`
-- once and feeds Helper 1 + Helper 2 to discharge the goal at index
-- `qv.refactor_length - 1`.
--
-- ## Design choices — subtask 6 refactor twins
--
-- *Signature change on Helper 1
--   (`refactor_isBifurcationDirectedHinge_cons_backward_of_directed`).*
--   The original took an ordered pair `a : Node × Node`, a
--   propositional `WalkStep` witness `h : G.WalkStep u a v`, and two
--   independent facts `ha_eq : a = (v, u)` and `ha_mem : a ∈ G.E` —
--   four arguments to encode "this single edge is a backward `E`-edge
--   from `u` to `v`".  Under the typed-step refactor, all four collapse
--   into a single `h_E : (v, u) ∈ G.E`: the typed constructor
--   `.backwardE h_E : refactor_WalkStep G u v` already pins both the
--   orientation (backward) and the channel (`E`) without a separate
--   `ha_eq` / `ha_mem` proof.  We accept the signature change rather
--   than threading a `(s : refactor_WalkStep G u v)` plus a
--   destructuring witness `∃ h_E, s = .backwardE h_E` (which would be
--   uglier at every call site and offer no proof-content gain).
--   Downstream consumers (Helpers 2, 3, 4 + the main theorem) build the
--   `.backwardE h_E` step themselves from the directed-walk data, so
--   the change is local to this helper.
--
-- *Building `backStep` directly as `.backwardE h_E` (Helpers 2, 3).*
--   The original built `backStep : G.WalkStep vMid a c` via
--   `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩` (the backward arm of the
--   `WalkStep` disjunction).  Under the typed refactor, the
--   directed-walk witness `hqv_dir` on `cons _ (.forwardE h_E) qv'`
--   already unfolds (definitionally) to `qv'.refactor_IsDirectedWalk`,
--   and the `h_E : (c, vMid) ∈ G.E` data is available directly from
--   the constructor match.  So `backStep := .backwardE h_E` is the
--   one-step replacement of the original's `Or.inr ⟨…⟩`.  No data is
--   lost: `.backwardE h_E : refactor_WalkStep G vMid c` carries the
--   same membership witness as `Or.inr ⟨ha_eq, ha_E⟩` did in the
--   untyped form.
--
-- *Case-split on the typed step `s` instead of `Or.inr`.*  In
--   Helpers 2 and 3, where the original obtained
--   `hqv_dir.1 / hqv_dir.2.1 / hqv_dir.2.2` from the
--   `IsDirectedWalk`-as-triple unfolding, the refactor case-splits on
--   `s : refactor_WalkStep G c vMid` first: only `.forwardE h_E`
--   survives `refactor_IsDirectedWalk`'s `False`-returning branches
--   for `.backwardE _` / `.bidir _`.  The structural impossibility of
--   the latter two cases is discharged by `hqv_dir.elim`, matching the
--   pattern already used in `refactor_reverseDirected`,
--   `refactor_isDirectedWalk_comp`, etc.
--
-- *Re-using `refactor_comp_assoc` verbatim.*  The associativity
--   rewrite step `((reverseDirected qv').comp single-back-edge).comp
--   rest → (reverseDirected qv').comp (single-back-edge.comp rest)`
--   is structurally identical to the original — the typed-step
--   refactor does not touch `refactor_comp`'s recursion shape, so
--   `refactor_comp_assoc` plays the same role as the original
--   `comp_assoc` in Helpers 3 and 4.

-- *Why this helper exists.*  Helper 3
-- (`refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux`)'s
-- inductive step re-associates `((refactor_reverseDirected qv').refactor_comp
-- single-back-edge).refactor_comp rest` into the form
-- `(refactor_reverseDirected qv').refactor_comp (single-back-edge.refactor_comp rest)`
-- that the IH matches.  Mathlib's walk concatenation does provide an
-- analogous `comp_assoc`, but our `refactor_comp` is a locally-`private`
-- re-declaration (subtask 2 above), so the associativity lemma is also
-- localised here.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the first walk's spine — the typed step never enters
-- the case split.  Body is the OLD's body with `comp` swapped for
-- `refactor_comp` and the cons-cell pattern shrunk from four args
-- (`vMid a h p`) to three (`vMid s p`).
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.comp_assoc (was: refactor_Walk.refactor_comp_assoc)
/-- Auxiliary: `refactor_comp` is associative.  Verbatim structural
induction on the first argument: the `nil` case reduces by definition
(`nil.refactor_comp q = q`, so `(nil.refactor_comp q).refactor_comp r
= q.refactor_comp r = nil.refactor_comp (q.refactor_comp r)`), and the
`cons` case unfolds `refactor_comp` once on each side, exposing the IH
on the tail. -/
private lemma refactor_Walk.refactor_comp_assoc {G : refactor_CDMG Node} :
    ∀ {u₁ u₂ u₃ u₄ : Node} (p : refactor_Walk G u₁ u₂) (q : refactor_Walk G u₂ u₃)
      (r : refactor_Walk G u₃ u₄),
      (p.refactor_comp q).refactor_comp r = p.refactor_comp (q.refactor_comp r)
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ s p, q, r => by
      change refactor_Walk.cons _ s ((p.refactor_comp q).refactor_comp r)
            = refactor_Walk.cons _ s (p.refactor_comp (q.refactor_comp r))
      rw [refactor_Walk.refactor_comp_assoc p q r]
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.comp_assoc

-- *Why this helper exists.*  The base case of Helper 3's induction:
-- a single backward `E`-edge `(v, u)` followed by a non-trivial
-- directed walk `p : refactor_Walk G v w` realises the directed-hinge
-- predicate at index 0.  Discharges the third clause of
-- `refactor_IsBifurcationDirectedHingeWithSplit`'s recursion
-- (`Walks.lean` REPLACEMENT:
-- `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.refactor_IsDirectedWalk`).
-- The `hp_nonempty` hypothesis is *load-bearing*: without it, the
-- predicate's second clause (`.cons _ (.backwardE _) (.nil _ _), 0 =>
-- False`) would fire instead.  Downstream this corresponds to the
-- `qw.refactor_length ≥ 1` constraint that the (⇐) direction obtains
-- from `c ≠ w`.
--
-- *Signature change: drop `(a, h, ha_eq, ha_mem)`, take `h_E` only.*
-- See the design block above for the full rationale.  The typed
-- constructor `.backwardE h_E : refactor_WalkStep G u v` carries
-- the channel and orientation that the OLD's four-argument tuple
-- `(a, h, ha_eq, ha_mem)` encoded.
--
-- *Proof: case-split `p`.*  Same shape as OLD.  `.nil _ _` branch
-- contradicts `hp_nonempty` (`(.nil _ _).refactor_length = 0`).
-- `.cons _ _ _` branch lands directly in the predicate's clause
-- `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.refactor_IsDirectedWalk`,
-- closed by `hp_dir`.  The OLD's `⟨ha_eq, ha_mem, hp_dir⟩` triple
-- collapses to a bare `hp_dir` because the channel and orientation
-- are already pinned by the typed `.backwardE` constructor.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isBifurcationDirectedHinge_cons_backward_of_directed (was: refactor_Walk.refactor_isBifurcationDirectedHinge_cons_backward_of_directed)
/-- **Subtask 6a (base case):** a single backward `E`-edge from `u` to
`v` (witnessed by `h_E : (v, u) ∈ G.E`) followed by a non-trivial
directed walk `p : refactor_Walk G v w` realises the directed-hinge
predicate at index 0. -/
private lemma refactor_Walk.refactor_isBifurcationDirectedHinge_cons_backward_of_directed
    {G : refactor_CDMG Node} {u v w : Node}
    (h_E : (v, u) ∈ G.E)
    (p : refactor_Walk G v w) (hp_dir : p.refactor_IsDirectedWalk)
    (hp_nonempty : p.refactor_length ≥ 1) :
    refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
      (refactor_Walk.cons v (.backwardE h_E) p) 0 := by
  cases p with
  | nil _ _ => simp [refactor_Walk.refactor_length] at hp_nonempty
  | cons _ _ _ => exact hp_dir
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isBifurcationDirectedHinge_cons_backward_of_directed

-- *Why this helper exists.*  The parametrised inductive step of
-- subtask 6: prepending the `refactor_reverseDirected qv` backward
-- chain (of length `qv.refactor_length`) in front of any walk `rest`
-- that already realises the directed-hinge predicate at index `k`
-- shifts the index by `qv.refactor_length`.  The parametrisation by
-- `rest` and `k` is what makes the structural induction on `qv` go
-- through: `refactor_reverseDirected`'s definition places the new edge
-- at the *rightmost* position of the recursion (via
-- `(refactor_reverseDirected qv').refactor_comp single-back-edge`), so
-- the IH on `qv'` must apply with an enriched
-- `rest' = .cons c (.backwardE h_E) rest` and shifted index
-- `k' = k + 1`.
--
-- *Typed-WalkStep shape: case-split `s` instead of `Or.inr`.*  In the
-- `cons` arm, where the OLD built `backStep` via
-- `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩`, the refactor case-splits the step
-- `s : refactor_WalkStep G c vMid` first: only `.forwardE h_E`
-- survives `refactor_IsDirectedWalk`, and `backStep := .backwardE h_E`
-- carries the same `(c, vMid) ∈ G.E` data.  The
-- `refactor_IsBifurcationDirectedHingeWithSplit (k+1)` witness on the
-- enriched `rest'` is then `hrest` directly — the predicate's
-- `.cons _ (.backwardE _) p, k + 1 => p.refactor_IsBifurcationDirectedHingeWithSplit k`
-- clause makes it a single proposition (in contrast to the OLD's
-- 3-tuple `⟨hqv_dir.1, hqv_dir.2.1, hrest⟩`).  The
-- `refactor_comp_assoc` rewrite + index arithmetic is otherwise
-- identical to OLD.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux (was: refactor_Walk.refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux)
/-- **Subtask 6b (parametrised inductive step):** prepending the
`refactor_reverseDirected qv` backward-edge chain in front of any walk
`rest` that already realises the directed-hinge predicate at index `k`
shifts the index by `qv.refactor_length`. -/
private lemma refactor_Walk.refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux
    {G : refactor_CDMG Node} :
    ∀ {c v : Node} (qv : refactor_Walk G c v) (hqv_dir : qv.refactor_IsDirectedWalk)
      {w : Node} (rest : refactor_Walk G c w) (k : ℕ)
      (_hrest : rest.refactor_IsBifurcationDirectedHingeWithSplit k),
      refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
        ((refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_comp rest)
        (qv.refactor_length + k)
  | _, _, .nil w hw, _, _, rest, k, hrest => by
      simp only [refactor_Walk.refactor_reverseDirected, refactor_Walk.refactor_comp,
        refactor_Walk.refactor_length, Nat.zero_add]
      exact hrest
  | c, _, .cons vMid (.forwardE h_E) qv', hqv_dir, _, rest, k, hrest => by
      have h_cons : refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
          (refactor_Walk.cons c (.backwardE h_E) rest) (k + 1) := by
        simp only [refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit]
        exact hrest
      have ih := refactor_Walk.refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir (refactor_Walk.cons c (.backwardE h_E) rest) (k + 1) h_cons
      change refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
        (((refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp
            (refactor_Walk.cons c (.backwardE h_E)
              (refactor_Walk.nil c
                (refactor_WalkStep.refactor_source_mem (.forwardE h_E))))).refactor_comp rest)
        (qv'.refactor_length + 1 + k)
      rw [refactor_Walk.refactor_comp_assoc]
      change refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
        ((refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp
          (refactor_Walk.cons c (.backwardE h_E) rest))
        (qv'.refactor_length + 1 + k)
      have hidx : qv'.refactor_length + 1 + k = qv'.refactor_length + (k + 1) := by omega
      rw [hidx]
      exact ih
  | _, _, .cons _ (.backwardE _) _, hqv_dir, _, _, _, _ => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir, _, _, _, _ => hqv_dir.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux

-- *Why this helper exists.*  The consumer-facing wrapper of subtask 6:
-- the `refactor_mkBifurcation`-shaped output of subtask 5 realises the
-- directed-hinge predicate at the intended split index
-- `qv.refactor_length - 1`.  Combines the base case (Helper 1) with
-- the inductive auxiliary (Helper 2) by decomposing `qv` once and
-- applying the auxiliary to its tail `qv'`.
--
-- *Typed-WalkStep shape: `cases qv` + case-split `s`.*  The OLD's
-- `match qv, hqv_dir, hqv_pos with | .nil ... | .cons vMid a hStep qv'`
-- becomes `cases qv` with `.nil` contradicting `hqv_pos` and `.cons
-- vMid s qv'` requiring a further case-split on `s : refactor_WalkStep
-- G c vMid`.  Only `.forwardE h_E` survives `refactor_IsDirectedWalk`;
-- the `.backwardE _` / `.bidir _` cases close by `hqv_dir.elim`.
-- `backStep := .backwardE h_E` is built directly from the surviving
-- `h_E` (see design block above).  Helper 1's call site uses the new
-- single-argument signature
-- `refactor_isBifurcationDirectedHinge_cons_backward_of_directed h_E qw hqw_dir hqw_pos`
-- (no `ha_eq` / `ha_mem` triples).  Index arithmetic via `omega`
-- unchanged.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isBifurcationDirectedHinge_mkBifurcation (was: refactor_Walk.refactor_isBifurcationDirectedHinge_mkBifurcation)
/-- **Subtask 6c (consumer-facing wrapper):** the
`refactor_mkBifurcation`-shaped output of subtask 5 realises the
directed-hinge predicate at the intended split index
`qv.refactor_length - 1`. -/
private lemma refactor_Walk.refactor_isBifurcationDirectedHinge_mkBifurcation
    {G : refactor_CDMG Node} {c v w : Node}
    (qv : refactor_Walk G c v) (hqv_dir : qv.refactor_IsDirectedWalk)
    (hqv_pos : qv.refactor_length ≥ 1)
    (qw : refactor_Walk G c w) (hqw_dir : qw.refactor_IsDirectedWalk)
    (hqw_pos : qw.refactor_length ≥ 1) :
    refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
      (refactor_Walk.refactor_mkBifurcation qv hqv_dir hqv_pos qw)
      (qv.refactor_length - 1) := by
  change refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
    ((refactor_Walk.refactor_reverseDirected qv hqv_dir).refactor_comp qw)
    (qv.refactor_length - 1)
  cases qv with
  | nil _ _ => simp [refactor_Walk.refactor_length] at hqv_pos
  | cons vMid s qv' =>
      match s, hqv_dir with
      | .forwardE h_E, hqv_dir =>
          have h_base : refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
              (refactor_Walk.cons c (.backwardE h_E) qw) 0 :=
            refactor_Walk.refactor_isBifurcationDirectedHinge_cons_backward_of_directed
              h_E qw hqw_dir hqw_pos
          have ih := refactor_Walk.refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux
            qv' hqv_dir (refactor_Walk.cons c (.backwardE h_E) qw) 0 h_base
          change refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
            (((refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp
                (refactor_Walk.cons c (.backwardE h_E)
                  (refactor_Walk.nil c
                    (refactor_WalkStep.refactor_source_mem (.forwardE h_E))))).refactor_comp qw)
            (qv'.refactor_length + 1 - 1)
          rw [refactor_Walk.refactor_comp_assoc]
          change refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit
            ((refactor_Walk.refactor_reverseDirected qv' hqv_dir).refactor_comp
              (refactor_Walk.cons c (.backwardE h_E) qw))
            (qv'.refactor_length + 1 - 1)
          have hidx : qv'.refactor_length + 1 - 1 = qv'.refactor_length + 0 := by omega
          rw [hidx]
          exact ih
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isBifurcationDirectedHinge_mkBifurcation

-- *Why this helper exists.*  Subtask 7 of `claim_3_5`: the largest
-- single helper in the file, and the converse of subtask 6's
-- `refactor_isBifurcationDirectedHinge_mkBifurcation`.  Given a
-- bifurcation walk `p : refactor_Walk G v w` together with a
-- directed-hinge witness
-- `p.refactor_IsBifurcationDirectedHingeWithSplit i`, decompose `p`
-- into its source vertex `c := p.refactor_vertices[i+1]`, a directed
-- left arm `L : refactor_Walk G c v` of length `≥ 1`, and a directed
-- right arm `R : refactor_Walk G c w` of length `≥ 1`, with two
-- vertex-containment witnesses pinning every vertex of `L` into
-- `p.refactor_vertices.dropLast` and every vertex of `R` into
-- `p.refactor_vertices.tail`.  The (⇒) direction of the main theorem
-- consumes this decomposition to obtain the two directed arms before
-- lifting them into the intervened CDMGs `G_{do({w})}` (for `L`) and
-- `G_{do({v})}` (for `R`).
--
-- *Typed-WalkStep shape: invert the case-split skeleton.*  The OLD
-- proof opened each induction step by destructuring the directed-
-- hinge predicate's data via
-- `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := h_hinge`, then read the cons-
-- cell's edge `a = (vMid, u)` and `a ∈ G.E` off the resulting `ha_eq`
-- and `ha_mem`.  The refactor cannot mirror this: the predicate
-- `refactor_IsBifurcationDirectedHingeWithSplit` defines its content
-- per *step constructor* (`.forwardE` / `.backwardE` / `.bidir`),
-- so the proposition doesn't reduce until the outer step is
-- concrete.  The skeleton therefore inverts: `cases s` first (the
-- typed `refactor_WalkStep`), then in the `.backwardE h_E` arm
-- `cases p'`.  The `.forwardE _` and `.bidir _` arms close by
-- `h_hinge.elim` because their predicate clauses return `False` — at
-- index `0` we additionally `cases p'` to force the inner pattern
-- match to fire (both `(.nil _ _)` and `(.cons _ _ _)` produce
-- `False`, so `cases p' <;> exact h_hinge.elim`); at index `k + 1`
-- the single clauses `.cons _ (.forwardE _) _, _ + 1 => False` and
-- `.cons _ (.bidir _) _, _ + 1 => False` fire regardless of `p'`.
--
-- *Forward step constructor reuse: `forwardStep := .forwardE h_E`.*
-- The left arm `L : refactor_Walk G vMid u` traverses `vMid → u` via
-- a single forward edge.  The outer cons step `s = .backwardE h_E :
-- refactor_WalkStep G u vMid` already carries
-- `h_E : (vMid, u) ∈ G.E` — exactly the witness that `.forwardE`
-- expects on a step `vMid → u`.  Same proof term, opposite-direction
-- constructor; the endpoint-index flip is by intent — the typed
-- `WalkStep` makes the channel/orientation swap structural rather
-- than tucked behind a `Or.inl ⟨..., Or.inl ...⟩` redirection (the
-- OLD's encoding).  `L.refactor_IsDirectedWalk` for
-- `cons u (.forwardE h_E) (nil u _)` then reduces via the predicate
-- to `(nil u _).refactor_IsDirectedWalk = True`, closed by
-- `trivial`.
--
-- *Predicate clause data collapses to a single proposition.*  The
-- OLD's `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := h_hinge` triple is
-- replaced by a bare rename: after `cases s | backwardE h_E` and
-- the relevant `cases p'`, the predicate clauses
-- `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 =>
--    p.refactor_IsDirectedWalk` (zero case) and
-- `.cons _ (.backwardE _) p, k + 1 =>
--    p.refactor_IsBifurcationDirectedHingeWithSplit k`
-- (succ case) return single propositions directly, with no
-- conjunctive structure to deconstruct.  Vertex-list bookkeeping
-- (`List.dropLast_cons_of_ne_nil`, `simpa`, `change`-rewrites)
-- ports mechanically with `vertices → refactor_vertices`,
-- `vertices_ne_nil → refactor_vertices_ne_nil`,
-- `vertices_comp → refactor_vertices_comp`, etc.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.exists_arms_of_bifurcation_directed_hinge (was: refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge)
/-- **Subtask 7 of `claim_3_5` (the arm extractor — refactor twin):**
given a bifurcation walk `p : refactor_Walk G v w` together with a
directed-hinge witness `p.refactor_IsBifurcationDirectedHingeWithSplit i`,
extract the source vertex `c = p.refactor_vertices[i + 1]`, a directed
left arm `L : refactor_Walk G c v` of length `≥ 1` whose vertices lie
in `p.refactor_vertices.dropLast`, and a directed right arm
`R : refactor_Walk G c w` of length `≥ 1` whose vertices lie in
`p.refactor_vertices.tail`.

Proof: outer `induction p generalizing i`.  In the `cons` case,
case-split `s` first (the typed `refactor_WalkStep` constructor),
then inside `.backwardE h_E` case-split `p'`. -/
private lemma refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge
    {G : refactor_CDMG Node} {v w : Node} (p : refactor_Walk G v w) :
    ∀ (i : ℕ), p.refactor_IsBifurcationDirectedHingeWithSplit i →
      ∃ (c : Node) (L : refactor_Walk G c v) (R : refactor_Walk G c w),
        L.refactor_IsDirectedWalk ∧ R.refactor_IsDirectedWalk ∧
        L.refactor_length ≥ 1 ∧ R.refactor_length ≥ 1 ∧
        p.refactor_vertices[i + 1]? = some c ∧
        (∀ x ∈ L.refactor_vertices, x ∈ p.refactor_vertices.dropLast) ∧
        (∀ x ∈ R.refactor_vertices, x ∈ p.refactor_vertices.tail) := by
  induction p with
  | nil v hv =>
      intro i h_hinge
      exact h_hinge.elim
  | @cons u w vMid s p' ih =>
      intro i h_hinge
      cases i with
      | zero =>
          cases s with
          | forwardE _ =>
              cases p' <;> exact h_hinge.elim
          | bidir _ =>
              cases p' <;> exact h_hinge.elim
          | backwardE h_E =>
              cases p' with
              | nil v_p' h_p' =>
                  exact h_hinge.elim
              | cons vMid' s' p'' =>
                  -- Predicate clause:
                  --   .cons _ (.backwardE _) (p@(.cons _ _ _)), 0 =>
                  --     p.refactor_IsDirectedWalk
                  -- so h_hinge : (cons vMid' s' p'').refactor_IsDirectedWalk.
                  have hu_in_G : u ∈ G :=
                    refactor_WalkStep.refactor_source_mem (.backwardE h_E)
                  let forwardStep : refactor_WalkStep G vMid u := .forwardE h_E
                  refine ⟨vMid,
                          refactor_Walk.cons u forwardStep (refactor_Walk.nil u hu_in_G),
                          refactor_Walk.cons vMid' s' p'',
                          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- L.refactor_IsDirectedWalk reduces to
                    -- (nil u _).refactor_IsDirectedWalk = True.
                    trivial
                  · -- R.refactor_IsDirectedWalk
                    exact h_hinge
                  · -- L.refactor_length ≥ 1
                    change 0 + 1 ≥ 1
                    exact Nat.le_refl 1
                  · -- R.refactor_length ≥ 1
                    change p''.refactor_length + 1 ≥ 1
                    exact Nat.succ_le_succ (Nat.zero_le _)
                  · -- p.refactor_vertices[1]? = some vMid
                    rfl
                  · -- ∀ x ∈ L.refactor_vertices, x ∈ p.refactor_vertices.dropLast
                    intro x hx
                    -- L.refactor_vertices = [vMid, u].
                    have hxv : x = vMid ∨ x = u := by
                      rcases List.mem_cons.mp hx with rfl | hx2
                      · exact Or.inl rfl
                      · rcases List.mem_cons.mp hx2 with rfl | hx3
                        · exact Or.inr rfl
                        · simp at hx3
                    -- p.refactor_vertices.dropLast = u :: vMid :: p''.refactor_vertices.dropLast.
                    have hp'_ne :
                        (refactor_Walk.cons vMid' s' p'').refactor_vertices ≠ [] :=
                      refactor_Walk.refactor_vertices_ne_nil _
                    have hp''_ne : p''.refactor_vertices ≠ [] :=
                      refactor_Walk.refactor_vertices_ne_nil _
                    change x ∈
                      (u :: (refactor_Walk.cons vMid' s' p'').refactor_vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.refactor_vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases hxv with rfl | rfl
                    · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                    · exact List.mem_cons_self
                  · -- ∀ x ∈ R.refactor_vertices, x ∈ p.refactor_vertices.tail
                    intro x hx
                    change x ∈
                      (u :: (refactor_Walk.cons vMid' s' p'').refactor_vertices).tail
                    exact hx
      | succ k =>
          cases s with
          | forwardE _ =>
              cases p' <;> exact h_hinge.elim
          | bidir _ =>
              cases p' <;> exact h_hinge.elim
          | backwardE h_E =>
              cases p' with
              | nil vNil hNil =>
                  -- After cases s | backwardE, the predicate reduces to
                  -- p'.refactor_IsBifurcationDirectedHingeWithSplit k.
                  -- With p' = nil, the .nil clause returns False.
                  exact h_hinge.elim
              | cons vMid' s' p'' =>
                  -- Predicate's recursion clause:
                  --   .cons _ (.backwardE _) p, k + 1 =>
                  --     p.refactor_IsBifurcationDirectedHingeWithSplit k
                  -- so h_hinge : (cons vMid' s' p'').refactor_IsBifurcationDirectedHingeWithSplit k.
                  -- Apply IH to p' and k.
                  obtain ⟨c, L', R, hL'_dir, hR_dir, _hL'_pos, hR_pos, h_idx_p',
                          hL'_sub, hR_sub⟩ :=
                    ih k h_hinge
                  -- Build L_new : refactor_Walk G c u by composing L' with a
                  -- single forward edge from vMid to u.
                  have hu_in_G : u ∈ G :=
                    refactor_WalkStep.refactor_source_mem (.backwardE h_E)
                  let forwardStep : refactor_WalkStep G vMid u := .forwardE h_E
                  let single : refactor_Walk G vMid u :=
                    refactor_Walk.cons u forwardStep (refactor_Walk.nil u hu_in_G)
                  have hsingle_dir : single.refactor_IsDirectedWalk := trivial
                  refine ⟨c, L'.refactor_comp single, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- (L'.refactor_comp single).refactor_IsDirectedWalk
                    exact refactor_Walk.refactor_isDirectedWalk_comp L' single
                      hL'_dir hsingle_dir
                  · -- R.refactor_IsDirectedWalk
                    exact hR_dir
                  · -- (L'.refactor_comp single).refactor_length ≥ 1
                    rw [refactor_Walk.refactor_length_comp]
                    change L'.refactor_length + 1 ≥ 1
                    exact Nat.succ_le_succ (Nat.zero_le _)
                  · -- R.refactor_length ≥ 1
                    exact hR_pos
                  · -- p.refactor_vertices[(k+1) + 1]? = some c
                    -- p.refactor_vertices = u :: p'.refactor_vertices.
                    change (u :: (refactor_Walk.cons vMid' s' p'').refactor_vertices)[k + 1 + 1]? = some c
                    simpa using h_idx_p'
                  · -- ∀ x ∈ (L'.refactor_comp single).refactor_vertices,
                    --   x ∈ p.refactor_vertices.dropLast
                    intro x hx
                    -- (L'.comp single).refactor_vertices
                    --   = L'.refactor_vertices.dropLast ++ single.refactor_vertices
                    --   = L'.refactor_vertices.dropLast ++ [vMid, u].
                    have hL_new_vs : (L'.refactor_comp single).refactor_vertices
                        = L'.refactor_vertices.dropLast ++ [vMid, u] := by
                      rw [refactor_Walk.refactor_vertices_comp]
                      rfl
                    rw [hL_new_vs] at hx
                    -- p.refactor_vertices.dropLast
                    --   = u :: vMid :: p''.refactor_vertices.dropLast.
                    have hp'_ne :
                        (refactor_Walk.cons vMid' s' p'').refactor_vertices ≠ [] :=
                      refactor_Walk.refactor_vertices_ne_nil _
                    have hp''_ne : p''.refactor_vertices ≠ [] :=
                      refactor_Walk.refactor_vertices_ne_nil _
                    change x ∈
                      (u :: (refactor_Walk.cons vMid' s' p'').refactor_vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.refactor_vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases List.mem_append.mp hx with hL'drop | h_in_tail
                    · -- x ∈ L'.refactor_vertices.dropLast: lift to
                      -- x ∈ L'.refactor_vertices via mem_of_mem_dropLast,
                      -- then to x ∈ p'.refactor_vertices.dropLast via hL'_sub.
                      have hx_L'_vertices : x ∈ L'.refactor_vertices :=
                        List.mem_of_mem_dropLast hL'drop
                      have hx_p'_drop :
                          x ∈ (refactor_Walk.cons vMid' s' p'').refactor_vertices.dropLast :=
                        hL'_sub x hx_L'_vertices
                      have hx_in : x ∈ (vMid :: p''.refactor_vertices).dropLast := by
                        have h_eq :
                            (refactor_Walk.cons vMid' s' p'').refactor_vertices.dropLast
                            = (vMid :: p''.refactor_vertices).dropLast := by
                          rfl
                        rw [h_eq] at hx_p'_drop
                        exact hx_p'_drop
                      rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_in
                      exact List.mem_cons.mpr (Or.inr hx_in)
                    · -- x ∈ [vMid, u]
                      rcases List.mem_cons.mp h_in_tail with rfl | hx_in2
                      · -- x = vMid
                        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                      · rcases List.mem_cons.mp hx_in2 with rfl | hx_empty
                        · -- x = u
                          exact List.mem_cons_self
                        · simp at hx_empty
                  · -- ∀ x ∈ R.refactor_vertices, x ∈ p.refactor_vertices.tail
                    intro x hx
                    have hx_p'_tail :
                        x ∈ (refactor_Walk.cons vMid' s' p'').refactor_vertices.tail :=
                      hR_sub x hx
                    have hx_p' :
                        x ∈ (refactor_Walk.cons vMid' s' p'').refactor_vertices :=
                      List.mem_of_mem_tail hx_p'_tail
                    change x ∈
                      (u :: (refactor_Walk.cons vMid' s' p'').refactor_vertices).tail
                    exact hx_p'
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.exists_arms_of_bifurcation_directed_hinge

-- ## Refactor-port design block — `refactor_bifurcationAlternative` (subtask 8 of `claim_3_5`)
--
-- *Mathematical content unchanged.*  This is the main theorem
-- twin for `claim_3_5` in the `cdmg_typed_edges` refactor.  Both
-- directions of the proof are mechanical ports of the ORIGINAL
-- `bifurcationAlternative` body above: every helper call is
-- swapped for its `refactor_`-prefixed twin (built in subtasks
-- 1–7 of the workspace plan), the cons-cell pattern shrinks from
-- four args (`vMid a h p`) to three (`vMid s p`), and `cases h`
-- on the OLD propositional `WalkStep` becomes a structural
-- `cases s` on the typed `refactor_WalkStep`.  The underlying
-- argument (shortest-walk truncation, concatenation, reversal,
-- and the five-clause verification of `def_3_4` item~vi) is
-- preserved verbatim.
--
-- *Channel-of-bifurcation: directed-only.*  Both the (⇒) and
-- (⇐) directions reason exclusively through *directed* walks
-- (the two arms of the bifurcation, lifted into the intervened
-- CDMGs `G_{do({w})}` / `G_{do({v})}`).  The bidirected L-channel
-- never appears structurally in the theorem body.  Consequently
-- the refactor's central encoding change (`Finset (Node × Node)`
-- → `Finset (Sym2 Node)` on `G.L`, plus elimination of `hL_symm`)
-- is neutral here: no `Sym2.mk` / `Sym2.mem_mk_left` calls appear
-- in this body — bidirected-edge handling lives entirely in the
-- supporting helpers (most prominently
-- `refactor_WalkStep.refactor_source_mem`, which case-splits the
-- typed `.bidir` constructor in subtask 4's
-- `refactor_truncateAtFirst`).
--
-- *Direct call-site swap.*  Every ORIGINAL helper used by the
-- theorem body has been ported above as a `refactor_`-prefixed
-- twin in this `namespace refactor_CDMG` block:
-- `refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge`
-- (subtask 7, the arm extractor); `refactor_head_mem_vertices`,
-- `refactor_vertices_eq_head_cons_tail`,
-- `refactor_liftTo_hardInterventionOn`,
-- `refactor_isDirectedWalk_liftTo_hardInterventionOn`,
-- `refactor_vertices_directed_avoid_of_hardInterventionOn`
-- (subtask 3); `refactor_exists_directed_walk_v_not_in_dropLast`
-- (subtask 4); `refactor_liftFromHardIntervention`,
-- `refactor_isDirectedWalk_liftFromHardIntervention`,
-- `refactor_vertices_liftFromHardIntervention`,
-- `refactor_length_liftFromHardIntervention` (subtask 1);
-- `refactor_mkBifurcation`, `refactor_vertices_mkBifurcation`,
-- `refactor_vertices_ne_nil` (subtask 5);
-- `refactor_isBifurcationDirectedHinge_mkBifurcation`
-- (subtask 6).  The proof body just swaps each call site to its
-- refactor twin.

-- ref: claim_3_5
-- For any CDMG `G : refactor_CDMG Node` and any three (not
-- necessarily distinct) nodes `v, w, c ∈ G` (i.e. `v, w, c ∈ G.J
-- ∪ G.V`), the following are equivalent:
--
-- (a) *Existence of a bifurcation between `v` and `w` with source
--     `c`.*  There exists a walk `p : refactor_Walk G v w` such
--     that `p.refactor_IsBifurcationSource c` (in the sense of
--     `def_3_4`'s trailing `refactor_IsBifurcationSource`
--     predicate).  This single existential packages both the LN's
--     "`p` is a bifurcation between `v` and `w`" (clauses (a)–(e)
--     of `def_3_4` item~vi, including the `v ≠ w` first-half of
--     clause (a) and the end-node-uniqueness clause), and the
--     LN's "the bifurcation has source `c`" (the closing
--     paragraph of `def_3_4` item~vi).  Under the `def_3_4`
--     encoding's chapter-init addition
--     `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
--     `refactor_IsBifurcationSource p c` automatically commits to
--     the interior-source convention `1 ≤ k ≤ n - 1`
--     (`0 ≤ i ≤ n - 2` in the Lean encoding), so `c ≠ v` and
--     `c ≠ w` are consequences of (a), not extra hypotheses.
--
-- (b) *Set-theoretic ancestral characterisation.*
--     The conjunction of:
--       (i)   `v ≠ w`;
--       (ii)  `c ∈ (G.refactor_hardInterventionOn {w} _).refactor_Anc v \ {v}`,
--             i.e. `c` is an ancestor of `v` in the
--             do-on-`{w}` intervened CDMG (`def_3_10` +
--             `def_3_5`'s `refactor_Anc`), and `c ≠ v`;
--       (iii) `c ∈ (G.refactor_hardInterventionOn {v} _).refactor_Anc w \ {w}`,
--             i.e. `c` is an ancestor of `w` in the
--             do-on-`{v}` intervened CDMG, and `c ≠ w`.
--
-- The `_` in (ii) and (iii) is the singleton-subset witness
-- `{w} ⊆ G.J ∪ G.V` / `{v} ⊆ G.J ∪ G.V`, supplied here by
-- `Finset.singleton_subset_iff.mpr hw` / `… hv` (recovering the
-- LN's "the lowercase `w` / `v` inside the `do(·)` slot is
-- shorthand for the singleton sets `{w}` / `{v}`" reading of
-- `def_3_10`'s `W` argument).
/-
LN tex (verbatim, from `graphs.tex`,
`\label{prp:bifurcations_alternative}`):

  \begin{Prp}\label{prp:bifurcations_alternative}
    Let $G = \lt J, V, E, L \rt$ be a CDMG.  For $v, w, c \in V
    \cup J$: there exists a bifurcation between $v$ and $w$ in
    $G$ with source $c$ if and only if $v \ne w$ and $c \in
    \Anc^{G_{\doit(w)}}(v) \sm \{v\}$ and $c \in
    \Anc^{G_{\doit(v)}}(w) \sm \{w\}$.
  \end{Prp}
-/
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: bifurcationAlternative (was: refactor_bifurcationAlternative)
-- claim_3_5 -- start statement
theorem refactor_bifurcationAlternative (G : refactor_CDMG Node) (v w c : Node)
    (hv : v ∈ G) (hw : w ∈ G) (hc : c ∈ G) :
    (∃ p : refactor_Walk G v w, p.refactor_IsBifurcationSource c)
      ↔
        v ≠ w
      ∧ c ∈ (G.refactor_hardInterventionOn {w}
              (Finset.singleton_subset_iff.mpr hw)).refactor_Anc v \ {v}
      ∧ c ∈ (G.refactor_hardInterventionOn {v}
              (Finset.singleton_subset_iff.mpr hv)).refactor_Anc w \ {w}
-- claim_3_5 -- end statement
  := by
  -- `hc` is part of the universal scope `v, w, c ∈ J ∪ V` per
  -- `def_3_2`; the RHS's `refactor_Anc` conjunct independently
  -- forces `c ∈ G`, but we carry `hc` for LN-faithfulness of the
  -- binder block.  The `let _` pin keeps it visible if the (⇒)
  -- direction's `Finset.mem_union.mp hc` would otherwise leave it
  -- unmentioned in the proof skeleton.
  let _ := hc
  constructor
  · -- (⇒) direction: from the bifurcation walk extract the two
    -- directed arms (subtask 7), then lift each arm into the
    -- appropriate intervened CDMG (subtask 3).
    rintro ⟨p, h_bif⟩
    obtain ⟨huv_ne, hu_tail, hv_drop, i, h_hinge, h_src⟩ := h_bif
    obtain ⟨c', L, R, hL_dir, hR_dir, hL_pos, hR_pos, hc_idx, hL_sub, hR_sub⟩ :=
      refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge p i h_hinge
    -- Identify `c' = c` using the source-index identification.  We
    -- keep both names alive (rather than `subst`-ing) so the
    -- theorem's universally-quantified `c` stays visible to the
    -- final `refine`'s LN-faithful conjuncts.
    have hc'_eq_c : c' = c := by
      rw [hc_idx] at h_src
      exact Option.some.inj h_src
    -- `c'` lies in `p.refactor_vertices.dropLast` (head of `L`'s
    -- vertices, all of which are in `p.refactor_vertices.dropLast`
    -- by `hL_sub`), and in `p.refactor_vertices.tail` (head of
    -- `R`'s vertices, all in `p.refactor_vertices.tail` by
    -- `hR_sub`).
    have hc'_in_drop : c' ∈ p.refactor_vertices.dropLast :=
      hL_sub c' (refactor_Walk.refactor_head_mem_vertices L)
    have hc'_in_tail : c' ∈ p.refactor_vertices.tail :=
      hR_sub c' (refactor_Walk.refactor_head_mem_vertices R)
    have hc_ne_v : c ≠ v := by
      intro h
      apply hu_tail
      have heq : c' = v := hc'_eq_c.trans h
      exact heq ▸ hc'_in_tail
    have hc_ne_w : c ≠ w := by
      intro h
      apply hv_drop
      have heq : c' = w := hc'_eq_c.trans h
      exact heq ▸ hc'_in_drop
    -- `c ∈ G_{do(w)}`: from `c ∈ G` (which is `c ∈ G.J ∪ G.V`)
    -- plus `c ≠ w`, we conclude `c ∈ (G.J ∪ {w}) ∪ (G.V \ {w})`.
    have hc_in_Gdow :
        c ∈ G.refactor_hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw) := by
      change c ∈ (G.J ∪ {w}) ∪ (G.V \ {w})
      rcases Finset.mem_union.mp hc with hJ | hV
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        rw [Finset.mem_singleton]
        exact hc_ne_w
    have hc_in_Gdov :
        c ∈ G.refactor_hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv) := by
      change c ∈ (G.J ∪ {v}) ∪ (G.V \ {v})
      rcases Finset.mem_union.mp hc with hJ | hV
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        rw [Finset.mem_singleton]
        exact hc_ne_v
    -- Transfer `c ∈ G_{do(w)}` to `c' ∈ G_{do(w)}` (and similarly
    -- for `c' ∈ G_{do(v)}`) so the lift consumer accepts
    -- `L : refactor_Walk G c' v` / `R : refactor_Walk G c' w`
    -- directly.
    have hc'_in_Gdow :
        c' ∈ G.refactor_hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw) := hc'_eq_c ▸ hc_in_Gdow
    have hc'_in_Gdov :
        c' ∈ G.refactor_hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv) := hc'_eq_c ▸ hc_in_Gdov
    -- Avoidance hypotheses for the lift: every tail-vertex of the
    -- left arm avoids `{w}`, and every tail-vertex of the right
    -- arm avoids `{v}`.  Both follow from `hL_sub` / `hR_sub` plus
    -- the end-node uniqueness clauses.
    have hL_avoid_w : ∀ x ∈ L.refactor_vertices.tail, x ∉ ({w} : Finset Node) := by
      intro x hx hxw
      rw [Finset.mem_singleton] at hxw
      exact hv_drop (hxw ▸ hL_sub x (List.mem_of_mem_tail hx))
    have hR_avoid_v : ∀ x ∈ R.refactor_vertices.tail, x ∉ ({v} : Finset Node) := by
      intro x hx hxv
      rw [Finset.mem_singleton] at hxv
      exact hu_tail (hxv ▸ hR_sub x (List.mem_of_mem_tail hx))
    refine ⟨huv_ne, ?_, ?_⟩
    · -- `c ∈ Anc^{G_{do(w)}}(v) \ {v}`.  Build at `c'` first, then
      -- transport via `hc'_eq_c`.
      refine ⟨hc'_eq_c ▸ ⟨hc'_in_Gdow,
              refactor_Walk.refactor_liftTo_hardInterventionOn L hc'_in_Gdow hL_dir hL_avoid_w,
              refactor_Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
                L hc'_in_Gdow hL_dir hL_avoid_w⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hc_ne_v
    · -- `c ∈ Anc^{G_{do(v)}}(w) \ {w}`.
      refine ⟨hc'_eq_c ▸ ⟨hc'_in_Gdov,
              refactor_Walk.refactor_liftTo_hardInterventionOn R hc'_in_Gdov hR_dir hR_avoid_v,
              refactor_Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
                R hc'_in_Gdov hR_dir hR_avoid_v⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hc_ne_w
  · -- (⇐) direction: extract minimum-length directed walks in
    -- each intervened CDMG (subtask 4), lift them back to `G`
    -- (subtask 1), assemble the bifurcation walk (subtask 5), and
    -- verify `refactor_IsBifurcationSource` (subtask 6 plus
    -- vertex bookkeeping).
    rintro ⟨hvw_ne, hc_anc_v_full, hc_anc_w_full⟩
    have hc_ne_v : c ≠ v := fun h =>
      hc_anc_v_full.2 (Set.mem_singleton_iff.mpr h)
    have hc_ne_w : c ≠ w := fun h =>
      hc_anc_w_full.2 (Set.mem_singleton_iff.mpr h)
    have hc_in_Gdow_anc :
        c ∈ (G.refactor_hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw)).refactor_Anc v := hc_anc_v_full.1
    have hc_in_Gdov_anc :
        c ∈ (G.refactor_hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv)).refactor_Anc w := hc_anc_w_full.1
    obtain ⟨q_v_Gdow, hq_v_Gdow_dir, hq_v_Gdow_drop⟩ :=
      refactor_exists_directed_walk_v_not_in_dropLast hc_in_Gdow_anc hc_ne_v
    obtain ⟨q_w_Gdov, hq_w_Gdov_dir, hq_w_Gdov_drop⟩ :=
      refactor_exists_directed_walk_v_not_in_dropLast hc_in_Gdov_anc hc_ne_w
    -- Inline structural-walk-length identity:
    -- `q.refactor_vertices.length = q.refactor_length + 1` (used
    -- downstream to derive `q.refactor_vertices.tail ≠ []` from
    -- `q.refactor_length ≥ 1`).  Refactor port: `cons _ _ _ q' ih`
    -- becomes `cons _ _ q' ih` (3-arg).
    have hvert_len_succ :
        ∀ {G' : refactor_CDMG Node} {u₁ u₂ : Node}
          (q : refactor_Walk G' u₁ u₂),
          q.refactor_vertices.length = q.refactor_length + 1 := by
      intro G' u₁ u₂ q
      induction q with
      | nil _ _ => rfl
      | cons _ _ q' ih =>
        change q'.refactor_vertices.length + 1 = q'.refactor_length + 1 + 1
        omega
    -- The two source walks have length `≥ 1`: a length-`0` walk
    -- would be `refactor_Walk.nil`, forcing `c = v` (resp. `c = w`)
    -- and contradicting `hc_ne_v` (resp. `hc_ne_w`).  Refactor
    -- port: `cons _ _ _ _` becomes `cons _ _ _` (3-arg).
    have hq_v_Gdow_pos : q_v_Gdow.refactor_length ≥ 1 := by
      cases q_v_Gdow with
      | nil _ _ => exact (hc_ne_v rfl).elim
      | cons _ _ _ =>
        change _ + 1 ≥ 1
        exact Nat.succ_le_succ (Nat.zero_le _)
    have hq_w_Gdov_pos : q_w_Gdov.refactor_length ≥ 1 := by
      cases q_w_Gdov with
      | nil _ _ => exact (hc_ne_w rfl).elim
      | cons _ _ _ =>
        change _ + 1 ≥ 1
        exact Nat.succ_le_succ (Nat.zero_le _)
    -- Tail-vertices of `q_v_Gdow` / `q_w_Gdov` avoid `{w}` / `{v}`
    -- by the head-of-edge argument of `def_3_10` item iii
    -- (subtask 3a).
    have hq_v_Gdow_avoid :
        ∀ x ∈ q_v_Gdow.refactor_vertices.tail, x ∉ ({w} : Finset Node) :=
      refactor_Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
        q_v_Gdow hq_v_Gdow_dir
    have hq_w_Gdov_avoid :
        ∀ x ∈ q_w_Gdov.refactor_vertices.tail, x ∉ ({v} : Finset Node) :=
      refactor_Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
        q_w_Gdov hq_w_Gdov_dir
    -- Abbreviations for the lifted walks in `G`.
    set qv := refactor_Walk.refactor_liftFromHardIntervention q_v_Gdow with hqv_def
    set qw := refactor_Walk.refactor_liftFromHardIntervention q_w_Gdov with hqw_def
    have hqv_dir : qv.refactor_IsDirectedWalk :=
      refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention
        q_v_Gdow hq_v_Gdow_dir
    have hqw_dir : qw.refactor_IsDirectedWalk :=
      refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention
        q_w_Gdov hq_w_Gdov_dir
    have hqv_verts : qv.refactor_vertices = q_v_Gdow.refactor_vertices :=
      refactor_Walk.refactor_vertices_liftFromHardIntervention q_v_Gdow
    have hqw_verts : qw.refactor_vertices = q_w_Gdov.refactor_vertices :=
      refactor_Walk.refactor_vertices_liftFromHardIntervention q_w_Gdov
    have hqv_len : qv.refactor_length = q_v_Gdow.refactor_length :=
      refactor_Walk.refactor_length_liftFromHardIntervention q_v_Gdow
    have hqw_len : qw.refactor_length = q_w_Gdov.refactor_length :=
      refactor_Walk.refactor_length_liftFromHardIntervention q_w_Gdov
    have hqv_pos : qv.refactor_length ≥ 1 := by rw [hqv_len]; exact hq_v_Gdow_pos
    have hqw_pos : qw.refactor_length ≥ 1 := by rw [hqw_len]; exact hq_w_Gdov_pos
    have hqv_head : qv.refactor_vertices = c :: qv.refactor_vertices.tail :=
      refactor_Walk.refactor_vertices_eq_head_cons_tail qv
    have hqw_head : qw.refactor_vertices = c :: qw.refactor_vertices.tail :=
      refactor_Walk.refactor_vertices_eq_head_cons_tail qw
    have hqv_vs_len : qv.refactor_vertices.length = qv.refactor_length + 1 :=
      hvert_len_succ qv
    have hqw_vs_len : qw.refactor_vertices.length = qw.refactor_length + 1 :=
      hvert_len_succ qw
    have hqv_tail_ne_nil : qv.refactor_vertices.tail ≠ [] := by
      intro h
      have h1 : qv.refactor_vertices.length = 1 := by rw [hqv_head]; simp [h]
      omega
    have hqw_tail_ne_nil : qw.refactor_vertices.tail ≠ [] := by
      intro h
      have h1 : qw.refactor_vertices.length = 1 := by rw [hqw_head]; simp [h]
      omega
    have hqv_tail_rev_ne_nil : qv.refactor_vertices.tail.reverse ≠ [] :=
      fun h => hqv_tail_ne_nil (List.reverse_eq_nil_iff.mp h)
    -- Tail-vertex avoidance, transferred from the intervened to
    -- lifted form.
    have hqv_avoid_w : ∀ x ∈ qv.refactor_vertices.tail, x ≠ w := by
      intro x hx hxw
      have hx_Gdow : x ∈ q_v_Gdow.refactor_vertices.tail := by
        rw [hqv_verts] at hx; exact hx
      exact hq_v_Gdow_avoid x hx_Gdow (by
        rw [Finset.mem_singleton]; exact hxw)
    have hqw_avoid_v : ∀ x ∈ qw.refactor_vertices.tail, x ≠ v := by
      intro x hx hxv
      have hx_Gdov : x ∈ q_w_Gdov.refactor_vertices.tail := by
        rw [hqw_verts] at hx; exact hx
      exact hq_w_Gdov_avoid x hx_Gdov (by
        rw [Finset.mem_singleton]; exact hxv)
    -- Minimum-length dropLast clauses transferred.
    have hqv_drop_v : v ∉ qv.refactor_vertices.dropLast := by
      rw [hqv_verts]; exact hq_v_Gdow_drop
    have hqw_drop_w : w ∉ qw.refactor_vertices.dropLast := by
      rw [hqw_verts]; exact hq_w_Gdov_drop
    -- Cross-arm non-memberships: `v ∉ qw.refactor_vertices` and
    -- `w ∉ qv.refactor_vertices`.
    have hv_notin_qw : v ∉ qw.refactor_vertices := by
      rw [hqw_head]
      intro hv_in
      rcases List.mem_cons.mp hv_in with hv_eq_c | hv_in_tail
      · exact hc_ne_v hv_eq_c.symm
      · exact hqw_avoid_v v hv_in_tail rfl
    have hw_notin_qv : w ∉ qv.refactor_vertices := by
      rw [hqv_head]
      intro hw_in
      rcases List.mem_cons.mp hw_in with hw_eq_c | hw_in_tail
      · exact hc_ne_w hw_eq_c.symm
      · exact hqv_avoid_w w hw_in_tail rfl
    -- The vertex list of the bifurcation walk:
    --   p.refactor_vertices = qv.refactor_vertices.reverse.dropLast
    --                          ++ qw.refactor_vertices
    --                       = qv.refactor_vertices.tail.reverse
    --                          ++ qw.refactor_vertices.
    have hp_verts :
        (refactor_Walk.refactor_mkBifurcation qv hqv_dir hqv_pos qw).refactor_vertices
          = qv.refactor_vertices.tail.reverse ++ qw.refactor_vertices := by
      rw [refactor_Walk.refactor_vertices_mkBifurcation qv hqv_dir hqv_pos qw]
      conv_lhs => rw [hqv_head, List.reverse_cons, List.dropLast_concat]
    -- Index arithmetic: `qv.refactor_length - 1 + 1 = qv.refactor_length`
    -- and `qv.refactor_vertices.tail.reverse.length = qv.refactor_length`.
    have hidx_succ : qv.refactor_length - 1 + 1 = qv.refactor_length := by omega
    have hqv_tail_rev_len :
        qv.refactor_vertices.tail.reverse.length = qv.refactor_length := by
      rw [List.length_reverse]
      have hlen : qv.refactor_vertices.tail.length + 1
          = qv.refactor_vertices.length := by
        rw [hqv_head]; simp
      omega
    -- Construct the bifurcation walk and discharge each clause of
    -- `refactor_IsBifurcationSource`.
    refine ⟨refactor_Walk.refactor_mkBifurcation qv hqv_dir hqv_pos qw,
            hvw_ne, ?_, ?_, qv.refactor_length - 1, ?_, ?_⟩
    · -- (1) `v ∉ p.refactor_vertices.tail`.
      rw [hp_verts, List.tail_append_of_ne_nil hqv_tail_rev_ne_nil]
      intro hv_in
      rcases List.mem_append.mp hv_in with hv_left | hv_right
      · rw [List.tail_reverse, List.mem_reverse] at hv_left
        apply hqv_drop_v
        rw [hqv_head, List.dropLast_cons_of_ne_nil hqv_tail_ne_nil]
        exact List.mem_cons.mpr (Or.inr hv_left)
      · exact hv_notin_qw hv_right
    · -- (2) `w ∉ p.refactor_vertices.dropLast`.
      rw [hp_verts, List.dropLast_append_of_ne_nil
              (l := qw.refactor_vertices) (l' := qv.refactor_vertices.tail.reverse)
              (refactor_Walk.refactor_vertices_ne_nil qw)]
      intro hw_in
      rcases List.mem_append.mp hw_in with hw_left | hw_right
      · rw [List.mem_reverse] at hw_left
        apply hw_notin_qv
        rw [hqv_head]
        exact List.mem_cons.mpr (Or.inr hw_left)
      · exact hqw_drop_w hw_right
    · -- (3) `refactor_IsBifurcationDirectedHingeWithSplit (qv.refactor_length - 1)`.
      exact refactor_Walk.refactor_isBifurcationDirectedHinge_mkBifurcation
        qv hqv_dir hqv_pos qw hqw_dir hqw_pos
    · -- (4) `p.refactor_vertices[qv.refactor_length - 1 + 1]? = some c`.
      rw [hidx_succ, hp_verts,
          List.getElem?_append_right (hqv_tail_rev_len ▸ Nat.le_refl _)]
      rw [hqv_tail_rev_len, Nat.sub_self]
      rw [hqw_head]
      rfl
-- REFACTOR-BLOCK-REPLACEMENT-END: bifurcationAlternative

end refactor_CDMG

end Causality
