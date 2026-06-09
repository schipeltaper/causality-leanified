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
-- claim_3_5 --- start helper

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
-- claim_3_5 --- end helper

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
-- claim_3_5 --- start helper

/-- Concatenate two walks `p : Walk G u v` and `q : Walk G v w` into a
walk `Walk G u w`.  The `nil` case forwards `q` unchanged; the `cons`
case recurses on the tail and re-attaches the head edge.  Verbatim copy
of `AcyclicIffTopologicalOrder.lean`'s `private Walk.comp`; re-declared
locally because the sibling copy is `private`. -/
private def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v a h p, q => .cons v a h (p.comp q)

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

/-- Auxiliary: every walk's `vertices` list is non-empty.  The `nil`
walk gives `[v]`; every `cons` cell prepends a new head vertex.  Needed
by `Walk.vertices_comp`'s `cons` case to discharge the side condition
of `List.dropLast_cons_of_ne_nil`. -/
private lemma Walk.vertices_ne_nil {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ _ => by simp [Walk.vertices]

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
-- claim_3_5 --- end helper

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
-- claim_3_5 --- start helper

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
-- claim_3_5 --- end helper

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
-- claim_3_5 --- start helper

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
-- claim_3_5 --- end helper

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
-- claim_3_5 --- start helper

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
-- claim_3_5 --- end helper

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
-- claim_3_5 --- start helper

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
-- claim_3_5 --- end helper

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
-- claim_3_5 --- start helper

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
-- claim_3_5 --- end helper

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

end CDMG

end Causality
