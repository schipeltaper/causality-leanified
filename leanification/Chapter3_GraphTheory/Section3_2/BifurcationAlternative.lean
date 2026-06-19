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
-- (`CDMG`): the `Membership Node (CDMG Node)`
-- instance from `def_3_2`'s refactor twin (`instMembership`
-- in `CDMGNotation.lean`) reduces to `Finset.mem` on `G.J ∪ G.V` and
-- so needs `DecidableEq Node`; the `Walk` recursion in the
-- four walk-class helpers, the `IsDirectedWalk` /
-- `IsBifurcationSource` Props in the main theorem body, and
-- the `G.Anc v` set-builder all transitively rely on
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
-- `CDMG.L` is retyped to `Finset (Sym2 Node)` (no
-- `hL_symm`), and `WalkStep` becomes a typed inductive
-- (`.forwardE` / `.backwardE` / `.bidir`) instead of the Prop-valued
-- disjunction.  But step~(0)'s edge-inclusion argument
-- (`E_{do(W)} ⊆ E` and `L_{do(W)} ⊆ L` follow from
-- `Finset.mem_filter`) is structurally unchanged, and so is the
-- walk-lift that uses it.

set_option linter.style.longLine false in
/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V` from the TeX statement block:
every node of the intervened CDMG is a node of `G`.  Consumes
`hW : W ⊆ G.J ∪ G.V` to fold the `W`-half of the left disjunct into
`G.J ∪ G.V`.  Body identical to the original — `G.J / G.V / W` are
unchanged by the `cdmg_typed_edges` refactor (only `L`'s type
changed), so the carrier-matching computation reads verbatim. -/
private lemma mem_of_mem_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {v : Node}
    (h : v ∈ G.hardInterventionOn W hW) : v ∈ G := by
  -- `v ∈ G.hardInterventionOn W hW` reduces by the
  -- `instMembership` instance (`def_3_2`'s refactor twin,
  -- `CDMGNotation.lean`) to `v ∈ (G.J ∪ W) ∪ (G.V \ W)`.
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJW | hVW
  · rcases Finset.mem_union.mp hJW with hJ | hWmem
    · exact Finset.mem_union_left _ hJ
    · exact hW hWmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1

set_option linter.style.longLine false in
/-- Per-edge content of step~(0): any typed `WalkStep` in
`G.hardInterventionOn W hW` is also a typed `WalkStep`
in `G`.  Under the refactor, `WalkStep` is a `Type _`-valued
inductive rather than a `Prop`, so this is a `def` (not a `lemma`)
that translates each constructor by stripping the `Finset.filter`
predicate via `Finset.mem_filter.mp`.

* `.forwardE h` and `.backwardE h` strip the `e.2 ∉ W` clause from
  the directed-edge filter and re-emit the same constructor.
* `.bidir h` strips the `∀ v ∈ s, v ∉ W` clause from the bidirected-
  edge filter and re-emits `.bidir`.  Under the `Sym2` encoding of
  `CDMG.L`, no symmetrisation step is needed — `s(u, v) =
  s(v, u)` is definitional, so the constructor preserves the
  unordered-pair identity verbatim. -/
private def Walk.refactor_liftWalkStep_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {u v : Node} :
    WalkStep (G.hardInterventionOn W hW) u v →
      WalkStep G u v
  | .forwardE h  => .forwardE  ((Finset.mem_filter.mp h).1)
  | .backwardE h => .backwardE ((Finset.mem_filter.mp h).1)
  | .bidir h     => .bidir     ((Finset.mem_filter.mp h).1)

set_option linter.style.longLine false in
/-- Step~(0)'s walk-lift, as a recursive function on `Walk`s:
a walk in the intervened CDMG `G.hardInterventionOn W hW`
is *the same tuple* viewed as a walk in `G`.  Each `cons` cell keeps
its middle vertex `v`; the typed WalkStep witness is replaced by its
lift through `Walk.refactor_liftWalkStep_of_hardInterventionOn`.

The cons-cell signature change is structural: under
`Walk.cons` the cons cell takes three explicit args
(`v`, `s`, `p`) rather than the original four (`v`, `a`, `h`, `p`).
The `a : Node × Node` is gone (the WalkStep carries its endpoints in
its type indices), and the Prop witness `h` is replaced by the typed
data `s : WalkStep G u v`. -/
private def Walk.refactor_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node},
      Walk (G.hardInterventionOn W hW) u v →
        Walk G u v
  | _, _, .nil w hw =>
      Walk.nil w (mem_of_mem_hardInterventionOn hw)
  | _, _, .cons vMid s p =>
      Walk.cons vMid
        (Walk.refactor_liftWalkStep_of_hardInterventionOn
          (hW := hW) s)
        (Walk.refactor_liftFromHardIntervention p)

set_option linter.style.longLine false in
/-- The walk-lift preserves `IsDirectedWalk`.

Under the refactor, `IsDirectedWalk` pattern-matches on the
typed WalkStep constructor: a `.forwardE` step advances the recursion
on the tail, while `.backwardE` and `.bidir` reduce to `False`
definitionally.  Consequently the proof simplifies from the
original's `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp` triple-conjunction
to a structural case-split on the typed step — the `.forwardE` case
recurses with no rewrite, and the other two close by `hp.elim`
(since `hp : False` for those constructors). -/
private lemma Walk.refactor_isDirectedWalk_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk →
        (Walk.refactor_liftFromHardIntervention
          (hW := hW) p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, hp =>
      Walk.refactor_isDirectedWalk_liftFromHardIntervention p hp
  | _, _, .cons _ (.backwardE _) _, hp => hp.elim
  | _, _, .cons _ (.bidir _) _, hp => hp.elim

set_option linter.style.longLine false in
/-- The walk-lift preserves `length`: each `cons` cell of
the input walk produces exactly one `cons` cell of the output walk,
with the same middle vertex / typed WalkStep data.  Body is the
original with the cons-cell pattern shrunk from four args to three
(the `a : Node × Node` is gone — see the design block on
`Walk.cons` in `Walks.lean`). -/
private lemma Walk.refactor_length_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.refactor_liftFromHardIntervention
        (hW := hW) p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p =>
      congrArg (· + 1)
        (Walk.refactor_length_liftFromHardIntervention p)

set_option linter.style.longLine false in
/-- The walk-lift preserves the underlying `vertices` list.
Each `cons` cell of the input keeps its middle vertex `v` verbatim
under the lift, so the induced list of vertices is byte-identical.
The `nil` case reduces to `[v] = [v]` definitionally; the `cons` case
is `u :: (lift p).vertices = u :: p.vertices` via
`congrArg (u :: ·) ih`.

Refactor port: structurally identical to the original
`Walk.vertices_liftFromHardIntervention` in the `namespace CDMG`
block above, modulo the cons-cell pattern shrinking from four args
(`vMid a h p`) to three (`vMid s p`) — see the design block on
`Walk.cons` in `Walks.lean`.  Used by the (⇐) direction's
clause~(a) / clause~(e) end-node-uniqueness bookkeeping when lifting
the minimum-length directed arms `q_v`, `q_w` back to `G`. -/
private lemma Walk.refactor_vertices_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.refactor_liftFromHardIntervention
        (hW := hW) p).vertices = p.vertices
  | _, _, .nil _ _ => rfl
  | u, _, .cons _ _ p =>
      congrArg (u :: ·)
        (Walk.refactor_vertices_liftFromHardIntervention p)

-- ## Proof-only helpers — Walk concatenation infrastructure (refactor twins)
--
-- Subtask 2 of the refactor port: the five private helpers below are
-- refactor twins of `Walk.comp`, `Walk.length_comp`,
-- `Walk.isDirectedWalk_comp`, `Walk.vertices_ne_nil`, and
-- `Walk.vertices_comp` (the original `namespace CDMG` block above).
-- The first three are verbatim copies of the already-solved twins in
-- `AcyclicIffTopologicalOrder.lean`'s REPLACEMENT block; the last two
-- (`vertices_ne_nil`, `vertices_comp`) are new to
-- this row and mirror the originals with the cons-cell pattern shrunk
-- from four args to three.
--
-- *Mathematical content unchanged (TL;DR).*  Concatenation does not
-- inspect the channel — it threads the typed `WalkStep`
-- through the recursion verbatim — so the structural recursion shape
-- of the original `Walk.comp` / `length_comp` / `vertices_comp` is
-- preserved.  Only `Walk.isDirectedWalk_comp` simplifies: the
-- original's `obtain ⟨_, _, hp_dir⟩` triple-conjunction is replaced
-- by a structural case-split on the typed step, with `.backwardE`
-- and `.bidir` closed by `hp.elim` since `IsDirectedWalk`
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
/-- Concatenate two `Walk`s `p : u → v` and `q : v → w` into
a walk `u → w`.  The `nil` case forwards `q` unchanged; the `cons`
case recurses on the tail and re-attaches the head step. -/
private def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w →
      Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v s p, q => .cons v s (p.comp q)

-- *Why this helper exists.*  Length arithmetic on the candidate
-- bifurcation walk and the truncated directed arms is the main
-- consumer of this lemma — `length_mkBifurcation` chains
-- this with `length_reverseDirected` to express the
-- candidate's length as `q_v.length + q_w.length`.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the walk spine plus `Nat` arithmetic — the typed
-- step never enters the case split.  Body is the original with
-- `length` / `comp` swapped for `length` / `comp`.
/-- The `length` of `p.comp q` is `p.length
+ q.length`. -/
private lemma Walk.length_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).length =
        p.length + q.length
  | _, _, _, .nil _ _, q => by
      simp [Walk.comp, Walk.length]
  | _, _, _, .cons _ _ p, q => by
      simp [Walk.comp, Walk.length,
            Walk.length_comp p q,
            Nat.add_comm, Nat.add_left_comm]

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
-- `IsDirectedWalk` is `False` definitionally — discharged
-- by structural impossibility, not by hand).
set_option linter.style.longLine false in
/-- Directedness is preserved under `comp`: concatenating
two directed walks produces a directed walk. -/
private lemma Walk.isDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsDirectedWalk → q.IsDirectedWalk →
        (p.comp q).IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ (.forwardE _) p, q, hp, hq =>
      Walk.isDirectedWalk_comp p q hp hq
  | _, _, _, .cons _ (.backwardE _) _, _, hp, _ => hp.elim
  | _, _, _, .cons _ (.bidir _) _, _, hp, _ => hp.elim

-- *Why this helper exists.*  `vertices_comp`'s `cons` case
-- needs `(u :: p.vertices).dropLast = u ::
-- p.vertices.dropLast`, which requires
-- `p.vertices ≠ []` to apply
-- `List.dropLast_cons_of_ne_nil`.  This lemma supplies the witness
-- structurally — every walk has at least its source vertex.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Both arms reduce by
-- `simp [vertices]` — the `nil` arm to `[v] ≠ []`, the
-- `cons` arm to `u :: rest ≠ []` — neither inspects the typed step.
/-- Auxiliary: every walk's `vertices` list is non-empty.
The `nil` walk gives `[v]`; every `cons` cell prepends a new head
vertex. -/
private lemma Walk.vertices_ne_nil {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ => by simp [Walk.vertices]

-- *Why this helper exists.*  The (⇐) direction's end-node /
-- interior-membership reasoning on `mkBifurcation`'s candidate walk
-- (predicates like `v ∉ p.vertices.tail` or `v ∈
-- p.vertices`) reduces to per-arm membership statements
-- via this equation.  Without it, vertex-list bookkeeping on the
-- concatenated walk would not factor through the constituent arms'
-- bookkeeping.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the walk spine plus `List` lemmas.  Body is the
-- original with `vertices` / `comp` / `vertices_ne_nil` swapped for
-- `vertices` / `comp` /
-- `vertices_ne_nil`, and the cons-cell pattern shrunk
-- from four args (`vMid a h p`) to three (`vMid s p`).
set_option linter.style.longLine false in
/-- `comp` interacts with `vertices` by dropping
the last vertex of the left arm and concatenating with the full
vertex list of the right arm.  The `nil` case closes by `rfl`
(`[v].dropLast = []` and `[] ++ _ = _` are both definitionally
true); the `cons` case applies the inductive hypothesis and uses
`List.dropLast_cons_of_ne_nil
(Walk.vertices_ne_nil p)` to unfold
`(u :: p.vertices).dropLast`. -/
private lemma Walk.vertices_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).vertices =
        p.vertices.dropLast ++ q.vertices
  | _, _, _, .nil _ _, _ => rfl
  | _, _, _, .cons _ _ p, q => by
      have hne : p.vertices ≠ [] :=
        Walk.vertices_ne_nil p
      simp [Walk.comp, Walk.vertices,
            Walk.vertices_comp p q,
            List.dropLast_cons_of_ne_nil hne]

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
-- *upgrade* a directed walk `p : Walk G u v` (in the
-- un-intervened CDMG) to a directed walk in
-- `G.hardInterventionOn W hW`, provided every non-source
-- vertex of `p` avoids `W`.  Consumed by the (⇐) direction's
-- candidate-bifurcation construction in
-- `bifurcationAlternative`.
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the same
-- lemmas as the originals; the refactor only swaps the upstream
-- `CDMG` / `Walk` / `WalkStep` shapes the helpers consume.  Two
-- structural simplifications fall out of the typed-step encoding:
--
-- * The cons-cell now takes three explicit args (`vMid`, `s`, `p'`)
--   rather than four (`vMid`, `a`, `h`, `p'`) — the `a : Node × Node`
--   is gone (endpoints live in the WalkStep's type indices).
-- * `IsDirectedWalk` returns `False` on `.backwardE` /
--   `.bidir` steps definitionally, so the original's
--   `obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` triple-conjunction is
--   replaced by a structural case-split on the typed WalkStep: the
--   `.forwardE` arm advances the recursion (and reads the underlying
--   `(u, vMid) ∈ G.E` witness directly from the constructor argument
--   `h_E`), while `.backwardE` and `.bidir` close by `hp_dir.elim`
--   (since `hp_dir : False` on those constructors).
-- * The `(u, vMid) ∈ (G.hardInterventionOn W hW).E` predicate
--   directly equals `(u, vMid) ∈ G.E ∧ (u, vMid).2 ∉ W` via
--   `Finset.mem_filter`, so `vMid ∉ W` reads off
--   `(Finset.mem_filter.mp h).2` without an intermediate
--   `rw [ha_eq]` step.

set_option linter.style.longLine false in
/-- Auxiliary: the source `u` of a walk `p : Walk G u v` is
the head of `p.vertices`, hence lies in `p.vertices`.
The `nil` case unfolds to `u ∈ [u]`; the `cons` case unfolds to
`u ∈ u :: rest`; both close by `simp [Walk.vertices]`.
Used by `refactor_liftTo_hardInterventionOn`'s `cons` recursion to
extract `vMid ∉ W` from the cons-walk's `vertices.tail`-
avoidance hypothesis (the cons-walk's `.vertices.tail`
definitionally equals `p'.vertices`, whose head is `vMid`).

Refactor port: structurally identical to the original
`Walk.head_mem_vertices`, modulo the cons-cell pattern shrinking from
four args (`vMid a h p`) to three (`vMid s p`) — see the design block
on `Walk.cons` in `Walks.lean`. -/
private lemma Walk.head_mem_vertices {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), u ∈ p.vertices
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ => by simp [Walk.vertices]

set_option linter.style.longLine false in
/-- Auxiliary: every walk's `vertices` list factors as
`source :: tail`.  The `nil` case: `[u].tail = []` and `u :: [] = [u]`,
so the equality is definitional.  The `cons` case:
`(u :: p'.vertices).tail = p'.vertices`, so
`u :: ((cons _ _ p').vertices.tail) = u :: p'.vertices
= (cons _ _ p').vertices`, again definitional.  Used by
`refactor_vertices_directed_avoid_of_hardInterventionOn`'s `cons`
case to split `x ∈ p'.vertices` into "x equals the source
vertex `vMid`" / "x lies in `p'.vertices.tail`" via
`List.mem_cons`.

Refactor port: structurally identical to the original
`Walk.vertices_eq_head_cons_tail`, modulo the cons-cell pattern
shrinking from four args to three. -/
private lemma Walk.vertices_eq_head_cons_tail {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.vertices = u :: p.vertices.tail
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ => rfl

-- *Why this helper exists.*  Subtask 3a: every vertex of a *directed*
-- walk in `G.hardInterventionOn W hW`, except the source,
-- avoids `W`.  The `.tail` carve-out is load-bearing: the source `u =
-- u_0` is unconstrained — it may or may not be in `W`.  Only the
-- heads of the edges (positions `1, 2, …, n` of `vertices`)
-- must avoid `W`, because `(u_i, u_{i+1}) ∈ E_{do(W)}` forces
-- `u_{i+1} ∉ W` via the `e.2 ∉ W` clause of `def_3_10` item iii's
-- `Finset.filter`.  Consumed by the (⇒) direction's avoidance check
-- when lifting the minimum-length directed arms back through the
-- intervention's filter.
--
-- *Typed-WalkStep shape: simplifies.*  The original obtains the
-- conjunction `⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` and reads `vMid ∉ W`
-- off `(Finset.mem_filter.mp ha_E).2` after `rw [ha_eq]` rewrites
-- `a` to `(u, vMid)`.  Under the typed `WalkStep`, only
-- `.forwardE h` survives `IsDirectedWalk`; the constructor
-- argument `h : (u, vMid) ∈ (G.hardInterventionOn W hW).E`
-- already filters on `e.2 ∉ W`, so `(Finset.mem_filter.mp h).2`
-- directly reads `vMid ∉ W` with no intermediate `rw [ha_eq]` step.
-- The other two constructors close by `hp_dir.elim` (the
-- `IsDirectedWalk` clauses for `.backwardE` and `.bidir`
-- reduce to `False` definitionally).
set_option linter.style.longLine false in
/-- **Subtask 3a:** every vertex of a *directed* walk in
`G.hardInterventionOn W hW`, except the source, avoids `W`.
Proof: induction on `p` with a structural case-split on the typed
WalkStep.  See the design block above for the simplification vs the
original. -/
private lemma Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk → ∀ x ∈ p.vertices.tail, x ∉ W
  | _, _, .nil _ _, _, _, hx => by simp [Walk.vertices] at hx
  | _, _, .cons vMid (.forwardE h) p', hp_dir, x, hx => by
      change x ∈ p'.vertices at hx
      have hvMid_notW : vMid ∉ W := (Finset.mem_filter.mp h).2
      rw [Walk.vertices_eq_head_cons_tail p'] at hx
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · exact hvMid_notW
      · exact Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
          p' hp_dir x hx_tail
  | _, _, .cons _ (.backwardE _) _, hp_dir, _, _ => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, hp_dir, _, _ => hp_dir.elim

-- *Why this helper exists.*  Subtask 3b: rebuild a directed walk
-- `p : Walk G u v` in the intervened CDMG
-- `G.hardInterventionOn W hW`, provided the source `u` is
-- itself a node of the intervention and every non-source vertex of
-- `p` avoids `W`.  Consumed by the (⇒) direction's final-arm
-- transport in `bifurcationAlternative`'s reverse direction.
--
-- *Typed-WalkStep shape: simplifies.*  The original built the
-- `WalkStep` witness via the disjunctive
-- `Or.inl ⟨hp_dir.1, Or.inl (Finset.mem_filter.mpr ⟨hp_dir.2.1, _⟩)⟩`
-- shape against the Prop-valued ordered-pair disjunction
-- `(a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∨ (a = (v, u) ∧ a ∈ G.E)`.
-- Under the typed `WalkStep`, the cons-cell carries
-- `s : WalkStep G u vMid` directly.  Only `.forwardE h_E`
-- with `h_E : (u, vMid) ∈ G.E` survives `IsDirectedWalk`
-- (the other two close by `hp_dir.elim`), and the intervened-edge
-- witness becomes `.forwardE (Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩)`
-- — a direct constructor call with no `Or.inl` / `rw [ha_eq]`
-- packaging.  Helper computations `hvMid_V`, `hvMid_inHard`,
-- `hp'_avoid` carry over verbatim modulo the rename
-- `hp_dir.2.1 ↦ h_E` (the typed constructor's argument).
set_option linter.style.longLine false in
/-- **Subtask 3b:** rebuild a directed walk `p : Walk G u v`
in the intervened CDMG `G.hardInterventionOn W hW`, provided
the source `u` is itself a node of the intervention and every
non-source vertex of `p` avoids `W`.

Cell-by-cell: each `cons` step's typed WalkStep is built from the
`.forwardE`-extracted edge witness `h_E : (u, vMid) ∈ G.E` (the only
constructor compatible with `IsDirectedWalk`) and the
head-of-tail-avoidance `vMid ∉ W` (extracted from `hp_avoid` via
`head_mem_vertices`).  These two facts package into
`Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩ : (u, vMid) ∈
(G.hardInterventionOn W hW).E`, which is the argument to
the `.forwardE` constructor of the new typed WalkStep. -/
private def Walk.refactor_liftTo_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk G u v),
      u ∈ G.hardInterventionOn W hW →
      p.IsDirectedWalk →
      (∀ x ∈ p.vertices.tail, x ∉ W) →
      Walk (G.hardInterventionOn W hW) u v
  | _, _, .nil v _, hu, _, _ => Walk.nil v hu
  | u, _, .cons vMid (.forwardE h_E) p', _, hp_dir, hp_avoid =>
      have hvMid_notW : vMid ∉ W :=
        hp_avoid vMid (Walk.head_mem_vertices p')
      have hvMid_V : vMid ∈ G.V := (G.hE_subset h_E).2
      have hvMid_inHard : vMid ∈ G.hardInterventionOn W hW := by
        change vMid ∈ (G.J ∪ W) ∪ (G.V \ W)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvMid_V, hvMid_notW⟩)
      have hStepFiltered : (u, vMid) ∈ (G.hardInterventionOn W hW).E :=
        Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩
      have hp'_avoid : ∀ x ∈ p'.vertices.tail, x ∉ W := fun y hy =>
        hp_avoid y (List.mem_of_mem_tail hy)
      Walk.cons vMid (.forwardE hStepFiltered)
        (Walk.refactor_liftTo_hardInterventionOn p'
          hvMid_inHard hp_dir hp'_avoid)
  | _, _, .cons _ (.backwardE _) _, _, hp_dir, _ => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, _, hp_dir, _ => hp_dir.elim

-- *Why this helper exists.*  Subtask 3c: the
-- `refactor_liftTo_hardInterventionOn` lift preserves
-- `IsDirectedWalk`.  Consumed by the (⇒) direction's
-- final-arm transport, paired with the lift itself.
--
-- *Typed-WalkStep shape: simplifies.*  The original discharged the
-- three-conjunct goal `⟨a = (u, vMid), a ∈ E_intervened,
-- (lift_tail).IsDirectedWalk⟩` via
-- `refine ⟨hp_dir.1, ?_, ?_⟩` + per-conjunct sub-proofs.  Under the
-- typed refactor, the new cons cell is
-- `.cons vMid (.forwardE hStepFiltered) (lift p')`, whose
-- `IsDirectedWalk` reduces definitionally to
-- `(lift p').IsDirectedWalk` — a single goal, discharged by
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
/-- **Subtask 3c:** the `refactor_liftTo_hardInterventionOn` lift
preserves `IsDirectedWalk`. -/
private lemma Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk G u v)
      (hu : u ∈ G.hardInterventionOn W hW)
      (hp_dir : p.IsDirectedWalk)
      (hp_avoid : ∀ x ∈ p.vertices.tail, x ∉ W),
      (Walk.refactor_liftTo_hardInterventionOn
        (hW := hW) p hu hp_dir hp_avoid).IsDirectedWalk
  | _, _, .nil _ _, _, _, _ => trivial
  | _, _, .cons vMid (.forwardE h_E) p', _, hp_dir, hp_avoid => by
      have hvMid_notW : vMid ∉ W :=
        hp_avoid vMid (Walk.head_mem_vertices p')
      have hvMid_V : vMid ∈ G.V := (G.hE_subset h_E).2
      have hvMid_inHard : vMid ∈ G.hardInterventionOn W hW := by
        change vMid ∈ (G.J ∪ W) ∪ (G.V \ W)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvMid_V, hvMid_notW⟩)
      have hp'_avoid : ∀ x ∈ p'.vertices.tail, x ∉ W := fun y hy =>
        hp_avoid y (List.mem_of_mem_tail hy)
      exact Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
        p' hvMid_inHard hp_dir hp'_avoid
  | _, _, .cons _ (.backwardE _) _, _, hp_dir, _ => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, _, hp_dir, _ => hp_dir.elim

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
-- `bifurcationAlternative`.
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the same
-- lemmas as the originals; the refactor swaps the upstream `CDMG` /
-- `Walk` / `WalkStep` shapes the helpers consume.  Three structural
-- simplifications fall out of the typed-step encoding:
--
-- * `WalkStep.source_mem` case-splits the typed
--   constructor `s : WalkStep G u v` into `.forwardE` /
--   `.backwardE` / `.bidir`.  The `.forwardE h_E` arm reads `u ∈ G.J ∪
--   G.V` off `(G.hE_subset h_E).1` directly (no `rw [ha_eq]`).  The
--   `.backwardE h_E` arm reads `u ∈ G.V` off `(G.hE_subset h_E).2` and
--   coerces via `Finset.mem_union_right`.  The `.bidir h_L` arm — with
--   `h_L : s(u, v) ∈ G.L` — invokes `G.hL_subset h_L (Sym2.mem_mk_left
--   u v) : u ∈ G.V` (the canonical Mathlib name for "the first slot of
--   `s(u, v)` is a member of `s(u, v)`"), then `Finset.mem_union_right`.
--   The `Sym2.Mem`-based shape of `CDMG.hL_subset`
--   (`∀ s ∈ L, ∀ v ∈ s, v ∈ V`) lines up with `Sym2.mem_mk_left u v`
--   one-step rather than the pre-refactor `(G.hL_subset ha_L).1` plus
--   `rw [ha_eq]` two-step.
--
-- * The cons-cell pattern shrinks from four args (`vMid a hStep p'`)
--   to three (`vMid s p'`) — the `a : Node × Node` is gone (endpoints
--   live in the typed WalkStep's type indices).  All five truncation
--   helpers consume `s` instead of `(a, hStep)`.
--
-- * `IsDirectedWalk` returns `False` on `.backwardE` /
--   `.bidir` steps definitionally, so the original's
--   `obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` triple-conjunction is
--   replaced in `refactor_isDirectedWalk_truncateAtFirst` by a
--   structural case-split on `s`: the `.forwardE` arm advances the
--   recursion (and the cons-cell's `IsDirectedWalk` reduces
--   definitionally to `p'.IsDirectedWalk`, supplying the
--   IH's hypothesis without an `obtain`), while `.backwardE` and
--   `.bidir` close by `hp_dir.elim`.

set_option linter.style.longLine false in
/-- Auxiliary: the source vertex of a `WalkStep` lies in `G`.
Used by `Walk.refactor_truncateAtFirst`'s `t = u` branch in
the `cons` arm to recover `u ∈ G` from `s : WalkStep G u
vMid` — the `cons`-pattern data does not carry `u ∈ G` directly (only
`Walk.nil` has that field).  The proof pattern-matches `s`
against its three constructors and reads off `u`'s membership from the
appropriate `G.hE_subset` / `G.hL_subset` projection.
* `.forwardE h_E`: `h_E : (u, vMid) ∈ G.E`, so `(G.hE_subset h_E).1 :
  u ∈ G.J ∪ G.V` lands in `u ∈ G` directly.
* `.backwardE h_E`: `h_E : (vMid, u) ∈ G.E`, so `(G.hE_subset h_E).2 :
  u ∈ G.V` lifts to `u ∈ G.J ∪ G.V` via `Finset.mem_union_right`.
* `.bidir h_L`: `h_L : s(u, vMid) ∈ G.L`; `G.hL_subset h_L : ∀ ⦃x⦄,
  x ∈ s(u, vMid) → x ∈ G.V`, applied to `Sym2.mem_mk_left u vMid : u ∈
  s(u, vMid)`, gives `u ∈ G.V`, then `Finset.mem_union_right`. -/
private lemma WalkStep.source_mem {G : CDMG Node}
    {u v : Node} (h : WalkStep G u v) : u ∈ G := by
  change u ∈ G.J ∪ G.V
  match h with
  | .forwardE h_E => exact (G.hE_subset h_E).1
  | .backwardE h_E => exact Finset.mem_union_right _ (G.hE_subset h_E).2
  | .bidir h_L =>
      exact Finset.mem_union_right _ (G.hL_subset h_L (Sym2.mem_mk_left u v))

set_option linter.style.longLine false in
/-- **Subtask 4a:** truncate `p : Walk G u v` at the *first*
occurrence of `t` in `p.vertices`, returning a `Σ' (v' :
Node), Walk G u v'` whose target `v'` equals `t` (the equality
is the content of `refactor_truncateAtFirst_target_eq` immediately
below).

* `nil` arm: `p.vertices = [v]`, so `h : t ∈ [v]` forces
  `t = v`; the truncation is the trivial walk `⟨v, .nil v hv⟩`.
* `cons` arm: `p = .cons vMid s p'`, `p.vertices = u ::
  p'.vertices`.  Case-split on `t = u`:
    * If `t = u`: the truncated walk is `⟨u, .nil u _⟩`; the needed
      `u ∈ G` is extracted from `s` via
      `WalkStep.source_mem`.
    * If `t ≠ u`: recurse on `p'` and re-prepend the head step with
      `Walk.cons`.

Refactor port: cons-cell pattern shrinks from four args to three
(`vMid s p'` not `vMid a hStep p'`); the WalkStep witness `s` threads
through the `cons` re-build directly instead of the pair
`(a, hStep)`. -/
private def Walk.refactor_truncateAtFirst {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node)
      (_h : t ∈ p.vertices),
      Σ' (v' : Node), Walk G u v'
  | _, _, .nil w hw, _, _ => ⟨w, .nil w hw⟩
  | u, _, .cons vMid s p', t, h =>
      if h_eq : t = u then
        ⟨u, .nil u (WalkStep.source_mem s)⟩
      else
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        let res := Walk.refactor_truncateAtFirst p' t h_in_p'
        ⟨res.1, .cons vMid s res.2⟩

set_option linter.style.longLine false in
/-- **Subtask 4b:** the truncated walk's target (`Σ'.fst`) equals `t`.
Consumers use this equality to convert the
`Walk G u (refactor_truncateAtFirst p t h).1` into a
`Walk G u t` (via `subst` on the fst-equality).  Proved by
structural recursion mirroring `refactor_truncateAtFirst`'s shape:
`nil` closes by `List.mem_singleton`; the `cons` case-splits on
`t = u` and recurses on `p'` in the `t ≠ u` branch.  Cons-cell
pattern shrinks from four args to three. -/
private lemma Walk.refactor_truncateAtFirst_target_eq {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node)
      (h : t ∈ p.vertices),
      (Walk.refactor_truncateAtFirst p t h).1 = t
  | _, _, .nil _ _, _, h => (List.mem_singleton.mp h).symm
  | u, _, .cons _ _ p', t, h => by
      simp only [Walk.refactor_truncateAtFirst]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        exact h_eq.symm
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        exact Walk.refactor_truncateAtFirst_target_eq p' t h_in_p'

set_option linter.style.longLine false in
/-- **Subtask 4c:** the truncated walk's length is bounded by the
original walk's length.  Both endpoints (`≤`) are attained: a `nil`
input gives a `nil` output of the same length 0; a `cons` input whose
truncation does not drop any cell yields equality.  The strict-
inequality version `refactor_length_truncateAtFirst_lt_of_mem_dropLast`
strengthens this under the `t ∈ p.vertices.dropLast`
hypothesis.  Mechanical refactor port: rename `length →
length`, `vertices → vertices`, `truncateAtFirst →
refactor_truncateAtFirst`; cons-cell pattern shrinks from four args to
three. -/
private lemma Walk.refactor_length_truncateAtFirst_le {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node)
      (h : t ∈ p.vertices),
      (Walk.refactor_truncateAtFirst p t h).2.length ≤ p.length
  | _, _, .nil _ _, _, _ => by
      simp only [Walk.refactor_truncateAtFirst,
                 Walk.length, le_refl]
  | u, _, .cons _ _ p', t, h => by
      simp only [Walk.refactor_truncateAtFirst,
                 Walk.length]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        simp [Walk.length]
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        have ih := Walk.refactor_length_truncateAtFirst_le p' t h_in_p'
        change (Walk.refactor_truncateAtFirst p' t h_in_p').2.length
            + 1 ≤ p'.length + 1
        omega

set_option linter.style.longLine false in
/-- **Subtask 4d:** the truncated walk inherits `IsDirectedWalk`
from the original walk.  The `nil` arm produces a `.nil` walk
(trivially directed).  The `cons` arm case-splits the typed WalkStep:
* `.forwardE h_E`: the `t = u` branch produces a `.nil` walk
  (trivially directed); the `t ≠ u` branch recurses on `p'`, whose
  `IsDirectedWalk` is `hp_dir` directly (the `.cons _
  (.forwardE _) p` clause of `IsDirectedWalk` reduces
  definitionally to `p.IsDirectedWalk`, so no `obtain` of the
  old triple-conjunction is needed).
* `.backwardE _` / `.bidir _`: close by `hp_dir.elim` since
  `IsDirectedWalk` returns `False` on these. -/
private lemma Walk.refactor_isDirectedWalk_truncateAtFirst
    {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node)
      (h : t ∈ p.vertices),
      p.IsDirectedWalk →
        (Walk.refactor_truncateAtFirst p t h).2.IsDirectedWalk
  | _, _, .nil _ _, _, _, _ => by
      simp only [Walk.refactor_truncateAtFirst]
      trivial
  | u, _, .cons _ (.forwardE _) p', t, h, hp_dir => by
      simp only [Walk.refactor_truncateAtFirst]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        trivial
      · rw [dif_neg h_eq]
        have h_in_p' : t ∈ p'.vertices := by
          have h' : t ∈ u :: p'.vertices := h
          rcases List.mem_cons.mp h' with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        exact Walk.refactor_isDirectedWalk_truncateAtFirst
          p' t h_in_p' hp_dir
  | _, _, .cons _ (.backwardE _) _, _, _, hp_dir => hp_dir.elim
  | _, _, .cons _ (.bidir _) _, _, _, hp_dir => hp_dir.elim

set_option linter.style.longLine false in
/-- Auxiliary: every `t ∈ p.vertices.dropLast` automatically
lies in the full `p.vertices`.  Direct application of
mathlib's `List.mem_of_mem_dropLast`.  Used by
`refactor_length_truncateAtFirst_lt_of_mem_dropLast` and
`exists_directed_walk_v_not_in_dropLast` to feed a `dropLast`
membership into `refactor_truncateAtFirst`'s `p.vertices`-
membership hypothesis.  Mechanical refactor port. -/
private lemma Walk.refactor_mem_vertices_of_mem_dropLast
    {G : CDMG Node} {u v : Node} {p : Walk G u v} {t : Node}
    (h : t ∈ p.vertices.dropLast) : t ∈ p.vertices :=
  List.mem_of_mem_dropLast h

set_option linter.style.longLine false in
/-- **Subtask 4e:** the load-bearing *strict* inequality.  When `t`
appears in `p.vertices.dropLast` (some non-terminal position
in the walk's vertex list), the truncation drops at least one `cons`
cell, so its length is strictly smaller than `p.length`.

The `nil` case is vacuous: `(.nil v _).vertices.dropLast =
[v].dropLast = []`.

The `cons` case unfolds `(u :: p'.vertices).dropLast =
u :: p'.vertices.dropLast` via `List.dropLast_cons_of_ne_nil`
(using `vertices_ne_nil` from subtask 2) and case-splits
`t ∈ u :: p'.vertices.dropLast`.  `t = u`: trivial walk of
length 0 < cons walk's length ≥ 1.  `t ∈
p'.vertices.dropLast`: recurse on `p'` via the inductive
hypothesis; `omega` closes the +1/+1 step.  Mechanical refactor port:
cons-cell pattern shrinks from four args to three; `vertices` /
`length` / `vertices_ne_nil` / `truncateAtFirst` all gain
`refactor_` prefix. -/
private lemma Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast
    {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (t : Node)
      (h_in_dropLast : t ∈ p.vertices.dropLast),
      (Walk.refactor_truncateAtFirst p t
          (Walk.refactor_mem_vertices_of_mem_dropLast
            h_in_dropLast)).2.length < p.length
  | _, _, .nil _ _, _, h => by
      simp [Walk.vertices] at h
  | u, _, .cons _ _ p', t, h_in_dropLast => by
      have hne : p'.vertices ≠ [] :=
        Walk.vertices_ne_nil p'
      change t ∈ (u :: p'.vertices).dropLast at h_in_dropLast
      rw [List.dropLast_cons_of_ne_nil hne] at h_in_dropLast
      simp only [Walk.refactor_truncateAtFirst,
                 Walk.length]
      by_cases h_eq : t = u
      · rw [dif_pos h_eq]
        simp [Walk.length]
      · rw [dif_neg h_eq]
        have h_in_p'_drop : t ∈ p'.vertices.dropLast := by
          rcases List.mem_cons.mp h_in_dropLast with rfl | h_in
          · exact absurd rfl h_eq
          · exact h_in
        have ih :=
          Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast
            p' t h_in_p'_drop
        change (Walk.refactor_truncateAtFirst p' t _).2.length
            + 1 < p'.length + 1
        omega

set_option linter.style.longLine false in
/-- **Subtask 4f:** the (⇐) direction's load-bearing existence lemma.
Given any ancestor `c ∈ G.Anc v` with `c ≠ v`, there exists a
*minimum-length* directed walk from `c` to `v` whose target `v` does
not appear in its `vertices.dropLast` (i.e. `v` occurs *only*
at the walk's final position).

Proof strategy: extract initial directed walk from `c ∈ G.Anc
v`; define `P n` as "exists directed `c → v` walk of length `n`";
witness non-emptiness of `{n | P n}` via `p₀`; let `n₀ := Nat.find` and
use `Nat.find_spec` to get a minimum-length walk `p_min`.  Contradict
`Nat.find_min` by truncating `p_min` at `v`'s first occurrence — the
truncated walk has strictly smaller length (via
`refactor_length_truncateAtFirst_lt_of_mem_dropLast`), targets `v`
(via `refactor_truncateAtFirst_target_eq`), and inherits directedness
(via `refactor_isDirectedWalk_truncateAtFirst`).

Mechanical refactor port: `Walk → Walk`, `IsDirectedWalk →
IsDirectedWalk`, `length → length`, `vertices →
vertices`, `Anc → Anc`, and all four truncation
helpers gain `refactor_` prefix.  The `Nat.find` / `Nat.find_spec` /
`Nat.find_min` machinery is structure-agnostic. -/
private lemma exists_directed_walk_v_not_in_dropLast
    {G : CDMG Node} {c v : Node}
    (hc_anc : c ∈ G.Anc v) (hcv : c ≠ v) :
    ∃ (p : Walk G c v), p.IsDirectedWalk
      ∧ v ∉ p.vertices.dropLast := by
  classical
  -- Step 1: extract initial walk from c ∈ Anc v.
  obtain ⟨_hc_in, p₀, hp₀_dir⟩ := hc_anc
  -- Step 2: predicate "exists directed c→v walk of length n", and witness.
  let P : ℕ → Prop :=
    fun n => ∃ (p : Walk G c v),
      p.IsDirectedWalk ∧ p.length = n
  have hP_nonempty : ∃ n, P n := ⟨p₀.length, p₀, hp₀_dir, rfl⟩
  -- Step 3: minimum length witness via Nat.find.
  obtain ⟨p_min, hp_min_dir, hp_min_len⟩ :
      P (Nat.find hP_nonempty) := Nat.find_spec hP_nonempty
  refine ⟨p_min, hp_min_dir, ?_⟩
  -- Step 4: contradiction with minimality.
  intro hv_drop
  have h_v_in : v ∈ p_min.vertices :=
    Walk.refactor_mem_vertices_of_mem_dropLast hv_drop
  obtain ⟨v', p_short, h_target, h_dir, h_lt⟩ :
      ∃ (v' : Node) (p_short : Walk G c v'),
        v' = v ∧ p_short.IsDirectedWalk
          ∧ p_short.length < p_min.length := by
    refine ⟨(Walk.refactor_truncateAtFirst p_min v h_v_in).1,
            (Walk.refactor_truncateAtFirst p_min v h_v_in).2,
            ?_, ?_, ?_⟩
    · exact Walk.refactor_truncateAtFirst_target_eq p_min v h_v_in
    · exact Walk.refactor_isDirectedWalk_truncateAtFirst
        p_min v h_v_in hp_min_dir
    · exact Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast
        p_min v hv_drop
  subst h_target
  have h_lt_n₀ : p_short.length < Nat.find hP_nonempty :=
    hp_min_len ▸ h_lt
  exact Nat.find_min hP_nonempty h_lt_n₀ ⟨p_short, h_dir, rfl⟩

-- ## Proof-only helpers — bifurcation walk construction (subtask 5, refactor twins)
--
-- Subtask 5 of the refactor port: assemble the candidate bifurcation
-- walk for the (⇐) direction.  Given two directed arms `q_v : c → v`
-- and `q_w : c → w`, `mkBifurcation` produces the walk
-- `(reverse q_v) ⌢ q_w : Walk G v w` whose middle vertex is
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
-- inductive `WalkStep`, the same proof term `h_E :
-- (c, vMid) ∈ G.E` carried by `.forwardE h_E` is *exactly* the
-- witness `.backwardE` expects for the reverse step, with no
-- repackaging.  See `reverseDirected` below for the
-- precise constructor swap.

-- *Why this helper exists.*  The (⇐) direction's candidate
-- bifurcation walk (subtask 5d's `mkBifurcation`) is built
-- by reversing the directed left arm `q_v : c → v` and concatenating
-- with the right arm `q_w : c → w`.  This primitive performs the
-- reversal.
--
-- *Typed-WalkStep shape: same `h_E`, different constructor wrap.*
-- The original step `.forwardE h_E : WalkStep G c vMid`
-- carries `h_E : (c, vMid) ∈ G.E`.  The reverse step
-- `WalkStep G vMid c` is constructed via `.backwardE h_E`:
-- the `.backwardE` constructor takes `h : (v, u) ∈ G.E`, which on
-- `(u, v) := (vMid, c)` reads `(c, vMid) ∈ G.E = h_E`.  So the same
-- proof term `h_E` lands in both constructors, distinguished only by
-- the constructor tag.  This is the central structural simplification
-- delivered by the typed-step encoding for this subtask (the OLD
-- propositional `WalkStep` had to re-package `h_E` through
-- `Or.inr ⟨_, _⟩`).
--
-- *Composition via the localised `comp`.*  The recursion
-- shape `reverse (cons s p) = reverse p ⌢ singleton (back s)`
-- threads through subtask 2's `comp` without introducing a
-- new global walk-reverse operator.  The two non-`.forwardE`
-- constructor branches close by `hqv_dir.elim` (since
-- `IsDirectedWalk` returns `False` on `.backwardE` /
-- `.bidir` definitionally — no `obtain` of an OLD-style triple
-- conjunction).
set_option linter.style.longLine false in
/-- **Subtask 5a:** reverse a directed walk
`qv : Walk G c v` into a walk `Walk G v c`.  Each
cell of the result uses the *backward* `WalkStep`
constructor `.backwardE`, re-using the same `h_E : (c, vMid) ∈ G.E`
witness extracted from the input's `.forwardE h_E` cell.

Structural recursion on `qv`:
* `nil` case: return the trivial walk `.nil w hw`.
* `cons _ (.forwardE h_E) qv'` case: recurse on `qv'` to get
  `qv'_rev : Walk G v vMid`; assemble the length-1
  backward-edge walk `Walk G vMid c` as
  `.cons c (.backwardE h_E) (.nil c _)` (with the nil's `c ∈ G`
  witness extracted from the original step via
  `WalkStep.source_mem`); compose via
  `comp`.
* `.backwardE _` / `.bidir _` cases: closed by `hqv_dir.elim`
  (`IsDirectedWalk` returns `False` definitionally). -/
private def Walk.reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v),
      qv.IsDirectedWalk → Walk G v c
  | _, _, .nil w hw, _ => .nil w hw
  | c, _, .cons _ (.forwardE h_E) qv', hqv_dir =>
      (Walk.reverseDirected qv' hqv_dir).comp
        (.cons c (.backwardE h_E)
          (.nil c (WalkStep.source_mem (.forwardE h_E))))
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim

-- *Why this helper exists.*  Length arithmetic on the candidate
-- bifurcation walk (subtask 5e's `length_mkBifurcation`)
-- chains this lemma with `length_comp` to express the
-- candidate's length as `q_v.length + q_w.length`.
--
-- *Typed-WalkStep shape: structure-agnostic body.*  Each cell of
-- the input produces one cell in the recursive reversal plus one
-- cell in the length-1 backward-edge walk, so the total length
-- comes out to `qv'.length + 1 = qv.length`.  The
-- `cons` branch is the OLD's body with `length` / `comp` / `IsDirectedWalk`
-- swapped for their `refactor_`-prefixed twins and the cons-cell
-- pattern shrunk from four args (`vMid a h p`) to three (`vMid s p`);
-- the `.backwardE` / `.bidir` cases close by `hqv_dir.elim`.
set_option linter.style.longLine false in
/-- **Subtask 5b:** `reverseDirected` preserves
`length`. -/
private lemma Walk.length_reverseDirected
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v)
      (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).length
        = qv.length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ (.forwardE _) qv', hqv_dir => by
      change ((Walk.reverseDirected qv' hqv_dir).comp _).length
            = qv'.length + 1
      rw [Walk.length_comp,
          Walk.length_reverseDirected qv' hqv_dir]
      rfl
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim

-- *Why this helper exists.*  Subtask 5f's
-- `vertices_mkBifurcation` factors the candidate
-- bifurcation walk's vertex list as
-- `q_v.vertices.reverse.dropLast ++ q_w.vertices`,
-- which in turn feeds the (⇐) direction's end-node / interior-
-- membership bookkeeping (clauses (a)/(c) of `def_3_4`).  This
-- intermediate result on the reverse alone is the key step.
--
-- *Typed-WalkStep shape: structure-agnostic body.*  The proof is the
-- OLD's body with `vertices` / `comp` / `vertices_eq_head_cons_tail`
-- swapped for their `refactor_`-prefixed twins and the cons-cell
-- pattern shrunk from four args to three; the `.backwardE` / `.bidir`
-- cases close by `hqv_dir.elim`.  The closing `simp` lemma set is
-- identical (`vertices`, `List.reverse_cons`) — the
-- `dropLast` of a reversed-cons list is handled by mathlib's
-- general-purpose simp lemmas.
set_option linter.style.longLine false in
/-- **Subtask 5c:** `reverseDirected` reverses the
`vertices` list. -/
private lemma Walk.vertices_reverseDirected
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v)
      (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).vertices
        = qv.vertices.reverse
  | _, _, .nil _ _, _ => rfl
  | c, _, .cons vMid (.forwardE _) qv', hqv_dir => by
      have ih := Walk.vertices_reverseDirected qv' hqv_dir
      have h_head : qv'.vertices = vMid :: qv'.vertices.tail :=
        Walk.vertices_eq_head_cons_tail qv'
      change ((Walk.reverseDirected qv' hqv_dir).comp _).vertices
            = (c :: qv'.vertices).reverse
      rw [Walk.vertices_comp, ih]
      conv_lhs => rw [h_head]
      conv_rhs => rw [h_head]
      simp [Walk.vertices, List.reverse_cons]
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim

-- *Why this helper exists.*  The constructor for the candidate
-- bifurcation walk consumed by the (⇐) direction of
-- `bifurcationAlternative`.  Built by reversing the left
-- arm `q_v` (subtask 5a) and concatenating with the right arm `q_w`
-- (subtask 2).
--
-- *`_hqv_pos` carried but unused at the definition level.*  Subtask
-- 6 needs `q_v.length ≥ 1` to realise the
-- `IsBifurcationDirectedHingeWithSplit` predicate on the
-- output (splitting at the hinge index `q_v.length - 1`,
-- which requires the index to be a valid `ℕ`).  Threading
-- `_hqv_pos` through the signature here keeps the downstream
-- subtask-6/8 API uniform — see the OLD's identical signature on
-- `Walk.mkBifurcation`.
--
-- *Typed-WalkStep shape: irrelevant here.*  This is a pure
-- concatenation of two walks; the typed step never enters.  Body is
-- one-for-one identical to the OLD modulo refactor-prefix renames.
set_option linter.style.longLine false in
/-- **Subtask 5d:** the bifurcation-walk constructor.  Given a
directed left arm `qv : Walk G c v` of length ≥ 1 and a
right arm `qw : Walk G c w`, assemble the candidate
bifurcation walk
`(reverseDirected qv hqv_dir).comp qw :
Walk G v w` whose middle vertex is `c`. -/
private def Walk.mkBifurcation {G : CDMG Node}
    {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (_hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    Walk G v w :=
  (Walk.reverseDirected qv hqv_dir).comp qw

-- *Why this helper exists.*  Length bookkeeping on the candidate
-- bifurcation walk feeds clause (e) of `def_3_4` item~vi
-- (`1 ≤ k ≤ n - 1`, where `n = qv.length + qw.length`
-- is the candidate's total length and `k = qv.length - 1` is
-- the hinge index).
--
-- *Typed-WalkStep shape: irrelevant here.*  Direct from
-- `length_comp` + `length_reverseDirected`.  Body
-- is one-for-one identical to the OLD modulo refactor-prefix
-- renames.
set_option linter.style.longLine false in
/-- **Subtask 5e:** the bifurcation walk's `length` is
`qv.length + qw.length`. -/
private lemma Walk.length_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).length
      = qv.length + qw.length := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).length
        = qv.length + qw.length
  rw [Walk.length_comp,
      Walk.length_reverseDirected qv hqv_dir]

-- *Why this helper exists.*  The vertex-list factorisation
-- `qv.vertices.reverse.dropLast ++ qw.vertices`
-- is the load-bearing splitting formula for the (⇐) direction's
-- clause~(a)/(c) end-node-uniqueness bookkeeping in Step 5 of the
-- TeX proof: the candidate bifurcation walk's vertex list factors
-- as *reverse of the left arm without its source* followed by
-- *full right arm*.  The end-node constraints `v ≠ w`,
-- `v ∉ p.vertices.tail`,
-- `w ∉ p.vertices.dropLast` then reduce to per-arm
-- vertex-membership statements via this equation.
--
-- *Typed-WalkStep shape: irrelevant here.*  Direct from
-- `vertices_comp` + `vertices_reverseDirected`.
-- Body is one-for-one identical to the OLD modulo refactor-prefix
-- renames.
set_option linter.style.longLine false in
/-- **Subtask 5f:** the bifurcation walk's `vertices` list
factors as `qv.vertices.reverse.dropLast ++
qw.vertices`. -/
private lemma Walk.vertices_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
      = qv.vertices.reverse.dropLast ++ qw.vertices := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).vertices
        = qv.vertices.reverse.dropLast ++ qw.vertices
  rw [Walk.vertices_comp,
      Walk.vertices_reverseDirected qv hqv_dir]

-- ## Proof-only helpers — `mkBifurcation` realises the directed-hinge predicate (subtask 6, refactor twins)
--
-- Subtask 6 of the refactor port: the four private helpers below are
-- refactor twins of `Walk.comp_assoc`,
-- `Walk.isBifurcationDirectedHinge_cons_backward_of_directed`,
-- `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux`, and
-- `Walk.isBifurcationDirectedHinge_mkBifurcation` (the `namespace
-- CDMG` ORIGINAL block above).  They connect subtask 5's
-- `mkBifurcation` constructor to the
-- `IsBifurcationDirectedHingeWithSplit` predicate (`Walks.lean`
-- REPLACEMENT block):  the (⇐) direction's Step 5 (TeX proof) needs
-- all five clauses (a)–(e) of `def_3_4` item~vi to hold on the
-- constructed walk at index `k = qv.length - 1`; the
-- directed-hinge predicate covers clauses (b), (c), (d) — chained
-- backward-`E` edges of the left arm followed by forward-`E` edges of
-- the right arm, with a directed hinge at the source vertex `c`.
--
-- The same three-step structure as the original carries over:
-- `comp_assoc` re-associates the composition produced by
-- `reverseDirected`'s `cons` case;
-- `isBifurcationDirectedHinge_cons_backward_of_directed`
-- (base case) handles a single backward edge followed by a non-trivial
-- directed walk; and
-- `isBifurcationDirectedHinge_comp_reverseDirected_aux`
-- (parametrised inductive step) shifts the predicate's index by
-- `qv.length` when prepending the backward-edge chain
-- `reverseDirected qv`.  The consumer-facing wrapper
-- `isBifurcationDirectedHinge_mkBifurcation` decomposes `qv`
-- once and feeds Helper 1 + Helper 2 to discharge the goal at index
-- `qv.length - 1`.
--
-- ## Design choices — subtask 6 refactor twins
--
-- *Signature change on Helper 1
--   (`isBifurcationDirectedHinge_cons_backward_of_directed`).*
--   The original took an ordered pair `a : Node × Node`, a
--   propositional `WalkStep` witness `h : G.WalkStep u a v`, and two
--   independent facts `ha_eq : a = (v, u)` and `ha_mem : a ∈ G.E` —
--   four arguments to encode "this single edge is a backward `E`-edge
--   from `u` to `v`".  Under the typed-step refactor, all four collapse
--   into a single `h_E : (v, u) ∈ G.E`: the typed constructor
--   `.backwardE h_E : WalkStep G u v` already pins both the
--   orientation (backward) and the channel (`E`) without a separate
--   `ha_eq` / `ha_mem` proof.  We accept the signature change rather
--   than threading a `(s : WalkStep G u v)` plus a
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
--   already unfolds (definitionally) to `qv'.IsDirectedWalk`,
--   and the `h_E : (c, vMid) ∈ G.E` data is available directly from
--   the constructor match.  So `backStep := .backwardE h_E` is the
--   one-step replacement of the original's `Or.inr ⟨…⟩`.  No data is
--   lost: `.backwardE h_E : WalkStep G vMid c` carries the
--   same membership witness as `Or.inr ⟨ha_eq, ha_E⟩` did in the
--   untyped form.
--
-- *Case-split on the typed step `s` instead of `Or.inr`.*  In
--   Helpers 2 and 3, where the original obtained
--   `hqv_dir.1 / hqv_dir.2.1 / hqv_dir.2.2` from the
--   `IsDirectedWalk`-as-triple unfolding, the refactor case-splits on
--   `s : WalkStep G c vMid` first: only `.forwardE h_E`
--   survives `IsDirectedWalk`'s `False`-returning branches
--   for `.backwardE _` / `.bidir _`.  The structural impossibility of
--   the latter two cases is discharged by `hqv_dir.elim`, matching the
--   pattern already used in `reverseDirected`,
--   `isDirectedWalk_comp`, etc.
--
-- *Re-using `comp_assoc` verbatim.*  The associativity
--   rewrite step `((reverseDirected qv').comp single-back-edge).comp
--   rest → (reverseDirected qv').comp (single-back-edge.comp rest)`
--   is structurally identical to the original — the typed-step
--   refactor does not touch `comp`'s recursion shape, so
--   `comp_assoc` plays the same role as the original
--   `comp_assoc` in Helpers 3 and 4.

-- *Why this helper exists.*  Helper 3
-- (`isBifurcationDirectedHinge_comp_reverseDirected_aux`)'s
-- inductive step re-associates `((reverseDirected qv').comp
-- single-back-edge).comp rest` into the form
-- `(reverseDirected qv').comp (single-back-edge.comp rest)`
-- that the IH matches.  Mathlib's walk concatenation does provide an
-- analogous `comp_assoc`, but our `comp` is a locally-`private`
-- re-declaration (subtask 2 above), so the associativity lemma is also
-- localised here.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the first walk's spine — the typed step never enters
-- the case split.  Body is the OLD's body with `comp` swapped for
-- `comp` and the cons-cell pattern shrunk from four args
-- (`vMid a h p`) to three (`vMid s p`).
/-- Auxiliary: `comp` is associative.  Verbatim structural
induction on the first argument: the `nil` case reduces by definition
(`nil.comp q = q`, so `(nil.comp q).comp r
= q.comp r = nil.comp (q.comp r)`), and the
`cons` case unfolds `comp` once on each side, exposing the IH
on the tail. -/
private lemma Walk.comp_assoc {G : CDMG Node} :
    ∀ {u₁ u₂ u₃ u₄ : Node} (p : Walk G u₁ u₂) (q : Walk G u₂ u₃)
      (r : Walk G u₃ u₄),
      (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ s p, q, r => by
      change Walk.cons _ s ((p.comp q).comp r)
            = Walk.cons _ s (p.comp (q.comp r))
      rw [Walk.comp_assoc p q r]

-- *Why this helper exists.*  The base case of Helper 3's induction:
-- a single backward `E`-edge `(v, u)` followed by a non-trivial
-- directed walk `p : Walk G v w` realises the directed-hinge
-- predicate at index 0.  Discharges the third clause of
-- `IsBifurcationDirectedHingeWithSplit`'s recursion
-- (`Walks.lean` REPLACEMENT:
-- `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.IsDirectedWalk`).
-- The `hp_nonempty` hypothesis is *load-bearing*: without it, the
-- predicate's second clause (`.cons _ (.backwardE _) (.nil _ _), 0 =>
-- False`) would fire instead.  Downstream this corresponds to the
-- `qw.length ≥ 1` constraint that the (⇐) direction obtains
-- from `c ≠ w`.
--
-- *Signature change: drop `(a, h, ha_eq, ha_mem)`, take `h_E` only.*
-- See the design block above for the full rationale.  The typed
-- constructor `.backwardE h_E : WalkStep G u v` carries
-- the channel and orientation that the OLD's four-argument tuple
-- `(a, h, ha_eq, ha_mem)` encoded.
--
-- *Proof: case-split `p`.*  Same shape as OLD.  `.nil _ _` branch
-- contradicts `hp_nonempty` (`(.nil _ _).length = 0`).
-- `.cons _ _ _` branch lands directly in the predicate's clause
-- `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.IsDirectedWalk`,
-- closed by `hp_dir`.  The OLD's `⟨ha_eq, ha_mem, hp_dir⟩` triple
-- collapses to a bare `hp_dir` because the channel and orientation
-- are already pinned by the typed `.backwardE` constructor.
set_option linter.style.longLine false in
/-- **Subtask 6a (base case):** a single backward `E`-edge from `u` to
`v` (witnessed by `h_E : (v, u) ∈ G.E`) followed by a non-trivial
directed walk `p : Walk G v w` realises the directed-hinge
predicate at index 0. -/
private lemma Walk.isBifurcationDirectedHinge_cons_backward_of_directed
    {G : CDMG Node} {u v w : Node}
    (h_E : (v, u) ∈ G.E)
    (p : Walk G v w) (hp_dir : p.IsDirectedWalk)
    (hp_nonempty : p.length ≥ 1) :
    Walk.IsBifurcationDirectedHingeWithSplit
      (Walk.cons v (.backwardE h_E) p) 0 := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_nonempty
  | cons _ _ _ => exact hp_dir

-- *Why this helper exists.*  The parametrised inductive step of
-- subtask 6: prepending the `reverseDirected qv` backward
-- chain (of length `qv.length`) in front of any walk `rest`
-- that already realises the directed-hinge predicate at index `k`
-- shifts the index by `qv.length`.  The parametrisation by
-- `rest` and `k` is what makes the structural induction on `qv` go
-- through: `reverseDirected`'s definition places the new edge
-- at the *rightmost* position of the recursion (via
-- `(reverseDirected qv').comp single-back-edge`), so
-- the IH on `qv'` must apply with an enriched
-- `rest' = .cons c (.backwardE h_E) rest` and shifted index
-- `k' = k + 1`.
--
-- *Typed-WalkStep shape: case-split `s` instead of `Or.inr`.*  In the
-- `cons` arm, where the OLD built `backStep` via
-- `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩`, the refactor case-splits the step
-- `s : WalkStep G c vMid` first: only `.forwardE h_E`
-- survives `IsDirectedWalk`, and `backStep := .backwardE h_E`
-- carries the same `(c, vMid) ∈ G.E` data.  The
-- `IsBifurcationDirectedHingeWithSplit (k+1)` witness on the
-- enriched `rest'` is then `hrest` directly — the predicate's
-- `.cons _ (.backwardE _) p, k + 1 => p.IsBifurcationDirectedHingeWithSplit k`
-- clause makes it a single proposition (in contrast to the OLD's
-- 3-tuple `⟨hqv_dir.1, hqv_dir.2.1, hrest⟩`).  The
-- `comp_assoc` rewrite + index arithmetic is otherwise
-- identical to OLD.
set_option linter.style.longLine false in
/-- **Subtask 6b (parametrised inductive step):** prepending the
`reverseDirected qv` backward-edge chain in front of any walk
`rest` that already realises the directed-hinge predicate at index `k`
shifts the index by `qv.length`. -/
private lemma Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
      {w : Node} (rest : Walk G c w) (k : ℕ)
      (_hrest : rest.IsBifurcationDirectedHingeWithSplit k),
      Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv hqv_dir).comp rest)
        (qv.length + k)
  | _, _, .nil w hw, _, _, rest, k, hrest => by
      simp only [Walk.reverseDirected, Walk.comp,
        Walk.length, Nat.zero_add]
      exact hrest
  | c, _, .cons vMid (.forwardE h_E) qv', hqv_dir, _, rest, k, hrest => by
      have h_cons : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c (.backwardE h_E) rest) (k + 1) := by
        simp only [Walk.IsBifurcationDirectedHingeWithSplit]
        exact hrest
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir (Walk.cons c (.backwardE h_E) rest) (k + 1) h_cons
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir).comp
            (Walk.cons c (.backwardE h_E)
              (Walk.nil c
                (WalkStep.source_mem (.forwardE h_E))))).comp rest)
        (qv'.length + 1 + k)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir).comp
          (Walk.cons c (.backwardE h_E) rest))
        (qv'.length + 1 + k)
      have hidx : qv'.length + 1 + k = qv'.length + (k + 1) := by omega
      rw [hidx]
      exact ih
  | _, _, .cons _ (.backwardE _) _, hqv_dir, _, _, _, _ => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir, _, _, _, _ => hqv_dir.elim

-- *Why this helper exists.*  The consumer-facing wrapper of subtask 6:
-- the `mkBifurcation`-shaped output of subtask 5 realises the
-- directed-hinge predicate at the intended split index
-- `qv.length - 1`.  Combines the base case (Helper 1) with
-- the inductive auxiliary (Helper 2) by decomposing `qv` once and
-- applying the auxiliary to its tail `qv'`.
--
-- *Typed-WalkStep shape: `cases qv` + case-split `s`.*  The OLD's
-- `match qv, hqv_dir, hqv_pos with | .nil ... | .cons vMid a hStep qv'`
-- becomes `cases qv` with `.nil` contradicting `hqv_pos` and `.cons
-- vMid s qv'` requiring a further case-split on `s : WalkStep
-- G c vMid`.  Only `.forwardE h_E` survives `IsDirectedWalk`;
-- the `.backwardE _` / `.bidir _` cases close by `hqv_dir.elim`.
-- `backStep := .backwardE h_E` is built directly from the surviving
-- `h_E` (see design block above).  Helper 1's call site uses the new
-- single-argument signature
-- `isBifurcationDirectedHinge_cons_backward_of_directed h_E qw hqw_dir hqw_pos`
-- (no `ha_eq` / `ha_mem` triples).  Index arithmetic via `omega`
-- unchanged.
set_option linter.style.longLine false in
/-- **Subtask 6c (consumer-facing wrapper):** the
`mkBifurcation`-shaped output of subtask 5 realises the
directed-hinge predicate at the intended split index
`qv.length - 1`. -/
private lemma Walk.isBifurcationDirectedHinge_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_dir : qw.IsDirectedWalk)
    (hqw_pos : qw.length ≥ 1) :
    Walk.IsBifurcationDirectedHingeWithSplit
      (Walk.mkBifurcation qv hqv_dir hqv_pos qw)
      (qv.length - 1) := by
  change Walk.IsBifurcationDirectedHingeWithSplit
    ((Walk.reverseDirected qv hqv_dir).comp qw)
    (qv.length - 1)
  cases qv with
  | nil _ _ => simp [Walk.length] at hqv_pos
  | cons vMid s qv' =>
      match s, hqv_dir with
      | .forwardE h_E, hqv_dir =>
          have h_base : Walk.IsBifurcationDirectedHingeWithSplit
              (Walk.cons c (.backwardE h_E) qw) 0 :=
            Walk.isBifurcationDirectedHinge_cons_backward_of_directed
              h_E qw hqw_dir hqw_pos
          have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
            qv' hqv_dir (Walk.cons c (.backwardE h_E) qw) 0 h_base
          change Walk.IsBifurcationDirectedHingeWithSplit
            (((Walk.reverseDirected qv' hqv_dir).comp
                (Walk.cons c (.backwardE h_E)
                  (Walk.nil c
                    (WalkStep.source_mem (.forwardE h_E))))).comp qw)
            (qv'.length + 1 - 1)
          rw [Walk.comp_assoc]
          change Walk.IsBifurcationDirectedHingeWithSplit
            ((Walk.reverseDirected qv' hqv_dir).comp
              (Walk.cons c (.backwardE h_E) qw))
            (qv'.length + 1 - 1)
          have hidx : qv'.length + 1 - 1 = qv'.length + 0 := by omega
          rw [hidx]
          exact ih

-- *Why this helper exists.*  Subtask 7 of `claim_3_5`: the largest
-- single helper in the file, and the converse of subtask 6's
-- `isBifurcationDirectedHinge_mkBifurcation`.  Given a
-- bifurcation walk `p : Walk G v w` together with a
-- directed-hinge witness
-- `p.IsBifurcationDirectedHingeWithSplit i`, decompose `p`
-- into its source vertex `c := p.vertices[i+1]`, a directed
-- left arm `L : Walk G c v` of length `≥ 1`, and a directed
-- right arm `R : Walk G c w` of length `≥ 1`, with two
-- vertex-containment witnesses pinning every vertex of `L` into
-- `p.vertices.dropLast` and every vertex of `R` into
-- `p.vertices.tail`.  The (⇒) direction of the main theorem
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
-- `IsBifurcationDirectedHingeWithSplit` defines its content
-- per *step constructor* (`.forwardE` / `.backwardE` / `.bidir`),
-- so the proposition doesn't reduce until the outer step is
-- concrete.  The skeleton therefore inverts: `cases s` first (the
-- typed `WalkStep`), then in the `.backwardE h_E` arm
-- `cases p'`.  The `.forwardE _` and `.bidir _` arms close by
-- `h_hinge.elim` because their predicate clauses return `False` — at
-- index `0` we additionally `cases p'` to force the inner pattern
-- match to fire (both `(.nil _ _)` and `(.cons _ _ _)` produce
-- `False`, so `cases p' <;> exact h_hinge.elim`); at index `k + 1`
-- the single clauses `.cons _ (.forwardE _) _, _ + 1 => False` and
-- `.cons _ (.bidir _) _, _ + 1 => False` fire regardless of `p'`.
--
-- *Forward step constructor reuse: `forwardStep := .forwardE h_E`.*
-- The left arm `L : Walk G vMid u` traverses `vMid → u` via
-- a single forward edge.  The outer cons step `s = .backwardE h_E :
-- WalkStep G u vMid` already carries
-- `h_E : (vMid, u) ∈ G.E` — exactly the witness that `.forwardE`
-- expects on a step `vMid → u`.  Same proof term, opposite-direction
-- constructor; the endpoint-index flip is by intent — the typed
-- `WalkStep` makes the channel/orientation swap structural rather
-- than tucked behind a `Or.inl ⟨..., Or.inl ...⟩` redirection (the
-- OLD's encoding).  `L.IsDirectedWalk` for
-- `cons u (.forwardE h_E) (nil u _)` then reduces via the predicate
-- to `(nil u _).IsDirectedWalk = True`, closed by
-- `trivial`.
--
-- *Predicate clause data collapses to a single proposition.*  The
-- OLD's `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := h_hinge` triple is
-- replaced by a bare rename: after `cases s | backwardE h_E` and
-- the relevant `cases p'`, the predicate clauses
-- `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 =>
--    p.IsDirectedWalk` (zero case) and
-- `.cons _ (.backwardE _) p, k + 1 =>
--    p.IsBifurcationDirectedHingeWithSplit k`
-- (succ case) return single propositions directly, with no
-- conjunctive structure to deconstruct.  Vertex-list bookkeeping
-- (`List.dropLast_cons_of_ne_nil`, `simpa`, `change`-rewrites)
-- ports mechanically with `vertices → vertices`,
-- `vertices_ne_nil → vertices_ne_nil`,
-- `vertices_comp → vertices_comp`, etc.
set_option linter.style.longLine false in
/-- **Subtask 7 of `claim_3_5` (the arm extractor — refactor twin):**
given a bifurcation walk `p : Walk G v w` together with a
directed-hinge witness `p.IsBifurcationDirectedHingeWithSplit i`,
extract the source vertex `c = p.vertices[i + 1]`, a directed
left arm `L : Walk G c v` of length `≥ 1` whose vertices lie
in `p.vertices.dropLast`, and a directed right arm
`R : Walk G c w` of length `≥ 1` whose vertices lie in
`p.vertices.tail`.

Proof: outer `induction p generalizing i`.  In the `cons` case,
case-split `s` first (the typed `WalkStep` constructor),
then inside `.backwardE h_E` case-split `p'`. -/
private lemma Walk.refactor_exists_arms_of_bifurcation_directed_hinge
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
                  --     p.IsDirectedWalk
                  -- so h_hinge : (cons vMid' s' p'').IsDirectedWalk.
                  have hu_in_G : u ∈ G :=
                    WalkStep.source_mem (.backwardE h_E)
                  let forwardStep : WalkStep G vMid u := .forwardE h_E
                  refine ⟨vMid,
                          Walk.cons u forwardStep (Walk.nil u hu_in_G),
                          Walk.cons vMid' s' p'',
                          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- L.IsDirectedWalk reduces to
                    -- (nil u _).IsDirectedWalk = True.
                    trivial
                  · -- R.IsDirectedWalk
                    exact h_hinge
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
                    have hp'_ne :
                        (Walk.cons vMid' s' p'').vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    have hp''_ne : p''.vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases hxv with rfl | rfl
                    · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                    · exact List.mem_cons_self
                  · -- ∀ x ∈ R.vertices, x ∈ p.vertices.tail
                    intro x hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
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
                  -- p'.IsBifurcationDirectedHingeWithSplit k.
                  -- With p' = nil, the .nil clause returns False.
                  exact h_hinge.elim
              | cons vMid' s' p'' =>
                  -- Predicate's recursion clause:
                  --   .cons _ (.backwardE _) p, k + 1 =>
                  --     p.IsBifurcationDirectedHingeWithSplit k
                  -- so h_hinge : (cons vMid' s' p'').IsBifurcationDirectedHingeWithSplit k.
                  -- Apply IH to p' and k.
                  obtain ⟨c, L', R, hL'_dir, hR_dir, _hL'_pos, hR_pos, h_idx_p',
                          hL'_sub, hR_sub⟩ :=
                    ih k h_hinge
                  -- Build L_new : Walk G c u by composing L' with a
                  -- single forward edge from vMid to u.
                  have hu_in_G : u ∈ G :=
                    WalkStep.source_mem (.backwardE h_E)
                  let forwardStep : WalkStep G vMid u := .forwardE h_E
                  let single : Walk G vMid u :=
                    Walk.cons u forwardStep (Walk.nil u hu_in_G)
                  have hsingle_dir : single.IsDirectedWalk := trivial
                  refine ⟨c, L'.comp single, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- (L'.comp single).IsDirectedWalk
                    exact Walk.isDirectedWalk_comp L' single
                      hL'_dir hsingle_dir
                  · -- R.IsDirectedWalk
                    exact hR_dir
                  · -- (L'.comp single).length ≥ 1
                    rw [Walk.length_comp]
                    change L'.length + 1 ≥ 1
                    exact Nat.succ_le_succ (Nat.zero_le _)
                  · -- R.length ≥ 1
                    exact hR_pos
                  · -- p.vertices[(k+1) + 1]? = some c
                    -- p.vertices = u :: p'.vertices.
                    change (u :: (Walk.cons vMid' s' p'').vertices)[k + 1 + 1]? = some c
                    simpa using h_idx_p'
                  · -- ∀ x ∈ (L'.comp single).vertices,
                    --   x ∈ p.vertices.dropLast
                    intro x hx
                    -- (L'.comp single).vertices
                    --   = L'.vertices.dropLast ++ single.vertices
                    --   = L'.vertices.dropLast ++ [vMid, u].
                    have hL_new_vs : (L'.comp single).vertices
                        = L'.vertices.dropLast ++ [vMid, u] := by
                      rw [Walk.vertices_comp]
                      rfl
                    rw [hL_new_vs] at hx
                    -- p.vertices.dropLast
                    --   = u :: vMid :: p''.vertices.dropLast.
                    have hp'_ne :
                        (Walk.cons vMid' s' p'').vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    have hp''_ne : p''.vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases List.mem_append.mp hx with hL'drop | h_in_tail
                    · -- x ∈ L'.vertices.dropLast: lift to
                      -- x ∈ L'.vertices via mem_of_mem_dropLast,
                      -- then to x ∈ p'.vertices.dropLast via hL'_sub.
                      have hx_L'_vertices : x ∈ L'.vertices :=
                        List.mem_of_mem_dropLast hL'drop
                      have hx_p'_drop :
                          x ∈ (Walk.cons vMid' s' p'').vertices.dropLast :=
                        hL'_sub x hx_L'_vertices
                      have hx_in : x ∈ (vMid :: p''.vertices).dropLast := by
                        have h_eq :
                            (Walk.cons vMid' s' p'').vertices.dropLast
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
                    have hx_p'_tail :
                        x ∈ (Walk.cons vMid' s' p'').vertices.tail :=
                      hR_sub x hx
                    have hx_p' :
                        x ∈ (Walk.cons vMid' s' p'').vertices :=
                      List.mem_of_mem_tail hx_p'_tail
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    exact hx_p'

-- ## Refactor-port design block — `bifurcationAlternative` (subtask 8 of `claim_3_5`)
--
-- *Mathematical content unchanged.*  This is the main theorem
-- twin for `claim_3_5` in the `cdmg_typed_edges` refactor.  Both
-- directions of the proof are mechanical ports of the ORIGINAL
-- `bifurcationAlternative` body above: every helper call is
-- swapped for its `refactor_`-prefixed twin (built in subtasks
-- 1–7 of the workspace plan), the cons-cell pattern shrinks from
-- four args (`vMid a h p`) to three (`vMid s p`), and `cases h`
-- on the OLD propositional `WalkStep` becomes a structural
-- `cases s` on the typed `WalkStep`.  The underlying
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
-- `WalkStep.source_mem`, which case-splits the
-- typed `.bidir` constructor in subtask 4's
-- `refactor_truncateAtFirst`).
--
-- *Direct call-site swap.*  Every ORIGINAL helper used by the
-- theorem body has been ported above as a `refactor_`-prefixed
-- twin in this `namespace CDMG` block:
-- `Walk.refactor_exists_arms_of_bifurcation_directed_hinge`
-- (subtask 7, the arm extractor); `head_mem_vertices`,
-- `vertices_eq_head_cons_tail`,
-- `refactor_liftTo_hardInterventionOn`,
-- `refactor_isDirectedWalk_liftTo_hardInterventionOn`,
-- `refactor_vertices_directed_avoid_of_hardInterventionOn`
-- (subtask 3); `exists_directed_walk_v_not_in_dropLast`
-- (subtask 4); `refactor_liftFromHardIntervention`,
-- `refactor_isDirectedWalk_liftFromHardIntervention`,
-- `refactor_vertices_liftFromHardIntervention`,
-- `refactor_length_liftFromHardIntervention` (subtask 1);
-- `mkBifurcation`, `vertices_mkBifurcation`,
-- `vertices_ne_nil` (subtask 5);
-- `isBifurcationDirectedHinge_mkBifurcation`
-- (subtask 6).  The proof body just swaps each call site to its
-- refactor twin.

-- ref: claim_3_5
-- For any CDMG `G : CDMG Node` and any three (not
-- necessarily distinct) nodes `v, w, c ∈ G` (i.e. `v, w, c ∈ G.J
-- ∪ G.V`), the following are equivalent:
--
-- (a) *Existence of a bifurcation between `v` and `w` with source
--     `c`.*  There exists a walk `p : Walk G v w` such
--     that `p.IsBifurcationSource c` (in the sense of
--     `def_3_4`'s trailing `IsBifurcationSource`
--     predicate).  This single existential packages both the LN's
--     "`p` is a bifurcation between `v` and `w`" (clauses (a)–(e)
--     of `def_3_4` item~vi, including the `v ≠ w` first-half of
--     clause (a) and the end-node-uniqueness clause), and the
--     LN's "the bifurcation has source `c`" (the closing
--     paragraph of `def_3_4` item~vi).  Under the `def_3_4`
--     encoding's chapter-init addition
--     `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
--     `IsBifurcationSource p c` automatically commits to
--     the interior-source convention `1 ≤ k ≤ n - 1`
--     (`0 ≤ i ≤ n - 2` in the Lean encoding), so `c ≠ v` and
--     `c ≠ w` are consequences of (a), not extra hypotheses.
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
-/
set_option linter.style.longLine false in
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
  -- `def_3_2`; the RHS's `Anc` conjunct independently
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
      Walk.refactor_exists_arms_of_bifurcation_directed_hinge p i h_hinge
    -- Identify `c' = c` using the source-index identification.  We
    -- keep both names alive (rather than `subst`-ing) so the
    -- theorem's universally-quantified `c` stays visible to the
    -- final `refine`'s LN-faithful conjuncts.
    have hc'_eq_c : c' = c := by
      rw [hc_idx] at h_src
      exact Option.some.inj h_src
    -- `c'` lies in `p.vertices.dropLast` (head of `L`'s
    -- vertices, all of which are in `p.vertices.dropLast`
    -- by `hL_sub`), and in `p.vertices.tail` (head of
    -- `R`'s vertices, all in `p.vertices.tail` by
    -- `hR_sub`).
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
    -- `c ∈ G_{do(w)}`: from `c ∈ G` (which is `c ∈ G.J ∪ G.V`)
    -- plus `c ≠ w`, we conclude `c ∈ (G.J ∪ {w}) ∪ (G.V \ {w})`.
    have hc_in_Gdow :
        c ∈ G.hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw) := by
      change c ∈ (G.J ∪ {w}) ∪ (G.V \ {w})
      rcases Finset.mem_union.mp hc with hJ | hV
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        rw [Finset.mem_singleton]
        exact hc_ne_w
    have hc_in_Gdov :
        c ∈ G.hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv) := by
      change c ∈ (G.J ∪ {v}) ∪ (G.V \ {v})
      rcases Finset.mem_union.mp hc with hJ | hV
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        rw [Finset.mem_singleton]
        exact hc_ne_v
    -- Transfer `c ∈ G_{do(w)}` to `c' ∈ G_{do(w)}` (and similarly
    -- for `c' ∈ G_{do(v)}`) so the lift consumer accepts
    -- `L : Walk G c' v` / `R : Walk G c' w`
    -- directly.
    have hc'_in_Gdow :
        c' ∈ G.hardInterventionOn {w}
          (Finset.singleton_subset_iff.mpr hw) := hc'_eq_c ▸ hc_in_Gdow
    have hc'_in_Gdov :
        c' ∈ G.hardInterventionOn {v}
          (Finset.singleton_subset_iff.mpr hv) := hc'_eq_c ▸ hc_in_Gdov
    -- Avoidance hypotheses for the lift: every tail-vertex of the
    -- left arm avoids `{w}`, and every tail-vertex of the right
    -- arm avoids `{v}`.  Both follow from `hL_sub` / `hR_sub` plus
    -- the end-node uniqueness clauses.
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
              Walk.refactor_liftTo_hardInterventionOn L hc'_in_Gdow hL_dir hL_avoid_w,
              Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
                L hc'_in_Gdow hL_dir hL_avoid_w⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hc_ne_v
    · -- `c ∈ Anc^{G_{do(v)}}(w) \ {w}`.
      refine ⟨hc'_eq_c ▸ ⟨hc'_in_Gdov,
              Walk.refactor_liftTo_hardInterventionOn R hc'_in_Gdov hR_dir hR_avoid_v,
              Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn
                R hc'_in_Gdov hR_dir hR_avoid_v⟩, ?_⟩
      rw [Set.mem_singleton_iff]
      exact hc_ne_w
  · -- (⇐) direction: extract minimum-length directed walks in
    -- each intervened CDMG (subtask 4), lift them back to `G`
    -- (subtask 1), assemble the bifurcation walk (subtask 5), and
    -- verify `IsBifurcationSource` (subtask 6 plus
    -- vertex bookkeeping).
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
    -- Inline structural-walk-length identity:
    -- `q.vertices.length = q.length + 1` (used
    -- downstream to derive `q.vertices.tail ≠ []` from
    -- `q.length ≥ 1`).  Refactor port: `cons _ _ _ q' ih`
    -- becomes `cons _ _ q' ih` (3-arg).
    have hvert_len_succ :
        ∀ {G' : CDMG Node} {u₁ u₂ : Node}
          (q : Walk G' u₁ u₂),
          q.vertices.length = q.length + 1 := by
      intro G' u₁ u₂ q
      induction q with
      | nil _ _ => rfl
      | cons _ _ q' ih =>
        change q'.vertices.length + 1 = q'.length + 1 + 1
        omega
    -- The two source walks have length `≥ 1`: a length-`0` walk
    -- would be `Walk.nil`, forcing `c = v` (resp. `c = w`)
    -- and contradicting `hc_ne_v` (resp. `hc_ne_w`).  Refactor
    -- port: `cons _ _ _ _` becomes `cons _ _ _` (3-arg).
    have hq_v_Gdow_pos : q_v_Gdow.length ≥ 1 := by
      cases q_v_Gdow with
      | nil _ _ => exact (hc_ne_v rfl).elim
      | cons _ _ _ =>
        change _ + 1 ≥ 1
        exact Nat.succ_le_succ (Nat.zero_le _)
    have hq_w_Gdov_pos : q_w_Gdov.length ≥ 1 := by
      cases q_w_Gdov with
      | nil _ _ => exact (hc_ne_w rfl).elim
      | cons _ _ _ =>
        change _ + 1 ≥ 1
        exact Nat.succ_le_succ (Nat.zero_le _)
    -- Tail-vertices of `q_v_Gdow` / `q_w_Gdov` avoid `{w}` / `{v}`
    -- by the head-of-edge argument of `def_3_10` item iii
    -- (subtask 3a).
    have hq_v_Gdow_avoid :
        ∀ x ∈ q_v_Gdow.vertices.tail, x ∉ ({w} : Finset Node) :=
      Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
        q_v_Gdow hq_v_Gdow_dir
    have hq_w_Gdov_avoid :
        ∀ x ∈ q_w_Gdov.vertices.tail, x ∉ ({v} : Finset Node) :=
      Walk.refactor_vertices_directed_avoid_of_hardInterventionOn
        q_w_Gdov hq_w_Gdov_dir
    -- Abbreviations for the lifted walks in `G`.
    set qv := Walk.refactor_liftFromHardIntervention q_v_Gdow with hqv_def
    set qw := Walk.refactor_liftFromHardIntervention q_w_Gdov with hqw_def
    have hqv_dir : qv.IsDirectedWalk :=
      Walk.refactor_isDirectedWalk_liftFromHardIntervention
        q_v_Gdow hq_v_Gdow_dir
    have hqw_dir : qw.IsDirectedWalk :=
      Walk.refactor_isDirectedWalk_liftFromHardIntervention
        q_w_Gdov hq_w_Gdov_dir
    have hqv_verts : qv.vertices = q_v_Gdow.vertices :=
      Walk.refactor_vertices_liftFromHardIntervention q_v_Gdow
    have hqw_verts : qw.vertices = q_w_Gdov.vertices :=
      Walk.refactor_vertices_liftFromHardIntervention q_w_Gdov
    have hqv_len : qv.length = q_v_Gdow.length :=
      Walk.refactor_length_liftFromHardIntervention q_v_Gdow
    have hqw_len : qw.length = q_w_Gdov.length :=
      Walk.refactor_length_liftFromHardIntervention q_w_Gdov
    have hqv_pos : qv.length ≥ 1 := by rw [hqv_len]; exact hq_v_Gdow_pos
    have hqw_pos : qw.length ≥ 1 := by rw [hqw_len]; exact hq_w_Gdov_pos
    have hqv_head : qv.vertices = c :: qv.vertices.tail :=
      Walk.vertices_eq_head_cons_tail qv
    have hqw_head : qw.vertices = c :: qw.vertices.tail :=
      Walk.vertices_eq_head_cons_tail qw
    have hqv_vs_len : qv.vertices.length = qv.length + 1 :=
      hvert_len_succ qv
    have hqw_vs_len : qw.vertices.length = qw.length + 1 :=
      hvert_len_succ qw
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
    -- Tail-vertex avoidance, transferred from the intervened to
    -- lifted form.
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
    -- Cross-arm non-memberships: `v ∉ qw.vertices` and
    -- `w ∉ qv.vertices`.
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
    --   p.vertices = qv.vertices.reverse.dropLast
    --                          ++ qw.vertices
    --                       = qv.vertices.tail.reverse
    --                          ++ qw.vertices.
    have hp_verts :
        (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
          = qv.vertices.tail.reverse ++ qw.vertices := by
      rw [Walk.vertices_mkBifurcation qv hqv_dir hqv_pos qw]
      conv_lhs => rw [hqv_head, List.reverse_cons, List.dropLast_concat]
    -- Index arithmetic: `qv.length - 1 + 1 = qv.length`
    -- and `qv.vertices.tail.reverse.length = qv.length`.
    have hidx_succ : qv.length - 1 + 1 = qv.length := by omega
    have hqv_tail_rev_len :
        qv.vertices.tail.reverse.length = qv.length := by
      rw [List.length_reverse]
      have hlen : qv.vertices.tail.length + 1
          = qv.vertices.length := by
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
      · rw [List.tail_reverse, List.mem_reverse] at hv_left
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
      · rw [List.mem_reverse] at hw_left
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
