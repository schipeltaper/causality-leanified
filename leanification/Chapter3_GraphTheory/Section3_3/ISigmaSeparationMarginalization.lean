import Chapter3_GraphTheory.Section3_3.ISigmaSeparation
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.MargPreservesAncestors
import Chapter3_GraphTheory.Section3_2.MarginalizationsCommute
import Chapter3_GraphTheory.Section3_3.LabelRoman
import Chapter3_GraphTheory.Section3_3.SigmaOpenPathsWalks

namespace Causality

/-!
# `iσ`-separation is stable under marginalization (`claim_3_25`)

This file formalises `claim_3_25`
(`\label{lem:stability_separation_marginalization}`), the lemma of
Section 3.3 of the lecture notes asserting that the
`iσ`-separation predicate of `def_3_18` is invariant under the
marginalization operator of `def_3_14`, provided the marginalized
set `D` is disjoint from the three argument sets `A, B, C`.

> Let `G = (J, V, E, L)` be a CDMG, `A, B, C ⊆ J ∪ V` and `D ⊆ V`
> subsets such that `D ∩ (A ∪ B ∪ C) = ∅`.  Then
> `A ⊥^iσ_G B | C  ⟺  A ⊥^iσ_{G^{∖D}} B | C`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/`
`claim_3_25_statement_ISigmaSeparation.tex`, verified equivalent
(both structurally and semantically) to the LN block (`graphs.tex`,
`\label{lem:stability_separation_marginalization}`).  The canonical
tex spells out the inline unfoldings of `iσ`-separation on each side
of the biconditional and pins down that the collider /
blockable-non-collider classifications and the ancestor set used in
the σ-blocking predicate are each computed *relative to the CDMG on
which the predicate is evaluated* — so on side (2) everything is
computed in `G^{∖D}`, not in `G`.  No `addition_to_the_LN` clauses
are attached to this row; the LN wording is authoritative as-is.

## Design pillars

1. **Single `theorem` declaration mirroring the LN's single
   biconditional.**  The LN's `\begin{Lem}` block bundles the
   statement as one equivalence between two `iσ`-separation
   predicates, with the same triple `(A, B, C)` reinterpreted on
   two CDMGs (`G` and `G^{∖D}`).  Encoded as one
   `theorem iSigmaSeparation_marginalize_iff` whose conclusion is
   a single `Iff`.  No multi-item split is appropriate: the LN
   does not stack independent sub-claims here.

2. **`Set Node`-valued node-subset arguments `A B C`.**  Matches
   the signature shape of `def_3_18`'s `IsISigmaSeparated`,
   which itself takes `A B C : Set Node`.  Keeping the same
   `Set Node` carrier at this row means the conclusion's two
   sides forward to the same `IsISigmaSeparated` predicate (just
   evaluated on two different CDMGs), with no coercion juggling
   at the iff level.

3. **`D : Finset Node` matching `marginalize`'s parameter type.**
   `def_3_14`'s `marginalize : (G : CDMG Node) (W : Finset Node)
   (hW : W ⊆ G.V) → CDMG Node` takes `W` as a `Finset` (because
   `G.V` is itself a `Finset`).  Keeping `D` as a `Finset` here
   avoids a coercion at the `marginalize`-call site inside the
   conclusion.  The disjointness premise lifts `D` to `Set Node`
   via the `↑` coercion so it can be intersected with the
   `Set`-valued triple `(A, B, C)`.

4. **`Disjoint (↑D : Set Node) (A ∪ B ∪ C)` for the LN's
   `D ∩ (A ∪ B ∪ C) = ∅`.**  The two formulations are
   propositionally equivalent (via `Set.disjoint_iff_inter_eq_empty`,
   not used here).  `Disjoint` is the more ergonomic formulation
   for threading the premise into the conclusion's three
   transported subset hypotheses: `Disjoint.mono_right` reduces
   `Disjoint ↑D (A ∪ B ∪ C)` to `Disjoint ↑D A`,
   `Disjoint ↑D B`, `Disjoint ↑D C` along the three obvious
   `_ ⊆ A ∪ B ∪ C` subset proofs.

5. **Statement-supporting helper `subset_marginalize_carrier_of_disjoint`
   transports a single subset across `marginalize`.**  The helper
   takes a `Set Node`-valued `S`, the `marginalize`'s precondition
   `hD_sub : D ⊆ G.V`, the carrier hypothesis
   `hS : S ⊆ ↑G.J ∪ ↑G.V`, and the disjointness
   `Disjoint (↑D) S`, and produces
   `S ⊆ ↑(G.marginalize D hD_sub).J ∪ ↑(G.marginalize D hD_sub).V`.
   Because the `where`-clause body of `marginalize` sets
   `.J := G.J` and `.V := G.V \ D`, this conclusion reduces
   definitionally to `S ⊆ ↑G.J ∪ ↑(G.V \ D)`, which the proof
   establishes by case-splitting on whether `a ∈ S` lies in `↑G.J`
   or in `↑G.V` (then using `Disjoint` to push `a ∉ ↑D`).  The
   helper is consumed *three times* in the main theorem's
   conclusion (once per argument set `A, B, C`); without it the
   conclusion would carry three inline tactical proofs of the
   same shape.

6. **Helper-marker placement (THREE dashes) for both the
   `variable` block and the transport lemma.**  Both are
   statement-typing infrastructure that the wrapped theorem
   signature cannot compile without: the `variable` block
   auto-binds `{Node : Type*} [DecidableEq Node]` into the
   theorem signature, and the transport lemma is referenced
   three times in the theorem's conclusion to discharge the
   well-typedness obligations of
   `(G.marginalize D hD_sub).IsISigmaSeparated A B C _ _ _`.
   Marker placement follows the
   "Helper signature only, no proof body" convention: the
   `lemma`'s end marker sits immediately after the type
   annotation, with the `:= by ...` proof body below.

7. **Body of `iSigmaSeparation_marginalize_iff` is `:= by sorry`.**
   Statement-only worker pass; the proof is the next handoff to
   Manager B.  The eventual proof will exploit the LN's reading
   that `walks-in-G-avoiding-D` are in canonical bijection with
   `walks-in-G^{∖D}`, transporting σ-blocking on each side along
   that bijection.

## Imports

* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation` —
  `def_3_18`, the `iσ`-separation predicate
  `CDMG.IsISigmaSeparated`.
* `Chapter3_GraphTheory.Section3_2.MarginalizationAK` —
  `def_3_14`, the marginalization operator `CDMG.marginalize`.

## Naming

* File: `ISigmaSeparationMarginalization.lean` — disambiguated
  from `ISigmaSeparation.lean` (which formalises `def_3_18`) by
  adding the `Marginalization` suffix that tracks the LN label
  `lem:stability_separation_marginalization`.
* Main theorem: `iSigmaSeparation_marginalize_iff` — terse,
  matches the LN's `⟺` shape and mirrors the surrounding
  Section 3.3 theorems' camelCase convention.
* Helper: `subset_marginalize_carrier_of_disjoint` — descriptive
  name capturing the "transport a subset across marginalize using
  disjointness" content.
-/

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — claim_3_25 section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same
--   chapter-wide convention used by every `CDMG`-opening file in
--   Sections 3.1, 3.2 and 3.3.  The `IsISigmaSeparated` predicate
--   (from `def_3_18`) and the `marginalize` operator (from
--   `def_3_14`) are both parameterised over this implicit binder
--   block, so the theorem signature below auto-binds these binders
--   into its type.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  This
--   `variable` block is statement-typing infrastructure that the
--   wrapped theorem signature cannot compile without.  Matches the
--   marker convention at `claim_3_22`'s `SigmaSeparationSymmetric.lean`
--   and `claim_3_24`'s `SigmaSeparationEquivalences.lean`.
-- claim_3_25 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_25 --- end helper

-- ## ref: claim_3_25 (helper) — well-typedness transport across marginalize.
--
-- `G.subset_marginalize_carrier_of_disjoint S D hD_sub hS hDS` is the
-- statement-typing helper that transports a single set inclusion
-- `S ⊆ ↑G.J ∪ ↑G.V` to its `G^{∖D}` analogue
-- `S ⊆ ↑(G.marginalize D hD_sub).J ∪ ↑(G.marginalize D hD_sub).V`,
-- using the disjointness `Disjoint (↑D : Set Node) S` as the key
-- "no element of `S` was projected away by `G ↦ G^{∖D}`" content.
--
-- The conclusion's carrier reduces by δ-reduction (the `where`-clause
-- body of `def_3_14`'s `marginalize` sets `.J := G.J` and
-- `.V := G.V \ D`) to `S ⊆ ↑G.J ∪ ↑(G.V \ D)`; the proof case-splits
-- `a ∈ S` on `↑G.J ∪ ↑G.V`, then pushes `a ∈ ↑G.V` into `↑G.V \ ↑D`
-- via the disjointness premise (`a ∈ S ⇒ a ∉ ↑D`) and
-- `Finset.coe_sdiff`.
--
-- ## Design choice — subset_marginalize_carrier_of_disjoint
--
-- *Helper-marker-wrapped (THREE dashes) because the main theorem
--   signature cannot compile without it.*  The main theorem's
--   conclusion references this helper *three times* (once per
--   argument set `A, B, C`) to produce the well-typedness proofs
--   needed by `(G.marginalize D hD_sub).IsISigmaSeparated A B C
--   _ _ _`.  Removing the helper would force the conclusion to
--   carry three inline tactical proofs of the same shape, scrambling
--   the LN-faithful surface of the iff.
--
-- *`Disjoint`-shaped disjointness premise.*  Equivalent to the LN's
--   `↑D ∩ S = ∅` (via `Set.disjoint_iff_inter_eq_empty`), but
--   `Disjoint`'s `mono_right` API gives ergonomic threading at the
--   call site: the main theorem's `hD_disj : Disjoint (↑D)
--   (A ∪ B ∪ C)` is destructured into `Disjoint (↑D) A`,
--   `Disjoint (↑D) B`, `Disjoint (↑D) C` by three short
--   `.mono_right (Set.subset_union_…)` steps.
--
-- *Polymorphism: `S : Set Node` (not specialised to `A`, `B`, or
--   `C`).*  Keeps the helper reusable across the three call sites
--   in `iSigmaSeparation_marginalize_iff`'s conclusion.  A version
--   specialised to a fixed `S` would defeat the purpose.
-- claim_3_25 --- start helper
lemma subset_marginalize_carrier_of_disjoint
    (G : CDMG Node) (S : Set Node) (D : Finset Node) (hD_sub : D ⊆ G.V)
    (hS : S ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hDS : Disjoint (↑D : Set Node) S) :
    S ⊆ (↑(G.marginalize D hD_sub).J : Set Node) ∪ ↑(G.marginalize D hD_sub).V
-- claim_3_25 --- end helper
:= by
  intro a ha
  -- (G.marginalize D hD_sub).J = G.J and
  -- (G.marginalize D hD_sub).V = G.V \ D definitionally
  -- via the `where`-clause body of `def_3_14`'s `marginalize`.
  change a ∈ (↑G.J : Set Node) ∪ ↑(G.V \ D)
  rcases hS ha with hJ | hV
  · exact Or.inl hJ
  · refine Or.inr ?_
    have ha_notD : a ∉ (↑D : Set Node) :=
      Set.disjoint_right.mp hDS ha
    rw [Finset.coe_sdiff]
    exact ⟨hV, ha_notD⟩

-- ## ref: claim_3_25 (Subtask 2 helper) — directed-walk short-witness
-- through `{u}`.
--
-- Tex Step 2(c), directed half: every `(v, w) ∈ E^{∖u}` is witnessed
-- by either a single edge `(v, w) ∈ G.E` or a 2-edge bridge
-- `v → u → w` in `G`.  This helper packages the LN's "short witness"
-- claim at the *walk level*: from any `MarginalizationΦE`-witnessing
-- directed walk `p : Walk G v w` whose intermediate vertices all
-- equal `u`, extract the disjunction
--   `(v, w) ∈ G.E ∨ ((v, u) ∈ G.E ∧ (u, w) ∈ G.E)`.
--
-- The walk `p` may have arbitrary length ≥ 1, but the conclusion
-- only exposes the first edge `(v, u)` and the last edge `(u, w)`
-- (intermediate `u → u` self-loops between them are absorbed by the
-- IH).  Structural recursion on `p`: the `.nil` case contradicts
-- `p.length ≥ 1`; the two non-`.forwardE` cons constructors
-- contradict `IsDirectedWalk`; the `.forwardE` case either has its
-- tail `q = .nil` (length-1 → direct edge `(v, w) ∈ G.E`) or
-- recurses on `q` after observing that the first intermediate
-- (the cons-middle vertex `mid`) is `u` (by `hinter` applied to
-- the head of `q.vertices.dropLast`).
--
-- ## Design choice — directed_walk_E_short_witness
--
-- *Private helper, kept narrow.*  Consumed once below by
-- `marginalize_one_node_E_short_witness` and three times by
-- `bifurcation_with_split_short_witness` (each `.bidir`/`.backwardE`
-- hinge case lands on a directed tail walk and extracts the
-- `(u, b) ∈ G.E` ending edge).  No use beyond this file is
-- anticipated, so `private` keeps it out of the public CDMG API.
--
-- *Structural recursion on the walk, not on a length-bound.*  Lean's
-- equation compiler accepts the recursion directly: the recursive
-- call on the inner walk `q` in the `.cons _ (.forwardE _) (.cons _ _ _)`
-- case feeds Lean a strictly smaller subterm of the outer cons.  A
-- strong-induction-on-length variant was considered and rejected as
-- a step backwards from the existing `Walks.lean` style (the
-- companion lemma `find_first_non_W_directed` of
-- `MargPreservesAncestors.lean:618` recurses on the walk too).
private lemma directed_walk_E_short_witness {G : CDMG Node} (u : Node) :
    ∀ {v w : Node} (p : Walk G v w),
      p.IsDirectedWalk → p.length ≥ 1 →
      (∀ x ∈ p.vertices.tail.dropLast, x = u) →
      ((v, w) ∈ G.E) ∨ ((v, u) ∈ G.E ∧ (u, w) ∈ G.E)
  | _, _, .nil _ _, _, hlen, _ => by simp [Walk.length] at hlen
  | _, _, .cons _ (.backwardE _) _, hdir, _, _ => hdir.elim
  | _, _, .cons _ (.bidir _) _, hdir, _, _ => hdir.elim
  | v, _, .cons mid (.forwardE h_E) q, hdir, _, hinter => by
      have hq_dir : q.IsDirectedWalk := hdir
      by_cases hq_pos : q.length ≥ 1
      · -- Length ≥ 2: extract `mid = u`, then convert types via the
        -- equality (avoiding `subst`, which in this equation-style
        -- function would erase the lemma parameter `u` rather than
        -- the pattern-bound `mid`).
        have hq_tail_ne : q.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos q hq_pos
        have hq_vs_decomp : q.vertices = mid :: q.vertices.tail :=
          Walk.vertices_eq_head_cons_tail q
        have hq_drop_decomp :
            q.vertices.dropLast = mid :: q.vertices.tail.dropLast := by
          conv_lhs => rw [hq_vs_decomp]
          exact List.dropLast_cons_of_ne_nil hq_tail_ne
        have hmid_eq : mid = u := by
          refine hinter mid ?_
          change mid ∈ q.vertices.dropLast
          rw [hq_drop_decomp]
          exact List.mem_cons_self
        have hq_inter : ∀ x ∈ q.vertices.tail.dropLast, x = u := by
          intro x hx
          refine hinter x ?_
          change x ∈ q.vertices.dropLast
          rw [hq_drop_decomp]
          exact List.mem_cons.mpr (Or.inr hx)
        have IH := directed_walk_E_short_witness u q hq_dir hq_pos hq_inter
        -- IH : ((mid, w) ∈ G.E) ∨ ((mid, u) ∈ G.E ∧ (u, w) ∈ G.E).
        -- Outer goal: ((v, w) ∈ G.E) ∨ ((v, u) ∈ G.E ∧ (u, w) ∈ G.E).
        -- `h_E : (v, mid) ∈ G.E`; convert via `hmid_eq` (`▸`).
        have hvu : (v, u) ∈ G.E := hmid_eq ▸ h_E
        rcases IH with h_mw | ⟨_, h_uw⟩
        · -- Pattern 2: combine `h_E` and `h_mw` after `mid = u` rewrite.
          exact Or.inr ⟨hvu, hmid_eq ▸ h_mw⟩
        · exact Or.inr ⟨hvu, h_uw⟩
      · -- Length 1: `q = .nil`, `mid = w`, direct edge `(v, w) ∈ G.E`.
        have hq_zero : q.length = 0 := by omega
        match q, hq_zero with
        | .nil _ _, _ => exact Or.inl h_E

-- ## ref: claim_3_25 (Subtask 2 helper) — bifurcation-with-split
-- short-witness through `{u}`.
--
-- Tex Step 2(c), bidirected half: every `s(v, w) ∈ L^{∖u}` is
-- witnessed by one of four short patterns from the LN —
--   (1) direct bidirected `s(v, w) ∈ G.L`,
--   (2) fork `v ← u → w` ⟺ `(u, v), (u, w) ∈ G.E`,
--   (3) left hinge `v ↔ u → w` ⟺ `s(v, u) ∈ G.L ∧ (u, w) ∈ G.E`,
--   (4) right hinge `v ← u ↔ w` ⟺ `(u, v) ∈ G.E ∧ s(u, w) ∈ G.L`.
-- This helper is the "with-split-index" sister: given a bifurcation
-- walk `p : Walk G a b` of split index `k` and all intermediates =
-- `u`, extract the 4-way disjunction for `(a, b)`.
--
-- Implementation: structural recursion on `p` with case-splits on
-- the head WalkStep constructor and the split index, matching the
-- def-cases of `Walk.IsBifurcationWithSplit` one-to-one:
-- * `.cons _ (.forwardE _) _, _`: always rejected by IsBifurcationWithSplit.
-- * `.cons _ (.backwardE _) (.nil _ _), _`: rejected (length 1 with .backwardE).
-- * `.cons _ (.bidir _) _, k+1`: rejected (only .backwardE first edges decrement).
-- * `.cons _ (.bidir h_L) (.nil _ _), 0`: direct bidir, pattern (1).
-- * `.cons mid (.bidir h_L) (.cons z s' p''), 0`: hinge-left, pattern (3);
--   tail is a directed walk and feeds `directed_walk_E_short_witness`.
-- * `.cons mid (.backwardE h_E) (.cons z s' p''), 0`: fork, pattern (2);
--   tail is a directed walk and feeds `directed_walk_E_short_witness`.
-- * `.cons mid (.backwardE h_E) (.cons z s' p''), k+1`: recursive case;
--   the tail is a bifurcation with split `k` over the same `{u}`-intermediates.
--
-- In every "real" case, `mid` is the first intermediate of the
-- outer walk, hence `mid = u` by `hinter` (this holds because the
-- tail is non-`.nil`, so `(Walk.cons z s' p'').vertices.tail ≠ []`
-- and `mid` lies at the head of the dropLast).  After `subst mid := u`,
-- the head WalkStep's edge witness `h_L`/`h_E` carries the correct
-- shape (resp.\ `s(a, u) ∈ G.L` or `(u, a) ∈ G.E`) for assembly
-- with the tail's pattern into the outer pattern.
--
-- ## Design choice — bifurcation_with_split_short_witness
--
-- *Private helper, kept narrow.*  Consumed once below by
-- `marginalize_one_node_L_short_witness`.  Not part of the public
-- CDMG API.
--
-- *Pass the split index `k` explicitly rather than `∃ k, …`.*  The
-- structural recursion needs a concrete `k` to case-split on; the
-- wrapper `marginalize_one_node_L_short_witness` destructures the
-- existential `∃ i, p.IsBifurcationWithSplit i` from
-- `Walk.IsBifurcation`'s fourth conjunct exactly once.
--
-- *No `a ≠ b` hypothesis.*  The conclusion's first disjunct
-- `s(a, b) ∈ G.L` is delivered only in the length-1 case where the
-- `.bidir` edge witnesses `s(a, b) ∈ G.L` directly; `G.L`'s own
-- irreflexivity (the `hL_irrefl` field of `CDMG`) would force
-- `a ≠ b` if needed downstream, so this helper does not require
-- the hypothesis.
private lemma bifurcation_with_split_short_witness {G : CDMG Node} (u : Node) :
    ∀ {a b : Node} (p : Walk G a b) (k : ℕ),
      p.IsBifurcationWithSplit k →
      (∀ x ∈ p.vertices.tail.dropLast, x = u) →
      (s(a, b) ∈ G.L) ∨
      ((u, a) ∈ G.E ∧ (u, b) ∈ G.E) ∨
      (s(u, a) ∈ G.L ∧ (u, b) ∈ G.E) ∨
      ((u, a) ∈ G.E ∧ s(u, b) ∈ G.L)
  | _, _, .nil _ _, _, h, _ => h.elim
  | _, _, .cons _ (.forwardE _) (.nil _ _), 0, h, _ => h.elim
  | _, _, .cons _ (.forwardE _) (.cons _ _ _), 0, h, _ => h.elim
  | _, _, .cons _ (.forwardE _) _, _ + 1, h, _ => by
      simp only [Walk.IsBifurcationWithSplit] at h
  | _, _, .cons _ (.backwardE _) (.nil _ _), 0, h, _ => h.elim
  | _, _, .cons _ (.backwardE _) (.nil _ _), _ + 1, h, _ => by
      simp only [Walk.IsBifurcationWithSplit] at h
  | _, _, .cons _ (.bidir _) _, _ + 1, h, _ => by
      simp only [Walk.IsBifurcationWithSplit] at h
  | _, _, .cons _ (.bidir h_L) (.nil _ _), 0, _, _ =>
      -- Length 1: single bidirected edge, pattern (1).
      Or.inl h_L
  | _, _, .cons mid (.bidir h_L) (.cons z s' p''), 0, h_split, hinter => by
      -- Length ≥ 2, hinge `.bidir` at position 0, tail is directed.
      have hq_dir : (Walk.cons z s' p'').IsDirectedWalk := h_split
      have hq_pos : (Walk.cons z s' p'').length ≥ 1 := by simp [Walk.length]
      have hq_tail_ne : (Walk.cons z s' p'').vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos _ hq_pos
      have hq_vs_decomp : (Walk.cons z s' p'').vertices
            = mid :: (Walk.cons z s' p'').vertices.tail :=
        Walk.vertices_eq_head_cons_tail _
      have hq_drop_decomp : (Walk.cons z s' p'').vertices.dropLast
            = mid :: (Walk.cons z s' p'').vertices.tail.dropLast := by
        conv_lhs => rw [hq_vs_decomp]
        exact List.dropLast_cons_of_ne_nil hq_tail_ne
      have hmid_eq : mid = u := by
        refine hinter mid ?_
        change mid ∈ (Walk.cons z s' p'').vertices.dropLast
        rw [hq_drop_decomp]
        exact List.mem_cons_self
      have hq_inter :
          ∀ x ∈ (Walk.cons z s' p'').vertices.tail.dropLast, x = u := by
        intro x hx
        refine hinter x ?_
        change x ∈ (Walk.cons z s' p'').vertices.dropLast
        rw [hq_drop_decomp]
        exact List.mem_cons.mpr (Or.inr hx)
      have IH := directed_walk_E_short_witness u (Walk.cons z s' p'')
        hq_dir hq_pos hq_inter
      -- IH : ((mid, b) ∈ G.E) ∨ ((mid, u) ∈ G.E ∧ (u, b) ∈ G.E)
      have h_ub : (u, _) ∈ G.E :=
        IH.elim (fun h_mid_b => hmid_eq ▸ h_mid_b) And.right
      -- `h_L : s(_, mid) ∈ G.L` (where `_` is the outer source);
      -- rewrite `mid → u` then swap via `Sym2.eq_swap` for pattern (3).
      have h_L_swap : s(u, _) ∈ G.L := Sym2.eq_swap ▸ hmid_eq ▸ h_L
      exact Or.inr (Or.inr (Or.inl ⟨h_L_swap, h_ub⟩))
  | _, _, .cons mid (.backwardE h_E) (.cons z s' p''), 0, h_split, hinter => by
      -- Length ≥ 2, hinge `.backwardE` at position 0, tail is directed.
      have hq_dir : (Walk.cons z s' p'').IsDirectedWalk := h_split
      have hq_pos : (Walk.cons z s' p'').length ≥ 1 := by simp [Walk.length]
      have hq_tail_ne : (Walk.cons z s' p'').vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos _ hq_pos
      have hq_vs_decomp : (Walk.cons z s' p'').vertices
            = mid :: (Walk.cons z s' p'').vertices.tail :=
        Walk.vertices_eq_head_cons_tail _
      have hq_drop_decomp : (Walk.cons z s' p'').vertices.dropLast
            = mid :: (Walk.cons z s' p'').vertices.tail.dropLast := by
        conv_lhs => rw [hq_vs_decomp]
        exact List.dropLast_cons_of_ne_nil hq_tail_ne
      have hmid_eq : mid = u := by
        refine hinter mid ?_
        change mid ∈ (Walk.cons z s' p'').vertices.dropLast
        rw [hq_drop_decomp]
        exact List.mem_cons_self
      have hq_inter :
          ∀ x ∈ (Walk.cons z s' p'').vertices.tail.dropLast, x = u := by
        intro x hx
        refine hinter x ?_
        change x ∈ (Walk.cons z s' p'').vertices.dropLast
        rw [hq_drop_decomp]
        exact List.mem_cons.mpr (Or.inr hx)
      have IH := directed_walk_E_short_witness u (Walk.cons z s' p'')
        hq_dir hq_pos hq_inter
      have h_ub : (u, _) ∈ G.E :=
        IH.elim (fun h_mid_b => hmid_eq ▸ h_mid_b) And.right
      -- `h_E : (mid, _) ∈ G.E` (backwardE encodes `(target, source) ∈ E`);
      -- rewrite `mid → u`.
      have h_ua : (u, _) ∈ G.E := hmid_eq ▸ h_E
      -- Pattern (2): fork `(u, a) ∈ G.E ∧ (u, b) ∈ G.E`.
      exact Or.inr (Or.inl ⟨h_ua, h_ub⟩)
  | _, _, .cons mid (.backwardE h_E) (.cons z s' p''), k + 1, h_split, hinter => by
      -- Length ≥ 2, split ≥ 1, recurse on tail with split `k`.
      have hq_split : (Walk.cons z s' p'').IsBifurcationWithSplit k := h_split
      have hq_pos : (Walk.cons z s' p'').length ≥ 1 := by simp [Walk.length]
      have hq_tail_ne : (Walk.cons z s' p'').vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos _ hq_pos
      have hq_vs_decomp : (Walk.cons z s' p'').vertices
            = mid :: (Walk.cons z s' p'').vertices.tail :=
        Walk.vertices_eq_head_cons_tail _
      have hq_drop_decomp : (Walk.cons z s' p'').vertices.dropLast
            = mid :: (Walk.cons z s' p'').vertices.tail.dropLast := by
        conv_lhs => rw [hq_vs_decomp]
        exact List.dropLast_cons_of_ne_nil hq_tail_ne
      have hmid_eq : mid = u := by
        refine hinter mid ?_
        change mid ∈ (Walk.cons z s' p'').vertices.dropLast
        rw [hq_drop_decomp]
        exact List.mem_cons_self
      have hq_inter :
          ∀ x ∈ (Walk.cons z s' p'').vertices.tail.dropLast, x = u := by
        intro x hx
        refine hinter x ?_
        change x ∈ (Walk.cons z s' p'').vertices.dropLast
        rw [hq_drop_decomp]
        exact List.mem_cons.mpr (Or.inr hx)
      have IH := bifurcation_with_split_short_witness u (Walk.cons z s' p'')
        k hq_split hq_inter
      -- IH gives the four patterns for `(mid, b)`.  Each `mid` becomes
      -- `u` via `hmid_eq ▸`.
      have h_ua : (u, _) ∈ G.E := hmid_eq ▸ h_E
      rcases IH with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      -- IH pattern (1): `s(mid, b) ∈ G.L` → outer pattern (4) right hinge.
      · exact Or.inr (Or.inr (Or.inr ⟨h_ua, hmid_eq ▸ h⟩))
      -- IH pattern (2): `(u, b) ∈ G.E` (right conjunct of fork) → outer (2) fork.
      · exact Or.inr (Or.inl ⟨h_ua, h⟩)
      -- IH pattern (3): `(u, b) ∈ G.E` (right of left hinge) → outer (2) fork.
      · exact Or.inr (Or.inl ⟨h_ua, h⟩)
      -- IH pattern (4): `s(u, b) ∈ G.L` (right of right hinge) → outer (4) right hinge.
      · exact Or.inr (Or.inr (Or.inr ⟨h_ua, h⟩))

-- ## ref: claim_3_25 (Subtask 2) — short-witness edge-lifting taxonomy
-- for directed edges of `G.marginalize {u} hu`.
--
-- `marginalize_one_node_E_short_witness G u hu hvw` is the LN's
-- Step 2(c) directed-edge taxonomy specialized to one-node
-- marginalization `W = {u}`: every directed edge
-- `(v, w) ∈ E^{∖u}` is either already present in `G.E` or arises
-- from a two-edge bridge `v → u → w` through the removed node
-- `u`.  The walk-level claim is established by
-- `directed_walk_E_short_witness` above; this lemma is its
-- edge-level corollary, threaded through the
-- `(Finset.mem_filter ↔ MarginalizationΦE)` unwrap of
-- `(G.marginalize {u} hu).E` membership.
--
-- ## Design choice — marginalize_one_node_E_short_witness
--
-- *Public lemma in the `CDMG` namespace.*  Consumed downstream by
-- Subtasks 4 (general-walk lift), 5 (collider preservation across
-- the lift), 7 (general-walk contraction), and 9 (walk-modification
-- surgery), each of which needs explicit pattern-classification for
-- the marg-edges they manipulate.  Dot-notation
-- `G.marginalize_one_node_E_short_witness u hu hvw` is the intended
-- consumer pattern.
--
-- *No `v ≠ u ∧ w ≠ u` premise in the conclusion.*  These are
-- *automatic* from `hvw`: the filter on `(G.marginalize {u} hu).E`
-- pins `v ∈ G.J ∪ (G.V \ {u})` and `w ∈ G.V \ {u}`, so `v ≠ u`
-- (either `v ∈ G.J` and `u ∈ G.V` are disjoint, or `v ∈ G.V \ {u}`)
-- and `w ≠ u` (likewise) without an extra hypothesis.  Downstream
-- consumers re-derive these if they need them, via the same filter
-- unfold (see `mem_of_mem_marginalize` /
-- `notW_of_mem_marginalize` in
-- `Section3_2/MargPreservesAncestors.lean`).
lemma marginalize_one_node_E_short_witness
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    {v w : Node} (hvw : (v, w) ∈ (G.marginalize {u} hu).E) :
    ((v, w) ∈ G.E) ∨ ((v, u) ∈ G.E ∧ (u, w) ∈ G.E) := by
  -- `(G.marginalize {u} hu).E` is `(...).filter (fun e => Φ_E {u} e.1 e.2)`,
  -- so membership gives the product membership AND `MarginalizationΦE`.
  have hvw_filter : (v, w) ∈
      ((G.J ∪ (G.V \ {u})) ×ˢ (G.V \ {u})).filter
        (fun e => G.MarginalizationΦE {u} e.1 e.2) := hvw
  have hΦ : G.MarginalizationΦE {u} v w := (Finset.mem_filter.mp hvw_filter).2
  obtain ⟨p, hp_dir, hp_len, hp_inter⟩ := hΦ
  -- `hp_inter` is `∀ x ∈ ..., x ∈ {u}`; reshape to `x = u`.
  have hp_inter' : ∀ x ∈ p.vertices.tail.dropLast, x = u := by
    intro x hx
    exact Finset.mem_singleton.mp (hp_inter x hx)
  exact directed_walk_E_short_witness u p hp_dir hp_len hp_inter'

-- ## ref: claim_3_25 (Subtask 2) — short-witness edge-lifting taxonomy
-- for bidirected edges of `G.marginalize {u} hu`.
--
-- `marginalize_one_node_L_short_witness G u hu hvw` is the LN's
-- Step 2(c) bidirected-edge taxonomy specialized to one-node
-- marginalization `W = {u}`: every bidirected edge
-- `s(v, w) ∈ L^{∖u}` falls into one of four short-witness patterns:
--   (1) direct `s(v, w) ∈ G.L`,
--   (2) fork `v ← u → w` ⟺ `(u, v), (u, w) ∈ G.E`,
--   (3) left hinge `v ↔ u → w` ⟺ `s(u, v) ∈ G.L ∧ (u, w) ∈ G.E`,
--   (4) right hinge `v ← u ↔ w` ⟺ `(u, v) ∈ G.E ∧ s(u, w) ∈ G.L`.
-- The walk-level claim is established by
-- `bifurcation_with_split_short_witness` above; this lemma is its
-- edge-level corollary, threaded through `marginalize_L_iff`
-- (the Sym2-image unwrap for `(G.marginalize {u} hu).L` membership)
-- and `Sym2.eq_iff` (to handle both orientations of the
-- `s(v, w) = s(e.1, e.2)` source-equality).
--
-- ## Design choice — marginalize_one_node_L_short_witness
--
-- *Four-way disjunction matches the LN's enumeration verbatim.*  The
-- LN lists exactly these four patterns at tex Step 2(c).  An
-- alternative "single existential" packaging (e.g.\ `∃ p, p.length ≤
-- 2 ∧ p.IsBifurcation ∧ p.vertices.tail.dropLast ⊆ {u}`) was
-- considered but rejected: Subtasks 4 (lift), 5 (collider
-- preservation), 7 (contract), and 9 (surgery) all need *explicit*
-- patterns to dispatch on, so packaging them into an existential
-- would force every consumer to unpack-by-hand at every use site.
--
-- *Sym2-symmetry handling.*  `marginalize_L_iff` gives the
-- representative `e : Node × Node` with `s(v, w) = s(e.1, e.2)`;
-- `Sym2.eq_iff` splits this into two orientations (`(v, w) = (e.1,
-- e.2)` or swapped).  Similarly,
-- `Walk.MarginalizationΦL` is a disjunction over forward and
-- backward bifurcations.  Combined, we have 4 sub-cases (2 × 2).
-- Patterns (1) and (2) are symmetric in `(v, w)`; patterns (3) and
-- (4) swap into each other (using `Sym2.eq_swap`).  The four
-- sub-cases are routed to the appropriate output disjunct via
-- `rcases` and a small amount of pattern-swap bookkeeping.
lemma marginalize_one_node_L_short_witness
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    {v w : Node} (hvw : s(v, w) ∈ (G.marginalize {u} hu).L) :
    (s(v, w) ∈ G.L) ∨
    ((u, v) ∈ G.E ∧ (u, w) ∈ G.E) ∨
    (s(u, v) ∈ G.L ∧ (u, w) ∈ G.E) ∨
    ((u, v) ∈ G.E ∧ s(u, w) ∈ G.L) := by
  -- Unwrap the Sym2-image membership.
  obtain ⟨e, _he1_VW, _he2_VW, _he_ne, hΦL, hs_eq⟩ :=
    (marginalize_L_iff G {u} hu).mp hvw
  -- `hs_eq : s(v, w) = s(e.1, e.2)`: case-split on the two
  -- orientations (Sym2 has only those two).
  rcases Sym2.eq_iff.mp hs_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Case A: `v = e.1, w = e.2`.
    rcases hΦL with ⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩
    · -- Forward bifurcation: `p : Walk G v w`.  Patterns match (a, b) = (v, w).
      have hp_inter' : ∀ x ∈ p.vertices.tail.dropLast, x = u := by
        intro x hx
        exact Finset.mem_singleton.mp (hp_inter x hx)
      obtain ⟨_, _, _, k, hk_split⟩ := hp_bif
      exact bifurcation_with_split_short_witness u p k hk_split hp_inter'
    · -- Backward bifurcation: `p : Walk G w v`.  Patterns match (a, b) = (w, v);
      -- swap to obtain (v, w) patterns.
      have hp_inter' : ∀ x ∈ p.vertices.tail.dropLast, x = u := by
        intro x hx
        exact Finset.mem_singleton.mp (hp_inter x hx)
      obtain ⟨_, _, _, k, hk_split⟩ := hp_bif
      have IH := bifurcation_with_split_short_witness u p k hk_split hp_inter'
      rcases IH with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- Inner pattern (1) `s(w, v) ∈ G.L` → outer pattern (1) `s(v, w) ∈ G.L`.
        left
        rw [Sym2.eq_swap]
        exact h
      · -- Inner pattern (2) `(u, w) ∈ G.E ∧ (u, v) ∈ G.E` → outer (2) fork.
        right; left
        exact ⟨h2, h1⟩
      · -- Inner pattern (3) `s(u, w) ∈ G.L ∧ (u, v) ∈ G.E` → outer (4) right hinge.
        right; right; right
        exact ⟨h2, h1⟩
      · -- Inner pattern (4) `(u, w) ∈ G.E ∧ s(u, v) ∈ G.L` → outer (3) left hinge.
        right; right; left
        exact ⟨h2, h1⟩
  · -- Case B: `v = e.2, w = e.1`.
    rcases hΦL with ⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩
    · -- Forward bifurcation: `p : Walk G w v` (since v = e.2, w = e.1).
      have hp_inter' : ∀ x ∈ p.vertices.tail.dropLast, x = u := by
        intro x hx
        exact Finset.mem_singleton.mp (hp_inter x hx)
      obtain ⟨_, _, _, k, hk_split⟩ := hp_bif
      have IH := bifurcation_with_split_short_witness u p k hk_split hp_inter'
      rcases IH with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [Sym2.eq_swap]
        exact h
      · right; left
        exact ⟨h2, h1⟩
      · right; right; right
        exact ⟨h2, h1⟩
      · right; right; left
        exact ⟨h2, h1⟩
    · -- Backward bifurcation: `p : Walk G v w`.
      have hp_inter' : ∀ x ∈ p.vertices.tail.dropLast, x = u := by
        intro x hx
        exact Finset.mem_singleton.mp (hp_inter x hx)
      obtain ⟨_, _, _, k, hk_split⟩ := hp_bif
      exact bifurcation_with_split_short_witness u p k hk_split hp_inter'

-- ## ref: claim_3_25 (Subtask 3 helper) — directed-walk empty-interior
-- reduction to a single directed edge.
--
-- `MarginalizationΦE G ∅ v w` is the LN's
-- `\exists` length-`≥ 1` directed walk from `v` to `w` in `G` whose
-- intermediate vertices all lie in `∅`.  Since no node lies in `∅`,
-- this forces the walk to have empty interior
-- (`p.vertices.tail.dropLast = []`), which combined with `length ≥ 1`
-- pins the walk to length exactly 1 — i.e.\ a single directed edge
-- `(v, w) ∈ G.E`.  Conversely, every `(v, w) ∈ G.E` is witnessed by
-- the length-1 walk `cons w (.forwardE _) (.nil w _)`, which has
-- empty interior by construction.
--
-- ## Design choice — marginalizationΦE_empty_iff
--
-- *Private helper.*  Consumed only by `marginalize_empty_eq_self`
-- below.  No other site in the chapter needs the empty-`W` specialisation
-- of `MarginalizationΦE`, so the helper stays `private`.
--
-- *Forward direction reuses `directed_walk_E_short_witness`.*  Subtask
-- 2's `directed_walk_E_short_witness u` consumes the stronger
-- "all intermediates equal `u`" hypothesis; ours is the empty-set
-- hypothesis, which vacuously implies "all equal `v`" (every element
-- of `∅` is also equal to `v`).  We instantiate with `u := v`; the
-- helper's two-disjunct conclusion
-- `((v, w) ∈ G.E) ∨ ((v, v) ∈ G.E ∧ (v, w) ∈ G.E)` collapses to
-- `(v, w) ∈ G.E` in both branches.
private lemma marginalizationΦE_empty_iff {G : CDMG Node} {v w : Node} :
    G.MarginalizationΦE ∅ v w ↔ (v, w) ∈ G.E := by
  constructor
  · rintro ⟨p, hdir, hlen, hinter⟩
    -- Convert the `∀ x ∈ ∅` hypothesis to `∀ x, x = v` (vacuously true
    -- since `x ∈ ∅` is `False`).
    have hinter' : ∀ x ∈ p.vertices.tail.dropLast, x = v := fun x hx =>
      absurd (hinter x hx) (Finset.notMem_empty x)
    rcases directed_walk_E_short_witness v p hdir hlen hinter' with h | ⟨_, h⟩
    · exact h
    · exact h
  · intro h_E
    -- Construct the length-1 directed walk `v →[h_E] w`.
    have hw_mem : w ∈ G := Finset.mem_union_right _ (G.hE_subset h_E).2
    refine ⟨Walk.cons w (.forwardE h_E) (.nil w hw_mem), ?_, ?_, ?_⟩
    · -- `IsDirectedWalk (.cons w (.forwardE _) (.nil w _))` reduces to
      -- `(.nil w _).IsDirectedWalk = True` by the def's pattern match.
      exact True.intro
    · -- length = 1 (one cons over a nil).
      rfl
    · -- empty interior: `vertices = [v, w]`, `tail = [w]`, `dropLast = []`.
      intro x hx
      exact absurd hx (by simp [Walk.vertices, List.tail])

-- ## ref: claim_3_25 (Subtask 3 helper) — bifurcation walk with empty
-- interior is a single bidirected edge.
--
-- Combined sub-lemma feeding `marginalizationΦL_empty_iff` below:
-- every walk `p : Walk G v w` that is a bifurcation *and* has empty
-- interior (`∀ x ∈ p.vertices.tail.dropLast, x ∈ ∅`) is a length-1
-- bidirected walk, giving `s(v, w) ∈ G.L ∧ v ≠ w`.
--
-- Structural recursion on `p` mirrors `IsBifurcationWithSplit`'s
-- pattern map: the `.nil` walk is rejected by `IsBifurcation`'s
-- `u ≠ v` clause; length-1 `.forwardE` / `.backwardE` walks are
-- rejected by `IsBifurcationWithSplit`'s def cases; the length-1
-- `.bidir` walk is the success case; length-`≥ 2` walks are rejected
-- by the empty-interior hypothesis (the middle vertex `mid` would
-- belong to `tail.dropLast`).
private lemma bifurcation_empty_interior {G : CDMG Node} :
    ∀ {v w : Node} (p : Walk G v w), p.IsBifurcation →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ (∅ : Finset Node)) →
      s(v, w) ∈ G.L ∧ v ≠ w
  | _, _, .nil _ _, hbif, _ => (hbif.1 rfl).elim
  | _, _, .cons _ (.forwardE _) (.nil _ _), hbif, _ => by
      obtain ⟨_, _, _, k, hk_split⟩ := hbif
      match k, hk_split with
      | 0, h => exact h.elim
      | _ + 1, h => simp only [Walk.IsBifurcationWithSplit] at h
  | _, _, .cons _ (.backwardE _) (.nil _ _), hbif, _ => by
      obtain ⟨_, _, _, k, hk_split⟩ := hbif
      match k, hk_split with
      | 0, h => exact h.elim
      | _ + 1, h => simp only [Walk.IsBifurcationWithSplit] at h
  | _, _, .cons _ (.bidir h_L) (.nil _ _), hbif, _ =>
      ⟨h_L, hbif.1⟩
  | _, _, .cons mid _ (.cons _ _ q), _, hinter => by
      exfalso
      -- Length ≥ 2 walk: outer.tail.dropLast = mid :: q.vertices.dropLast,
      -- so `mid` is in the interior — contradicts the empty hypothesis.
      have h_q_vs_ne : q.vertices ≠ [] := by
        cases q <;> simp [Walk.vertices]
      have h_mid_in : mid ∈ (mid :: q.vertices).dropLast := by
        rw [List.dropLast_cons_of_ne_nil h_q_vs_ne]
        exact List.mem_cons_self
      exact Finset.notMem_empty mid (hinter mid h_mid_in)

-- ## ref: claim_3_25 (Subtask 3 helper) — `Φ_L ∅ ↔ direct G-bidir edge`.
--
-- The bifurcation predicate `MarginalizationΦL` with empty
-- intermediate set reduces (via `bifurcation_empty_interior` above)
-- to the existence of a length-1 bidirected walk between `v` and `w`
-- in either orientation; both orientations yield `s(v, w) ∈ G.L`
-- (via `Sym2.eq_swap` for the reverse case) together with `v ≠ w`
-- (which IsBifurcation already requires).  Conversely, every
-- `s(v, w) ∈ G.L` with `v ≠ w` is witnessed by the length-1 bidir
-- walk `cons w (.bidir _) (.nil w _)`.
--
-- ## Design choice — marginalizationΦL_empty_iff
--
-- *Private helper.*  Consumed only by `marginalize_empty_eq_self`
-- below.  No other site in the chapter needs the empty-`W`
-- specialisation of `MarginalizationΦL`.
--
-- *Conclusion bundles `v ≠ w` even though the LN-level conclusion
-- only mentions `s(v, w) ∈ G.L`.*  The `v ≠ w` conjunct is
-- *load-bearing* for the L-field equality in
-- `marginalize_empty_eq_self`: the marginalize `L`-field filter
-- carries an `e.1 ≠ e.2` conjunct that must be exhibited at every
-- membership site, so packaging `v ≠ w` here saves a re-derivation
-- at the consumer.
private lemma marginalizationΦL_empty_iff {G : CDMG Node} {v w : Node} :
    G.MarginalizationΦL ∅ v w ↔ s(v, w) ∈ G.L ∧ v ≠ w := by
  constructor
  · rintro (⟨p, hbif, hinter⟩ | ⟨p, hbif, hinter⟩)
    · exact bifurcation_empty_interior p hbif hinter
    · -- Reverse-orientation walk `p : Walk G w v`; result is
      -- `s(w, v) ∈ G.L ∧ w ≠ v`; rephrase via `Sym2.eq_swap` and `Ne.symm`.
      obtain ⟨hwv, hne⟩ := bifurcation_empty_interior p hbif hinter
      exact ⟨Sym2.eq_swap ▸ hwv, hne.symm⟩
  · rintro ⟨h_L, hne⟩
    -- Witness: the length-1 bidir walk.
    have hw_mem : w ∈ G :=
      Finset.mem_union_right _ (G.hL_subset h_L (Sym2.mem_mk_right v w))
    refine Or.inl ⟨Walk.cons w (.bidir h_L) (.nil w hw_mem), ?_, ?_⟩
    · -- IsBifurcation: u ≠ v + endpoint-not-in-tail/dropLast + split witness.
      refine ⟨hne, ?_, ?_, 0, ?_⟩
      · -- v ∉ [w]: reduces via the walk's vertex list to `v ≠ w`.
        intro hmem
        have : v = w := by
          simpa only [Walk.vertices, List.tail_cons, List.mem_singleton]
            using hmem
        exact hne this
      · -- w ∉ [v]: reduces via the walk's vertex list to `w ≠ v`.
        intro hmem
        have : w = v := by
          simpa only [Walk.vertices, List.dropLast_cons_of_ne_nil,
            List.dropLast, List.mem_singleton] using hmem
        exact hne.symm this
      · -- IsBifurcationWithSplit (cons w (.bidir _) (.nil w _)) 0 = True
        exact True.intro
    · -- empty interior: tail.dropLast = [].
      intro x hx
      exact absurd hx (by simp [Walk.vertices, List.tail])

-- ## ref: claim_3_25 (Subtask 3) — `G.marginalize ∅ _ = G` (CDMG eq).
--
-- The LN's tex-proof base case (tex line 108) reads: "If #D = 0, then
-- D = ∅, and by def 3.14 items i.-iv., G^{∖∅} = G verbatim (the
-- predicates Φ_E and Φ_L then reduce to 'the edge already lies in E
-- resp. L'); the equivalence is trivially the reflexive equivalence."
--
-- We realise this "G^{∖∅} = G verbatim" reading literally as a CDMG
-- equality.  The four data fields agree:
--   * `J^{∖∅} := G.J` — definitionally.
--   * `V^{∖∅} := G.V \ ∅ = G.V` — via `Finset.sdiff_empty`.
--   * `E^{∖∅} = G.E` — via `marginalizationΦE_empty_iff` plus
--     `Finset.ext` over the filter-product carrier.
--   * `L^{∖∅} = G.L` — via `marginalizationΦL_empty_iff` plus the
--     Sym2-image / filter-product unwrap; the backward inclusion
--     uses `hL_subset` and `hL_irrefl` to exhibit `s(a, b) ∈ G.L`
--     as living in the image's domain.
-- The four `Prop`-valued obligation fields (`hJV_disj, hE_subset,
-- hL_subset, hL_irrefl`) collapse via proof-irrelevance once the
-- four data fields are pinned down (CDMG-extensionality pattern from
-- `marginalize_comm`, `MarginalizationsCommute.lean:3480-3485`).
--
-- ## Design choice — marginalize_empty_eq_self
--
-- *Public lemma in the `CDMG` namespace.*  Consumed downstream by
-- Subtask 11 (the outer induction's `D.card = 0` branch) to dispatch
-- the base case in two lines: `subst` `D = ∅`, then
-- `rw [marginalize_empty_eq_self G hW]` reduces the iff to
-- `Iff.rfl` modulo proof-irrelevance on the carrier witnesses.
--
-- *Explicit `hW : ∅ ⊆ G.V` parameter, not `Finset.empty_subset _`.*
-- Subtask 11 will be calling this in a `D.card = 0 → D = ∅` branch
-- where the relevant `D ⊆ G.V` hypothesis is in context as
-- `hD_sub : D ⊆ G.V`.  After `subst hD_empty`, the hypothesis
-- becomes `∅ ⊆ G.V` of the *same shape* this lemma's `hW` accepts;
-- inlining `Finset.empty_subset _` would force the caller to either
-- re-derive the proof or do extra `proof_irrel` juggling.  The
-- explicit binder is the more flexible choice.
--
-- *CDMG-extensionality is inlined as a local `have`, not promoted to
-- a global lemma.*  Matches `marginalize_comm`'s inline pattern at
-- `MarginalizationsCommute.lean:3480-3485`; no named CDMG-ext lemma
-- exists in the codebase, and adding one is out of scope for this
-- subtask.
lemma marginalize_empty_eq_self (G : CDMG Node)
    (hW : (∅ : Finset Node) ⊆ G.V) :
    G.marginalize ∅ hW = G := by
  -- ## CDMG extensionality (8-field destructure; no `hL_symm`).
  have cdmgExt : ∀ {G₁ G₂ : CDMG Node},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, _, E₁, _, L₁, _, _⟩
           ⟨J₂, V₂, _, E₂, _, L₂, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt rfl ?_ ?_ ?_
  · -- (G.marginalize ∅ hW).V = G.V \ ∅ = G.V (definitionally + sdiff_empty).
    exact Finset.sdiff_empty
  · -- (G.marginalize ∅ hW).E = G.E.
    apply Finset.ext
    intro e
    -- Unfold the marg.E filter+product carrier; use sdiff_empty to drop the `\ ∅`.
    change e ∈ ((G.J ∪ (G.V \ ∅)) ×ˢ (G.V \ ∅)).filter
              (fun e => G.MarginalizationΦE ∅ e.1 e.2) ↔ e ∈ G.E
    rw [Finset.sdiff_empty]
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨fun ⟨_, hΦ⟩ => marginalizationΦE_empty_iff.mp hΦ, fun he => ?_⟩
    exact ⟨⟨(G.hE_subset he).1, (G.hE_subset he).2⟩,
           marginalizationΦE_empty_iff.mpr he⟩
  · -- (G.marginalize ∅ hW).L = G.L.
    apply Finset.ext
    intro s
    -- Unfold the marg.L Sym2-image-of-filter-product carrier.
    change s ∈ (((G.V \ ∅) ×ˢ (G.V \ ∅)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL ∅ e.1 e.2)).image
              (fun e => s(e.1, e.2)) ↔ s ∈ G.L
    rw [Finset.sdiff_empty]
    rw [Finset.mem_image]
    refine ⟨fun ⟨e, hF, hSeq⟩ => ?_, fun hs => ?_⟩
    · -- Forward: e ∈ filter ⇒ Φ_L ∅ e.1 e.2 ⇒ s(e.1, e.2) ∈ G.L = s.
      rw [Finset.mem_filter, Finset.mem_product] at hF
      obtain ⟨_, _, hΦ⟩ := hF
      subst hSeq
      exact (marginalizationΦL_empty_iff.mp hΦ).1
    · -- Backward: s = s(a, b) ∈ G.L gives (a, b) in the filter via
      -- hL_subset (carrier) + hL_irrefl (irreflex) + Φ_L iff.
      induction s using Sym2.ind with
      | _ a b =>
        refine ⟨(a, b), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        have h_aV : a ∈ G.V := G.hL_subset hs (Sym2.mem_mk_left a b)
        have h_bV : b ∈ G.V := G.hL_subset hs (Sym2.mem_mk_right a b)
        have h_ne : a ≠ b := by
          intro h_eq
          exact G.hL_irrefl hs (Sym2.mk_isDiag_iff.mpr h_eq)
        exact ⟨⟨h_aV, h_bV⟩, h_ne,
               marginalizationΦL_empty_iff.mpr ⟨hs, h_ne⟩⟩

-- ## ref: claim_3_25 (Subtask 3 helper) — `iσ`-separation transports
-- across CDMG equality.
--
-- A small private helper to side-step the `motive is not type correct`
-- failure that arises from a direct `rw [marginalize_empty_eq_self ...]`
-- on the main iff lemma below.  By binding *two* fresh CDMG variables
-- `G₁ G₂` and the equality between them, `subst heq` cleanly replaces
-- one with the other (in particular, in the *types* of the dependent
-- witness arguments `hA₂ hB₂ hC₂`).  After substitution, both sides of
-- the iff reduce to `G₁.IsISigmaSeparated A B C ? ? ?` with
-- propositionally-equal witnesses; `rfl` closes via proof-irrelevance.
--
-- Consumed once below by `iSigmaSeparation_marginalize_empty_iff`; no
-- other planned site needs the general "transport-across-CDMG-eq"
-- shape, so the helper stays `private`.
private lemma iSigmaSeparated_iff_of_eq {G₁ G₂ : CDMG Node} (heq : G₁ = G₂)
    {A B C : Set Node}
    (hA₁ : A ⊆ (↑G₁.J : Set Node) ∪ ↑G₁.V)
    (hB₁ : B ⊆ (↑G₁.J : Set Node) ∪ ↑G₁.V)
    (hC₁ : C ⊆ (↑G₁.J : Set Node) ∪ ↑G₁.V)
    (hA₂ : A ⊆ (↑G₂.J : Set Node) ∪ ↑G₂.V)
    (hB₂ : B ⊆ (↑G₂.J : Set Node) ∪ ↑G₂.V)
    (hC₂ : C ⊆ (↑G₂.J : Set Node) ∪ ↑G₂.V) :
    G₁.IsISigmaSeparated A B C hA₁ hB₁ hC₁ ↔
      G₂.IsISigmaSeparated A B C hA₂ hB₂ hC₂ := by
  subst heq
  rfl

-- ## ref: claim_3_25 (Subtask 3) — `iσ`-separation iff at `D = ∅`.
--
-- The LN's tex-proof base case (tex line 108): "the equivalence is
-- trivially the reflexive equivalence."  We expose this as a
-- convenience wrapper around `marginalize_empty_eq_self`: Subtask
-- 11's `D.card = 0` branch substitutes `D = ∅` and applies this iff
-- to discharge the outer iff's base case in one tactic step.
--
-- ## Design choice — iSigmaSeparation_marginalize_empty_iff
--
-- *Explicit transported witnesses `hA' hB' hC'` as binders.*
-- Subtask 11 will be calling this after a `subst hD_empty : D = ∅`,
-- at which point the outer theorem's three inlined
-- `subset_marginalize_carrier_of_disjoint A D hD_sub hA <slice>`
-- witnesses become `subset_marginalize_carrier_of_disjoint A ∅ hW hA
-- <slice>`-typed terms — concrete, named, and already in scope.
-- Taking them as explicit binders lets Subtask 11 pass them directly,
-- without forcing a particular construction shape.  An "inlined-
-- witness" alternative (calling `subset_marginalize_carrier_of_disjoint`
-- inside this lemma's signature) was considered and rejected: it
-- would couple this lemma to a *specific* witness construction at the
-- caller (the disjointness slicing chain), defeating the
-- proof-irrelevance flexibility the `hA' hB' hC'` binders give.
--
-- *Proof body — `set + subst` to fold marg → G into a fresh local
-- variable, then eliminate via the eq.*  A direct
-- `rw [marginalize_empty_eq_self G hW]` was tried first but Lean
-- rejected it with a `motive is not type correct` error: the
-- carrier witnesses `hA' hB' hC'` have types *dependent* on
-- `G.marginalize ∅ hW`, and the `rw` motive
-- `fun _a => G.IsISigmaSeparated A B C hA hB hC ↔ _a.IsISigmaSeparated
-- A B C hA' hB' hC'` does not type-check on arbitrary `_a`.  The
-- `set M := G.marginalize ∅ hW with hM` workaround abstracts the
-- marginalised graph into a fresh local variable `M` (rewriting
-- types of `hA' hB' hC'` to depend on `M` instead of `G.marginalize
-- ∅ hW`), after which `subst M` (using `M = G` from `hM` chained
-- with `marginalize_empty_eq_self`) reduces both sides of the iff
-- to `G.IsISigmaSeparated A B C ? ? ?` with proof-irrelevant
-- witnesses, and `rfl` closes.
lemma iSigmaSeparation_marginalize_empty_iff
    (G : CDMG Node) (A B C : Set Node)
    (hW : (∅ : Finset Node) ⊆ G.V)
    (hA : A ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hB : B ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hA' : A ⊆ (↑(G.marginalize ∅ hW).J : Set Node) ∪ ↑(G.marginalize ∅ hW).V)
    (hB' : B ⊆ (↑(G.marginalize ∅ hW).J : Set Node) ∪ ↑(G.marginalize ∅ hW).V)
    (hC' : C ⊆ (↑(G.marginalize ∅ hW).J : Set Node) ∪ ↑(G.marginalize ∅ hW).V) :
    G.IsISigmaSeparated A B C hA hB hC ↔
      (G.marginalize ∅ hW).IsISigmaSeparated A B C hA' hB' hC' := by
  -- Apply the `iSigmaSeparated_iff_of_eq` helper above with the CDMG
  -- equality `G = G.marginalize ∅ hW` (obtained by symmetrising
  -- `marginalize_empty_eq_self`).  The helper's `subst` cleanly
  -- replaces one CDMG with the other in the dependent witness types,
  -- which sidesteps `rw`'s motive-type-check failure on this lemma's
  -- goal shape.
  exact iSigmaSeparated_iff_of_eq (marginalize_empty_eq_self G hW).symm
    hA hB hC hA' hB' hC'

-- ## ref: claim_3_25 (Subtask 4 mini-helper) — target endpoint of a
-- WalkStep lies in the CDMG's carrier.
--
-- Sister of the existing `WalkStep.source_mem` from
-- `MargPreservesAncestors.lean:187`.  Each WalkStep constructor's
-- edge-witness puts the target endpoint into either `G.V` (E channel)
-- or `G.V` (L channel via `hL_subset` and `Sym2.mem_mk_right`).  Used
-- by the Subtask 4 step-lift helper below for the `Walk.nil` membership
-- witnesses on the lifted 1- or 2-edge bridges.
private lemma WalkStep.target_mem {G : CDMG Node}
    {u v : Node} (s : WalkStep G u v) : v ∈ G := by
  change v ∈ G.J ∪ G.V
  cases s with
  | forwardE h_E => exact Finset.mem_union_right _ (G.hE_subset h_E).2
  | backwardE h_E => exact (G.hE_subset h_E).1
  | bidir h_L =>
      exact Finset.mem_union_right _ (G.hL_subset h_L (Sym2.mem_mk_right u v))

-- ## ref: claim_3_25 (Subtask 4 helper) — single-WalkStep lift through
-- `{u}`-marginalization.
--
-- Tex Step 3 (lift each edge of `π'` to a short walk segment in `G`,
-- tex lines 174-182).  Given a single WalkStep
-- `s : WalkStep (G.marginalize {u} hu) v w`, produce a `Walk G v w`
-- of length 1 or 2 that "lifts" `s` through the LN's edge-taxonomy:
-- either the same edge already lies in `G` (length-1 segment), or `s`
-- becomes a 2-edge bridge `v ⤳ u ⤳ w` whose middle vertex is `u`.
--
-- ## Design choice — expand_walk_marginalize_one_step
--
-- *Private helper, consumed only by `expand_walk_marginalize_one`.*
-- The walk-level lift recurses on the input walk, applying this
-- helper at each cons-cell.  No anticipated direct use outside the
-- file.
--
-- *Minimal structural data in the conclusion.*  We expose only:
--   (1) `q.length = 1 ∨ q.length = 2` — short-witness bound from
--       Subtask 2's taxonomy.
--   (2) `∀ x ∈ q.vertices, x = v ∨ x = w ∨ x = u` — every vertex of
--       the lift is an endpoint of `s` or the inserted `u`.
-- Downstream consumers (Subtask 5: collider preservation, Subtask 6:
-- σ-openness assembly) re-derive arrowhead correspondence and
-- collider classification by performing their own case-split on the
-- WalkStep at the point of consumption; bundling that data here would
-- require a complex dependent-typed conjunction (matching
-- post-construction equalities `q = Walk.cons ...`) that hits Lean's
-- HEq friction.  Keeping the API minimal lets each downstream consumer
-- choose the destructuring shape that fits its proof goal.
--
-- *Existential packaging instead of a `noncomputable def`.*  The
-- short-witness disjunction from
-- `marginalize_one_node_E_short_witness` /
-- `marginalize_one_node_L_short_witness` is a `Prop`, so a constructive
-- function from `WalkStep marg v w` to `Walk G v w` would require
-- `Classical.choice`.  The existential packaging here is lighter
-- and matches the existing idiom of `expand_directed_walk_marginalize`
-- (`MargPreservesAncestors.lean:426`).
private lemma expand_walk_marginalize_one_step
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    {v w : Node} (s : WalkStep (G.marginalize {u} hu) v w) :
    ∃ (q : Walk G v w),
      (q.length = 1 ∨ q.length = 2) ∧
      (∀ x ∈ q.vertices, x = v ∨ x = w ∨ x = u) := by
  -- `u ∈ G.V`, hence `u ∈ G.J ∪ G.V = G`.
  have hu_V : u ∈ G.V := Finset.singleton_subset_iff.mp hu
  have huG : u ∈ G := Finset.mem_union_right _ hu_V
  -- `w ∈ G` via `WalkStep.target_mem` (small helper above) applied to
  -- the marg-WalkStep `s`, then transported across `mem_of_mem_marginalize`.
  have hwG : w ∈ G :=
    mem_of_mem_marginalize
      (WalkStep.target_mem (G := G.marginalize {u} hu) s)
  cases s with
  | forwardE h_marg =>
      rcases G.marginalize_one_node_E_short_witness u hu h_marg
        with h_E | ⟨h_vu, h_uw⟩
      · -- Single edge `v → w ∈ G.E`.
        refine ⟨Walk.cons w (.forwardE h_E) (.nil w hwG), Or.inl rfl, ?_⟩
        intro x hx
        change x ∈ [v, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · -- 2-edge `v → u → w`.
        refine ⟨Walk.cons u (.forwardE h_vu)
                  (Walk.cons w (.forwardE h_uw) (.nil w hwG)),
                Or.inr rfl, ?_⟩
        intro x hx
        change x ∈ [v, u, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl (List.mem_singleton.mp h))
  | backwardE h_marg =>
      rcases G.marginalize_one_node_E_short_witness u hu h_marg
        with h_E | ⟨h_wu, h_uv⟩
      · -- Single edge `(w, v) ∈ G.E`, traversed backward.
        refine ⟨Walk.cons w (.backwardE h_E) (.nil w hwG), Or.inl rfl, ?_⟩
        intro x hx
        change x ∈ [v, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · -- 2-edge `v ← u ← w`.
        refine ⟨Walk.cons u (.backwardE h_uv)
                  (Walk.cons w (.backwardE h_wu) (.nil w hwG)),
                Or.inr rfl, ?_⟩
        intro x hx
        change x ∈ [v, u, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl (List.mem_singleton.mp h))
  | bidir h_marg =>
      rcases G.marginalize_one_node_L_short_witness u hu h_marg
        with h_L | ⟨h_uv_E, h_uw_E⟩ | ⟨h_uv_L, h_uw_E⟩ | ⟨h_uv_E, h_uw_L⟩
      · -- Direct bidirected edge.
        refine ⟨Walk.cons w (.bidir h_L) (.nil w hwG), Or.inl rfl, ?_⟩
        intro x hx
        change x ∈ [v, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · -- Fork `v ← u → w`.
        refine ⟨Walk.cons u (.backwardE h_uv_E)
                  (Walk.cons w (.forwardE h_uw_E) (.nil w hwG)),
                Or.inr rfl, ?_⟩
        intro x hx
        change x ∈ [v, u, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · -- Left hinge `v ↔ u → w`.  Need `s(v, u) ∈ G.L` from `s(u, v) ∈ G.L`
        -- via Sym2.eq_swap.
        have h_vu_L : s(v, u) ∈ G.L := Sym2.eq_swap ▸ h_uv_L
        refine ⟨Walk.cons u (.bidir h_vu_L)
                  (Walk.cons w (.forwardE h_uw_E) (.nil w hwG)),
                Or.inr rfl, ?_⟩
        intro x hx
        change x ∈ [v, u, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · -- Right hinge `v ← u ↔ w`.
        refine ⟨Walk.cons u (.backwardE h_uv_E)
                  (Walk.cons w (.bidir h_uw_L) (.nil w hwG)),
                Or.inr rfl, ?_⟩
        intro x hx
        change x ∈ [v, u, w] at hx
        rcases List.mem_cons.mp hx with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl (List.mem_singleton.mp h))

-- ## ref: claim_3_25 (Subtask 4) — general-walk lift `G^∖u → G`.
--
-- Tex Step 3 (tex lines 165-214): lift a walk in the one-node
-- marginalization `G.marginalize {u} hu` back to a walk in `G`,
-- preserving endpoints.  This is the structural-lift infrastructure;
-- σ-openness preservation across the lift (LN's per-position
-- verification in Step 3) is a separate downstream concern (Subtask
-- 5's collider preservation + Subtask 6's `(1) ⟹ (2)` assembly) that
-- consumes this lemma's output together with a per-vertex
-- arrowhead-classification analysis.
--
-- The lemma's conclusion bundles the lifted walk with two pieces of
-- structural data:
--   * `q.length ≥ p.length` — the lift is at least as long as the
--     original (each `G^∖u`-edge maps to either a single `G`-edge or a
--     2-edge bridge through `u`).
--   * `∀ x ∈ q.vertices, x ∈ p.vertices ∨ x = u` — every vertex of the
--     lift is either a vertex of the original or the inserted `u`.
--     This is the vertex-set bookkeeping downstream consumers use to
--     locate the "preserved" vs "u-inserted" positions of the lift.
--
-- ## Design choice — expand_walk_marginalize_one
--
-- *Public lemma in the `CDMG` namespace.*  Consumed by Subtasks 5
-- (collider classification preservation across the lift) and 6
-- (assembly of the `(1) ⟹ (2)` direction of the main theorem).
-- Dot-notation `G.expand_walk_marginalize_one u hu p` is the intended
-- consumer pattern.
--
-- *Minimal vertex-correspondence contract (`x ∈ p.vertices ∨ x = u`).*
-- Mirrors the contract of `expand_directed_walk_marginalize`
-- (`MargPreservesAncestors.lean:426`): a single pointwise vertex
-- inclusion on the full `vertices` list, no per-slice variants.  If
-- downstream consumers need slice-restricted variants (e.g., for
-- `dropLast` / `tail` / `tail.dropLast`), they can re-derive in a
-- few lines using `Walk.vertices_comp` and `Walk.vertices_eq_head_cons_tail`
-- (the same idiom `expand_directed_walk_marginalize` carries inline).
-- Keeping the public API minimal avoids over-committing the
-- conjunction shape; downstream subtasks can extend if needed.
--
-- *No σ-openness conjunct.*  σ-openness preservation across the lift
-- is the substantive content of Subtask 6 (Step 3 of the LN proof):
-- per-position case analysis using arrowhead-type preservation +
-- collider classification preservation + `Anc^{G^∖u} ⊆ Anc^G`
-- (Subtask 1) + LN's joint treatment of (ii)/(iii) (which requires the
-- `Sc^G(b_j) ∋ u` deduction via directed-cycle membership in the
-- E-pattern-2 case, tex line 202).  That argument is large enough to
-- warrant its own subtask and is left for Subtask 6; this Subtask 4
-- deliverable is the structural backbone Subtask 6 builds on.
--
-- *Proof structure: induction on `p`.*  Base case `Walk.nil`: lift to
-- a single-vertex `Walk.nil v` in `G` via `mem_of_mem_marginalize`.
-- Inductive case `Walk.cons mid s p'`: apply
-- `expand_walk_marginalize_one_step` to `s` (gives a length-1-or-2
-- segment `q_step` in `G`), apply the IH to `p'` (gives a lifted tail
-- `q_tail`), concatenate via `Walk.comp`.  Mirror the structure of
-- `expand_directed_walk_marginalize` (~70 lines for the inductive
-- step).
lemma expand_walk_marginalize_one
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    {a b : Node} (p : Walk (G.marginalize {u} hu) a b) :
    ∃ (q : Walk G a b),
      q.length ≥ p.length ∧
      (∀ x ∈ q.vertices, x ∈ p.vertices ∨ x = u) := by
  induction p with
  | nil v hv =>
      refine ⟨Walk.nil v (mem_of_mem_marginalize hv), ?_, ?_⟩
      · -- length nil = 0 ≥ 0.
        simp [Walk.length]
      · -- All vertices of the lift are in `[v]`, which is `p.vertices`.
        intro x hx
        change x ∈ [v] at hx
        exact Or.inl hx
  | @cons _ _ mid s p' ih =>
      -- Lift the head step.
      obtain ⟨q_step, hq_step_len, hq_step_vs⟩ :=
        expand_walk_marginalize_one_step G u hu s
      -- Lift the tail.
      obtain ⟨q_tail, hq_tail_len, hq_tail_vs⟩ := ih
      refine ⟨q_step.comp q_tail, ?_, ?_⟩
      · -- Length lower bound: q_step.length + q_tail.length ≥ p'.length + 1.
        rw [Walk.length_comp]
        change p'.length + 1 ≤ q_step.length + q_tail.length
        have h_step_pos : q_step.length ≥ 1 := by
          rcases hq_step_len with h1 | h2
          · omega
          · omega
        omega
      · -- Vertex correspondence.
        intro x hx
        rw [Walk.vertices_comp] at hx
        rcases List.mem_append.mp hx with hx_step | hx_tail
        · -- x is in q_step.vertices.dropLast.
          have hx_in_q_step : x ∈ q_step.vertices :=
            List.mem_of_mem_dropLast hx_step
          rcases hq_step_vs x hx_in_q_step with h | h | h
          · -- x = (a, the source of the outer walk).
            -- The outer walk's vertex list starts with the source.
            change x ∈ (Walk.cons mid s p').vertices ∨ x = u
            change x ∈ _ :: p'.vertices ∨ x = u
            exact Or.inl (List.mem_cons.mpr (Or.inl h))
          · -- x = mid, which is the head of p'.vertices.
            change x ∈ (Walk.cons mid s p').vertices ∨ x = u
            change x ∈ _ :: p'.vertices ∨ x = u
            refine Or.inl (List.mem_cons.mpr (Or.inr ?_))
            rw [h]
            exact Walk.head_mem_vertices p'
          · exact Or.inr h
        · -- x is in q_tail.vertices.
          rcases hq_tail_vs x hx_tail with h | h
          · -- x is in p'.vertices, so x is in (cons mid s p').vertices.
            change x ∈ _ :: p'.vertices ∨ x = u
            exact Or.inl (List.mem_cons.mpr (Or.inr h))
          · exact Or.inr h

-- ## ref: claim_3_25 (Subtask 5) — per-`WalkStep` arrowhead-pattern
-- classification for `{u}`-marginalized walk-steps.
--
-- Tex Step 3 (tex lines 174-211; in particular, the "arrowhead types
-- preserved" observation at lines 181-182, the joint treatment of
-- (ii)/(iii) at lines 195-205, and the "inserted `u` is a non-
-- collider" observation at lines 210-211): every WalkStep
-- `s : WalkStep (G.marginalize {u} hu) v w` is either *identity-
-- lifted* to a single WalkStep `s' : WalkStep G v w` with the same
-- arrowhead pattern at both endpoints, or *bridge-lifted* to a
-- 2-edge chain `s₁ : WalkStep G v u` followed by
-- `s₂ : WalkStep G u w`, with three properties baked into the chain
-- shape:
--   (i)   `s₁.HeadAtSource ↔ s.HeadAtSource` — source-side arrowhead
--         agreement at `v`.
--   (ii)  `s₂.HeadAtTarget ↔ s.HeadAtTarget` — target-side arrowhead
--         agreement at `w`.
--   (iii) `¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource)` — the inserted `u`
--         vertex sits in the middle of the chain as a *non-collider*
--         (in the sense of `def_3_15`, item~ii, evaluated on the
--         length-2 sub-walk `Walk.cons u s₁ (Walk.cons w s₂ q_rest)`:
--         that walk's collider check at position 1 reduces by the
--         second-clause definition of `IsCollider` to
--         `s₁.HeadAtTarget ∧ s₂.HeadAtSource`, which the conjunct
--         negates).
--
-- These three conjuncts package the LN's "arrowhead types preserved"
-- and "inserted `u` is a non-collider" facts at the single-WalkStep
-- granularity Subtask 6 will recurse over: when Subtask 6 inducts on
-- a `(G.marginalize {u} hu)`-walk `p` and lifts each cons-cell's step
-- via this classification, the per-position arrowhead correspondence
-- at the non-`u` boundary vertices is read off via the `↔` conjuncts,
-- and the inserted-`u` non-collider property is read off the third
-- conjunct.
--
-- ## Design choice — walkstep_marginalize_one_classification
--
-- *Public lemma in the `CDMG` namespace.*  Consumed by Subtask 6
--   ((1) ⟹ (2) direction assembly).  Dot-notation
--   `G.walkstep_marginalize_one_classification u hu s` is the
--   intended consumer pattern.  Subtask 6 will branch on the outer
--   disjunction at each cons-cell of its walk induction.
--
-- *Existential-of-`WalkStep` packaging, not existential-of-`Walk`
--   packaging.*  The `expand_walk_marginalize_one_step` helper at
--   line 1034 already produces an existential `Walk G v w` of length
--   1 or 2; one might naively repackage that lemma's output by adding
--   the arrowhead conjuncts.  Doing so requires destructuring a
--   length-1-or-2 `Walk G v w` into its constituent WalkSteps, which
--   per Subtask 4's HEq friction (documented at workspace lines
--   1502-1511) triggers dependent-type goals on
--   `Walk.cons.injEq`-style destructuring.  This lemma instead avoids
--   the intermediate `Walk` packaging: it returns the constituent
--   `WalkStep`s directly as existential witnesses, so the consumer
--   builds the walk-segment with `Walk.cons` at the point of use
--   without ever pattern-matching on an outer Walk.
--
-- *`Iff` conjuncts, not `=` conjuncts, on the arrowhead-correspondence
--   clauses.*  `HeadAtSource` and `HeadAtTarget` are `Prop`-valued,
--   and their values reduce definitionally to `True` or `False` once
--   the WalkStep's constructor tag is fixed.  An `=`-conjunct between
--   two such reduced values would force `propext`-flavoured manoeuvres
--   at the call site; the `↔`-conjunct lets the consumer chain via
--   `.mp` / `.mpr` directly.  In this lemma's proof, both conjunct
--   forms are discharged by `Iff.rfl` (each branch's constructor-tag
--   pattern reduces both sides to a syntactic literal `True` /
--   `False` Prop).
--
-- *Outer 2-way disjunction (1-edge vs 2-edge lift), inner taxonomy
--   abstracted.*  The output disjunction has two outer cases that
--   abstract over the inner four-way taxonomy of
--   `marginalize_one_node_L_short_witness` (and the inner two-way
--   taxonomy of `marginalize_one_node_E_short_witness`).  This outer
--   shape matches what Subtask 6 will branch on: in the 1-edge case
--   the lifted walk's vertex at position 1 corresponds to the
--   marginalized walk's vertex at position 1 *as the same node*, so
--   σ-openness transports straightforwardly; in the 2-edge case
--   Subtask 6 inserts a `u` vertex and uses the non-collider conjunct
--   plus `u ∉ C` (from the main theorem's disjointness premise) to
--   discharge `u`'s σ-openness obligation.
--
-- *Why not also expose the `q.length = 1 ∨ q.length = 2` short-witness
--   length bound?*  The bound is implicit in the disjunction shape:
--   1-edge lift ⟹ length 1, 2-edge lift ⟹ length 2.  Adding it
--   as an extra conjunct would be redundant.  The existing
--   `expand_walk_marginalize_one_step` retains the length bound
--   because it returns a single `Walk` and the bound is otherwise
--   inaccessible; here, the disjunction shape carries the
--   information.
lemma walkstep_marginalize_one_classification
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    {v w : Node} (s : WalkStep (G.marginalize {u} hu) v w) :
    (∃ (s' : WalkStep G v w),
        (s'.HeadAtSource ↔ s.HeadAtSource) ∧
        (s'.HeadAtTarget ↔ s.HeadAtTarget)) ∨
    (∃ (s₁ : WalkStep G v u) (s₂ : WalkStep G u w),
        (s₁.HeadAtSource ↔ s.HeadAtSource) ∧
        (s₂.HeadAtTarget ↔ s.HeadAtTarget) ∧
        ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource)) := by
  cases s with
  | forwardE h_marg =>
      -- `s.HeadAtSource = False`, `s.HeadAtTarget = True` (forwardE).
      rcases G.marginalize_one_node_E_short_witness u hu h_marg
        with h_E | ⟨h_vu, h_uw⟩
      · -- 1-edge lift: directed edge `v → w` already in `G.E`.
        exact Or.inl ⟨.forwardE h_E, Iff.rfl, Iff.rfl⟩
      · -- 2-edge lift `v → u → w` via two forward directed steps.
        --   `s₁ := .forwardE h_vu` : HeadAtSource False, HeadAtTarget True.
        --   `s₂ := .forwardE h_uw` : HeadAtSource False, HeadAtTarget True.
        -- HeadAtSource at `v`: False ↔ False ✓.
        -- HeadAtTarget at `w`: True  ↔ True  ✓.
        -- Inserted-`u` non-collider: HeadAtTarget(s₁) ∧ HeadAtSource(s₂)
        --   = True ∧ False = False; the negation is vacuous.
        refine Or.inr ⟨.forwardE h_vu, .forwardE h_uw,
          Iff.rfl, Iff.rfl, ?_⟩
        rintro ⟨_, h⟩; exact h
  | backwardE h_marg =>
      -- `s.HeadAtSource = True`, `s.HeadAtTarget = False` (backwardE).
      rcases G.marginalize_one_node_E_short_witness u hu h_marg
        with h_E | ⟨h_wu, h_uv⟩
      · exact Or.inl ⟨.backwardE h_E, Iff.rfl, Iff.rfl⟩
      · -- 2-edge lift `v ← u ← w` via two backward directed steps
        -- (the underlying edges are `(u, v) ∈ G.E` and `(w, u) ∈ G.E`).
        --   `s₁ := .backwardE h_uv` : HeadAtSource True, HeadAtTarget False.
        --   `s₂ := .backwardE h_wu` : HeadAtSource True, HeadAtTarget False.
        -- HeadAtSource at `v`: True  ↔ True  ✓.
        -- HeadAtTarget at `w`: False ↔ False ✓.
        -- Inserted-`u` non-collider: HeadAtTarget(s₁) = False, conjunction
        --   is False ⟹ negation is vacuous.
        refine Or.inr ⟨.backwardE h_uv, .backwardE h_wu,
          Iff.rfl, Iff.rfl, ?_⟩
        rintro ⟨h, _⟩; exact h
  | bidir h_marg =>
      -- `s.HeadAtSource = True`, `s.HeadAtTarget = True` (bidir).
      rcases G.marginalize_one_node_L_short_witness u hu h_marg
        with h_L | ⟨h_uv_E, h_uw_E⟩ | ⟨h_uv_L, h_uw_E⟩ | ⟨h_uv_E, h_uw_L⟩
      · -- 1-edge bidirected lift: `s(v, w) ∈ G.L`.
        exact Or.inl ⟨.bidir h_L, Iff.rfl, Iff.rfl⟩
      · -- 2-edge fork `v ← u → w` from `(u, v), (u, w) ∈ G.E`.
        --   `s₁ := .backwardE h_uv_E` : HeadAtSource True, HeadAtTarget False.
        --   `s₂ := .forwardE  h_uw_E` : HeadAtSource False, HeadAtTarget True.
        -- HeadAtSource at `v`: True ↔ True ✓; HeadAtTarget at `w`: True ↔ True ✓.
        -- Inserted-`u` non-collider: HeadAtTarget(s₁) = False (backwardE),
        --   conjunction is False ⟹ negation is vacuous.
        refine Or.inr ⟨.backwardE h_uv_E, .forwardE h_uw_E,
          Iff.rfl, Iff.rfl, ?_⟩
        rintro ⟨h, _⟩; exact h
      · -- 2-edge left hinge `v ↔ u → w` from `s(u, v) ∈ G.L, (u, w) ∈ G.E`.
        -- The bidirected source-pair is symmetric: `s(u, v) = s(v, u)`,
        -- so `s(v, u) ∈ G.L` and `.bidir` typechecks as `WalkStep G v u`.
        --   `s₁ := .bidir h_vu_L`   : HeadAtSource True, HeadAtTarget True.
        --   `s₂ := .forwardE h_uw_E`: HeadAtSource False, HeadAtTarget True.
        -- HeadAtSource at `v`: True ↔ True ✓; HeadAtTarget at `w`: True ↔ True ✓.
        -- Inserted-`u` non-collider: HeadAtSource(s₂) = False (forwardE),
        --   conjunction is False ⟹ negation is vacuous.
        have h_vu_L : s(v, u) ∈ G.L := Sym2.eq_swap ▸ h_uv_L
        refine Or.inr ⟨.bidir h_vu_L, .forwardE h_uw_E,
          Iff.rfl, Iff.rfl, ?_⟩
        rintro ⟨_, h⟩; exact h
      · -- 2-edge right hinge `v ← u ↔ w` from `(u, v) ∈ G.E, s(u, w) ∈ G.L`.
        --   `s₁ := .backwardE h_uv_E` : HeadAtSource True, HeadAtTarget False.
        --   `s₂ := .bidir h_uw_L`     : HeadAtSource True, HeadAtTarget True.
        -- HeadAtSource at `v`: True ↔ True ✓; HeadAtTarget at `w`: True ↔ True ✓.
        -- Inserted-`u` non-collider: HeadAtTarget(s₁) = False (backwardE),
        --   conjunction is False ⟹ negation is vacuous.
        refine Or.inr ⟨.backwardE h_uv_E, .bidir h_uw_L,
          Iff.rfl, Iff.rfl, ?_⟩
        rintro ⟨h, _⟩; exact h

-- ## ref: claim_3_25 (Subtask 5) — Walk-level inserted-`u`
-- non-collider helper.
--
-- Tex Step 3 (tex lines 210-211): each inserted `u`-position on the
-- 2-edge lift of a marginalized walk-step is a *non-collider*.  At
-- the Walk level, when the 2-edge lift produced by
-- `walkstep_marginalize_one_classification`'s Case B is assembled
-- with a tail `tail : Walk G w x` via
-- `Walk.cons u s₁ (Walk.cons w s₂ tail)`, position 1 of the
-- resulting walk (the inserted `u` vertex) is an `IsNonCollider` in
-- the sense of `def_3_15`, item~i.
--
-- ## Design choice — walk_two_edge_inserted_u_is_non_collider
--
-- *Private helper, scoped to this file.*  Consumed by Subtask 6 to
--   discharge the inserted-`u` σ-openness obligation: combined with
--   `u ∉ C` (from the main theorem's disjointness premise
--   `Disjoint ↑{u} (A ∪ B ∪ C)`), the blockable-non-collider clause
--   of `def_3_17` (`IsSigmaOpenGiven`, second conjunct) at position
--   1 fires trivially.  The non-collider status (i.e.\ this lemma's
--   conclusion) is needed to *invoke* that clause.
--
-- *Why a separate Walk-level wrapper rather than reading off the
--   classification's third conjunct directly.*  The classification
--   conjunct is the propositional content
--   `¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource)`, which is the inserted-`u`
--   non-collider expressed at the *WalkStep arithmetic* level.
--   `IsNonCollider` is a Walk-level predicate that additionally
--   demands `1 ≤ length` (which holds tautologically for a
--   cons-of-cons walk of length `tail.length + 2`).  This wrapper
--   bundles the trivial length bound with the classification's
--   non-collider conjunct so Subtask 6 can pass the `IsNonCollider`
--   witness to `def_3_17`-style consumers without re-deriving the
--   length bound at every call site.
--
-- *Position 1, not generic position `k`.*  An inserted-`u` from a
--   marginalized cons-cell at "outer" position `k` of the
--   marginalized walk `p` ends up at *some* position of the lifted
--   walk `q` — typically `k + (number of 2-edge lifts in p[:k])`.
--   The exact position depends on the prefix's lift pattern, which
--   Subtask 6 tracks in its own recursion.  At each recursion
--   step, the inserted-`u` is *locally* at position 1 of the
--   `Walk.cons u s₁ (Walk.cons w s₂ tail)` sub-walk being built;
--   Subtask 6 then shifts to the global position via
--   `Walk.IsCollider`'s recursive clause
--   (`.cons _ _ (p@(.cons _ _ _)), k + 2 => p.IsCollider (k + 1)`,
--   `def_3_15` line 592).  So this helper's position-1 statement
--   is the right local primitive; Subtask 6's induction handles
--   the position shift.
private lemma walk_two_edge_inserted_u_is_non_collider
    {G : CDMG Node} {v u w x : Node}
    (s₁ : WalkStep G v u) (s₂ : WalkStep G u w) (tail : Walk G w x)
    (h_arrow : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource)) :
    (Walk.cons u s₁ (Walk.cons w s₂ tail)).IsNonCollider 1 := by
  refine ⟨?_, ?_⟩
  · -- `1 ≤ length`: the outer walk has length `tail.length + 2 ≥ 2 ≥ 1`.
    --   `(cons u s₁ (cons w s₂ tail)).length` reduces by two `cons`
    --   unfoldings to `tail.length + 2`.
    simp [Walk.length]
  · -- `¬ IsCollider 1`: by the fourth clause of `IsCollider`'s
    --   pattern-match (`.cons _ s₀ (.cons _ s₁ _), 1`), this reduces
    --   to `¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource)`, exactly `h_arrow`.
    exact h_arrow

-- ## ref: claim_3_25 (Subtask 6 helper) — `(v, u) ∈ G.E` lifts to
-- `u ∈ G.Desc v` via the trivial length-1 directed walk.
--
-- Inlined here (rather than imported from `LabelRoman.lean`) to avoid
-- adding a heavy import (`LabelRoman` pulls in σ-open paths + walk
-- replacement infrastructure) at this row's site.  Body is a 3-line
-- term that constructs the `Walk.cons v (.forwardE h) (Walk.nil v _)`
-- witness with `IsDirectedWalk = True` (by `Walk.nil`).
private lemma Desc.of_edge {G : CDMG Node} {v u : Node}
    (h : (v, u) ∈ G.E) : u ∈ G.Desc v := by
  have hu_V : u ∈ G.V := (G.hE_subset h).2
  have hu_G : u ∈ G := Finset.mem_union_right _ hu_V
  exact ⟨hu_G, Walk.cons u (.forwardE h) (Walk.nil u hu_G), trivial⟩

-- ## ref: claim_3_25 (Subtask 6 helper) — `(v, u) ∈ G.E` lifts to
-- `v ∈ G.Anc u` via the trivial length-1 directed walk.
--
-- Sister of `Desc.of_edge` above.  The same length-1 directed walk
-- `Walk G v u` witnesses both `u ∈ Desc v` and `v ∈ Anc u`; the
-- difference is only the side of `G.Anc` / `G.Desc` whose
-- existential the walk discharges.
private lemma Anc.of_edge {G : CDMG Node} {v u : Node}
    (h : (v, u) ∈ G.E) : v ∈ G.Anc u := by
  have hv_G : v ∈ G := (G.hE_subset h).1
  have hu_V : u ∈ G.V := (G.hE_subset h).2
  have hu_G : u ∈ G := Finset.mem_union_right _ hu_V
  exact ⟨hv_G, Walk.cons u (.forwardE h) (Walk.nil u hu_G), trivial⟩

-- ## ref: claim_3_25 (Subtask 6 helper) — `Anc` transitivity via
-- directed-walk composition.
--
-- Local inline copy of `LabelRoman.lean:184`'s
-- `mem_Anc_trans` so that this file does not need to import
-- `LabelRoman.lean` (which would add Section 3.3's σ-open-paths /
-- walk-replacement transitive dependencies).  The body is the
-- 3-line `Walk.comp` + `Walk.isDirectedWalk_comp` composition; the
-- composition idiom is the same as Section 3.2's
-- `MargPreservesAncestors.lean:145, 168`.
private lemma Anc.trans {G : CDMG Node} {u v w : Node}
    (huv : u ∈ G.Anc v) (hvw : v ∈ G.Anc w) : u ∈ G.Anc w := by
  obtain ⟨huG, p_uv, hp_uv⟩ := huv
  obtain ⟨_hvG, p_vw, hp_vw⟩ := hvw
  exact ⟨huG, p_uv.comp p_vw, Walk.isDirectedWalk_comp _ _ hp_uv hp_vw⟩

-- ## ref: claim_3_25 (Subtask 6 helper) — the LN's case (b)
-- substantive deduction: a forward-fork pass-through `b → u → w` with
-- `w ∈ Sc^G(b)` forces `u ∈ Sc^G(b)`.
--
-- Tex Step 3, joint treatment of (ii)/(iii), case (b) (tex line 202).
-- Packages the LN's "directed cycle through `u`" argument: from
-- `b → u ∈ G.E`, `u → w ∈ G.E`, and `w ∈ Sc^G(b) ⊆ Anc^G(b)`, chain
-- the directed walk `u → w → ... → b` to get `u ∈ Anc^G(b)`, and
-- chain the single edge `b → u` to get `u ∈ Desc^G(b)`.  Both
-- together give `u ∈ Sc^G(b) = Anc^G(b) ∩ Desc^G(b)`.
--
-- ## Design choice — Sc.of_directed_pass_through
--
-- *Asymmetric signature `b → u → w` (forward + forward).*  The LN's
--   case (b) covers two-edge lifts where the first step out of `b`
--   is `b → u` (directed-forward).  The second step `u ⊸ w` can be
--   either directed-forward (`u → w ∈ G.E`) or bidirected
--   (`s(u, w) ∈ G.L`).  This helper specialises to the
--   doubly-forward sub-case, where we can construct
--   `u ∈ Anc^G w` from the directed edge `u → w`.
--
-- *The bidir-second sub-case is excluded at the LN's source.*  When
--   the second step is bidirected (`s(u, w) ∈ G.L`), the outgoing
--   edge of `π` at `b` is the bidir edge itself, NOT a `b → u`
--   directed edge; the two-edge sub-case for an unblockable non-
--   collider's outgoing direction therefore does not arise.  See
--   tex line 202, final clause ("For the fork/hinge bifurcation
--   cases producing a bidirected lift `b_j ↔ b_{j±1}` in `L^{∖u}`,
--   the outgoing edge of `π` at `b_j` is the bidirected edge itself
--   ... so this sub-case does not arise").  Subtask 6's σ-openness
--   verification handles the elimination at the
--   walkstep-classification site; no bidir-second variant of this
--   helper is needed.
private lemma Sc.of_directed_pass_through {G : CDMG Node} {b u w : Node}
    (h_bu : (b, u) ∈ G.E) (h_uw : (u, w) ∈ G.E)
    (h_w_Sc_b : w ∈ G.Sc b) : u ∈ G.Sc b := by
  refine ⟨?_, Desc.of_edge h_bu⟩
  -- `u ∈ G.Anc b`: chain `u → w` (gives `u ∈ Anc w`) with
  -- `w ∈ G.Anc b` (from `w ∈ G.Sc b`) via `Anc.trans`.
  exact Anc.trans (Anc.of_edge h_uw) h_w_Sc_b.1

-- ## ref: claim_3_25 (Subtask 6c) — σ-open weakened to skip position-0
-- blockable check.
--
-- The σ-openness lift `sigma_open_lift_marg_one` (Subtask 6c) recurses
-- on the marg-walk `p'` cons-cell by cons-cell, but at each cons-cell
-- `p' = cons mid s p''` the σ-openness of `p'` does NOT imply the
-- σ-openness of the tail walk `p''`: position 0 of `p''` (vertex `mid`)
-- is automatically a blockable non-collider via the `k = 0` disjunct of
-- `def_3_16`'s `IsBlockableNonCollider`, demanding `mid ∉ C`, but
-- `mid ∈ C` is admissible when `mid` is an unblockable non-collider on
-- `p'` (handled by the LN's case (b) deduction at tex line 202).
--
-- To sidestep this, we weaken the σ-open predicate by dropping the
-- position-0 blockable check.  `IsSigmaOpenAtInterior p C hC` agrees
-- with `IsSigmaOpenGiven p C hC` at every position except `k = 0`,
-- where the blockable clause is dropped.  The full σ-open hypothesis
-- on `p'` is unfolded to interior-σ-open + position-0 vertex ∉ C, and
-- after the lift the output's interior-σ-open + (still) source ∉ C
-- reassembles to full σ-open on `p`.
--
-- ## Design choice — IsSigmaOpenAtInterior
--
-- *Private helper, scoped to this file.*  Consumed only by the
--   σ-openness preservation proof below for the LN's Step 3.
--   Downstream consumers want the full `IsSigmaOpenGiven`.
--
-- *`1 ≤ k` restriction on the blockable clause.*  The blockable
--   clause is dropped at `k = 0` only.  All other positions retain
--   the full clause.  The collider clause is unchanged (it is
--   vacuously True at `k = 0` anyway, since `IsCollider 0` is `False`
--   by the def's `cons _ _ (cons _ _ _), 0 ↦ False` and `nil`, `cons
--   _ _ (nil _ _)` clauses).
set_option linter.unusedVariables false in
private def IsSigmaOpenAtInterior {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V) : Prop :=
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk → p.IsCollider k →
      vk ∈ G.AncSet C) ∧
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk →
      p.IsBlockableNonCollider k → 1 ≤ k → vk ∉ C)

-- ## ref: claim_3_25 (Subtask 6c helper) — vertices-at-0 lookup.
--
-- Inline of `Walk.vertices_zero_eq_source` from
-- `Section3_3/LabelRoman.lean:1534` (not imported here).  Stated and
-- proved in 3 lines via the two `Walk` constructors' `vertices`
-- definitions reducing definitionally.
private lemma Walk.vertices_zero_eq_source' {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices[0]? = some u
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ => rfl

-- ## ref: claim_3_25 (Subtask 6c helper) — full σ-open ⟹ interior σ-open.
--
-- The forward weakening is immediate: drop the position-0 blockable
-- clause (which the interior predicate doesn't require).  Used at the
-- top of `sigma_open_lift_marg_one` to feed the recursive lift.
private lemma sigma_open_to_interior
    {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (C : Set Node) (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hp : p.IsSigmaOpenGiven C hC) :
    IsSigmaOpenAtInterior p C hC :=
  ⟨hp.1, fun k vk hk h_blk _ => hp.2 k vk hk h_blk⟩

-- ## ref: claim_3_25 (Subtask 6c helper) — IsCollider equation lemmas.
--
-- Local inline of the `Walk.isCollider_nil_false` / `_cons_nil_false`
-- pattern from `SigmaOpenPathsWalks.lean:504` (not imported here).
-- These small computational facts are needed to discharge the vacuous
-- `IsCollider 0` and `IsCollider _` on `.nil` / `.cons _ _ .nil` cases
-- in the σ-open' inheritance proof below.
private lemma isCollider_nil_eq_false {G : CDMG Node} {v : Node}
    (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv : Walk G v v).IsCollider k = False := by
  cases k <;> rfl

private lemma isCollider_cons_zero_eq_false {G : CDMG Node}
    {u mid v : Node} (s : WalkStep G u mid) (p : Walk G mid v) :
    (Walk.cons mid s p : Walk G u v).IsCollider 0 = False := by
  cases p <;> rfl

private lemma hasBlockingLeftSlot_nil_eq_false {G : CDMG Node} {v : Node}
    (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv : Walk G v v).HasBlockingLeftSlot k = False := by
  cases k <;> rfl

-- ## ref: claim_3_25 (Subtask 6c helper) — cons walk interior σ-open ⟹
-- tail interior σ-open (position-shift inheritance).
--
-- For `outer = cons mid s tail`, every σ-open clause at position
-- `k ≥ 1` of `tail` corresponds to a σ-open clause at position `k + 1`
-- of `outer` (via the `(_ :: vs)[k+1]? = vs[k]?` definitional reduction
-- on `vertices`, and the `cons _ _ (p@(cons _ _ _)), k + 2 ↦ p.IsCollider
-- (k + 1)` recursion case of `IsCollider` (and the analogous recursion
-- cases of `HasBlockingLeftSlot`, `HasBlockingRightSlot`)).  The
-- interior predicate's `1 ≤ k` restriction on the blockable clause
-- exactly accommodates the position-0 of `tail` mismatch (vertex
-- `mid`, which may be in `C` if mid is unblockable on `outer`).
private lemma sigma_open_interior_cons_tail
    {G : CDMG Node} {u w : Node} {mid : Node}
    (s : WalkStep G u mid) (tail : Walk G mid w)
    (C : Set Node) (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (h_outer : IsSigmaOpenAtInterior (Walk.cons mid s tail) C hC) :
    IsSigmaOpenAtInterior tail C hC := by
  obtain ⟨h_outer_coll, h_outer_blk⟩ := h_outer
  refine ⟨?_, ?_⟩
  · -- Collider clause for `tail`.
    intro k vk hk_tail h_coll_tail
    -- Use `cases tail` (without `h :`) so substitution propagates into the goal.
    cases tail with
    | nil v hv =>
        rw [isCollider_nil_eq_false hv] at h_coll_tail
        exact h_coll_tail.elim
    | cons mid' s' tail_inner =>
        cases k with
        | zero =>
            rw [isCollider_cons_zero_eq_false s' tail_inner] at h_coll_tail
            exact h_coll_tail.elim
        | succ n =>
            apply h_outer_coll (n + 2) vk
            · -- vertices indexing.
              exact hk_tail
            · -- Substantive case: outer.IsCollider (n + 2) reduces via
              -- `cons _ _ (p@(cons _ _ _)), k + 2 ↦ p.IsCollider (k + 1)` to
              -- tail.IsCollider (n + 1) = h_coll_tail.
              -- Destructure `s` so Lean's matcher can route to the catch-all.
              cases s <;> exact h_coll_tail
  · -- Blockable clause (for k ≥ 1).
    intro k vk hk_tail h_blk_tail h_k_pos
    refine h_outer_blk (k + 1) vk ?_ ?_ ?_
    · exact hk_tail
    · -- Blockable transport.
      obtain ⟨h_nc_tail, h_disj_tail⟩ := h_blk_tail
      refine ⟨?_, ?_⟩
      · -- IsNonCollider (k + 1) on outer.
        refine ⟨?_, ?_⟩
        · -- k + 1 ≤ outer.length = tail.length + 1
          have : k ≤ tail.length := h_nc_tail.1
          show k + 1 ≤ tail.length + 1
          omega
        · -- ¬ outer.IsCollider (k + 1) ← ¬ tail.IsCollider k
          intro h_coll_outer
          apply h_nc_tail.2
          -- Symmetric transport.
          cases tail with
          | nil v hv =>
              -- outer = cons _ s (nil _ _) at index ≥ 1: IsCollider = False.
              -- The cases `cons _ _ (nil _ _), _ ↦ False` fires regardless of `s`.
              revert h_coll_outer
              cases s <;> intro h <;> exact h.elim
          | cons mid' s' tail_inner =>
              cases k with
              | zero => exact absurd h_k_pos (by omega)
              | succ n =>
                  -- outer.IsCollider (n + 2) reduces to tail.IsCollider (n + 1).
                  revert h_coll_outer
                  cases s <;> exact id
      · -- Disjunction transport.
        rcases h_disj_tail with hzero | hlen | hHBLS | hHBRS
        · exfalso; omega
        · -- k = tail.length → k + 1 = outer.length = tail.length + 1.
          right; left
          show k + 1 = tail.length + 1
          omega
        · -- HBLS k on tail → HBLS (k + 1) on outer.
          right; right; left
          cases tail with
          | nil v hv =>
              rw [hasBlockingLeftSlot_nil_eq_false hv] at hHBLS
              exact hHBLS.elim
          | cons mid' s' tail_inner =>
              cases k with
              | zero => exact absurd h_k_pos (by omega)
              | succ n =>
                  -- outer.HBLS (n + 2) = tail.HBLS (n + 1) = hHBLS.
                  cases s <;> exact hHBLS
        · -- HBRS k on tail → HBRS (k + 1) on outer.
          right; right; right
          -- outer.HBRS (k + 1) = tail.HBRS k via the `cons _ _ p, k + 1` case.
          cases s <;> exact hHBRS
    · -- 1 ≤ k + 1 (trivial).
      omega

-- ## ref: claim_3_25 (Subtask 7b) — inverse WalkStep classification.
--
-- The reverse direction of `walkstep_marginalize_one_classification`
-- (line 1342): given a G-edge (or a non-collider 2-edge pair through
-- `u` with `a, mid ≠ u`), produce the corresponding marg-edge
-- `WalkStep (G.marginalize {u} hu) a mid` with matching arrowhead
-- profile.  Two lemmas:
--
--   * `walkstep_lift_one_edge` (1-edge case): lifts a single
--     `WalkStep G a mid` (with `a, mid ≠ u`) to a single
--     `WalkStep marg a mid` via the direct-inclusion clause of
--     `def_3_14`'s `E^{∖u}` (length-1 directed walk through `{u}`
--     with empty interior, items~iii) and `L^{∖u}` (length-1
--     bidirected bifurcation through `{u}` with empty interior,
--     items~iv).
--
--   * `walkstep_lift_two_edge` (2-edge case): lifts a non-collider
--     2-edge G-pair `(s₁ : WalkStep G a u, s₂ : WalkStep G u mid)`
--     (with `a, mid ≠ u`) to a single `WalkStep marg a mid`.  The
--     5 substantive (non-collider) constructor patterns dispatch to
--     two output families:
--
--     - **Directed pass-through** ((forwardE, forwardE) and
--       (backwardE, backwardE)) → `.forwardE` / `.backwardE` in
--       marg via a 2-edge Φ_E directed walk through `{u}`.
--
--     - **Bifurcation** ((backwardE, forwardE) — fork;
--       (bidir, forwardE) — left hinge; (backwardE, bidir) — right
--       hinge) → `.bidir` in marg via a 2-edge Φ_L bifurcation
--       walk through `{u}`.
--
--     The 4 collider patterns ((forwardE, backwardE),
--     (forwardE, bidir), (bidir, backwardE), (bidir, bidir)) are
--     all dispatched by `hNonColl` (each yields
--     `s₁.HeadAtTarget = True ∧ s₂.HeadAtSource = True`).
--
-- Subtask 7c consumes these to mirror `exists_isLift_of_walk_marg`
-- (line 1819) via the `IsLift` constructors below.
--
-- ## Design choice — `hne : a ≠ mid` hypothesis on
-- `walkstep_lift_two_edge`
--
-- *Why this hypothesis is necessary.*  The 3 bifurcation cases
-- output a `.bidir` in marg, which requires `s(a, mid) ∈ marg.L` —
-- and marg.L's filter carries an `e.1 ≠ e.2` conjunct (inherited
-- from `def_3_14`'s `L^{∖u}` definition).  Hence the marg-bidir
-- self-loop case (`a = mid`) is structurally excluded.  For those
-- 3 patterns with `a = mid`, the only G-edges supplied by the
-- hypotheses are insufficient to construct a Φ_E witness either
-- (each provides at most one of `(a, u), (u, a) ∈ G.E`; a closed
-- directed walk `a → u → a` requires both).  So `a = mid` admits
-- no marg-edge witness at all in those 3 cases, forcing the `hne`
-- hypothesis.  The 2 directed-pass-through patterns
-- ((forwardE, forwardE), (backwardE, backwardE)) do admit a self-
-- loop witness `(a, a) ∈ marg.E` when `a = mid`, but a uniform
-- `hne` simplifies 7c's interface; Subtask 7c handles the
-- `a = mid` u-side-trip case separately (by eliding the segment
-- in the marg-walk rather than producing a marg-edge).
--
-- *Deviation from the original brief.*  The 7b worker brief did
-- not include the `hne` hypothesis.  Worker analysis revealed that
-- the brief's signature is propositionally false in the 3 bidir-
-- output cases with `a = mid` (no marg-edge witness exists), so
-- adding `hne` is necessary for the lemma to be true at all.

private lemma walkstep_lift_one_edge {G : CDMG Node} (u : Node)
    (hu : ({u} : Finset Node) ⊆ G.V) {a mid : Node}
    (ha : a ≠ u) (hmid : mid ≠ u)
    (s' : WalkStep G a mid) :
    ∃ (s : WalkStep (G.marginalize {u} hu) a mid),
      (s.HeadAtSource ↔ s'.HeadAtSource) ∧
      (s.HeadAtTarget ↔ s'.HeadAtTarget) := by
  cases s' with
  | forwardE h_E =>
      -- 1-edge directed: `(a, mid) ∈ G.E` (already in `E^{∖u}` by
      -- the direct-inclusion clause of `def_3_14`'s `E^{∖u}` via a
      -- length-1 Φ_E witness with empty interior).
      have h_a_GJV : a ∈ G.J ∪ G.V := (G.hE_subset h_E).1
      have h_mid_GV : mid ∈ G.V := (G.hE_subset h_E).2
      have h_mid_marg : mid ∈ G.V \ ({u} : Finset Node) := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨h_mid_GV, hmid⟩
      have h_a_carrier : a ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := by
        rcases Finset.mem_union.mp h_a_GJV with hJ | hV
        · exact Finset.mem_union_left _ hJ
        · refine Finset.mem_union_right _ ?_
          rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hV, ha⟩
      have h_mid_G : mid ∈ G := Finset.mem_union_right _ h_mid_GV
      have h_marg_E : (a, mid) ∈ (G.marginalize {u} hu).E := by
        change (a, mid) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                (G.V \ ({u} : Finset Node))).filter
              (fun e => G.MarginalizationΦE {u} e.1 e.2)
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h_a_carrier, h_mid_marg⟩, ?_⟩
        refine ⟨Walk.cons mid (.forwardE h_E) (.nil mid h_mid_G), ?_, ?_, ?_⟩
        · exact True.intro
        · rfl
        · intro x hx
          exact absurd hx (by simp [Walk.vertices, List.tail])
      exact ⟨.forwardE h_marg_E, Iff.rfl, Iff.rfl⟩
  | backwardE h_E =>
      -- 1-edge backward: `(mid, a) ∈ G.E` (already in `E^{∖u}`).
      have h_mid_GJV : mid ∈ G.J ∪ G.V := (G.hE_subset h_E).1
      have h_a_GV : a ∈ G.V := (G.hE_subset h_E).2
      have h_a_marg : a ∈ G.V \ ({u} : Finset Node) := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨h_a_GV, ha⟩
      have h_mid_carrier : mid ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := by
        rcases Finset.mem_union.mp h_mid_GJV with hJ | hV
        · exact Finset.mem_union_left _ hJ
        · refine Finset.mem_union_right _ ?_
          rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hV, hmid⟩
      have h_a_G : a ∈ G := Finset.mem_union_right _ h_a_GV
      have h_marg_E : (mid, a) ∈ (G.marginalize {u} hu).E := by
        change (mid, a) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                (G.V \ ({u} : Finset Node))).filter
              (fun e => G.MarginalizationΦE {u} e.1 e.2)
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h_mid_carrier, h_a_marg⟩, ?_⟩
        refine ⟨Walk.cons a (.forwardE h_E) (.nil a h_a_G), ?_, ?_, ?_⟩
        · exact True.intro
        · rfl
        · intro x hx
          exact absurd hx (by simp [Walk.vertices, List.tail])
      exact ⟨.backwardE h_marg_E, Iff.rfl, Iff.rfl⟩
  | bidir h_L =>
      -- 1-edge bidirected: `s(a, mid) ∈ G.L` (already in `L^{∖u}`
      -- by the direct-inclusion clause via marginalize_L_iff with a
      -- length-1 Φ_L bidirected bifurcation witness, empty interior).
      have h_a_GV : a ∈ G.V := G.hL_subset h_L (Sym2.mem_mk_left a mid)
      have h_mid_GV : mid ∈ G.V :=
        G.hL_subset h_L (Sym2.mem_mk_right a mid)
      have h_a_marg : a ∈ G.V \ ({u} : Finset Node) := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨h_a_GV, ha⟩
      have h_mid_marg : mid ∈ G.V \ ({u} : Finset Node) := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨h_mid_GV, hmid⟩
      have h_ne : a ≠ mid := fun h_eq =>
        G.hL_irrefl h_L (Sym2.mk_isDiag_iff.mpr h_eq)
      have h_mid_G : mid ∈ G := Finset.mem_union_right _ h_mid_GV
      have h_marg_L : s(a, mid) ∈ (G.marginalize {u} hu).L := by
        rw [marginalize_L_iff]
        refine ⟨(a, mid), h_a_marg, h_mid_marg, h_ne, ?_, rfl⟩
        left
        refine ⟨Walk.cons mid (.bidir h_L) (.nil mid h_mid_G), ?_, ?_⟩
        · -- IsBifurcation: a ≠ mid, a ∉ tail = [mid], mid ∉ dropLast
          --   = [a], ∃ split k = 0.
          refine ⟨h_ne, ?_, ?_, 0, ?_⟩
          · intro hmem
            have h_eq : a = mid := by
              simpa only [Walk.vertices, List.tail_cons, List.mem_singleton]
                using hmem
            exact h_ne h_eq
          · intro hmem
            have h_eq : mid = a := by
              simpa only [Walk.vertices, List.dropLast_cons_of_ne_nil,
                List.dropLast, List.mem_singleton] using hmem
            exact h_ne.symm h_eq
          · exact True.intro
        · intro x hx
          exact absurd hx (by simp [Walk.vertices, List.tail])
      exact ⟨.bidir h_marg_L, Iff.rfl, Iff.rfl⟩

private lemma walkstep_lift_two_edge {G : CDMG Node} (u : Node)
    (hu : ({u} : Finset Node) ⊆ G.V) {a mid : Node}
    (ha : a ≠ u) (hmid : mid ≠ u) (hne : a ≠ mid)
    (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid)
    (hNonColl : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource)) :
    ∃ (s : WalkStep (G.marginalize {u} hu) a mid),
      (s.HeadAtSource ↔ s₁.HeadAtSource) ∧
      (s.HeadAtTarget ↔ s₂.HeadAtTarget) := by
  cases s₁ with
  | forwardE h₁ =>
      -- h₁ : (a, u) ∈ G.E. s₁.HeadAtTarget = True (forwardE).
      cases s₂ with
      | forwardE h₂ =>
          -- (forwardE, forwardE): directed pass-through a → u → mid.
          -- Marg-edge: (a, mid) ∈ marg.E via 2-edge Φ_E witness a → u → mid.
          have h_a_GJV : a ∈ G.J ∪ G.V := (G.hE_subset h₁).1
          have h_mid_GV : mid ∈ G.V := (G.hE_subset h₂).2
          have h_mid_G : mid ∈ G := Finset.mem_union_right _ h_mid_GV
          have h_mid_marg : mid ∈ G.V \ ({u} : Finset Node) := by
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨h_mid_GV, hmid⟩
          have h_a_carrier : a ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := by
            rcases Finset.mem_union.mp h_a_GJV with hJ | hV
            · exact Finset.mem_union_left _ hJ
            · refine Finset.mem_union_right _ ?_
              rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hV, ha⟩
          have h_marg_E : (a, mid) ∈ (G.marginalize {u} hu).E := by
            change (a, mid) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                    (G.V \ ({u} : Finset Node))).filter
                  (fun e => G.MarginalizationΦE {u} e.1 e.2)
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨h_a_carrier, h_mid_marg⟩, ?_⟩
            refine ⟨Walk.cons u (.forwardE h₁)
                      (Walk.cons mid (.forwardE h₂) (.nil mid h_mid_G)),
                    ?_, ?_, ?_⟩
            · exact True.intro
            · exact Nat.le_add_left 1 1
            · intro x hx
              have h_eq : x = u := by
                simpa only [Walk.vertices, List.tail_cons,
                  List.dropLast_cons_of_ne_nil, List.dropLast,
                  List.mem_singleton] using hx
              exact Finset.mem_singleton.mpr h_eq
          exact ⟨.forwardE h_marg_E, Iff.rfl, Iff.rfl⟩
      | backwardE _ =>
          -- (forwardE, backwardE): collider at u
          -- (s₁.HeadAtTarget = T, s₂.HeadAtSource = T).
          exact (hNonColl ⟨trivial, trivial⟩).elim
      | bidir _ =>
          -- (forwardE, bidir): collider at u.
          exact (hNonColl ⟨trivial, trivial⟩).elim
  | backwardE h₁ =>
      -- h₁ : (u, a) ∈ G.E. s₁.HeadAtTarget = False (backwardE).
      have h_a_GV : a ∈ G.V := (G.hE_subset h₁).2
      have h_a_marg : a ∈ G.V \ ({u} : Finset Node) := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨h_a_GV, ha⟩
      have h_a_G : a ∈ G := Finset.mem_union_right _ h_a_GV
      cases s₂ with
      | forwardE h₂ =>
          -- (backwardE, forwardE): fork a ← u → mid.
          -- Marg-edge: s(a, mid) ∈ marg.L via 2-edge Φ_L bifurcation
          -- walk a → u → mid with .backwardE then .forwardE.
          have h_mid_GV : mid ∈ G.V := (G.hE_subset h₂).2
          have h_mid_G : mid ∈ G := Finset.mem_union_right _ h_mid_GV
          have h_mid_marg : mid ∈ G.V \ ({u} : Finset Node) := by
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨h_mid_GV, hmid⟩
          have h_marg_L : s(a, mid) ∈ (G.marginalize {u} hu).L := by
            rw [marginalize_L_iff]
            refine ⟨(a, mid), h_a_marg, h_mid_marg, hne, ?_, rfl⟩
            left
            refine ⟨Walk.cons u (.backwardE h₁)
                      (Walk.cons mid (.forwardE h₂) (.nil mid h_mid_G)),
                    ?_, ?_⟩
            · -- IsBifurcation
              refine ⟨hne, ?_, ?_, 0, ?_⟩
              · intro hmem
                -- hmem : a ∈ <walk>.vertices.tail
                -- <walk>.vertices reduces to [a, u, mid]; .tail to [u, mid].
                have h_in : a ∈ (u :: ([mid] : List Node)) := hmem
                rcases List.mem_cons.mp h_in with hau | hamid_in
                · exact ha hau
                · exact hne (List.mem_singleton.mp hamid_in)
              · intro hmem
                -- hmem : mid ∈ <walk>.vertices.dropLast
                -- .vertices reduces to [a, u, mid]; .dropLast to [a, u].
                have h_in : mid ∈ (a :: ([u] : List Node)) := hmem
                rcases List.mem_cons.mp h_in with hma | hmu_in
                · exact hne.symm hma
                · exact hmid (List.mem_singleton.mp hmu_in)
              · -- IsBifurcationWithSplit 0 reduces to inner walk's
                --   IsDirectedWalk via `.cons _ (.backwardE _) (p@cons _ _ _),
                --   0 ↦ p.IsDirectedWalk`; inner walk's IsDirectedWalk = True
                --   via two further reductions.
                exact True.intro
            · intro x hx
              have h_eq : x = u := by
                simpa only [Walk.vertices, List.tail_cons,
                  List.dropLast_cons_of_ne_nil, List.dropLast,
                  List.mem_singleton] using hx
              exact Finset.mem_singleton.mpr h_eq
          exact ⟨.bidir h_marg_L, Iff.rfl, Iff.rfl⟩
      | backwardE h₂ =>
          -- (backwardE, backwardE): reverse directed pass-through
          --   `a ← u ← mid` with G-edges (u, a), (mid, u).
          -- Marg-edge: (mid, a) ∈ marg.E via 2-edge Φ_E witness
          --   mid → u → a (using .forwardE h₂ then .forwardE h₁).
          have h_mid_GJV : mid ∈ G.J ∪ G.V := (G.hE_subset h₂).1
          have h_mid_carrier : mid ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := by
            rcases Finset.mem_union.mp h_mid_GJV with hJ | hV
            · exact Finset.mem_union_left _ hJ
            · refine Finset.mem_union_right _ ?_
              rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hV, hmid⟩
          have h_marg_E : (mid, a) ∈ (G.marginalize {u} hu).E := by
            change (mid, a) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                    (G.V \ ({u} : Finset Node))).filter
                  (fun e => G.MarginalizationΦE {u} e.1 e.2)
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨h_mid_carrier, h_a_marg⟩, ?_⟩
            refine ⟨Walk.cons u (.forwardE h₂)
                      (Walk.cons a (.forwardE h₁) (.nil a h_a_G)),
                    ?_, ?_, ?_⟩
            · exact True.intro
            · exact Nat.le_add_left 1 1
            · intro x hx
              have h_eq : x = u := by
                simpa only [Walk.vertices, List.tail_cons,
                  List.dropLast_cons_of_ne_nil, List.dropLast,
                  List.mem_singleton] using hx
              exact Finset.mem_singleton.mpr h_eq
          exact ⟨.backwardE h_marg_E, Iff.rfl, Iff.rfl⟩
      | bidir h₂ =>
          -- (backwardE, bidir): right hinge `a ← u ↔ mid`.
          -- Marg-edge: s(a, mid) ∈ marg.L via 2-edge Φ_L bifurcation walk
          -- a ← u ↔ mid with .backwardE then .bidir.
          have h_mid_GV : mid ∈ G.V :=
            G.hL_subset h₂ (Sym2.mem_mk_right u mid)
          have h_mid_G : mid ∈ G := Finset.mem_union_right _ h_mid_GV
          have h_mid_marg : mid ∈ G.V \ ({u} : Finset Node) := by
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨h_mid_GV, hmid⟩
          have h_marg_L : s(a, mid) ∈ (G.marginalize {u} hu).L := by
            rw [marginalize_L_iff]
            refine ⟨(a, mid), h_a_marg, h_mid_marg, hne, ?_, rfl⟩
            left
            refine ⟨Walk.cons u (.backwardE h₁)
                      (Walk.cons mid (.bidir h₂) (.nil mid h_mid_G)),
                    ?_, ?_⟩
            · -- IsBifurcation: use split k = 1 (the .backwardE then
              --   .bidir pattern: outer reduces to inner.IsBifurcationWithSplit
              --   0, which matches `.cons _ (.bidir _) (.nil _ _), 0 ↦ True`).
              refine ⟨hne, ?_, ?_, 1, ?_⟩
              · intro hmem
                -- hmem : a ∈ <walk>.vertices.tail
                -- <walk>.vertices reduces to [a, u, mid]; .tail to [u, mid].
                have h_in : a ∈ (u :: ([mid] : List Node)) := hmem
                rcases List.mem_cons.mp h_in with hau | hamid_in
                · exact ha hau
                · exact hne (List.mem_singleton.mp hamid_in)
              · intro hmem
                -- hmem : mid ∈ <walk>.vertices.dropLast
                -- .vertices reduces to [a, u, mid]; .dropLast to [a, u].
                have h_in : mid ∈ (a :: ([u] : List Node)) := hmem
                rcases List.mem_cons.mp h_in with hma | hmu_in
                · exact hne.symm hma
                · exact hmid (List.mem_singleton.mp hmu_in)
              · exact True.intro
            · intro x hx
              have h_eq : x = u := by
                simpa only [Walk.vertices, List.tail_cons,
                  List.dropLast_cons_of_ne_nil, List.dropLast,
                  List.mem_singleton] using hx
              exact Finset.mem_singleton.mpr h_eq
          exact ⟨.bidir h_marg_L, Iff.rfl, Iff.rfl⟩
  | bidir h₁ =>
      -- h₁ : s(a, u) ∈ G.L. s₁.HeadAtTarget = True (bidir).
      have h_a_GV : a ∈ G.V := G.hL_subset h₁ (Sym2.mem_mk_left a u)
      have h_a_marg : a ∈ G.V \ ({u} : Finset Node) := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨h_a_GV, ha⟩
      cases s₂ with
      | forwardE h₂ =>
          -- (bidir, forwardE): left hinge `a ↔ u → mid`.
          -- Marg-edge: s(a, mid) ∈ marg.L via 2-edge Φ_L bifurcation walk
          -- a ↔ u → mid with .bidir then .forwardE.
          have h_mid_GV : mid ∈ G.V := (G.hE_subset h₂).2
          have h_mid_G : mid ∈ G := Finset.mem_union_right _ h_mid_GV
          have h_mid_marg : mid ∈ G.V \ ({u} : Finset Node) := by
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨h_mid_GV, hmid⟩
          have h_marg_L : s(a, mid) ∈ (G.marginalize {u} hu).L := by
            rw [marginalize_L_iff]
            refine ⟨(a, mid), h_a_marg, h_mid_marg, hne, ?_, rfl⟩
            left
            refine ⟨Walk.cons u (.bidir h₁)
                      (Walk.cons mid (.forwardE h₂) (.nil mid h_mid_G)),
                    ?_, ?_⟩
            · -- IsBifurcation: split k = 0 matches `.cons _ (.bidir _)
              --   (p@(.cons _ _ _)), 0 ↦ p.IsDirectedWalk`; inner walk
              --   reduces to True.
              refine ⟨hne, ?_, ?_, 0, ?_⟩
              · intro hmem
                -- hmem : a ∈ <walk>.vertices.tail
                -- <walk>.vertices reduces to [a, u, mid]; .tail to [u, mid].
                have h_in : a ∈ (u :: ([mid] : List Node)) := hmem
                rcases List.mem_cons.mp h_in with hau | hamid_in
                · exact ha hau
                · exact hne (List.mem_singleton.mp hamid_in)
              · intro hmem
                -- hmem : mid ∈ <walk>.vertices.dropLast
                -- .vertices reduces to [a, u, mid]; .dropLast to [a, u].
                have h_in : mid ∈ (a :: ([u] : List Node)) := hmem
                rcases List.mem_cons.mp h_in with hma | hmu_in
                · exact hne.symm hma
                · exact hmid (List.mem_singleton.mp hmu_in)
              · exact True.intro
            · intro x hx
              have h_eq : x = u := by
                simpa only [Walk.vertices, List.tail_cons,
                  List.dropLast_cons_of_ne_nil, List.dropLast,
                  List.mem_singleton] using hx
              exact Finset.mem_singleton.mpr h_eq
          exact ⟨.bidir h_marg_L, Iff.rfl, Iff.rfl⟩
      | backwardE _ =>
          -- (bidir, backwardE): collider at u (s₁.HeadAtTarget = T,
          -- s₂.HeadAtSource = T).
          exact (hNonColl ⟨trivial, trivial⟩).elim
      | bidir _ =>
          -- (bidir, bidir): collider at u.
          exact (hNonColl ⟨trivial, trivial⟩).elim

-- ## ref: claim_3_25 (Subtask 6c) — `IsLift G u hu p' p` inductive predicate.
--
-- Tex Step 3 (tex lines 174-181): an inductive characterisation of when
-- a G-walk `p` is a *step-by-step lift* of a marg-walk `p'` through the
-- `walkstep_marginalize_one_classification` taxonomy.  Three constructors:
--   * `nil_lift`: the trivial walk lifts to the trivial walk.
--   * `cons_one_edge`: a 1-edge cons-cell of `p'` lifts to a 1-edge
--     cons-cell of `p` with the same source/target arrowhead pattern.
--   * `cons_two_edge`: a 1-edge cons-cell of `p'` lifts to a 2-edge
--     cons-cell of `p` with arrowhead correspondence at the non-`u`
--     boundary, plus the inserted-`u` non-collider conjunct.
--
-- The arrowhead-correspondence conjuncts (`hSrc`, `hTgt`) are the
-- per-step iff data carried by the classification lemma; the
-- inserted-`u` non-collider conjunct `hNonColl` is needed by the
-- σ-openness preservation argument's case analysis at the `u`-inserted
-- position of `p`.
--
-- ## Design choice — IsLift
--
-- *Inductive predicate, not a recursive function.*  A function returning
--   the lifted walk would require `Classical.choice` to extract from
--   `walkstep_marginalize_one_classification`'s existential, and would
--   trigger HEq friction at the σ-openness preservation site (which
--   needs to case-split on the lift's structure per cons-cell).  The
--   inductive predicate carries the same information via constructor
--   case-splits, which the σ-openness preservation proof recurses over
--   without HEq pitfalls.
--
-- *Three constructors mirror the classification's 2-way disjunction
--   plus the nil base case.*  Captures exactly the `(1-edge ∨ 2-edge)`
--   shape of `walkstep_marginalize_one_classification` at the
--   cons-cell, with the base case `nil_lift` for the walk endpoint.
private inductive IsLift (G : CDMG Node) (u : Node)
    (hu : ({u} : Finset Node) ⊆ G.V) :
    ∀ {a b : Node}, Walk (G.marginalize {u} hu) a b → Walk G a b → Prop
  | nil_lift {v : Node} (hv_marg : v ∈ G.marginalize {u} hu)
      (hv_G : v ∈ G) :
      IsLift G u hu (Walk.nil v hv_marg) (Walk.nil v hv_G)
  | cons_one_edge {a mid b : Node}
      (s : WalkStep (G.marginalize {u} hu) a mid)
      (p'' : Walk (G.marginalize {u} hu) mid b)
      (s' : WalkStep G a mid) (p_tail : Walk G mid b)
      (hSrc : s'.HeadAtSource ↔ s.HeadAtSource)
      (hTgt : s'.HeadAtTarget ↔ s.HeadAtTarget)
      (htail : IsLift G u hu p'' p_tail) :
      IsLift G u hu (Walk.cons mid s p'') (Walk.cons mid s' p_tail)
  | cons_two_edge {a mid b : Node}
      (s : WalkStep (G.marginalize {u} hu) a mid)
      (p'' : Walk (G.marginalize {u} hu) mid b)
      (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid)
      (p_tail : Walk G mid b)
      (hSrc : s₁.HeadAtSource ↔ s.HeadAtSource)
      (hTgt : s₂.HeadAtTarget ↔ s.HeadAtTarget)
      (hNonColl : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource))
      (htail : IsLift G u hu p'' p_tail) :
      IsLift G u hu (Walk.cons mid s p'')
        (Walk.cons u s₁ (Walk.cons mid s₂ p_tail))

-- ## ref: claim_3_25 (Subtask 6c) — existence of the lift.
--
-- Every marg-walk has a G-side lift in the `IsLift` sense, constructed
-- by structural recursion on `p'`: at each cons-cell, apply
-- `walkstep_marginalize_one_classification` (line 1341) to the head
-- step, then recurse on the tail.
private lemma exists_isLift_of_walk_marg
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V) :
    ∀ {a b : Node} (p' : Walk (G.marginalize {u} hu) a b),
      ∃ p : Walk G a b, IsLift G u hu p' p := by
  intro a b p'
  induction p' with
  | nil v hv_marg =>
      refine ⟨Walk.nil v (mem_of_mem_marginalize hv_marg), ?_⟩
      exact IsLift.nil_lift hv_marg _
  | @cons _ _ mid s p'' ih =>
      obtain ⟨p_tail, htail⟩ := ih
      rcases walkstep_marginalize_one_classification G u hu s with
        ⟨s', hSrc, hTgt⟩ | ⟨s₁, s₂, hSrc, hTgt, hNonColl⟩
      · -- 1-edge lift.
        refine ⟨Walk.cons mid s' p_tail, ?_⟩
        exact IsLift.cons_one_edge s p'' s' p_tail hSrc hTgt htail
      · -- 2-edge lift.
        refine ⟨Walk.cons u s₁ (Walk.cons mid s₂ p_tail), ?_⟩
        exact IsLift.cons_two_edge s p'' s₁ s₂ p_tail hSrc hTgt hNonColl htail

-- ## ref: claim_3_25 (Subtask 6c helper) — `marg.Sc ⊆ G.Sc`.
--
-- Marginalization can only shrink the SCC: every vertex in the marg-Sc
-- of `v` is also in the G-Sc of `v`.  Proved by combining
-- `marginalize_preserves_ancestors` and `marginalize_preserves_descendants`
-- (`Section3_2/MargPreservesAncestors.lean:124, 3996`).  Useful for the
-- σ-openness lift's blockable-slot transport (where we need
-- `x ∉ G.Sc mid → x ∉ marg.Sc mid` via the contrapositive of this
-- inclusion).
private lemma marg_sc_subset {G : CDMG Node} (u : Node)
    (hu : ({u} : Finset Node) ⊆ G.V) {v : Node}
    (hv_marg : v ∈ G.marginalize {u} hu) :
    (G.marginalize {u} hu).Sc v ⊆ G.Sc v := by
  intro x hx
  obtain ⟨hx_anc, hx_desc⟩ := hx
  have hx_marg : x ∈ G.marginalize {u} hu := hx_anc.1
  refine ⟨?_, ?_⟩
  · exact (marginalize_preserves_ancestors G {u} hu x v hx_marg hv_marg).mpr hx_anc
  · exact (marginalize_preserves_descendants G {u} hu x v hx_marg hv_marg).mpr hx_desc

-- ## ref: claim_3_25 (Subtask 6c helper) — vertex of marg-walk is ≠ u.
--
-- Every endpoint of a `WalkStep` in `G.marginalize {u} hu` is in the
-- marginalized graph's carrier, hence ≠ `u` by `notW_of_mem_marginalize`.
private lemma walkstep_target_ne_u {G : CDMG Node} {u : Node}
    (hu : ({u} : Finset Node) ⊆ G.V) {a mid : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid) : mid ≠ u := by
  intro h_eq
  have hmid_marg : mid ∈ G.marginalize {u} hu :=
    WalkStep.target_mem s
  have : mid ∉ ({u} : Finset Node) := notW_of_mem_marginalize hu hmid_marg
  exact this (h_eq ▸ Finset.mem_singleton_self u)

-- ## ref: claim_3_25 (Subtask 7a) — collapse u-self-loops on a walk.
--
-- For any σ-open walk `p : Walk G a b` whose colliders all lie in `C`
-- (the colliders-in-C invariant), construct an equivalent σ-open walk
-- `p_clean : Walk G a b` with no two consecutive vertices both equal
-- to `u`.  The collapse preserves σ-open AND colliders-in-C and adds
-- the "no consecutive u's" invariant that the downstream structural
-- lift (Subtasks 7b, 7c) requires.
--
-- ## Design choice — Path 2 (explicit splice via `splitAt + comp`)
--
-- An earlier attempt (workspace Option B) wrapped `replaceWalk` with
-- σ_ij = .nil to discharge each u-self-loop.  That stalled on a
-- structural-access gap (workspace lines 4793-5076): `replaceWalk`
-- returns the result walk inside an existential, hiding its
-- constructor unfolding, but `IsCollider`'s body reads structural
-- data off the walk's edges, which is sealed off by the existential.
-- Path 2 sidesteps this by constructing the spliced walk explicitly
-- as `prefix.comp suffix` where
-- `prefix = h_mid_i_eq ▸ (p.splitAt i hi).2.1 : Walk G a u` and
-- `suffix = h_mid_ip1_eq ▸ (p.splitAt (i+1) hip1).2.2 : Walk G u b`.
-- The comp-refactor lemmas in `LabelRoman.lean`
-- (`refactor_IsCollider_comp_left/right`, `HasBlocking*Slot_comp_*`,
-- and the splice-boundary
-- `refactor_IsCollider_comp_at_p_length_no_head_source/target`) all
-- apply directly to the resulting concrete shape, enabling
-- position-by-position transport of σ-open AND colliders-in-C from
-- `p` to `p_clean = prefix.comp suffix`.

-- Cast-invariance of `firstStepHeadAtSource` / `lastStepHeadAtTarget`
-- under source / target type rewrites.  Identical bodies to the
-- (private) originals in `LabelRoman.lean` (lines 874 and 1130);
-- re-declared here because those originals' `private` visibility
-- restricts them to that file.

private lemma firstStepHeadAtSource_cast_source'
    {G : CDMG Node} {v : Node} {u u' : Node}
    (h : u = u') (p : Walk G u v) :
    (h ▸ p).firstStepHeadAtSource = p.firstStepHeadAtSource := by
  subst h; rfl

private lemma lastStepHeadAtTarget_cast_target'
    {G : CDMG Node} {u : Node} {v v' : Node}
    (h : v = v') (p : Walk G u v) :
    (h ▸ p).lastStepHeadAtTarget = p.lastStepHeadAtTarget := by
  subst h; rfl

-- Vertex-lookup on a composition `p.comp q` at an interior position
-- `k ≤ p.length`: the lookup forwards to `p.vertices[k]?`.  Mirrors
-- the right-side `Walk.vertices_comp_right_shift` from `LabelRoman.lean`
-- (line 1564); needed at the splice-position vertex identification
-- (k = prefix.length = i) and at the strict left interior (k < i).
private lemma vertices_comp_left_le {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w) (k : ℕ),
      k ≤ p.length → (p.comp q).vertices[k]? = p.vertices[k]?
  | _, v, _, .nil _ hv, q, k, hk => by
      have hk0 : k = 0 := by simp [Walk.length] at hk; omega
      subst hk0
      show q.vertices[0]? = some v
      exact Walk.vertices_zero_eq_source q
  | _, _, _, .cons mid s p', q, 0, _ => by
      show (Walk.cons _ s (p'.comp q)).vertices[0]? = _
      rfl
  | u, _, _, .cons mid s p', q, k + 1, hk => by
      have hk' : k ≤ p'.length := by
        simp [Walk.length] at hk; omega
      show (Walk.cons _ s (p'.comp q)).vertices[k + 1]? =
            (Walk.cons _ s p').vertices[k + 1]?
      change (p'.comp q).vertices[k]? = p'.vertices[k]?
      exact vertices_comp_left_le p' q k hk'

-- ## ref: claim_3_25 (Subtask 7a) — collapse u-self-loops, signature.
--
-- See the design-choice comment block above for the Path 2 rationale.
private lemma collapse_u_self_loops
    {G : CDMG Node} (u : Node) (C : Set Node)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hu_notC : u ∉ C)
    {a b : Node} (p : Walk G a b)
    (hp_σ : p.IsSigmaOpenGiven C hC_G)
    (hp_colC :
        ∀ k vk, p.vertices[k]? = some vk → p.IsCollider k → vk ∈ C) :
    ∃ p_clean : Walk G a b,
      p_clean.IsSigmaOpenGiven C hC_G ∧
      (∀ k vk, p_clean.vertices[k]? = some vk → p_clean.IsCollider k →
         vk ∈ C) ∧
      (∀ k, p_clean.vertices[k]? = some u →
         p_clean.vertices[k+1]? ≠ some u) := by
  -- Strong induction on `p.length` via an explicit aux helper.
  suffices aux :
      ∀ (n : ℕ), ∀ {a' b' : Node} (p' : Walk G a' b'), p'.length = n →
        p'.IsSigmaOpenGiven C hC_G →
        (∀ k vk, p'.vertices[k]? = some vk → p'.IsCollider k → vk ∈ C) →
        ∃ p_clean : Walk G a' b',
          p_clean.IsSigmaOpenGiven C hC_G ∧
          (∀ k vk, p_clean.vertices[k]? = some vk → p_clean.IsCollider k →
             vk ∈ C) ∧
          (∀ k, p_clean.vertices[k]? = some u →
             p_clean.vertices[k+1]? ≠ some u) by
    exact aux p.length p rfl hp_σ hp_colC
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intros a' b' p' h_len hp'_σ hp'_colC
    -- Decide: does p' have a u-self-loop?
    by_cases h_uu :
        ∃ i, i + 1 ≤ p'.length ∧
          p'.vertices[i]? = some u ∧ p'.vertices[i+1]? = some u
    · -- Case 1: u-self-loop exists.  Splice it out and recurse.
      obtain ⟨i, h_ip1_le, h_get_i, h_get_ip1⟩ := h_uu
      have h_i_lt : i < p'.length := h_ip1_le
      have h_i_le : i ≤ p'.length := Nat.le_of_lt h_i_lt
      -- Midpoint identity at position i.
      have h_mid_i_eq : (p'.splitAt i h_i_le).1 = u := by
        have h := Walk.splitAt_mid_get p' i h_i_le
        rw [h_get_i] at h
        exact (Option.some.inj h).symm
      -- The prefix walk: Walk G a' u, length i, vertices = p'.vertices.take (i + 1).
      let prefix_walk : Walk G a' u := h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1
      have h_prefix_len : prefix_walk.length = i := by
        show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).length = i
        rw [Walk.length_cast_target h_mid_i_eq]
        exact Walk.splitAt_length_left p' i h_i_le
      have h_prefix_vertices :
          prefix_walk.vertices = p'.vertices.take (i + 1) := by
        show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).vertices = p'.vertices.take (i + 1)
        rw [Walk.vertices_cast_target h_mid_i_eq]
        exact Walk.splitAt_vertices_left p' i h_i_le
      -- Suffix-at-i: Walk G u b' (cast from (p'.splitAt i h_i_le).2.2).
      -- Length p'.length - i ≥ 1, vertices = p'.vertices.drop i.
      have h_sub_len_pre :
          (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2 : Walk G u b').length
            = p'.length - i := by
        rw [Walk.length_cast_source h_mid_i_eq]
        exact Walk.splitAt_length_right p' i h_i_le
      have h_sub_vert_pre :
          (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2 : Walk G u b').vertices
            = p'.vertices.drop i := by
        rw [Walk.vertices_cast_source h_mid_i_eq]
        exact Walk.splitAt_vertices_right p' i h_i_le
      -- Case on the suffix-at-i decomposition.
      cases h_sub_decomp :
          (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2 : Walk G u b') with
      | nil v hv =>
          -- length 0, contradiction.
          exfalso
          rw [h_sub_decomp] at h_sub_len_pre
          simp [Walk.length] at h_sub_len_pre
          omega
      | cons mid step_i suffix_after_i =>
          -- Derive mid = u from p'.vertices[i+1]? = some u.
          have h_mid_eq_u : mid = u := by
            have h1 :
                (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2 : Walk G u b').vertices
                  = (Walk.cons mid step_i suffix_after_i).vertices := by
              rw [h_sub_decomp]
            rw [h_sub_vert_pre] at h1
            -- h1 : p'.vertices.drop i = u :: suffix_after_i.vertices
            have h2 : (p'.vertices.drop i)[1]?
                    = (Walk.cons mid step_i suffix_after_i).vertices[1]? := by
              rw [h1]
            rw [List.getElem?_drop] at h2
            -- LHS: p'.vertices[i + 1]? = some u
            -- RHS reduces to suffix_after_i.vertices[0]? = some mid
            change p'.vertices[i + 1]? = suffix_after_i.vertices[0]? at h2
            rw [h_get_ip1, Walk.vertices_zero_eq_source] at h2
            exact (Option.some.inj h2).symm
          -- `subst` with the .symm direction so we substitute mid → u (keeping u).
          have h_u_eq_mid : u = mid := h_mid_eq_u.symm
          subst h_u_eq_mid
          -- Now: step_i : WalkStep G u u, suffix_after_i : Walk G u b'.
          -- Define p_collapsed.
          let p_collapsed : Walk G a' b' := prefix_walk.comp suffix_after_i
          have h_suffix_after_len : suffix_after_i.length = p'.length - i - 1 := by
            have h_total : (Walk.cons u step_i suffix_after_i : Walk G u b').length
                = suffix_after_i.length + 1 := by simp [Walk.length]
            rw [← h_sub_decomp] at h_total
            rw [h_sub_len_pre] at h_total
            omega
          have h_collapsed_len : p_collapsed.length = p'.length - 1 := by
            show (prefix_walk.comp suffix_after_i).length = _
            rw [Walk.length_comp, h_prefix_len, h_suffix_after_len]
            omega
          have h_collapsed_lt_n : p_collapsed.length < n := by
            rw [h_collapsed_len, ← h_len]; omega
          -- ## Splice boundary: ¬ p_collapsed.IsCollider i.
          --
          -- If we ASSUME `p_collapsed.IsCollider i`, then by the
          -- contrapositives of `refactor_IsCollider_comp_at_p_length_no_head_*`
          -- both `prefix_walk.lastStepHeadAtTarget` AND
          -- `suffix_after_i.firstStepHeadAtSource` hold.  Casing on `step_i`
          -- (the dropped self-loop step):
          --   * `.forwardE he`: from `suffix_after_i.firstStepHeadAtSource`
          --      and `step_i.HeadAtTarget = True`, derive
          --      `p'.IsCollider (i + 1) = True` via the splitAt + comp lemmas,
          --      contradicting `hp'_colC (i + 1) u` ∋ `u ∉ C`.
          --   * `.backwardE he`: dual; derive `p'.IsCollider i = True`,
          --      contradicting `hp'_colC i u`.
          --   * `.bidir he`: `he : s(u, u) ∈ G.L` contradicts `G.hL_irrefl`.
          have h_not_coll_at_i : ¬ p_collapsed.IsCollider i := by
            intro h_col_assumed
            -- Reframe `p_collapsed.IsCollider i` as
            -- `(prefix_walk.comp suffix_after_i).IsCollider prefix_walk.length`.
            have h_col_assumed' :
                (prefix_walk.comp suffix_after_i).IsCollider prefix_walk.length := by
              rw [h_prefix_len]; exact h_col_assumed
            have h_prefix_last : prefix_walk.lastStepHeadAtTarget := by
              by_contra h_no
              exact Walk.refactor_IsCollider_comp_at_p_length_no_head_target
                prefix_walk suffix_after_i h_no h_col_assumed'
            have h_suffix_first : suffix_after_i.firstStepHeadAtSource := by
              by_contra h_no
              exact Walk.refactor_IsCollider_comp_at_p_length_no_head_source
                prefix_walk suffix_after_i h_no h_col_assumed'
            -- Case on `step_i`.
            cases step_i with
            | forwardE he =>
                -- step_i = .forwardE he : (u, u) ∈ G.E.
                -- (.forwardE he).HeadAtTarget = True.
                -- Plan: derive p'.IsCollider (i + 1) = True using
                -- (.cons u (.forwardE he) (.nil u _)) and suffix_after_i.
                have h_u_mem : u ∈ G := (G.hE_subset he).1
                have h_single_lastStep :
                    (Walk.cons u (.forwardE he) (Walk.nil u h_u_mem) : Walk G u u).lastStepHeadAtTarget := by
                  simp only [Walk.lastStepHeadAtTarget, WalkStep.HeadAtTarget]
                have h_of_heads :=
                  Walk.refactor_IsCollider_comp_at_p_length_of_heads
                    (Walk.cons u (.forwardE he) (Walk.nil u h_u_mem) : Walk G u u)
                    suffix_after_i
                    h_single_lastStep
                    h_suffix_first
                -- h_of_heads : ((Walk.cons u (.forwardE he) (.nil u h_u_mem)).comp
                --               suffix_after_i).IsCollider
                --              (Walk.cons u (.forwardE he) (.nil u h_u_mem)).length
                -- Reduce: comp on cons-nil = cons; length on cons-nil = 1.
                have h_red :
                    (Walk.cons u (.forwardE he) (Walk.nil u h_u_mem)).comp suffix_after_i
                      = Walk.cons u (.forwardE he) suffix_after_i := rfl
                rw [h_red] at h_of_heads
                -- h_of_heads : (Walk.cons u (.forwardE he) suffix_after_i).IsCollider 1
                change (Walk.cons u (.forwardE he) suffix_after_i : Walk G u b').IsCollider 1
                  at h_of_heads
                -- Connect to (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2).IsCollider 1
                -- via h_sub_decomp.
                rw [← h_sub_decomp] at h_of_heads
                -- h_of_heads : (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2).IsCollider 1
                rw [Walk.refactor_IsCollider_cast_source] at h_of_heads
                -- h_of_heads : (p'.splitAt i h_i_le).2.2.IsCollider 1
                -- Lift to p'.IsCollider (i + 1) via splitAt_comp + comp_right.
                have h_p'_col : p'.IsCollider (i + 1) := by
                  have h_split_len := Walk.splitAt_length_left p' i h_i_le
                  have h_split_comp := Walk.splitAt_comp p' i h_i_le
                  conv_lhs => rw [← h_split_comp]
                  rw [Walk.refactor_IsCollider_comp_right _ _ (i + 1)
                      (by rw [h_split_len]; omega)]
                  rw [h_split_len, show (i + 1) - i = 1 from by omega]
                  exact h_of_heads
                exact hu_notC (hp'_colC (i + 1) u h_get_ip1 h_p'_col)
            | backwardE he =>
                -- step_i = .backwardE he : (u, u) ∈ G.E.
                -- (.backwardE he).HeadAtSource = True.
                -- Plan: derive p'.IsCollider i = True using the splitAt
                -- decomposition + _of_heads on the splitAt operands.
                -- We need (p'.splitAt i h_i_le).2.1.lastStepHeadAtTarget and
                -- (p'.splitAt i h_i_le).2.2.firstStepHeadAtSource.
                have h_split_pre_last :
                    (p'.splitAt i h_i_le).2.1.lastStepHeadAtTarget := by
                  rw [← lastStepHeadAtTarget_cast_target' h_mid_i_eq
                        (p'.splitAt i h_i_le).2.1]
                  exact h_prefix_last
                have h_split_suf_first :
                    (p'.splitAt i h_i_le).2.2.firstStepHeadAtSource := by
                  rw [← firstStepHeadAtSource_cast_source' h_mid_i_eq
                        (p'.splitAt i h_i_le).2.2]
                  rw [h_sub_decomp]
                  -- Goal: (Walk.cons u (.backwardE he) suffix_after_i).firstStepHeadAtSource
                  --     = (.backwardE he).HeadAtSource = True
                  trivial
                have h_split_col_i :=
                  Walk.refactor_IsCollider_comp_at_p_length_of_heads
                    (p'.splitAt i h_i_le).2.1 (p'.splitAt i h_i_le).2.2
                    h_split_pre_last h_split_suf_first
                -- h_split_col_i : ((p'.splitAt i h_i_le).2.1.comp
                --                  (p'.splitAt i h_i_le).2.2).IsCollider
                --                 (p'.splitAt i h_i_le).2.1.length
                rw [Walk.splitAt_comp, Walk.splitAt_length_left] at h_split_col_i
                -- h_split_col_i : p'.IsCollider i
                exact hu_notC (hp'_colC i u h_get_i h_split_col_i)
            | bidir he =>
                -- he : s(u, u) ∈ G.L.  Contradicts `G.hL_irrefl`.
                exact G.hL_irrefl he (Sym2.mk_isDiag_iff.mpr rfl)
          -- ## Transport helpers.
          --
          -- For positions k different from the splice index i, the
          -- collider / vertex / HBLS / HBRS predicates on p_collapsed
          -- transport to the matching predicates on p' (at index k for
          -- k < i, at index k + 1 for k > i).  Each helper combines the
          -- comp-refactor lemma, a cast-invariance step, and the
          -- splitAt_comp identity.
          -- u ∈ G (needed to build a length-1 "single self-loop step" walk
          -- for the cons-cell HBLS/HBRS rewrites on the right side).
          have h_u_mem : u ∈ G := by
            have h_lt : i < p'.vertices.length := by
              rw [Walk.vertices_length]; omega
            have h_in : u ∈ p'.vertices := by
              rw [List.getElem?_eq_getElem h_lt] at h_get_i
              have : u = p'.vertices[i] := (Option.some.inj h_get_i).symm
              rw [this]
              exact List.getElem_mem _
            exact Walk.mem_of_mem_vertices p' h_in
          -- IsCollider transport at k < i.
          have h_col_lt : ∀ k, k < i →
              p_collapsed.IsCollider k = p'.IsCollider k := fun k hk_lt => by
            show (prefix_walk.comp suffix_after_i).IsCollider k = _
            rw [Walk.refactor_IsCollider_comp_left _ _ _ (h_prefix_len ▸ hk_lt)]
            show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).IsCollider k = _
            rw [Walk.refactor_IsCollider_cast_target h_mid_i_eq]
            conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
            rw [Walk.refactor_IsCollider_comp_left _ _ _
                (by rw [Walk.splitAt_length_left]; exact hk_lt)]
          -- IsCollider transport at k > i.
          have h_col_gt : ∀ k, i < k →
              p_collapsed.IsCollider k = p'.IsCollider (k + 1) := fun k hk_gt => by
            show (prefix_walk.comp suffix_after_i).IsCollider k = _
            rw [Walk.refactor_IsCollider_comp_right _ _ _ (h_prefix_len ▸ hk_gt)]
            rw [h_prefix_len]
            -- Connect suffix_after_i.IsCollider (k - i) via the cons cell.
            have h_one_step :
                ((Walk.cons u step_i (Walk.nil u h_u_mem) : Walk G u u).comp suffix_after_i).IsCollider
                    (k - i + 1)
                = suffix_after_i.IsCollider (k - i) := by
              rw [Walk.refactor_IsCollider_comp_right _ _ _ (by show 1 < _; omega)]
              show suffix_after_i.IsCollider ((k - i + 1) - _) = _
              congr 1
            rw [← h_one_step]
            -- LHS reduces by `(.cons _ _ .nil).comp q = .cons _ _ q`.
            change (Walk.cons u step_i suffix_after_i : Walk G u b').IsCollider (k - i + 1) = _
            rw [← h_sub_decomp]
            rw [Walk.refactor_IsCollider_cast_source h_mid_i_eq]
            conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
            rw [Walk.refactor_IsCollider_comp_right _ _ _
                (by rw [Walk.splitAt_length_left]; omega)]
            rw [Walk.splitAt_length_left]
            congr 1; omega
          -- Vertex transport at k ≤ i.
          have h_v_le : ∀ k, k ≤ i →
              p_collapsed.vertices[k]? = p'.vertices[k]? := fun k hk_le => by
            show (prefix_walk.comp suffix_after_i).vertices[k]? = _
            rw [vertices_comp_left_le prefix_walk suffix_after_i k (h_prefix_len ▸ hk_le)]
            show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).vertices[k]? = _
            rw [Walk.vertices_cast_target h_mid_i_eq]
            rw [Walk.splitAt_vertices_left, List.getElem?_take, if_pos (by omega)]
          -- Vertex transport at k > i.
          have h_v_gt : ∀ k, i < k →
              p_collapsed.vertices[k]? = p'.vertices[k + 1]? := fun k hk_gt => by
            show (prefix_walk.comp suffix_after_i).vertices[k]? = _
            conv_lhs => rw [show k = prefix_walk.length + (k - i)
              from by rw [h_prefix_len]; omega]
            rw [Walk.vertices_comp_right_shift]
            -- suffix_after_i.vertices[k - i]? = p'.vertices[k + 1]?
            have h_eq : (Walk.cons u step_i suffix_after_i : Walk G u b').vertices
                = p'.vertices.drop i := by
              rw [← h_sub_decomp]
              exact h_sub_vert_pre
            -- (Walk.cons u step_i suffix_after_i).vertices = u :: suffix_after_i.vertices.
            have h_step :
                suffix_after_i.vertices[k - i]?
                  = (Walk.cons u step_i suffix_after_i : Walk G u b').vertices[(k - i) + 1]? :=
              rfl
            rw [h_step, h_eq, List.getElem?_drop]
            congr 1; omega
          -- Vertex at splice position is u.
          have h_v_at_i : p_collapsed.vertices[i]? = some u := by
            rw [h_v_le i le_rfl]; exact h_get_i
          -- HBLS transport at k < i.
          have h_HBLS_lt : ∀ k, k < i →
              p_collapsed.HasBlockingLeftSlot k
                = p'.HasBlockingLeftSlot k := fun k hk_lt => by
            show (prefix_walk.comp suffix_after_i).HasBlockingLeftSlot k = _
            rw [Walk.HasBlockingLeftSlot_comp_left _ _ _ (h_prefix_len ▸ hk_lt.le)]
            show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).HasBlockingLeftSlot k = _
            rw [Walk.HasBlockingLeftSlot_cast_target h_mid_i_eq]
            conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
            rw [Walk.HasBlockingLeftSlot_comp_left _ _ _
                (by rw [Walk.splitAt_length_left]; exact hk_lt.le)]
          -- HBLS transport at k > i.
          have h_HBLS_gt : ∀ k, i < k →
              p_collapsed.HasBlockingLeftSlot k
                = p'.HasBlockingLeftSlot (k + 1) := fun k hk_gt => by
            show (prefix_walk.comp suffix_after_i).HasBlockingLeftSlot k = _
            rw [Walk.HasBlockingLeftSlot_comp_right _ _ _ (h_prefix_len ▸ hk_gt)]
            rw [h_prefix_len]
            have h_one_step :
                ((Walk.cons u step_i (Walk.nil u h_u_mem) : Walk G u u).comp suffix_after_i).HasBlockingLeftSlot
                    (k - i + 1)
                = suffix_after_i.HasBlockingLeftSlot (k - i) := by
              rw [Walk.HasBlockingLeftSlot_comp_right _ _ _ (by show 1 < _; omega)]
              show suffix_after_i.HasBlockingLeftSlot ((k - i + 1) - _) = _
              congr 1
            rw [← h_one_step]
            change (Walk.cons u step_i suffix_after_i : Walk G u b').HasBlockingLeftSlot (k - i + 1) = _
            rw [← h_sub_decomp]
            rw [Walk.HasBlockingLeftSlot_cast_source h_mid_i_eq]
            conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
            rw [Walk.HasBlockingLeftSlot_comp_right _ _ _
                (by rw [Walk.splitAt_length_left]; omega)]
            rw [Walk.splitAt_length_left]
            congr 1; omega
          -- HBRS transport at k < i.
          have h_HBRS_lt : ∀ k, k < i →
              p_collapsed.HasBlockingRightSlot k
                = p'.HasBlockingRightSlot k := fun k hk_lt => by
            show (prefix_walk.comp suffix_after_i).HasBlockingRightSlot k = _
            rw [Walk.HasBlockingRightSlot_comp_left _ _ _ (h_prefix_len ▸ hk_lt)]
            show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).HasBlockingRightSlot k = _
            rw [Walk.HasBlockingRightSlot_cast_target h_mid_i_eq]
            conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
            rw [Walk.HasBlockingRightSlot_comp_left _ _ _
                (by rw [Walk.splitAt_length_left]; exact hk_lt)]
          -- HBRS transport at k > i.
          have h_HBRS_gt : ∀ k, i < k →
              p_collapsed.HasBlockingRightSlot k
                = p'.HasBlockingRightSlot (k + 1) := fun k hk_gt => by
            show (prefix_walk.comp suffix_after_i).HasBlockingRightSlot k = _
            rw [Walk.HasBlockingRightSlot_comp_right _ _ _ (h_prefix_len ▸ hk_gt.le)]
            rw [h_prefix_len]
            have h_one_step :
                ((Walk.cons u step_i (Walk.nil u h_u_mem) : Walk G u u).comp suffix_after_i).HasBlockingRightSlot
                    (k - i + 1)
                = suffix_after_i.HasBlockingRightSlot (k - i) := by
              rw [Walk.HasBlockingRightSlot_comp_right _ _ _ (by show 1 ≤ _; omega)]
              show suffix_after_i.HasBlockingRightSlot ((k - i + 1) - _) = _
              congr 1
            rw [← h_one_step]
            change (Walk.cons u step_i suffix_after_i : Walk G u b').HasBlockingRightSlot (k - i + 1) = _
            rw [← h_sub_decomp]
            rw [Walk.HasBlockingRightSlot_cast_source h_mid_i_eq]
            conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
            rw [Walk.HasBlockingRightSlot_comp_right _ _ _
                (by rw [Walk.splitAt_length_left]; omega)]
            rw [Walk.splitAt_length_left]
            congr 1; omega
          -- ## σ-open of p_collapsed.
          --
          -- Position-by-position transport from `hp'_σ`:
          --   * k < i: vertex / collider / blockable-noncollider clauses
          --     transport directly via the `_lt` helpers above.
          --   * k = i: the splice position.  Vertex is `u`.  For the
          --     collider clause, `¬ p_collapsed.IsCollider i` is
          --     `h_not_coll_at_i`, making the collider clause vacuous at
          --     this position.  For the blockable clause, the vertex
          --     being `u` and `hu_notC : u ∉ C` closes the goal.
          --   * k > i: vertex / collider / blockable-noncollider clauses
          --     transport via the `_gt` helpers (shift k → k + 1 on p').
          have h_collapsed_σ : p_collapsed.IsSigmaOpenGiven C hC_G := by
            refine ⟨?_, ?_⟩
            · -- Collider clause: every collider position has vk ∈ G.AncSet C.
              intros k vk h_get_k h_col_k
              rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
              · -- k < i: direct transport via _lt helpers.
                rw [h_v_le k hk_lt.le] at h_get_k
                rw [h_col_lt k hk_lt] at h_col_k
                exact hp'_σ.1 k vk h_get_k h_col_k
              · -- k = i: vacuous, ¬ p_collapsed.IsCollider i.
                exact absurd h_col_k h_not_coll_at_i
              · -- k > i: transport via _gt helpers with k → k + 1 on p'.
                rw [h_v_gt k hk_gt] at h_get_k
                rw [h_col_gt k hk_gt] at h_col_k
                exact hp'_σ.1 (k + 1) vk h_get_k h_col_k
            · -- Blockable clause: every blockable non-collider has vk ∉ C.
              intros k vk h_get_k h_blk_k
              rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
              · -- k < i.
                rw [h_v_le k hk_lt.le] at h_get_k
                -- Rebuild p'.IsBlockableNonCollider k from p_collapsed's.
                have h_blk' : p'.IsBlockableNonCollider k := by
                  refine ⟨⟨?_, ?_⟩, ?_⟩
                  · -- k ≤ p'.length: k < i < p'.length.
                    omega
                  · -- ¬ p'.IsCollider k: via h_col_lt.
                    rw [← h_col_lt k hk_lt]
                    exact h_blk_k.1.2
                  · -- Disjunct: transport each disjunct.
                    rcases h_blk_k.2 with hk0 | hk_len | h_hbls | h_hbrs
                    · exact Or.inl hk0
                    · -- k = p_collapsed.length: but k < i ≤ p'.length - 1
                      --   = p_collapsed.length, contradicting k = p_collapsed.length.
                      exfalso
                      rw [h_collapsed_len] at hk_len
                      omega
                    · refine Or.inr (Or.inr (Or.inl ?_))
                      rw [← h_HBLS_lt k hk_lt]
                      exact h_hbls
                    · refine Or.inr (Or.inr (Or.inr ?_))
                      rw [← h_HBRS_lt k hk_lt]
                      exact h_hbrs
                exact hp'_σ.2 k vk h_get_k h_blk'
              · -- k = i: vertex is u; u ∉ C closes the goal.
                rw [h_v_at_i] at h_get_k
                have h_eq : u = vk := Option.some.inj h_get_k
                exact h_eq ▸ hu_notC
              · -- k > i.
                rw [h_v_gt k hk_gt] at h_get_k
                -- Rebuild p'.IsBlockableNonCollider (k + 1).
                have h_blk' : p'.IsBlockableNonCollider (k + 1) := by
                  refine ⟨⟨?_, ?_⟩, ?_⟩
                  · -- k + 1 ≤ p'.length: from k ≤ p_collapsed.length = p'.length - 1.
                    have h_k_le := h_blk_k.1.1
                    omega
                  · -- ¬ p'.IsCollider (k + 1): via h_col_gt.
                    rw [← h_col_gt k hk_gt]
                    exact h_blk_k.1.2
                  · -- Disjunct: transport each disjunct.
                    rcases h_blk_k.2 with hk0 | hk_len | h_hbls | h_hbrs
                    · -- k = 0 contradicts i < k.
                      exfalso; omega
                    · -- k = p_collapsed.length → k + 1 = p'.length.
                      refine Or.inr (Or.inl ?_)
                      rw [h_collapsed_len] at hk_len
                      omega
                    · refine Or.inr (Or.inr (Or.inl ?_))
                      rw [← h_HBLS_gt k hk_gt]
                      exact h_hbls
                    · refine Or.inr (Or.inr (Or.inr ?_))
                      rw [← h_HBRS_gt k hk_gt]
                      exact h_hbrs
                exact hp'_σ.2 (k + 1) vk h_get_k h_blk'
          -- ## colliders-in-C of p_collapsed.
          have h_collapsed_colC :
              ∀ k vk, p_collapsed.vertices[k]? = some vk → p_collapsed.IsCollider k →
                vk ∈ C := by
            intros k vk h_get_k h_col_k
            rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
            · -- k < i
              rw [h_v_le k hk_lt.le] at h_get_k
              rw [h_col_lt k hk_lt] at h_col_k
              exact hp'_colC k vk h_get_k h_col_k
            · -- k = i: ¬ p_collapsed.IsCollider i (vacuous).
              exact absurd h_col_k h_not_coll_at_i
            · -- k > i
              rw [h_v_gt k hk_gt] at h_get_k
              rw [h_col_gt k hk_gt] at h_col_k
              exact hp'_colC (k + 1) vk h_get_k h_col_k
          -- ## Recurse via the IH on p_collapsed.
          obtain ⟨p_clean, h_clean_σ, h_clean_colC, h_clean_no_uu⟩ :=
            ih p_collapsed.length h_collapsed_lt_n p_collapsed rfl
              h_collapsed_σ h_collapsed_colC
          exact ⟨p_clean, h_clean_σ, h_clean_colC, h_clean_no_uu⟩
    · -- Case 2: no u-self-loop.  Return p' directly.
      refine ⟨p', hp'_σ, hp'_colC, ?_⟩
      intros k h_get_k h_get_kp1
      apply h_uu
      refine ⟨k, ?_, h_get_k, h_get_kp1⟩
      -- Derive k + 1 ≤ p'.length from h_get_kp1.
      by_contra h_too_big
      push_neg at h_too_big
      have h_vlen : p'.vertices.length = p'.length + 1 := Walk.vertices_length p'
      have h_ge : p'.vertices.length ≤ k + 1 := by
        rw [h_vlen]; omega
      rw [List.getElem?_eq_none h_ge] at h_get_kp1
      cases h_get_kp1

-- ## ref: claim_3_25 (Subtask 7a-2) — elide u-side-trip bifurcations.
--
-- Extends `collapse_u_self_loops` (above): after collapsing all
-- consecutive u-self-loops, a σ-open walk through u may still contain
-- "u-side-trip" 2-edge segments of the form `b ... u ... b` (3-position
-- pattern `(b, u, b)` with the same flanking vertex `b`) whose
-- WalkStep arrowhead pattern at u is a *bifurcation* — one of: fork
-- `(.backwardE, .forwardE)`, left hinge `(.bidir, .forwardE)`, right
-- hinge `(.backwardE, .bidir)`.  For such segments, Subtask 7c's lift
-- attempt via `walkstep_lift_two_edge` fails: the lift would require an
-- `s(b, b) ∈ marg.L` edge (a marg-bidir self-loop), which is structurally
-- excluded by `marg.L`'s `e.1 ≠ e.2` filter (inherited from `def_3_14`'s
-- `L^{∖u}` definition).  The 2 *directed pass-through* patterns
-- ((.forwardE, .forwardE), (.backwardE, .backwardE)) DO admit a marg-E
-- self-loop `(b, b) ∈ marg.E` witness, so those segments can be handled
-- by 7c directly without elision.
--
-- This lemma's elision is therefore *necessary* and *sufficient* for
-- 7c to dispatch `walkstep_lift_two_edge` uniformly on every 2-edge
-- segment through u with coinciding flanking vertices: the side-trips
-- that survive after this preprocessing are guaranteed to be directed
-- pass-throughs.
--
-- ## What this formalizes from the LN
--
-- The LN's Case B classification of u-non-collider 2-edge segments
-- (tex `claim_3_25_proof_ISigmaSeparation.tex` lines 240–249) groups
-- the 5 substantive patterns into directed pass-through (1 case +
-- reflection = 2 patterns) and bifurcation (2 cases + 1 reflection =
-- 3 patterns).  The LN's text silently assumes (in its Case B
-- "contracted edge" construction) that the flanking vertices `b_l`
-- and `b_{l+1}` are distinct — otherwise the bifurcation patterns
-- would produce a marg-L self-loop, which doesn't exist.  This lemma
-- formalizes the *step that removes this implicit assumption*: when
-- the flanking vertices coincide AND the arrowhead pattern is a
-- bifurcation, the 2-edge segment is elided from the walk, leaving
-- the merged endpoint position to inherit its boundary heads from the
-- original segment's neighbors.
--
-- ## Design choice — Path 2 (mirror `collapse_u_self_loops`'s splice)
--
-- Same explicit-splice architecture as `collapse_u_self_loops`
-- (lines 1946–2433): well-founded recursion on `p.length`, search for
-- the first u-side-trip with bifurcation arrowhead pattern, splice via
-- `prefix_walk.comp suffix_walk` where:
--   * `prefix_walk = (p.splitAt i hi).2.1 : Walk G a b''` (cast from
--     midpoint identity at position i = b''),
--   * `suffix_walk = (p.splitAt (i+2) hip2).2.2 : Walk G b'' b` (cast
--     from midpoint identity at position i+2 = b'').
-- The elision drops length by 2 (positions i+1 = u and i+2 = b'' are
-- removed; the merged vertex at p_clean position i = b'' inherits its
-- incoming edge from p's position i-1 and its outgoing edge from p's
-- position i+2).
--
-- ## The substantive new piece — σ-open transport at the merged boundary
--
-- The merged boundary at position i of p_clean has:
--   * Incoming edge = p's edge at position i-1 (unchanged).
--   * Outgoing edge = p's edge at position i+2 (was the post-side-trip edge).
-- So the merged collider classification at i differs from BOTH original
-- p's classifications at positions i and i+2.  Using the bifurcation
-- flank assumption `s_i.HeadAtSource = T ∧ s_{i+1}.HeadAtTarget = T`
-- at vertex `b''`:
--   * Merged collider at i ⟺ in-HEAD ∧ out-HEAD.
--   * Original i collider ⟺ in-HEAD ∧ T = in-HEAD.
--   * Original (i+2) collider ⟺ T ∧ out-HEAD = out-HEAD.
-- Hence merged collider ⟹ both original positions are colliders,
-- giving `b'' ∈ C` via colliders-in-C, hence `b'' ∈ AncSet C` trivially.
--
-- For the blockable clause at merged i (with `k = i ≥ 1`,
-- `IsBlockableNonCollider` on p_clean, want `b'' ∉ C`): case-analyze
-- on which disjunct of `IsBlockableNonCollider` fires:
--   * `k = 0`: excluded by `k ≥ 1`.
--   * `k = p_clean.length`: then `i+2 = p.length`.  Apply σ-open of p
--     at i+2 (k ≥ 1): `IsBlockableNonCollider` via `k = p.length`
--     disjunct gives `b'' ∉ C`.
--   * `HBLS_clean i`: equals `HBLS_p i` (same incoming edge).
--     `HBLS_p i` fires ⟹ p's edge[i-1] is `.backwardE` ⟹ in-HEAD = F ⟹
--     original i is non-collider.  Apply σ-open of p at i (k ≥ 1):
--     `IsBlockableNonCollider` via HBLS disjunct gives `b'' ∉ C`.
--   * `HBRS_clean i`: equals `HBRS_p (i+2)` (same outgoing edge).
--     `HBRS_p (i+2)` fires ⟹ p's edge[i+2] is `.forwardE` ⟹ out-HEAD = F
--     ⟹ original (i+2) is non-collider.  Apply σ-open of p at i+2
--     (k = i+2 ≥ 2 ≥ 1): `IsBlockableNonCollider` via HBRS disjunct
--     gives `b'' ∉ C`.

-- ### Helper: bifurcation flank pattern at a position.
--
-- `p.IsBifurcationFlankAt (k + 1)` queries whether the WalkStep pair
-- at positions (k, k+1) of p (i.e., the steps `s_k` and `s_{k+1}`) has
-- a HEAD at BOTH flanking vertices (positions k and k+2) — the
-- structural dual of `IsCollider`, which queries HEADs at the MIDDLE
-- vertex (position k+1).  For a 3-position pattern (b, u, b) at
-- positions (i, i+1, i+2), `IsBifurcationFlankAt (i+1)` evaluates to
-- `s_i.HeadAtSource ∧ s_{i+1}.HeadAtTarget` (both heads at the flank
-- vertex b), which discriminates the 3 bifurcation patterns
-- ((backwardE, forwardE), (bidir, forwardE), (backwardE, bidir)) from
-- the 2 directed pass-throughs ((forwardE, forwardE),
-- (backwardE, backwardE)) and — assuming u-non-collider — from the
-- (bidir, bidir) collider.
private def Walk.IsBifurcationFlankAt {G : CDMG Node} :
    ∀ {a b : Node}, Walk G a b → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ (.nil _ _), _ => False
  | _, _, .cons _ _ (.cons _ _ _), 0 => False
  | _, _, .cons _ s₀ (.cons _ s₁ _), 1 =>
      s₀.HeadAtSource ∧ s₁.HeadAtTarget
  | _, _, .cons _ _ (p@(.cons _ _ _)), k + 2 =>
      p.IsBifurcationFlankAt (k + 1)

-- ### Helper: "no bifurcation side-trip at u" invariant.
--
-- For every 3-position pattern (b, u, b) on `p`, the WalkStep
-- arrowhead pattern at u is NOT a bifurcation (i.e., is one of the
-- 2 directed pass-throughs).  Used by Subtask 7c to dispatch
-- `walkstep_lift_two_edge` uniformly: when a 2-edge G-walk segment
-- through u has coinciding flanking vertices (a = mid), the
-- arrowhead pattern must be directed pass-through, in which case
-- `walkstep_lift_two_edge`'s `hne : a ≠ mid` requirement is
-- side-stepped via a marg-E self-loop `(a, a) ∈ marg.E` witness.
private def NoBifurcationSideTrip {G : CDMG Node} {a b : Node}
    (p : Walk G a b) (u : Node) : Prop :=
  ∀ (i : ℕ) (v : Node),
    p.vertices[i]? = some v →
    p.vertices[i+1]? = some u →
    p.vertices[i+2]? = some v →
    ¬ p.IsBifurcationFlankAt (i + 1)

-- ### Helper: comp-right transport for IsBifurcationFlankAt.
--
-- Mirror of `Walk.refactor_IsCollider_comp_right` (LabelRoman.lean:602).
-- At position k > p1.length on (p1.comp p2), the predicate's value
-- reads entirely off p2 at position (k - p1.length).  Used inside
-- `elide_u_side_trip_bifurcations` to relate the input walk's
-- IsBifurcationFlankAt to the splitAt-suffix's IsBifurcationFlankAt
-- at position 1 (which definitionally reduces to the bifurcation
-- flank head conjunction on the first two cons-cells).
private lemma Walk.IsBifurcationFlankAt_comp_right {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), p1.length < k →
      (p1.comp p2).IsBifurcationFlankAt k
        = p2.IsBifurcationFlankAt (k - p1.length) := by
  induction p1 with
  | nil v hv =>
      intros p2 k _
      show p2.IsBifurcationFlankAt k = p2.IsBifurcationFlankAt (k - 0)
      rfl
  | cons mid s p1' ih =>
      intros p2 k hk
      have hk_ge : k ≥ 2 := by simp [Walk.length] at hk; omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hk_ih : p1'.length < k' + 1 := by
        simp [Walk.length] at hk; omega
      have h_sub : k' + 2 - (Walk.cons mid s p1').length =
                   k' + 1 - p1'.length := by
        simp only [Walk.length]; omega
      rw [h_sub]
      simp only [Walk.comp, Walk.IsBifurcationFlankAt]
      cases p1' with
      | nil _ _ =>
          cases p2 with
          | nil _ _ => rfl
          | cons _ _ _ => rfl
      | cons mid' s' p1'' =>
          exact ih p2 (k' + 1) hk_ih

-- ### Helper: source-cast invariance for IsBifurcationFlankAt.
-- Used to relate the splitAt-suffix's IsBifurcationFlankAt to the
-- casted-source version (where we've cast the source from
-- `(p.splitAt i hi).1` to the externally-known value `b''`).
private lemma Walk.IsBifurcationFlankAt_cast_source {G : CDMG Node}
    {v : Node} {u u' : Node} (h : u = u') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).IsBifurcationFlankAt k = p.IsBifurcationFlankAt k := by
  subst h; rfl

-- ### Helper: HBLS at position k rules out IsCollider at k.
-- Re-declared here (the canonical version in `LabelRoman.lean:1582` is
-- `private` and not accessible from this file).  Body byte-identical
-- to the LabelRoman version; rationale: HBLS at k requires the slot
-- (k-1) step to be `.backwardE`, whose `HeadAtTarget = False`, ruling
-- out the collider-at-k conjunct `s_{k-1}.HeadAtTarget`.
private lemma Walk.HBLS_not_IsCollider {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.HasBlockingLeftSlot k → ¬ p.IsCollider k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros k h_blk
      cases k <;> exact h_blk.elim
  | cons mid s p' ih =>
      intros k h_blk h_coll
      match k with
      | 0 => exact h_blk.elim
      | 1 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ s' _ =>
              cases s with
              | forwardE _ => exact h_blk.elim
              | backwardE _ =>
                  obtain ⟨h_left, _⟩ := h_coll
                  exact h_left
              | bidir _ => exact h_blk.elim
      | k' + 2 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ _ _ => exact ih _ h_blk h_coll

-- ### Helper: HBRS at position k rules out IsCollider at k.
-- Re-declared here (the canonical version in `LabelRoman.lean:1609` is
-- `private` and not accessible from this file).  Body byte-identical
-- to the LabelRoman version; rationale: HBRS at k requires the slot
-- k step to be `.forwardE`, whose `HeadAtSource = False`, ruling out
-- the collider-at-k conjunct `s_k.HeadAtSource`.
private lemma Walk.HBRS_not_IsCollider {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.HasBlockingRightSlot k → ¬ p.IsCollider k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros k h_blk
      cases k <;> exact h_blk.elim
  | cons mid s p' ih =>
      intros k h_blk h_coll
      match k with
      | 0 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ _ _ => exact h_coll
      | k' + 1 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ s' p'' =>
              cases s with
              | forwardE _ =>
                  change (Walk.cons _ s' p'').HasBlockingRightSlot k' at h_blk
                  match k' with
                  | 0 =>
                      cases s' with
                      | forwardE _ =>
                          obtain ⟨_, h_right⟩ := h_coll
                          exact h_right
                      | backwardE _ => change False at h_blk; exact h_blk
                      | bidir _ => change False at h_blk; exact h_blk
                  | k'' + 1 => exact ih _ h_blk h_coll
              | backwardE _ =>
                  change (Walk.cons _ s' p'').HasBlockingRightSlot k' at h_blk
                  match k' with
                  | 0 =>
                      cases s' with
                      | forwardE _ =>
                          obtain ⟨_, h_right⟩ := h_coll
                          exact h_right
                      | backwardE _ => change False at h_blk; exact h_blk
                      | bidir _ => change False at h_blk; exact h_blk
                  | k'' + 1 => exact ih _ h_blk h_coll
              | bidir _ =>
                  change (Walk.cons _ s' p'').HasBlockingRightSlot k' at h_blk
                  match k' with
                  | 0 =>
                      cases s' with
                      | forwardE _ =>
                          obtain ⟨_, h_right⟩ := h_coll
                          exact h_right
                      | backwardE _ => change False at h_blk; exact h_blk
                      | bidir _ => change False at h_blk; exact h_blk
                  | k'' + 1 => exact ih _ h_blk h_coll

-- ## ref: claim_3_25 (Subtask 7a-2) — elide u-side-trip bifurcations, signature.
--
-- See the design-choice comment block above for the Path 2 rationale
-- and the merged-boundary σ-open transport sketch.
private lemma elide_u_side_trip_bifurcations
    {G : CDMG Node} (u : Node) (C : Set Node)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hu_notC : u ∉ C) :
    ∀ {a b : Node} (p : Walk G a b),
      a ≠ u → b ≠ u →
      (∀ k, p.vertices[k]? = some u → p.IsNonCollider k) →
      (∀ k, p.vertices[k]? = some u → p.vertices[k+1]? ≠ some u) →
      (∀ k vk, p.vertices[k]? = some vk → p.IsCollider k → vk ∈ C) →
      IsSigmaOpenAtInterior p C hC_G →
      ∃ p_clean : Walk G a b,
        (∀ k, p_clean.vertices[k]? = some u → p_clean.IsNonCollider k) ∧
        (∀ k, p_clean.vertices[k]? = some u →
           p_clean.vertices[k+1]? ≠ some u) ∧
        NoBifurcationSideTrip p_clean u ∧
        (∀ k vk, p_clean.vertices[k]? = some vk → p_clean.IsCollider k →
           vk ∈ C) ∧
        IsSigmaOpenAtInterior p_clean C hC_G := by
  intros a b p
  suffices aux : ∀ (n : ℕ), ∀ {a' b' : Node} (p' : Walk G a' b'),
      p'.length = n →
      a' ≠ u → b' ≠ u →
      (∀ k, p'.vertices[k]? = some u → p'.IsNonCollider k) →
      (∀ k, p'.vertices[k]? = some u → p'.vertices[k+1]? ≠ some u) →
      (∀ k vk, p'.vertices[k]? = some vk → p'.IsCollider k → vk ∈ C) →
      IsSigmaOpenAtInterior p' C hC_G →
      ∃ p_clean : Walk G a' b',
        (∀ k, p_clean.vertices[k]? = some u → p_clean.IsNonCollider k) ∧
        (∀ k, p_clean.vertices[k]? = some u →
           p_clean.vertices[k+1]? ≠ some u) ∧
        NoBifurcationSideTrip p_clean u ∧
        (∀ k vk, p_clean.vertices[k]? = some vk → p_clean.IsCollider k →
           vk ∈ C) ∧
        IsSigmaOpenAtInterior p_clean C hC_G by
    intros ha hb h_noncoll h_no_cons_u h_colC h_sigma
    exact aux p.length p rfl ha hb h_noncoll h_no_cons_u h_colC h_sigma
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intros a' b' p' h_len ha' hb' h_noncoll' h_no_cons_u' h_colC' h_sigma'
    -- Decide: does p' have a bifurcation side-trip?
    by_cases h_st :
        ∃ (i : ℕ) (v : Node), i + 2 ≤ p'.length ∧
          p'.vertices[i]? = some v ∧
          p'.vertices[i+1]? = some u ∧
          p'.vertices[i+2]? = some v ∧
          p'.IsBifurcationFlankAt (i + 1)
    · -- Case 1: a bifurcation side-trip exists.  Splice it out and recurse.
      obtain ⟨i, b'', h_ip2_le, h_get_i, h_get_ip1, h_get_ip2, h_bif⟩ := h_st
      have h_i_lt : i < p'.length := by omega
      have h_i_le : i ≤ p'.length := h_i_lt.le
      -- Midpoint identities.
      have h_mid_i_eq : (p'.splitAt i h_i_le).1 = b'' := by
        have h := Walk.splitAt_mid_get p' i h_i_le
        rw [h_get_i] at h
        exact (Option.some.inj h).symm
      have h_mid_ip2_eq : (p'.splitAt (i+2) h_ip2_le).1 = b'' := by
        have h := Walk.splitAt_mid_get p' (i+2) h_ip2_le
        rw [h_get_ip2] at h
        exact (Option.some.inj h).symm
      -- Prefix walk: Walk G a' b'', length i.
      let prefix_walk : Walk G a' b'' := h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1
      have h_prefix_len : prefix_walk.length = i := by
        show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).length = i
        rw [Walk.length_cast_target h_mid_i_eq]
        exact Walk.splitAt_length_left p' i h_i_le
      have h_prefix_vertices :
          prefix_walk.vertices = p'.vertices.take (i + 1) := by
        show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).vertices
            = p'.vertices.take (i + 1)
        rw [Walk.vertices_cast_target h_mid_i_eq]
        exact Walk.splitAt_vertices_left p' i h_i_le
      -- Suffix walk: Walk G b'' b', length p'.length - (i+2).
      let suffix_walk : Walk G b'' b' :=
        h_mid_ip2_eq ▸ (p'.splitAt (i+2) h_ip2_le).2.2
      have h_suffix_len :
          suffix_walk.length = p'.length - (i + 2) := by
        show (h_mid_ip2_eq ▸ (p'.splitAt (i+2) h_ip2_le).2.2).length
            = p'.length - (i + 2)
        rw [Walk.length_cast_source h_mid_ip2_eq]
        exact Walk.splitAt_length_right p' (i+2) h_ip2_le
      have h_suffix_vertices :
          suffix_walk.vertices = p'.vertices.drop (i + 2) := by
        show (h_mid_ip2_eq ▸ (p'.splitAt (i+2) h_ip2_le).2.2).vertices
            = p'.vertices.drop (i + 2)
        rw [Walk.vertices_cast_source h_mid_ip2_eq]
        exact Walk.splitAt_vertices_right p' (i+2) h_ip2_le
      -- p_collapsed: Walk G a' b', length p'.length - 2.
      let p_collapsed : Walk G a' b' := prefix_walk.comp suffix_walk
      have h_collapsed_len : p_collapsed.length = p'.length - 2 := by
        show (prefix_walk.comp suffix_walk).length = _
        rw [Walk.length_comp, h_prefix_len, h_suffix_len]
        omega
      have h_collapsed_lt_n : p_collapsed.length < n := by
        rw [h_collapsed_len, ← h_len]; omega
      -- ## Extract step_i and step_ip1 via cons-decomposition of the splitAt(i) suffix.
      --
      -- (p'.splitAt i h_i_le).2.2 is a walk starting at b'' (after cast)
      -- and going to b'.  Its first two cons-cells expose step_i (= s_i,
      -- the edge from b'' to u) and step_ip1 (= s_{i+1}, the edge from
      -- u to b'').  h_bif on p' at position i+1 reduces to
      -- step_i.HeadAtSource ∧ step_ip1.HeadAtTarget via comp_right.
      let suffix_at_i_cast : Walk G b'' b' :=
        h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2
      have h_suffix_at_i_len :
          suffix_at_i_cast.length = p'.length - i := by
        show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2).length = p'.length - i
        rw [Walk.length_cast_source h_mid_i_eq]
        exact Walk.splitAt_length_right p' i h_i_le
      have h_suffix_at_i_vertices :
          suffix_at_i_cast.vertices = p'.vertices.drop i := by
        show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2).vertices
            = p'.vertices.drop i
        rw [Walk.vertices_cast_source h_mid_i_eq]
        exact Walk.splitAt_vertices_right p' i h_i_le
      -- Decompose suffix_at_i_cast: first cons-cell.
      -- u ∈ G needed for the WalkStep extraction.
      have h_u_mem : u ∈ G := by
        have h_lt : (i + 1) < p'.vertices.length := by
          rw [Walk.vertices_length]; omega
        have h_in : u ∈ p'.vertices := by
          rw [List.getElem?_eq_getElem h_lt] at h_get_ip1
          have : u = p'.vertices[i + 1] := (Option.some.inj h_get_ip1).symm
          rw [this]
          exact List.getElem_mem _
        exact Walk.mem_of_mem_vertices p' h_in
      -- b'' ∈ G needed for various manipulations.
      have h_b''_mem : b'' ∈ G := by
        have h_lt : i < p'.vertices.length := by
          rw [Walk.vertices_length]; omega
        have h_in : b'' ∈ p'.vertices := by
          rw [List.getElem?_eq_getElem h_lt] at h_get_i
          have : b'' = p'.vertices[i] := (Option.some.inj h_get_i).symm
          rw [this]
          exact List.getElem_mem _
        exact Walk.mem_of_mem_vertices p' h_in
      -- Length ≥ 2.
      have h_suffix_at_i_len_ge_two : suffix_at_i_cast.length ≥ 2 := by
        rw [h_suffix_at_i_len]; omega
      -- ## Splice-boundary collider check: derive heads + use h_bif.
      --
      -- For p_collapsed.IsCollider i: assume it holds; via the two
      -- comp_at_p_length_no_head_* contrapositives, derive both
      -- prefix_walk.lastStepHeadAtTarget AND suffix_walk.firstStepHeadAtSource.
      -- Combined with h_bif's step_i.HeadAtSource and step_ip1.HeadAtTarget,
      -- derive p'.IsCollider i AND p'.IsCollider (i+2), getting
      -- b'' ∈ C via colliders-in-C, hence b'' ∈ G.AncSet C.
      --
      -- ## Splice-boundary blockable check (for σ-open clause 2).
      --
      -- Case-split on the disjunct of IsBlockableNonCollider on p_collapsed
      -- at i.  Each disjunct (k = length, HBLS_clean i, HBRS_clean i)
      -- transports to an IsBlockableNonCollider on p' at a related
      -- position (i+2 for length and HBRS; i for HBLS), where p's
      -- σ-open gives b'' ∉ C.  The k = 0 disjunct is excluded by k ≥ 1
      -- of the interior-σ-open requirement.

      -- ### Bifurcation flank heads extraction.
      --
      -- Use IsBifurcationFlankAt_comp_right to transport h_bif from p'
      -- to suffix_at_i_cast at position 1.
      have h_bif_at_suffix :
          suffix_at_i_cast.IsBifurcationFlankAt 1 := by
        have h_eq := Walk.splitAt_comp p' i h_i_le
        have h_le_lt : (p'.splitAt i h_i_le).2.1.length < i + 1 := by
          rw [Walk.splitAt_length_left]; omega
        have h_comp_eq :=
          Walk.IsBifurcationFlankAt_comp_right (p'.splitAt i h_i_le).2.1
            (p'.splitAt i h_i_le).2.2 (i + 1) h_le_lt
        rw [h_eq] at h_comp_eq
        rw [Walk.splitAt_length_left] at h_comp_eq
        -- h_comp_eq : p'.IsBifurcationFlankAt (i+1) =
        --             (p'.splitAt i h_i_le).2.2.IsBifurcationFlankAt (i + 1 - i)
        -- = (p'.splitAt i h_i_le).2.2.IsBifurcationFlankAt 1.
        have h_simp : i + 1 - i = 1 := by omega
        rw [h_simp] at h_comp_eq
        -- Connect via cast.
        have h_cast :
            (p'.splitAt i h_i_le).2.2.IsBifurcationFlankAt 1
              = suffix_at_i_cast.IsBifurcationFlankAt 1 := by
          show (p'.splitAt i h_i_le).2.2.IsBifurcationFlankAt 1
              = (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.2).IsBifurcationFlankAt 1
          rw [Walk.IsBifurcationFlankAt_cast_source h_mid_i_eq]
        rw [h_cast] at h_comp_eq
        rw [← h_comp_eq]
        exact h_bif
      -- Cons-decompose to extract step_i and step_ip1.
      cases h_decomp_1 : suffix_at_i_cast with
      | nil v hv =>
          exfalso
          rw [h_decomp_1] at h_suffix_at_i_len_ge_two
          simp [Walk.length] at h_suffix_at_i_len_ge_two
      | cons mid_at_ip1 step_i suffix_after_ip1 =>
          -- mid_at_ip1 should equal u.
          have h_mid_at_ip1_eq_u : mid_at_ip1 = u := by
            have h_vert_eq :
                suffix_at_i_cast.vertices
                  = (Walk.cons mid_at_ip1 step_i suffix_after_ip1).vertices := by
              rw [h_decomp_1]
            rw [h_suffix_at_i_vertices] at h_vert_eq
            -- h_vert_eq : p'.vertices.drop i = b'' :: suffix_after_ip1.vertices
            have h_idx :
                (p'.vertices.drop i)[1]?
                  = (Walk.cons mid_at_ip1 step_i suffix_after_ip1).vertices[1]? := by
              rw [h_vert_eq]
            rw [List.getElem?_drop] at h_idx
            change p'.vertices[i + 1]? = suffix_after_ip1.vertices[0]? at h_idx
            rw [h_get_ip1, Walk.vertices_zero_eq_source] at h_idx
            exact (Option.some.inj h_idx).symm
          -- `subst` with the .symm direction so we substitute mid_at_ip1 → u (keeping u).
          have h_u_eq_mid_at_ip1 : u = mid_at_ip1 := h_mid_at_ip1_eq_u.symm
          subst h_u_eq_mid_at_ip1
          -- Now step_i : WalkStep G b'' u, suffix_after_ip1 : Walk G u b'.
          -- Cons-decompose suffix_after_ip1.
          have h_suffix_after_ip1_len_ge_one :
              suffix_after_ip1.length ≥ 1 := by
            have h_total :
                (Walk.cons u step_i suffix_after_ip1 : Walk G b'' b').length
                  = suffix_after_ip1.length + 1 := by simp [Walk.length]
            rw [← h_decomp_1] at h_total
            rw [h_suffix_at_i_len] at h_total
            omega
          cases h_decomp_2 : suffix_after_ip1 with
          | nil v hv =>
              exfalso
              rw [h_decomp_2] at h_suffix_after_ip1_len_ge_one
              simp [Walk.length] at h_suffix_after_ip1_len_ge_one
          | cons mid_at_ip2 step_ip1 suffix_after_ip2 =>
              -- mid_at_ip2 should equal b''.
              have h_mid_at_ip2_eq_b'' : mid_at_ip2 = b'' := by
                have h_vert_eq :
                    suffix_at_i_cast.vertices
                      = (Walk.cons u step_i
                          (Walk.cons mid_at_ip2 step_ip1 suffix_after_ip2)).vertices := by
                  rw [h_decomp_1, h_decomp_2]
                rw [h_suffix_at_i_vertices] at h_vert_eq
                -- h_vert_eq : p'.vertices.drop i = [b''] ++ [u] ++ suffix_after_ip2.vertices_tail
                have h_idx :
                    (p'.vertices.drop i)[2]?
                      = (Walk.cons u step_i
                          (Walk.cons mid_at_ip2 step_ip1 suffix_after_ip2)).vertices[2]? := by
                  rw [h_vert_eq]
                rw [List.getElem?_drop] at h_idx
                change p'.vertices[i + 2]? = suffix_after_ip2.vertices[0]? at h_idx
                rw [h_get_ip2, Walk.vertices_zero_eq_source] at h_idx
                exact (Option.some.inj h_idx).symm
              -- `subst` with .symm direction to substitute mid_at_ip2 → b'' (keeping b'').
              have h_b''_eq_mid_at_ip2 : b'' = mid_at_ip2 := h_mid_at_ip2_eq_b''.symm
              subst h_b''_eq_mid_at_ip2
              -- Now step_ip1 : WalkStep G u b'', suffix_after_ip2 : Walk G b'' b'.
              -- Extract bifurcation flank heads from h_bif_at_suffix.
              rw [h_decomp_1, h_decomp_2] at h_bif_at_suffix
              -- h_bif_at_suffix has type:
              --   (Walk.cons u step_i (Walk.cons b'' step_ip1 suffix_after_ip2)).IsBifurcationFlankAt 1
              -- = step_i.HeadAtSource ∧ step_ip1.HeadAtTarget (by def at position 1 of cons-cons walk).
              change step_i.HeadAtSource ∧ step_ip1.HeadAtTarget at h_bif_at_suffix
              obtain ⟨h_step_i_src, h_step_ip1_tgt⟩ := h_bif_at_suffix
              -- ## Now derive p'.IsCollider i and p'.IsCollider (i+2) FROM the heads + suffix/prefix heads.
              -- These will be used at the splice-boundary collider transport.
              --
              -- Helper: relate suffix_at_i_cast's heads to (p'.splitAt i).2.2's heads
              -- (via cast invariance).
              have h_split_i_first_head :
                  (p'.splitAt i h_i_le).2.2.firstStepHeadAtSource
                    = step_i.HeadAtSource := by
                have h_cast :
                    (p'.splitAt i h_i_le).2.2.firstStepHeadAtSource
                      = suffix_at_i_cast.firstStepHeadAtSource := by
                  rw [← firstStepHeadAtSource_cast_source' h_mid_i_eq
                        (p'.splitAt i h_i_le).2.2]
                rw [h_cast, h_decomp_1]
                rfl
              -- Helper: relate the suffix-at-(i+1) for last-step queries.
              -- Hmm we instead need (p'.splitAt (i+2) h_ip2_le).2.1's lastStepHeadAtTarget.
              -- (p'.splitAt (i+2)).2.1 has length i+2 and last step is the step from
              -- position i+1 to position i+2 of p' = step_ip1 (after substitutions).
              -- This is harder to express directly; we use comp lemmas.

              -- ## Transport helpers (mirror collapse_u_self_loops, shift by 2 on the right).
              -- IsCollider transport at k < i.
              have h_col_lt : ∀ k, k < i →
                  p_collapsed.IsCollider k = p'.IsCollider k := fun k hk_lt => by
                show (prefix_walk.comp suffix_walk).IsCollider k = _
                rw [Walk.refactor_IsCollider_comp_left _ _ _
                    (h_prefix_len ▸ hk_lt)]
                show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).IsCollider k = _
                rw [Walk.refactor_IsCollider_cast_target h_mid_i_eq]
                conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
                rw [Walk.refactor_IsCollider_comp_left _ _ _
                    (by rw [Walk.splitAt_length_left]; exact hk_lt)]
              -- IsCollider transport at k > i.
              have h_col_gt : ∀ k, i < k →
                  p_collapsed.IsCollider k = p'.IsCollider (k + 2) := fun k hk_gt => by
                show (prefix_walk.comp suffix_walk).IsCollider k = _
                rw [Walk.refactor_IsCollider_comp_right _ _ _
                    (h_prefix_len ▸ hk_gt)]
                rw [h_prefix_len]
                show (h_mid_ip2_eq ▸ (p'.splitAt (i+2) h_ip2_le).2.2).IsCollider (k - i) = _
                rw [Walk.refactor_IsCollider_cast_source h_mid_ip2_eq]
                conv_rhs => rw [← Walk.splitAt_comp p' (i+2) h_ip2_le]
                rw [Walk.refactor_IsCollider_comp_right _ _ _
                    (by rw [Walk.splitAt_length_left]; omega)]
                rw [Walk.splitAt_length_left]
                congr 1; omega
              -- Vertex transport at k ≤ i.
              have h_v_le : ∀ k, k ≤ i →
                  p_collapsed.vertices[k]? = p'.vertices[k]? := fun k hk_le => by
                show (prefix_walk.comp suffix_walk).vertices[k]? = _
                rw [vertices_comp_left_le prefix_walk suffix_walk k
                    (h_prefix_len ▸ hk_le)]
                show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).vertices[k]? = _
                rw [Walk.vertices_cast_target h_mid_i_eq]
                rw [Walk.splitAt_vertices_left, List.getElem?_take,
                    if_pos (by omega)]
              -- Vertex transport at k > i.
              have h_v_gt : ∀ k, i < k →
                  p_collapsed.vertices[k]? = p'.vertices[k + 2]? := fun k hk_gt => by
                show (prefix_walk.comp suffix_walk).vertices[k]? = _
                conv_lhs => rw [show k = prefix_walk.length + (k - i)
                  from by rw [h_prefix_len]; omega]
                rw [Walk.vertices_comp_right_shift]
                show suffix_walk.vertices[k - i]? = _
                rw [h_suffix_vertices, List.getElem?_drop]
                congr 1; omega
              -- Vertex at splice position is b''.
              have h_v_at_i : p_collapsed.vertices[i]? = some b'' := by
                rw [h_v_le i le_rfl]; exact h_get_i
              -- HBLS transport at k ≤ i (uses ≤ since HBLS_comp_left takes ≤).
              have h_HBLS_le : ∀ k, k ≤ i →
                  p_collapsed.HasBlockingLeftSlot k
                    = p'.HasBlockingLeftSlot k := fun k hk_le => by
                show (prefix_walk.comp suffix_walk).HasBlockingLeftSlot k = _
                rw [Walk.HasBlockingLeftSlot_comp_left _ _ _
                    (h_prefix_len ▸ hk_le)]
                show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).HasBlockingLeftSlot k = _
                rw [Walk.HasBlockingLeftSlot_cast_target h_mid_i_eq]
                conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
                rw [Walk.HasBlockingLeftSlot_comp_left _ _ _
                    (by rw [Walk.splitAt_length_left]; exact hk_le)]
              -- HBLS transport at k > i.
              have h_HBLS_gt : ∀ k, i < k →
                  p_collapsed.HasBlockingLeftSlot k
                    = p'.HasBlockingLeftSlot (k + 2) := fun k hk_gt => by
                show (prefix_walk.comp suffix_walk).HasBlockingLeftSlot k = _
                rw [Walk.HasBlockingLeftSlot_comp_right _ _ _
                    (h_prefix_len ▸ hk_gt)]
                rw [h_prefix_len]
                show (h_mid_ip2_eq ▸ (p'.splitAt (i+2) h_ip2_le).2.2).HasBlockingLeftSlot (k - i) = _
                rw [Walk.HasBlockingLeftSlot_cast_source h_mid_ip2_eq]
                conv_rhs => rw [← Walk.splitAt_comp p' (i+2) h_ip2_le]
                rw [Walk.HasBlockingLeftSlot_comp_right _ _ _
                    (by rw [Walk.splitAt_length_left]; omega)]
                rw [Walk.splitAt_length_left]
                congr 1; omega
              -- HBRS transport at k < i.
              have h_HBRS_lt : ∀ k, k < i →
                  p_collapsed.HasBlockingRightSlot k
                    = p'.HasBlockingRightSlot k := fun k hk_lt => by
                show (prefix_walk.comp suffix_walk).HasBlockingRightSlot k = _
                rw [Walk.HasBlockingRightSlot_comp_left _ _ _
                    (h_prefix_len ▸ hk_lt)]
                show (h_mid_i_eq ▸ (p'.splitAt i h_i_le).2.1).HasBlockingRightSlot k = _
                rw [Walk.HasBlockingRightSlot_cast_target h_mid_i_eq]
                conv_rhs => rw [← Walk.splitAt_comp p' i h_i_le]
                rw [Walk.HasBlockingRightSlot_comp_left _ _ _
                    (by rw [Walk.splitAt_length_left]; exact hk_lt)]
              -- HBRS transport at k ≥ i (uses ≤ since HBRS_comp_right takes ≤).
              have h_HBRS_ge : ∀ k, i ≤ k →
                  p_collapsed.HasBlockingRightSlot k
                    = p'.HasBlockingRightSlot (k + 2) := fun k hk_ge => by
                show (prefix_walk.comp suffix_walk).HasBlockingRightSlot k = _
                rw [Walk.HasBlockingRightSlot_comp_right _ _ _
                    (h_prefix_len ▸ hk_ge)]
                rw [h_prefix_len]
                show (h_mid_ip2_eq ▸ (p'.splitAt (i+2) h_ip2_le).2.2).HasBlockingRightSlot (k - i) = _
                rw [Walk.HasBlockingRightSlot_cast_source h_mid_ip2_eq]
                conv_rhs => rw [← Walk.splitAt_comp p' (i+2) h_ip2_le]
                rw [Walk.HasBlockingRightSlot_comp_right _ _ _
                    (by rw [Walk.splitAt_length_left]; omega)]
                rw [Walk.splitAt_length_left]
                congr 1; omega
              -- ## p_collapsed satisfies the input invariants for the IH.
              -- u-non-collider on p_collapsed.
              have h_collapsed_noncoll : ∀ k,
                  p_collapsed.vertices[k]? = some u →
                  p_collapsed.IsNonCollider k := by
                intros k h_get_k
                rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
                · -- k < i: vertex transport via h_v_le.
                  rw [h_v_le k hk_lt.le] at h_get_k
                  have h_p'_noncoll := h_noncoll' k h_get_k
                  refine ⟨?_, ?_⟩
                  · -- k ≤ p_collapsed.length.
                    rw [h_collapsed_len]
                    have h_p'_kle := h_p'_noncoll.1
                    omega
                  · -- ¬ p_collapsed.IsCollider k via h_col_lt.
                    rw [h_col_lt k hk_lt]
                    exact h_p'_noncoll.2
                · -- k = i: vertex is b''.  If b'' = u, contradicts no-consecutive-u
                  -- on p' at position k (= i): vertex k = b'' = u and vertex k+1 = u.
                  -- (Note: `rfl` in rcases substituted `i := k`, eliminating `i`; use `k`.)
                  exfalso
                  rw [h_v_at_i] at h_get_k
                  have h_eq : b'' = u := Option.some.inj h_get_k
                  rw [h_eq] at h_get_i
                  exact h_no_cons_u' k h_get_i h_get_ip1
                · -- k > i: vertex transport via h_v_gt.
                  rw [h_v_gt k hk_gt] at h_get_k
                  have h_p'_noncoll := h_noncoll' (k + 2) h_get_k
                  refine ⟨?_, ?_⟩
                  · -- k ≤ p_collapsed.length.
                    rw [h_collapsed_len]
                    have h_p'_kle := h_p'_noncoll.1
                    omega
                  · -- ¬ p_collapsed.IsCollider k via h_col_gt.
                    rw [h_col_gt k hk_gt]
                    exact h_p'_noncoll.2
              -- no-consecutive-u on p_collapsed.
              have h_collapsed_no_cons_u : ∀ k,
                  p_collapsed.vertices[k]? = some u →
                  p_collapsed.vertices[k+1]? ≠ some u := by
                intros k h_get_k h_get_kp1
                -- Transport to p' and use h_no_cons_u'.
                rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
                · -- k < i. k+1 ≤ i: by k < i.
                  rw [h_v_le k hk_lt.le] at h_get_k
                  by_cases h_kp1_lt : k + 1 < i
                  · rw [h_v_le (k+1) hk_lt] at h_get_kp1
                    exact h_no_cons_u' k h_get_k h_get_kp1
                  · -- k + 1 = i.
                    have h_kp1_eq_i : k + 1 = i := by omega
                    rw [h_kp1_eq_i, h_v_at_i] at h_get_kp1
                    -- p_collapsed.vertices[i]? = some b'' = some u.
                    have h_b''_eq_u : b'' = u := Option.some.inj h_get_kp1
                    -- Then h_get_i = some b'' = some u. But p'.vertices[i+1] = some u
                    -- and h_no_cons_u' applied at position i would give contradiction.
                    rw [h_b''_eq_u] at h_get_i
                    exact h_no_cons_u' i h_get_i h_get_ip1
                · -- k = i. Vertex at k (= i) is b''. h_get_k says b'' = u.
                  -- (Note: `rfl` substituted `i := k`, eliminating `i`; use `k`.)
                  rw [h_v_at_i] at h_get_k
                  have h_b''_eq_u : b'' = u := Option.some.inj h_get_k
                  rw [h_b''_eq_u] at h_get_i
                  exact h_no_cons_u' k h_get_i h_get_ip1
                · -- k > i.
                  rw [h_v_gt k hk_gt] at h_get_k
                  -- k + 1 > i, transport via h_v_gt.
                  have h_kp1_gt : i < k + 1 := by omega
                  rw [h_v_gt (k+1) h_kp1_gt] at h_get_kp1
                  -- p'.vertices[k+2] = some u and p'.vertices[k+1+2] = some u.
                  -- Apply h_no_cons_u' at k+2.
                  exact h_no_cons_u' (k+2) h_get_k h_get_kp1
              -- colliders-in-C on p_collapsed.
              have h_collapsed_colC : ∀ k vk,
                  p_collapsed.vertices[k]? = some vk →
                  p_collapsed.IsCollider k → vk ∈ C := by
                intros k vk h_get_k h_col_k
                rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
                · -- k < i.
                  rw [h_v_le k hk_lt.le] at h_get_k
                  rw [h_col_lt k hk_lt] at h_col_k
                  exact h_colC' k vk h_get_k h_col_k
                · -- k = i.  The substantive case (note: `rfl` substituted `i := k`).
                  -- p_collapsed.IsCollider k derives prefix.lastStepHeadAtTarget AND
                  -- suffix.firstStepHeadAtSource via the comp_at_p_length_no_head
                  -- contrapositives.
                  rw [h_v_at_i] at h_get_k
                  have h_vk_eq_b'' : vk = b'' := (Option.some.inj h_get_k).symm
                  -- Reframe p_collapsed.IsCollider k as IsCollider at prefix_walk.length.
                  have h_col_at_plen :
                      (prefix_walk.comp suffix_walk).IsCollider prefix_walk.length := by
                    rw [h_prefix_len]; exact h_col_k
                  have h_prefix_last : prefix_walk.lastStepHeadAtTarget := by
                    by_contra h_no
                    exact Walk.refactor_IsCollider_comp_at_p_length_no_head_target
                      prefix_walk suffix_walk h_no h_col_at_plen
                  have h_suffix_first : suffix_walk.firstStepHeadAtSource := by
                    by_contra h_no
                    exact Walk.refactor_IsCollider_comp_at_p_length_no_head_source
                      prefix_walk suffix_walk h_no h_col_at_plen
                  -- Show p'.IsCollider k: combine h_prefix_last with h_step_i_src.
                  have h_prefix_last_split :
                      (p'.splitAt k h_i_le).2.1.lastStepHeadAtTarget := by
                    rw [← lastStepHeadAtTarget_cast_target' h_mid_i_eq
                          (p'.splitAt k h_i_le).2.1]
                    exact h_prefix_last
                  have h_split_i_suf_first :
                      (p'.splitAt k h_i_le).2.2.firstStepHeadAtSource := by
                    rw [h_split_i_first_head]
                    exact h_step_i_src
                  have h_p'_col_i : p'.IsCollider k := by
                    have h_of_heads :=
                      Walk.refactor_IsCollider_comp_at_p_length_of_heads
                        (p'.splitAt k h_i_le).2.1 (p'.splitAt k h_i_le).2.2
                        h_prefix_last_split h_split_i_suf_first
                    rw [Walk.splitAt_comp, Walk.splitAt_length_left] at h_of_heads
                    exact h_of_heads
                  have h_b''_in_C : b'' ∈ C :=
                    h_colC' k b'' h_get_i h_p'_col_i
                  rw [h_vk_eq_b'']
                  exact h_b''_in_C
                · -- k > i.
                  rw [h_v_gt k hk_gt] at h_get_k
                  rw [h_col_gt k hk_gt] at h_col_k
                  exact h_colC' (k + 2) vk h_get_k h_col_k
              -- σ-open of p_collapsed at interior.
              have h_collapsed_sigma : IsSigmaOpenAtInterior p_collapsed C hC_G := by
                refine ⟨?_, ?_⟩
                · -- Collider clause.
                  intros k vk h_get_k h_col_k
                  rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
                  · -- k < i.
                    rw [h_v_le k hk_lt.le] at h_get_k
                    rw [h_col_lt k hk_lt] at h_col_k
                    exact h_sigma'.1 k vk h_get_k h_col_k
                  · -- k = i: the substantive case (rfl substituted i := k).
                    -- p_collapsed.IsCollider k → b'' ∈ C (via h_collapsed_colC) → b'' ∈ AncSet C.
                    rw [h_v_at_i] at h_get_k
                    have h_vk_eq_b'' : vk = b'' := (Option.some.inj h_get_k).symm
                    -- Derive via colliders-in-C transport above.
                    have h_b''_in_C := h_collapsed_colC k b'' h_v_at_i h_col_k
                    -- b'' ∈ G.AncSet C from b'' ∈ C trivially via the self-ancestor.
                    rw [h_vk_eq_b'']
                    show b'' ∈ G.AncSet C
                    unfold CDMG.AncSet
                    simp only [Set.mem_iUnion]
                    refine ⟨b'', h_b''_in_C, ?_⟩
                    refine ⟨h_b''_mem, ?_⟩
                    refine ⟨Walk.nil b'' h_b''_mem, trivial⟩
                  · -- k > i.
                    rw [h_v_gt k hk_gt] at h_get_k
                    rw [h_col_gt k hk_gt] at h_col_k
                    exact h_sigma'.1 (k + 2) vk h_get_k h_col_k
                · -- Blockable clause.
                  intros k vk h_get_k h_blk_k h_pos
                  rcases lt_trichotomy k i with hk_lt | rfl | hk_gt
                  · -- k < i: transport.
                    rw [h_v_le k hk_lt.le] at h_get_k
                    have h_blk' : p'.IsBlockableNonCollider k := by
                      refine ⟨⟨?_, ?_⟩, ?_⟩
                      · -- k ≤ p'.length.
                        have h_p'_pos : k ≤ p_collapsed.length := h_blk_k.1.1
                        rw [h_collapsed_len] at h_p'_pos
                        omega
                      · -- ¬ p'.IsCollider k.
                        rw [← h_col_lt k hk_lt]
                        exact h_blk_k.1.2
                      · rcases h_blk_k.2 with hk0 | hk_len | h_hbls | h_hbrs
                        · exact Or.inl hk0
                        · -- k = p_collapsed.length excluded by k < i ≤ p_collapsed.length.
                          exfalso
                          rw [h_collapsed_len] at hk_len
                          omega
                        · refine Or.inr (Or.inr (Or.inl ?_))
                          rw [← h_HBLS_le k hk_lt.le]
                          exact h_hbls
                        · refine Or.inr (Or.inr (Or.inr ?_))
                          rw [← h_HBRS_lt k hk_lt]
                          exact h_hbrs
                    exact h_sigma'.2 k vk h_get_k h_blk' h_pos
                  · -- k = i.  The substantive case.
                    rw [h_v_at_i] at h_get_k
                    have h_vk_eq_b'' : vk = b'' := (Option.some.inj h_get_k).symm
                    rw [h_vk_eq_b'']
                    -- Case-analyze on the disjunct of h_blk_k.
                    -- (Note: `rfl` substituted `i := k`, eliminating `i`; use `k`.)
                    rcases h_blk_k.2 with hk0 | hk_len | h_hbls | h_hbrs
                    · -- k = 0: excluded by h_pos : 1 ≤ k.
                      exfalso; omega
                    · -- k = p_collapsed.length, so k+2 = p'.length.
                      rw [h_collapsed_len] at hk_len
                      have h_kp2_eq : k + 2 = p'.length := by omega
                      -- Apply σ-open of p' at k+2.
                      have h_p'_blk : p'.IsBlockableNonCollider (k + 2) := by
                        refine ⟨⟨?_, ?_⟩, ?_⟩
                        · omega
                        · -- ¬ p'.IsCollider (k+2): at position p'.length, IsCollider = False.
                          rw [h_kp2_eq]
                          intro h_col
                          exact Walk.refactor_IsCollider_length_eq_False p' h_col
                        · -- Disjunct via k+2 = p'.length.
                          exact Or.inr (Or.inl h_kp2_eq)
                      have h_pos' : (1 : ℕ) ≤ k + 2 := by omega
                      exact h_sigma'.2 (k + 2) b'' h_get_ip2 h_p'_blk h_pos'
                    · -- HBLS_clean k fires.
                      have h_HBLS_p_k : p'.HasBlockingLeftSlot k := by
                        rw [← h_HBLS_le k le_rfl]; exact h_hbls
                      -- HBLS_p_k → step k-1 of p' is .backwardE → ¬IsCollider at k on p'.
                      have h_p'_noncol_k : ¬ p'.IsCollider k := by
                        intro h_col
                        exact Walk.HBLS_not_IsCollider p' k h_HBLS_p_k h_col
                      have h_p'_blk : p'.IsBlockableNonCollider k := by
                        refine ⟨⟨?_, h_p'_noncol_k⟩, ?_⟩
                        · -- k ≤ p'.length.
                          exact h_i_le
                        · -- Disjunct via HBLS_p k.
                          exact Or.inr (Or.inr (Or.inl h_HBLS_p_k))
                      exact h_sigma'.2 k b'' h_get_i h_p'_blk h_pos
                    · -- HBRS_clean k fires.
                      have h_HBRS_p_kp2 : p'.HasBlockingRightSlot (k + 2) := by
                        rw [← h_HBRS_ge k le_rfl]; exact h_hbrs
                      -- HBRS_p_(k+2) → step k+2 of p' is .forwardE → ¬IsCollider at k+2 on p'.
                      have h_p'_noncol_kp2 : ¬ p'.IsCollider (k + 2) := by
                        intro h_col
                        exact Walk.HBRS_not_IsCollider p' (k + 2) h_HBRS_p_kp2 h_col
                      have h_p'_blk : p'.IsBlockableNonCollider (k + 2) := by
                        refine ⟨⟨?_, h_p'_noncol_kp2⟩, ?_⟩
                        · -- k+2 ≤ p'.length.
                          exact h_ip2_le
                        · -- Disjunct via HBRS_p (k+2).
                          exact Or.inr (Or.inr (Or.inr h_HBRS_p_kp2))
                      have h_pos' : (1 : ℕ) ≤ k + 2 := by omega
                      exact h_sigma'.2 (k + 2) b'' h_get_ip2 h_p'_blk h_pos'
                  · -- k > i.
                    rw [h_v_gt k hk_gt] at h_get_k
                    have h_blk' : p'.IsBlockableNonCollider (k + 2) := by
                      refine ⟨⟨?_, ?_⟩, ?_⟩
                      · -- (k+2) ≤ p'.length.
                        have h_p'_pos : k ≤ p_collapsed.length := h_blk_k.1.1
                        rw [h_collapsed_len] at h_p'_pos
                        omega
                      · rw [← h_col_gt k hk_gt]
                        exact h_blk_k.1.2
                      · rcases h_blk_k.2 with hk0 | hk_len | h_hbls | h_hbrs
                        · -- k = 0 excluded by i < k.
                          exfalso; omega
                        · -- k = p_collapsed.length → k+2 = p'.length.
                          refine Or.inr (Or.inl ?_)
                          rw [h_collapsed_len] at hk_len
                          omega
                        · refine Or.inr (Or.inr (Or.inl ?_))
                          rw [← h_HBLS_gt k hk_gt]
                          exact h_hbls
                        · refine Or.inr (Or.inr (Or.inr ?_))
                          rw [← h_HBRS_ge k hk_gt.le]
                          exact h_hbrs
                    have h_pos' : (1 : ℕ) ≤ k + 2 := by omega
                    exact h_sigma'.2 (k + 2) vk h_get_k h_blk' h_pos'
              -- ## Apply IH on p_collapsed.
              obtain ⟨p_clean, h_clean_noncoll, h_clean_no_cons_u,
                      h_clean_no_bif, h_clean_colC, h_clean_sigma⟩ :=
                ih p_collapsed.length h_collapsed_lt_n p_collapsed rfl ha' hb'
                  h_collapsed_noncoll h_collapsed_no_cons_u h_collapsed_colC
                  h_collapsed_sigma
              exact ⟨p_clean, h_clean_noncoll, h_clean_no_cons_u,
                     h_clean_no_bif, h_clean_colC, h_clean_sigma⟩
    · -- Case 2: no bifurcation side-trip on p'.  Return p' directly.
      refine ⟨p', h_noncoll', h_no_cons_u', ?_, h_colC', h_sigma'⟩
      intros j v h_get_j h_get_jp1 h_get_jp2 h_bif
      apply h_st
      refine ⟨j, v, ?_, h_get_j, h_get_jp1, h_get_jp2, h_bif⟩
      -- Derive j + 2 ≤ p'.length from h_get_jp2.
      by_contra h_too_big
      push_neg at h_too_big
      have h_vlen : p'.vertices.length = p'.length + 1 := Walk.vertices_length p'
      have h_ge : p'.vertices.length ≤ j + 2 := by rw [h_vlen]; omega
      rw [List.getElem?_eq_none h_ge] at h_get_jp2
      cases h_get_jp2

-- ## ref: claim_3_25 (Subtask 7c) — reverse-direction IsLift existence.
--
-- The mirror of `exists_isLift_of_walk_marg` (line 2209): given a
-- G-walk `p` satisfying the preprocessing invariants output by
-- Subtasks 7a + 7a-2 (u-non-collider at every u-visit, no consecutive
-- u, and no bifurcation side-trip at u), exhibit a marg-walk `p'`
-- together with an `IsLift G u hu p' p` proof.  This is the gateway
-- to the entire reverse direction of `iSigmaSeparation_marginalize_iff`:
-- once we have the IsLift, downstream subtasks (8-11) transport
-- σ-open, colliders-in-C, and ancestor structure across the lift to
-- conclude σ-blocking on the G side from σ-blocking on the marg side.
--
-- ## Design choice — strong induction on length (not structural).
--
-- `exists_isLift_of_walk_marg`'s structural-recursion template does
-- not work here.  In the `mid = u` branch, we must recurse on
-- `p_tail_inner` (the walk-tail two cons-cells deep), not on
-- `p_tail` (one cons-cell deep).  The structural IH would give only
-- the latter, and `p_tail`'s source is `u`, violating the IH's
-- `a ≠ u` hypothesis.  Strong induction on length lets us recurse on
-- any sub-walk with strictly smaller length, both in the `mid = u`
-- 2-edge branch (length n-2 sub-walk) and the `mid ≠ u` 1-edge branch
-- (length n-1 sub-walk).
--
-- ## Design choice — side-trip dispatch via `NoBifurcationSideTrip`.
--
-- When `mid = u` and `a' = mid'` (the side-trip case where the walk
-- visits `u` and returns to the same source vertex), `walkstep_lift_two_edge`
-- cannot be applied directly because its `hne : a ≠ mid` hypothesis
-- fails.  The `NoBifurcationSideTrip` invariant (from Subtask 7a-2)
-- rules out the 3 bifurcation patterns ((backwardE, forwardE),
-- (bidir, forwardE), (backwardE, bidir)) at the `(a', u, a')` flank
-- pattern; combined with the u-non-collider `hNonColl` ruling out
-- the 4 collider patterns, only the 2 directed-pass-through patterns
-- ((forwardE, forwardE), (backwardE, backwardE)) remain.  In each
-- of those, we construct a marg-E self-loop `(a', a') ∈ marg.E` via
-- a 2-edge Φ_E witness `a' → u → a'` and assemble `IsLift.cons_two_edge`
-- as in the standard 2-edge case (with `hSrc = hTgt = Iff.rfl` since
-- both `s'` and the marg-self-loop's WalkStep share the same
-- arrowhead profile by construction).
private lemma exists_isLift_of_walk_G
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V) :
    ∀ {a b : Node} (p : Walk G a b),
      a ≠ u → b ≠ u →
      (∀ k, p.vertices[k]? = some u → p.IsNonCollider k) →
      (∀ k, p.vertices[k]? = some u → p.vertices[k+1]? ≠ some u) →
      NoBifurcationSideTrip p u →
      ∃ p' : Walk (G.marginalize {u} hu) a b, IsLift G u hu p' p := by
  -- Strong induction on length, since the side-trip case recurses two
  -- cons-cells deep rather than one (so we cannot use structural induction).
  suffices aux :
      ∀ (n : ℕ), ∀ {a' b' : Node} (p' : Walk G a' b'), p'.length = n →
        a' ≠ u → b' ≠ u →
        (∀ k, p'.vertices[k]? = some u → p'.IsNonCollider k) →
        (∀ k, p'.vertices[k]? = some u → p'.vertices[k+1]? ≠ some u) →
        NoBifurcationSideTrip p' u →
        ∃ p'' : Walk (G.marginalize {u} hu) a' b', IsLift G u hu p'' p' by
    intro a b p ha hb h_nc h_no_cons h_no_bif
    exact aux p.length p rfl ha hb h_nc h_no_cons h_no_bif
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intros a' b' p' h_len ha' hb' h_nc' h_no_cons' h_no_bif'
    cases p' with
    | nil _ hv_G =>
        -- a' (= b') ≠ u, so a' ∈ G.J ∪ (G.V \ {u}) = marg.carrier.
        have hv_marg : a' ∈ G.marginalize {u} hu := by
          change a' ∈ G.J ∪ (G.V \ ({u} : Finset Node))
          rcases Finset.mem_union.mp hv_G with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · refine Finset.mem_union_right _ ?_
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨hV, ha'⟩
        exact ⟨Walk.nil a' hv_marg, IsLift.nil_lift hv_marg hv_G⟩
    | @cons _ _ mid s' p_tail =>
        by_cases h_mid : mid = u
        · -- Case mid = u.  Sub-extract p_tail = cons mid' s₂ p_tail_inner.
          -- Subst .symm to substitute mid → u (keeping u), not the default
          -- direction (which would eliminate u; see 7a's pattern at line 2430).
          have h_u_eq_mid : u = mid := h_mid.symm
          subst h_u_eq_mid
          cases p_tail with
          | nil v hv =>
              -- nil forces b' = u, contradicting hb'.
              exact absurd rfl hb'
          | @cons _ _ mid' s₂ p_tail_inner =>
              -- Establish mid' ≠ u from h_no_cons' at position 1.
              have h_get1_u :
                  (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).vertices[1]?
                    = some u := rfl
              have h_get2_eq_mid' :
                  (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).vertices[2]?
                    = some mid' :=
                Walk.vertices_zero_eq_source' p_tail_inner
              have h_mid'_ne_u : mid' ≠ u := by
                intro h_eq
                apply h_no_cons' 1 h_get1_u
                rw [h_get2_eq_mid', h_eq]
              -- hNonColl : ¬(s'.HeadAtTarget ∧ s₂.HeadAtSource) from u-non-collider at 1.
              have h_p_nc_1 :
                  (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).IsNonCollider 1
                  := h_nc' 1 h_get1_u
              have hNonColl :
                  ¬ (s'.HeadAtTarget ∧ s₂.HeadAtSource) := h_p_nc_1.2
              -- Length info for IH.
              have h_inner_lt : p_tail_inner.length < n := by
                have h_len_eq :
                    (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).length
                      = p_tail_inner.length + 2 := rfl
                omega
              -- p_tail_inner's u-non-collider invariant (position shift by 2).
              have h_nc_inner :
                  ∀ k, p_tail_inner.vertices[k]? = some u →
                    p_tail_inner.IsNonCollider k := by
                intro k hk_inner
                have hk_p :
                    (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).vertices[k+2]?
                      = some u := hk_inner
                have h_nc_kp2 := h_nc' (k+2) hk_p
                refine ⟨?_, ?_⟩
                · have h1 := h_nc_kp2.1
                  have h_len_eq :
                      (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).length
                        = p_tail_inner.length + 2 := rfl
                  omega
                · intro h_coll_inner
                  apply h_nc_kp2.2
                  cases p_tail_inner with
                  | nil _ _ =>
                      exact absurd h_coll_inner (by cases k <;> exact id)
                  | cons mid_i s_i p_i =>
                      cases k with
                      | zero =>
                          rw [isCollider_cons_zero_eq_false s_i p_i] at h_coll_inner
                          exact h_coll_inner.elim
                      | succ k' =>
                          cases s' <;> cases s₂ <;> exact h_coll_inner
              -- p_tail_inner's no-consecutive-u invariant.
              have h_no_cons_inner :
                  ∀ k, p_tail_inner.vertices[k]? = some u →
                    p_tail_inner.vertices[k+1]? ≠ some u := by
                intro k hk h_kp1
                exact h_no_cons' (k+2) hk h_kp1
              -- p_tail_inner's no-bifurcation-side-trip invariant.
              have h_no_bif_inner : NoBifurcationSideTrip p_tail_inner u := by
                intro i v h_i h_ip1 h_ip2 h_bif
                apply h_no_bif' (i+2) v h_i h_ip1 h_ip2
                cases p_tail_inner with
                | nil _ _ => exact h_bif.elim
                | cons _ _ _ => cases s' <;> cases s₂ <;> exact h_bif
              -- Recurse on p_tail_inner.
              obtain ⟨p_lift_inner, htail⟩ :=
                ih p_tail_inner.length h_inner_lt p_tail_inner rfl
                  h_mid'_ne_u hb' h_nc_inner h_no_cons_inner h_no_bif_inner
              -- Side-trip dispatch.
              by_cases h_st : a' = mid'
              · -- Side-trip: a' = mid'.  After subst, mid' becomes a'.
                subst h_st
                -- ¬IsBifurcationFlankAt 1 from h_no_bif' at position 0.
                have h_get0_a :
                    (Walk.cons u s' (Walk.cons a' s₂ p_tail_inner)).vertices[0]?
                      = some a' := rfl
                have h_get2_a :
                    (Walk.cons u s' (Walk.cons a' s₂ p_tail_inner)).vertices[2]?
                      = some a' :=
                  Walk.vertices_zero_eq_source' p_tail_inner
                have h_not_bif :
                    ¬ (Walk.cons u s' (Walk.cons a' s₂ p_tail_inner)).IsBifurcationFlankAt 1 :=
                  h_no_bif' 0 a' h_get0_a h_get1_u h_get2_a
                -- Of the 9 patterns: only (forwardE, forwardE) and
                -- (backwardE, backwardE) survive hNonColl + h_not_bif.
                cases s' with
                | forwardE h₁ =>
                    cases s₂ with
                    | forwardE h₂ =>
                        -- (forwardE, forwardE) side-trip: marg-E self-loop (a', a').
                        have h_a_GV : a' ∈ G.V := (G.hE_subset h₂).2
                        have h_a_marg :
                            a' ∈ G.V \ ({u} : Finset Node) := by
                          rw [Finset.mem_sdiff, Finset.mem_singleton]
                          exact ⟨h_a_GV, ha'⟩
                        have h_a_carrier :
                            a' ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                          Finset.mem_union_right _ h_a_marg
                        have h_a_G : a' ∈ G :=
                          Finset.mem_union_right _ h_a_GV
                        have h_marg_E :
                            (a', a') ∈ (G.marginalize {u} hu).E := by
                          change (a', a') ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                                  (G.V \ ({u} : Finset Node))).filter
                                (fun e => G.MarginalizationΦE {u} e.1 e.2)
                          refine Finset.mem_filter.mpr
                            ⟨Finset.mem_product.mpr
                              ⟨h_a_carrier, h_a_marg⟩, ?_⟩
                          refine ⟨Walk.cons u (.forwardE h₁)
                                    (Walk.cons a' (.forwardE h₂)
                                      (.nil a' h_a_G)),
                                  ?_, ?_, ?_⟩
                          · exact True.intro
                          · exact Nat.le_add_left 1 1
                          · intro x hx
                            have h_eq : x = u := by
                              simpa only [Walk.vertices, List.tail_cons,
                                List.dropLast_cons_of_ne_nil, List.dropLast,
                                List.mem_singleton] using hx
                            exact Finset.mem_singleton.mpr h_eq
                        refine ⟨Walk.cons a' (.forwardE h_marg_E) p_lift_inner, ?_⟩
                        exact IsLift.cons_two_edge (.forwardE h_marg_E)
                          p_lift_inner (.forwardE h₁) (.forwardE h₂)
                          p_tail_inner Iff.rfl Iff.rfl hNonColl htail
                    | backwardE _ =>
                        exact (hNonColl ⟨trivial, trivial⟩).elim
                    | bidir _ =>
                        exact (hNonColl ⟨trivial, trivial⟩).elim
                | backwardE h₁ =>
                    cases s₂ with
                    | forwardE _ =>
                        exact (h_not_bif ⟨trivial, trivial⟩).elim
                    | backwardE h₂ =>
                        -- (backwardE, backwardE) side-trip: marg-E self-loop (a', a').
                        have h_a_GV : a' ∈ G.V := (G.hE_subset h₁).2
                        have h_a_marg :
                            a' ∈ G.V \ ({u} : Finset Node) := by
                          rw [Finset.mem_sdiff, Finset.mem_singleton]
                          exact ⟨h_a_GV, ha'⟩
                        have h_a_carrier :
                            a' ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                          Finset.mem_union_right _ h_a_marg
                        have h_a_G : a' ∈ G :=
                          Finset.mem_union_right _ h_a_GV
                        have h_marg_E :
                            (a', a') ∈ (G.marginalize {u} hu).E := by
                          change (a', a') ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                                  (G.V \ ({u} : Finset Node))).filter
                                (fun e => G.MarginalizationΦE {u} e.1 e.2)
                          refine Finset.mem_filter.mpr
                            ⟨Finset.mem_product.mpr
                              ⟨h_a_carrier, h_a_marg⟩, ?_⟩
                          refine ⟨Walk.cons u (.forwardE h₂)
                                    (Walk.cons a' (.forwardE h₁)
                                      (.nil a' h_a_G)),
                                  ?_, ?_, ?_⟩
                          · exact True.intro
                          · exact Nat.le_add_left 1 1
                          · intro x hx
                            have h_eq : x = u := by
                              simpa only [Walk.vertices, List.tail_cons,
                                List.dropLast_cons_of_ne_nil, List.dropLast,
                                List.mem_singleton] using hx
                            exact Finset.mem_singleton.mpr h_eq
                        refine ⟨Walk.cons a' (.backwardE h_marg_E) p_lift_inner, ?_⟩
                        exact IsLift.cons_two_edge (.backwardE h_marg_E)
                          p_lift_inner (.backwardE h₁) (.backwardE h₂)
                          p_tail_inner Iff.rfl Iff.rfl hNonColl htail
                    | bidir _ =>
                        exact (h_not_bif ⟨trivial, trivial⟩).elim
                | bidir _ =>
                    cases s₂ with
                    | forwardE _ =>
                        exact (h_not_bif ⟨trivial, trivial⟩).elim
                    | backwardE _ =>
                        exact (hNonColl ⟨trivial, trivial⟩).elim
                    | bidir _ =>
                        exact (hNonColl ⟨trivial, trivial⟩).elim
              · -- Standard 2-edge case: a' ≠ mid'.
                obtain ⟨s_marg, hSrc, hTgt⟩ :=
                  walkstep_lift_two_edge u hu ha' h_mid'_ne_u h_st s' s₂ hNonColl
                refine ⟨Walk.cons mid' s_marg p_lift_inner, ?_⟩
                exact IsLift.cons_two_edge s_marg p_lift_inner s' s₂
                  p_tail_inner hSrc.symm hTgt.symm hNonColl htail
        · -- Case mid ≠ u: 1-edge dispatch via walkstep_lift_one_edge.
          have h_tail_lt : p_tail.length < n := by
            have h_len_eq :
                (Walk.cons mid s' p_tail).length = p_tail.length + 1 := rfl
            omega
          have h_nc_tail :
              ∀ k, p_tail.vertices[k]? = some u →
                p_tail.IsNonCollider k := by
            intro k hk_tail
            have hk_p :
                (Walk.cons mid s' p_tail).vertices[k+1]? = some u := hk_tail
            have h_nc_kp1 := h_nc' (k+1) hk_p
            refine ⟨?_, ?_⟩
            · have h1 := h_nc_kp1.1
              have h_len_eq :
                  (Walk.cons mid s' p_tail).length = p_tail.length + 1 := rfl
              omega
            · intro h_coll_tail
              apply h_nc_kp1.2
              cases p_tail with
              | nil _ _ =>
                  exact absurd h_coll_tail (by cases k <;> exact id)
              | cons mid_t s_t p_t =>
                  cases k with
                  | zero =>
                      rw [isCollider_cons_zero_eq_false s_t p_t] at h_coll_tail
                      exact h_coll_tail.elim
                  | succ k' =>
                      cases s' <;> exact h_coll_tail
          have h_no_cons_tail :
              ∀ k, p_tail.vertices[k]? = some u →
                p_tail.vertices[k+1]? ≠ some u := by
            intro k hk h_kp1
            exact h_no_cons' (k+1) hk h_kp1
          have h_no_bif_tail : NoBifurcationSideTrip p_tail u := by
            intro i v h_i h_ip1 h_ip2 h_bif
            apply h_no_bif' (i+1) v h_i h_ip1 h_ip2
            cases p_tail with
            | nil _ _ => exact h_bif.elim
            | cons _ _ _ => cases s' <;> exact h_bif
          obtain ⟨p_lift_tail, htail⟩ :=
            ih p_tail.length h_tail_lt p_tail rfl h_mid hb' h_nc_tail
              h_no_cons_tail h_no_bif_tail
          obtain ⟨s_marg, hSrc, hTgt⟩ :=
            walkstep_lift_one_edge u hu ha' h_mid s'
          refine ⟨Walk.cons mid s_marg p_lift_tail, ?_⟩
          exact IsLift.cons_one_edge s_marg p_lift_tail s' p_tail
            hSrc.symm hTgt.symm htail

-- ## ref: claim_3_25 (Subtask 6c helper) — interior σ-open + source ∉ C
-- ⟹ full σ-open.
--
-- The reverse re-assembly: restoring full σ-open from interior σ-open
-- requires re-adding the position-0 blockable clause, i.e.\ the
-- source vertex ∉ C constraint.  Used at the bottom of
-- `sigma_open_lift_marg_one` to reassemble the σ-open output from the
-- interior-σ-open output of the recursive lift.
private lemma sigma_open_of_interior_of_source_notC
    {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (C : Set Node) (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hp_int : IsSigmaOpenAtInterior p C hC)
    (h_src_notC : u ∉ C) :
    p.IsSigmaOpenGiven C hC := by
  refine ⟨hp_int.1, ?_⟩
  intro k vk hk h_blk
  by_cases hk0 : k = 0
  · -- Position 0: vertex is the source `u`.
    subst hk0
    have h_eq : (some u : Option Node) = some vk :=
      (Walk.vertices_zero_eq_source' p).symm.trans hk
    have : u = vk := Option.some.inj h_eq
    exact this ▸ h_src_notC
  · -- Position k ≥ 1: use the interior-blockable clause.
    exact hp_int.2 k vk hk h_blk (Nat.pos_of_ne_zero hk0)

-- ## ref: claim_3_25 (Subtask 6e) — nil-case branch of the σ-open' lift.
--
-- Trivial: a length-0 walk has no colliders (`isCollider_nil_eq_false`)
-- and no positions with `k ≥ 1` (the blockable clause is vacuous via
-- `IsNonCollider`'s `k ≤ length = 0` first conjunct).
private lemma sigma_open_interior_lift_nil_case
    {G : CDMG Node} (v : Node) (hv_G : v ∈ G)
    (C : Set Node) (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V) :
    IsSigmaOpenAtInterior (Walk.nil v hv_G) C hC_G := by
  refine ⟨?_, ?_⟩
  · intro k vk _ h_coll
    rw [isCollider_nil_eq_false hv_G] at h_coll
    exact h_coll.elim
  · intro k vk _ h_blk h_pos
    obtain ⟨h_nc, _⟩ := h_blk
    have h_len : k ≤ (Walk.nil v hv_G : Walk G v v).length := h_nc.1
    simp [Walk.length] at h_len
    omega

-- ## ref: claim_3_25 (Subtask 6e) — cons_one_edge case, collider clause.
--
-- For the outer `cons mid s' p_tail` lift of `cons mid s p''`:
--   * position 0: `IsCollider 0` on a cons-cons is False (vacuous).
--   * position 1 (= mid): the substantive case.  We transport the
--     hypothesised collider on the G-walk back to a collider on the
--     marg-walk via the arrowhead correspondence (outer `hTgt` for the
--     left arrowhead of mid; inner-step `hSrc` from `cases htail` for
--     the right arrowhead of mid), then read off `mid ∈ marg.AncSet C`
--     from the outer marg σ-open' hypothesis and transport to
--     `mid ∈ G.AncSet C` via `anc_set_marginalize_eq_inter_carrier`.
--   * position k + 2: transport via `h_tail_G_open` at position k + 1.
private lemma sigma_open_interior_lift_cons_one_edge_collider_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s' : WalkStep G a mid) (p_tail : Walk G mid b)
    (hTgt : s'.HeadAtTarget ↔ s.HeadAtTarget)
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_outer_marg_open : IsSigmaOpenAtInterior
      (Walk.cons mid s p'') C hC_marg)
    (h_tail_G_open : IsSigmaOpenAtInterior p_tail C hC_G) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons mid s' p_tail).vertices[k]? = some vk →
      (Walk.cons mid s' p_tail).IsCollider k →
      vk ∈ G.AncSet C := by
  intro k vk hk_vert h_coll
  cases k with
  | zero =>
      rw [isCollider_cons_zero_eq_false s' p_tail] at h_coll
      exact h_coll.elim
  | succ k1 =>
      cases k1 with
      | zero =>
          -- k = 1: substantive — mid is a collider on the outer G-walk.
          have hvk_mid : vk = mid := by
            have h1 : (Walk.cons mid s' p_tail).vertices[1]? = some mid := by
              show p_tail.vertices[0]? = some mid
              exact Walk.vertices_zero_eq_source' p_tail
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_mid]
          have h_marg_coll : (Walk.cons mid s p'').IsCollider 1 := by
            cases htail with
            | nil_lift _ _ =>
                exfalso
                revert h_coll
                cases s' <;> intro hh <;> exact hh.elim
            | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                  hSrcᵢ _ _ =>
                cases s' <;> cases s <;> cases s_x <;> cases s_marg <;>
                  first
                  | exact h_coll
                  | (refine ⟨?_, ?_⟩ <;> first
                      | exact hTgt.mp h_coll.1
                      | exact hSrcᵢ.mp h_coll.2
                      | exact h_coll.1
                      | exact h_coll.2)
                  | exact h_coll.elim
                  | exact h_coll.2.elim
                  | exact h_coll.1.elim
            | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner
                  hSrcᵢ _ _ _ =>
                cases s' <;> cases s <;> cases s_x₁ <;> cases s_marg <;>
                  first
                  | exact h_coll
                  | (refine ⟨?_, ?_⟩ <;> first
                      | exact hTgt.mp h_coll.1
                      | exact hSrcᵢ.mp h_coll.2
                      | exact h_coll.1
                      | exact h_coll.2)
                  | exact h_coll.elim
                  | exact h_coll.2.elim
                  | exact h_coll.1.elim
          have hmid_marg : (Walk.cons mid s p'').vertices[1]? = some mid := by
            show p''.vertices[0]? = some mid
            exact Walk.vertices_zero_eq_source' p''
          have hmid_anc_marg : mid ∈ (G.marginalize {u} hu).AncSet C :=
            h_outer_marg_open.1 1 mid hmid_marg h_marg_coll
          have h_eq := anc_set_marginalize_eq_inter_carrier G {u} hu C hC_G hC_disj
          rw [h_eq] at hmid_anc_marg
          exact hmid_anc_marg.1
      | succ k2 =>
          -- k = k2 + 2: transport from `h_tail_G_open` at p_tail position k2 + 1.
          have hvk_tail : p_tail.vertices[k2 + 1]? = some vk := hk_vert
          have h_tail_coll : p_tail.IsCollider (k2 + 1) := by
            cases p_tail with
            | nil v hv =>
                revert h_coll
                cases s' <;> intro hh <;> exact hh.elim
            | cons mid' s_x tail_inner =>
                revert h_coll
                cases s' <;> exact id
          exact h_tail_G_open.1 (k2 + 1) vk hvk_tail h_tail_coll

-- ## ref: claim_3_25 (Subtask 6e) — cons_one_edge case, blockable clause.
--
-- For the outer `cons mid s' p_tail` lift of `cons mid s p''`:
--   * position 0: impossible by `h_pos : 1 ≤ 0`.
--   * position 1 (= mid): the substantive case.  By contradiction
--     (assume `mid ∈ C`), we build the marg-side
--     `IsBlockableNonCollider 1` and apply `h_outer_marg_open.2` to
--     get `mid ∉ C` — contradiction.  The construction transports the
--     4-disjunct: trivial omega for `k = 0`; length disjunct via
--     `cases htail = nil_lift`; HBLS via the `marg_sc_subset`
--     contrapositive; HBRS via case-analysis on `htail`'s inner lift:
--     `nil_lift` is vacuous, `cons_one_edge` uses `marg_sc_subset`
--     contrapositive, `cons_two_edge` is the LN's case (b)
--     `by_cases mid_in ∈ marg.Sc mid` with the "yes" branch using
--     `Sc.of_directed_pass_through` to derive a contradiction.
--   * position k + 2: transport from `h_tail_G_open` at position k + 1.
set_option maxHeartbeats 400000 in
private lemma sigma_open_interior_lift_cons_one_edge_blockable_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s' : WalkStep G a mid) (p_tail : Walk G mid b)
    (hSrc : s'.HeadAtSource ↔ s.HeadAtSource)
    (hTgt : s'.HeadAtTarget ↔ s.HeadAtTarget)
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_outer_marg_open : IsSigmaOpenAtInterior
      (Walk.cons mid s p'') C hC_marg)
    (h_tail_G_open : IsSigmaOpenAtInterior p_tail C hC_G) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons mid s' p_tail).vertices[k]? = some vk →
      (Walk.cons mid s' p_tail).IsBlockableNonCollider k → 1 ≤ k →
      vk ∉ C := by
  intro k vk hk_vert h_blk h_pos
  cases k with
  | zero => omega
  | succ k1 =>
      cases k1 with
      | zero =>
          -- ## k = 1: substantive — build marg IsBlockableNonCollider 1.
          intro hmid_C
          have hvk_mid : vk = mid := by
            have h1 : (Walk.cons mid s' p_tail).vertices[1]? = some mid := by
              show p_tail.vertices[0]? = some mid
              exact Walk.vertices_zero_eq_source' p_tail
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_mid] at hmid_C
          have hmid_marg_vert : (Walk.cons mid s p'').vertices[1]? = some mid := by
            show p''.vertices[0]? = some mid
            exact Walk.vertices_zero_eq_source' p''
          have hmid_in_marg_of_s : mid ∈ G.marginalize {u} hu :=
            WalkStep.target_mem s
          -- ### Build marg.IsBlockableNonCollider 1.
          have h_marg_blk :
              (Walk.cons mid s p'').IsBlockableNonCollider 1 := by
            refine ⟨?_, ?_⟩
            · -- IsNonCollider 1: length bound + ¬ marg.IsCollider 1.
              refine ⟨?_, ?_⟩
              · -- 1 ≤ (cons mid s p'').length
                show 1 ≤ p''.length + 1
                omega
              · -- ¬ (cons mid s p'').IsCollider 1: by contradiction, derive
                -- (cons mid s' p_tail).IsCollider 1 (= ¬ h_blk.1.2).
                intro h_marg_coll
                apply h_blk.1.2
                cases htail with
                | nil_lift _ _ =>
                    -- p'' = nil mid _: (cons _ s (nil _ _)).IsCollider 1 = False
                    cases s <;> exact h_marg_coll.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ _ _ =>
                    cases s' <;> cases s <;> cases s_x <;> cases s_marg <;>
                      first
                      | exact h_marg_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mpr h_marg_coll.1
                          | exact hSrcᵢ.mpr h_marg_coll.2
                          | exact h_marg_coll.1
                          | exact h_marg_coll.2)
                      | exact h_marg_coll.elim
                      | exact h_marg_coll.2.elim
                      | exact h_marg_coll.1.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner
                      hSrcᵢ _ _ _ =>
                    cases s' <;> cases s <;> cases s_x₁ <;> cases s_marg <;>
                      first
                      | exact h_marg_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mpr h_marg_coll.1
                          | exact hSrcᵢ.mpr h_marg_coll.2
                          | exact h_marg_coll.1
                          | exact h_marg_coll.2)
                      | exact h_marg_coll.elim
                      | exact h_marg_coll.2.elim
                      | exact h_marg_coll.1.elim
            · -- ### Disjunct: 1 = 0 ∨ 1 = length ∨ HBLS 1 ∨ HBRS 1.
              rcases h_blk.2 with h0 | hlen | hHBLS | hHBRS
              · omega
              · -- Length disjunct: forces htail = nil_lift.
                right; left
                cases htail with
                | nil_lift _ _ =>
                    show 1 = (Walk.cons mid s (Walk.nil mid _)).length
                    simp [Walk.length]
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner _ _ _ =>
                    exfalso
                    simp [Walk.length] at hlen
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner _ _ _ _ =>
                    exfalso
                    simp [Walk.length] at hlen
              · -- HBLS 1: transport via marg_sc_subset contrapositive.
                right; right; left
                -- Force s' = .backwardE (only constructor where HBLS 1 fires).
                cases s' with
                | forwardE _ => exact hHBLS.elim
                | backwardE _ =>
                    -- hHBLS : a ∉ G.Sc mid; s.HeadAtSource = True, s.HeadAtTarget = False.
                    have h_src_s : s.HeadAtSource := hSrc.mp trivial
                    have h_tgt_s_neg : ¬ s.HeadAtTarget := fun h => hTgt.mpr h
                    cases s with
                    | forwardE _ => exact h_src_s.elim
                    | backwardE _ =>
                        intro h_a_marg_sc
                        exact hHBLS
                          (marg_sc_subset u hu hmid_in_marg_of_s h_a_marg_sc)
                    | bidir _ => exact (h_tgt_s_neg trivial).elim
                | bidir _ => exact hHBLS.elim
              · -- HBRS 1: the LN's case (b) substantive deduction.
                right; right; right
                cases htail with
                | nil_lift _ _ =>
                    exfalso
                    revert hHBRS
                    cases s' <;> intro hh <;> exact hh.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ _ _ =>
                    have hHBRS' :
                        (Walk.cons mid_in s_x p_tail_inner).HasBlockingRightSlot 0 := by
                      cases s' <;> exact hHBRS
                    have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                      WalkStep.target_mem s_marg
                    cases s_x with
                    | forwardE _ =>
                        have h_smarg_HAS_false : ¬ s_marg.HeadAtSource :=
                          fun h => (hSrcᵢ.mpr h)
                        cases s_marg with
                        | forwardE _ =>
                            suffices h_marg :
                                (Walk.cons mid_in (.forwardE (by assumption))
                                    p''_inner).HasBlockingRightSlot 0 by
                              cases s <;> exact h_marg
                            intro h_marg_sc
                            exact hHBRS'
                              (marg_sc_subset u hu hmid_in_marg_of_s h_marg_sc)
                        | backwardE _ => exact (h_smarg_HAS_false trivial).elim
                        | bidir _ => exact (h_smarg_HAS_false trivial).elim
                    | backwardE _ => exact hHBRS'.elim
                    | bidir _ => exact hHBRS'.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner
                      hSrcᵢ _ hNonCollᵢ _ =>
                    have hHBRS' : (Walk.cons u s_x₁
                        (Walk.cons mid_in s_x₂ p_tail_inner)).HasBlockingRightSlot 0 := by
                      cases s' <;> exact hHBRS
                    have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                      WalkStep.target_mem s_marg
                    cases s_x₁ with
                    | forwardE h_mid_u =>
                        -- hHBRS' : u ∉ G.Sc mid
                        have h_smarg_HAS_false : ¬ s_marg.HeadAtSource :=
                          fun h => (hSrcᵢ.mpr h)
                        have h_sx2_HAS_false : ¬ s_x₂.HeadAtSource :=
                          fun h => hNonCollᵢ ⟨trivial, h⟩
                        cases s_x₂ with
                        | forwardE h_u_midin =>
                            cases s_marg with
                            | forwardE _ =>
                                by_cases h_midin_marg_sc :
                                    mid_in ∈ (G.marginalize {u} hu).Sc mid
                                · exfalso
                                  have h_midin_G_sc : mid_in ∈ G.Sc mid :=
                                    marg_sc_subset u hu hmid_in_marg_of_s
                                      h_midin_marg_sc
                                  exact hHBRS' (Sc.of_directed_pass_through
                                    h_mid_u h_u_midin h_midin_G_sc)
                                · suffices h_marg :
                                      (Walk.cons mid_in (.forwardE (by assumption))
                                          p''_inner).HasBlockingRightSlot 0 by
                                    cases s <;> exact h_marg
                                  exact h_midin_marg_sc
                            | backwardE _ => exact (h_smarg_HAS_false trivial).elim
                            | bidir _ => exact (h_smarg_HAS_false trivial).elim
                        | backwardE _ => exact (h_sx2_HAS_false trivial).elim
                        | bidir _ => exact (h_sx2_HAS_false trivial).elim
                    | backwardE _ => exact hHBRS'.elim
                    | bidir _ => exact hHBRS'.elim
          exact h_outer_marg_open.2 1 mid hmid_marg_vert h_marg_blk (by omega) hmid_C
      | succ k2 =>
          -- ## k = k2 + 2: transport from `h_tail_G_open`.
          have hvk_tail : p_tail.vertices[k2 + 1]? = some vk := hk_vert
          have h_blk_tail : p_tail.IsBlockableNonCollider (k2 + 1) := by
            obtain ⟨h_nc, h_disj⟩ := h_blk
            refine ⟨?_, ?_⟩
            · -- IsNonCollider on tail
              refine ⟨?_, ?_⟩
              · -- k2 + 1 ≤ p_tail.length
                have : k2 + 2 ≤ (Walk.cons mid s' p_tail).length := h_nc.1
                show k2 + 1 ≤ p_tail.length
                simp [Walk.length] at this
                omega
              · -- ¬ p_tail.IsCollider (k2 + 1)
                intro h_tail_coll
                apply h_nc.2
                cases p_tail with
                | nil v hv =>
                    exact h_tail_coll.elim
                | cons mid' s_x tail_inner =>
                    cases s' <;> exact h_tail_coll
            · -- Disjunct on tail
              rcases h_disj with h0 | hlen | hHBLS | hHBRS
              · omega
              · right; left
                show k2 + 1 = p_tail.length
                simp [Walk.length] at hlen
                omega
              · right; right; left
                -- HBLS (k2 + 2) on outer → HBLS (k2 + 1) on tail
                cases p_tail with
                | nil v hv =>
                    exfalso
                    revert hHBLS
                    cases s' <;> intro h <;> exact h.elim
                | cons mid' s_x tail_inner =>
                    revert hHBLS
                    cases s' <;> exact id
              · right; right; right
                -- HBRS (k2 + 2) on outer → HBRS (k2 + 1) on tail
                revert hHBRS
                cases s' <;> exact id
          exact h_tail_G_open.2 (k2 + 1) vk hvk_tail h_blk_tail (by omega)

-- ## ref: claim_3_25 (Subtask 6e) — cons_two_edge case, collider clause.
--
-- For the outer `cons u s₁ (cons mid s₂ p_tail)` lift of `cons mid s p''`:
--   * position 0: vacuous (cons-cons IsCollider 0 = False).
--   * position 1 (= u inserted): hNonColl forbids u from being a collider.
--   * position 2 (= mid): the substantive transport via arrowhead
--     correspondence.  After two `cons _ _ ...` shifts, the G-side
--     `IsCollider 2` reduces to `s₂.HeadAtTarget ∧ <first p_tail step>.HeadAtSource`,
--     which transports to the marg-side `IsCollider 1` via `hTgt` and
--     the inner-lift `hSrc` (from `cases htail`).
--   * position k + 3: transport from `h_tail_G_open` at position k + 1.
private lemma sigma_open_interior_lift_cons_two_edge_collider_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid) (p_tail : Walk G mid b)
    (hTgt : s₂.HeadAtTarget ↔ s.HeadAtTarget)
    (hNonColl : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource))
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_outer_marg_open : IsSigmaOpenAtInterior
      (Walk.cons mid s p'') C hC_marg)
    (h_tail_G_open : IsSigmaOpenAtInterior p_tail C hC_G) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).vertices[k]? = some vk →
      (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).IsCollider k →
      vk ∈ G.AncSet C := by
  intro k vk hk_vert h_coll
  cases k with
  | zero =>
      rw [isCollider_cons_zero_eq_false s₁ (Walk.cons mid s₂ p_tail)] at h_coll
      exact h_coll.elim
  | succ k1 =>
      cases k1 with
      | zero =>
          -- k = 1: inserted u, non-collider by hNonColl.
          exfalso
          exact hNonColl h_coll
      | succ k2 =>
          cases k2 with
          | zero =>
              -- k = 2: vertex mid, substantive transport.
              have hvk_mid : vk = mid := by
                have h2 : (Walk.cons u s₁
                    (Walk.cons mid s₂ p_tail)).vertices[2]? = some mid := by
                  show p_tail.vertices[0]? = some mid
                  exact Walk.vertices_zero_eq_source' p_tail
                rw [h2] at hk_vert
                exact (Option.some.inj hk_vert).symm
              rw [hvk_mid]
              have h_marg_coll : (Walk.cons mid s p'').IsCollider 1 := by
                cases htail with
                | nil_lift _ _ =>
                    exfalso
                    revert h_coll
                    cases s₁ <;> cases s₂ <;> intro hh <;> exact hh.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ _ _ =>
                    cases s₁ <;> cases s₂ <;> cases s <;>
                      cases s_x <;> cases s_marg <;>
                      first
                      | exact h_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mp h_coll.1
                          | exact hSrcᵢ.mp h_coll.2
                          | exact h_coll.1
                          | exact h_coll.2)
                      | exact h_coll.elim
                      | exact h_coll.2.elim
                      | exact h_coll.1.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁_inner s_x₂_inner
                      p_tail_inner hSrcᵢ _ _ _ =>
                    cases s₁ <;> cases s₂ <;> cases s <;>
                      cases s_x₁_inner <;> cases s_marg <;>
                      first
                      | exact h_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mp h_coll.1
                          | exact hSrcᵢ.mp h_coll.2
                          | exact h_coll.1
                          | exact h_coll.2)
                      | exact h_coll.elim
                      | exact h_coll.2.elim
                      | exact h_coll.1.elim
              have hmid_marg_vert : (Walk.cons mid s p'').vertices[1]? = some mid := by
                show p''.vertices[0]? = some mid
                exact Walk.vertices_zero_eq_source' p''
              have hmid_anc_marg : mid ∈ (G.marginalize {u} hu).AncSet C :=
                h_outer_marg_open.1 1 mid hmid_marg_vert h_marg_coll
              have h_eq := anc_set_marginalize_eq_inter_carrier G {u} hu C hC_G hC_disj
              rw [h_eq] at hmid_anc_marg
              exact hmid_anc_marg.1
          | succ k3 =>
              -- k = k3 + 3: transport from h_tail_G_open at p_tail pos k3 + 1.
              have hvk_tail : p_tail.vertices[k3 + 1]? = some vk := hk_vert
              have h_tail_coll : p_tail.IsCollider (k3 + 1) := by
                cases p_tail with
                | nil v hv =>
                    revert h_coll
                    cases s₁ <;> cases s₂ <;> intro hh <;> exact hh.elim
                | cons mid' s_x tail_inner =>
                    revert h_coll
                    cases s₁ <;> cases s₂ <;> exact id
              exact h_tail_G_open.1 (k3 + 1) vk hvk_tail h_tail_coll

-- ## ref: claim_3_25 (Subtask 6e) — cons_two_edge case, blockable clause.
--
-- For the outer `cons u s₁ (cons mid s₂ p_tail)` lift of `cons mid s p''`:
--   * position 0: impossible by `h_pos`.
--   * position 1 (= u inserted): `u ∉ C` by `hu_notC`.
--   * position 2 (= mid): the substantive case.  By-contra
--     `mid ∈ C` → build marg `IsBlockableNonCollider 1`.  Disjunct
--     transport: HBLS 2 is the LN case (b) at the `s₁/s₂` level
--     (`s₂ = .backwardE` forces `s₁ = .backwardE` via `hNonColl` and
--     `s = .backwardE` via `hTgt`; then `Sc.of_directed_pass_through`
--     yields `u ∈ G.Sc mid`, contradicting the HBLS hypothesis); HBRS
--     2 mirrors cons_one_edge's HBRS 1 substantive (case-split on
--     `htail`).
--   * position k + 3: transport from `h_tail_G_open` at position k + 1.
set_option maxHeartbeats 800000 in
private lemma sigma_open_interior_lift_cons_two_edge_blockable_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid) (p_tail : Walk G mid b)
    (hSrc : s₁.HeadAtSource ↔ s.HeadAtSource)
    (hTgt : s₂.HeadAtTarget ↔ s.HeadAtTarget)
    (hNonColl : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource))
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node) (hu_notC : u ∉ C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_outer_marg_open : IsSigmaOpenAtInterior
      (Walk.cons mid s p'') C hC_marg)
    (h_tail_G_open : IsSigmaOpenAtInterior p_tail C hC_G) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).vertices[k]? = some vk →
      (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).IsBlockableNonCollider k → 1 ≤ k →
      vk ∉ C := by
  intro k vk hk_vert h_blk h_pos
  cases k with
  | zero => omega
  | succ k1 =>
      cases k1 with
      | zero =>
          -- ## k = 1: inserted u, u ∉ C via hu_notC.
          intro hu_C
          have hvk_u : vk = u := by
            have h1 : (Walk.cons u s₁
                (Walk.cons mid s₂ p_tail)).vertices[1]? = some u := by
              show (Walk.cons mid s₂ p_tail).vertices[0]? = some u
              exact Walk.vertices_zero_eq_source' (Walk.cons mid s₂ p_tail)
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_u] at hu_C
          exact hu_notC hu_C
      | succ k2 =>
          cases k2 with
          | zero =>
              -- ## k = 2: vertex mid, substantive LN-case-(b) transport.
              intro hmid_C
              have hvk_mid : vk = mid := by
                have h2 : (Walk.cons u s₁
                    (Walk.cons mid s₂ p_tail)).vertices[2]? = some mid := by
                  show p_tail.vertices[0]? = some mid
                  exact Walk.vertices_zero_eq_source' p_tail
                rw [h2] at hk_vert
                exact (Option.some.inj hk_vert).symm
              rw [hvk_mid] at hmid_C
              have hmid_marg_vert :
                  (Walk.cons mid s p'').vertices[1]? = some mid := by
                show p''.vertices[0]? = some mid
                exact Walk.vertices_zero_eq_source' p''
              have hmid_in_marg_of_s : mid ∈ G.marginalize {u} hu :=
                WalkStep.target_mem s
              -- ### Build marg.IsBlockableNonCollider 1.
              have h_marg_blk :
                  (Walk.cons mid s p'').IsBlockableNonCollider 1 := by
                refine ⟨?_, ?_⟩
                · -- IsNonCollider 1
                  refine ⟨?_, ?_⟩
                  · show 1 ≤ p''.length + 1; omega
                  · intro h_marg_coll
                    apply h_blk.1.2
                    cases htail with
                    | nil_lift _ _ =>
                        cases s <;> exact h_marg_coll.elim
                    | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                          hSrcᵢ _ _ =>
                        cases s₁ <;> cases s₂ <;> cases s <;>
                          cases s_x <;> cases s_marg <;>
                          first
                          | exact h_marg_coll
                          | (refine ⟨?_, ?_⟩ <;> first
                              | exact hTgt.mpr h_marg_coll.1
                              | exact hSrcᵢ.mpr h_marg_coll.2
                              | exact h_marg_coll.1
                              | exact h_marg_coll.2)
                          | exact h_marg_coll.elim
                          | exact h_marg_coll.2.elim
                          | exact h_marg_coll.1.elim
                    | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁_inner s_x₂_inner
                          p_tail_inner hSrcᵢ _ _ _ =>
                        cases s₁ <;> cases s₂ <;> cases s <;>
                          cases s_x₁_inner <;> cases s_marg <;>
                          first
                          | exact h_marg_coll
                          | (refine ⟨?_, ?_⟩ <;> first
                              | exact hTgt.mpr h_marg_coll.1
                              | exact hSrcᵢ.mpr h_marg_coll.2
                              | exact h_marg_coll.1
                              | exact h_marg_coll.2)
                          | exact h_marg_coll.elim
                          | exact h_marg_coll.2.elim
                          | exact h_marg_coll.1.elim
                · -- ### Disjunct.
                  rcases h_blk.2 with h0 | hlen | hHBLS | hHBRS
                  · omega
                  · -- length: forces htail = nil_lift
                    right; left
                    cases htail with
                    | nil_lift _ _ =>
                        show 1 = (Walk.cons mid s (Walk.nil mid _)).length
                        simp [Walk.length]
                    | @cons_one_edge _ _ _ _ _ _ _ _ _ _ =>
                        exfalso; simp [Walk.length] at hlen
                    | @cons_two_edge _ _ _ _ _ _ _ _ _ _ _ _ =>
                        exfalso; simp [Walk.length] at hlen
                  · -- HBLS 2: LN case (b) at s₁/s₂ level
                    right; right; left
                    revert hHBLS
                    cases s₁ with
                    | forwardE _ =>
                        cases s₂ with
                        | forwardE _ => intro hh; exact hh.elim
                        | backwardE _ =>
                            intro _; exfalso
                            exact hNonColl ⟨trivial, trivial⟩
                        | bidir _ => intro hh; exact hh.elim
                    | backwardE h_E_u_a =>
                        cases s₂ with
                        | forwardE _ => intro hh; exact hh.elim
                        | backwardE h_E_mid_u =>
                            intro hHBLS
                            cases s with
                            | forwardE _ =>
                                exact (hSrc.mp trivial).elim
                            | backwardE _ =>
                                intro h_a_marg_sc
                                have h_a_G_sc : a ∈ G.Sc mid :=
                                  marg_sc_subset u hu hmid_in_marg_of_s
                                    h_a_marg_sc
                                exact hHBLS (Sc.of_directed_pass_through
                                  h_E_mid_u h_E_u_a h_a_G_sc)
                            | bidir _ =>
                                exact (hTgt.mpr trivial).elim
                        | bidir _ => intro hh; exact hh.elim
                    | bidir _ =>
                        cases s₂ with
                        | forwardE _ => intro hh; exact hh.elim
                        | backwardE _ =>
                            intro _; exfalso
                            exact hNonColl ⟨trivial, trivial⟩
                        | bidir _ => intro hh; exact hh.elim
                  · -- HBRS 2: same substantive analysis as cons_one_edge HBRS 1.
                    right; right; right
                    cases htail with
                    | nil_lift _ _ =>
                        exfalso
                        revert hHBRS
                        cases s₁ <;> cases s₂ <;> intro hh <;> exact hh.elim
                    | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                          hSrcᵢ _ _ =>
                        have hHBRS' : (Walk.cons mid_in s_x
                            p_tail_inner).HasBlockingRightSlot 0 := by
                          cases s₁ <;> cases s₂ <;> exact hHBRS
                        have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                          WalkStep.target_mem s_marg
                        cases s_x with
                        | forwardE _ =>
                            have h_smarg_HAS_false : ¬ s_marg.HeadAtSource :=
                              fun h => (hSrcᵢ.mpr h)
                            cases s_marg with
                            | forwardE _ =>
                                suffices h_marg :
                                    (Walk.cons mid_in (.forwardE (by assumption))
                                        p''_inner).HasBlockingRightSlot 0 by
                                  cases s <;> exact h_marg
                                intro h_marg_sc
                                exact hHBRS'
                                  (marg_sc_subset u hu hmid_in_marg_of_s h_marg_sc)
                            | backwardE _ => exact (h_smarg_HAS_false trivial).elim
                            | bidir _ => exact (h_smarg_HAS_false trivial).elim
                        | backwardE _ => exact hHBRS'.elim
                        | bidir _ => exact hHBRS'.elim
                    | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁_inner s_x₂_inner
                          p_tail_inner hSrcᵢ _ hNonCollᵢ _ =>
                        have hHBRS' : (Walk.cons u s_x₁_inner
                            (Walk.cons mid_in s_x₂_inner
                                p_tail_inner)).HasBlockingRightSlot 0 := by
                          cases s₁ <;> cases s₂ <;> exact hHBRS
                        have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                          WalkStep.target_mem s_marg
                        cases s_x₁_inner with
                        | forwardE h_mid_u_inner =>
                            have h_smarg_HAS_false : ¬ s_marg.HeadAtSource :=
                              fun h => (hSrcᵢ.mpr h)
                            have h_sx2_HAS_false : ¬ s_x₂_inner.HeadAtSource :=
                              fun h => hNonCollᵢ ⟨trivial, h⟩
                            cases s_x₂_inner with
                            | forwardE h_u_midin =>
                                cases s_marg with
                                | forwardE _ =>
                                    by_cases h_midin_marg_sc :
                                        mid_in ∈ (G.marginalize {u} hu).Sc mid
                                    · exfalso
                                      have h_midin_G_sc :
                                          mid_in ∈ G.Sc mid :=
                                        marg_sc_subset u hu hmid_in_marg_of_s
                                          h_midin_marg_sc
                                      exact hHBRS' (Sc.of_directed_pass_through
                                        h_mid_u_inner h_u_midin h_midin_G_sc)
                                    · suffices h_marg :
                                          (Walk.cons mid_in (.forwardE (by assumption))
                                              p''_inner).HasBlockingRightSlot 0 by
                                        cases s <;> exact h_marg
                                      exact h_midin_marg_sc
                                | backwardE _ =>
                                    exact (h_smarg_HAS_false trivial).elim
                                | bidir _ =>
                                    exact (h_smarg_HAS_false trivial).elim
                            | backwardE _ =>
                                exact (h_sx2_HAS_false trivial).elim
                            | bidir _ =>
                                exact (h_sx2_HAS_false trivial).elim
                        | backwardE _ => exact hHBRS'.elim
                        | bidir _ => exact hHBRS'.elim
              exact h_outer_marg_open.2 1 mid hmid_marg_vert h_marg_blk (by omega) hmid_C
          | succ k3 =>
              -- ## k = k3 + 3: transport from h_tail_G_open at pos k3 + 1.
              have hvk_tail : p_tail.vertices[k3 + 1]? = some vk := hk_vert
              have h_blk_tail : p_tail.IsBlockableNonCollider (k3 + 1) := by
                obtain ⟨h_nc, h_disj⟩ := h_blk
                refine ⟨?_, ?_⟩
                · refine ⟨?_, ?_⟩
                  · have : k3 + 3 ≤ (Walk.cons u s₁
                        (Walk.cons mid s₂ p_tail)).length := h_nc.1
                    show k3 + 1 ≤ p_tail.length
                    simp [Walk.length] at this
                    omega
                  · intro h_tail_coll
                    apply h_nc.2
                    cases p_tail with
                    | nil v hv => exact h_tail_coll.elim
                    | cons mid' s_x tail_inner =>
                        cases s₁ <;> cases s₂ <;> exact h_tail_coll
                · rcases h_disj with h0 | hlen | hHBLS | hHBRS
                  · omega
                  · right; left
                    show k3 + 1 = p_tail.length
                    simp [Walk.length] at hlen
                    omega
                  · right; right; left
                    cases p_tail with
                    | nil v hv =>
                        exfalso
                        revert hHBLS
                        cases s₁ <;> cases s₂ <;> intro h <;> exact h.elim
                    | cons mid' s_x tail_inner =>
                        revert hHBLS
                        cases s₁ <;> cases s₂ <;> exact id
                  · right; right; right
                    revert hHBRS
                    cases s₁ <;> cases s₂ <;> exact id
              exact h_tail_G_open.2 (k3 + 1) vk hvk_tail h_blk_tail (by omega)

-- ## ref: claim_3_25 (Subtask 6e) — main σ-open' preservation lemma.
--
-- Wraps the three case-by-case helpers above into a single induction on
-- `IsLift`.  At each cons case, the IH is fed by:
--   * `walkstep_target_ne_u` (target of `s` is ≠ `u`, since `s` is a
--     marg-WalkStep).
--   * `sigma_open_interior_cons_tail` (tail σ-open' inherits from outer
--     σ-open' via the position-shift inheritance lemma).
private lemma sigma_open_interior_lift_via_isLift
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (C : Set Node) (hu_notC : u ∉ C)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V) :
    ∀ {a b : Node} {p' : Walk (G.marginalize {u} hu) a b}
      {p : Walk G a b},
      IsLift G u hu p' p → a ≠ u → b ≠ u →
      IsSigmaOpenAtInterior p' C hC_marg →
      IsSigmaOpenAtInterior p C hC_G := by
  intro a b p' p hlift
  induction hlift with
  | nil_lift hv_marg hv_G =>
      intros _ _ _
      exact sigma_open_interior_lift_nil_case _ hv_G C hC_G
  | @cons_one_edge a' mid b' s p'' s' p_tail hSrc hTgt htail ih =>
      intros ha hb h_outer
      have h_mid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
      have h_tail_marg_open :=
        sigma_open_interior_cons_tail s p'' C hC_marg h_outer
      have h_tail_G_open := ih h_mid_ne_u hb h_tail_marg_open
      refine ⟨?_, ?_⟩
      · exact sigma_open_interior_lift_cons_one_edge_collider_clause
          hu s p'' s' p_tail hTgt htail C hC_disj hC_G hC_marg h_outer h_tail_G_open
      · exact sigma_open_interior_lift_cons_one_edge_blockable_clause
          hu s p'' s' p_tail hSrc hTgt htail C hC_G hC_marg h_outer h_tail_G_open
  | @cons_two_edge a' mid b' s p'' s₁ s₂ p_tail hSrc hTgt hNonColl htail ih =>
      intros ha hb h_outer
      have h_mid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
      have h_tail_marg_open :=
        sigma_open_interior_cons_tail s p'' C hC_marg h_outer
      have h_tail_G_open := ih h_mid_ne_u hb h_tail_marg_open
      refine ⟨?_, ?_⟩
      · exact sigma_open_interior_lift_cons_two_edge_collider_clause
          hu s p'' s₁ s₂ p_tail hTgt hNonColl htail C hC_disj hC_G hC_marg
          h_outer h_tail_G_open
      · exact sigma_open_interior_lift_cons_two_edge_blockable_clause
          hu s p'' s₁ s₂ p_tail hSrc hTgt hNonColl htail C hu_notC hC_G hC_marg
          h_outer h_tail_G_open

-- ## ref: claim_3_25 (Subtask 6e) — top-level σ-openness lift.
--
-- Composes (a) the existence of an `IsLift` for any marg-walk, (b) the
-- σ-open' preservation lemma above, and (c) the source-∉-C reassembly
-- to deliver: every σ-open marg-walk lifts to a σ-open G-walk between
-- the same endpoints.  This is the contrapositive of LN's "every
-- C-σ-blocked-in-G regime forces every C-σ-blocked-in-G^{∖u} regime"
-- statement (Step 3 of the tex proof).
private lemma sigma_open_lift_marg_one
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (C : Set Node) (hu_notC : u ∉ C)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V) :
    ∀ {a b : Node} (p' : Walk (G.marginalize {u} hu) a b),
      a ≠ u → b ≠ u → p'.IsSigmaOpenGiven C hC_marg →
      ∃ p : Walk G a b, p.IsSigmaOpenGiven C hC_G := by
  intro a b p' ha hb hp'
  obtain ⟨p, hlift⟩ := exists_isLift_of_walk_marg G u hu p'
  refine ⟨p, ?_⟩
  have h_interior_marg : IsSigmaOpenAtInterior p' C hC_marg :=
    sigma_open_to_interior p' C hC_marg hp'
  have h_interior_G : IsSigmaOpenAtInterior p C hC_G :=
    sigma_open_interior_lift_via_isLift G u hu C hu_notC hC_disj hC_G hC_marg
      hlift ha hb h_interior_marg
  refine sigma_open_of_interior_of_source_notC p C hC_G h_interior_G ?_
  -- Position 0 of `p'` is a blockable non-collider (k = 0 disjunct
  -- fires automatically), with vertex `a`.  σ-openness of `p'` gives
  -- `a ∉ C`.
  refine hp'.2 0 a (Walk.vertices_zero_eq_source' p') ⟨⟨Nat.zero_le _, ?_⟩, Or.inl rfl⟩
  intro h_coll
  cases p' with
  | nil _ _ => exact h_coll
  | cons _ _ tail =>
      cases tail with
      | nil _ _ => exact h_coll
      | cons _ _ _ => exact h_coll

-- ## ref: claim_3_25 (Subtask 8) — "no-problematic-position" predicate.
--
-- Encodes the residual obligation that Subtask 9's surgery is
-- responsible for discharging.  Phrased recursively on the `IsLift`
-- inductive: at every `cons_two_edge` cell (the cells where the
-- marg-walk contracts a 2-edge G-subwalk through `u`), if the
-- contracted edge is a directed pass-through and the source/target
-- vertex of the cell is in `C` while the inserted vertex `u` is in
-- `G.Sc`, then the contracted-edge's other endpoint lies in
-- `marg.Sc` — exactly the LN's case-(b) obligation at b_l ∈ C.
--
-- Two arrowhead-conditional conjuncts at each `cons_two_edge` cell
-- (the forward and backward directed-pass-through patterns), plus a
-- recursive call on the `htail`.  Vacuously `True` on `nil_lift`;
-- transparent on `cons_one_edge` (no contraction).
--
-- ## Design choice — NoProblematicLift
--
-- *Two arrowhead-conditional conjuncts, not a single one.*  The
--   marg-step `s`'s constructor partitions into three families:
--   `.forwardE` (directed pass-through `a → mid`), `.backwardE`
--   (directed pass-through `mid → a`), and `.bidir` (bifurcation).
--   The directed-pass-through cases are exactly the ones the LN's
--   tex line 273 identifies as problematic; the bifurcation case
--   is non-problematic (the contracted bidir edge witnesses
--   `a ↔ mid` regardless of `Sc` membership).  So we have two
--   directed-pass-through conjuncts (one per arrowhead orientation)
--   and no `.bidir` conjunct.
--
-- *`s.HeadAtSource` / `s.HeadAtTarget` characterisation, not
--   pattern match on constructor.*  The LN's "directed pass-through"
--   condition is `s.HeadAtSource ≠ s.HeadAtTarget` (exactly one
--   arrowhead): forward = `False, True`, backward = `True, False`.
--   Using these predicates avoids re-doing the constructor case
--   analysis at every helper consumption site.
private inductive NoProblematicLift {G : CDMG Node} {u : Node}
    (hu : ({u} : Finset Node) ⊆ G.V) (C : Set Node) :
    ∀ {a b : Node}, Walk (G.marginalize {u} hu) a b → Walk G a b → Prop
  | nil_npl {v : Node} (hv_marg : v ∈ G.marginalize {u} hu) (hv_G : v ∈ G) :
      NoProblematicLift hu C (Walk.nil v hv_marg) (Walk.nil v hv_G)
  | one_edge_npl {a mid b : Node}
      (s : WalkStep (G.marginalize {u} hu) a mid)
      (p'' : Walk (G.marginalize {u} hu) mid b)
      (s' : WalkStep G a mid) (p_tail : Walk G mid b)
      (npl_tail : NoProblematicLift hu C p'' p_tail) :
      NoProblematicLift hu C (Walk.cons mid s p'') (Walk.cons mid s' p_tail)
  | two_edge_npl {a mid b : Node}
      (s : WalkStep (G.marginalize {u} hu) a mid)
      (p'' : Walk (G.marginalize {u} hu) mid b)
      (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid) (p_tail : Walk G mid b)
      (h_fwd : ¬ s.HeadAtSource ∧ s.HeadAtTarget →
          a ∈ C → u ∈ G.Sc a → mid ∈ (G.marginalize {u} hu).Sc a)
      (h_bwd : s.HeadAtSource ∧ ¬ s.HeadAtTarget →
          mid ∈ C → u ∈ G.Sc mid → a ∈ (G.marginalize {u} hu).Sc mid)
      (npl_tail : NoProblematicLift hu C p'' p_tail) :
      NoProblematicLift hu C (Walk.cons mid s p'')
          (Walk.cons u s₁ (Walk.cons mid s₂ p_tail))

-- ## ref: claim_3_25 (Subtask 8) — nil-case branch of the reverse
-- σ-open' lift.
--
-- Trivial: a length-0 marg walk has no colliders
-- (`isCollider_nil_eq_false`) and no positions with `k ≥ 1` (the
-- blockable clause is vacuous via `IsNonCollider`'s `k ≤ length = 0`
-- first conjunct).  Mirror of `sigma_open_interior_lift_nil_case`
-- (line 4106).
private lemma sigma_open_interior_lift_reverse_nil_case
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    (v : Node) (hv_marg : v ∈ G.marginalize {u} hu)
    (C : Set Node) (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                                ↑(G.marginalize {u} hu).V) :
    IsSigmaOpenAtInterior
      (Walk.nil v hv_marg : Walk (G.marginalize {u} hu) v v) C hC_marg := by
  refine ⟨?_, ?_⟩
  · intro k vk _ h_coll
    rw [isCollider_nil_eq_false hv_marg] at h_coll
    exact h_coll.elim
  · intro k vk _ h_blk h_pos
    obtain ⟨h_nc, _⟩ := h_blk
    have h_len : k ≤ (Walk.nil v hv_marg :
        Walk (G.marginalize {u} hu) v v).length := h_nc.1
    simp [Walk.length] at h_len
    omega

-- ## ref: claim_3_25 (Subtask 8) — cons_one_edge case, collider clause
-- (reverse direction).
--
-- For the outer `cons mid s p''` lift of `cons mid s' p_tail`:
--   * position 0: vacuous via `isCollider_cons_zero_eq_false`.
--   * position 1 (= mid): the substantive case.  Transport the
--     hypothesised collider on the marg-walk back to a collider on the
--     G-walk via arrowhead correspondence (outer `hTgt` for the left
--     arrowhead; inner-step `hSrc` from `cases htail`).  Then the
--     G-walk σ-open collider clause `h_G_open_coll` (read off
--     `IsSigmaOpenAtInterior` directly, NOT the strengthened
--     "every collider in C" witness) gives `mid ∈ G.AncSet C`, which is
--     transported to `mid ∈ marg.AncSet C` via
--     `anc_set_marginalize_eq_inter_carrier`
--     (`MargPreservesAncestors.lean:4018`) combined with
--     `mid ∈ marg.carrier` (derived from `mid ∈ G` via `WalkStep.target_mem
--     s'` and `mid ≠ u` via `walkstep_target_ne_u hu s`).  This is the
--     Resolution-A weakening of Subtask 8 documented at the bottom of
--     `workspace_claim_3_25.md` — matches LN tex line 268's collider
--     obligation `b_l ∈ \Anc^{G^{\sm u}}(C)` (no strict `b_l ∈ C` needed).
--   * position k + 2: transport via `h_tail_marg_open` at p''-position
--     k + 1.
private lemma sigma_open_interior_lift_reverse_cons_one_edge_collider_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s' : WalkStep G a mid) (p_tail : Walk G mid b)
    (hTgt : s'.HeadAtTarget ↔ s.HeadAtTarget)
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_G_open_coll : ∀ k vk,
        (Walk.cons mid s' p_tail).vertices[k]? = some vk →
        (Walk.cons mid s' p_tail).IsCollider k → vk ∈ G.AncSet C)
    (h_tail_marg_open : IsSigmaOpenAtInterior p'' C hC_marg) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons mid s p'').vertices[k]? = some vk →
      (Walk.cons mid s p'').IsCollider k →
      vk ∈ (G.marginalize {u} hu).AncSet C := by
  intro k vk hk_vert h_coll
  cases k with
  | zero =>
      rw [isCollider_cons_zero_eq_false s p''] at h_coll
      exact h_coll.elim
  | succ k1 =>
      cases k1 with
      | zero =>
          -- k = 1: substantive — transport marg-collider to G-collider.
          have hvk_mid : vk = mid := by
            have h1 : (Walk.cons mid s p'').vertices[1]? = some mid := by
              show p''.vertices[0]? = some mid
              exact Walk.vertices_zero_eq_source' p''
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_mid]
          have h_G_coll : (Walk.cons mid s' p_tail).IsCollider 1 := by
            cases htail with
            | nil_lift _ _ =>
                exfalso
                revert h_coll
                cases s <;> intro hh <;> exact hh.elim
            | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                  hSrcᵢ _ _ =>
                cases s' <;> cases s <;> cases s_x <;> cases s_marg <;>
                  first
                  | exact h_coll
                  | (refine ⟨?_, ?_⟩ <;> first
                      | exact hTgt.mpr h_coll.1
                      | exact hSrcᵢ.mpr h_coll.2
                      | exact h_coll.1
                      | exact h_coll.2)
                  | exact h_coll.elim
                  | exact h_coll.2.elim
                  | exact h_coll.1.elim
            | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner
                  hSrcᵢ _ _ _ =>
                cases s' <;> cases s <;> cases s_x₁ <;> cases s_marg <;>
                  first
                  | exact h_coll
                  | (refine ⟨?_, ?_⟩ <;> first
                      | exact hTgt.mpr h_coll.1
                      | exact hSrcᵢ.mpr h_coll.2
                      | exact h_coll.1
                      | exact h_coll.2)
                  | exact h_coll.elim
                  | exact h_coll.2.elim
                  | exact h_coll.1.elim
          have hmid_G_vert : (Walk.cons mid s' p_tail).vertices[1]? = some mid := by
            show p_tail.vertices[0]? = some mid
            exact Walk.vertices_zero_eq_source' p_tail
          -- Resolution A: read `mid ∈ G.AncSet C` off σ-open directly
          -- (instead of strict `mid ∈ C`), then transport to
          -- `mid ∈ marg.AncSet C` via the carrier intersection identity.
          have hmid_AncG : mid ∈ G.AncSet C :=
            h_G_open_coll 1 mid hmid_G_vert h_G_coll
          have hmid_G : mid ∈ G := WalkStep.target_mem (G := G) s'
          have hmid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
          have hmid_marg : mid ∈ G.marginalize {u} hu := by
            change mid ∈ G.J ∪ (G.V \ ({u} : Finset Node))
            rcases Finset.mem_union.mp hmid_G with hJ | hV
            · exact Finset.mem_union_left _ hJ
            · refine Finset.mem_union_right _
                (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
              intro hmem
              exact hmid_ne_u (Finset.mem_singleton.mp hmem)
          have hmid_carrier_set :
              mid ∈ ((↑G.J : Set Node) ∪ ↑(G.V \ ({u} : Finset Node))) := by
            have h_union : mid ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := hmid_marg
            rcases Finset.mem_union.mp h_union with hJ | hVW
            · exact Or.inl (Finset.mem_coe.mpr hJ)
            · exact Or.inr (Finset.mem_coe.mpr hVW)
          have h_eq := anc_set_marginalize_eq_inter_carrier
            G ({u} : Finset Node) hu C hC_G hC_disj
          rw [h_eq]
          exact Set.mem_inter hmid_AncG hmid_carrier_set
      | succ k2 =>
          -- k = k2 + 2: transport from `h_tail_marg_open` at p'' pos k2 + 1.
          have hvk_tail : p''.vertices[k2 + 1]? = some vk := hk_vert
          have h_tail_coll : p''.IsCollider (k2 + 1) := by
            cases p'' with
            | nil v hv =>
                revert h_coll
                cases s <;> intro hh <;> exact hh.elim
            | cons mid' s_x tail_inner =>
                revert h_coll
                cases s <;> exact id
          exact h_tail_marg_open.1 (k2 + 1) vk hvk_tail h_tail_coll

-- ## ref: claim_3_25 (Subtask 8) — Sc membership transport from G to marg.
--
-- For any vertex `v` in the marg-carrier and any `x ≠ u`, x is in
-- `G.Sc(v)` iff x is in `marg.Sc(v)`.  The contrapositive direction
-- (`x ∉ marg.Sc(v) → x ∉ G.Sc(v)`) is what we need for the reverse-
-- direction HBLS / HBRS transport.  Proof uses
-- `marginalize_preserves_ancestors` and `marginalize_preserves_descendants`
-- after establishing x ∈ marg-carrier (via x ∈ G and x ≠ u).
private lemma marg_sc_iff_G_sc {G : CDMG Node} (u : Node)
    (hu : ({u} : Finset Node) ⊆ G.V) {v x : Node}
    (hv_marg : v ∈ G.marginalize {u} hu) (hx_G : x ∈ G) (hx_ne_u : x ≠ u) :
    x ∈ (G.marginalize {u} hu).Sc v ↔ x ∈ G.Sc v := by
  have hx_notU : x ∉ ({u} : Finset Node) := by
    intro h_in; exact hx_ne_u (Finset.mem_singleton.mp h_in)
  have hx_marg : x ∈ G.marginalize {u} hu := by
    change x ∈ G.J ∪ (G.V \ ({u} : Finset Node))
    rcases Finset.mem_union.mp hx_G with hJ | hV
    · exact Finset.mem_union_left _ hJ
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hx_notU⟩)
  unfold CDMG.Sc
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨h_anc, h_desc⟩
    refine ⟨?_, ?_⟩
    · exact (marginalize_preserves_ancestors G {u} hu x v hx_marg hv_marg).mpr h_anc
    · exact (marginalize_preserves_descendants G {u} hu x v hx_marg hv_marg).mpr h_desc
  · rintro ⟨h_anc, h_desc⟩
    refine ⟨?_, ?_⟩
    · exact (marginalize_preserves_ancestors G {u} hu x v hx_marg hv_marg).mp h_anc
    · exact (marginalize_preserves_descendants G {u} hu x v hx_marg hv_marg).mp h_desc

-- ## ref: claim_3_25 (Subtask 8) — inversion helper: extract forward
-- and backward case-(b) conditions from a `two_edge_npl`-shaped NPL.
private lemma NoProblematicLift.two_edge_inv
    {G : CDMG Node} {u : Node}
    {hu : ({u} : Finset Node) ⊆ G.V} {C : Set Node}
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid)
    (p_tail : Walk G mid b)
    (hmid_ne_u : mid ≠ u)
    (h : NoProblematicLift hu C (Walk.cons mid s p'')
        (Walk.cons u s₁ (Walk.cons mid s₂ p_tail))) :
    (¬ s.HeadAtSource ∧ s.HeadAtTarget →
        a ∈ C → u ∈ G.Sc a → mid ∈ (G.marginalize {u} hu).Sc a) ∧
    (s.HeadAtSource ∧ ¬ s.HeadAtTarget →
        mid ∈ C → u ∈ G.Sc mid → a ∈ (G.marginalize {u} hu).Sc mid) ∧
    NoProblematicLift hu C p'' p_tail := by
  cases h
  case one_edge_npl => exact (hmid_ne_u rfl).elim
  case two_edge_npl h_fwd h_bwd npl_tail =>
      exact ⟨h_fwd, h_bwd, npl_tail⟩

-- Inversion helper: extract `p''/p_tail`'s NPL from a `one_edge_npl`-shaped NPL.
private lemma NoProblematicLift.one_edge_inv
    {G : CDMG Node} {u : Node}
    {hu : ({u} : Finset Node) ⊆ G.V} {C : Set Node}
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s' : WalkStep G a mid) (p_tail : Walk G mid b)
    (hmid_ne_u : mid ≠ u)
    (h : NoProblematicLift hu C (Walk.cons mid s p'') (Walk.cons mid s' p_tail)) :
    NoProblematicLift hu C p'' p_tail := by
  cases h
  case one_edge_npl npl_tail => exact npl_tail
  case two_edge_npl => exact (hmid_ne_u rfl).elim

-- ## ref: claim_3_25 (Subtask 8) — cons_one_edge case, blockable clause
-- (reverse direction).
--
-- For the outer `cons mid s p''` lift of `cons mid s' p_tail`:
--   * position 0: vacuous via `h_pos : 1 ≤ 0`.
--   * position 1 (= mid): the substantive case.  By contradiction
--     (`mid ∈ C`), build the G-side `IsBlockableNonCollider 1` and
--     apply `h_outer_G_open.2` to get `mid ∉ C` — contradiction.  The
--     construction transports each disjunct: length via
--     `cases htail = nil_lift`; HBLS via `marg_sc_iff_G_sc`
--     plus `a ≠ u`; HBRS via case-analysis on `htail`:
--     `nil_lift` is vacuous, `cons_one_edge_inner` uses
--     `marg_sc_iff_G_sc` plus `mid_in ≠ u`, `cons_two_edge_inner`
--     uses the inner cell's forward `NoProblematicLift` data plus
--     `by_cases u ∈ G.Sc mid` (LN's case (b) at the inner cell).
--   * position k + 2: transport from `h_tail_marg_open` at position k+1.
set_option maxHeartbeats 400000 in
private lemma sigma_open_interior_lift_reverse_cons_one_edge_blockable_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s' : WalkStep G a mid) (p_tail : Walk G mid b)
    (hSrc : s'.HeadAtSource ↔ s.HeadAtSource)
    (hTgt : s'.HeadAtTarget ↔ s.HeadAtTarget)
    (htail : IsLift G u hu p'' p_tail)
    (ha : a ≠ u)
    (C : Set Node)
    (h_NPL : NoProblematicLift hu C (Walk.cons mid s p'')
        (Walk.cons mid s' p_tail))
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_outer_G_open : IsSigmaOpenAtInterior
      (Walk.cons mid s' p_tail) C hC_G)
    (h_tail_marg_open : IsSigmaOpenAtInterior p'' C hC_marg) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons mid s p'').vertices[k]? = some vk →
      (Walk.cons mid s p'').IsBlockableNonCollider k → 1 ≤ k →
      vk ∉ C := by
  intro k vk hk_vert h_blk h_pos
  cases k with
  | zero => omega
  | succ k1 =>
      cases k1 with
      | zero =>
          -- ## k = 1: substantive — build G IsBlockableNonCollider 1.
          intro hmid_C
          have hvk_mid : vk = mid := by
            have h1 : (Walk.cons mid s p'').vertices[1]? = some mid := by
              show p''.vertices[0]? = some mid
              exact Walk.vertices_zero_eq_source' p''
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_mid] at hmid_C
          have hmid_G_vert :
              (Walk.cons mid s' p_tail).vertices[1]? = some mid := by
            show p_tail.vertices[0]? = some mid
            exact Walk.vertices_zero_eq_source' p_tail
          have hmid_in_marg_of_s : mid ∈ G.marginalize {u} hu :=
            WalkStep.target_mem s
          have hmid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
          -- ### Build G.IsBlockableNonCollider 1.
          have h_G_blk :
              (Walk.cons mid s' p_tail).IsBlockableNonCollider 1 := by
            refine ⟨?_, ?_⟩
            · -- IsNonCollider 1: length bound + ¬ G.IsCollider 1.
              refine ⟨?_, ?_⟩
              · show 1 ≤ p_tail.length + 1; omega
              · intro h_G_coll
                apply h_blk.1.2
                cases htail with
                | nil_lift _ _ =>
                    cases s' <;> exact h_G_coll.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ _ _ =>
                    cases s' <;> cases s <;> cases s_x <;> cases s_marg <;>
                      first
                      | exact h_G_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mp h_G_coll.1
                          | exact hSrcᵢ.mp h_G_coll.2
                          | exact h_G_coll.1
                          | exact h_G_coll.2)
                      | exact h_G_coll.elim
                      | exact h_G_coll.2.elim
                      | exact h_G_coll.1.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner
                      hSrcᵢ _ _ _ =>
                    cases s' <;> cases s <;> cases s_x₁ <;> cases s_marg <;>
                      first
                      | exact h_G_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mp h_G_coll.1
                          | exact hSrcᵢ.mp h_G_coll.2
                          | exact h_G_coll.1
                          | exact h_G_coll.2)
                      | exact h_G_coll.elim
                      | exact h_G_coll.2.elim
                      | exact h_G_coll.1.elim
            · -- ### Disjunct: 1 = 0 ∨ 1 = length ∨ HBLS 1 ∨ HBRS 1.
              rcases h_blk.2 with h0 | hlen | hHBLS | hHBRS
              · omega
              · -- Length: 1 = (cons mid s p'').length = p''.length + 1, so p'' = nil.
                right; left
                cases htail with
                | nil_lift _ _ =>
                    show 1 = (Walk.cons mid s' (Walk.nil mid _)).length
                    simp [Walk.length]
                | @cons_one_edge _ mid_in _ s_marg p''_inner _ _ _ _ _ =>
                    exfalso; simp [Walk.length] at hlen
                | @cons_two_edge _ mid_in _ s_marg p''_inner _ _ _ _ _ _ _ =>
                    exfalso; simp [Walk.length] at hlen
              · -- HBLS 1: transport via marg_sc_iff_G_sc + a ≠ u.
                right; right; left
                -- HBLS 1 requires s = .backwardE.  Force s' = .backwardE
                -- via hSrc, hTgt (.backwardE has HeadAtSource = True,
                -- HeadAtTarget = False — uniquely matching s' from the iff).
                revert hHBLS
                cases s with
                | forwardE _ => intro hh; exact hh.elim
                | bidir _ => intro hh; exact hh.elim
                | backwardE _ =>
                    -- s = .backwardE: hSrc gives s'.HeadAtSource = True;
                    -- hTgt gives s'.HeadAtTarget = False. So s' = .backwardE.
                    intro hHBLS_marg
                    cases s' with
                    | forwardE _ => exact (hSrc.mpr trivial).elim
                    | bidir _ => exact (hTgt.mp trivial).elim
                    | backwardE he_mid_a =>
                        -- Goal: a ∉ G.Sc mid.
                        -- hHBLS_marg : a ∉ marg.Sc mid.
                        -- a ∈ G (target of (mid, a) ∈ G.E via .backwardE _).
                        intro h_a_G_sc
                        have ha_G : a ∈ G := Finset.mem_union_right _
                          (G.hE_subset he_mid_a).2
                        exact hHBLS_marg
                          ((marg_sc_iff_G_sc u hu hmid_in_marg_of_s
                              ha_G ha).mpr h_a_G_sc)
              · -- HBRS 1: case-analyze htail.
                right; right; right
                have hmid_ne_u_local : mid ≠ u := walkstep_target_ne_u hu s
                have h_NPL_tail : NoProblematicLift hu C p'' p_tail :=
                  NoProblematicLift.one_edge_inv s p'' s' p_tail
                      hmid_ne_u_local h_NPL
                cases htail with
                | nil_lift _ _ =>
                    exfalso
                    revert hHBRS
                    cases s <;> intro hh <;> exact hh.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ hTgtᵢ _ =>
                    -- HBRS_marg 1 fires via s_marg = .forwardE, says
                    -- mid_in ∉ marg.Sc mid.
                    have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                      WalkStep.target_mem s_marg
                    have hmid_in_ne_u : mid_in ≠ u :=
                      walkstep_target_ne_u hu s_marg
                    have hHBRS' :
                        (Walk.cons mid_in s_marg p''_inner).HasBlockingRightSlot 0 := by
                      cases s <;> exact hHBRS
                    cases s_marg with
                    | forwardE he_mid_midin_marg =>
                        -- hHBRS' : mid_in ∉ marg.Sc mid.
                        -- s_x.HeadAtSource = False (from hSrcᵢ); s_x.HeadAtTarget = True (hTgtᵢ).
                        -- So s_x = .forwardE.
                        cases s_x with
                        | forwardE he_mid_midin_G =>
                            -- Goal: outer_G.HBRS 1 = p_tail.HBRS 0
                            --     = (cons mid_in (.forwardE _) p_tail_inner).HBRS 0
                            --     = `mid_in ∉ G.Sc mid`.
                            suffices h_G :
                                (Walk.cons mid_in (.forwardE he_mid_midin_G)
                                    p_tail_inner).HasBlockingRightSlot 0 by
                              cases s' <;> exact h_G
                            intro h_mid_in_G_sc
                            have hmid_in_G : mid_in ∈ G :=
                              Finset.mem_union_right _ (G.hE_subset he_mid_midin_G).2
                            exact hHBRS'
                              ((marg_sc_iff_G_sc u hu hmid_in_marg_of_s
                                  hmid_in_G hmid_in_ne_u).mpr h_mid_in_G_sc)
                        | backwardE _ => exact (hSrcᵢ.mp trivial).elim
                        | bidir _ => exact (hSrcᵢ.mp trivial).elim
                    | backwardE _ => exact hHBRS'.elim
                    | bidir _ => exact hHBRS'.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁ s_x₂ p_tail_inner
                      hSrcᵢ hTgtᵢ hNonCollᵢ _ =>
                    have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                      WalkStep.target_mem s_marg
                    have hmid_in_ne_u : mid_in ≠ u :=
                      walkstep_target_ne_u hu s_marg
                    have hHBRS' :
                        (Walk.cons mid_in s_marg p''_inner).HasBlockingRightSlot 0 := by
                      cases s <;> exact hHBRS
                    cases s_marg with
                    | forwardE he_mid_midin_marg =>
                        -- hHBRS' : mid_in ∉ marg.Sc mid.
                        -- s_x₁.HeadAtSource = False; s_x₂.HeadAtTarget = True; hNonCollᵢ.
                        cases s_x₁ with
                        | forwardE h_mid_u_E =>
                            -- s_x₂: HeadAtTarget = True. hNonCollᵢ rules out HeadAtSource.
                            cases s_x₂ with
                            | forwardE h_u_midin_E =>
                                -- Goal: outer_G.HBRS 1 = p_tail.HBRS 0
                                --   = (cons u s_x₁ ...).HBRS 0 with s_x₁ = .forwardE.
                                -- That fires with `u ∉ G.Sc mid`.
                                by_cases h_u_G_sc : u ∈ G.Sc mid
                                · -- u ∈ G.Sc mid: use inner NPL forward.
                                  exfalso
                                  -- Extract inner NPL forward condition from
                                  -- the threaded h_NPL_tail.
                                  obtain ⟨h_fwd_inner, _, _⟩ :=
                                    NoProblematicLift.two_edge_inv
                                        (.forwardE he_mid_midin_marg) p''_inner
                                        (.forwardE h_mid_u_E) (.forwardE h_u_midin_E)
                                        p_tail_inner hmid_in_ne_u h_NPL_tail
                                  have hmid_in_marg_sc :
                                      mid_in ∈ (G.marginalize {u} hu).Sc mid :=
                                    h_fwd_inner ⟨fun h => h, trivial⟩
                                      hmid_C h_u_G_sc
                                  exact hHBRS' hmid_in_marg_sc
                                · -- u ∉ G.Sc mid: HBRS_G 1 fires.
                                  suffices h_G :
                                      (Walk.cons u (.forwardE h_mid_u_E)
                                          (Walk.cons mid_in (.forwardE h_u_midin_E)
                                              p_tail_inner)).HasBlockingRightSlot 0 by
                                    cases s' <;> exact h_G
                                  exact h_u_G_sc
                            | backwardE _ =>
                                exact (hNonCollᵢ ⟨trivial, trivial⟩).elim
                            | bidir _ =>
                                exact (hNonCollᵢ ⟨trivial, trivial⟩).elim
                        | backwardE _ => exact (hSrcᵢ.mp trivial).elim
                        | bidir _ => exact (hSrcᵢ.mp trivial).elim
                    | backwardE _ => exact hHBRS'.elim
                    | bidir _ => exact hHBRS'.elim
          exact h_outer_G_open.2 1 mid hmid_G_vert h_G_blk (by omega) hmid_C
      | succ k2 =>
          -- ## k = k2 + 2: transport from `h_tail_marg_open` at p'' pos k2 + 1.
          have hvk_tail : p''.vertices[k2 + 1]? = some vk := hk_vert
          have h_blk_tail : p''.IsBlockableNonCollider (k2 + 1) := by
            obtain ⟨h_nc, h_disj⟩ := h_blk
            refine ⟨?_, ?_⟩
            · refine ⟨?_, ?_⟩
              · have : k2 + 2 ≤ (Walk.cons mid s p'').length := h_nc.1
                show k2 + 1 ≤ p''.length
                simp [Walk.length] at this
                omega
              · intro h_tail_coll
                apply h_nc.2
                cases p'' with
                | nil v hv => exact h_tail_coll.elim
                | cons mid' s_x tail_inner =>
                    cases s <;> exact h_tail_coll
            · rcases h_disj with h0 | hlen | hHBLS | hHBRS
              · omega
              · right; left
                show k2 + 1 = p''.length
                simp [Walk.length] at hlen
                omega
              · right; right; left
                cases p'' with
                | nil v hv =>
                    exfalso
                    revert hHBLS
                    cases s <;> intro h <;> exact h.elim
                | cons mid' s_x tail_inner =>
                    revert hHBLS
                    cases s <;> exact id
              · right; right; right
                revert hHBRS
                cases s <;> exact id
          exact h_tail_marg_open.2 (k2 + 1) vk hvk_tail h_blk_tail (by omega)

-- ## ref: claim_3_25 (Subtask 8) — cons_two_edge case, collider clause
-- (reverse direction).
--
-- For the outer `cons mid s p''` (marg) lift of
-- `cons u s₁ (cons mid s₂ p_tail)` (G):
--   * position 0: vacuous via `isCollider_cons_zero_eq_false`.
--   * position 1 (= mid on marg, position 2 = mid on G): the
--     substantive transport.  Collider at position 1 on marg ⟺
--     collider at position 2 on G (since position 1 on G is `u`,
--     which is a non-collider via `hNonColl`).  Apply `hcol_C` at
--     position 2 to get `mid ∈ C`, then `subset_anc_set_marginalize_of_disjoint`
--     gives `mid ∈ marg.AncSet C`.
--   * position k + 2: transport via `h_tail_marg_open` at p''
--     position k + 1.
private lemma sigma_open_interior_lift_reverse_cons_two_edge_collider_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid) (p_tail : Walk G mid b)
    (hTgt : s₂.HeadAtTarget ↔ s.HeadAtTarget)
    (hNonColl : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource))
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_G_open_coll : ∀ k vk,
        (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).vertices[k]? = some vk →
        (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).IsCollider k →
        vk ∈ G.AncSet C)
    (h_tail_marg_open : IsSigmaOpenAtInterior p'' C hC_marg) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons mid s p'').vertices[k]? = some vk →
      (Walk.cons mid s p'').IsCollider k →
      vk ∈ (G.marginalize {u} hu).AncSet C := by
  intro k vk hk_vert h_coll
  cases k with
  | zero =>
      rw [isCollider_cons_zero_eq_false s p''] at h_coll
      exact h_coll.elim
  | succ k1 =>
      cases k1 with
      | zero =>
          -- k = 1: substantive — collider on outer marg at mid.
          have hvk_mid : vk = mid := by
            have h1 : (Walk.cons mid s p'').vertices[1]? = some mid := by
              show p''.vertices[0]? = some mid
              exact Walk.vertices_zero_eq_source' p''
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_mid]
          have h_G_coll :
              (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).IsCollider 2 := by
            cases htail with
            | nil_lift _ _ =>
                exfalso
                revert h_coll
                cases s <;> intro hh <;> exact hh.elim
            | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                  hSrcᵢ _ _ =>
                cases s₁ <;> cases s₂ <;> cases s <;>
                  cases s_x <;> cases s_marg <;>
                  first
                  | exact h_coll
                  | (refine ⟨?_, ?_⟩ <;> first
                      | exact hTgt.mpr h_coll.1
                      | exact hSrcᵢ.mpr h_coll.2
                      | exact h_coll.1
                      | exact h_coll.2)
                  | exact h_coll.elim
                  | exact h_coll.2.elim
                  | exact h_coll.1.elim
            | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁_inner s_x₂_inner
                  p_tail_inner hSrcᵢ _ _ _ =>
                cases s₁ <;> cases s₂ <;> cases s <;>
                  cases s_x₁_inner <;> cases s_marg <;>
                  first
                  | exact h_coll
                  | (refine ⟨?_, ?_⟩ <;> first
                      | exact hTgt.mpr h_coll.1
                      | exact hSrcᵢ.mpr h_coll.2
                      | exact h_coll.1
                      | exact h_coll.2)
                  | exact h_coll.elim
                  | exact h_coll.2.elim
                  | exact h_coll.1.elim
          have hmid_G_vert :
              (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).vertices[2]? =
                some mid := by
            show p_tail.vertices[0]? = some mid
            exact Walk.vertices_zero_eq_source' p_tail
          -- Resolution A: read `mid ∈ G.AncSet C` off σ-open's collider
          -- clause directly, then transport via the carrier intersection.
          have hmid_AncG : mid ∈ G.AncSet C :=
            h_G_open_coll 2 mid hmid_G_vert h_G_coll
          have hmid_G : mid ∈ G := WalkStep.target_mem (G := G) s₂
          have hmid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
          have hmid_marg : mid ∈ G.marginalize {u} hu := by
            change mid ∈ G.J ∪ (G.V \ ({u} : Finset Node))
            rcases Finset.mem_union.mp hmid_G with hJ | hV
            · exact Finset.mem_union_left _ hJ
            · refine Finset.mem_union_right _
                (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
              intro hmem
              exact hmid_ne_u (Finset.mem_singleton.mp hmem)
          have hmid_carrier_set :
              mid ∈ ((↑G.J : Set Node) ∪ ↑(G.V \ ({u} : Finset Node))) := by
            have h_union : mid ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := hmid_marg
            rcases Finset.mem_union.mp h_union with hJ | hVW
            · exact Or.inl (Finset.mem_coe.mpr hJ)
            · exact Or.inr (Finset.mem_coe.mpr hVW)
          have h_eq := anc_set_marginalize_eq_inter_carrier
            G ({u} : Finset Node) hu C hC_G hC_disj
          rw [h_eq]
          exact Set.mem_inter hmid_AncG hmid_carrier_set
      | succ k2 =>
          -- k = k2 + 2: transport from `h_tail_marg_open` at p'' pos k2 + 1.
          have hvk_tail : p''.vertices[k2 + 1]? = some vk := hk_vert
          have h_tail_coll : p''.IsCollider (k2 + 1) := by
            cases p'' with
            | nil v hv =>
                revert h_coll
                cases s <;> intro hh <;> exact hh.elim
            | cons mid' s_x tail_inner =>
                revert h_coll
                cases s <;> exact id
          exact h_tail_marg_open.1 (k2 + 1) vk hvk_tail h_tail_coll

-- ## ref: claim_3_25 (Subtask 8) — cons_two_edge case, blockable clause
-- (reverse direction).
--
-- The substantive helper for the residual case.  For the outer
-- `cons mid s p''` (marg) lift of `cons u s₁ (cons mid s₂ p_tail)` (G):
--   * position 0: vacuous via `h_pos`.
--   * position 1 (= mid on marg, position 2 = mid on G): the
--     substantive case.  By contradiction (mid ∈ C), build outer_G's
--     `IsBlockableNonCollider 2` and apply `h_outer_G_open.2`.  The
--     length disjunct forces `htail = nil_lift`; HBLS substantive
--     dispatches via `by_cases u ∈ G.Sc mid`: yes → use outer NPL
--     backward direction to derive `a ∈ marg.Sc mid` contradicting
--     `HBLS_marg`; no → fires HBLS_G via `u ∉ G.Sc mid`.  HBRS
--     substantive mirrors but uses the inner NPL forward (extracted
--     via `one_edge_inv` then `two_edge_inv`) when the inner is
--     `cons_two_edge_inner`.
--   * position k + 2: transport from `h_tail_marg_open` at p''
--     position k + 1.
set_option maxHeartbeats 800000 in
private lemma sigma_open_interior_lift_reverse_cons_two_edge_blockable_clause
    {G : CDMG Node} {u : Node} (hu : ({u} : Finset Node) ⊆ G.V)
    {a mid b : Node}
    (s : WalkStep (G.marginalize {u} hu) a mid)
    (p'' : Walk (G.marginalize {u} hu) mid b)
    (s₁ : WalkStep G a u) (s₂ : WalkStep G u mid) (p_tail : Walk G mid b)
    (hSrc : s₁.HeadAtSource ↔ s.HeadAtSource)
    (hTgt : s₂.HeadAtTarget ↔ s.HeadAtTarget)
    (hNonColl : ¬(s₁.HeadAtTarget ∧ s₂.HeadAtSource))
    (htail : IsLift G u hu p'' p_tail)
    (C : Set Node) (hu_notC : u ∉ C)
    (h_NPL : NoProblematicLift hu C (Walk.cons mid s p'')
        (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)))
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V)
    (h_outer_G_open : IsSigmaOpenAtInterior
      (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)) C hC_G)
    (h_tail_marg_open : IsSigmaOpenAtInterior p'' C hC_marg) :
    ∀ (k : ℕ) (vk : Node),
      (Walk.cons mid s p'').vertices[k]? = some vk →
      (Walk.cons mid s p'').IsBlockableNonCollider k → 1 ≤ k →
      vk ∉ C := by
  intro k vk hk_vert h_blk h_pos
  cases k with
  | zero => omega
  | succ k1 =>
      cases k1 with
      | zero =>
          -- ## k = 1: substantive — vk = mid.
          intro hmid_C
          have hvk_mid : vk = mid := by
            have h1 : (Walk.cons mid s p'').vertices[1]? = some mid := by
              show p''.vertices[0]? = some mid
              exact Walk.vertices_zero_eq_source' p''
            rw [h1] at hk_vert
            exact (Option.some.inj hk_vert).symm
          rw [hvk_mid] at hmid_C
          have hmid_G_vert :
              (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).vertices[2]? = some mid := by
            show p_tail.vertices[0]? = some mid
            exact Walk.vertices_zero_eq_source' p_tail
          have hmid_in_marg_of_s : mid ∈ G.marginalize {u} hu :=
            WalkStep.target_mem s
          have hmid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
          -- Extract NPL forward and backward from outer NPL.
          obtain ⟨h_NPL_fwd, h_NPL_bwd, h_NPL_tail⟩ :=
            NoProblematicLift.two_edge_inv s p'' s₁ s₂ p_tail hmid_ne_u h_NPL
          -- ### Build outer_G.IsBlockableNonCollider 2.
          have h_G_blk :
              (Walk.cons u s₁ (Walk.cons mid s₂ p_tail)).IsBlockableNonCollider 2 := by
            refine ⟨?_, ?_⟩
            · -- IsNonCollider 2 on outer_G.
              refine ⟨?_, ?_⟩
              · show 2 ≤ p_tail.length + 2; omega
              · intro h_G_coll
                apply h_blk.1.2
                -- Transport collider from G to marg.
                cases htail with
                | nil_lift _ _ =>
                    cases s₁ <;> cases s₂ <;> exact h_G_coll.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ _ _ =>
                    cases s₁ <;> cases s₂ <;> cases s <;>
                      cases s_x <;> cases s_marg <;>
                      first
                      | exact h_G_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mp h_G_coll.1
                          | exact hSrcᵢ.mp h_G_coll.2
                          | exact h_G_coll.1
                          | exact h_G_coll.2)
                      | exact h_G_coll.elim
                      | exact h_G_coll.2.elim
                      | exact h_G_coll.1.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁_inner s_x₂_inner
                      p_tail_inner hSrcᵢ _ _ _ =>
                    cases s₁ <;> cases s₂ <;> cases s <;>
                      cases s_x₁_inner <;> cases s_marg <;>
                      first
                      | exact h_G_coll
                      | (refine ⟨?_, ?_⟩ <;> first
                          | exact hTgt.mp h_G_coll.1
                          | exact hSrcᵢ.mp h_G_coll.2
                          | exact h_G_coll.1
                          | exact h_G_coll.2)
                      | exact h_G_coll.elim
                      | exact h_G_coll.2.elim
                      | exact h_G_coll.1.elim
            · -- ### Disjunct.
              rcases h_blk.2 with h0 | hlen | hHBLS | hHBRS
              · omega
              · -- length: 1 = outer_marg.length → p'' = nil → htail = nil_lift → p_tail = nil.
                right; left
                cases htail with
                | nil_lift _ _ =>
                    show 2 = (Walk.cons u s₁ (Walk.cons mid s₂ (Walk.nil mid _))).length
                    simp [Walk.length]
                | @cons_one_edge _ _ _ _ _ _ _ _ _ _ =>
                    exfalso; simp [Walk.length] at hlen
                | @cons_two_edge _ _ _ _ _ _ _ _ _ _ _ _ =>
                    exfalso; simp [Walk.length] at hlen
              · -- HBLS_marg 1: s = .backwardE, a ∉ marg.Sc mid.
                -- Force s₁ = .backwardE, s₂ = .backwardE; then by_cases u ∈ G.Sc mid.
                revert hHBLS
                cases s with
                | forwardE _ => intro hh; exact hh.elim
                | bidir _ => intro hh; exact hh.elim
                | backwardE _ =>
                    intro hHBLS_marg
                    cases s₁ with
                    | forwardE _ => exact (hSrc.mpr trivial).elim
                    | bidir _ =>
                        -- s₁.HeadAtTarget = True; hNonColl: ¬ (True ∧ s₂.HeadAtSource).
                        -- So s₂.HeadAtSource = False, s₂ = .forwardE.
                        -- But hTgt.mp trivial: s₂.HeadAtTarget = True implies s.HeadAtTarget = True,
                        -- but s = .backwardE has HeadAtTarget = False. Contradiction.
                        cases s₂ with
                        | forwardE _ => exact (hTgt.mp trivial).elim
                        | backwardE _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                        | bidir _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                    | backwardE he_u_a =>
                        cases s₂ with
                        | forwardE _ => exact (hTgt.mp trivial).elim
                        | bidir _ => exact (hTgt.mp trivial).elim
                        | backwardE he_mid_u =>
                            -- s = .backwardE, s₁ = .backwardE, s₂ = .backwardE.
                            by_cases h_u_G_sc : u ∈ G.Sc mid
                            · -- NPL_bwd gives a ∈ marg.Sc mid, contradicts HBLS_marg.
                              exfalso
                              have h_a_marg_sc :
                                  a ∈ (G.marginalize {u} hu).Sc mid :=
                                h_NPL_bwd ⟨trivial, fun h => h⟩
                                    hmid_C h_u_G_sc
                              exact hHBLS_marg h_a_marg_sc
                            · -- u ∉ G.Sc mid: HBLS_G 2 fires.
                              right; right; left
                              show (Walk.cons u (.backwardE he_u_a)
                                  (Walk.cons mid (.backwardE he_mid_u)
                                      p_tail)).HasBlockingLeftSlot 2
                              -- HBLS 2 on (cons u s₁ (cons mid s₂ p_tail)) reduces
                              -- to (cons mid s₂ p_tail).HBLS 1 = `u ∉ G.Sc mid`.
                              exact h_u_G_sc
              · -- HBRS_marg 1: p''.first = .forwardE, mid_in ∉ marg.Sc mid.
                cases htail with
                | nil_lift _ _ =>
                    exfalso
                    revert hHBRS
                    cases s <;> intro hh <;> exact hh.elim
                | @cons_one_edge _ mid_in _ s_marg p''_inner s_x p_tail_inner
                      hSrcᵢ hTgtᵢ _ =>
                    have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                      WalkStep.target_mem s_marg
                    have hmid_in_ne_u : mid_in ≠ u :=
                      walkstep_target_ne_u hu s_marg
                    have hHBRS' :
                        (Walk.cons mid_in s_marg p''_inner).HasBlockingRightSlot 0 := by
                      cases s <;> exact hHBRS
                    cases s_marg with
                    | forwardE he_mid_midin_marg =>
                        cases s_x with
                        | forwardE he_mid_midin_G =>
                            right; right; right
                            -- Goal: outer_G.HBRS 2 reduces to p_tail.HBRS 0
                            --     = `mid_in ∉ G.Sc mid`.
                            have hmid_in_G : mid_in ∈ G :=
                              Finset.mem_union_right _
                                (G.hE_subset he_mid_midin_G).2
                            suffices h_G :
                                (Walk.cons mid_in (.forwardE he_mid_midin_G)
                                    p_tail_inner).HasBlockingRightSlot 0 by
                              cases s₁ <;> cases s₂ <;> exact h_G
                            intro h_mid_in_G_sc
                            exact hHBRS'
                              ((marg_sc_iff_G_sc u hu hmid_in_marg_of_s
                                  hmid_in_G hmid_in_ne_u).mpr h_mid_in_G_sc)
                        | backwardE _ => exact (hSrcᵢ.mp trivial).elim
                        | bidir _ => exact (hSrcᵢ.mp trivial).elim
                    | backwardE _ => exact hHBRS'.elim
                    | bidir _ => exact hHBRS'.elim
                | @cons_two_edge _ mid_in _ s_marg p''_inner s_x₁_inner s_x₂_inner
                      p_tail_inner hSrcᵢ hTgtᵢ hNonCollᵢ _ =>
                    have hmid_in_marg : mid_in ∈ G.marginalize {u} hu :=
                      WalkStep.target_mem s_marg
                    have hmid_in_ne_u : mid_in ≠ u :=
                      walkstep_target_ne_u hu s_marg
                    have hHBRS' :
                        (Walk.cons mid_in s_marg p''_inner).HasBlockingRightSlot 0 := by
                      cases s <;> exact hHBRS
                    cases s_marg with
                    | forwardE he_mid_midin_marg =>
                        cases s_x₁_inner with
                        | forwardE h_mid_u_E =>
                            cases s_x₂_inner with
                            | forwardE h_u_midin_E =>
                                -- Inner NPL forward applies.
                                by_cases h_u_G_sc : u ∈ G.Sc mid
                                · -- NPL_tail's inner forward gives mid_in ∈ marg.Sc mid.
                                  exfalso
                                  obtain ⟨h_fwd_inner, _, _⟩ :=
                                    NoProblematicLift.two_edge_inv
                                        (.forwardE he_mid_midin_marg) p''_inner
                                        (.forwardE h_mid_u_E) (.forwardE h_u_midin_E)
                                        p_tail_inner hmid_in_ne_u h_NPL_tail
                                  have hmid_in_marg_sc :
                                      mid_in ∈ (G.marginalize {u} hu).Sc mid :=
                                    h_fwd_inner ⟨fun h => h, trivial⟩
                                      hmid_C h_u_G_sc
                                  exact hHBRS' hmid_in_marg_sc
                                · right; right; right
                                  -- HBRS_G 2 reduces to HBRS 0 on the inner p_tail.
                                  -- p_tail = cons u (.forwardE h_mid_u_E) (...).
                                  -- HBRS 0 fires with `u ∉ G.Sc mid`.
                                  suffices h_G :
                                      (Walk.cons u (.forwardE h_mid_u_E)
                                          (Walk.cons mid_in (.forwardE h_u_midin_E)
                                              p_tail_inner)).HasBlockingRightSlot 0 by
                                    cases s₁ <;> cases s₂ <;> exact h_G
                                  exact h_u_G_sc
                            | backwardE _ =>
                                exact (hNonCollᵢ ⟨trivial, trivial⟩).elim
                            | bidir _ =>
                                exact (hNonCollᵢ ⟨trivial, trivial⟩).elim
                        | backwardE _ => exact (hSrcᵢ.mp trivial).elim
                        | bidir _ => exact (hSrcᵢ.mp trivial).elim
                    | backwardE _ => exact hHBRS'.elim
                    | bidir _ => exact hHBRS'.elim
          exact h_outer_G_open.2 2 mid hmid_G_vert h_G_blk (by omega) hmid_C
      | succ k2 =>
          -- ## k = k2 + 2: transport from `h_tail_marg_open` at p'' pos k2 + 1.
          have hvk_tail : p''.vertices[k2 + 1]? = some vk := hk_vert
          have h_blk_tail : p''.IsBlockableNonCollider (k2 + 1) := by
            obtain ⟨h_nc, h_disj⟩ := h_blk
            refine ⟨?_, ?_⟩
            · refine ⟨?_, ?_⟩
              · have : k2 + 2 ≤ (Walk.cons mid s p'').length := h_nc.1
                show k2 + 1 ≤ p''.length
                simp [Walk.length] at this
                omega
              · intro h_tail_coll
                apply h_nc.2
                cases p'' with
                | nil v hv => exact h_tail_coll.elim
                | cons mid' s_x tail_inner =>
                    cases s <;> exact h_tail_coll
            · rcases h_disj with h0 | hlen | hHBLS | hHBRS
              · omega
              · right; left
                show k2 + 1 = p''.length
                simp [Walk.length] at hlen
                omega
              · right; right; left
                cases p'' with
                | nil v hv =>
                    exfalso
                    revert hHBLS
                    cases s <;> intro h <;> exact h.elim
                | cons mid' s_x tail_inner =>
                    revert hHBLS
                    cases s <;> exact id
              · right; right; right
                revert hHBRS
                cases s <;> exact id
          exact h_tail_marg_open.2 (k2 + 1) vk hvk_tail h_blk_tail (by omega)

-- ## ref: claim_3_25 (Subtask 8) — main σ-open' preservation lemma
-- (reverse direction).
--
-- Wraps the four cell-case helpers above into a single induction on
-- `IsLift`.  At each cons cell, the IH is fed by:
--   * the G-side tail σ-open' (which carries its own collider /
--     blockable clauses).
--   * `walkstep_target_ne_u` (target of `s` is ≠ `u`).
--   * `sigma_open_interior_cons_tail` (G-side tail σ-open' from
--     outer σ-open').
--   * `NoProblematicLift.one_edge_inv` / `two_edge_inv` to extract
--     the tail NPL from the outer NPL.
--
-- Resolution-A weakening (workspace 2026-06-25): the original
-- `hcol_C` ("every collider in `C`") strengthened-witness hypothesis
-- has been dropped.  The collider clause is now read off the outer
-- σ-open' (`h_outer_G.1`) directly and passed in `G.AncSet C` form to
-- the two collider-clause cell helpers (which transport to
-- `marg.AncSet C` via `anc_set_marginalize_eq_inter_carrier`).
-- Matches LN tex line 268's collider obligation
-- `b_l ∈ \Anc^{G^{\sm u}}(C)` (no strict `b_l ∈ C` needed).
private lemma sigma_open_interior_lift_reverse_via_isLift
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (C : Set Node) (hu_notC : u ∉ C)
    (hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C)
    (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                   ↑(G.marginalize {u} hu).V) :
    ∀ {a b : Node} {p' : Walk (G.marginalize {u} hu) a b}
      {p : Walk G a b},
      IsLift G u hu p' p → a ≠ u → b ≠ u →
      IsSigmaOpenAtInterior p C hC_G →
      NoProblematicLift hu C p' p →
      IsSigmaOpenAtInterior p' C hC_marg := by
  intro a b p' p hlift
  induction hlift with
  | nil_lift hv_marg _ =>
      intros _ _ _ _
      exact sigma_open_interior_lift_reverse_nil_case hu _ hv_marg C hC_marg
  | @cons_one_edge a' mid b' s p'' s' p_tail hSrc hTgt htail ih =>
      intros ha hb h_outer_G h_NPL
      have h_mid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
      -- Build the G-side tail σ-open' from outer_G via cons_tail.
      have h_tail_G_open :=
        sigma_open_interior_cons_tail s' p_tail C hC_G h_outer_G
      -- Extract tail NPL.
      have h_NPL_tail : NoProblematicLift hu C p'' p_tail :=
        NoProblematicLift.one_edge_inv s p'' s' p_tail h_mid_ne_u h_NPL
      have h_tail_marg_open :=
        ih h_mid_ne_u hb h_tail_G_open h_NPL_tail
      refine ⟨?_, ?_⟩
      · exact sigma_open_interior_lift_reverse_cons_one_edge_collider_clause
          hu s p'' s' p_tail hTgt htail C hC_disj hC_G hC_marg
          h_outer_G.1 h_tail_marg_open
      · exact sigma_open_interior_lift_reverse_cons_one_edge_blockable_clause
          hu s p'' s' p_tail hSrc hTgt htail ha C h_NPL hC_G hC_marg
          h_outer_G h_tail_marg_open
  | @cons_two_edge a' mid b' s p'' s₁ s₂ p_tail hSrc hTgt hNonColl htail ih =>
      intros ha hb h_outer_G h_NPL
      have h_mid_ne_u : mid ≠ u := walkstep_target_ne_u hu s
      -- Build the G-side tail σ-open' from outer_G via TWO cons_tail steps.
      have h_skip_u :=
        sigma_open_interior_cons_tail s₁ (Walk.cons mid s₂ p_tail) C hC_G h_outer_G
      have h_tail_G_open :=
        sigma_open_interior_cons_tail s₂ p_tail C hC_G h_skip_u
      -- Extract tail NPL from outer two_edge_npl.
      have h_NPL_tail : NoProblematicLift hu C p'' p_tail := by
        obtain ⟨_, _, h_tail⟩ :=
          NoProblematicLift.two_edge_inv s p'' s₁ s₂ p_tail h_mid_ne_u h_NPL
        exact h_tail
      have h_tail_marg_open :=
        ih h_mid_ne_u hb h_tail_G_open h_NPL_tail
      refine ⟨?_, ?_⟩
      · exact sigma_open_interior_lift_reverse_cons_two_edge_collider_clause
          hu s p'' s₁ s₂ p_tail hTgt hNonColl htail C hC_disj hC_G hC_marg
          h_outer_G.1 h_tail_marg_open
      · exact sigma_open_interior_lift_reverse_cons_two_edge_blockable_clause
          hu s p'' s₁ s₂ p_tail hSrc hTgt hNonColl htail C hu_notC h_NPL
          hC_G hC_marg h_outer_G h_tail_marg_open

-- ## ref: claim_3_25 (Subtask 9, helper) — directed-path-clean-head.
--
-- Given a directed walk `p : Walk G u v` with `u ≠ v`, extract a
-- "clean" first successor of `u`: a vertex `w` with
-- `(u, w) ∈ G.E`, `w ≠ u`, and a directed walk `p' : Walk G w v`.
-- The output drops any leading self-loops `u → u → ...` from `p`
-- so the first edge of the cleaned witness leaves the source.
--
-- ## Purpose for Subtask 9's surgery
--
-- The LN's tex-line 273-285 surgery picks the auxiliary node `w`
-- as "the successor of u on a directed path u → ... → b_l".  The tex
-- argues `w ≠ u` "unless the path is the length-0 'u itself',
-- impossible since the path goes from u to b_l ≠ u".  This wording
-- silently assumes the path's first edge doesn't loop back to `u`;
-- in Lean we must produce a witness that explicitly enforces it.
-- This helper does the leading-self-loop removal: structurally
-- induct on `p.length`; whenever the first edge is `u → u`, recurse
-- on the strictly shorter tail.  The recursion terminates because
-- every self-loop strictly decreases the walk length, and the base
-- case `length = 0` (i.e., `Walk.nil`) is impossible from `u ≠ v`.
--
-- ## Design choice — return type as an `∃` quadruple
--
-- The output bundles `⟨w, h_uw, h_w_ne_u, ⟨p', h_dir'⟩⟩` (the
-- inner `∃ p'` is propositionally redundant under classical logic
-- but needed in Lean's `Type _`-valued `Walk` setting to record the
-- *witness path* explicitly).  Downstream Subtask 9 unpacks the
-- quadruple at the surgery site to (a) construct the new edge
-- `(u, w) ∈ G.E` for the surgical 4-edge G-segment, and (b) feed
-- `p'` into `Anc.trans` to recover `w ∈ G.Anc(v)` (one half of
-- `w ∈ G.Sc(v)`).
private lemma directed_path_clean_head
    {G : CDMG Node} {u v : Node} (h_uv_ne : u ≠ v)
    (p : Walk G u v) (h_dir : p.IsDirectedWalk) :
    ∃ (w : Node), (u, w) ∈ G.E ∧ w ≠ u ∧
      ∃ (p' : Walk G w v), p'.IsDirectedWalk := by
  -- Strong induction on length: self-loop-removal recurses one
  -- cell deep on the tail, so structural induction suffices, but
  -- we package as length-induction for clarity of termination.
  suffices aux :
      ∀ (n : ℕ), ∀ (q : Walk G u v), q.length = n →
        q.IsDirectedWalk →
        ∃ (w : Node), (u, w) ∈ G.E ∧ w ≠ u ∧
          ∃ (q' : Walk G w v), q'.IsDirectedWalk by
    exact aux p.length p rfl h_dir
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q h_len h_q_dir
    cases q with
    | nil _ _ =>
        -- Walk.nil : Walk G v v.  Source = target = u.  But u ≠ v.
        exact absurd rfl h_uv_ne
    | @cons _ _ mid s_first p_rest =>
        cases s_first with
        | forwardE h_uw =>
            -- `h_q_dir : (cons mid (.forwardE h_uw) p_rest).IsDirectedWalk`
            -- reduces by `Walk.IsDirectedWalk` to `p_rest.IsDirectedWalk`.
            have h_dir_rest : p_rest.IsDirectedWalk := h_q_dir
            by_cases h_mid_eq : mid = u
            · -- Leading self-loop u → u.  Recurse on p_rest (strictly
              -- shorter; `(Walk.cons _ _ p_rest).length = p_rest.length + 1`).
              -- Symmetrise then `subst`: Lean 4's `subst h : a = b`
              -- eliminates the RHS `b`, so to keep `u` and eliminate
              -- `mid` we feed `h_u_eq_mid : u = mid` (the symmetric).
              -- Pattern from 7c line 3835.
              have h_u_eq_mid : u = mid := h_mid_eq.symm
              subst h_u_eq_mid
              have h_rest_lt : p_rest.length < n := by
                have h_eq :
                    (Walk.cons u (.forwardE h_uw) p_rest).length
                      = p_rest.length + 1 := rfl
                omega
              exact ih p_rest.length h_rest_lt p_rest rfl h_dir_rest
            · -- First step `u → mid` with `mid ≠ u` — done.
              exact ⟨mid, h_uw, h_mid_eq, p_rest, h_dir_rest⟩
        | backwardE _ =>
            -- `.backwardE` in a directed walk: `IsDirectedWalk` reduces
            -- to `False` by the `backwardE` rewrite of the defining
            -- equation (Walks.lean:944).
            exact h_q_dir.elim
        | bidir _ =>
            -- Same reasoning as `.backwardE`: `Walks.lean:945` gives
            -- `False` for `.bidir`.
            exact h_q_dir.elim

-- ## ref: claim_3_25 (Subtask 9, helper) — Sc-clean successor.
--
-- Given `u ∈ G.Sc(a)` with `a ≠ u`, extract a vertex `w`
-- satisfying:
--   * `(u, w) ∈ G.E` (so the surgery's single-edge `u → w` step is
--     well-typed),
--   * `w ≠ u` (a-priori the surgery requires this; ensured by
--     `directed_path_clean_head`'s self-loop removal),
--   * `w ∈ G.Sc(a)` (both `w ∈ G.Anc(a)` from the tail of the
--     cleaned `u → ... → a` directed path, AND `w ∈ G.Desc(a)`
--     from extending the `a → ... → u` directed walk by the new
--     edge `u → w`).
--
-- This is the surgical-`w` extractor for the (fw, fw) and (bw, bw)
-- problematic cases of Subtask 9's main lemma.
private lemma sc_clean_successor
    {G : CDMG Node} {u a : Node} (h_a_ne_u : a ≠ u)
    (h_u_in_Sc_a : u ∈ G.Sc a) :
    ∃ (w : Node), (u, w) ∈ G.E ∧ w ≠ u ∧ w ∈ G.Sc a := by
  obtain ⟨h_u_in_Anc_a, h_u_in_Desc_a⟩ := h_u_in_Sc_a
  obtain ⟨_huG, p_u_to_a, h_u_to_a_dir⟩ := h_u_in_Anc_a
  have h_u_ne_a : u ≠ a := fun h => h_a_ne_u h.symm
  obtain ⟨w, h_uw, h_w_ne_u, p_w_to_a, h_w_to_a_dir⟩ :=
    directed_path_clean_head h_u_ne_a p_u_to_a h_u_to_a_dir
  have h_w_GV : w ∈ G.V := (G.hE_subset h_uw).2
  have h_w_G : w ∈ G := Finset.mem_union_right _ h_w_GV
  refine ⟨w, h_uw, h_w_ne_u, ?_, ?_⟩
  · -- w ∈ G.Anc a: directly from p_w_to_a (directed walk w → a).
    exact ⟨h_w_G, p_w_to_a, h_w_to_a_dir⟩
  · -- w ∈ G.Desc a: extend p_a_to_u by edge u → w.
    obtain ⟨_haG, p_a_to_u, h_a_to_u_dir⟩ := h_u_in_Desc_a
    let single : Walk G u w := Walk.cons w (.forwardE h_uw) (.nil w h_w_G)
    have h_single_dir : single.IsDirectedWalk := True.intro
    exact ⟨h_w_G, p_a_to_u.comp single,
           Walk.isDirectedWalk_comp _ _ h_a_to_u_dir h_single_dir⟩

-- ## ref: claim_3_25 (Subtask 9) — walk-surgery producing an
-- NPL-clean lift (Resolution-A version).
--
-- Given a σ-open G-walk `p` with all of 7a/7a-2's preprocessing
-- invariants (u-non-collider, no-consecutive-u, NoBifurcationSideTrip),
-- produce `p_fixed : Walk G a b` and `p'_fixed : Walk marg a b` such
-- that:
--   (1) `p_fixed` preserves all of 7a/7a-2's invariants;
--   (2) `p_fixed` is σ-open in G (with the LN-faithful collider clause
--       `vk ∈ G.AncSet C`, not the strict `vk ∈ C` strengthening — this
--       matches Subtask 8's Resolution-A weakened hypothesis profile);
--   (3) `IsLift G u hu p'_fixed p_fixed` holds;
--   (4) `NoProblematicLift hu C p'_fixed p_fixed` holds, gating
--       Subtask 8's reverse σ-open transport.
--
-- The recursion mirrors 7c (`exists_isLift_of_walk_G`, line 3796),
-- adding NPL + σ-open + invariant proofs at each cell, plus
-- surgical insertion at the (fw, fw) and (bw, bw) NPL-problematic
-- cells per tex lines 273–285.
--
-- ## Design — strong induction on `p.length`, mirroring 7c
--
-- Cell dispatch (mirroring 7c's structure):
--   * `nil`: trivial; `p_fixed = nil`, `p'_fixed = nil`, NPL = `.nil_npl`.
--   * `cons mid s' p_tail` with `mid ≠ u`: 1-edge G-cell; recurse on
--     `p_tail` (length n-1), build `IsLift.cons_one_edge` and
--     `.one_edge_npl` over the recursive result.
--   * `cons u s' (cons mid' s₂ p_tail_inner)`: 2-edge dispatch on `(s', s₂)`.
--     * Side-trip (a = mid'): only (fw, fw) and (bw, bw) survive
--       (others ruled out by `h_no_bif`/`hNonColl`); the marg-cell is a
--       self-loop, NPL discharged by `a ∈ marg.Sc a` reflexivity.
--     * Non-side-trip (a ≠ mid'):
--       - 4 collider patterns ((fw,bw), (fw,bd), (bd,bw), (bd,bd)):
--         ruled out by `hu_nc`'s u-non-collider hypothesis.
--       - 3 vacuous-NPL patterns ((bw,fw), (bw,bd), (bd,fw)): marg-step
--         is `.bidir`, NPL trivially vacuous.
--       - (fw, fw): by_cases on the problematic condition
--         `a ∈ C ∧ u ∈ G.Sc a ∧ mid' ∉ marg.Sc a`.
--         * Non-problematic: keep cell as-is; NPL.h_fwd discharged
--           by case-analysis on the False conjunct of the negation.
--         * Problematic: apply the LN's 4-edge surgery
--           `a → u → w ← u → mid'` where `w` is the cleaned successor
--           of `u` on a directed path `u → ... → a` (via
--           `sc_clean_successor`).  The new lift has two `.two_edge_npl`
--           cells: outer with `s_marg = .forwardE`, inner with
--           `s_marg = .bidir`.  NPL.h_fwd discharged by
--           `w ∈ marg.Sc a` (which holds by construction).
--       - (bw, bw): symmetric problematic-vs-not by_cases.
--
-- The deliverable's `<σ-open p_fixed in G>` is `IsSigmaOpenAtInterior`
-- (the same shape Subtask 8 consumes).
--
-- For details of each cell's design, see the inline `-- Cell: ...`
-- comments below.  The full Phase-2 design is documented in
-- `workspace_claim_3_25.md` under "Subtask 9 — PHASE 1 DELIVERY
-- 2026-06-25 (Resolution A landed)" → "Worker handoff for Subtask 9
-- — Phase 2".
-- Internal note (Phase 2): the recursive output below carries an
-- extra "first-step preservation" conjunct (`h_fst`), needed to
-- discharge σ-openness at the outer cell's mid-position during
-- the inductive step.  Surgery and side-trip handling all preserve
-- the cell's first WalkStep verbatim, so the conjunct is honoured
-- at every recursive case.  The outer caller does not need it
-- (Subtask 10 only consumes σ-open + IsLift + NPL).
set_option maxHeartbeats 1600000 in
private lemma exists_NPL_clean_lift_of_walk_G
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (C : Set Node) (hC_G : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hu_notC : u ∉ C) :
    ∀ {a b : Node} (p : Walk G a b),
      a ≠ u → b ≠ u →
      (∀ k, p.vertices[k]? = some u → p.IsNonCollider k) →
      (∀ k, p.vertices[k]? = some u → p.vertices[k+1]? ≠ some u) →
      NoBifurcationSideTrip p u →
      IsSigmaOpenAtInterior p C hC_G →
      ∃ (p_fixed : Walk G a b),
        (∀ k, p_fixed.vertices[k]? = some u → p_fixed.IsNonCollider k) ∧
        (∀ k, p_fixed.vertices[k]? = some u → p_fixed.vertices[k+1]? ≠ some u) ∧
        NoBifurcationSideTrip p_fixed u ∧
        IsSigmaOpenAtInterior p_fixed C hC_G ∧
        ∃ (p'_fixed : Walk (G.marginalize {u} hu) a b),
            IsLift G u hu p'_fixed p_fixed ∧
            NoProblematicLift hu C p'_fixed p_fixed := by
  suffices aux :
      ∀ (n : ℕ), ∀ {a' b' : Node} (p : Walk G a' b'), p.length = n →
        a' ≠ u → b' ≠ u →
        (∀ k, p.vertices[k]? = some u → p.IsNonCollider k) →
        (∀ k, p.vertices[k]? = some u → p.vertices[k+1]? ≠ some u) →
        NoBifurcationSideTrip p u →
        IsSigmaOpenAtInterior p C hC_G →
        ∃ (p_fixed : Walk G a' b'),
          (∀ k, p_fixed.vertices[k]? = some u → p_fixed.IsNonCollider k) ∧
          (∀ k, p_fixed.vertices[k]? = some u → p_fixed.vertices[k+1]? ≠ some u) ∧
          NoBifurcationSideTrip p_fixed u ∧
          IsSigmaOpenAtInterior p_fixed C hC_G ∧
          -- First-step preservation meta-invariant (internal):
          -- nil-preservation (iff) + same first WalkStep when non-nil.
          (p.length = 0 ↔ p_fixed.length = 0) ∧
          (∀ {mid : Node} (s : WalkStep G a' mid) (p_tail : Walk G mid b'),
              p = Walk.cons mid s p_tail →
              ∃ (p_tail_fixed : Walk G mid b'),
                  p_fixed = Walk.cons mid s p_tail_fixed) ∧
          ∃ (p'_fixed : Walk (G.marginalize {u} hu) a' b'),
              IsLift G u hu p'_fixed p_fixed ∧
              NoProblematicLift hu C p'_fixed p_fixed by
    intro a b p ha hb h_nc h_nocons h_nobif h_sigma_open
    obtain ⟨p_fixed, h1, h2, h3, h4, _h_nil, _h_fst, p'_fixed, h_lift, h_npl⟩ :=
      aux p.length p rfl ha hb h_nc h_nocons h_nobif h_sigma_open
    exact ⟨p_fixed, h1, h2, h3, h4, p'_fixed, h_lift, h_npl⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intros a b p h_len ha hb h_nc h_nocons h_nobif h_sigma_open
    cases p with
    | nil _ hv_G =>
        -- ## Cell: nil
        -- a = b (by Walk.nil's type), a ≠ u → a ∈ G \ {u} = marg-carrier.
        have hv_marg : a ∈ G.marginalize {u} hu := by
          change a ∈ G.J ∪ (G.V \ ({u} : Finset Node))
          rcases Finset.mem_union.mp hv_G with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · refine Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
            intro h_in
            exact ha (Finset.mem_singleton.mp h_in)
        refine ⟨Walk.nil a hv_G, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- u-non-collider on nil: nil has no positions with vertex u.
          intro k hk
          exfalso
          cases k with
          | zero =>
              have h_eq : (some a : Option Node) = some u := by
                rw [← hk]
                exact Walk.vertices_zero_eq_source' (Walk.nil a hv_G)
              exact ha (Option.some.inj h_eq)
          | succ k' =>
              have h_none : (Walk.nil a hv_G).vertices[k' + 1]? = none := by
                simp [Walk.vertices]
              rw [h_none] at hk
              contradiction
        · -- no-consecutive-u on nil: vacuous (no u positions).
          intro k hk
          exfalso
          cases k with
          | zero =>
              have h_eq : (some a : Option Node) = some u := by
                rw [← hk]
                exact Walk.vertices_zero_eq_source' (Walk.nil a hv_G)
              exact ha (Option.some.inj h_eq)
          | succ k' =>
              have h_none : (Walk.nil a hv_G).vertices[k' + 1]? = none := by
                simp [Walk.vertices]
              rw [h_none] at hk
              contradiction
        · -- NoBifurcationSideTrip on nil: vacuous via IsBifurcationFlankAt.nil
          intro i v hi hi1 hi2 h_bif
          exact h_bif.elim
        · -- IsSigmaOpenAtInterior on nil
          exact sigma_open_interior_lift_nil_case a hv_G C hC_G
        · -- Nil-length preservation: both p and p_fixed are nil here.
          exact Iff.rfl
        · -- First-step preservation meta-invariant.
          -- p = Walk.nil cannot equal Walk.cons; vacuous via length.
          intro mid s p_tail h_eq
          exfalso
          have h_len_eq :
              (Walk.nil a hv_G).length = (Walk.cons mid s p_tail).length := by
            rw [h_eq]
          simp [Walk.length] at h_len_eq
        · -- p'_fixed = nil; IsLift = .nil_lift; NPL = .nil_npl
          refine ⟨Walk.nil a hv_marg, ?_, ?_⟩
          · exact IsLift.nil_lift hv_marg hv_G
          · exact NoProblematicLift.nil_npl hv_marg hv_G
    | @cons _ _ mid s' p_tail =>
        by_cases h_mid : mid = u
        · -- Case mid = u: 2-edge dispatch.
          have h_u_eq_mid : u = mid := h_mid.symm
          subst h_u_eq_mid
          cases p_tail with
          | nil v hv =>
              -- p = cons u s' (nil u ...); but b = u contradicts hb.
              exact absurd rfl hb
          | @cons _ _ mid' s₂ p_tail_inner =>
              -- 2-edge dispatch.  Setup hypotheses (mirror 7c lines 3843–3909).
              have h_get1_u :
                  (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).vertices[1]?
                    = some u := rfl
              have h_get2_eq_mid' :
                  (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).vertices[2]?
                    = some mid' :=
                Walk.vertices_zero_eq_source' p_tail_inner
              have h_mid'_ne_u : mid' ≠ u := by
                intro h_eq
                apply h_nocons 1 h_get1_u
                rw [h_get2_eq_mid', h_eq]
              have h_p_nc_1 :
                  (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).IsNonCollider 1
                  := h_nc 1 h_get1_u
              have hNonColl :
                  ¬ (s'.HeadAtTarget ∧ s₂.HeadAtSource) := h_p_nc_1.2
              have h_inner_lt : p_tail_inner.length < n := by
                have h_len_eq :
                    (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).length
                      = p_tail_inner.length + 2 := rfl
                omega
              have h_nc_inner :
                  ∀ k, p_tail_inner.vertices[k]? = some u →
                    p_tail_inner.IsNonCollider k := by
                intro k hk_inner
                have hk_p :
                    (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).vertices[k+2]?
                      = some u := hk_inner
                have h_nc_kp2 := h_nc (k+2) hk_p
                refine ⟨?_, ?_⟩
                · have h1 := h_nc_kp2.1
                  have h_len_eq :
                      (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).length
                        = p_tail_inner.length + 2 := rfl
                  omega
                · intro h_coll_inner
                  apply h_nc_kp2.2
                  cases p_tail_inner with
                  | nil _ _ =>
                      exact absurd h_coll_inner (by cases k <;> exact id)
                  | cons mid_i s_i p_i =>
                      cases k with
                      | zero =>
                          rw [isCollider_cons_zero_eq_false s_i p_i] at h_coll_inner
                          exact h_coll_inner.elim
                      | succ k' =>
                          cases s' <;> cases s₂ <;> exact h_coll_inner
              have h_nocons_inner :
                  ∀ k, p_tail_inner.vertices[k]? = some u →
                    p_tail_inner.vertices[k+1]? ≠ some u := by
                intro k hk h_kp1
                exact h_nocons (k+2) hk h_kp1
              have h_nobif_inner : NoBifurcationSideTrip p_tail_inner u := by
                intro i v h_i h_ip1 h_ip2 h_bif
                apply h_nobif (i+2) v h_i h_ip1 h_ip2
                cases p_tail_inner with
                | nil _ _ => exact h_bif.elim
                | cons _ _ _ => cases s' <;> cases s₂ <;> exact h_bif
              have h_sigma_open_inner :
                  IsSigmaOpenAtInterior p_tail_inner C hC_G :=
                sigma_open_interior_cons_tail s₂ p_tail_inner C hC_G
                  (sigma_open_interior_cons_tail s' _ C hC_G h_sigma_open)
              obtain ⟨p_tail_inner_fixed, h_nc_pf_inner, h_nocons_pf_inner,
                      h_nobif_pf_inner, h_so_pf_inner, h_nil_pres_inner,
                      h_fst_pres_inner, p_tail_inner_lift, h_lift_inner,
                      h_npl_inner⟩ :=
                ih p_tail_inner.length h_inner_lt p_tail_inner rfl h_mid'_ne_u hb
                  h_nc_inner h_nocons_inner h_nobif_inner h_sigma_open_inner
              -- Side-trip vs non-side-trip dispatch.
              by_cases h_st : a = mid'
              · -- Side-trip case (a = mid').  After subst, the 2-edge
                -- cell becomes a self-loop a → u → a.  Only (fw, fw)
                -- and (bw, bw) survive (h_not_bif + hNonColl eliminate
                -- the rest).
                subst h_st
                -- Derive ¬IsBifurcationFlankAt 1 from h_nobif at i=0.
                have h_get0_a :
                    (Walk.cons u s' (Walk.cons a s₂ p_tail_inner)).vertices[0]?
                      = some a := rfl
                have h_get2_a :
                    (Walk.cons u s' (Walk.cons a s₂ p_tail_inner)).vertices[2]?
                      = some a :=
                  Walk.vertices_zero_eq_source' p_tail_inner
                have h_not_bif :
                    ¬ (Walk.cons u s' (Walk.cons a s₂ p_tail_inner)).IsBifurcationFlankAt 1 :=
                  h_nobif 0 a h_get0_a h_get1_u h_get2_a
                cases s' with
                | forwardE h₁ =>
                    cases s₂ with
                    | forwardE h₂ =>
                        -- (forwardE, forwardE) side-trip.  Build marg-E self-loop.
                        have h_a_GV : a ∈ G.V := (G.hE_subset h₂).2
                        have h_a_marg :
                            a ∈ G.V \ ({u} : Finset Node) := by
                          rw [Finset.mem_sdiff, Finset.mem_singleton]
                          exact ⟨h_a_GV, ha⟩
                        have h_a_carrier :
                            a ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                          Finset.mem_union_right _ h_a_marg
                        have h_a_G : a ∈ G :=
                          Finset.mem_union_right _ h_a_GV
                        have h_a_marg_mem : a ∈ G.marginalize {u} hu := by
                          change a ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                          exact h_a_carrier
                        have h_marg_E :
                            (a, a) ∈ (G.marginalize {u} hu).E := by
                          change (a, a) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                                  (G.V \ ({u} : Finset Node))).filter
                                (fun e => G.MarginalizationΦE {u} e.1 e.2)
                          refine Finset.mem_filter.mpr
                            ⟨Finset.mem_product.mpr
                              ⟨h_a_carrier, h_a_marg⟩, ?_⟩
                          refine ⟨Walk.cons u (.forwardE h₁)
                                    (Walk.cons a (.forwardE h₂)
                                      (.nil a h_a_G)),
                                  ?_, ?_, ?_⟩
                          · exact True.intro
                          · exact Nat.le_add_left 1 1
                          · intro x hx
                            have h_eq : x = u := by
                              simpa only [Walk.vertices, List.tail_cons,
                                List.dropLast_cons_of_ne_nil, List.dropLast,
                                List.mem_singleton] using hx
                            exact Finset.mem_singleton.mpr h_eq
                        -- Build p_fixed, refine 7-conjunct.
                        refine ⟨Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                  p_tail_inner_fixed), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        · -- u-non-collider.
                          intro k hk_vert
                          cases k with
                          | zero =>
                              exfalso
                              have h_v0 :
                                  (Walk.cons u (.forwardE h₁)
                                    (Walk.cons a (.forwardE h₂)
                                      p_tail_inner_fixed)).vertices[0]?
                                    = some a :=
                                Walk.vertices_zero_eq_source' _
                              rw [h_v0] at hk_vert
                              exact ha (Option.some.inj hk_vert)
                          | succ k1 =>
                              cases k1 with
                              | zero =>
                                  refine ⟨?_, ?_⟩
                                  · show 1 ≤ p_tail_inner_fixed.length + 2
                                    omega
                                  · intro h_coll1
                                    cases p_tail_inner_fixed with
                                    | nil _ _ =>
                                        -- IsCollider 1 = True ∧ False = False, so this is False.
                                        cases h_coll1.2
                                    | cons _ _ _ =>
                                        cases h_coll1.2
                              | succ k2 =>
                                  cases k2 with
                                  | zero =>
                                      exfalso
                                      have h_v2 :
                                          (Walk.cons u (.forwardE h₁)
                                            (Walk.cons a (.forwardE h₂)
                                              p_tail_inner_fixed)).vertices[2]?
                                            = some a := by
                                        show p_tail_inner_fixed.vertices[0]? = some a
                                        exact Walk.vertices_zero_eq_source' _
                                      rw [h_v2] at hk_vert
                                      exact ha (Option.some.inj hk_vert)
                                  | succ k3 =>
                                      have hk_inner :
                                          p_tail_inner_fixed.vertices[k3 + 1]? = some u := hk_vert
                                      have h_nc_inner_k := h_nc_pf_inner (k3 + 1) hk_inner
                                      refine ⟨?_, ?_⟩
                                      · have h1 := h_nc_inner_k.1
                                        show k3 + 3 ≤ p_tail_inner_fixed.length + 2
                                        omega
                                      · intro h_coll_outer
                                        apply h_nc_inner_k.2
                                        cases p_tail_inner_fixed with
                                        | nil _ _ =>
                                            exact absurd hk_inner
                                              (by simp [Walk.vertices])
                                        | cons _ _ _ => exact h_coll_outer
                        · -- no-cons-u.
                          intro k hk_vert h_kp1
                          cases k with
                          | zero =>
                              exfalso
                              have h_v0 :
                                  (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                      p_tail_inner_fixed)).vertices[0]?
                                    = some a :=
                                Walk.vertices_zero_eq_source' _
                              rw [h_v0] at hk_vert
                              exact ha (Option.some.inj hk_vert)
                          | succ k1 =>
                              cases k1 with
                              | zero =>
                                  exfalso
                                  have h_v2 :
                                      (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                          p_tail_inner_fixed)).vertices[2]?
                                        = some a := by
                                    show p_tail_inner_fixed.vertices[0]? = some a
                                    exact Walk.vertices_zero_eq_source' _
                                  rw [h_v2] at h_kp1
                                  exact ha (Option.some.inj h_kp1)
                              | succ k2 =>
                                  cases k2 with
                                  | zero =>
                                      exfalso
                                      have h_v2 :
                                          (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                              p_tail_inner_fixed)).vertices[2]?
                                            = some a := by
                                        show p_tail_inner_fixed.vertices[0]? = some a
                                        exact Walk.vertices_zero_eq_source' _
                                      rw [h_v2] at hk_vert
                                      exact ha (Option.some.inj hk_vert)
                                  | succ k3 =>
                                      have hk_inner :
                                          p_tail_inner_fixed.vertices[k3 + 1]? = some u := hk_vert
                                      have h_kp1_inner :
                                          p_tail_inner_fixed.vertices[k3 + 2]? = some u := h_kp1
                                      exact h_nocons_pf_inner (k3 + 1) hk_inner h_kp1_inner
                        · -- NBS.
                          intro i v h_i h_ip1 h_ip2 h_bif
                          cases i with
                          | zero =>
                              -- v = a, NBS would fire; need ¬IsBifurcationFlankAt 1.
                              -- For (fw, fw): IsBifurcationFlankAt 1 = False ∧ True;
                              -- h_bif.1 : False (forwardE.HeadAtSource).
                              cases p_tail_inner_fixed with
                              | nil _ _ =>
                                  exact h_bif.1.elim
                              | cons _ _ _ =>
                                  exact h_bif.1.elim
                          | succ i1 =>
                              cases i1 with
                              | zero =>
                                  exfalso
                                  have h_v2 :
                                      (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                          p_tail_inner_fixed)).vertices[2]?
                                        = some a := by
                                    show p_tail_inner_fixed.vertices[0]? = some a
                                    exact Walk.vertices_zero_eq_source' _
                                  rw [h_v2] at h_ip1
                                  exact ha (Option.some.inj h_ip1)
                              | succ i2 =>
                                  apply h_nobif_pf_inner i2 v h_i h_ip1 h_ip2
                                  cases p_tail_inner_fixed with
                                  | nil _ _ => exact h_bif.elim
                                  | cons _ _ _ => exact h_bif
                        · -- σ-open.
                          refine ⟨?_, ?_⟩
                          · intro k vk hk_vert h_coll
                            cases k with
                            | zero =>
                                cases p_tail_inner_fixed with
                                | nil _ _ => exact h_coll.elim
                                | cons _ _ _ =>
                                    rw [isCollider_cons_zero_eq_false _ _] at h_coll
                                    exact h_coll.elim
                            | succ k1 =>
                                cases k1 with
                                | zero =>
                                    -- pos 1 for (fw, fw): IsCollider 1 = True ∧ False;
                                    -- h_coll.2 : False (forwardE.HeadAtSource).
                                    exfalso
                                    cases p_tail_inner_fixed with
                                    | nil _ _ => exact h_coll.2.elim
                                    | cons _ _ _ => exact h_coll.2.elim
                                | succ k2 =>
                                    cases k2 with
                                    | zero =>
                                        -- pos 2: vertex a.
                                        have hvk_a : vk = a := by
                                          have h_v2 :
                                              (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                  p_tail_inner_fixed)).vertices[2]?
                                                = some a := by
                                            show p_tail_inner_fixed.vertices[0]? = some a
                                            exact Walk.vertices_zero_eq_source' _
                                          rw [h_v2] at hk_vert
                                          exact (Option.some.inj hk_vert).symm
                                        rw [hvk_a]
                                        -- Transport via meta-invariants on p_tail_inner.
                                        cases h_pti : p_tail_inner with
                                        | nil v_pti hv_pti =>
                                            have h_pti_lz : p_tail_inner.length = 0 := by
                                              rw [h_pti]; rfl
                                            have h_pf_lz :
                                                p_tail_inner_fixed.length = 0 :=
                                              h_nil_pres_inner.mp h_pti_lz
                                            cases p_tail_inner_fixed with
                                            | nil _ _ => exact h_coll.elim
                                            | cons _ _ _ =>
                                                simp [Walk.length] at h_pf_lz
                                        | cons mid_x s_first p_inner_inner =>
                                            obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                              h_fst_pres_inner s_first p_inner_inner h_pti
                                            rw [h_pf_eq] at h_coll
                                            have h_input_coll :
                                                (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                    p_tail_inner)).IsCollider 2 := by
                                              rw [h_pti]
                                              cases s_first <;>
                                                first
                                                | exact h_coll
                                                | exact h_coll.elim
                                                | exact ⟨h_coll.1, h_coll.2⟩
                                            have h_vert_a :
                                                (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                    p_tail_inner)).vertices[2]?
                                                  = some a := by
                                              show p_tail_inner.vertices[0]? = some a
                                              exact Walk.vertices_zero_eq_source' p_tail_inner
                                            exact h_sigma_open.1 2 a h_vert_a h_input_coll
                                    | succ k3 =>
                                        have hvk_tail :
                                            p_tail_inner_fixed.vertices[k3 + 1]? = some vk := hk_vert
                                        have h_tail_coll :
                                            p_tail_inner_fixed.IsCollider (k3 + 1) := by
                                          cases p_tail_inner_fixed with
                                          | nil _ _ => exact h_coll.elim
                                          | cons _ _ _ => exact h_coll
                                        exact h_so_pf_inner.1 (k3 + 1) vk hvk_tail h_tail_coll
                          · intro k vk hk_vert h_blk h_pos
                            cases k with
                            | zero => omega
                            | succ k1 =>
                                cases k1 with
                                | zero =>
                                    -- pos 1: vertex u. u ∉ C.
                                    have hvk_u : vk = u := by
                                      have h_v1 :
                                          (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                              p_tail_inner_fixed)).vertices[1]?
                                            = some u := rfl
                                      rw [h_v1] at hk_vert
                                      exact (Option.some.inj hk_vert).symm
                                    rw [hvk_u]
                                    exact hu_notC
                                | succ k2 =>
                                    cases k2 with
                                    | zero =>
                                        -- pos 2: vertex a.
                                        cases h_pti : p_tail_inner with
                                        | nil v_pti hv_pti =>
                                            have h_pti_lz : p_tail_inner.length = 0 := by
                                              rw [h_pti]; rfl
                                            have h_pf_lz :
                                                p_tail_inner_fixed.length = 0 :=
                                              h_nil_pres_inner.mp h_pti_lz
                                            cases p_tail_inner_fixed with
                                            | nil _ _ =>
                                                refine h_sigma_open.2 2 vk ?_ ?_ h_pos
                                                · rw [h_pti]; exact hk_vert
                                                · rw [h_pti]; exact h_blk
                                            | cons _ _ _ =>
                                                simp [Walk.length] at h_pf_lz
                                        | cons mid_x s_first p_inner_inner =>
                                            have hvk_a : vk = a := by
                                              have h_v2 :
                                                  (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                      p_tail_inner_fixed)).vertices[2]?
                                                    = some a := by
                                                show p_tail_inner_fixed.vertices[0]? = some a
                                                exact Walk.vertices_zero_eq_source' _
                                              rw [h_v2] at hk_vert
                                              exact (Option.some.inj hk_vert).symm
                                            rw [hvk_a]
                                            obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                              h_fst_pres_inner s_first p_inner_inner h_pti
                                            rw [h_pf_eq] at h_blk
                                            have h_vert_a :
                                                (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                    p_tail_inner)).vertices[2]?
                                                  = some a := by
                                              show p_tail_inner.vertices[0]? = some a
                                              exact Walk.vertices_zero_eq_source' p_tail_inner
                                            have h_input_blk :
                                                (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                    p_tail_inner)).IsBlockableNonCollider 2 := by
                                              rw [h_pti]
                                              obtain ⟨h_nc_outer, h_disj_outer⟩ := h_blk
                                              refine ⟨?_, ?_⟩
                                              · refine ⟨?_, ?_⟩
                                                · show 2 ≤
                                                      (Walk.cons mid_x s_first p_inner_inner).length + 2
                                                  simp [Walk.length]
                                                · intro h_coll_input
                                                  apply h_nc_outer.2
                                                  cases s_first <;>
                                                    first
                                                    | exact h_coll_input
                                                    | exact h_coll_input.elim
                                                    | exact ⟨h_coll_input.1, h_coll_input.2⟩
                                              · rcases h_disj_outer with h_eq0 | h_eq_len | hHBLS | hHBRS
                                                · exact absurd h_eq0 (by omega)
                                                · exfalso
                                                  have h_len_eq :
                                                      (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                          (Walk.cons mid_x s_first p_inner_inner_fixed))).length
                                                        = p_inner_inner_fixed.length + 3 := rfl
                                                  rw [h_len_eq] at h_eq_len
                                                  omega
                                                · right; right; left
                                                  -- (fw,fw) side-trip's HBLS 2 reduces to
                                                  -- inner cons's HBLS 1 (.forwardE)? = False;
                                                  -- the simp at hHBLS closes via contradiction.
                                                  simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                                · right; right; right
                                                  simp only [Walk.HasBlockingRightSlot] at hHBRS ⊢
                                                  cases s_first <;>
                                                    first
                                                    | exact hHBRS
                                                    | exact hHBRS.elim
                                            exact h_sigma_open.2 2 a h_vert_a h_input_blk h_pos
                                    | succ k3 =>
                                        have hvk_tail :
                                            p_tail_inner_fixed.vertices[k3 + 1]? = some vk := hk_vert
                                        have h_tail_blk :
                                            p_tail_inner_fixed.IsBlockableNonCollider (k3 + 1) := by
                                          obtain ⟨h_nc, h_disj⟩ := h_blk
                                          refine ⟨?_, ?_⟩
                                          · refine ⟨?_, ?_⟩
                                            · have h1 := h_nc.1
                                              have h_len_eq :
                                                  (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                      p_tail_inner_fixed)).length
                                                    = p_tail_inner_fixed.length + 2 := rfl
                                              omega
                                            · intro h_coll_tail
                                              apply h_nc.2
                                              cases p_tail_inner_fixed with
                                              | nil _ _ =>
                                                  exact absurd h_coll_tail
                                                    (by cases k3 <;> exact id)
                                              | cons _ _ _ => exact h_coll_tail
                                          · rcases h_disj with h_eq0 | h_eq_len | hHBLS | hHBRS
                                            · omega
                                            · right; left
                                              have h_len_eq :
                                                  (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                                      p_tail_inner_fixed)).length
                                                    = p_tail_inner_fixed.length + 2 := rfl
                                              omega
                                            · right; right; left
                                              cases p_tail_inner_fixed with
                                              | nil _ _ =>
                                                  simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                              | cons _ _ _ => exact hHBLS
                                            · right; right; right
                                              cases p_tail_inner_fixed with
                                              | nil _ _ =>
                                                  simp only [Walk.HasBlockingRightSlot] at hHBRS
                                              | cons _ _ _ => exact hHBRS
                                        exact h_so_pf_inner.2 (k3 + 1) vk hvk_tail h_tail_blk
                                          (by omega)
                        · -- Nil-pres iff.
                          constructor
                          · intro h
                            exfalso
                            have h_len_eq :
                                (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                    p_tail_inner)).length
                                  = p_tail_inner.length + 2 := rfl
                            omega
                          · intro h
                            exfalso
                            have h_len_eq :
                                (Walk.cons u (.forwardE h₁) (Walk.cons a (.forwardE h₂)
                                    p_tail_inner_fixed)).length
                                  = p_tail_inner_fixed.length + 2 := rfl
                            omega
                        · -- First-step pres.
                          intro mid'' s'' p_tail'' h_eq
                          cases h_eq
                          exact ⟨Walk.cons a (.forwardE h₂) p_tail_inner_fixed, rfl⟩
                        · -- p'_fixed: marg self-loop + IsLift.cons_two_edge + NPL.two_edge_npl.
                          refine ⟨Walk.cons a (.forwardE h_marg_E) p_tail_inner_lift, ?_, ?_⟩
                          · exact IsLift.cons_two_edge (.forwardE h_marg_E) p_tail_inner_lift
                              (.forwardE h₁) (.forwardE h₂) p_tail_inner_fixed Iff.rfl Iff.rfl
                              hNonColl h_lift_inner
                          · refine NoProblematicLift.two_edge_npl (.forwardE h_marg_E)
                              p_tail_inner_lift (.forwardE h₁) (.forwardE h₂) p_tail_inner_fixed
                              ?_ ?_ h_npl_inner
                            · -- h_fwd: need a ∈ marg.Sc a (trivially).
                              intro _ _ _
                              refine ⟨⟨h_a_marg_mem, ?_⟩, ⟨h_a_marg_mem, ?_⟩⟩
                              · exact ⟨Walk.nil a h_a_marg_mem, True.intro⟩
                              · exact ⟨Walk.nil a h_a_marg_mem, True.intro⟩
                            · -- h_bwd: vacuous (s_marg = .forwardE has HeadAtSource = False).
                              intro h_ant
                              exact h_ant.1.elim
                    | backwardE _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                    | bidir _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                | backwardE h₁ =>
                    cases s₂ with
                    | forwardE _ => exact (h_not_bif ⟨trivial, trivial⟩).elim
                    | backwardE h₂ =>
                        -- (backwardE, backwardE) side-trip.  Symmetric to (fw, fw).
                        have h_a_GV : a ∈ G.V := (G.hE_subset h₁).2
                        have h_a_marg :
                            a ∈ G.V \ ({u} : Finset Node) := by
                          rw [Finset.mem_sdiff, Finset.mem_singleton]
                          exact ⟨h_a_GV, ha⟩
                        have h_a_carrier :
                            a ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                          Finset.mem_union_right _ h_a_marg
                        have h_a_G : a ∈ G :=
                          Finset.mem_union_right _ h_a_GV
                        have h_a_marg_mem : a ∈ G.marginalize {u} hu := by
                          change a ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                          exact h_a_carrier
                        have h_marg_E :
                            (a, a) ∈ (G.marginalize {u} hu).E := by
                          change (a, a) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                                  (G.V \ ({u} : Finset Node))).filter
                                (fun e => G.MarginalizationΦE {u} e.1 e.2)
                          refine Finset.mem_filter.mpr
                            ⟨Finset.mem_product.mpr
                              ⟨h_a_carrier, h_a_marg⟩, ?_⟩
                          refine ⟨Walk.cons u (.forwardE h₂)
                                    (Walk.cons a (.forwardE h₁)
                                      (.nil a h_a_G)),
                                  ?_, ?_, ?_⟩
                          · exact True.intro
                          · exact Nat.le_add_left 1 1
                          · intro x hx
                            have h_eq : x = u := by
                              simpa only [Walk.vertices, List.tail_cons,
                                List.dropLast_cons_of_ne_nil, List.dropLast,
                                List.mem_singleton] using hx
                            exact Finset.mem_singleton.mpr h_eq
                        refine ⟨Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                  p_tail_inner_fixed), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        · -- u-non-collider (symmetric to fw-fw).
                          intro k hk_vert
                          cases k with
                          | zero =>
                              exfalso
                              have h_v0 :
                                  (Walk.cons u (.backwardE h₁)
                                    (Walk.cons a (.backwardE h₂)
                                      p_tail_inner_fixed)).vertices[0]?
                                    = some a :=
                                Walk.vertices_zero_eq_source' _
                              rw [h_v0] at hk_vert
                              exact ha (Option.some.inj hk_vert)
                          | succ k1 =>
                              cases k1 with
                              | zero =>
                                  refine ⟨?_, ?_⟩
                                  · show 1 ≤ p_tail_inner_fixed.length + 2
                                    omega
                                  · intro h_coll1
                                    cases p_tail_inner_fixed with
                                    | nil _ _ =>
                                        cases h_coll1.1
                                    | cons _ _ _ =>
                                        cases h_coll1.1
                              | succ k2 =>
                                  cases k2 with
                                  | zero =>
                                      exfalso
                                      have h_v2 :
                                          (Walk.cons u (.backwardE h₁)
                                            (Walk.cons a (.backwardE h₂)
                                              p_tail_inner_fixed)).vertices[2]?
                                            = some a := by
                                        show p_tail_inner_fixed.vertices[0]? = some a
                                        exact Walk.vertices_zero_eq_source' _
                                      rw [h_v2] at hk_vert
                                      exact ha (Option.some.inj hk_vert)
                                  | succ k3 =>
                                      have hk_inner :
                                          p_tail_inner_fixed.vertices[k3 + 1]? = some u := hk_vert
                                      have h_nc_inner_k := h_nc_pf_inner (k3 + 1) hk_inner
                                      refine ⟨?_, ?_⟩
                                      · have h1 := h_nc_inner_k.1
                                        show k3 + 3 ≤ p_tail_inner_fixed.length + 2
                                        omega
                                      · intro h_coll_outer
                                        apply h_nc_inner_k.2
                                        cases p_tail_inner_fixed with
                                        | nil _ _ =>
                                            exact absurd hk_inner
                                              (by simp [Walk.vertices])
                                        | cons _ _ _ => exact h_coll_outer
                        · -- no-cons-u.
                          intro k hk_vert h_kp1
                          cases k with
                          | zero =>
                              exfalso
                              have h_v0 :
                                  (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                      p_tail_inner_fixed)).vertices[0]?
                                    = some a :=
                                Walk.vertices_zero_eq_source' _
                              rw [h_v0] at hk_vert
                              exact ha (Option.some.inj hk_vert)
                          | succ k1 =>
                              cases k1 with
                              | zero =>
                                  exfalso
                                  have h_v2 :
                                      (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                          p_tail_inner_fixed)).vertices[2]?
                                        = some a := by
                                    show p_tail_inner_fixed.vertices[0]? = some a
                                    exact Walk.vertices_zero_eq_source' _
                                  rw [h_v2] at h_kp1
                                  exact ha (Option.some.inj h_kp1)
                              | succ k2 =>
                                  cases k2 with
                                  | zero =>
                                      exfalso
                                      have h_v2 :
                                          (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                              p_tail_inner_fixed)).vertices[2]?
                                            = some a := by
                                        show p_tail_inner_fixed.vertices[0]? = some a
                                        exact Walk.vertices_zero_eq_source' _
                                      rw [h_v2] at hk_vert
                                      exact ha (Option.some.inj hk_vert)
                                  | succ k3 =>
                                      have hk_inner :
                                          p_tail_inner_fixed.vertices[k3 + 1]? = some u := hk_vert
                                      have h_kp1_inner :
                                          p_tail_inner_fixed.vertices[k3 + 2]? = some u := h_kp1
                                      exact h_nocons_pf_inner (k3 + 1) hk_inner h_kp1_inner
                        · -- NBS.
                          intro i v h_i h_ip1 h_ip2 h_bif
                          cases i with
                          | zero =>
                              -- IsBifurcationFlankAt 1 = True ∧ False (backwardE);
                              -- h_bif.2 : False.
                              cases p_tail_inner_fixed with
                              | nil _ _ => exact h_bif.2.elim
                              | cons _ _ _ => exact h_bif.2.elim
                          | succ i1 =>
                              cases i1 with
                              | zero =>
                                  exfalso
                                  have h_v2 :
                                      (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                          p_tail_inner_fixed)).vertices[2]?
                                        = some a := by
                                    show p_tail_inner_fixed.vertices[0]? = some a
                                    exact Walk.vertices_zero_eq_source' _
                                  rw [h_v2] at h_ip1
                                  exact ha (Option.some.inj h_ip1)
                              | succ i2 =>
                                  apply h_nobif_pf_inner i2 v h_i h_ip1 h_ip2
                                  cases p_tail_inner_fixed with
                                  | nil _ _ => exact h_bif.elim
                                  | cons _ _ _ => exact h_bif
                        · -- σ-open.
                          refine ⟨?_, ?_⟩
                          · intro k vk hk_vert h_coll
                            cases k with
                            | zero =>
                                cases p_tail_inner_fixed with
                                | nil _ _ => exact h_coll.elim
                                | cons _ _ _ =>
                                    rw [isCollider_cons_zero_eq_false _ _] at h_coll
                                    exact h_coll.elim
                            | succ k1 =>
                                cases k1 with
                                | zero =>
                                    -- IsCollider 1 = backwardE.HeadAtTarget ∧ backwardE.HeadAtSource = False ∧ True = False.
                                    exfalso
                                    cases p_tail_inner_fixed with
                                    | nil _ _ => exact h_coll.1.elim
                                    | cons _ _ _ => exact h_coll.1.elim
                                | succ k2 =>
                                    cases k2 with
                                    | zero =>
                                        have hvk_a : vk = a := by
                                          have h_v2 :
                                              (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                  p_tail_inner_fixed)).vertices[2]?
                                                = some a := by
                                            show p_tail_inner_fixed.vertices[0]? = some a
                                            exact Walk.vertices_zero_eq_source' _
                                          rw [h_v2] at hk_vert
                                          exact (Option.some.inj hk_vert).symm
                                        rw [hvk_a]
                                        cases h_pti : p_tail_inner with
                                        | nil v_pti hv_pti =>
                                            have h_pti_lz : p_tail_inner.length = 0 := by
                                              rw [h_pti]; rfl
                                            have h_pf_lz :
                                                p_tail_inner_fixed.length = 0 :=
                                              h_nil_pres_inner.mp h_pti_lz
                                            cases p_tail_inner_fixed with
                                            | nil _ _ => exact h_coll.elim
                                            | cons _ _ _ =>
                                                simp [Walk.length] at h_pf_lz
                                        | cons mid_x s_first p_inner_inner =>
                                            obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                              h_fst_pres_inner s_first p_inner_inner h_pti
                                            rw [h_pf_eq] at h_coll
                                            have h_input_coll :
                                                (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                    p_tail_inner)).IsCollider 2 := by
                                              rw [h_pti]
                                              cases s_first <;>
                                                first
                                                | exact h_coll
                                                | exact h_coll.elim
                                                | exact ⟨h_coll.1, h_coll.2⟩
                                            have h_vert_a :
                                                (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                    p_tail_inner)).vertices[2]?
                                                  = some a := by
                                              show p_tail_inner.vertices[0]? = some a
                                              exact Walk.vertices_zero_eq_source' p_tail_inner
                                            exact h_sigma_open.1 2 a h_vert_a h_input_coll
                                    | succ k3 =>
                                        have hvk_tail :
                                            p_tail_inner_fixed.vertices[k3 + 1]? = some vk := hk_vert
                                        have h_tail_coll :
                                            p_tail_inner_fixed.IsCollider (k3 + 1) := by
                                          cases p_tail_inner_fixed with
                                          | nil _ _ => exact h_coll.elim
                                          | cons _ _ _ => exact h_coll
                                        exact h_so_pf_inner.1 (k3 + 1) vk hvk_tail h_tail_coll
                          · intro k vk hk_vert h_blk h_pos
                            cases k with
                            | zero => omega
                            | succ k1 =>
                                cases k1 with
                                | zero =>
                                    have hvk_u : vk = u := by
                                      have h_v1 :
                                          (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                              p_tail_inner_fixed)).vertices[1]?
                                            = some u := rfl
                                      rw [h_v1] at hk_vert
                                      exact (Option.some.inj hk_vert).symm
                                    rw [hvk_u]
                                    exact hu_notC
                                | succ k2 =>
                                    cases k2 with
                                    | zero =>
                                        cases h_pti : p_tail_inner with
                                        | nil v_pti hv_pti =>
                                            have h_pti_lz : p_tail_inner.length = 0 := by
                                              rw [h_pti]; rfl
                                            have h_pf_lz :
                                                p_tail_inner_fixed.length = 0 :=
                                              h_nil_pres_inner.mp h_pti_lz
                                            cases p_tail_inner_fixed with
                                            | nil _ _ =>
                                                refine h_sigma_open.2 2 vk ?_ ?_ h_pos
                                                · rw [h_pti]; exact hk_vert
                                                · rw [h_pti]; exact h_blk
                                            | cons _ _ _ =>
                                                simp [Walk.length] at h_pf_lz
                                        | cons mid_x s_first p_inner_inner =>
                                            have hvk_a : vk = a := by
                                              have h_v2 :
                                                  (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                      p_tail_inner_fixed)).vertices[2]?
                                                    = some a := by
                                                show p_tail_inner_fixed.vertices[0]? = some a
                                                exact Walk.vertices_zero_eq_source' _
                                              rw [h_v2] at hk_vert
                                              exact (Option.some.inj hk_vert).symm
                                            rw [hvk_a]
                                            obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                              h_fst_pres_inner s_first p_inner_inner h_pti
                                            rw [h_pf_eq] at h_blk
                                            have h_vert_a :
                                                (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                    p_tail_inner)).vertices[2]?
                                                  = some a := by
                                              show p_tail_inner.vertices[0]? = some a
                                              exact Walk.vertices_zero_eq_source' p_tail_inner
                                            have h_input_blk :
                                                (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                    p_tail_inner)).IsBlockableNonCollider 2 := by
                                              rw [h_pti]
                                              obtain ⟨h_nc_outer, h_disj_outer⟩ := h_blk
                                              refine ⟨?_, ?_⟩
                                              · refine ⟨?_, ?_⟩
                                                · show 2 ≤
                                                      (Walk.cons mid_x s_first p_inner_inner).length + 2
                                                  simp [Walk.length]
                                                · intro h_coll_input
                                                  apply h_nc_outer.2
                                                  cases s_first <;>
                                                    first
                                                    | exact h_coll_input
                                                    | exact h_coll_input.elim
                                                    | exact ⟨h_coll_input.1, h_coll_input.2⟩
                                              · rcases h_disj_outer with h_eq0 | h_eq_len | hHBLS | hHBRS
                                                · exact absurd h_eq0 (by omega)
                                                · exfalso
                                                  have h_len_eq :
                                                      (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                          (Walk.cons mid_x s_first p_inner_inner_fixed))).length
                                                        = p_inner_inner_fixed.length + 3 := rfl
                                                  rw [h_len_eq] at h_eq_len
                                                  omega
                                                · right; right; left
                                                  simp only [Walk.HasBlockingLeftSlot] at hHBLS ⊢
                                                  exact hHBLS
                                                · right; right; right
                                                  simp only [Walk.HasBlockingRightSlot] at hHBRS ⊢
                                                  cases s_first <;>
                                                    first
                                                    | exact hHBRS
                                                    | exact hHBRS.elim
                                            exact h_sigma_open.2 2 a h_vert_a h_input_blk h_pos
                                    | succ k3 =>
                                        have hvk_tail :
                                            p_tail_inner_fixed.vertices[k3 + 1]? = some vk := hk_vert
                                        have h_tail_blk :
                                            p_tail_inner_fixed.IsBlockableNonCollider (k3 + 1) := by
                                          obtain ⟨h_nc, h_disj⟩ := h_blk
                                          refine ⟨?_, ?_⟩
                                          · refine ⟨?_, ?_⟩
                                            · have h1 := h_nc.1
                                              have h_len_eq :
                                                  (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                      p_tail_inner_fixed)).length
                                                    = p_tail_inner_fixed.length + 2 := rfl
                                              omega
                                            · intro h_coll_tail
                                              apply h_nc.2
                                              cases p_tail_inner_fixed with
                                              | nil _ _ =>
                                                  exact absurd h_coll_tail
                                                    (by cases k3 <;> exact id)
                                              | cons _ _ _ => exact h_coll_tail
                                          · rcases h_disj with h_eq0 | h_eq_len | hHBLS | hHBRS
                                            · omega
                                            · right; left
                                              have h_len_eq :
                                                  (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                                      p_tail_inner_fixed)).length
                                                    = p_tail_inner_fixed.length + 2 := rfl
                                              omega
                                            · right; right; left
                                              cases p_tail_inner_fixed with
                                              | nil _ _ =>
                                                  simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                              | cons _ _ _ => exact hHBLS
                                            · right; right; right
                                              cases p_tail_inner_fixed with
                                              | nil _ _ =>
                                                  simp only [Walk.HasBlockingRightSlot] at hHBRS
                                              | cons _ _ _ => exact hHBRS
                                        exact h_so_pf_inner.2 (k3 + 1) vk hvk_tail h_tail_blk
                                          (by omega)
                        · -- Nil-pres iff.
                          constructor
                          · intro h
                            exfalso
                            have h_len_eq :
                                (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                    p_tail_inner)).length
                                  = p_tail_inner.length + 2 := rfl
                            omega
                          · intro h
                            exfalso
                            have h_len_eq :
                                (Walk.cons u (.backwardE h₁) (Walk.cons a (.backwardE h₂)
                                    p_tail_inner_fixed)).length
                                  = p_tail_inner_fixed.length + 2 := rfl
                            omega
                        · -- First-step pres.
                          intro mid'' s'' p_tail'' h_eq
                          cases h_eq
                          exact ⟨Walk.cons a (.backwardE h₂) p_tail_inner_fixed, rfl⟩
                        · -- p'_fixed: marg self-loop + IsLift.cons_two_edge + NPL.two_edge_npl.
                          refine ⟨Walk.cons a (.backwardE h_marg_E) p_tail_inner_lift, ?_, ?_⟩
                          · exact IsLift.cons_two_edge (.backwardE h_marg_E) p_tail_inner_lift
                              (.backwardE h₁) (.backwardE h₂) p_tail_inner_fixed Iff.rfl Iff.rfl
                              hNonColl h_lift_inner
                          · refine NoProblematicLift.two_edge_npl (.backwardE h_marg_E)
                              p_tail_inner_lift (.backwardE h₁) (.backwardE h₂) p_tail_inner_fixed
                              ?_ ?_ h_npl_inner
                            · -- h_fwd: vacuous (s_marg = .backwardE has HeadAtSource = True).
                              intro h_ant
                              exact h_ant.1 trivial |>.elim
                            · -- h_bwd: need a ∈ marg.Sc a (trivially).
                              intro _ _ _
                              refine ⟨⟨h_a_marg_mem, ?_⟩, ⟨h_a_marg_mem, ?_⟩⟩
                              · exact ⟨Walk.nil a h_a_marg_mem, True.intro⟩
                              · exact ⟨Walk.nil a h_a_marg_mem, True.intro⟩
                    | bidir _ => exact (h_not_bif ⟨trivial, trivial⟩).elim
                | bidir _ =>
                    cases s₂ with
                    | forwardE _ => exact (h_not_bif ⟨trivial, trivial⟩).elim
                    | backwardE _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                    | bidir _ => exact (hNonColl ⟨trivial, trivial⟩).elim
              · -- Non-side-trip case (a ≠ mid').
                -- TOP-LEVEL DISPATCH: surgical (fw,fw), surgical (bw,bw), or non-surgical.
                -- The two surgical cases need different p_fixed structures (4-edge
                -- insertion); they are handled in separate branches before the
                -- standard non-surgical body.
                by_cases h_use_surgery_fwfw :
                    (∃ (h_au_x : (a, u) ∈ G.E) (h_um_x : (u, mid') ∈ G.E),
                      s' = WalkStep.forwardE h_au_x ∧
                      s₂ = WalkStep.forwardE h_um_x) ∧
                    a ∈ C ∧ u ∈ G.Sc a ∧ mid' ∉ (G.marginalize {u} hu).Sc a
                · -- SURGICAL (fw, fw).  Per tex lines 273-285.
                  --   Surgical 4-edge G-walk: `a → u → w ← u → mid'`.
                  --   Marg-walk: `cons w (.forwardE _) (cons mid' (.bidir _) ...)`
                  --   (or with w = a self-loop in marg.E for the degenerate case).
                  obtain ⟨⟨h_au, h_um, h_s'_eq, h_s₂_eq⟩, ha_C, h_uSc, h_mid_notSc⟩ :=
                    h_use_surgery_fwfw
                  subst h_s'_eq
                  subst h_s₂_eq
                  -- Extract w via sc_clean_successor.
                  obtain ⟨w, h_uw, h_w_ne_u, h_w_in_Sc_a⟩ :=
                    sc_clean_successor ha h_uSc
                  -- Membership facts.
                  have h_w_GV : w ∈ G.V := (G.hE_subset h_uw).2
                  have h_w_G : w ∈ G := Finset.mem_union_right _ h_w_GV
                  have h_w_marg_mem : w ∈ G.marginalize {u} hu := by
                    change w ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                    refine Finset.mem_union_right _
                      (Finset.mem_sdiff.mpr ⟨h_w_GV, ?_⟩)
                    intro h_in
                    exact h_w_ne_u (Finset.mem_singleton.mp h_in)
                  have h_a_G : a ∈ G := (G.hE_subset h_au).1
                  have h_a_marg_mem : a ∈ G.marginalize {u} hu := by
                    change a ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                    rcases Finset.mem_union.mp h_a_G with hJ | hV
                    · exact Finset.mem_union_left _ hJ
                    · refine Finset.mem_union_right _
                        (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
                      intro h_in
                      exact ha (Finset.mem_singleton.mp h_in)
                  have h_mid'_G : mid' ∈ G :=
                    Finset.mem_union_right _ (G.hE_subset h_um).2
                  have h_mid'_marg_mem : mid' ∈ G.marginalize {u} hu := by
                    change mid' ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                    refine Finset.mem_union_right _
                      (Finset.mem_sdiff.mpr ⟨(G.hE_subset h_um).2, ?_⟩)
                    intro h_in
                    exact h_mid'_ne_u (Finset.mem_singleton.mp h_in)
                  have h_a_GJV : a ∈ G.J ∪ G.V := h_a_G
                  have h_a_carrier :
                      a ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := h_a_marg_mem
                  have h_mid'_marg :
                      mid' ∈ G.V \ ({u} : Finset Node) := by
                    rw [Finset.mem_sdiff, Finset.mem_singleton]
                    exact ⟨(G.hE_subset h_um).2, h_mid'_ne_u⟩
                  have h_w_marg :
                      w ∈ G.V \ ({u} : Finset Node) := by
                    rw [Finset.mem_sdiff, Finset.mem_singleton]
                    exact ⟨h_w_GV, h_w_ne_u⟩
                  have h_w_carrier :
                      w ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                    Finset.mem_union_right _ h_w_marg
                  -- w ∈ marg.Sc a (key for NPL.h_fwd).
                  have h_w_in_marg_Sc_a :
                      w ∈ (G.marginalize {u} hu).Sc a :=
                    (marg_sc_iff_G_sc u hu h_a_marg_mem h_w_G h_w_ne_u).mpr
                      h_w_in_Sc_a
                  -- w ≠ mid' (from problematic).
                  have h_w_ne_mid' : w ≠ mid' := by
                    intro h_w_eq
                    rw [h_w_eq] at h_w_in_marg_Sc_a
                    exact h_mid_notSc h_w_in_marg_Sc_a
                  -- w ∈ G.AncSet C (for σ-open at the surgical w-collider).
                  have h_w_in_AncSet_C : w ∈ G.AncSet C := by
                    unfold CDMG.AncSet
                    simp only [Set.mem_iUnion]
                    exact ⟨a, ha_C, h_w_in_Sc_a.1⟩
                  -- Build marg-cell 1: (a, w) ∈ marg.E (via 2-edge a → u → w).
                  -- Direct construction handles both w = a (self-loop) and w ≠ a uniformly.
                  have h_marg_E_aw :
                      (a, w) ∈ (G.marginalize {u} hu).E := by
                    change (a, w) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                            (G.V \ ({u} : Finset Node))).filter
                          (fun e => G.MarginalizationΦE {u} e.1 e.2)
                    refine Finset.mem_filter.mpr
                      ⟨Finset.mem_product.mpr
                        ⟨h_a_carrier, h_w_marg⟩, ?_⟩
                    refine ⟨Walk.cons u (.forwardE h_au)
                              (Walk.cons w (.forwardE h_uw) (.nil w h_w_G)),
                            ?_, ?_, ?_⟩
                    · exact True.intro
                    · exact Nat.le_add_left 1 1
                    · intro x hx
                      have h_eq : x = u := by
                        simpa only [Walk.vertices, List.tail_cons,
                          List.dropLast_cons_of_ne_nil, List.dropLast,
                          List.mem_singleton] using hx
                      exact Finset.mem_singleton.mpr h_eq
                  -- Build marg-cell 2: s(w, mid') ∈ marg.L (fork w ← u → mid').
                  have h_marg_L_wmid :
                      s(w, mid') ∈ (G.marginalize {u} hu).L := by
                    rw [marginalize_L_iff]
                    refine ⟨(w, mid'), h_w_marg, h_mid'_marg, h_w_ne_mid', ?_, rfl⟩
                    left
                    refine ⟨Walk.cons u (.backwardE h_uw)
                              (Walk.cons mid' (.forwardE h_um)
                                (.nil mid' h_mid'_G)),
                            ?_, ?_⟩
                    · refine ⟨h_w_ne_mid', ?_, ?_, 0, ?_⟩
                      · intro hmem
                        have h_in : w ∈ (u :: ([mid'] : List Node)) := hmem
                        rcases List.mem_cons.mp h_in with hwu | hwmid_in
                        · exact h_w_ne_u hwu
                        · exact h_w_ne_mid' (List.mem_singleton.mp hwmid_in)
                      · intro hmem
                        have h_in : mid' ∈ (w :: ([u] : List Node)) := hmem
                        rcases List.mem_cons.mp h_in with hmw | hmu_in
                        · exact h_w_ne_mid'.symm hmw
                        · exact h_mid'_ne_u (List.mem_singleton.mp hmu_in)
                      · exact True.intro
                    · intro x hx
                      have h_eq : x = u := by
                        simpa only [Walk.vertices, List.tail_cons,
                          List.dropLast_cons_of_ne_nil, List.dropLast,
                          List.mem_singleton] using hx
                      exact Finset.mem_singleton.mpr h_eq
                  -- Build the surgical 4-edge G-walk.
                  refine
                    ⟨Walk.cons u (.forwardE h_au)
                      (Walk.cons w (.forwardE h_uw)
                        (Walk.cons u (.backwardE h_uw)
                          (Walk.cons mid' (.forwardE h_um) p_tail_inner_fixed))),
                     ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- u-non-collider on surgical walk.
                    intro k hk_vert
                    -- Surgical walk positions: 0=a, 1=u, 2=w, 3=u, 4=mid', k+5=p_tail_inner_fixed[k+1].
                    cases k with
                    | zero =>
                        exfalso
                        have h_v0 :
                            (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                (Walk.cons u (.backwardE h_uw)
                                  (Walk.cons mid' (.forwardE h_um)
                                    p_tail_inner_fixed)))).vertices[0]?
                              = some a :=
                          Walk.vertices_zero_eq_source' _
                        rw [h_v0] at hk_vert
                        exact ha (Option.some.inj hk_vert)
                    | succ k1 =>
                        cases k1 with
                        | zero =>
                            -- pos 1 = u; IsNonCollider 1.
                            refine ⟨?_, ?_⟩
                            · show 1 ≤ p_tail_inner_fixed.length + 4
                              omega
                            · intro h_coll
                              -- IsCollider 1 = forwardE.HeadAtTarget ∧ forwardE.HeadAtSource = True ∧ False
                              exact h_coll.2.elim
                        | succ k2 =>
                            cases k2 with
                            | zero =>
                                -- pos 2 = w; w ≠ u.
                                exfalso
                                have h_v2 :
                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                        (Walk.cons u (.backwardE h_uw)
                                          (Walk.cons mid' (.forwardE h_um)
                                            p_tail_inner_fixed)))).vertices[2]?
                                      = some w := rfl
                                rw [h_v2] at hk_vert
                                exact h_w_ne_u (Option.some.inj hk_vert)
                            | succ k3 =>
                                cases k3 with
                                | zero =>
                                    -- pos 3 = u; IsNonCollider 3.
                                    refine ⟨?_, ?_⟩
                                    · show 3 ≤ p_tail_inner_fixed.length + 4
                                      omega
                                    · intro h_coll
                                      -- IsCollider 3 reduces through cons-pattern.  For our nested cons-cons-cons-cons,
                                      -- IsCollider 3 = inner-cons.IsCollider 2 = inner2-cons.IsCollider 1
                                      -- = (.backwardE h_uw).HeadAtTarget ∧ (.forwardE h_um).HeadAtSource = False ∧ False
                                      exact h_coll.1.elim
                                | succ k4 =>
                                    cases k4 with
                                    | zero =>
                                        -- pos 4 = mid' ≠ u.
                                        exfalso
                                        have h_v4 :
                                            (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                (Walk.cons u (.backwardE h_uw)
                                                  (Walk.cons mid' (.forwardE h_um)
                                                    p_tail_inner_fixed)))).vertices[4]?
                                              = some mid' := by
                                          show p_tail_inner_fixed.vertices[0]? = some mid'
                                          exact Walk.vertices_zero_eq_source' _
                                        rw [h_v4] at hk_vert
                                        exact h_mid'_ne_u (Option.some.inj hk_vert)
                                    | succ k5 =>
                                        -- pos k5+5 = p_tail_inner_fixed.vertices[k5+1]?
                                        have hk_inner :
                                            p_tail_inner_fixed.vertices[k5 + 1]? = some u := hk_vert
                                        have h_nc_inner_k := h_nc_pf_inner (k5 + 1) hk_inner
                                        refine ⟨?_, ?_⟩
                                        · have h1 := h_nc_inner_k.1
                                          show k5 + 5 ≤ p_tail_inner_fixed.length + 4
                                          omega
                                        · intro h_coll_outer
                                          apply h_nc_inner_k.2
                                          cases p_tail_inner_fixed with
                                          | nil _ _ =>
                                              exact absurd hk_inner (by simp [Walk.vertices])
                                          | cons _ _ _ => exact h_coll_outer
                  · -- no-cons-u on surgical walk.
                    intro k hk_vert h_kp1
                    -- Similar position dispatch.
                    cases k with
                    | zero =>
                        exfalso
                        have h_v0 :
                            (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                (Walk.cons u (.backwardE h_uw)
                                  (Walk.cons mid' (.forwardE h_um)
                                    p_tail_inner_fixed)))).vertices[0]?
                              = some a :=
                          Walk.vertices_zero_eq_source' _
                        rw [h_v0] at hk_vert
                        exact ha (Option.some.inj hk_vert)
                    | succ k1 =>
                        cases k1 with
                        | zero =>
                            -- pos 1 = u, pos 2 should be u (h_kp1 says vertices[2] = some u). But vertices[2] = w ≠ u.
                            exfalso
                            have h_v2 :
                                (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                    (Walk.cons u (.backwardE h_uw)
                                      (Walk.cons mid' (.forwardE h_um)
                                        p_tail_inner_fixed)))).vertices[2]?
                                  = some w := rfl
                            rw [h_v2] at h_kp1
                            exact h_w_ne_u (Option.some.inj h_kp1)
                        | succ k2 =>
                            cases k2 with
                            | zero =>
                                exfalso
                                have h_v2 :
                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                        (Walk.cons u (.backwardE h_uw)
                                          (Walk.cons mid' (.forwardE h_um)
                                            p_tail_inner_fixed)))).vertices[2]?
                                      = some w := rfl
                                rw [h_v2] at hk_vert
                                exact h_w_ne_u (Option.some.inj hk_vert)
                            | succ k3 =>
                                cases k3 with
                                | zero =>
                                    -- pos 3 = u, pos 4 should be u. But pos 4 = mid' ≠ u.
                                    exfalso
                                    have h_v4 :
                                        (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                            (Walk.cons u (.backwardE h_uw)
                                              (Walk.cons mid' (.forwardE h_um)
                                                p_tail_inner_fixed)))).vertices[4]?
                                          = some mid' := by
                                      show p_tail_inner_fixed.vertices[0]? = some mid'
                                      exact Walk.vertices_zero_eq_source' _
                                    rw [h_v4] at h_kp1
                                    exact h_mid'_ne_u (Option.some.inj h_kp1)
                                | succ k4 =>
                                    cases k4 with
                                    | zero =>
                                        exfalso
                                        have h_v4 :
                                            (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                (Walk.cons u (.backwardE h_uw)
                                                  (Walk.cons mid' (.forwardE h_um)
                                                    p_tail_inner_fixed)))).vertices[4]?
                                              = some mid' := by
                                          show p_tail_inner_fixed.vertices[0]? = some mid'
                                          exact Walk.vertices_zero_eq_source' _
                                        rw [h_v4] at hk_vert
                                        exact h_mid'_ne_u (Option.some.inj hk_vert)
                                    | succ k5 =>
                                        have hk_inner :
                                            p_tail_inner_fixed.vertices[k5 + 1]? = some u := hk_vert
                                        have h_kp1_inner :
                                            p_tail_inner_fixed.vertices[k5 + 2]? = some u := h_kp1
                                        exact h_nocons_pf_inner (k5 + 1) hk_inner h_kp1_inner
                  · -- NBS on surgical walk.
                    intro i v h_i h_ip1 h_ip2 h_bif
                    -- NBS positions to check: 0 (a/u/w), 1 (u/w/u), 2 (w/u/mid'), 3 (u/mid'/p_inner_fixed[1]),
                    -- i+4 (p_tail_inner_fixed-derived).
                    cases i with
                    | zero =>
                        -- vertices[0]=a, [1]=u, [2]=w.  NBS requires a = w.
                        -- If w ≠ a: vacuous.  If w = a: ¬IsBifurcationFlankAt 1.
                        -- IsBifurcationFlankAt 1 = forwardE.HeadAtSource ∧ forwardE.HeadAtTarget = False ∧ True
                        exact h_bif.1.elim
                    | succ i1 =>
                        cases i1 with
                        | zero =>
                            -- vertices[1]=u (matches v=u), [2]=w (h_ip1 says =u, but w≠u).
                            exfalso
                            have h_v2 :
                                (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                    (Walk.cons u (.backwardE h_uw)
                                      (Walk.cons mid' (.forwardE h_um)
                                        p_tail_inner_fixed)))).vertices[2]?
                                  = some w := rfl
                            rw [h_v2] at h_ip1
                            exact h_w_ne_u (Option.some.inj h_ip1)
                        | succ i2 =>
                            cases i2 with
                            | zero =>
                                -- vertices[2]=w (=v), [3]=u (matches h_ip1), [4]=mid'.
                                -- NBS requires v=w=mid'.  But w ≠ mid'.
                                exfalso
                                have h_v2 :
                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                        (Walk.cons u (.backwardE h_uw)
                                          (Walk.cons mid' (.forwardE h_um)
                                            p_tail_inner_fixed)))).vertices[2]?
                                      = some w := rfl
                                rw [h_v2] at h_i
                                have h_v_eq_w : v = w := (Option.some.inj h_i).symm
                                have h_v4 :
                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                        (Walk.cons u (.backwardE h_uw)
                                          (Walk.cons mid' (.forwardE h_um)
                                            p_tail_inner_fixed)))).vertices[4]?
                                      = some mid' := by
                                  show p_tail_inner_fixed.vertices[0]? = some mid'
                                  exact Walk.vertices_zero_eq_source' _
                                rw [h_v4] at h_ip2
                                have h_v_eq_mid' : v = mid' := (Option.some.inj h_ip2).symm
                                exact h_w_ne_mid' (h_v_eq_w ▸ h_v_eq_mid')
                            | succ i3 =>
                                cases i3 with
                                | zero =>
                                    -- vertices[3]=u, [4]=mid' (h_ip1 says =u, but mid' ≠ u).
                                    exfalso
                                    have h_v4 :
                                        (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                            (Walk.cons u (.backwardE h_uw)
                                              (Walk.cons mid' (.forwardE h_um)
                                                p_tail_inner_fixed)))).vertices[4]?
                                          = some mid' := by
                                      show p_tail_inner_fixed.vertices[0]? = some mid'
                                      exact Walk.vertices_zero_eq_source' _
                                    rw [h_v4] at h_ip1
                                    exact h_mid'_ne_u (Option.some.inj h_ip1)
                                | succ i4 =>
                                    -- i = i4+4: shift to p_tail_inner_fixed at i4.
                                    apply h_nobif_pf_inner i4 v h_i h_ip1 h_ip2
                                    cases p_tail_inner_fixed with
                                    | nil _ _ => exact h_bif.elim
                                    | cons _ _ _ => exact h_bif
                  · -- σ-open on surgical walk.
                    refine ⟨?_, ?_⟩
                    · -- Collider clause.
                      intro k vk hk_vert h_coll
                      cases k with
                      | zero =>
                          rw [isCollider_cons_zero_eq_false _ _] at h_coll
                          exact h_coll.elim
                      | succ k1 =>
                          cases k1 with
                          | zero =>
                              -- pos 1: IsCollider 1 = forwardE.HeadAtTarget ∧ forwardE.HeadAtSource = True ∧ False.
                              exact h_coll.2.elim
                          | succ k2 =>
                              cases k2 with
                              | zero =>
                                  -- pos 2 = w; vk = w.  IsCollider 2 on surgical walk.
                                  -- Need w ∈ G.AncSet C.
                                  have hvk_w : vk = w := by
                                    have h_v2 :
                                        (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                            (Walk.cons u (.backwardE h_uw)
                                              (Walk.cons mid' (.forwardE h_um)
                                                p_tail_inner_fixed)))).vertices[2]?
                                          = some w := rfl
                                    rw [h_v2] at hk_vert
                                    exact (Option.some.inj hk_vert).symm
                                  rw [hvk_w]
                                  exact h_w_in_AncSet_C
                              | succ k3 =>
                                  cases k3 with
                                  | zero =>
                                      -- pos 3: IsCollider 3 = (.bw h_uw).HeadAtTarget ∧ (.fw h_um).HeadAtSource = False ∧ False.
                                      exact h_coll.1.elim
                                  | succ k4 =>
                                      cases k4 with
                                      | zero =>
                                          -- pos 4 = mid'; substantive via h_sigma_open.
                                          have hvk_mid' : vk = mid' := by
                                            have h_v4 :
                                                (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                    (Walk.cons u (.backwardE h_uw)
                                                      (Walk.cons mid' (.forwardE h_um)
                                                        p_tail_inner_fixed)))).vertices[4]?
                                                  = some mid' := by
                                              show p_tail_inner_fixed.vertices[0]? = some mid'
                                              exact Walk.vertices_zero_eq_source' _
                                            rw [h_v4] at hk_vert
                                            exact (Option.some.inj hk_vert).symm
                                          rw [hvk_mid']
                                          -- IsCollider 4 on surgical walk = (.fw h_um).HeadAtTarget ∧ (next step).HeadAtSource
                                          -- = True ∧ (next step).HeadAtSource.  Need to know p_tail_inner_fixed's first step.
                                          -- Transport via meta-invariants on p_tail_inner.
                                          cases h_pti : p_tail_inner with
                                          | nil v_pti hv_pti =>
                                              have h_pti_lz : p_tail_inner.length = 0 := by
                                                rw [h_pti]; rfl
                                              have h_pf_inner_lz :
                                                  p_tail_inner_fixed.length = 0 :=
                                                h_nil_pres_inner.mp h_pti_lz
                                              cases p_tail_inner_fixed with
                                              | nil _ _ => exact h_coll.elim
                                              | cons _ _ _ =>
                                                  simp [Walk.length] at h_pf_inner_lz
                                          | cons mid_x s_first p_inner_inner =>
                                              obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                                h_fst_pres_inner s_first p_inner_inner h_pti
                                              rw [h_pf_eq] at h_coll
                                              -- IsCollider 4 on outer p_fixed (with cons s_first p_inner_inner_fixed inner)
                                              -- reduces to (cons mid' s_first ...).IsCollider 1 (or similar).
                                              -- Match with IsCollider 2 on input p (cons u s' (cons mid' s₂ p_tail_inner)).
                                              -- After cases s' / s₂ as forwardE (which we did via subst h_s'_eq h_s₂_eq),
                                              -- input p IsCollider 2 = (cons mid' .fw h_um (cons mid_x s_first p_inner_inner)).IsCollider 1
                                              -- = (.fw h_um).HeadAtTarget ∧ s_first.HeadAtSource = True ∧ s_first.HeadAtSource.
                                              have h_input_coll :
                                                  (Walk.cons u (.forwardE h_au) (Walk.cons mid'
                                                      (.forwardE h_um) p_tail_inner)).IsCollider 2 := by
                                                rw [h_pti]
                                                cases s_first <;>
                                                  first
                                                  | exact h_coll
                                                  | exact h_coll.elim
                                                  | exact ⟨h_coll.1, h_coll.2⟩
                                              have h_vert_mid' :
                                                  (Walk.cons u (.forwardE h_au) (Walk.cons mid'
                                                      (.forwardE h_um) p_tail_inner)).vertices[2]?
                                                    = some mid' := by
                                                show p_tail_inner.vertices[0]? = some mid'
                                                exact Walk.vertices_zero_eq_source' p_tail_inner
                                              exact h_sigma_open.1 2 mid' h_vert_mid' h_input_coll
                                      | succ k5 =>
                                          -- pos k5+5: shift to p_tail_inner_fixed at k5+1.
                                          have hvk_tail :
                                              p_tail_inner_fixed.vertices[k5 + 1]? = some vk :=
                                            hk_vert
                                          have h_tail_coll :
                                              p_tail_inner_fixed.IsCollider (k5 + 1) := by
                                            cases p_tail_inner_fixed with
                                            | nil _ _ => exact h_coll.elim
                                            | cons _ _ _ => exact h_coll
                                          exact h_so_pf_inner.1 (k5 + 1) vk hvk_tail h_tail_coll
                    · -- Blockable clause.
                      intro k vk hk_vert h_blk h_pos
                      cases k with
                      | zero => omega
                      | succ k1 =>
                          cases k1 with
                          | zero =>
                              -- pos 1 = u; need u ∉ C.
                              have hvk_u : vk = u := by
                                have h_v1 :
                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                        (Walk.cons u (.backwardE h_uw)
                                          (Walk.cons mid' (.forwardE h_um)
                                            p_tail_inner_fixed)))).vertices[1]?
                                      = some u := rfl
                                rw [h_v1] at hk_vert
                                exact (Option.some.inj hk_vert).symm
                              rw [hvk_u]
                              exact hu_notC
                          | succ k2 =>
                              cases k2 with
                              | zero =>
                                  -- pos 2 = w; IsBlockableNonCollider 2 vacuous since IsCollider 2 = True.
                                  exfalso
                                  obtain ⟨h_nc_w, _⟩ := h_blk
                                  apply h_nc_w.2
                                  -- IsCollider 2 on surgical walk = True ∧ True = True (collider at w).
                                  exact ⟨trivial, trivial⟩
                              | succ k3 =>
                                  cases k3 with
                                  | zero =>
                                      -- pos 3 = u; need u ∉ C.
                                      have hvk_u : vk = u := by
                                        have h_v3 :
                                            (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                (Walk.cons u (.backwardE h_uw)
                                                  (Walk.cons mid' (.forwardE h_um)
                                                    p_tail_inner_fixed)))).vertices[3]?
                                              = some u := rfl
                                        rw [h_v3] at hk_vert
                                        exact (Option.some.inj hk_vert).symm
                                      rw [hvk_u]
                                      exact hu_notC
                                  | succ k4 =>
                                      cases k4 with
                                      | zero =>
                                          -- pos 4 = mid'; transport via h_sigma_open.
                                          have hvk_mid' : vk = mid' := by
                                            have h_v4 :
                                                (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                    (Walk.cons u (.backwardE h_uw)
                                                      (Walk.cons mid' (.forwardE h_um)
                                                        p_tail_inner_fixed)))).vertices[4]?
                                                  = some mid' := by
                                              show p_tail_inner_fixed.vertices[0]? = some mid'
                                              exact Walk.vertices_zero_eq_source' _
                                            rw [h_v4] at hk_vert
                                            exact (Option.some.inj hk_vert).symm
                                          rw [hvk_mid']
                                          -- Cases on p_tail_inner via meta-invariants.
                                          -- BEFORE cases: build the σ-open discharge using
                                          -- the input walk, *before* index-substitution kicks in.
                                          have hv2_input :
                                              (Walk.cons u (.forwardE h_au)
                                                (Walk.cons mid' (.forwardE h_um)
                                                  p_tail_inner)).vertices[2]? = some mid' := by
                                            show p_tail_inner.vertices[0]? = some mid'
                                            exact Walk.vertices_zero_eq_source' p_tail_inner
                                          suffices h_blk_input :
                                              (Walk.cons u (.forwardE h_au)
                                                (Walk.cons mid' (.forwardE h_um)
                                                  p_tail_inner)).IsBlockableNonCollider 2 from
                                            h_sigma_open.2 2 mid' hv2_input h_blk_input (by omega)
                                          cases h_pti : p_tail_inner with
                                          | nil _ _ =>
                                              -- input walk = cons u .fw (cons _ .fw nil _ _).
                                              -- Goal already substituted by cases.
                                              refine ⟨?_, ?_⟩
                                              · refine ⟨?_, ?_⟩
                                                · simp [Walk.length]
                                                · intro h_coll; cases h_coll
                                              · right; left
                                                simp [Walk.length]
                                          | cons mid_x s_first p_inner_inner =>
                                              obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                                h_fst_pres_inner s_first p_inner_inner h_pti
                                              rw [h_pf_eq] at h_blk
                                              obtain ⟨h_nc_outer, h_disj_outer⟩ := h_blk
                                              refine ⟨?_, ?_⟩
                                              · refine ⟨?_, ?_⟩
                                                · show 2 ≤
                                                      (Walk.cons mid_x s_first p_inner_inner).length + 2
                                                  simp [Walk.length]
                                                · intro h_coll_input
                                                  apply h_nc_outer.2
                                                  cases s_first <;>
                                                    first
                                                    | exact h_coll_input
                                                    | exact h_coll_input.elim
                                                    | exact ⟨h_coll_input.1, h_coll_input.2⟩
                                              · rcases h_disj_outer with h_eq0 | h_eq_len | hHBLS | hHBRS
                                                · exact absurd h_eq0 (by omega)
                                                · exfalso
                                                  have h_len_eq :
                                                      (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                          (Walk.cons u (.backwardE h_uw)
                                                            (Walk.cons mid' (.forwardE h_um)
                                                              (Walk.cons mid_x s_first p_inner_inner_fixed))))).length
                                                        = p_inner_inner_fixed.length + 5 := rfl
                                                  rw [h_len_eq] at h_eq_len
                                                  omega
                                                · right; right; left
                                                  -- HBLS 4 on surgical outer reduces through cons-shifts.
                                                  simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                                · right; right; right
                                                  simp only [Walk.HasBlockingRightSlot] at hHBRS ⊢
                                                  cases s_first <;>
                                                    first
                                                    | exact hHBRS
                                                    | exact hHBRS.elim
                                      | succ k5 =>
                                          -- pos k5+5: shift to p_tail_inner_fixed.
                                          have hvk_tail :
                                              p_tail_inner_fixed.vertices[k5 + 1]? = some vk :=
                                            hk_vert
                                          have h_tail_blk :
                                              p_tail_inner_fixed.IsBlockableNonCollider (k5 + 1) := by
                                            obtain ⟨h_nc, h_disj⟩ := h_blk
                                            refine ⟨?_, ?_⟩
                                            · refine ⟨?_, ?_⟩
                                              · have h1 := h_nc.1
                                                have h_len_eq :
                                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                        (Walk.cons u (.backwardE h_uw)
                                                          (Walk.cons mid' (.forwardE h_um)
                                                            p_tail_inner_fixed)))).length
                                                      = p_tail_inner_fixed.length + 4 := rfl
                                                omega
                                              · intro h_coll_tail
                                                apply h_nc.2
                                                cases p_tail_inner_fixed with
                                                | nil _ _ =>
                                                    exact absurd h_coll_tail
                                                      (by cases k5 <;> exact id)
                                                | cons _ _ _ => exact h_coll_tail
                                            · rcases h_disj with h_eq0 | h_eq_len | hHBLS | hHBRS
                                              · omega
                                              · right; left
                                                have h_len_eq :
                                                    (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                        (Walk.cons u (.backwardE h_uw)
                                                          (Walk.cons mid' (.forwardE h_um)
                                                            p_tail_inner_fixed)))).length
                                                      = p_tail_inner_fixed.length + 4 := rfl
                                                omega
                                              · right; right; left
                                                cases p_tail_inner_fixed with
                                                | nil _ _ =>
                                                    simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                                | cons _ _ _ => exact hHBLS
                                              · right; right; right
                                                cases p_tail_inner_fixed with
                                                | nil _ _ =>
                                                    simp only [Walk.HasBlockingRightSlot] at hHBRS
                                                | cons _ _ _ => exact hHBRS
                                          exact h_so_pf_inner.2 (k5 + 1) vk hvk_tail h_tail_blk
                                            (by omega)
                  · -- Nil-pres iff (vacuous on both sides, length ≥ 2 / 4).
                    constructor
                    · intro h_p_len
                      exfalso
                      have h_len_eq :
                          (Walk.cons u (.forwardE h_au) (Walk.cons mid' (.forwardE h_um)
                              p_tail_inner)).length
                            = p_tail_inner.length + 2 := rfl
                      omega
                    · intro h_pf_len
                      exfalso
                      have h_len_eq :
                          (Walk.cons u (.forwardE h_au) (Walk.cons w (.forwardE h_uw)
                              (Walk.cons u (.backwardE h_uw)
                                (Walk.cons mid' (.forwardE h_um)
                                  p_tail_inner_fixed)))).length
                            = p_tail_inner_fixed.length + 4 := rfl
                      omega
                  · -- First-step pres.
                    intro mid'' s'' p_tail'' h_eq
                    cases h_eq
                    exact ⟨_, rfl⟩
                  · -- p'_fixed = 2 marg-cells: (a → w forwardE) + (w ↔ mid' bidir).
                    refine ⟨Walk.cons w (.forwardE h_marg_E_aw)
                              (Walk.cons mid' (.bidir h_marg_L_wmid) p_tail_inner_lift),
                            ?_, ?_⟩
                    · -- IsLift: two nested cons_two_edge.
                      refine IsLift.cons_two_edge (.forwardE h_marg_E_aw)
                        (Walk.cons mid' (.bidir h_marg_L_wmid) p_tail_inner_lift)
                        (.forwardE h_au) (.forwardE h_uw)
                        (Walk.cons u (.backwardE h_uw)
                          (Walk.cons mid' (.forwardE h_um) p_tail_inner_fixed))
                        Iff.rfl Iff.rfl ?_ ?_
                      · -- hNonColl outer: ¬(True ∧ False) = ¬False.
                        intro ⟨_, h2⟩
                        exact h2.elim
                      · -- Inner IsLift.
                        refine IsLift.cons_two_edge (.bidir h_marg_L_wmid) p_tail_inner_lift
                          (.backwardE h_uw) (.forwardE h_um) p_tail_inner_fixed
                          Iff.rfl Iff.rfl ?_ h_lift_inner
                        intro ⟨h1, _⟩
                        exact h1.elim
                    · -- NPL: two nested two_edge_npl.
                      refine NoProblematicLift.two_edge_npl (.forwardE h_marg_E_aw)
                        (Walk.cons mid' (.bidir h_marg_L_wmid) p_tail_inner_lift)
                        (.forwardE h_au) (.forwardE h_uw)
                        (Walk.cons u (.backwardE h_uw)
                          (Walk.cons mid' (.forwardE h_um) p_tail_inner_fixed))
                        ?_ ?_ ?_
                      · -- h_fwd: substantive.  Need w ∈ marg.Sc a (have).
                        intro _ _ _
                        exact h_w_in_marg_Sc_a
                      · -- h_bwd: vacuous (.forwardE has HeadAtSource = False).
                        intro ⟨h1, _⟩
                        exact h1.elim
                      · -- NPL inner: s_marg = .bidir, both h_fwd / h_bwd vacuous.
                        refine NoProblematicLift.two_edge_npl (.bidir h_marg_L_wmid)
                          p_tail_inner_lift (.backwardE h_uw) (.forwardE h_um)
                          p_tail_inner_fixed ?_ ?_ h_npl_inner
                        · -- h_fwd antecedent ⟨¬True, True⟩ → False via .1 trivial.
                          intro h_ant
                          exact (h_ant.1 trivial).elim
                        · -- h_bwd antecedent ⟨True, ¬True⟩ → False via .2 trivial.
                          intro h_ant
                          exact (h_ant.2 trivial).elim
                · by_cases h_use_surgery_bwbw :
                      (∃ (h_au_x : (u, a) ∈ G.E) (h_um_x : (mid', u) ∈ G.E),
                        s' = WalkStep.backwardE h_au_x ∧
                        s₂ = WalkStep.backwardE h_um_x) ∧
                      mid' ∈ C ∧ u ∈ G.Sc mid' ∧ a ∉ (G.marginalize {u} hu).Sc mid'
                  · -- SURGICAL (bw, bw).  Symmetric to (fw, fw).
                    -- Surgical 4-edge G-walk: `a ← u → w' ← u ← mid'`.
                    -- Marg-walk: `cons w' (.bidir) (cons mid' (.backwardE) ...)`.
                    obtain ⟨⟨h_au, h_um, h_s'_eq, h_s₂_eq⟩, hm_C, h_uSc, h_a_notSc⟩ :=
                      h_use_surgery_bwbw
                    subst h_s'_eq
                    subst h_s₂_eq
                    -- Extract w' via sc_clean_successor.
                    obtain ⟨w, h_uw, h_w_ne_u, h_w_in_Sc_mid'⟩ :=
                      sc_clean_successor h_mid'_ne_u h_uSc
                    -- Membership facts.
                    have h_w_GV : w ∈ G.V := (G.hE_subset h_uw).2
                    have h_w_G : w ∈ G := Finset.mem_union_right _ h_w_GV
                    have h_w_marg_mem : w ∈ G.marginalize {u} hu := by
                      change w ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                      refine Finset.mem_union_right _
                        (Finset.mem_sdiff.mpr ⟨h_w_GV, ?_⟩)
                      intro h_in
                      exact h_w_ne_u (Finset.mem_singleton.mp h_in)
                    have h_a_G : a ∈ G := Finset.mem_union_right _ (G.hE_subset h_au).2
                    have h_a_marg_mem : a ∈ G.marginalize {u} hu := by
                      change a ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                      rcases Finset.mem_union.mp h_a_G with hJ | hV
                      · exact Finset.mem_union_left _ hJ
                      · refine Finset.mem_union_right _
                          (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
                        intro h_in
                        exact ha (Finset.mem_singleton.mp h_in)
                    have h_mid'_G : mid' ∈ G := (G.hE_subset h_um).1
                    have h_mid'_marg_mem : mid' ∈ G.marginalize {u} hu := by
                      change mid' ∈ G.J ∪ (G.V \ ({u} : Finset Node))
                      rcases Finset.mem_union.mp h_mid'_G with hJ | hV
                      · exact Finset.mem_union_left _ hJ
                      · refine Finset.mem_union_right _
                          (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
                        intro h_in
                        exact h_mid'_ne_u (Finset.mem_singleton.mp h_in)
                    have h_a_marg :
                        a ∈ G.V \ ({u} : Finset Node) := by
                      rw [Finset.mem_sdiff, Finset.mem_singleton]
                      exact ⟨(G.hE_subset h_au).2, ha⟩
                    have h_a_carrier :
                        a ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                      Finset.mem_union_right _ h_a_marg
                    have h_mid'_carrier :
                        mid' ∈ G.J ∪ (G.V \ ({u} : Finset Node)) := h_mid'_marg_mem
                    have h_w_marg :
                        w ∈ G.V \ ({u} : Finset Node) := by
                      rw [Finset.mem_sdiff, Finset.mem_singleton]
                      exact ⟨h_w_GV, h_w_ne_u⟩
                    have h_w_carrier :
                        w ∈ G.J ∪ (G.V \ ({u} : Finset Node)) :=
                      Finset.mem_union_right _ h_w_marg
                    -- w ∈ marg.Sc mid' (key for NPL.h_bwd).
                    have h_w_in_marg_Sc_mid' :
                        w ∈ (G.marginalize {u} hu).Sc mid' :=
                      (marg_sc_iff_G_sc u hu h_mid'_marg_mem h_w_G h_w_ne_u).mpr
                        h_w_in_Sc_mid'
                    -- w ≠ a (from problematic).
                    have h_w_ne_a : w ≠ a := by
                      intro h_w_eq
                      rw [h_w_eq] at h_w_in_marg_Sc_mid'
                      exact h_a_notSc h_w_in_marg_Sc_mid'
                    have h_a_ne_w : a ≠ w := h_w_ne_a.symm
                    -- w ∈ G.AncSet C (for σ-open at the surgical w-collider).
                    have h_w_in_AncSet_C : w ∈ G.AncSet C := by
                      unfold CDMG.AncSet
                      simp only [Set.mem_iUnion]
                      exact ⟨mid', hm_C, h_w_in_Sc_mid'.1⟩
                    -- Build marg-cell 1: s(a, w) ∈ marg.L (fork a ← u → w).
                    have h_marg_L_aw :
                        s(a, w) ∈ (G.marginalize {u} hu).L := by
                      rw [marginalize_L_iff]
                      refine ⟨(a, w), h_a_marg, h_w_marg, h_a_ne_w, ?_, rfl⟩
                      left
                      refine ⟨Walk.cons u (.backwardE h_au)
                                (Walk.cons w (.forwardE h_uw)
                                  (.nil w h_w_G)),
                              ?_, ?_⟩
                      · refine ⟨h_a_ne_w, ?_, ?_, 0, ?_⟩
                        · intro hmem
                          have h_in : a ∈ (u :: ([w] : List Node)) := hmem
                          rcases List.mem_cons.mp h_in with hau | haw_in
                          · exact ha hau
                          · exact h_a_ne_w (List.mem_singleton.mp haw_in)
                        · intro hmem
                          have h_in : w ∈ (a :: ([u] : List Node)) := hmem
                          rcases List.mem_cons.mp h_in with hwa | hwu_in
                          · exact h_w_ne_a hwa
                          · exact h_w_ne_u (List.mem_singleton.mp hwu_in)
                        · exact True.intro
                      · intro x hx
                        have h_eq : x = u := by
                          simpa only [Walk.vertices, List.tail_cons,
                            List.dropLast_cons_of_ne_nil, List.dropLast,
                            List.mem_singleton] using hx
                        exact Finset.mem_singleton.mpr h_eq
                    -- Build marg-cell 2: (mid', w) ∈ marg.E (via 2-edge mid' → u → w).
                    have h_marg_E_midw :
                        (mid', w) ∈ (G.marginalize {u} hu).E := by
                      change (mid', w) ∈ ((G.J ∪ (G.V \ ({u} : Finset Node))) ×ˢ
                              (G.V \ ({u} : Finset Node))).filter
                            (fun e => G.MarginalizationΦE {u} e.1 e.2)
                      refine Finset.mem_filter.mpr
                        ⟨Finset.mem_product.mpr
                          ⟨h_mid'_carrier, h_w_marg⟩, ?_⟩
                      refine ⟨Walk.cons u (.forwardE h_um)
                                (Walk.cons w (.forwardE h_uw) (.nil w h_w_G)),
                              ?_, ?_, ?_⟩
                      · exact True.intro
                      · exact Nat.le_add_left 1 1
                      · intro x hx
                        have h_eq : x = u := by
                          simpa only [Walk.vertices, List.tail_cons,
                            List.dropLast_cons_of_ne_nil, List.dropLast,
                            List.mem_singleton] using hx
                        exact Finset.mem_singleton.mpr h_eq
                    -- Build the surgical 4-edge G-walk: a ← u → w ← u ← mid'.
                    refine
                      ⟨Walk.cons u (.backwardE h_au)
                        (Walk.cons w (.forwardE h_uw)
                          (Walk.cons u (.backwardE h_uw)
                            (Walk.cons mid' (.backwardE h_um) p_tail_inner_fixed))),
                       ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · -- u-non-collider on (bw,bw) surgical walk.
                      -- Positions: 0=a, 1=u, 2=w, 3=u, 4=mid', k+5=p_tail_inner_fixed[k+1].
                      intro k hk_vert
                      cases k with
                      | zero =>
                          exfalso
                          have h_v0 :
                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                  (Walk.cons u (.backwardE h_uw)
                                    (Walk.cons mid' (.backwardE h_um)
                                      p_tail_inner_fixed)))).vertices[0]?
                                = some a :=
                            Walk.vertices_zero_eq_source' _
                          rw [h_v0] at hk_vert
                          exact ha (Option.some.inj hk_vert)
                      | succ k1 =>
                          cases k1 with
                          | zero =>
                              -- pos 1 = u; IsNonCollider 1.
                              refine ⟨?_, ?_⟩
                              · show 1 ≤ p_tail_inner_fixed.length + 4
                                omega
                              · intro h_coll
                                -- IsCollider 1 = (.bw).HeadAtTarget ∧ (.fw).HeadAtSource = False ∧ False
                                exact h_coll.1.elim
                          | succ k2 =>
                              cases k2 with
                              | zero =>
                                  -- pos 2 = w; w ≠ u.
                                  exfalso
                                  have h_v2 :
                                      (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                          (Walk.cons u (.backwardE h_uw)
                                            (Walk.cons mid' (.backwardE h_um)
                                              p_tail_inner_fixed)))).vertices[2]?
                                        = some w := rfl
                                  rw [h_v2] at hk_vert
                                  exact h_w_ne_u (Option.some.inj hk_vert)
                              | succ k3 =>
                                  cases k3 with
                                  | zero =>
                                      -- pos 3 = u; IsNonCollider 3.
                                      refine ⟨?_, ?_⟩
                                      · show 3 ≤ p_tail_inner_fixed.length + 4
                                        omega
                                      · intro h_coll
                                        -- IsCollider 3 = (.bw).HeadAtTarget ∧ (.bw).HeadAtSource = False ∧ True
                                        exact h_coll.1.elim
                                  | succ k4 =>
                                      cases k4 with
                                      | zero =>
                                          -- pos 4 = mid' ≠ u.
                                          exfalso
                                          have h_v4 :
                                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                  (Walk.cons u (.backwardE h_uw)
                                                    (Walk.cons mid' (.backwardE h_um)
                                                      p_tail_inner_fixed)))).vertices[4]?
                                                = some mid' := by
                                            show p_tail_inner_fixed.vertices[0]? = some mid'
                                            exact Walk.vertices_zero_eq_source' _
                                          rw [h_v4] at hk_vert
                                          exact h_mid'_ne_u (Option.some.inj hk_vert)
                                      | succ k5 =>
                                          have hk_inner :
                                              p_tail_inner_fixed.vertices[k5 + 1]? = some u := hk_vert
                                          have h_nc_inner_k := h_nc_pf_inner (k5 + 1) hk_inner
                                          refine ⟨?_, ?_⟩
                                          · have h1 := h_nc_inner_k.1
                                            show k5 + 5 ≤ p_tail_inner_fixed.length + 4
                                            omega
                                          · intro h_coll_outer
                                            apply h_nc_inner_k.2
                                            cases p_tail_inner_fixed with
                                            | nil _ _ =>
                                                exact absurd hk_inner (by simp [Walk.vertices])
                                            | cons _ _ _ => exact h_coll_outer
                    · -- no-cons-u on (bw,bw) surgical walk.
                      intro k hk_vert h_kp1
                      cases k with
                      | zero =>
                          exfalso
                          have h_v0 :
                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                  (Walk.cons u (.backwardE h_uw)
                                    (Walk.cons mid' (.backwardE h_um)
                                      p_tail_inner_fixed)))).vertices[0]?
                                = some a :=
                            Walk.vertices_zero_eq_source' _
                          rw [h_v0] at hk_vert
                          exact ha (Option.some.inj hk_vert)
                      | succ k1 =>
                          cases k1 with
                          | zero =>
                              exfalso
                              have h_v2 :
                                  (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                      (Walk.cons u (.backwardE h_uw)
                                        (Walk.cons mid' (.backwardE h_um)
                                          p_tail_inner_fixed)))).vertices[2]?
                                    = some w := rfl
                              rw [h_v2] at h_kp1
                              exact h_w_ne_u (Option.some.inj h_kp1)
                          | succ k2 =>
                              cases k2 with
                              | zero =>
                                  exfalso
                                  have h_v2 :
                                      (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                          (Walk.cons u (.backwardE h_uw)
                                            (Walk.cons mid' (.backwardE h_um)
                                              p_tail_inner_fixed)))).vertices[2]?
                                        = some w := rfl
                                  rw [h_v2] at hk_vert
                                  exact h_w_ne_u (Option.some.inj hk_vert)
                              | succ k3 =>
                                  cases k3 with
                                  | zero =>
                                      exfalso
                                      have h_v4 :
                                          (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                              (Walk.cons u (.backwardE h_uw)
                                                (Walk.cons mid' (.backwardE h_um)
                                                  p_tail_inner_fixed)))).vertices[4]?
                                            = some mid' := by
                                        show p_tail_inner_fixed.vertices[0]? = some mid'
                                        exact Walk.vertices_zero_eq_source' _
                                      rw [h_v4] at h_kp1
                                      exact h_mid'_ne_u (Option.some.inj h_kp1)
                                  | succ k4 =>
                                      cases k4 with
                                      | zero =>
                                          exfalso
                                          have h_v4 :
                                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                  (Walk.cons u (.backwardE h_uw)
                                                    (Walk.cons mid' (.backwardE h_um)
                                                      p_tail_inner_fixed)))).vertices[4]?
                                                = some mid' := by
                                            show p_tail_inner_fixed.vertices[0]? = some mid'
                                            exact Walk.vertices_zero_eq_source' _
                                          rw [h_v4] at hk_vert
                                          exact h_mid'_ne_u (Option.some.inj hk_vert)
                                      | succ k5 =>
                                          have hk_inner :
                                              p_tail_inner_fixed.vertices[k5 + 1]? = some u := hk_vert
                                          have h_kp1_inner :
                                              p_tail_inner_fixed.vertices[k5 + 2]? = some u := h_kp1
                                          exact h_nocons_pf_inner (k5 + 1) hk_inner h_kp1_inner
                    · -- NBS on (bw,bw) surgical walk.  Key: w ≠ a guaranteed by problematic, so
                      -- pos 1 (flanks (a, w)) NBS doesn't fire.
                      intro i v h_i h_ip1 h_ip2 h_bif
                      cases i with
                      | zero =>
                          -- vertices[0]=a, [2]=w.  NBS requires v=a=w; contra h_w_ne_a.
                          exfalso
                          have h_v0 :
                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                  (Walk.cons u (.backwardE h_uw)
                                    (Walk.cons mid' (.backwardE h_um)
                                      p_tail_inner_fixed)))).vertices[0]?
                                = some a :=
                            Walk.vertices_zero_eq_source' _
                          have h_v2 :
                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                  (Walk.cons u (.backwardE h_uw)
                                    (Walk.cons mid' (.backwardE h_um)
                                      p_tail_inner_fixed)))).vertices[2]?
                                = some w := rfl
                          rw [h_v0] at h_i
                          rw [h_v2] at h_ip2
                          have h_v_eq_a : v = a := (Option.some.inj h_i).symm
                          have h_v_eq_w : v = w := (Option.some.inj h_ip2).symm
                          exact h_w_ne_a (h_v_eq_w.symm.trans h_v_eq_a)
                      | succ i1 =>
                          cases i1 with
                          | zero =>
                              exfalso
                              have h_v2 :
                                  (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                      (Walk.cons u (.backwardE h_uw)
                                        (Walk.cons mid' (.backwardE h_um)
                                          p_tail_inner_fixed)))).vertices[2]?
                                    = some w := rfl
                              rw [h_v2] at h_ip1
                              exact h_w_ne_u (Option.some.inj h_ip1)
                          | succ i2 =>
                              cases i2 with
                              | zero =>
                                  -- IsBifurcationFlankAt 3 = (.bw h_uw).HeadAtSource ∧ (.bw h_um).HeadAtTarget
                                  --   = True ∧ False; h_bif.2 : False.
                                  exact h_bif.2.elim
                              | succ i3 =>
                                  cases i3 with
                                  | zero =>
                                      exfalso
                                      have h_v4 :
                                          (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                              (Walk.cons u (.backwardE h_uw)
                                                (Walk.cons mid' (.backwardE h_um)
                                                  p_tail_inner_fixed)))).vertices[4]?
                                            = some mid' := by
                                        show p_tail_inner_fixed.vertices[0]? = some mid'
                                        exact Walk.vertices_zero_eq_source' _
                                      rw [h_v4] at h_ip1
                                      exact h_mid'_ne_u (Option.some.inj h_ip1)
                                  | succ i4 =>
                                      apply h_nobif_pf_inner i4 v h_i h_ip1 h_ip2
                                      cases p_tail_inner_fixed with
                                      | nil _ _ => exact h_bif.elim
                                      | cons _ _ _ => exact h_bif
                    · -- σ-open on (bw,bw) surgical walk.
                      refine ⟨?_, ?_⟩
                      · -- Collider clause.
                        intro k vk hk_vert h_coll
                        cases k with
                        | zero =>
                            rw [isCollider_cons_zero_eq_false _ _] at h_coll
                            exact h_coll.elim
                        | succ k1 =>
                            cases k1 with
                            | zero =>
                                -- pos 1: IsCollider 1 = (.bw).HeadAtTarget ∧ (.fw).HeadAtSource = False ∧ False.
                                exact h_coll.1.elim
                            | succ k2 =>
                                cases k2 with
                                | zero =>
                                    -- pos 2 = w; vk = w.  Need w ∈ G.AncSet C.
                                    have hvk_w : vk = w := by
                                      have h_v2 :
                                          (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                              (Walk.cons u (.backwardE h_uw)
                                                (Walk.cons mid' (.backwardE h_um)
                                                  p_tail_inner_fixed)))).vertices[2]?
                                            = some w := rfl
                                      rw [h_v2] at hk_vert
                                      exact (Option.some.inj hk_vert).symm
                                    rw [hvk_w]
                                    exact h_w_in_AncSet_C
                                | succ k3 =>
                                    cases k3 with
                                    | zero =>
                                        -- pos 3: IsCollider 3 = (.bw).HeadAtTarget ∧ (.bw).HeadAtSource = False ∧ True.
                                        exact h_coll.1.elim
                                    | succ k4 =>
                                        cases k4 with
                                        | zero =>
                                            -- pos 4 = mid'; substantive via h_sigma_open.
                                            have hvk_mid' : vk = mid' := by
                                              have h_v4 :
                                                  (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                      (Walk.cons u (.backwardE h_uw)
                                                        (Walk.cons mid' (.backwardE h_um)
                                                          p_tail_inner_fixed)))).vertices[4]?
                                                    = some mid' := by
                                                show p_tail_inner_fixed.vertices[0]? = some mid'
                                                exact Walk.vertices_zero_eq_source' _
                                              rw [h_v4] at hk_vert
                                              exact (Option.some.inj hk_vert).symm
                                            rw [hvk_mid']
                                            cases h_pti : p_tail_inner with
                                            | nil v_pti hv_pti =>
                                                have h_pti_lz : p_tail_inner.length = 0 := by
                                                  rw [h_pti]; rfl
                                                have h_pf_inner_lz :
                                                    p_tail_inner_fixed.length = 0 :=
                                                  h_nil_pres_inner.mp h_pti_lz
                                                cases p_tail_inner_fixed with
                                                | nil _ _ => exact h_coll.elim
                                                | cons _ _ _ =>
                                                    simp [Walk.length] at h_pf_inner_lz
                                            | cons mid_x s_first p_inner_inner =>
                                                obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                                  h_fst_pres_inner s_first p_inner_inner h_pti
                                                rw [h_pf_eq] at h_coll
                                                have h_input_coll :
                                                    (Walk.cons u (.backwardE h_au) (Walk.cons mid'
                                                        (.backwardE h_um) p_tail_inner)).IsCollider 2 := by
                                                  rw [h_pti]
                                                  cases s_first <;>
                                                    first
                                                    | exact h_coll
                                                    | exact h_coll.elim
                                                    | exact ⟨h_coll.1, h_coll.2⟩
                                                have h_vert_mid' :
                                                    (Walk.cons u (.backwardE h_au) (Walk.cons mid'
                                                        (.backwardE h_um) p_tail_inner)).vertices[2]?
                                                      = some mid' := by
                                                  show p_tail_inner.vertices[0]? = some mid'
                                                  exact Walk.vertices_zero_eq_source' p_tail_inner
                                                exact h_sigma_open.1 2 mid' h_vert_mid' h_input_coll
                                        | succ k5 =>
                                            have hvk_tail :
                                                p_tail_inner_fixed.vertices[k5 + 1]? = some vk :=
                                              hk_vert
                                            have h_tail_coll :
                                                p_tail_inner_fixed.IsCollider (k5 + 1) := by
                                              cases p_tail_inner_fixed with
                                              | nil _ _ => exact h_coll.elim
                                              | cons _ _ _ => exact h_coll
                                            exact h_so_pf_inner.1 (k5 + 1) vk hvk_tail h_tail_coll
                      · -- Blockable clause.
                        intro k vk hk_vert h_blk h_pos
                        cases k with
                        | zero => omega
                        | succ k1 =>
                            cases k1 with
                            | zero =>
                                -- pos 1 = u; need u ∉ C.
                                have hvk_u : vk = u := by
                                  have h_v1 :
                                      (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                          (Walk.cons u (.backwardE h_uw)
                                            (Walk.cons mid' (.backwardE h_um)
                                              p_tail_inner_fixed)))).vertices[1]?
                                        = some u := rfl
                                  rw [h_v1] at hk_vert
                                  exact (Option.some.inj hk_vert).symm
                                rw [hvk_u]
                                exact hu_notC
                            | succ k2 =>
                                cases k2 with
                                | zero =>
                                    -- pos 2 = w; w is a collider, blockable vacuous.
                                    exfalso
                                    obtain ⟨h_nc_w, _⟩ := h_blk
                                    apply h_nc_w.2
                                    exact ⟨trivial, trivial⟩
                                | succ k3 =>
                                    cases k3 with
                                    | zero =>
                                        -- pos 3 = u; need u ∉ C.
                                        have hvk_u : vk = u := by
                                          have h_v3 :
                                              (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                  (Walk.cons u (.backwardE h_uw)
                                                    (Walk.cons mid' (.backwardE h_um)
                                                      p_tail_inner_fixed)))).vertices[3]?
                                                = some u := rfl
                                          rw [h_v3] at hk_vert
                                          exact (Option.some.inj hk_vert).symm
                                        rw [hvk_u]
                                        exact hu_notC
                                    | succ k4 =>
                                        cases k4 with
                                        | zero =>
                                            -- pos 4 = mid'; substantive via h_sigma_open.
                                            have hvk_mid' : vk = mid' := by
                                              have h_v4 :
                                                  (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                      (Walk.cons u (.backwardE h_uw)
                                                        (Walk.cons mid' (.backwardE h_um)
                                                          p_tail_inner_fixed)))).vertices[4]?
                                                    = some mid' := by
                                                show p_tail_inner_fixed.vertices[0]? = some mid'
                                                exact Walk.vertices_zero_eq_source' _
                                              rw [h_v4] at hk_vert
                                              exact (Option.some.inj hk_vert).symm
                                            rw [hvk_mid']
                                            -- Build the σ-open discharge BEFORE cases (so mid' is in scope).
                                            have hv2_input :
                                                (Walk.cons u (.backwardE h_au)
                                                  (Walk.cons mid' (.backwardE h_um)
                                                    p_tail_inner)).vertices[2]? = some mid' := by
                                              show p_tail_inner.vertices[0]? = some mid'
                                              exact Walk.vertices_zero_eq_source' p_tail_inner
                                            suffices h_blk_input :
                                                (Walk.cons u (.backwardE h_au)
                                                  (Walk.cons mid' (.backwardE h_um)
                                                    p_tail_inner)).IsBlockableNonCollider 2 from
                                              h_sigma_open.2 2 mid' hv2_input h_blk_input (by omega)
                                            cases h_pti : p_tail_inner with
                                            | nil _ _ =>
                                                -- input walk = cons u .bw (cons _ .bw nil _ _), length 2.
                                                refine ⟨?_, ?_⟩
                                                · refine ⟨?_, ?_⟩
                                                  · simp [Walk.length]
                                                  · -- IsCollider 2 on cons-cons-nil with .bw = False ∧ _ = False.
                                                    intro h_coll; cases h_coll
                                                · right; left
                                                  simp [Walk.length]
                                            | cons mid_x s_first p_inner_inner =>
                                                obtain ⟨p_inner_inner_fixed, h_pf_eq⟩ :=
                                                  h_fst_pres_inner s_first p_inner_inner h_pti
                                                rw [h_pf_eq] at h_blk
                                                obtain ⟨h_nc_outer, h_disj_outer⟩ := h_blk
                                                refine ⟨?_, ?_⟩
                                                · refine ⟨?_, ?_⟩
                                                  · show 2 ≤
                                                        (Walk.cons mid_x s_first p_inner_inner).length + 2
                                                    simp [Walk.length]
                                                  · -- IsCollider 2 on input = .bw_um.HeadAtTarget ∧ s_first.HeadAtSource
                                                    --                       = False ∧ _ = False.  Trivially non-collider.
                                                    intro h_coll_input
                                                    cases s_first <;> exact h_coll_input.1.elim
                                                · rcases h_disj_outer with h_eq0 | h_eq_len | hHBLS | hHBRS
                                                  · exact absurd h_eq0 (by omega)
                                                  · exfalso
                                                    have h_len_eq :
                                                        (Walk.cons u (.backwardE h_au)
                                                            (Walk.cons w (.forwardE h_uw)
                                                              (Walk.cons u (.backwardE h_uw)
                                                                (Walk.cons mid' (.backwardE h_um)
                                                                  (Walk.cons mid_x s_first
                                                                    p_inner_inner_fixed))))).length
                                                          = p_inner_inner_fixed.length + 5 := rfl
                                                    rw [h_len_eq] at h_eq_len
                                                    omega
                                                  · -- HBLS 4 on (bw,bw) outer surgical unfolds to u ∉ G.Sc mid',
                                                    -- contradicting h_uSc : u ∈ G.Sc mid'.
                                                    exfalso
                                                    simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                                    exact hHBLS h_uSc
                                                  · right; right; right
                                                    simp only [Walk.HasBlockingRightSlot] at hHBRS ⊢
                                                    cases s_first <;>
                                                      first
                                                      | exact hHBRS
                                                      | exact hHBRS.elim
                                        | succ k5 =>
                                            have hvk_tail :
                                                p_tail_inner_fixed.vertices[k5 + 1]? = some vk :=
                                              hk_vert
                                            have h_tail_blk :
                                                p_tail_inner_fixed.IsBlockableNonCollider (k5 + 1) := by
                                              obtain ⟨h_nc, h_disj⟩ := h_blk
                                              refine ⟨?_, ?_⟩
                                              · refine ⟨?_, ?_⟩
                                                · have h1 := h_nc.1
                                                  have h_len_eq :
                                                      (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                          (Walk.cons u (.backwardE h_uw)
                                                            (Walk.cons mid' (.backwardE h_um)
                                                              p_tail_inner_fixed)))).length
                                                        = p_tail_inner_fixed.length + 4 := rfl
                                                  omega
                                                · intro h_coll_tail
                                                  apply h_nc.2
                                                  cases p_tail_inner_fixed with
                                                  | nil _ _ =>
                                                      exact absurd h_coll_tail
                                                        (by cases k5 <;> exact id)
                                                  | cons _ _ _ => exact h_coll_tail
                                              · rcases h_disj with h_eq0 | h_eq_len | hHBLS | hHBRS
                                                · omega
                                                · right; left
                                                  have h_len_eq :
                                                      (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                                          (Walk.cons u (.backwardE h_uw)
                                                            (Walk.cons mid' (.backwardE h_um)
                                                              p_tail_inner_fixed)))).length
                                                        = p_tail_inner_fixed.length + 4 := rfl
                                                  omega
                                                · right; right; left
                                                  cases p_tail_inner_fixed with
                                                  | nil _ _ =>
                                                      simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                                  | cons _ _ _ => exact hHBLS
                                                · right; right; right
                                                  cases p_tail_inner_fixed with
                                                  | nil _ _ =>
                                                      simp only [Walk.HasBlockingRightSlot] at hHBRS
                                                  | cons _ _ _ => exact hHBRS
                                            exact h_so_pf_inner.2 (k5 + 1) vk hvk_tail h_tail_blk
                                              (by omega)
                    · -- Nil-pres iff (length ≥ 2 / 4).
                      constructor
                      · intro h_p_len
                        exfalso
                        have h_len_eq :
                            (Walk.cons u (.backwardE h_au) (Walk.cons mid' (.backwardE h_um)
                                p_tail_inner)).length
                              = p_tail_inner.length + 2 := rfl
                        omega
                      · intro h_pf_len
                        exfalso
                        have h_len_eq :
                            (Walk.cons u (.backwardE h_au) (Walk.cons w (.forwardE h_uw)
                                (Walk.cons u (.backwardE h_uw)
                                  (Walk.cons mid' (.backwardE h_um)
                                    p_tail_inner_fixed)))).length
                              = p_tail_inner_fixed.length + 4 := rfl
                        omega
                    · -- First-step pres.
                      intro mid'' s'' p_tail'' h_eq
                      cases h_eq
                      exact ⟨_, rfl⟩
                    · -- p'_fixed = cons w (.bidir) (cons mid' (.backwardE) ...).
                      refine ⟨Walk.cons w (.bidir h_marg_L_aw)
                                (Walk.cons mid' (.backwardE h_marg_E_midw) p_tail_inner_lift),
                              ?_, ?_⟩
                      · -- IsLift: two nested cons_two_edge.
                        refine IsLift.cons_two_edge (.bidir h_marg_L_aw)
                          (Walk.cons mid' (.backwardE h_marg_E_midw) p_tail_inner_lift)
                          (.backwardE h_au) (.forwardE h_uw)
                          (Walk.cons u (.backwardE h_uw)
                            (Walk.cons mid' (.backwardE h_um) p_tail_inner_fixed))
                          Iff.rfl Iff.rfl ?_ ?_
                        · -- hNonColl: ¬(.backwardE.HeadAtTarget ∧ .forwardE.HeadAtSource) = ¬(False ∧ False)
                          intro ⟨h1, _⟩
                          exact h1.elim
                        · -- Inner IsLift.
                          refine IsLift.cons_two_edge (.backwardE h_marg_E_midw) p_tail_inner_lift
                            (.backwardE h_uw) (.backwardE h_um) p_tail_inner_fixed
                            Iff.rfl Iff.rfl ?_ h_lift_inner
                          intro ⟨h1, _⟩
                          exact h1.elim
                      · -- NPL: two nested two_edge_npl.
                        refine NoProblematicLift.two_edge_npl (.bidir h_marg_L_aw)
                          (Walk.cons mid' (.backwardE h_marg_E_midw) p_tail_inner_lift)
                          (.backwardE h_au) (.forwardE h_uw)
                          (Walk.cons u (.backwardE h_uw)
                            (Walk.cons mid' (.backwardE h_um) p_tail_inner_fixed))
                          ?_ ?_ ?_
                        · -- h_fwd outer vacuous (.bidir HeadAtSource = True).
                          intro h_ant
                          exact (h_ant.1 trivial).elim
                        · -- h_bwd outer vacuous (.bidir HeadAtTarget = True).
                          intro h_ant
                          exact (h_ant.2 trivial).elim
                        · -- NPL inner.
                          refine NoProblematicLift.two_edge_npl (.backwardE h_marg_E_midw)
                            p_tail_inner_lift (.backwardE h_uw) (.backwardE h_um)
                            p_tail_inner_fixed ?_ ?_ h_npl_inner
                          · -- h_fwd inner: .backwardE HeadAtSource = True; vacuous via .1 trivial.
                            intro h_ant
                            exact (h_ant.1 trivial).elim
                          · -- h_bwd inner substantive: need w ∈ marg.Sc mid'.
                            intro _ _ _
                            exact h_w_in_marg_Sc_mid'
                  · -- NON-SURGICAL: existing body.  s_marg via walkstep_lift_two_edge.
                    obtain ⟨s_marg, hSrc, hTgt⟩ :=
                      walkstep_lift_two_edge u hu ha h_mid'_ne_u h_st s' s₂ hNonColl
                    refine
                      ⟨Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner_fixed),
                        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · -- u-non-collider on cons u s' (cons mid' s₂ p_tail_inner_fixed).
                      intro k hk_vert
                      cases k with
                      | zero =>
                          exfalso
                          have h_vert0 :
                              (Walk.cons u s'
                                  (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[0]?
                                = some a :=
                            Walk.vertices_zero_eq_source' _
                          rw [h_vert0] at hk_vert
                          exact ha (Option.some.inj hk_vert)
                      | succ k1 =>
                          cases k1 with
                          | zero =>
                              -- Pos 1: vertex u.  IsNonCollider 1 from hNonColl.
                              refine ⟨?_, ?_⟩
                              · show 1 ≤ p_tail_inner_fixed.length + 2
                                omega
                              · intro h_coll1
                                -- IsCollider 1 on cons-cons-cons reduces to
                                -- s'.HeadAtTarget ∧ s₂.HeadAtSource, contra hNonColl.
                                cases p_tail_inner_fixed with
                                | nil _ _ =>
                                    exact hNonColl ⟨h_coll1.1, h_coll1.2⟩
                                | cons _ _ _ =>
                                    exact hNonColl ⟨h_coll1.1, h_coll1.2⟩
                          | succ k2 =>
                              cases k2 with
                              | zero =>
                                  -- Pos 2: vertex mid' ≠ u.
                                  exfalso
                                  have h_vert2 :
                                      (Walk.cons u s'
                                          (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                        = some mid' := by
                                    show p_tail_inner_fixed.vertices[0]? = some mid'
                                    exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                                  rw [h_vert2] at hk_vert
                                  exact h_mid'_ne_u (Option.some.inj hk_vert)
                              | succ k3 =>
                                  -- Pos k3+3: shift to p_tail_inner_fixed at pos k3+1.
                                  have hk_inner :
                                      p_tail_inner_fixed.vertices[k3 + 1]? = some u := hk_vert
                                  have h_nc_inner_k := h_nc_pf_inner (k3 + 1) hk_inner
                                  refine ⟨?_, ?_⟩
                                  · have h1 := h_nc_inner_k.1
                                    show k3 + 1 + 1 + 1 ≤ p_tail_inner_fixed.length + 2
                                    omega
                                  · intro h_coll_outer
                                    apply h_nc_inner_k.2
                                    cases p_tail_inner_fixed with
                                    | nil _ _ =>
                                        exact absurd hk_inner (by simp [Walk.vertices])
                                    | cons _ _ _ =>
                                        cases s' <;> cases s₂ <;> exact h_coll_outer
                    · -- no-consecutive-u.
                      intro k hk_vert h_kp1
                      cases k with
                      | zero =>
                          exfalso
                          have h_vert0 :
                              (Walk.cons u s'
                                  (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[0]?
                                = some a :=
                            Walk.vertices_zero_eq_source' _
                          rw [h_vert0] at hk_vert
                          exact ha (Option.some.inj hk_vert)
                      | succ k1 =>
                          cases k1 with
                          | zero =>
                              -- Pos 1: vertex u; vertices[2] = mid' ≠ u.
                              exfalso
                              have h_vert2 :
                                  (Walk.cons u s'
                                      (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                    = some mid' := by
                                show p_tail_inner_fixed.vertices[0]? = some mid'
                                exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                              rw [h_vert2] at h_kp1
                              exact h_mid'_ne_u (Option.some.inj h_kp1)
                          | succ k2 =>
                              cases k2 with
                              | zero =>
                                  -- Pos 2: vertex mid' ≠ u.
                                  exfalso
                                  have h_vert2 :
                                      (Walk.cons u s'
                                          (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                        = some mid' := by
                                    show p_tail_inner_fixed.vertices[0]? = some mid'
                                    exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                                  rw [h_vert2] at hk_vert
                                  exact h_mid'_ne_u (Option.some.inj hk_vert)
                              | succ k3 =>
                                  -- Pos k3+3: shift.
                                  have hk_inner :
                                      p_tail_inner_fixed.vertices[k3 + 1]? = some u := hk_vert
                                  have h_kp1_inner :
                                      p_tail_inner_fixed.vertices[k3 + 2]? = some u := h_kp1
                                  exact h_nocons_pf_inner (k3 + 1) hk_inner h_kp1_inner
                    · -- NBS on outer.
                      intro i v h_i h_ip1 h_ip2 h_bif
                      cases i with
                      | zero =>
                          -- vertices[0] = a, vertices[2] = mid'.  NBS needs a = mid'; contra non-side-trip.
                          have h_v_a : v = a := by
                            have h_vert0 :
                                (Walk.cons u s'
                                    (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[0]?
                                  = some a :=
                              Walk.vertices_zero_eq_source' _
                            rw [h_vert0] at h_i
                            exact (Option.some.inj h_i).symm
                          have h_v_mid' : v = mid' := by
                            have h_vert2 :
                                (Walk.cons u s'
                                    (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                  = some mid' := by
                              show p_tail_inner_fixed.vertices[0]? = some mid'
                              exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                            rw [h_vert2] at h_ip2
                            exact (Option.some.inj h_ip2).symm
                          exact h_st (h_v_a ▸ h_v_mid')
                      | succ i1 =>
                          cases i1 with
                          | zero =>
                              -- i = 1: vertices[2] should be u (h_ip1) but = mid' ≠ u.
                              exfalso
                              have h_vert2 :
                                  (Walk.cons u s'
                                      (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                    = some mid' := by
                                show p_tail_inner_fixed.vertices[0]? = some mid'
                                exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                              rw [h_vert2] at h_ip1
                              exact h_mid'_ne_u (Option.some.inj h_ip1)
                          | succ i2 =>
                              -- i = i2 + 2: shift to NBS at i2 on p_tail_inner_fixed.
                              apply h_nobif_pf_inner i2 v h_i h_ip1 h_ip2
                              cases p_tail_inner_fixed with
                              | nil _ _ => exact h_bif.elim
                              | cons _ _ _ =>
                                  cases s' <;> cases s₂ <;> exact h_bif
                    · -- σ-open on outer.
                      refine ⟨?_, ?_⟩
                      · -- Collider clause.
                        intro k vk hk_vert h_coll
                        cases k with
                        | zero =>
                            cases p_tail_inner_fixed with
                            | nil _ _ => exact h_coll.elim
                            | cons _ _ _ =>
                                rw [isCollider_cons_zero_eq_false s' _] at h_coll
                                exact h_coll.elim
                        | succ k1 =>
                            cases k1 with
                            | zero =>
                                -- Pos 1: vertex u.  IsCollider 1 on outer = s'.HeadAtTarget ∧ s₂.HeadAtSource = False (hNonColl).
                                exfalso
                                apply hNonColl
                                cases p_tail_inner_fixed with
                                | nil _ _ => exact ⟨h_coll.1, h_coll.2⟩
                                | cons _ _ _ => exact ⟨h_coll.1, h_coll.2⟩
                            | succ k2 =>
                                cases k2 with
                                | zero =>
                                    -- Pos 2: vertex mid'.  Substantive.
                                    have hvk_mid' : vk = mid' := by
                                      have h_vert2 :
                                          (Walk.cons u s'
                                              (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                            = some mid' := by
                                        show p_tail_inner_fixed.vertices[0]? = some mid'
                                        exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                                      rw [h_vert2] at hk_vert
                                      exact (Option.some.inj hk_vert).symm
                                    rw [hvk_mid']
                                    -- Cases on p_tail_inner to derive transport via h_fst_pres_inner.
                                    cases h_pti : p_tail_inner with
                                    | nil v_pti hv_pti =>
                                        have h_pti_len_zero : p_tail_inner.length = 0 := by
                                          rw [h_pti]; rfl
                                        have h_pf_inner_len_zero :
                                            p_tail_inner_fixed.length = 0 :=
                                          h_nil_pres_inner.mp h_pti_len_zero
                                        cases p_tail_inner_fixed with
                                        | nil _ _ => exact h_coll.elim
                                        | cons _ _ _ =>
                                            simp [Walk.length] at h_pf_inner_len_zero
                                    | cons mid_x s_first p_inner_inner =>
                                        obtain ⟨p_inner_inner_fixed, h_pf_inner_eq⟩ :=
                                          h_fst_pres_inner s_first p_inner_inner h_pti
                                        rw [h_pf_inner_eq] at h_coll
                                        have h_input_coll :
                                            (Walk.cons u s'
                                                (Walk.cons mid' s₂ p_tail_inner)).IsCollider 2 := by
                                          rw [h_pti]
                                          cases s' <;> cases s₂ <;> cases s_first <;>
                                            first
                                            | exact h_coll
                                            | exact h_coll.elim
                                            | exact ⟨h_coll.1, h_coll.2⟩
                                        have h_vert_mid' :
                                            (Walk.cons u s'
                                                (Walk.cons mid' s₂ p_tail_inner)).vertices[2]?
                                              = some mid' := by
                                          show p_tail_inner.vertices[0]? = some mid'
                                          exact Walk.vertices_zero_eq_source' p_tail_inner
                                        exact h_sigma_open.1 2 mid' h_vert_mid' h_input_coll
                                | succ k3 =>
                                    -- Pos k3+3: shift to p_tail_inner_fixed σ-open at k3+1.
                                    have hvk_tail :
                                        p_tail_inner_fixed.vertices[k3 + 1]? = some vk :=
                                      hk_vert
                                    have h_tail_coll :
                                        p_tail_inner_fixed.IsCollider (k3 + 1) := by
                                      cases p_tail_inner_fixed with
                                      | nil _ _ => exact h_coll.elim
                                      | cons _ _ _ => cases s' <;> cases s₂ <;> exact h_coll
                                    exact h_so_pf_inner.1 (k3 + 1) vk hvk_tail h_tail_coll
                      · -- Blockable clause.
                        intro k vk hk_vert h_blk h_pos
                        cases k with
                        | zero => omega
                        | succ k1 =>
                            cases k1 with
                            | zero =>
                                -- Pos 1: vertex u.  Need u ∉ C.  Given hu_notC.
                                have hvk_u : vk = u := by
                                  have h_vert1 :
                                      (Walk.cons u s'
                                          (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[1]?
                                        = some u := rfl
                                  rw [h_vert1] at hk_vert
                                  exact (Option.some.inj hk_vert).symm
                                rw [hvk_u]
                                exact hu_notC
                            | succ k2 =>
                                cases k2 with
                                | zero =>
                                    -- Pos 2: vertex mid'.  Substantive.
                                    -- Don't rewrite vk → mid' before the cases (mid' gets
                                    -- substituted away in the nil branch of p_tail_inner).
                                    -- Cases on p_tail_inner first.
                                    cases h_pti : p_tail_inner with
                                    | nil v_pti hv_pti =>
                                        have h_pti_len_zero : p_tail_inner.length = 0 := by
                                          rw [h_pti]; rfl
                                        have h_pf_inner_len_zero :
                                            p_tail_inner_fixed.length = 0 :=
                                          h_nil_pres_inner.mp h_pti_len_zero
                                        cases p_tail_inner_fixed with
                                        | nil _ _ =>
                                            -- Both walks are cons-cons-nil with same vertex;
                                            -- transport via h_sigma_open.2 with vk directly.
                                            refine h_sigma_open.2 2 vk ?_ ?_ h_pos
                                            · rw [h_pti]; exact hk_vert
                                            · rw [h_pti]; exact h_blk
                                        | cons _ _ _ =>
                                            simp [Walk.length] at h_pf_inner_len_zero
                                    | cons mid_x s_first p_inner_inner =>
                                        have hvk_mid' : vk = mid' := by
                                          have h_vert2 :
                                              (Walk.cons u s'
                                                  (Walk.cons mid' s₂ p_tail_inner_fixed)).vertices[2]?
                                                = some mid' := by
                                            show p_tail_inner_fixed.vertices[0]? = some mid'
                                            exact Walk.vertices_zero_eq_source' p_tail_inner_fixed
                                          rw [h_vert2] at hk_vert
                                          exact (Option.some.inj hk_vert).symm
                                        rw [hvk_mid']
                                        obtain ⟨p_inner_inner_fixed, h_pf_inner_eq⟩ :=
                                          h_fst_pres_inner s_first p_inner_inner h_pti
                                        rw [h_pf_inner_eq] at h_blk
                                        have h_vert_mid' :
                                            (Walk.cons u s'
                                                (Walk.cons mid' s₂ p_tail_inner)).vertices[2]?
                                              = some mid' := by
                                          show p_tail_inner.vertices[0]? = some mid'
                                          exact Walk.vertices_zero_eq_source' p_tail_inner
                                        have h_input_blk :
                                            (Walk.cons u s'
                                                (Walk.cons mid' s₂ p_tail_inner)).IsBlockableNonCollider 2 := by
                                          rw [h_pti]
                                          obtain ⟨h_nc_outer, h_disj_outer⟩ := h_blk
                                          refine ⟨?_, ?_⟩
                                          · refine ⟨?_, ?_⟩
                                            · show 2 ≤
                                                  (Walk.cons mid_x s_first p_inner_inner).length + 2
                                              simp [Walk.length]
                                            · intro h_coll_input
                                              apply h_nc_outer.2
                                              cases s' <;> cases s₂ <;> cases s_first <;>
                                                first
                                                | exact h_coll_input
                                                | exact h_coll_input.elim
                                                | exact ⟨h_coll_input.1, h_coll_input.2⟩
                                          · rcases h_disj_outer with h_eq0 | h_eq_len | hHBLS | hHBRS
                                            · exact absurd h_eq0 (by omega)
                                            · exfalso
                                              have h_len_eq :
                                                  (Walk.cons u s' (Walk.cons mid' s₂
                                                      (Walk.cons mid_x s_first p_inner_inner_fixed))).length
                                                    = p_inner_inner_fixed.length + 3 := rfl
                                              rw [h_len_eq] at h_eq_len
                                              omega
                                            · right; right; left
                                              -- HBLS 2 on outer reduces to inner cons's HBLS 1,
                                              -- which depends on s₂.  Unfold and dispatch on s₂.
                                              simp only [Walk.HasBlockingLeftSlot] at hHBLS ⊢
                                              cases s' <;> cases s₂ <;>
                                                first
                                                | exact hHBLS
                                                | exact hHBLS.elim
                                            · right; right; right
                                              -- HBRS 2 on outer reduces to HBRS 0 on the
                                              -- inner-inner cons (cons mid_x s_first ...),
                                              -- which depends on s_first.
                                              simp only [Walk.HasBlockingRightSlot] at hHBRS ⊢
                                              cases s' <;> cases s₂ <;> cases s_first <;>
                                                first
                                                | exact hHBRS
                                                | exact hHBRS.elim
                                        exact h_sigma_open.2 2 mid' h_vert_mid' h_input_blk h_pos
                                | succ k3 =>
                                    -- Pos k3+3: shift.
                                    have hvk_tail :
                                        p_tail_inner_fixed.vertices[k3 + 1]? = some vk :=
                                      hk_vert
                                    have h_tail_blk :
                                        p_tail_inner_fixed.IsBlockableNonCollider (k3 + 1) := by
                                      obtain ⟨h_nc, h_disj⟩ := h_blk
                                      refine ⟨?_, ?_⟩
                                      · refine ⟨?_, ?_⟩
                                        · have h1 := h_nc.1
                                          have h_len_eq :
                                              (Walk.cons u s'
                                                  (Walk.cons mid' s₂ p_tail_inner_fixed)).length
                                                = p_tail_inner_fixed.length + 2 := rfl
                                          omega
                                        · intro h_coll_tail
                                          apply h_nc.2
                                          cases p_tail_inner_fixed with
                                          | nil _ _ =>
                                              exact absurd h_coll_tail
                                                (by cases k3 <;> exact id)
                                          | cons _ _ _ =>
                                              cases s' <;> cases s₂ <;> exact h_coll_tail
                                      · rcases h_disj with h_eq0 | h_eq_len | hHBLS | hHBRS
                                        · omega
                                        · right; left
                                          have h_len_eq :
                                              (Walk.cons u s'
                                                  (Walk.cons mid' s₂ p_tail_inner_fixed)).length
                                                = p_tail_inner_fixed.length + 2 := rfl
                                          omega
                                        · right; right; left
                                          cases p_tail_inner_fixed with
                                          | nil _ _ =>
                                              simp only [Walk.HasBlockingLeftSlot] at hHBLS
                                          | cons _ _ _ =>
                                              cases s' <;> cases s₂ <;> exact hHBLS
                                        · right; right; right
                                          cases p_tail_inner_fixed with
                                          | nil _ _ =>
                                              simp only [Walk.HasBlockingRightSlot] at hHBRS
                                          | cons _ _ _ =>
                                              cases s' <;> cases s₂ <;> exact hHBRS
                                    exact h_so_pf_inner.2 (k3 + 1) vk hvk_tail h_tail_blk
                                      (by omega)
                    · -- Nil-length pres iff: both sides cons-cons (length ≥ 2).
                      constructor
                      · intro h_p_len0
                        exfalso
                        have h_len_eq :
                            (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner)).length
                              = p_tail_inner.length + 2 := rfl
                        omega
                      · intro h_pf_len0
                        exfalso
                        have h_len_eq :
                            (Walk.cons u s' (Walk.cons mid' s₂ p_tail_inner_fixed)).length
                              = p_tail_inner_fixed.length + 2 := rfl
                        omega
                    · -- First-step preservation: p = cons u s' _ → p_fixed = cons u s' _.
                      intro mid'' s'' p_tail'' h_eq
                      cases h_eq
                      exact ⟨Walk.cons mid' s₂ p_tail_inner_fixed, rfl⟩
                    · -- p'_fixed via IsLift.cons_two_edge + NPL.two_edge_npl.
                      refine ⟨Walk.cons mid' s_marg p_tail_inner_lift, ?_, ?_⟩
                      · exact IsLift.cons_two_edge s_marg p_tail_inner_lift s' s₂
                          p_tail_inner_fixed hSrc.symm hTgt.symm hNonColl h_lift_inner
                      · refine NoProblematicLift.two_edge_npl s_marg p_tail_inner_lift
                          s' s₂ p_tail_inner_fixed ?_ ?_ h_npl_inner
                        · -- h_fwd: substantive for (fw,fw) only.
                          intro h_ant ha_C h_uSc
                          -- h_ant : ¬ s_marg.HeadAtSource ∧ s_marg.HeadAtTarget.
                          -- For s' = .backwardE/.bidir: s_marg.HeadAtSource = True (via hSrc), h_ant.1 absurd.
                          -- For s' = .forwardE: handle by_cases on (s', s₂) = (fw,fw).
                          cases s' with
                          | forwardE _ =>
                              cases s₂ with
                              | forwardE _ =>
                                  -- (fw, fw): substantive.  by_cases problematic.
                                  by_cases h_problematic :
                                      a ∈ C ∧ u ∈ G.Sc a ∧ mid' ∉ (G.marginalize {u} hu).Sc a
                                  · -- Problematic: derive False via h_use_surgery_fwfw=False.
                                    exact absurd
                                      ⟨⟨_, _, rfl, rfl⟩,
                                        h_problematic.1, h_problematic.2.1, h_problematic.2.2⟩
                                      h_use_surgery_fwfw
                                  · -- Non-problematic: derive mid' ∈ marg.Sc a from negation.
                                    push_neg at h_problematic
                                    exact h_problematic ha_C h_uSc
                              | backwardE _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                              | bidir _ => exact (hNonColl ⟨trivial, trivial⟩).elim
                          | backwardE _ =>
                              exact (h_ant.1 (hSrc.mpr trivial)).elim
                          | bidir _ =>
                              exact (h_ant.1 (hSrc.mpr trivial)).elim
                        · -- h_bwd: substantive for (bw,bw) only.
                          intro h_ant hm_C h_uSc
                          cases s' with
                          | backwardE _ =>
                              cases s₂ with
                              | forwardE _ =>
                                  exact (h_ant.2 (hTgt.mpr trivial)).elim
                              | backwardE _ =>
                                  -- (bw, bw): substantive.  by_cases problematic.
                                  by_cases h_problematic :
                                      mid' ∈ C ∧ u ∈ G.Sc mid' ∧ a ∉ (G.marginalize {u} hu).Sc mid'
                                  · -- Problematic: derive False via h_use_surgery_bwbw=False.
                                    exact absurd
                                      ⟨⟨_, _, rfl, rfl⟩,
                                        h_problematic.1, h_problematic.2.1, h_problematic.2.2⟩
                                      h_use_surgery_bwbw
                                  · -- Non-problematic.
                                    push_neg at h_problematic
                                    exact h_problematic hm_C h_uSc
                              | bidir _ =>
                                  exact (h_ant.2 (hTgt.mpr trivial)).elim
                          | forwardE _ =>
                              -- s' = .forwardE → s'.HeadAtSource = False → via hSrc,
                              -- s_marg.HeadAtSource = False, contradicting h_ant.1.
                              exact (hSrc.mp h_ant.1).elim
                          | bidir _ =>
                              -- (bidir, ?) dispatch on s₂.
                              cases s₂ with
                              | forwardE _ =>
                                  -- (bidir, forwardE): s_marg.HeadAtTarget = True,
                                  -- contradicting h_ant.2.
                                  exact (h_ant.2 (hTgt.mpr trivial)).elim
                              | backwardE _ =>
                                  -- (bidir, backwardE): collider at u, hNonColl.
                                  exact (hNonColl ⟨trivial, trivial⟩).elim
                              | bidir _ =>
                                  -- (bidir, bidir): collider at u, hNonColl.
                                  exact (hNonColl ⟨trivial, trivial⟩).elim
        · -- Case mid ≠ u: 1-edge G-cell, no surgery.
          have h_tail_lt : p_tail.length < n := by
            have h_len_eq :
                (Walk.cons mid s' p_tail).length = p_tail.length + 1 := rfl
            omega
          have h_nc_tail :
              ∀ k, p_tail.vertices[k]? = some u →
                p_tail.IsNonCollider k := by
            intro k hk_tail
            have hk_p :
                (Walk.cons mid s' p_tail).vertices[k+1]? = some u := hk_tail
            have h_nc_kp1 := h_nc (k+1) hk_p
            refine ⟨?_, ?_⟩
            · have h1 := h_nc_kp1.1
              have h_len_eq :
                  (Walk.cons mid s' p_tail).length = p_tail.length + 1 := rfl
              omega
            · intro h_coll_tail
              apply h_nc_kp1.2
              cases p_tail with
              | nil _ _ =>
                  exact absurd h_coll_tail (by cases k <;> exact id)
              | cons mid_t s_t p_t =>
                  cases k with
                  | zero =>
                      rw [isCollider_cons_zero_eq_false s_t p_t] at h_coll_tail
                      exact h_coll_tail.elim
                  | succ k' => cases s' <;> exact h_coll_tail
          have h_nocons_tail :
              ∀ k, p_tail.vertices[k]? = some u →
                p_tail.vertices[k+1]? ≠ some u := by
            intro k hk h_kp1
            exact h_nocons (k+1) hk h_kp1
          have h_nobif_tail : NoBifurcationSideTrip p_tail u := by
            intro i v h_i h_ip1 h_ip2 h_bif
            apply h_nobif (i+1) v h_i h_ip1 h_ip2
            cases p_tail with
            | nil _ _ => exact h_bif.elim
            | cons _ _ _ => cases s' <;> exact h_bif
          have h_sigma_open_tail : IsSigmaOpenAtInterior p_tail C hC_G :=
            sigma_open_interior_cons_tail s' p_tail C hC_G h_sigma_open
          obtain ⟨p_tail_fixed, h_nc_pf, h_nocons_pf, h_nobif_pf, h_so_pf,
                  h_nil_pres, h_fst_pres, p_tail_lift, h_lift_tail, h_npl_tail⟩ :=
            ih p_tail.length h_tail_lt p_tail rfl h_mid hb h_nc_tail
              h_nocons_tail h_nobif_tail h_sigma_open_tail
          obtain ⟨s_marg, hSrc, hTgt⟩ :=
            walkstep_lift_one_edge u hu ha h_mid s'
          refine ⟨Walk.cons mid s' p_tail_fixed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- u-non-collider on cons mid s' p_tail_fixed.
            intro k hk_vert
            cases k with
            | zero =>
                exfalso
                have h_vert0 :
                    (Walk.cons mid s' p_tail_fixed).vertices[0]? = some a :=
                  Walk.vertices_zero_eq_source' _
                rw [h_vert0] at hk_vert
                exact ha (Option.some.inj hk_vert)
            | succ k' =>
                have hk_pf : p_tail_fixed.vertices[k']? = some u := hk_vert
                cases k' with
                | zero =>
                    -- vertex at outer pos 1 = mid = u would contradict h_mid.
                    have h_vert0_pf :
                        p_tail_fixed.vertices[0]? = some mid :=
                      Walk.vertices_zero_eq_source' _
                    rw [h_vert0_pf] at hk_pf
                    exfalso
                    exact h_mid (Option.some.inj hk_pf)
                | succ k'' =>
                    have h_nc_pf_k := h_nc_pf (k''+1) hk_pf
                    refine ⟨?_, ?_⟩
                    · have h_k_le : k''+1 ≤ p_tail_fixed.length := h_nc_pf_k.1
                      have h_len_eq :
                          (Walk.cons mid s' p_tail_fixed).length
                            = p_tail_fixed.length + 1 := rfl
                      omega
                    · intro h_coll_outer
                      apply h_nc_pf_k.2
                      cases p_tail_fixed with
                      | nil _ _ =>
                          exact absurd hk_pf
                            (by simp [Walk.vertices])
                      | cons _ _ _ =>
                          cases s' <;> exact h_coll_outer
          · -- no-consecutive-u on cons mid s' p_tail_fixed.
            intro k hk_vert
            cases k with
            | zero =>
                exfalso
                have h_vert0 :
                    (Walk.cons mid s' p_tail_fixed).vertices[0]? = some a :=
                  Walk.vertices_zero_eq_source' _
                rw [h_vert0] at hk_vert
                exact ha (Option.some.inj hk_vert)
            | succ k' =>
                have hk_pf : p_tail_fixed.vertices[k']? = some u := hk_vert
                intro h_kp1
                have h_kp1_tail :
                    p_tail_fixed.vertices[k'+1]? = some u := h_kp1
                exact h_nocons_pf k' hk_pf h_kp1_tail
          · -- NoBifurcationSideTrip on cons mid s' p_tail_fixed.
            intro i v h_i h_ip1 h_ip2 h_bif
            cases i with
            | zero =>
                -- vertices[1] = some mid; h_ip1 says mid = u, contra h_mid.
                exfalso
                have h_vert1 :
                    (Walk.cons mid s' p_tail_fixed).vertices[1]? = some mid := by
                  show p_tail_fixed.vertices[0]? = some mid
                  exact Walk.vertices_zero_eq_source' p_tail_fixed
                rw [h_vert1] at h_ip1
                exact h_mid (Option.some.inj h_ip1)
            | succ i' =>
                apply h_nobif_pf i' v h_i h_ip1 h_ip2
                cases p_tail_fixed with
                | nil _ _ => exact h_bif.elim
                | cons _ _ _ => cases s' <;> exact h_bif
          · -- IsSigmaOpenAtInterior on cons mid s' p_tail_fixed.
            refine ⟨?_, ?_⟩
            · -- Collider clause.
              intro k vk hk_vert h_coll
              cases k with
              | zero =>
                  cases p_tail_fixed with
                  | nil _ _ => exact h_coll.elim
                  | cons _ _ _ =>
                      rw [isCollider_cons_zero_eq_false s' _] at h_coll
                      exact h_coll.elim
              | succ k1 =>
                  cases k1 with
                  | zero =>
                      -- k = 1: substantive.  Cases on p_tail (nil branch
                      -- substitutes mid; cons branch preserves it).
                      cases h_pt : p_tail with
                      | nil v_pt hv_pt =>
                          -- mid substituted; derive p_tail_fixed = nil via iff,
                          -- then h_coll becomes False.  No mention of mid.
                          have h_pt_len_zero : p_tail.length = 0 := by rw [h_pt]; rfl
                          have h_pf_len_zero : p_tail_fixed.length = 0 :=
                            h_nil_pres.mp h_pt_len_zero
                          cases p_tail_fixed with
                          | nil _ _ => exact h_coll.elim
                          | cons _ _ _ =>
                              simp [Walk.length] at h_pf_len_zero
                      | cons mid_x s_first p_inner =>
                          -- mid preserved.
                          have hvk_mid : vk = mid := by
                            have h_vert1 :
                                (Walk.cons mid s' p_tail_fixed).vertices[1]? = some mid := by
                              show p_tail_fixed.vertices[0]? = some mid
                              exact Walk.vertices_zero_eq_source' p_tail_fixed
                            rw [h_vert1] at hk_vert
                            exact (Option.some.inj hk_vert).symm
                          rw [hvk_mid]
                          obtain ⟨p_inner_fixed, h_pf_eq⟩ :=
                            h_fst_pres s_first p_inner h_pt
                          rw [h_pf_eq] at h_coll
                          have h_input_coll :
                              (Walk.cons mid s' p_tail).IsCollider 1 := by
                            rw [h_pt]
                            cases s' <;> cases s_first <;>
                              first
                              | exact h_coll
                              | exact h_coll.elim
                              | exact ⟨h_coll.1, h_coll.2⟩
                          have h_vert_mid :
                              (Walk.cons mid s' p_tail).vertices[1]? = some mid := by
                            show p_tail.vertices[0]? = some mid
                            exact Walk.vertices_zero_eq_source' p_tail
                          exact h_sigma_open.1 1 mid h_vert_mid h_input_coll
                  | succ k2 =>
                      have hvk_tail :
                          p_tail_fixed.vertices[k2 + 1]? = some vk := hk_vert
                      have h_tail_coll : p_tail_fixed.IsCollider (k2 + 1) := by
                        cases p_tail_fixed with
                        | nil _ _ => exact h_coll.elim
                        | cons _ _ _ => cases s' <;> exact h_coll
                      exact h_so_pf.1 (k2 + 1) vk hvk_tail h_tail_coll
            · -- Blockable clause.
              intro k vk hk_vert h_blk h_pos
              cases k with
              | zero => omega
              | succ k1 =>
                  cases k1 with
                  | zero =>
                      -- k = 1: substantive.  Cases on p_tail.
                      cases h_pt : p_tail with
                      | nil v_pt hv_pt =>
                          -- mid substituted via Walk.nil's index unification.
                          -- Both p_tail and p_tail_fixed are nil (same vertex by
                          -- iff + length=0 → nil); inputs and outputs walk shapes
                          -- coincide.  Feed h_blk through h_sigma_open after rw.
                          have h_pt_len_zero : p_tail.length = 0 := by rw [h_pt]; rfl
                          have h_pf_len_zero : p_tail_fixed.length = 0 :=
                            h_nil_pres.mp h_pt_len_zero
                          cases p_tail_fixed with
                          | nil _ _ =>
                              refine h_sigma_open.2 1 vk ?_ ?_ h_pos
                              · rw [h_pt]; exact hk_vert
                              · rw [h_pt]; exact h_blk
                          | cons _ _ _ =>
                              simp [Walk.length] at h_pf_len_zero
                      | cons mid_x s_first p_inner =>
                          -- mid preserved.
                          have hvk_mid : vk = mid := by
                            have h_vert1 :
                                (Walk.cons mid s' p_tail_fixed).vertices[1]? = some mid := by
                              show p_tail_fixed.vertices[0]? = some mid
                              exact Walk.vertices_zero_eq_source' p_tail_fixed
                            rw [h_vert1] at hk_vert
                            exact (Option.some.inj hk_vert).symm
                          rw [hvk_mid]
                          obtain ⟨p_inner_fixed, h_pf_eq⟩ :=
                            h_fst_pres s_first p_inner h_pt
                          rw [h_pf_eq] at h_blk
                          have h_vert_mid_p :
                              (Walk.cons mid s' p_tail).vertices[1]? = some mid := by
                            show p_tail.vertices[0]? = some mid
                            exact Walk.vertices_zero_eq_source' p_tail
                          have h_input_blk :
                              (Walk.cons mid s' p_tail).IsBlockableNonCollider 1 := by
                            rw [h_pt]
                            obtain ⟨h_nc_outer, h_disj_outer⟩ := h_blk
                            refine ⟨?_, ?_⟩
                            · refine ⟨?_, ?_⟩
                              · show 1 ≤ (Walk.cons mid_x s_first p_inner).length + 1
                                simp [Walk.length]
                              · intro h_coll_input
                                apply h_nc_outer.2
                                cases s' <;> cases s_first <;>
                                  first
                                  | exact h_coll_input
                                  | exact h_coll_input.elim
                                  | exact ⟨h_coll_input.1, h_coll_input.2⟩
                            · rcases h_disj_outer with h_eq0 | h_eq_len | hHBLS | hHBRS
                              · exact absurd h_eq0 (by omega)
                              · exfalso
                                have h_len_eq :
                                    (Walk.cons mid s' (Walk.cons mid_x s_first p_inner_fixed)).length
                                      = p_inner_fixed.length + 2 := rfl
                                rw [h_len_eq] at h_eq_len
                                omega
                              · right; right; left
                                cases s' with
                                | forwardE _ => cases hHBLS
                                | backwardE _ => exact hHBLS
                                | bidir _ => cases hHBLS
                              · right; right; right
                                -- HBRS 1 reduces to (inner walk).HBRS 0, then to the
                                -- s_first-specific value.  Unfold both sides and exact.
                                simp only [Walk.HasBlockingRightSlot] at hHBRS ⊢
                                cases s_first with
                                | forwardE _ => exact hHBRS
                                | backwardE _ => exact hHBRS.elim
                                | bidir _ => exact hHBRS.elim
                          exact h_sigma_open.2 1 mid h_vert_mid_p h_input_blk h_pos
                  | succ k2 =>
                      have hvk_tail :
                          p_tail_fixed.vertices[k2 + 1]? = some vk := hk_vert
                      have h_tail_blk :
                          p_tail_fixed.IsBlockableNonCollider (k2 + 1) := by
                        obtain ⟨h_nc, h_disj⟩ := h_blk
                        refine ⟨?_, ?_⟩
                        · refine ⟨?_, ?_⟩
                          · have h1 := h_nc.1
                            have h_len_eq :
                                (Walk.cons mid s' p_tail_fixed).length
                                  = p_tail_fixed.length + 1 := rfl
                            omega
                          · intro h_coll_tail
                            apply h_nc.2
                            cases p_tail_fixed with
                            | nil _ _ =>
                                exact absurd h_coll_tail (by cases k2 <;> exact id)
                            | cons _ _ _ => cases s' <;> exact h_coll_tail
                        · rcases h_disj with h_eq0 | h_eq_len | hHBLS | hHBRS
                          · omega
                          · right; left
                            have h_len_eq :
                                (Walk.cons mid s' p_tail_fixed).length
                                  = p_tail_fixed.length + 1 := rfl
                            omega
                          · right; right; left
                            cases p_tail_fixed with
                            | nil _ _ =>
                                simp only [Walk.HasBlockingLeftSlot] at hHBLS
                            | cons _ _ _ => cases s' <;> exact hHBLS
                          · right; right; right
                            cases p_tail_fixed with
                            | nil _ _ =>
                                simp only [Walk.HasBlockingRightSlot] at hHBRS
                            | cons _ _ _ => cases s' <;> exact hHBRS
                      exact h_so_pf.2 (k2 + 1) vk hvk_tail h_tail_blk (by omega)
          · -- Nil-length pres iff: both sides are cons (length ≥ 1).
            constructor
            · intro h_p_len0
              exfalso
              have h_len_eq :
                  (Walk.cons mid s' p_tail).length = p_tail.length + 1 := rfl
              omega
            · intro h_pf_len0
              exfalso
              have h_len_eq :
                  (Walk.cons mid s' p_tail_fixed).length
                    = p_tail_fixed.length + 1 := rfl
              omega
          · -- First-step preservation.
            intro mid'' s'' p_tail'' h_eq
            cases h_eq
            exact ⟨p_tail_fixed, rfl⟩
          · -- p'_fixed: build via IsLift.cons_one_edge + NPL.one_edge_npl.
            refine ⟨Walk.cons mid s_marg p_tail_lift, ?_, ?_⟩
            · exact IsLift.cons_one_edge s_marg p_tail_lift s' p_tail_fixed
                hSrc.symm hTgt.symm h_lift_tail
            · exact NoProblematicLift.one_edge_npl s_marg p_tail_lift s' p_tail_fixed
                h_npl_tail

-- ## ref: claim_3_25 (Subtask 11) — (1) ⟹ (2) one-node assembly.
--
-- The G-side `iσ`-separation transports forward to marg-side `iσ`-
-- separation for the one-node case `D = {u}` with `u ∉ A ∪ B ∪ C`.
-- Argued by contrapositive: a marg-side σ-open walk from `A` to
-- `J ∪ B` lifts to a G-side σ-open walk between the same
-- endpoints (via Subtask 6e's `sigma_open_lift_marg_one`),
-- contradicting the G-side separation hypothesis.
--
-- This is the forward direction analogue of
-- `iSigmaSeparation_marginalize_one_mpr` below.  It is shorter
-- because the forward direction does not need the
-- claim_3_23 strengthening or the surgery chain — the marg-side
-- σ-open walk lifts directly to a G-side σ-open walk via the
-- `IsLift`-based machinery delivered in Subtask 6e.  Endpoint
-- transport: `b ∈ (G.marginalize {u} hu).J ∪ B` reduces
-- definitionally to `b ∈ G.J ∪ B` (because
-- `(G.marginalize {u} hu).J = G.J` per `def_3_14`'s
-- `where`-clause), so the G-side separation hypothesis applies
-- with the same `b ∈ G.J ∪ B` witness.
private lemma iSigmaSeparation_marginalize_one_mp
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (A B C : Set Node)
    (hA : A ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hB : B ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hu_disj : Disjoint (↑({u} : Finset Node) : Set Node) (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C hA hB hC →
    (G.marginalize {u} hu).IsISigmaSeparated A B C
        (G.subset_marginalize_carrier_of_disjoint A {u} hu hA
          (hu_disj.mono_right
            (Set.subset_union_left.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint B {u} hu hB
          (hu_disj.mono_right
            (Set.subset_union_right.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint C {u} hu hC
          (hu_disj.mono_right Set.subset_union_right)) := by
  intro h_G_sep a b π' ha hb
  -- Goal: π'.IsSigmaBlockedGiven C hC_marg.  Argue by contradiction.
  by_contra h_not_blk
  -- Step 1: ¬ blocked → σ-open (De Morgan on the two disjuncts).
  have hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                     ↑(G.marginalize {u} hu).V :=
    G.subset_marginalize_carrier_of_disjoint C {u} hu hC
      (hu_disj.mono_right Set.subset_union_right)
  have h_open : π'.IsSigmaOpenGiven C hC_marg := by
    refine ⟨?_, ?_⟩
    · intro k vk hvk hcol
      by_contra h_nin
      exact h_not_blk (Or.inl ⟨k, vk, hvk, hcol, h_nin⟩)
    · intro k vk hvk hbnc
      by_contra h_in
      exact h_not_blk (Or.inr ⟨k, vk, hvk, hbnc, h_in⟩)
  -- Extract per-set non-membership facts from hu_disj.
  have hu_mem_sing : (u : Node) ∈ (↑({u} : Finset Node) : Set Node) := by
    simp
  have hu_notABC : u ∉ A ∪ B ∪ C :=
    Set.disjoint_left.mp hu_disj hu_mem_sing
  have hu_notA : u ∉ A := fun h => hu_notABC (Or.inl (Or.inl h))
  have hu_notB : u ∉ B := fun h => hu_notABC (Or.inl (Or.inr h))
  have hu_notC : u ∉ C := fun h => hu_notABC (Or.inr h)
  have ha_ne_u : a ≠ u := fun h_eq => hu_notA (h_eq ▸ ha)
  have hb_ne_u : b ≠ u := by
    intro h_eq
    rcases hb with hbJ | hbB
    · -- u ∈ J ∩ V = ∅.
      have hu_V : u ∈ G.V := hu (Finset.mem_singleton.mpr rfl)
      have hu_J : u ∈ G.J := h_eq ▸ hbJ
      exact (Finset.disjoint_left.mp G.hJV_disj hu_J) hu_V
    · exact hu_notB (h_eq ▸ hbB)
  -- Singleton-vs-C disjointness for the lift.
  have hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C :=
    hu_disj.mono_right Set.subset_union_right
  -- Lift the marg σ-open walk to a G σ-open walk (Subtask 6e).
  obtain ⟨p, hp_open⟩ :=
    sigma_open_lift_marg_one G u hu C hu_notC hC_disj hC hC_marg
      π' ha_ne_u hb_ne_u h_open
  -- Apply G-side separation: hb reads as `b ∈ G.J ∪ B` by definitional
  -- reduction of `(G.marginalize {u} hu).J = G.J`.
  have hb_G : b ∈ (↑G.J : Set Node) ∪ B := hb
  have hp_blocked : p.IsSigmaBlockedGiven C hC := h_G_sep p ha hb_G
  rcases hp_blocked with ⟨k, vk, hvk, hcol, hnin⟩ | ⟨k, vk, hvk, hbnc, hin⟩
  · exact hnin (hp_open.1 k vk hvk hcol)
  · exact (hp_open.2 k vk hvk hbnc) hin

-- ## ref: claim_3_25 (Subtask 10) — (2) ⟹ (1) one-node assembly.
--
-- The marg-side `iσ`-separation transports back to G-side `iσ`-
-- separation for the one-node case `D = {u}` with `u ∉ A ∪ B ∪ C`.
-- Argued by contrapositive: a `G`-side σ-open walk from `A` to
-- `J ∪ B` lifts to a `G^{∖u}`-side σ-open walk between the same
-- endpoints, contradicting the marg-side separation.
--
-- ## Proof skeleton
--
-- 1. Convert `¬ IsSigmaBlockedGiven` to `IsSigmaOpenGiven`
--    (direct De Morgan via the two existential disjuncts).
-- 2. Apply `sigma_open_paths_walks` (claim_3_23, item~3 direction)
--    to strengthen colliders to `∈ C` (not merely `∈ AncSet C`).
-- 3. Apply `collapse_u_self_loops` (Subtask 7a) to remove
--    consecutive-`u` runs.
-- 4. Derive: `u` is a non-collider at every appearance position
--    (any collider at `u` would force `u ∈ C` via step 2, but
--    `u ∉ C`).
-- 5. Apply `elide_u_side_trip_bifurcations` (line 3096) to
--    eliminate residual bifurcation side-trips through `u`.
-- 6. Apply `exists_NPL_clean_lift_of_walk_G` (Subtask 9): get a
--    marg-side lift `π'_fixed` with `IsLift` and `NoProblematicLift`.
-- 7. Apply `sigma_open_interior_lift_reverse_via_isLift` (Subtask
--    8): transport interior σ-openness to the marg side.
-- 8. Apply `sigma_open_of_interior_of_source_notC` to reassemble
--    full σ-openness (source `a ∈ A`, `A ∩ C = ∅` gives `a ∉ C`).
-- 9. Contradict the marg-side separation hypothesis using the
--    lifted σ-open walk.
--
-- ## Design choice — single bundled `hu_disj`
--
-- The hypothesis bundles `Disjoint {u} (A ∪ B ∪ C)` rather than
-- three separate `u ∉ A`, `u ∉ B`, `u ∉ C` premises.  Matches the
-- main theorem's statement shape (which also bundles); the three
-- per-set non-membership facts are derived in-proof via
-- `Set.disjoint_left.mp` + `Set.mem_singleton_iff.mpr rfl` chains.
-- The `Disjoint`-shape also chains cleanly through the
-- `subset_marginalize_carrier_of_disjoint` slice consumed at the
-- conclusion's transported subset witnesses (matching the main
-- theorem's shape).
private lemma iSigmaSeparation_marginalize_one_mpr
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (A B C : Set Node)
    (hA : A ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hB : B ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hu_disj : Disjoint (↑({u} : Finset Node) : Set Node) (A ∪ B ∪ C)) :
    (G.marginalize {u} hu).IsISigmaSeparated A B C
        (G.subset_marginalize_carrier_of_disjoint A {u} hu hA
          (hu_disj.mono_right
            (Set.subset_union_left.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint B {u} hu hB
          (hu_disj.mono_right
            (Set.subset_union_right.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint C {u} hu hC
          (hu_disj.mono_right Set.subset_union_right)) →
    G.IsISigmaSeparated A B C hA hB hC := by
  intro h_marg_sep a b π ha hb
  -- Goal: π.IsSigmaBlockedGiven C hC.  Argue by contradiction.
  by_contra h_nb
  -- Step 1: ¬ blocked → σ-open (De Morgan on the two disjuncts).
  have h_open : π.IsSigmaOpenGiven C hC := by
    refine ⟨?_, ?_⟩
    · intro k vk hvk hcol
      by_contra h_nin
      exact h_nb (Or.inl ⟨k, vk, hvk, hcol, h_nin⟩)
    · intro k vk hvk hbnc
      by_contra h_in
      exact h_nb (Or.inr ⟨k, vk, hvk, hbnc, h_in⟩)
  -- Extract per-set non-membership facts from hu_disj.
  have hu_mem_sing : (u : Node) ∈ (↑({u} : Finset Node) : Set Node) := by
    simp
  have hu_notABC : u ∉ A ∪ B ∪ C :=
    Set.disjoint_left.mp hu_disj hu_mem_sing
  have hu_notA : u ∉ A := fun h => hu_notABC (Or.inl (Or.inl h))
  have hu_notB : u ∉ B := fun h => hu_notABC (Or.inl (Or.inr h))
  have hu_notC : u ∉ C := fun h => hu_notABC (Or.inr h)
  have ha_ne_u : a ≠ u := fun h_eq => hu_notA (h_eq ▸ ha)
  have hb_ne_u : b ≠ u := by
    intro h_eq
    rcases hb with hbJ | hbB
    · -- u ∈ J ∩ V = ∅.
      have hu_V : u ∈ G.V := hu (Finset.mem_singleton.mpr rfl)
      have hu_J : u ∈ G.J := h_eq ▸ hbJ
      exact (Finset.disjoint_left.mp G.hJV_disj hu_J) hu_V
    · -- u ∈ B contradicts hu_notB.
      exact hu_notB (h_eq ▸ hbB)
  -- Endpoint memberships for claim_3_23.
  have ha_GJV : a ∈ ((↑G.J : Set Node) ∪ ↑G.V) := hA ha
  have hb_GJV : b ∈ ((↑G.J : Set Node) ∪ ↑G.V) := by
    rcases hb with hbJ | hbB
    · exact Or.inl hbJ
    · exact hB hbB
  -- Step 2: get σ-open walk with all colliders in C via claim_3_23 (2 → 3).
  have h_tfae := sigma_open_paths_walks G C hC ha_GJV hb_GJV
  have h_ex_w : ∃ π' : Walk G a b, π'.IsSigmaOpenGiven C hC := ⟨π, h_open⟩
  obtain ⟨π_strong, h_open_strong, h_col_strong⟩ := (h_tfae.out 1 2).mp h_ex_w
  -- Step 3: collapse u-self-loops.
  obtain ⟨π_clean, h_open_clean, h_col_clean, h_no_cons_clean⟩ :=
    collapse_u_self_loops u C hC hu_notC π_strong h_open_strong h_col_strong
  -- Step 4: u-non-collider invariant from h_col_clean + hu_notC.
  have h_u_nc : ∀ k, π_clean.vertices[k]? = some u → π_clean.IsNonCollider k := by
    intro k hk
    refine ⟨?_, ?_⟩
    · -- k ≤ π_clean.length: derive from vertices[k]? = some u.
      by_contra h_lt
      push_neg at h_lt
      -- k > length means vertices[k]? = none (out of range).
      have h_v_len : π_clean.vertices.length = π_clean.length + 1 :=
        Walk.vertices_length π_clean
      have h_k_ge : k ≥ π_clean.vertices.length := by
        rw [h_v_len]; omega
      have h_none : π_clean.vertices[k]? = none :=
        List.getElem?_eq_none h_k_ge
      rw [h_none] at hk
      cases hk
    · -- ¬ IsCollider k via strengthened colliders.
      intro h_col
      exact hu_notC (h_col_clean k u hk h_col)
  -- Step 5: elide bifurcation side-trips through u.
  obtain ⟨π_NBS, h_u_nc_NBS, h_no_cons_NBS, h_no_bif_NBS, _h_col_NBS, h_interior_NBS⟩ :=
    elide_u_side_trip_bifurcations u C hC hu_notC π_clean ha_ne_u hb_ne_u
      h_u_nc h_no_cons_clean h_col_clean
      (sigma_open_to_interior π_clean C hC h_open_clean)
  -- Step 6: NPL-clean lift (Subtask 9).
  obtain ⟨_π_fixed, _h_u_nc_fixed, _h_no_cons_fixed, _h_no_bif_fixed,
      h_interior_fixed, π'_fixed, h_lift, h_npl⟩ :=
    exists_NPL_clean_lift_of_walk_G G u hu C hC hu_notC π_NBS ha_ne_u hb_ne_u
      h_u_nc_NBS h_no_cons_NBS h_no_bif_NBS h_interior_NBS
  -- Step 7: reverse interior σ-open transport (Subtask 8).
  have hC_disj : Disjoint (↑({u} : Finset Node) : Set Node) C :=
    hu_disj.mono_right Set.subset_union_right
  have hC_marg : C ⊆ (↑(G.marginalize {u} hu).J : Set Node) ∪
                     ↑(G.marginalize {u} hu).V :=
    G.subset_marginalize_carrier_of_disjoint C {u} hu hC hC_disj
  have h_interior_marg : IsSigmaOpenAtInterior π'_fixed C hC_marg :=
    sigma_open_interior_lift_reverse_via_isLift G u hu C hu_notC hC_disj hC hC_marg
      h_lift ha_ne_u hb_ne_u h_interior_fixed h_npl
  -- Step 8: full σ-open from interior + a ∉ C.
  have ha_notC : a ∉ C := by
    intro h_in
    -- Derive via π_clean's σ-open at position 0 (always a blockable non-collider).
    have h_v0 : π_clean.vertices[0]? = some a :=
      Walk.vertices_zero_eq_source' π_clean
    have h_blk_0 : π_clean.IsBlockableNonCollider 0 := by
      refine ⟨⟨Nat.zero_le _, ?_⟩, Or.inl rfl⟩
      intro h_coll
      cases π_clean with
      | nil _ _ => exact h_coll
      | cons _ _ tail =>
          cases tail with
          | nil _ _ => exact h_coll
          | cons _ _ _ => exact h_coll
    exact h_open_clean.2 0 a h_v0 h_blk_0 h_in
  have h_marg_open : π'_fixed.IsSigmaOpenGiven C hC_marg :=
    sigma_open_of_interior_of_source_notC π'_fixed C hC_marg h_interior_marg ha_notC
  -- Step 9: contradict h_marg_sep.
  have h_marg_blocked : π'_fixed.IsSigmaBlockedGiven C hC_marg :=
    h_marg_sep π'_fixed ha hb
  rcases h_marg_blocked with ⟨k, vk, hvk, hcol, hnin⟩ | ⟨k, vk, hvk, hbnc, hin⟩
  · exact hnin (h_marg_open.1 k vk hvk hcol)
  · exact (h_marg_open.2 k vk hvk hbnc) hin

-- ## ref: claim_3_25 (Subtask 11) — one-node iff combinator.
--
-- Bundles the forward direction `iSigmaSeparation_marginalize_one_mp`
-- and the backward direction `iSigmaSeparation_marginalize_one_mpr`
-- into a single iff for the one-node case `D = {u}` with
-- `u ∉ A ∪ B ∪ C`.  Consumed in the inductive step of the main
-- theorem `iSigmaSeparation_marginalize_iff` (below) to chain the
-- one-node iff against the IH applied to `G.marginalize {u} hu` and
-- `D.erase u`.
private lemma iSigmaSeparation_marginalize_one_iff
    (G : CDMG Node) (u : Node) (hu : ({u} : Finset Node) ⊆ G.V)
    (A B C : Set Node)
    (hA : A ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hB : B ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hu_disj : Disjoint (↑({u} : Finset Node) : Set Node) (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C hA hB hC ↔
      (G.marginalize {u} hu).IsISigmaSeparated A B C
        (G.subset_marginalize_carrier_of_disjoint A {u} hu hA
          (hu_disj.mono_right
            (Set.subset_union_left.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint B {u} hu hB
          (hu_disj.mono_right
            (Set.subset_union_right.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint C {u} hu hC
          (hu_disj.mono_right Set.subset_union_right)) :=
  ⟨iSigmaSeparation_marginalize_one_mp G u hu A B C hA hB hC hu_disj,
   iSigmaSeparation_marginalize_one_mpr G u hu A B C hA hB hC hu_disj⟩

-- ## ref: claim_3_25 — `iσ`-separation is stable under marginalization.
--
-- `iSigmaSeparation_marginalize_iff G A B C D hD_sub hA hB hC
-- hD_disj` is the LN's
-- `A ⊥^iσ_G B | C  ⟺  A ⊥^iσ_{G^{∖D}} B | C` under the standing
-- hypotheses `A, B, C ⊆ J ∪ V`, `D ⊆ V`, and
-- `D ∩ (A ∪ B ∪ C) = ∅`.
--
-- ## Design choice — iSigmaSeparation_marginalize_iff
--
-- *Math-level shape: "the same `iσ`-separation predicate, applied
--   to the same triple `(A, B, C)`, on two graphs".*  This is the
--   LN's content verbatim, and it dictates two structural Lean
--   choices: (i) all marginalization-specific work lives in the
--   *graph* slot (`G` vs `G.marginalize D hD_sub` — the LN's
--   `G^{∖D}`), and (ii) the `iσ`-separation predicate of `def_3_18`
--   is reused verbatim on both sides of the `Iff` — no
--   re-definition, no inlining of its walk-blocking content into
--   the conclusion, no parallel "marginalized version" of
--   `def_3_18`.  A bespoke `IsISigmaSeparated_OnMarginalized`
--   wrapping the marginalize step was considered and rejected: it
--   would duplicate `def_3_18`, and the LN itself treats `G^{∖D}`
--   as just another CDMG on which the *same* predicate is
--   evaluated (cf.\ the canonical tex's "Reading of the
--   equivalence" paragraph).
--
-- *Single `theorem`, single `Iff`, no multi-item split.*  The LN's
--   `\begin{Lem}` block bundles one biconditional with no sub-
--   bullets, so the Lean shape is one `theorem` with one `Iff`.
--   This deliberately contrasts with `claim_3_24`
--   (`SigmaSeparationEquivalences`), where the LN itself bullets
--   four sub-items `(1a), (1b), (2a), (2b)` and the Lean shape
--   splits into four stacked theorems — there, the multi-theorem
--   split is *LN-driven* (each downstream consumer cites a
--   different sub-item), not a stylistic default.  Here, the LN
--   has no sub-bullets and no separately quotable sub-claims, so
--   the single-`theorem` shape is the only LN-faithful shape; an
--   `And`-bundled variant carrying extra side properties (e.g.\
--   "and the per-walk evaluation also agrees") was considered and
--   rejected for the same reason.
--
-- *Asymmetric typing `A, B, C : Set Node` vs `D : Finset Node`.*
--   Mirrors the LN's asymmetric typing `A, B, C ⊆ J ∪ V` vs
--   `D ⊆ V`.  The math reason is that marginalization is only
--   defined when its target lies in the output-node set `V` (per
--   `def_3_14`), whereas `iσ`-separation admits arbitrary node-
--   subsets `⊆ J ∪ V` (per `def_3_18`); the asymmetry is not
--   stylistic.  The Lean-mechanical consequence is dictated by
--   upstream APIs: `def_3_14`'s `marginalize` takes
--   `(W : Finset Node) (hW : W ⊆ G.V)` (because `G.V` is itself a
--   `Finset Node` in `CDMG`), while `def_3_18`'s
--   `IsISigmaSeparated` takes `A B C : Set Node`.  Honouring both
--   APIs means `D : Finset Node` and `A B C : Set Node`, with the
--   `Finset → Set` coercion `↑D : Set Node` used only in the
--   disjointness premise where the two carriers must meet.  A
--   `D : Set Node` variant with an added `D.Finite` hypothesis was
--   considered and rejected: it would force a coercion at every
--   `marginalize` call site and would not match the LN's reading.
--
-- *Three transported well-typedness witnesses inlined into the
--   conclusion.*  The right-hand side of the `Iff` calls
--   `(G.marginalize D hD_sub).IsISigmaSeparated A B C _ _ _` where
--   the three holes are the transported subset hypotheses for
--   `A, B, C` against the `G^{∖D}` carrier.  Each is produced by a
--   call to the helper `subset_marginalize_carrier_of_disjoint`
--   with the matching disjointness slice (extracted from
--   `hD_disj : Disjoint (↑D) (A ∪ B ∪ C)` via `Disjoint.mono_right`
--   on the obvious `_ ⊆ A ∪ B ∪ C` subset proofs).  The math
--   reason for *inlining* (rather than promoting these to three
--   extra hypotheses `hA' : A ⊆ ↑G^{∖D}.J ∪ ↑G^{∖D}.V`, etc.) is
--   that the LN treats the well-typedness of `A, B, C` against the
--   marginalized carrier as a *derivable consequence* of the
--   disjointness premise together with `D ⊆ V` and the carrier
--   identity `(J ∪ V) ∖ D = J ∪ (V ∖ D)` (cf.\ the canonical tex's
--   "Well-typedness of $A$, $B$, $C$" paragraph).  Promoting them
--   to named hypotheses would over-constrain the call site by
--   forcing the caller to discharge an obligation the LN already
--   exhibits as derivable; inlining preserves the LN's reading and
--   keeps the well-typedness inside the statement so
--   `verify_equivalence` can read the LN's "$A, B, C$ are subsets
--   of $G^{∖D}$'s carrier" content off the type.
--
-- *`Disjoint (↑D : Set Node) (A ∪ B ∪ C)` for the LN's
--   `D ∩ (A ∪ B ∪ C) = ∅`.*  Propositionally equivalent via
--   `Set.disjoint_iff_inter_eq_empty`; `Disjoint`-on-`Set` is the
--   Mathlib-idiomatic phrasing, pairs cleanly with the
--   `Disjoint.mono_right` slicing used to extract the three
--   per-argument disjointness premises consumed by
--   `subset_marginalize_carrier_of_disjoint`, and is downstream-
--   API-stable in case the proof later needs to chain with other
--   `Disjoint`-shaped Mathlib lemmas.  A literal
--   `↑D ∩ (A ∪ B ∪ C) = ∅` rendering was considered and rejected:
--   it would need an explicit
--   `Set.disjoint_iff_inter_eq_empty` rewrite at every consumer
--   site that wanted the `Disjoint` shape Mathlib expects.
--
-- *Hypothesis names mirror Section 3.3 convention.*  `hA, hB, hC`
--   for the `G`-side subset hypotheses (matching `def_3_18`'s
--   binder names); `hD_sub` for the `marginalize`-precondition
--   `D ⊆ G.V`; `hD_disj` for the disjointness premise.  The
--   helper-derived transported subset proofs are inline term
--   expressions, not named binders, because they are uniquely
--   determined by `hA, hB, hC, hD_disj` (proof-irrelevance
--   guarantees uniqueness).
--
-- *Body: `:= by sorry`.*  Statement-only worker pass; the proof
--   is the next handoff to Manager B.  The proof strategy (sketch,
--   for the next worker): walks in `G` avoiding `D` are in
--   canonical bijection with walks in `G^{∖D}` (folding each
--   directed-walk-through-`D` slab into a single `E^{∖D}`-edge,
--   each bifurcation-through-`D` slab into a single `L^{∖D}`-edge),
--   and σ-blocking on each side transports along that bijection
--   because the disjointness `D ∩ (A ∪ B ∪ C) = ∅` ensures the
--   endpoints and conditioning set are preserved, and `claim_3_16`
--   (ancestors are preserved by marginalization on `J ∪ (V ∖ D)`)
--   ensures the ancestor-set used in the collider clause matches
--   on the two sides.
set_option linter.unusedVariables false in
-- claim_3_25 -- start statement
theorem iSigmaSeparation_marginalize_iff
    (G : CDMG Node) (A B C : Set Node) (D : Finset Node) (hD_sub : D ⊆ G.V)
    (hA : A ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hB : B ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hD_disj : Disjoint (↑D : Set Node) (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C hA hB hC ↔
      (G.marginalize D hD_sub).IsISigmaSeparated A B C
        (G.subset_marginalize_carrier_of_disjoint A D hD_sub hA
          (hD_disj.mono_right
            (Set.subset_union_left.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint B D hD_sub hB
          (hD_disj.mono_right
            (Set.subset_union_right.trans Set.subset_union_left)))
        (G.subset_marginalize_carrier_of_disjoint C D hD_sub hC
          (hD_disj.mono_right Set.subset_union_right))
-- claim_3_25 -- end statement
:= by
  -- ## Step 1 (LN tex) — reduction to one-node marginalization.
  --
  -- Outer induction on `D.card`.  The IH needs to apply at a
  -- different CDMG (`G.marginalize {u} hu` for some `u ∈ D`) with a
  -- different argument set (`D.erase u`), so we promote the iff to a
  -- form universally quantified over the CDMG `G'` and the Finset
  -- `D'` before inducting on `n = D'.card`.
  suffices h : ∀ (n : ℕ) (G' : CDMG Node)
      (hA' : A ⊆ (↑G'.J : Set Node) ∪ ↑G'.V)
      (hB' : B ⊆ (↑G'.J : Set Node) ∪ ↑G'.V)
      (hC' : C ⊆ (↑G'.J : Set Node) ∪ ↑G'.V)
      (D' : Finset Node) (hD'_sub : D' ⊆ G'.V)
      (hD'_disj : Disjoint (↑D' : Set Node) (A ∪ B ∪ C)),
      D'.card = n →
      (G'.IsISigmaSeparated A B C hA' hB' hC' ↔
        (G'.marginalize D' hD'_sub).IsISigmaSeparated A B C
          (G'.subset_marginalize_carrier_of_disjoint A D' hD'_sub hA'
            (hD'_disj.mono_right
              (Set.subset_union_left.trans Set.subset_union_left)))
          (G'.subset_marginalize_carrier_of_disjoint B D' hD'_sub hB'
            (hD'_disj.mono_right
              (Set.subset_union_right.trans Set.subset_union_left)))
          (G'.subset_marginalize_carrier_of_disjoint C D' hD'_sub hC'
            (hD'_disj.mono_right Set.subset_union_right))) by
    exact h D.card G hA hB hC D hD_sub hD_disj rfl
  intro n
  induction n with
  | zero =>
      -- Base case: D'.card = 0 ⇒ D' = ∅; reduce to
      -- `iSigmaSeparation_marginalize_empty_iff`.
      intro G' _ _ _ D' hD'_sub hD'_disj h_card
      have hD'_empty : D' = ∅ := Finset.card_eq_zero.mp h_card
      subst hD'_empty
      exact iSigmaSeparation_marginalize_empty_iff G' A B C hD'_sub _ _ _ _ _ _
  | succ n ih =>
      -- Inductive step: D'.card = n + 1 ⇒ ∃ u ∈ D'.  Let E := D'.erase u
      -- (E.card = n).  Chain:
      --   G'.IsISigmaSep A B C
      --     ↔[one_iff at u]
      --   (G'.marginalize {u} hu_sub).IsISigmaSep A B C
      --     ↔[ih at G'.marginalize {u} hu_sub, E]
      --   ((G'.marginalize {u} hu_sub).marginalize E hE_sub_marg).IsISigmaSep A B C
      --     ↔[iSigmaSeparated_iff_of_eq via marginalize_comm]
      --   (G'.marginalize D' hD'_sub).IsISigmaSep A B C
      intro G' hA' hB' hC' D' hD'_sub hD'_disj h_card
      have hD'_ne : D'.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u, hu_in_D'⟩ := hD'_ne
      let E : Finset Node := D'.erase u
      have hE_card : E.card = n := by
        change (D'.erase u).card = n
        have h := Finset.card_erase_add_one hu_in_D'
        omega
      -- {u} ⊆ G'.V from u ∈ D' ⊆ G'.V.
      have hu_sub : ({u} : Finset Node) ⊆ G'.V := by
        intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        exact hD'_sub hu_in_D'
      have hu_notin_E : u ∉ E := Finset.notMem_erase u D'
      -- E ⊆ (G'.marginalize {u} hu_sub).V (= G'.V \ {u}) via u ∉ E.
      have hE_sub_marg : E ⊆ (G'.marginalize {u} hu_sub).V := by
        change E ⊆ G'.V \ {u}
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        refine ⟨hD'_sub (Finset.mem_of_mem_erase hx), ?_⟩
        intro h_eq
        subst h_eq
        exact hu_notin_E hx
      have hE_sub_G' : E ⊆ G'.V :=
        fun x hx => hD'_sub (Finset.mem_of_mem_erase hx)
      -- {u} ∩ (A ∪ B ∪ C) = ∅, derived from D' ∩ (A ∪ B ∪ C) = ∅ and
      -- {u} ⊆ D' (Set-coercion side).
      have hu_in_D'_coe : (↑({u} : Finset Node) : Set Node) ⊆ ↑D' := by
        rw [Finset.coe_subset, Finset.singleton_subset_iff]
        exact hu_in_D'
      have hu_disj_ABC : Disjoint (↑({u} : Finset Node) : Set Node)
                                  (A ∪ B ∪ C) :=
        hD'_disj.mono_left hu_in_D'_coe
      -- E ∩ (A ∪ B ∪ C) = ∅ from E ⊆ D'.
      have hE_sub_D'_coe : (↑E : Set Node) ⊆ ↑D' :=
        Finset.coe_subset.mpr (Finset.erase_subset u D')
      have hE_disj_ABC : Disjoint (↑E : Set Node) (A ∪ B ∪ C) :=
        hD'_disj.mono_left hE_sub_D'_coe
      -- Carrier transports on G'.marginalize {u} hu_sub for A, B, C.
      have hA_marg : A ⊆ (↑(G'.marginalize {u} hu_sub).J : Set Node) ∪
                         ↑(G'.marginalize {u} hu_sub).V :=
        G'.subset_marginalize_carrier_of_disjoint A {u} hu_sub hA'
          (hu_disj_ABC.mono_right
            (Set.subset_union_left.trans Set.subset_union_left))
      have hB_marg : B ⊆ (↑(G'.marginalize {u} hu_sub).J : Set Node) ∪
                         ↑(G'.marginalize {u} hu_sub).V :=
        G'.subset_marginalize_carrier_of_disjoint B {u} hu_sub hB'
          (hu_disj_ABC.mono_right
            (Set.subset_union_right.trans Set.subset_union_left))
      have hC_marg : C ⊆ (↑(G'.marginalize {u} hu_sub).J : Set Node) ∪
                         ↑(G'.marginalize {u} hu_sub).V :=
        G'.subset_marginalize_carrier_of_disjoint C {u} hu_sub hC'
          (hu_disj_ABC.mono_right Set.subset_union_right)
      -- IH at (G'.marginalize {u} hu_sub, E).
      have step_ih := ih (G'.marginalize {u} hu_sub) hA_marg hB_marg hC_marg
                          E hE_sub_marg hE_disj_ABC hE_card
      -- One-node iff at (G', u).
      have step_one := iSigmaSeparation_marginalize_one_iff G' u hu_sub A B C
                          hA' hB' hC' hu_disj_ABC
      -- The CDMG equality:
      --   (G'.marginalize {u} hu_sub).marginalize E hE_sub_marg
      --     = G'.marginalize D' hD'_sub.
      -- Via marginalize_comm + the union identity {u} ∪ E = D'.
      have h_uE_disj : Disjoint ({u} : Finset Node) E := by
        rw [Finset.disjoint_singleton_left]
        exact hu_notin_E
      have h_union_eq : ({u} : Finset Node) ∪ E = D' := by
        ext x
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, E]
        constructor
        · rintro (rfl | ⟨_, hx⟩)
          · exact hu_in_D'
          · exact hx
        · intro hx
          by_cases h : x = u
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
      have h_marg_chain :
          (G'.marginalize {u} hu_sub).marginalize E hE_sub_marg
            = G'.marginalize D' hD'_sub := by
        -- Bridge marginalize_comm's `G'.marginalize ({u} ∪ E) _` to
        -- `G'.marginalize D' hD'_sub` via the union identity
        -- `{u} ∪ E = D'`.  Direct `rw` on the goal fails (the subset
        -- proof's type depends on the Finset arg, so the motive is
        -- not type-correct); instead we `clear_value` the let-binding
        -- for `E` and then `subst` to substitute D' := {u} ∪ E,
        -- after which proof irrelevance closes the residual.
        have h_comm := (marginalize_comm G' {u} E hu_sub hE_sub_G' h_uE_disj).1
        clear_value E
        subst h_union_eq
        exact h_comm
      -- Transport the iff endpoint via h_marg_chain.
      have step_eq := iSigmaSeparated_iff_of_eq (A := A) (B := B) (C := C)
        h_marg_chain
        ((G'.marginalize {u} hu_sub).subset_marginalize_carrier_of_disjoint A E
          hE_sub_marg hA_marg
          (hE_disj_ABC.mono_right
            (Set.subset_union_left.trans Set.subset_union_left)))
        ((G'.marginalize {u} hu_sub).subset_marginalize_carrier_of_disjoint B E
          hE_sub_marg hB_marg
          (hE_disj_ABC.mono_right
            (Set.subset_union_right.trans Set.subset_union_left)))
        ((G'.marginalize {u} hu_sub).subset_marginalize_carrier_of_disjoint C E
          hE_sub_marg hC_marg
          (hE_disj_ABC.mono_right Set.subset_union_right))
        (G'.subset_marginalize_carrier_of_disjoint A D' hD'_sub hA'
          (hD'_disj.mono_right
            (Set.subset_union_left.trans Set.subset_union_left)))
        (G'.subset_marginalize_carrier_of_disjoint B D' hD'_sub hB'
          (hD'_disj.mono_right
            (Set.subset_union_right.trans Set.subset_union_left)))
        (G'.subset_marginalize_carrier_of_disjoint C D' hD'_sub hC'
          (hD'_disj.mono_right Set.subset_union_right))
      exact step_one.trans (step_ih.trans step_eq)

end CDMG

end Causality
