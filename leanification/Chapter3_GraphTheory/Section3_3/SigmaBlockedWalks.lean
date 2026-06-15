import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_3.CollidersAndNon
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable

namespace Causality

/-!
# σ-blocked and σ-open walks (`def_3_17`)

This file formalises `def_3_17` (`\label{def:sigma_blocking}`), the
third definition of Section 3.3 of the lecture notes.  Given a CDMG
`G = (J, V, E, L)`, a subset of nodes `C ⊆ J ∪ V`, and a walk
`π = (v_0, a_0, v_1, …, a_{n-1}, v_n)` in `G`, the walk `π` is
classified as either `C-σ-open` or `C-σ-blocked`:

* `Walk.IsSigmaOpenGiven p C` — every collider position `k` on `p` has
  `v_k ∈ Anc^G(C)`, AND every blockable non-collider position `k` on
  `p` has `v_k ∉ C`.
* `Walk.IsSigmaBlockedGiven p C` — there exists a collider position
  `k` on `p` with `v_k ∉ Anc^G(C)`, OR there exists a blockable
  non-collider position `k` on `p` with `v_k ∈ C`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/def_3_17_SigmaBlockedWalks.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:sigma_blocking}`) augmented with one operator
clarification:

* `[claim_type_mismatch_vertex_vs_walk]` — the trailing LN remark
  ("unblockable non-colliders are always `C-σ-open`") is informal
  commentary, not part of the definition proper.  It applies the
  walk-level predicate `C-σ-open` to *vertices* (specifically to
  unblockable non-collider occurrences on a walk), which is a type
  mismatch with the just-stated definition (which only classifies
  *walks* as σ-open or σ-blocked).  No Lean obligation is derived
  from it here; any walk-level reformulation of its underlying
  content is handled separately as the dedicated claim row
  `claim_3_21`.

## Design pillars

1. **Walk-level `Prop` predicates `(p : Walk G u v) (C : Set Node)`.**
   The LN classifies *walks* as σ-open / σ-blocked relative to a
   conditioning set; matching that shape directly via
   `Walk.IsSigmaOpenGiven` / `Walk.IsSigmaBlockedGiven` reads as the
   LN does, and dot-notation `p.IsSigmaOpenGiven C` mirrors the LN's
   "π is C-σ-open" prose.  No vertex-level σ-open predicate is
   introduced — the addition `[claim_type_mismatch_vertex_vs_walk]`
   explicitly excludes that direction from this row's formalisation.

2. **Per-position quantification via the existing `IsCollider` and
   `IsBlockableNonCollider` predicates.**  Collider and blockable
   non-collider positions are *already* classified by `def_3_15`
   (`CollidersAndNon.lean`) and `def_3_16`
   (`BlockableAndUnblockable.lean`); reusing those predicates verbatim
   keeps the LN's "for every collider on π" / "for every blockable
   non-collider on π" scope visible at the type level rather than
   re-spelling the arrowhead-count / outgoing-walk-edge case-splits.

3. **`G.AncSet` reused from `FamilyRelationships.lean` (`def_3_5`,
   item iv set form).**  The LN's `Anc^G(C)` for `C ⊆ J ∪ V` is the
   indexed-union ancestor set `⋃_{c ∈ C} Anc^G(c)`, which
   `CDMG.AncSet : CDMG Node → Set Node → Set Node` already encodes.
   Out-of-graph `c ∈ C` contribute `G.Anc c = ∅` (via the `w ∈ G`
   guard inside `Anc`), so no `C ⊆ J ∪ V` hypothesis is needed at
   the def site.

4. **Vertex lookup via `p.vertices[k]? = some vk`, mirroring the
   `IsCollider` / `IsUnblockableNonCollider` idiom.**  The LN writes
   `v_k` for the vertex at position `k` on the walk; in Lean this
   reads off `p.vertices` as an `Option Node` lookup.  Pinning down
   `vk` with a `p.vertices[k]? = some vk` hypothesis lets the
   membership claim `vk ∈ G.AncSet C` (resp. `vk ∈ C`) be stated
   directly on the witness.  Out-of-range `k > p.length` make the
   lookup `none`, so the universal antecedents in `IsSigmaOpenGiven`
   become vacuous and the existential witnesses in
   `IsSigmaBlockedGiven` cannot be formed — matching the LN's
   scoping to `{0, …, n}` without an explicit upper-bound hypothesis.

5. **Unblockable non-colliders are silently outside both
   quantifications.**  Clause (i) ranges over collider positions;
   clause (ii) ranges over *blockable* non-collider positions.
   Unblockable non-collider positions are therefore not constrained
   by either clause — they are "vacuously open" in the walk-level
   sense.  The addition `[claim_type_mismatch_vertex_vs_walk]`
   excludes any per-vertex extension of "σ-open" to unblockable
   positions from this row's formalisation; the closest walk-level
   reformulation of the trailing LN remark lives in `claim_3_21`.

6. **Positive existential disjunction for `IsSigmaBlockedGiven`, NOT
   `¬ IsSigmaOpenGiven`.**  The rewritten canonical tex notes that
   the two classifiers are De Morgan duals and "by construction
   mutually exclusive and jointly exhaustive over walks in `G`".  We
   nonetheless encode `IsSigmaBlockedGiven` *directly* in the
   positive existential form: (a) it mirrors the LN's literal
   `∃ … \notin Anc^G(C) ∨ ∃ … \in C` writing; (b) downstream proofs
   that construct a blocking witness can directly form the
   `Or.inl ⟨k, vk, …⟩` / `Or.inr ⟨k, vk, …⟩` term; (c) the
   equivalence `¬ p.IsSigmaOpenGiven C ↔ p.IsSigmaBlockedGiven C` is
   a standalone (classical) De Morgan lemma to be proved when a
   downstream row needs it — not a definitional reduction the
   def-shape forces.  Encoding `IsSigmaBlockedGiven` as
   `¬ IsSigmaOpenGiven` was considered: it would make the negation
   definitional but would force downstream witness-construction
   proofs to wade through a double-negation push, inverting the
   readability win.
-/

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches
--   the chapter convention set by every prior file (`CDMG.lean`,
--   `CDMGNotation.lean`, `EdgeRelations.lean`, `Walks.lean`,
--   `FamilyRelationships.lean`, `CollidersAndNon.lean`,
--   `BlockableAndUnblockable.lean`).  Without the `variable` the
--   wrapped predicate signatures below have free type variables and
--   fail to type-check.
--
-- *Three-dash `--- start helper` / `--- end helper` markers, not
--   two-dash `-- start statement`.*  Lean 4's `variable` auto-binding
--   folds these implicit binders into every declaration below — they
--   are load-bearing infrastructure, not throwaway local sugar.
--   Matches the wrapping convention used by every prior file in this
--   chapter on the identical `variable` line.
-- def_3_17 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_17 --- end helper

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Namespace-level `variable {G : CDMG Node}`.*  Both
--   `IsSigmaOpenGiven` and `IsSigmaBlockedGiven` take a walk
--   `p : Walk G u v` and reach into `G` for `G.AncSet`.  Without the
--   namespace-wide `variable`, every signature would carry an
--   explicit `{G : CDMG Node}` binder; the auto-binding keeps the
--   signatures readable and matches the LN's once-at-the-top "Let
--   $G = (J, V, E, L)$ be a CDMG" quantifier.  `{G}` is implicit
--   because downstream consumers reach into `G` via dot-notation on
--   the walk (`p.IsSigmaOpenGiven C`).
-- def_3_17 --- start helper
variable {G : CDMG Node}
-- def_3_17 --- end helper

-- ref: def_3_17 (paragraph "C-σ-open walk")
--
-- `p.IsSigmaOpenGiven C` iff the walk `p` is `C-σ-open` in the LN's
-- sense:
--   (i)   for every position `k` on `p` and every vertex `vk` with
--         `p.vertices[k]? = some vk`, if `p.IsCollider k` (per
--         `def_3_15` item ii) then `vk ∈ G.AncSet C`;
--   (ii)  for every position `k` on `p` and every vertex `vk` with
--         `p.vertices[k]? = some vk`, if
--         `p.IsBlockableNonCollider k` (per `def_3_16` paragraph
--         "Blockable non-collider on π") then `vk ∉ C`.
--
-- ## Design choice
--
-- *Universally quantified over all `(k, vk)` pairs witnessing a
--   vertex of `p`.*  The LN's "for every collider `v_k` on `π`"
--   ranges over positions `k ∈ {0, …, n}`; the `(k, vk)` pair
--   together pins down both the position index AND the vertex it
--   refers to.  The `p.vertices[k]? = some vk` hypothesis bounds
--   `k ≤ p.length` implicitly (out-of-range lookups return `none`),
--   so out-of-range `k` make the antecedent `False` and the
--   implication vacuous — matching the LN's scoping to `{0, …, n}`
--   without an explicit upper-bound conjunct.  This mirrors the
--   `IsCollider` / `IsUnblockableNonCollider` idiom of `def_3_15`
--   / `def_3_16`, which both pin down `v_k` the same way.
--
-- *`p.IsCollider k` as antecedent, not unfolding to the arrowhead-
--   count witness.*  The LN's "every collider on π" is already the
--   `IsCollider` predicate of `def_3_15`; reusing it verbatim keeps
--   the LN-grep correspondence and avoids re-spelling the count-
--   based classification.  An alternative shape that ranges over
--   the existential witnesses already inside `IsCollider` (e.g.
--   `∀ k a₁ a₂, p.edges[k - 1]? = some a₁ → … → vk ∈ G.AncSet C`)
--   would inline the collider definition and break the one-to-one
--   LN-to-Lean correspondence.
--
-- *`p.IsBlockableNonCollider k`, NOT `p.IsNonCollider k`.*  The LN's
--   clause (ii) restricts to *blockable* non-colliders; unblockable
--   non-colliders are silently outside both clauses.  This is the
--   LN's intended restriction (per the addition
--   `[claim_type_mismatch_vertex_vs_walk]`, which excludes the
--   trailing LN remark "unblockable non-colliders are always
--   σ-open" from this row's formalisation; any walk-level
--   reformulation of that remark is deferred to the dedicated claim
--   row `claim_3_21`).  The addition nonetheless records the
--   underlying intent the remark was gesturing at — that unblockable
--   positions do not contribute to (un)blocking — and that intent is
--   encoded structurally here: clause (ii)'s quantification over
--   *blockable* non-colliders only is its predicate-level
--   realisation.  Encoding clause (ii) as `p.IsNonCollider k →
--   vk ∉ C` would over-fire: it would require unblockable
--   non-collider positions to be outside `C`, which is *not* what
--   the LN says.
--
-- *`G.AncSet C` reused from `FamilyRelationships.lean` (`def_3_5`,
--   item iv set form).*  The LN's `Anc^G(C)` for `C ⊆ J ∪ V` is the
--   indexed-union ancestor set, which `CDMG.AncSet` already encodes
--   verbatim.  Out-of-graph `c ∈ C` contribute `G.Anc c = ∅` (by
--   the `w ∈ G` guard inside `Anc`), so the LN's `C ⊆ J ∪ V`
--   hypothesis is not needed at the def site — an escaping `C`
--   simply restricts the effective ancestor set to
--   `Anc^G(C ∩ (J ∪ V))`.  Downstream consumers that genuinely
--   need `C ⊆ J ∪ V` pass it as an extra hypothesis at the use
--   site, following the chapter convention from `def_3_5`'s
--   `PaSet` / `AncSet` / `DescSet`.
--
-- *Conjunction of two universals, NOT a single universal over a
--   sum-typed predicate.*  The LN spells the two clauses as two
--   parallel universals (one over colliders, one over blockable
--   non-colliders); a single universal of the form
--   `∀ k vk, p.vertices[k]? = some vk → (collider-clause ∧
--   blockable-clause)` would also be admissible, but the two-clause
--   form mirrors the LN's bullet-list writing literally and lets a
--   downstream proof destructure `⟨h_collider, h_blockable⟩`
--   without a per-position conjunction shuffle.
-- def_3_17 -- start statement
def IsSigmaOpenGiven {u v : Node} (p : Walk G u v) (C : Set Node) : Prop :=
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk → p.IsCollider k →
      vk ∈ G.AncSet C) ∧
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk →
      p.IsBlockableNonCollider k → vk ∉ C)
-- def_3_17 -- end statement

-- ref: def_3_17 (paragraph "C-σ-blocked walk")
--
-- `p.IsSigmaBlockedGiven C` iff the walk `p` is `C-σ-blocked` in the
-- LN's sense — the existential disjunction dual of
-- `IsSigmaOpenGiven`:
--   (i)   there exists a position `k` on `p` and vertex `vk` with
--         `p.vertices[k]? = some vk`, `p.IsCollider k`, and
--         `vk ∉ G.AncSet C`; OR
--   (ii)  there exists a position `k` on `p` and vertex `vk` with
--         `p.vertices[k]? = some vk`, `p.IsBlockableNonCollider k`,
--         and `vk ∈ C`.
--
-- ## Design choice
--
-- *Positive existential disjunction, NOT `¬ IsSigmaOpenGiven`.*  The
--   LN spells `C-σ-blocked` as an existential ∨ of negated forms of
--   the universal clauses of `C-σ-open` — the De Morgan dual.  We
--   encode it directly in that existential form, rather than as
--   `¬ p.IsSigmaOpenGiven C`, for three reasons: (a) it mirrors the
--   LN's `∃ … \notin Anc^G(C) ∨ ∃ … \in C` writing literally; (b)
--   downstream proofs that *construct* a blocking witness can
--   directly form the `Or.inl ⟨k, vk, _, _, _⟩` /
--   `Or.inr ⟨k, vk, _, _, _⟩` term, rather than pushing a double
--   negation through universal quantifiers and conjunctions; (c)
--   the equivalence `¬ p.IsSigmaOpenGiven C ↔
--   p.IsSigmaBlockedGiven C` is a standalone (classical) De Morgan
--   lemma to be proved when a downstream row needs it — not a
--   definitional reduction the def-shape forces.
--
-- *Same `(k, vk)` pair encoding as `IsSigmaOpenGiven`.*  The
--   existential takes `∃ k vk` pinning both the position index and
--   the vertex at that position via `p.vertices[k]? = some vk`.
--   Keeping both classifiers structurally symmetric makes the De
--   Morgan duality lemma (when proved) align witness-to-witness on
--   each clause.
--
-- *Conjunction `p.vertices[k]? = some vk ∧ p.IsCollider k ∧ vk ∉
--   G.AncSet C` inside the existential.*  Mirrors the LN's "there
--   exists a position `k` on `π` such that [k is a collider on π]
--   and [v_k ∉ Anc^G(C)]" writing, with the vertex-lookup conjunct
--   added to extract `vk` from the existential.  The three-conjunct
--   shape destructures cleanly as `⟨h_lookup, h_collider, h_anc⟩`
--   at the use site.
--
-- *`p.IsBlockableNonCollider k`, same as `IsSigmaOpenGiven`.*  The
--   LN's "blockable non-collider on π in C" of clause (ii) is
--   exactly the `IsBlockableNonCollider` predicate of `def_3_16`,
--   conjoined with `vk ∈ C`.  Reusing the existing predicate keeps
--   the LN-grep correspondence and inherits the walk-edge reading
--   of "blockable" from `def_3_16` rather than re-spelling the
--   outgoing-walk-edge case-split.  Encoding clause (ii) as
--   `p.IsNonCollider k ∧ vk ∈ C` would under-fire: it would admit
--   unblockable non-collider positions inside `C` as blocking
--   witnesses, which is *not* what the LN says — the dual of the
--   over-fire argument on `IsSigmaOpenGiven`, and equally a
--   consequence of the addition
--   `[claim_type_mismatch_vertex_vs_walk]`'s exclusion of any
--   per-vertex "unblockable ⇒ open" extension (walk-level
--   reformulation deferred to `claim_3_21`).
--
-- *Mutually exclusive and jointly exhaustive — by classical De
--   Morgan, not by Lean reduction.*  Per the rewritten canonical
--   tex's "De Morgan duality" paragraph, `p.IsSigmaBlockedGiven C
--   ↔ ¬ p.IsSigmaOpenGiven C` holds.  This is a downstream lemma
--   (classical, by De Morgan) intentionally not forced at the def
--   site — see the "Positive existential disjunction" rationale
--   above for why the positive existential shape is primary.
-- def_3_17 -- start statement
def IsSigmaBlockedGiven {u v : Node} (p : Walk G u v) (C : Set Node) : Prop :=
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.IsCollider k ∧ vk ∉ G.AncSet C) ∨
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.IsBlockableNonCollider k ∧ vk ∈ C)
-- def_3_17 -- end statement

end Walk

end CDMG

end Causality
