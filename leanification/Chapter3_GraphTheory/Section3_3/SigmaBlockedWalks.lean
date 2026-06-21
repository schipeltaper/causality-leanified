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

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same chapter
--   convention used by the `CDMG` namespace above and by every other
--   `CDMG`-opening file in the chapter (`BlockableAndUnblockable.lean`,
--   `CollidersAndNon.lean`, `Walks.lean`, `CDMG.lean`,
--   `CDMGNotation.lean`, `EdgeRelations.lean`,
--   `FamilyRelationships.lean`).  The binders here are byte-identical
--   to the `CDMG`-namespace variable line at the top of this file.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds these
--   implicit binders into every declaration below.  Matches the
--   helper-flavour tagging used elsewhere in this chapter.
-- def_3_17 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_17 --- end helper

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : CDMG Node}`.*  Both
--   `IsSigmaOpenGiven` and `IsSigmaBlockedGiven` take
--   a walk `p : Walk G u v` and reach into `G` for
--   `G.AncSet`.  Without the namespace-wide `variable`, every
--   signature would carry an explicit `{G : CDMG Node}` binder;
--   the auto-binding keeps the signatures readable and matches the LN's
--   once-at-the-top "Let $G = (J, V, E, L)$ be a CDMG" quantifier.
--   Matches the `namespace Walk` openings at
--   `BlockableAndUnblockable.lean` and `CollidersAndNon.lean`.
--   `{G}` is implicit because downstream consumers reach into `G`
--   via dot-notation on the walk (`p.IsSigmaOpenGiven C`).
-- def_3_17 --- start helper
variable {G : CDMG Node}
-- def_3_17 --- end helper


-- ref: def_3_17 (paragraph "C-σ-open walk").
--
-- `p.IsSigmaOpenGiven C hC` iff the walk `p` is `C-σ-open` in the LN's
-- sense, under the *side-aware* per-step arrowhead-contribution
-- reading: collider classification at each position reads
-- arrowhead-presence off the `WalkStep`'s constructor tag via
-- `HeadAtSource` / `HeadAtTarget`; see `def_3_15`'s `IsCollider`
-- design block for the full rationale.
--
-- ## Design choice — IsSigmaOpenGiven
--
-- *Behaviour at directed self-loops (deviation from the LN's surface
--   presentation).*  At a directed self-loop step (encoded as
--   `.forwardE _ : WalkStep G v v` with `u = v`), the side-aware
--   collider reading classifies the self-loop-adjacent interior
--   position as a non-collider: `HeadAtSource` on `.forwardE _`
--   returns `False` because its single L-disjunct `s(v, v) ∈ G.L` is
--   vacuously false at a self-loop by `def_3_1`'s `hL_irrefl`.
--   Clause (i)'s universal therefore does not constrain the
--   self-loop-adjacent position, and clause (ii)'s blockable
--   classification can apply instead, with the canonical tex's
--   "Treatment of directed self-loops" reading governing the
--   disambiguation (a self-loop alone never disqualifies an interior
--   position from being unblockable — the position's blockable /
--   unblockable classification depends on the other walk-incident
--   edge if any).  Realises the manager-accepted deviation
--   `collider_side_aware_at_self_loops` from
--   `leanification/deviations.json`.
--
-- *Two-clause conjunction shape.*  The `Prop`-level two-clause
--   conjunction, the per-position universal via
--   `p.vertices[k]? = some vk` Option-membership lookup convention,
--   the asymmetric blockable-only quantification on clause (ii) (per
--   the addition `[claim_type_mismatch_vertex_vs_walk]`'s exclusion
--   of any per-vertex extension of σ-open to unblockable positions),
--   the `hC : C ⊆ ↑G.J ∪ ↑G.V` LN-faithful subset hypothesis on the
--   signature (matching the chapter-wide convention shared by
--   `def_3_18`'s `IsISigmaSeparated` and the other `C`-conditioned
--   predicates), and the `set_option linter.unusedVariables false in`
--   prefix that suppresses the unused-binder warning on the
--   LN-faithful-but-body-inert `hC` all match the chapter convention.
set_option linter.unusedVariables false in
-- def_3_17 -- start statement
def IsSigmaOpenGiven {u v : Node} (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk → p.IsCollider k →
      vk ∈ G.AncSet C) ∧
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk →
      p.IsBlockableNonCollider k → vk ∉ C)
-- def_3_17 -- end statement


-- ref: def_3_17 (paragraph "C-σ-blocked walk").
--
-- `p.IsSigmaBlockedGiven C hC` iff the walk `p` is `C-σ-blocked` in
-- the LN's sense — the positive existential disjunction dual of
-- `IsSigmaOpenGiven`, under the *side-aware* per-step arrowhead-
-- contribution reading from `def_3_15`.
--
-- ## Design choice — IsSigmaBlockedGiven
--
-- *Behaviour at directed self-loops (deviation from the LN's surface
--   presentation).*  Specialisation of the σ-open self-loop analysis
--   above to the existential dual.  At a directed self-loop step the
--   side-aware collider reading rejects the self-loop-adjacent
--   interior position from clause (i)'s blocking-witness set
--   (the `.forwardE _` source-side head-contribution `HeadAtSource`
--   is `False` via the vacuously-false `s(v, v) ∈ G.L` disjunct
--   under `def_3_1`'s `hL_irrefl`).  The newly-non-collider
--   self-loop-adjacent position becomes a candidate for the
--   side-aware blockable / unblockable classification, and a
--   clause-(ii) blocking witness can be formed from it iff the
--   position is blockable AND `vk ∈ C` — matching the canonical
--   tex's "Treatment of directed self-loops" reading and the
--   manager-accepted deviation `collider_side_aware_at_self_loops`
--   from `leanification/deviations.json`.
--
-- *Positive existential disjunction, NOT `¬ IsSigmaOpenGiven`.*  See
--   module-docstring design pillar 6 for the full three-reason
--   rationale: (a) mirrors the LN's
--   `∃ … \notin Anc^G(C) ∨ ∃ … \in C` writing literally;
--   (b) downstream proofs constructing a blocking witness can
--   directly form `Or.inl ⟨k, vk, _, _, _⟩` /
--   `Or.inr ⟨k, vk, _, _, _⟩` terms; (c) the equivalence
--   `¬ p.IsSigmaOpenGiven C hC ↔ p.IsSigmaBlockedGiven C hC` is a
--   standalone (classical) De Morgan lemma to be proved when a
--   downstream row needs it.
--
-- *Three-conjunct-per-existential shape.*  The `(k, vk)` pair
--   encoding (same as the σ-open form, so a classical De Morgan
--   duality lemma can align witness-to-witness on each clause), the
--   three-conjunct structure (`p.vertices[k]? = some vk ∧
--   classifier ∧ membership`), the asymmetric blockable-only
--   quantification on clause (ii) (per the addition
--   `[claim_type_mismatch_vertex_vs_walk]`'s exclusion of any
--   per-vertex extension of σ-open to unblockable positions — a
--   clause-(ii) form `IsNonCollider k ∧ vk ∈ C` would under-fire by
--   admitting unblockable non-collider positions inside `C` as
--   blocking witnesses), the `hC : C ⊆ ↑G.J ∪ ↑G.V` LN-faithful
--   subset hypothesis, and the
--   `set_option linter.unusedVariables false in` prefix all match
--   the chapter convention.
set_option linter.unusedVariables false in
-- def_3_17 -- start statement
def IsSigmaBlockedGiven {u v : Node} (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.IsCollider k ∧ vk ∉ G.AncSet C) ∨
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.IsBlockableNonCollider k ∧ vk ∈ C)
-- def_3_17 -- end statement

end Walk

end CDMG

end Causality
