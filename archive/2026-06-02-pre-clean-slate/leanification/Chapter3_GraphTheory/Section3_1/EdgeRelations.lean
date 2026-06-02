import Chapter3_GraphTheory.Section3_1.CDMGNotation

/-!
# Named edge relations (def 3.3)

This file introduces three semantic names for combinations of the
primitive directed/bidirected edge relations defined in
`Section3_1.CDMGNotation` (def 3.2):

  * `Adjacent G v₁ v₂` -- there is *any* edge between `v₁` and `v₂`.
  * `EdgeInto G v₁ v₂` -- there is an edge with an arrowhead at `v₁`
    (either `v₁ ⟵[G] v₂` or `v₁ ⟷[G] v₂`).
  * `EdgeOutOf G v₁ v₂` -- there is a directed edge from `v₁` to
    `v₂` (i.e. `v₁ ⟶[G] v₂`).

These mirror the LN's prose phrasings "adjacent in $G$", "into $v$",
"out of $v$". They are *pure terminology*: no new graph structure is
introduced, just prose-readable Lean identifiers on top of the
existing def_3_2 relations. Downstream rows -- def_3_4 (Walks) talks
about walks "into $v_0$" / "out of $v_0$", claim_3_1 talks about
nodes being "adjacent", def_3_5 (FamilyRelationships) uses the
directed-edge "out of" reading -- compose on top of these names.

Each definition is paired with a `@[simp]` characterisation lemma
that unfolds the new name to its def_3_2 underlying form by
`Iff.rfl`, so callers can rewrite freely between the two layers.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- def_3_3 (item 1)
-- title: EdgeRelations -- adjacency
--
-- `Adjacent G v₁ v₂` means there is *some* edge of any kind between
-- `v₁` and `v₂` in the CDMG `G`. This is the LN's "$v_1$ and $v_2$
-- are adjacent in $G$" phrasing -- a prose-level name for the `sus`
-- relation of def_3_2.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.3,
item 1):

  If $v_1 \sus v_2 \in G$ then we call $v_1$ and $v_2$ \emph{adjacent
  in $G$}.
-/
--
-- ## Design choice
--
-- * **`def`, not `abbrev` or `notation`.** A `def` gives us a proper
--   identifier we can mention by name in claim statements (claim 3.1
--   reads "no two nodes in $J$ are adjacent") and that appears in
--   goals and error messages. `abbrev` would dissolve into `sus`
--   immediately, losing the readable name. `notation` would
--   introduce a new arrow token, which we don't need -- def_3_2
--   already provides `v₁ ↮[G] v₂` for the formal reading, and
--   `Adjacent G v₁ v₂` is what we want for the prose.
--
-- * **No new arrow notation.** The LN reserves arrow notation for
--   the six primitives of def_3_2; def_3_3 introduces *English*
--   names for compositions of those primitives. Mirroring that
--   editorial choice, we keep the def_3_2 arrows as the formal-
--   syntax layer and these new identifiers as the prose-syntax
--   layer.
/-- `v₁` and `v₂` are *adjacent in `G`*: there is some edge of any
orientation between them. Definitionally `sus G v₁ v₂` from
def_3_2; the readable name exists so downstream prose statements
such as claim 3.1's "no two nodes in $J$ are adjacent" can be cited
without unfolding to `sus`. -/
def Adjacent (G : CDMG α) (v₁ v₂ : α) : Prop := sus G v₁ v₂

/-- `Adjacent G v₁ v₂` unfolds to the def_3_2 relation
`sus G v₁ v₂`. Tagged `@[simp]` so callers can rewrite freely
between the prose name and the underlying form. -/
@[simp] theorem adjacent_iff {G : CDMG α} {v₁ v₂ : α} :
    Adjacent G v₁ v₂ ↔ sus G v₁ v₂ := Iff.rfl

-- def_3_3 (item 2)
-- title: EdgeRelations -- edge into v₁
--
-- `EdgeInto G v₁ v₂` means the edge between `v₁` and `v₂` has an
-- arrowhead at `v₁`. The two LN spellings of this -- `v₁ \hut v₂`
-- and `v₁ \huh v₂` -- are exactly the disjuncts of `hus` from
-- def_3_2. Item-2's second sentence ("edges of the form
-- $v_1 \tuh v_2$ or $v_1 \huh v_2$ are called into $v_2$") uses the
-- same predicate with the arguments swapped: "edge into $v_2$" is
-- `EdgeInto G v₂ v₁`. No second predicate is introduced.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.3,
item 2):

  Edges of the form $v_1 \hut v_2$ or $v_1 \huh v_2$ are called
  \emph{into $v_1$}.  \\
        Edges of the form $v_1 \tuh v_2$ or $v_1 \huh v_2$ are called
  \emph{into $v_2$}.
-/
--
-- ## Design choice
--
-- * **Convention: arrowhead at the *first* argument.** The LN uses
--   "into $v_1$" with $v_1$ as the first vertex listed, and `hus`
--   (the def_3_2 underlying form) also picks out the $v_1$
--   endpoint as the arrowhead site. By matching that convention,
--   `EdgeInto G v₁ v₂` reads as "an edge into $v_1$, between $v_1$
--   and $v_2$". The LN's "into $v_2$" sentence is the same
--   predicate with arguments swapped: `EdgeInto G v₂ v₁`.
--
-- * **`def`, not `abbrev` or new notation.** Same reasoning as for
--   `Adjacent`: this is prose terminology, and def_3_2's
--   `v₁ ⇷[G] v₂` already covers the formal phrasing.
/-- `EdgeInto G v₁ v₂` -- the edge between `v₁` and `v₂` is *into
`v₁`*, i.e. has an arrowhead at `v₁` (either a directed edge
`v₁ ⟵[G] v₂` or a bidirected edge `v₁ ⟷[G] v₂`). Definitionally
`hus G v₁ v₂` from def_3_2. -/
def EdgeInto (G : CDMG α) (v₁ v₂ : α) : Prop := hus G v₁ v₂

/-- `EdgeInto G v₁ v₂` unfolds to the def_3_2 relation
`hus G v₁ v₂`. -/
@[simp] theorem edgeInto_iff {G : CDMG α} {v₁ v₂ : α} :
    EdgeInto G v₁ v₂ ↔ hus G v₁ v₂ := Iff.rfl

-- def_3_3 (item 3)
-- title: EdgeRelations -- edge out of v₁
--
-- `EdgeOutOf G v₁ v₂` means there is a *directed* edge with `v₁`
-- as the tail, i.e. `(v₁, v₂) ∈ G.E`, equivalently `tuh G v₁ v₂`
-- from def_3_2. The LN gives two equivalent spellings of this same
-- condition: `v₁ \tuh v₂` and `v₂ \hut v₁` -- both unfold to the
-- same `G.E` membership. `edgeOutOf_iff_hut` below makes that
-- equivalence explicit.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.3,
item 3):

  Edges of the form $v_1 \tuh v_2$ or $v_2 \hut v_1$ are called
  \emph{out of $v_1$}.
-/
--
-- ## Design choice
--
-- * **Bidirected edges are deliberately excluded.** A bidirected
--   edge $v_1 \huh v_2$ has arrowheads at *both* endpoints, so it
--   is "into" both vertices but "out of" neither. The LN encodes
--   that asymmetry between items 2 and 3 by listing `\huh` only on
--   the "into" side, never on the "out of" side. This is load-
--   bearing downstream: directed walks (def_3_4) and the
--   parents/ancestors relations (def_3_5) all condition on directed
--   (`\tuh`) edges only, never bidirected ones.
--
-- * **The LN's two spellings collapse to one.** $v_1 \tuh v_2$ and
--   $v_2 \hut v_1$ are *equal* propositions (both unfold to
--   $(v_1, v_2) \in G.E$); the LN gives both spellings to tell the
--   reader they may pick whichever orientation reads better in a
--   given context. We pick `tuh G v₁ v₂` as the canonical form and
--   record the alternative spelling as `edgeOutOf_iff_hut` below.
--
-- * **`def`, not `abbrev` or new notation.** Same reasoning as the
--   two previous items.
/-- `EdgeOutOf G v₁ v₂` -- the edge between `v₁` and `v₂` is *out
of `v₁`*: a directed edge `v₁ ⟶[G] v₂`. Definitionally
`tuh G v₁ v₂` from def_3_2. Note the deliberate asymmetry with
`EdgeInto`: bidirected edges are excluded here, because a
bidirected edge has arrowheads at both endpoints and so is "into"
both vertices but "out of" neither. -/
def EdgeOutOf (G : CDMG α) (v₁ v₂ : α) : Prop := tuh G v₁ v₂

/-- `EdgeOutOf G v₁ v₂` unfolds to the def_3_2 relation
`tuh G v₁ v₂`. -/
@[simp] theorem edgeOutOf_iff {G : CDMG α} {v₁ v₂ : α} :
    EdgeOutOf G v₁ v₂ ↔ tuh G v₁ v₂ := Iff.rfl

/-- The LN's alternative spelling: "$v_2 \hut v_1$" also expresses
"out of $v_1$". Both `tuh G v₁ v₂` (canonical) and `hut G v₂ v₁`
(alternative) unfold to `(v₁, v₂) ∈ G.E`, so the equivalence is
definitional. -/
theorem edgeOutOf_iff_hut (G : CDMG α) (v₁ v₂ : α) :
    EdgeOutOf G v₁ v₂ ↔ hut G v₂ v₁ := Iff.rfl

/-- Adjacency is symmetric. The directed-edge cases swap
`tuh`/`hut` (which are propositionally equal up to argument order);
the bidirected case uses `G.L_symm` from def_3_1. Later chapters
use this implicitly whenever they restate an "adjacent" hypothesis
with the arguments swapped. -/
theorem Adjacent.symm {G : CDMG α} {v₁ v₂ : α}
    (h : Adjacent G v₁ v₂) : Adjacent G v₂ v₁ := by
  rcases h with htuh | hhut | hhuh
  · exact Or.inr (Or.inl htuh)
  · exact Or.inl hhut
  · exact Or.inr (Or.inr (G.L_symm hhuh))

end CDMG

end Causality
