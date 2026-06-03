import Chapter3_GraphTheory.Section3_1.CDMG

/-!
# Notation for Conditional Directed Mixed Graphs

This file equips the `CDMG` structure introduced in `Section3_1.CDMG`
(def 3.1 of the lecture notes) with the seven notations of the LN's
`\begin{Not}` block (def 3.2):

  * vertex membership `v ∈ G`,
  * directed edge `v₁ ⟶[G] v₂`,
  * reverse directed edge `v₁ ⟵[G] v₂`,
  * bidirected edge `v₁ ⟷[G] v₂`,
  * "arrowhead at `v₂`" (LN's `\suh`) `v₁ ⇸[G] v₂`,
  * "arrowhead at `v₁`" (LN's `\hus`) `v₁ ⇷[G] v₂`,
  * "any edge between" (LN's `\sus`) `v₁ ↮[G] v₂`.

The notations are `scoped` under `Causality.CDMG`; users bring them in
with `open scoped Causality.CDMG`.
-/

namespace Causality

variable {α : Type*}

-- def_3_2 (item 1)
-- title: CDMGNotation -- vertex membership
--
-- `v ∈ G` means `v ∈ G.J ∪ G.V`, i.e. `v` is either an input node or
-- an output node of the CDMG `G`. We register this as a `Membership`
-- instance so the literal Lean syntax `v ∈ G` typechecks and unfolds
-- to set-union membership.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.2,
item 1, in `\begin{Not}\label{not-cdmg}`):

  $v \in G$ to mean $v \in J \cup V$,
-/
instance : Membership α (CDMG α) where
  mem G v := v ∈ G.J ∪ G.V

/-- The membership `v ∈ G` defining equation: `v` belongs to the CDMG
`G` iff it is either an input or an output node. By definition. -/
@[simp] theorem CDMG.mem_iff {G : CDMG α} {v : α} :
    v ∈ G ↔ v ∈ G.J ∪ G.V := Iff.rfl

namespace CDMG

-- def_3_2 (items 2-4) -- the three primitive edge relations
-- title: CDMGNotation -- directed, reverse-directed, bidirected edges
--
-- `tuh` / `hut` / `huh` mirror the LN macros `\tuh` / `\hut` / `\huh`.
-- They are `Prop`-valued one-line aliases for membership in `G.E`
-- (directed) or `G.L` (bidirected). The names are deliberately kept
-- close to the LN macros so a reader bouncing between the notes and
-- the Lean source can recognise them.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.2,
items 2-4):

  $v_1 \tuh v_2 \in G$ to mean $(v_1,v_2) \in E$,
  $v_1 \hut v_2 \in G$ to mean $(v_2,v_1) \in E$,
  $v_1 \huh v_2 \in G$ to mean $(v_1,v_2) \in L$,
-/

/-- LN's `\tuh`: there is a *directed* edge `v₁ → v₂` in `G`, i.e.
`(v₁, v₂) ∈ G.E`. -/
def tuh (G : CDMG α) (v₁ v₂ : α) : Prop := (v₁, v₂) ∈ G.E

/-- LN's `\hut`: there is a *directed* edge `v₁ ← v₂` in `G`, i.e.
`(v₂, v₁) ∈ G.E` (the same `G.E` membership, with arguments swapped). -/
def hut (G : CDMG α) (v₁ v₂ : α) : Prop := (v₂, v₁) ∈ G.E

/-- LN's `\huh`: there is a *bidirected* edge `v₁ ↔ v₂` in `G`, i.e.
`(v₁, v₂) ∈ G.L`. Because `G.L` is required to be symmetric (see
`CDMG.L_symm` in `def_3_1`), `huh G v₁ v₂` and `huh G v₂ v₁` are
propositionally equivalent. -/
def huh (G : CDMG α) (v₁ v₂ : α) : Prop := (v₁, v₂) ∈ G.L

-- def_3_2 (items 5-7) -- the three "star" relations
-- title: CDMGNotation -- arrowhead-at-target / -source / any edge
--
-- The "star" in the LN means "arrowhead or tail"; these three
-- relations are exactly the disjunctions of the primitive edges.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.2,
items 5-7):

  $v_1 \suh v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$
                                       or $v_1 \huh v_2 \in G$,
  $v_1 \hus v_2 \in G$ to mean that either $v_1 \hut v_2 \in G$
                                       or $v_1 \huh v_2 \in G$,
  $v_1 \sus v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$
                                       or $v_1 \hut v_2 \in G$
                                       or $v_1 \huh v_2 \in G$.

The star stands for a placeholder to mean: "arrowhead or tail".
-/

/-- LN's `\suh`: there is an edge with an arrowhead at `v₂` in `G`,
i.e. either `tuh G v₁ v₂` (`→`) or `huh G v₁ v₂` (`↔`). -/
def suh (G : CDMG α) (v₁ v₂ : α) : Prop := tuh G v₁ v₂ ∨ huh G v₁ v₂

/-- LN's `\hus`: there is an edge with an arrowhead at `v₁` in `G`,
i.e. either `hut G v₁ v₂` (`←`) or `huh G v₁ v₂` (`↔`). -/
def hus (G : CDMG α) (v₁ v₂ : α) : Prop := hut G v₁ v₂ ∨ huh G v₁ v₂

/-- LN's `\sus`: there is *some* edge between `v₁` and `v₂` in `G`,
i.e. any of `tuh G v₁ v₂`, `hut G v₁ v₂`, or `huh G v₁ v₂`. This is
the "adjacency" relation used in def 3.3. -/
def sus (G : CDMG α) (v₁ v₂ : α) : Prop :=
  tuh G v₁ v₂ ∨ hut G v₁ v₂ ∨ huh G v₁ v₂

/-- LN `v₁ ⟶[G] v₂`: directed edge `v₁ → v₂` in the CDMG `G`. Matches
LN macro `\tuh`. Unicode arrow is `⟶` (`\longrightarrow`, U+27F6),
chosen distinct from the function arrow `→` to avoid any clash with
Lean's built-in syntax. -/
scoped notation:50 v₁ " ⟶[" G "] " v₂ => Causality.CDMG.tuh G v₁ v₂

/-- LN `v₁ ⟵[G] v₂`: directed edge `v₁ ← v₂` in `G`. Matches LN macro
`\hut`. Equivalent to `v₂ ⟶[G] v₁` by definition. -/
scoped notation:50 v₁ " ⟵[" G "] " v₂ => Causality.CDMG.hut G v₁ v₂

/-- LN `v₁ ⟷[G] v₂`: bidirected edge `v₁ ↔ v₂` in `G`. Matches LN
macro `\huh`. Symmetric in `v₁`/`v₂` thanks to `CDMG.L_symm`. -/
scoped notation:50 v₁ " ⟷[" G "] " v₂ => Causality.CDMG.huh G v₁ v₂

/-- LN `v₁ ⇸[G] v₂`: there is an arrowhead at `v₂` (`→` or `↔`).
Matches LN macro `\suh`. Unicode is `⇸` (U+21F8, RIGHTWARDS ARROW
WITH VERTICAL STROKE) -- the vertical stroke evokes the LN's star
placeholder at the left endpoint. -/
scoped notation:50 v₁ " ⇸[" G "] " v₂ => Causality.CDMG.suh G v₁ v₂

/-- LN `v₁ ⇷[G] v₂`: there is an arrowhead at `v₁` (`←` or `↔`).
Matches LN macro `\hus`. Unicode is `⇷` (U+21F7, LEFTWARDS ARROW
WITH VERTICAL STROKE). -/
scoped notation:50 v₁ " ⇷[" G "] " v₂ => Causality.CDMG.hus G v₁ v₂

/-- LN `v₁ ↮[G] v₂`: any edge of any orientation between `v₁` and
`v₂` ("adjacency"). Matches LN macro `\sus`. Unicode is `↮` (U+21AE,
LEFT RIGHT ARROW WITH STROKE) -- the doubled stroke evokes a
placeholder at both endpoints. -/
scoped notation:50 v₁ " ↮[" G "] " v₂ => Causality.CDMG.sus G v₁ v₂

end CDMG

end Causality

-- ## Design choice
--
-- * **`Membership` instance vs. a separate predicate `CDMG.mem`.**
--   The LN consistently writes `v ∈ G`, which strongly suggests using
--   Lean's built-in `∈` so callers can write the literal phrase. A
--   bespoke predicate `CDMG.mem` would force `CDMG.mem G v` (or, with
--   dot notation, `G.mem v`) at every use site and would not interact
--   with Mathlib's `mem_*` library lemmas at all. The `Membership`
--   instance gives us the LN syntax for free and lets `v ∈ G` rewrite
--   to `v ∈ G.J ∪ G.V` via the `simp` lemma `CDMG.mem_iff`, after
--   which the full power of `Set.mem_union`, `Set.mem_insert_iff`,
--   etc. is available.
--
-- * **Six separate `def`s vs. one inductive `EdgeKind` enum.**
--   An alternative was a single `inductive EdgeKind | dir | revDir |
--   bidir` plus one predicate `hasEdge : EdgeKind → CDMG α → α → α →
--   Prop`. We rejected this for two reasons:
--   1. The LN treats `v₁ \tuh v₂ ∈ G`, `v₁ \huh v₂ ∈ G`, etc. as
--      *atoms* in proofs -- e.g. claim 3.1 reads "no `j ∈ J` has
--      `j \hus v ∈ G`", and def 3.5 defines parents as
--      `{w | w \tuh v \in G}`. Atoms compose better with `simp`,
--      `rw`, and pattern matching than wrapped predicates.
--   2. The three "star" relations (`suh`, `hus`, `sus`) are *not*
--      single edge types -- they are disjunctions. An enum would not
--      naturally represent them; either we'd need a second sum-of-
--      enums layer or we'd revert to disjunctions anyway. Spelling
--      out the disjunctions directly is the LN's own approach.
--
-- * **Notation characters.**
--   We pick Unicode arrows that visually echo the LN macros without
--   clashing with mathlib's existing notation:
--     - `⟶` / `⟵` / `⟷` (U+27F6/F5/F7, long arrows) for `\tuh` /
--       `\hut` / `\huh`. We deliberately avoid the short `→`/`←`/`↔`
--       because those are heavily overloaded (function arrows, `Iff`,
--       rewrite-direction in `rw`, etc.).
--     - `⇸` / `⇷` (U+21F8 / U+21F7, arrows with vertical stroke) for
--       `\suh` / `\hus`. The stroke evokes the LN's "star =
--       arrowhead-or-tail" placeholder.
--     - `↮` (U+21AE, left-right arrow with stroke) for `\sus`.
--   The `[G]` suffix (rather than `\in G` postfix) makes the graph
--   argument explicit at the notation level and avoids the ambiguity
--   of trying to overload Lean's `∈`.
--
-- * **`Prop`-valued, not `Bool`.**
--   `Prop` matches the LN, lets us write `(v₁, v₂) ∈ G.E` directly
--   (which is `Prop`-valued because `G.E : Set (α × α)`), and avoids
--   imposing `DecidableEq α` everywhere -- the lecture notes treat
--   the vertex type as arbitrary, sometimes uncountable (chapters 4
--   and beyond use real-valued nodes), so we cannot assume
--   decidability at this layer. Where decidability matters later
--   (e.g. constructive algorithms over finite graphs) it will be
--   introduced as a separate hypothesis.
--
-- * **Scoped vs. global notation.**
--   `scoped` keeps the arrow notations under `Causality.CDMG`, so a
--   file that doesn't open the namespace isn't paying for our
--   Unicode tokens. Downstream rows (def_3_3 onwards) will
--   `open scoped Causality.CDMG` near the top.
