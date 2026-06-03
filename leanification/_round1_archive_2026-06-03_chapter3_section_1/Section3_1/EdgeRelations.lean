import Chapter3_GraphTheory.Section3_1.CDMGNotation

namespace Causality

/-!
# Edge relations on a CDMG: adjacency, into-`v`, out-of-`v`

This file formalises the three numbered items of `def_3_3`.  The LN
block, with $G=(J,V,E,L)$ a CDMG, reads:

```
1.  If $v_1 \sus v_2 \in G$ then we call $v_1$ and $v_2$ adjacent in $G$.
2.  Edges of the form $v_1 \hut v_2$ or $v_1 \huh v_2$ are called into $v_1$.
    Edges of the form $v_1 \tuh v_2$ or $v_1 \huh v_2$ are called into $v_2$.
3.  Edges of the form $v_1 \tuh v_2$ or $v_2 \hut v_1$ are called out of $v_1$.
```

The operator clarification
`[inconsistent_writing_order_enumeration_into_vs_out_of]` (treated as
part of the LN) tells us that throughout the enumeration the writings
$v_1 \tuh v_2$ and $v_2 \hut v_1$ denote the same edge (and the
bidirected writings $v_1 \huh v_2$ and $v_2 \huh v_1$ likewise
coincide).  Membership in the categories "into $v$" / "out of $v$"
depends only on the underlying element of `E` / `L`, not on which
textual writing is used.  Concretely:

* Item 2's two sub-clauses ("into $v_1$" vs "into $v_2$") are the *same*
  notion with focal vertex on different sides of the writing — by
  `huh` symmetry (a corollary of `CDMG.hL_symm`) and the definitional
  equality `G.hut v_1 v_2 = G.tuh v_2 v_1`, both sub-clauses collapse
  to a single two-argument relation "edge between two vertices with an
  arrowhead at the focal vertex".
* Item 3's two listed writings (`v_1 \tuh v_2` and `v_2 \hut v_1`)
  *unfold to the same condition* `(v_1, v_2) ∈ G.E` — the LN spells
  the same edge two ways but they are not a disjunction over distinct
  edges.

All three relations are encoded as **two-argument predicates** of the
focal vertex and "the other endpoint" of the edge, sitting on top of
the seven primitive operators from `CDMGNotation`.  Substantive
design-choice notes live in the comment block immediately above each
`def`; read those before modifying.

## Top-level naming and shape

* `CDMG.adjacent G v1 v2` — item 1; `:= G.sus v1 v2`.  Symmetric.
* `CDMG.edgeInto G v1 v2` — item 2; `:= G.hus v1 v2` (focal `v1` on
  the left, other endpoint `v2`).  *Not* symmetric in general — the
  focal vertex is the one with the arrowhead.
* `CDMG.edgeOutOf G v1 v2` — item 3; `:= G.tuh v1 v2` (focal `v1` is
  the source, `v2` is the target).  *Not* symmetric — directed.

Downstream consumers in chapter 3 (`def_3_4` walk-into / walk-out-of,
`def_3_5` parent / child / sibling sets, `def_3_6` acyclicity over
directed walks, `claim_3_1` no-arrowhead-into-`J` restriction) pattern-
match on the LN macros `\hus / \suh / \tuh / \hut / \sus` directly,
so these wrapped relations are not strictly required by later rows —
they exist to *name* the LN's three "edge-relation" concepts so that
chapter 3 (and especially later text-level argument) can refer to them
by their LN names.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- ref: def_3_3 (item 1)
--
-- Adjacency: `G.adjacent v1 v2` says "`v_1` and `v_2` are adjacent in
-- `G`", i.e. there is some edge of any type between them.  Defined as
-- the literal `G.sus v1 v2` from `def_3_2` item 7.
/-
LN tex (item 1 of `def_3_3`):

  If $v_1 \sus v_2 \in G$ then we call $v_1$ and $v_2$
  \emph{adjacent in $G$}.
-/
-- ## Design choice
--
-- *Why `def`, not `abbrev`.*  Parallels every `def` in
--   `CDMGNotation`.  An `abbrev` would unfold eagerly, so any `simp`
--   pass touching `adjacent` would immediately rip it open into the
--   three-disjunct `sus` and then into `Finset` memberships,
--   defeating the point of having a named "adjacency" concept that
--   downstream proofs (`def_3_4` walks, `claim_3_1` no-`J`-adjacency)
--   can reason about as a primitive.  `def` keeps the wrapper opaque
--   by default; `simp only [CDMG.adjacent]` unfolds one controlled
--   layer to `sus` when a proof genuinely needs to case-analyse the
--   underlying edge type.
--
-- *Why a thin rename of `sus`, not an independent disjunction.*  The
--   LN literally defines adjacency by appealing to `\sus`: "if
--   $v_1 \sus v_2 \in G$ then we call them adjacent".  `CDMGNotation`
--   already gives us `G.sus v1 v2 := G.tuh v1 v2 ∨ G.hut v1 v2 ∨
--   G.huh v1 v2` (the three-disjunct form, see the design block above
--   `CDMGNotation.sus` for why `tut` is excluded).  Reusing it via a
--   one-line `def` keeps adjacency definitionally equal to `sus`, so
--   `simp only [CDMG.adjacent]` reaches the `Finset`-membership
--   disjunction in a single step.  Spelling out the three disjuncts
--   here was rejected: it would diverge from `sus` and force any
--   future refactor (e.g. adding a fourth edge type) to update two
--   places instead of one — exactly the failure mode `CDMGNotation`'s
--   `sus` design block warns against.
--
-- *Why `adjacent`, not `Adj` / `Adjacent` / `areAdjacent`.*  Lowercase
--   `adjacent` matches the LN's prose ("we call $v_1$ and $v_2$
--   adjacent in $G$") and the camelCase convention already in use for
--   `tuh / hut / huh / suh / hus / sus`.  Mathlib's
--   `SimpleGraph.Adj` was considered as a guiding analogue, but our
--   CDMG type is bespoke (`structure CDMG` is not a `SimpleGraph`),
--   so there is no actual `Adj` field to mirror.
--
-- *Symmetry.*  `G.adjacent` is a symmetric relation because `G.sus`
--   is symmetric (`tuh ∨ hut ∨ huh` swaps to itself under argument
--   reversal, using `CDMG.hL_symm` for the `huh` disjunct).  The
--   symmetry lemma `G.adjacent v1 v2 ↔ G.adjacent v2 v1` is a one-line
--   corollary; we do not state it here since `def_3_3` itself does
--   not assert it and `claim_3_1` / later rows derive what they need
--   on demand.
--
-- *Addition + wording-check resolution.*  The operator addition
--   identifies same-edge writings, and the LN-critic flagged a
--   notational asymmetry between items 2 and 3.  Neither concern
--   touches item 1: `sus` already collapses writing-equivalent edges
--   to the same predicate value via the underlying `E` / `L`
--   memberships, so `adjacent` inherits the right behaviour for free.
--
-- *Downstream consumers.*  `def_3_4`'s "alternating sequence of
--   adjacent nodes and edges" appeals to this notion implicitly;
--   `claim_3_1` ("no two nodes in $J$ are adjacent") uses adjacency
--   over a restricted node subset; later chapter-3 text-level
--   arguments about active paths and separation refer to adjacency
--   by name.
-- def_3_3 -- start statement
def adjacent (G : CDMG Node) (v1 v2 : Node) : Prop := G.sus v1 v2
-- def_3_3 -- end statement

-- ref: def_3_3 (item 2)
--
-- Edge into the focal vertex: `G.edgeInto v1 v2` says "there is an
-- edge between `v_1` and `v_2` with an arrowhead pointing at `v_1`"
-- (the focal vertex).  Defined as `G.hus v1 v2`, i.e. either the
-- directed edge $v_2 \tuh v_1$ (spelled `v_1 \hut v_2`) or the
-- bidirected edge $v_1 \huh v_2$.
/-
LN tex (item 2 of `def_3_3`):

  Edges of the form $v_1 \hut v_2$ or $v_1 \huh v_2$ are called
  \emph{into $v_1$}.  \\
  Edges of the form $v_1 \tuh v_2$ or $v_1 \huh v_2$ are called
  \emph{into $v_2$}.
-/
-- ## Design choice
--
-- *Why `def`, not `abbrev`.*  Same rationale as for `adjacent` above
--   and every `def` in `CDMGNotation`: an `abbrev` would unfold
--   eagerly to `hus`'s two-disjunct form and then to `Finset`
--   memberships on every `simp`, defeating the purpose of having a
--   named "edge into `v`" concept.  Downstream walk proofs
--   (`def_3_4` walk-into-$v_0$ / walk-into-$v_n$) and `claim_3_1`'s
--   "no edges into `J`" argument want to reason about `edgeInto` as
--   a primitive.  `simp only [CDMG.edgeInto]` opens one controlled
--   layer to `hus` when the proof genuinely needs the disjunction.
--
-- *Two-argument relation `edgeInto G v1 v2` with `v1` the focal
--   vertex.*  Item 2 has *two* sub-clauses written with the focal
--   vertex on opposite sides of the edge writing (left for "into
--   $v_1$", right for "into $v_2$").  Under the addition
--   `[inconsistent_writing_order_enumeration_into_vs_out_of]` these
--   are the same notion at the level of underlying edges in `E`/`L`,
--   so we encode them as one predicate parameterised by the focal
--   vertex.  Concretely:
--     * first sub-clause "into $v_1$" via `v_1 \hut v_2` / `v_1 \huh
--       v_2` → focal `v_1` on the left → `G.hus v1 v2` literally;
--     * second sub-clause "into $v_2$" via `v_1 \tuh v_2` / `v_1
--       \huh v_2` → focal `v_2` on the right → `G.suh v_1 v_2`,
--       which under `huh`-symmetry from `CDMG.hL_symm` (plus the
--       definitional equality `G.hut v_2 v_1 = G.tuh v_1 v_2`) is
--       logically equivalent to `G.hus v_2 v_1`.
--   So both sub-clauses are captured by *one* predicate
--   `edgeInto G v v'` with `v` the focal vertex — exactly the
--   unified shape the LN-critic suggested.
--
-- *Why pick the `hus` (focal-on-left) spelling, not `suh` (focal-on-
--   right) or a brand-new disjunction.*  Three reasons.
--   1.  Item 2's *first* sub-clause is the LN's primary statement of
--       "into $v_1$" and is written with focal vertex on the left;
--       matching that orientation keeps the Lean spelling visually
--       aligned with the LN.
--   2.  `CDMGNotation.hus` is already `G.hut v1 v2 ∨ G.huh v1 v2` —
--       the exact disjunction in item 2's first sub-clause — so we
--       reuse the existing primitive instead of duplicating it.
--   3.  Downstream usage in `def_3_4` walk-into-$v_0$ is spelled
--       `a_0 = v_0 \hus v_1` (focal $v_0$ on the left), and walk-
--       into-$v_n$ is spelled `a_{n-1} = v_{n-1} \suh v_n` (focal
--       $v_n$ on the right).  The chapter 3 walk vocabulary uses
--       *both* `\hus` and `\suh` depending on which endpoint is the
--       focal one; our `edgeInto` collapses the two when the focal
--       vertex is named explicitly, so downstream argument that
--       refers to "edge into $v$" generically (rather than to a
--       specific walk-endpoint role) lands on the same predicate.
--
-- *Why two-argument, not edge-as-object.*  The LN-critic suggested a
--   cleaner reformulation: take an edge `e : Node × Node` and a focal
--   vertex `v`, and check whether the edge has a head at `v`.  We
--   rejected this for chapter 3 because every downstream consumer
--   (`def_3_4` walk-edge constraints `a_0 = v_0 \hus v_1`, `def_3_5`
--   parent / sibling sets, `claim_3_1` no-`\hus`-into-`J`) pattern-
--   matches on the LN macros `\hus / \suh / \tuh / \hut` *directly*,
--   not on an edge-as-object abstraction.  Introducing the abstraction
--   here would force every consumer to convert back and forth.  The
--   `edge-as-object` shape would also have to decide whether the edge
--   is intended to live in `E`, in `L`, or in their union — an
--   additional design knob with no clear LN-side answer.
--
-- *Not symmetric — focal vertex is fixed.*  `G.edgeInto v1 v2` and
--   `G.edgeInto v2 v1` are different predicates in general: the
--   former says "arrowhead at `v_1`", the latter says "arrowhead at
--   `v_2`".  The two coincide exactly when both endpoints have
--   arrowheads, i.e. on bidirected edges.  No symmetry lemma is
--   stated here.
--
-- *Wording-check subtleties addressed.*  The LN-critic's two flags
--   (`into_split_per_endpoint_out_of_single_clause_asymmetry` and
--   `edges_of_the_form_pattern_vs_object`) are both downstream of the
--   addition: by encoding against underlying `E` / `L` membership
--   (via the existing `hus`), same-edge writings collapse to the
--   same predicate value automatically, and the LN's "of the form
--   $X$" phrasing is read object-side (b) not syntactically (a).
--
-- *Downstream consumers.*  `def_3_4`'s "the walk is called into
--   $v_0$ if $a_0 = v_0 \hus v_1$" is exactly `G.edgeInto v_0 v_1`;
--   `def_3_4`'s walk-into-$v_n$ via `a_{n-1} = v_{n-1} \suh v_n` is
--   `G.edgeInto v_n v_{n-1}` (focal at the right endpoint);
--   `claim_3_1`'s "$j \hus v \notin G$" for $j \in J$ is the
--   negation of `G.edgeInto j v`.
-- def_3_3 -- start statement
def edgeInto (G : CDMG Node) (v1 v2 : Node) : Prop := G.hus v1 v2
-- def_3_3 -- end statement

-- ref: def_3_3 (item 3)
--
-- Edge out of the focal vertex: `G.edgeOutOf v1 v2` says "there is a
-- directed edge from `v_1` to `v_2`".  Defined as `G.tuh v1 v2`,
-- i.e. literally `(v_1, v_2) ∈ G.E`.
/-
LN tex (item 3 of `def_3_3`):

  Edges of the form $v_1 \tuh v_2$ or $v_2 \hut v_1$ are called
  \emph{out of $v_1$}.
-/
-- ## Design choice
--
-- *Why `def`, not `abbrev`.*  Same rationale as for `adjacent` and
--   `edgeInto` above: keep the named relation opaque by default.  An
--   `abbrev` would always unfold into `tuh` and then into `G.E`
--   membership on every `simp`, defeating the purpose of having a
--   named "edge out of `v`" concept that downstream walks
--   (`def_3_4` walk-out-of-$v_0$ / walk-out-of-$v_n$), parent / child
--   sets (`def_3_5`), and acyclicity (`def_3_6`) can refer to.
--   `simp only [CDMG.edgeOutOf]` exposes the `tuh` layer in one
--   controlled step.
--
-- *Why a single `tuh`, NOT a disjunction `tuh ∨ hut`.*  This is the
--   load-bearing design call for this row.  Item 3 lists two
--   writings — `v_1 \tuh v_2` and `v_2 \hut v_1` — but under the
--   addition `[inconsistent_writing_order_enumeration_into_vs_out_of]`
--   these are the *same edge*: both unfold to `(v_1, v_2) ∈ G.E`.
--   The LN spells the same edge two ways for stylistic symmetry
--   (matching the placeholder vocabulary of items 5–7 in `def_3_2`)
--   but item 3 is enumerating one notion, not a disjunction of two.
--   A naive `G.tuh v_1 v_2 ∨ G.hut v_1 v_2` would be **wrong**:
--   `G.hut v_1 v_2 = G.tuh v_2 v_1` is the *opposite* directed edge
--   (from `v_2` to `v_1`), so the naive disjunction would call a
--   directed edge `v_2 → v_1` "out of `v_1`", which contradicts the
--   LN's intent.  The addition explicitly fixes this reading.
--
-- *Wording-check subtlety
--   `into_split_per_endpoint_out_of_single_clause_asymmetry`.*  The
--   LN-critic flagged that item 3 covers both writings of "out of
--   $v_1$" in a single clause (treating $v_1$ as the focal vertex
--   that can sit on either side of the writing), while item 2 splits
--   into two clauses.  Encoding "out of $v_1$" as the single
--   directed edge `G.tuh v_1 v_2` is consistent with the critic's
--   suggested unified form ("edge $e$ is *out of* $v$ iff $e$ has a
--   tail at $v$"): in a CDMG only directed edges (`E`) have tails
--   (bidirected edges in `L` have arrowheads at both ends), so "out
--   of $v_1$" is precisely "directed edge with source $v_1$" =
--   "$(v_1, ?) \in G.E$".  No bidirected case appears in item 3 for
--   this reason.
--
-- *Why not an edge-as-object form.*  Same reasoning as for
--   `edgeInto`: downstream walk-edge predicates in `def_3_4` are
--   written with the LN macros directly (`a_0 = v_0 \tuh v_1` for
--   "walk out of $v_0$"), not over an edge-as-object abstraction.
--   We stay aligned with that convention.
--
-- *Naming.*  `edgeOutOf` (camelCase, two words for "out of") parallels
--   `edgeInto`.  Spelling the LN preposition out is clearer than
--   abbreviating; the `edge`-prefix groups items 2 and 3 visually,
--   distinguishing them from `adjacent` (a vertex-vertex relation
--   rather than an edge-oriented one).
--
-- *Not symmetric.*  `G.edgeOutOf v_1 v_2` is directed: it says the
--   directed edge originates at `v_1` and lands at `v_2`.
--   `G.edgeOutOf v_2 v_1` is the opposite directed edge.  Both can
--   hold simultaneously (a 2-cycle in `E`) without contradiction;
--   the type does not forbid it.
--
-- *Relationship to `edgeInto`.*  By the definitional equality
--   `G.hut v_2 v_1 = G.tuh v_1 v_2` we get
--   `G.edgeOutOf v_1 v_2 ↔ G.hut v_2 v_1`, i.e. "out of $v_1$
--   towards $v_2$" iff "into $v_2$ from $v_1$ via the directed
--   half".  The bidirected half of `edgeInto` has no analogue under
--   `edgeOutOf` — bidirected edges are not "out of" anything in this
--   formalisation, again because they have no tail.  This asymmetry
--   between items 2 and 3 is the LN's own and we preserve it.
--
-- *Downstream consumers.*  `def_3_4`'s "the walk is called out of
--   $v_0$ if $a_0 = v_0 \tuh v_1$" is exactly `G.edgeOutOf v_0 v_1`;
--   `def_3_4`'s walk-out-of-$v_n$ via `a_{n-1} = v_{n-1} \hut v_n`
--   is `G.edgeOutOf v_n v_{n-1}` (the same directed edge, focal at
--   the source); `claim_3_1`'s "$j \tuh v$ are allowed" for $j \in J$
--   refers to `G.edgeOutOf j v`.
-- def_3_3 -- start statement
def edgeOutOf (G : CDMG Node) (v1 v2 : Node) : Prop := G.tuh v1 v2
-- def_3_3 -- end statement

end CDMG

end Causality
