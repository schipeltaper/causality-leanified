import Chapter3_GraphTheory.Section3_1.CDMG

namespace Causality

/-!
# CDMG notation: `v ∈ G`, `\tuh`, `\hut`, `\huh`, `\suh`, `\hus`, `\sus`

This file formalises the seven items of the LN notation block
`def_3_2` (`\label{not-cdmg}`).  The block introduces the shorthand
through which every later definition, walk, and graph operation in the
chapter is written.  Concretely:

* `v ∈ G` is the ambient-vertex predicate (the union `J ∪ V`).
* `G.tuh v1 v2`, `G.hut v1 v2`, `G.huh v1 v2` are the three primitive
  edge relations — directed forward, directed backward, bidirected.
* `G.suh`, `G.hus`, `G.sus` are the LN's "star" disjunctions, where the
  star is a placeholder reading "arrowhead or tail".

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_2_CDMGNotation.tex`,
verified equivalent to the LN block (`graphs.tex`, `\label{not-cdmg}`)
augmented with two operator clarifications:

* `[sus_omits_tail_tail_despite_star_eq_head_or_tail]` — `sus` is the
  three-disjunct `tuh ∨ hut ∨ huh`, not the four-disjunct
  `tuh ∨ hut ∨ huh ∨ tut` that the placeholder rule would suggest.
  CDMGs have no tail-tail edge type, so the missing `tut` case is
  excluded by definition, not by oversight.  Any case-analysis on
  `G.sus v1 v2` downstream may treat the three listed disjuncts as
  exhaustive.
* `[huh_visual_symmetry_vs_ordered_pair_in_L]` — `huh` is symmetric in
  its two arguments as a *graph-theoretic* relation, because `CDMG`'s
  `hL_symm` field forces `(v1, v2) ∈ L ↔ (v2, v1) ∈ L`.  The Lean
  definition is *literally* `(v1, v2) ∈ G.L` (asymmetric in shape),
  and the symmetry is a consequence of `hL_symm` rather than baked
  into the definition.  This propagates to `suh`, `hus`, `sus`, whose
  `huh` disjuncts inherit the same property.

The substantive design discussion for every item lives in the comment
block immediately above its `start statement` marker; read those
before modifying the file.  Three design pillars are common to all
seven:

1. **Stay literal w.r.t. the LN.**  Item 1 is a `Membership` instance
   (so that `v ∈ G` parses verbatim, with no need for a custom
   `G.Mem v` call site).  Items 2–4 unfold to the literal
   `(v1, v2) ∈ G.E` / `(v2, v1) ∈ G.E` / `(v1, v2) ∈ G.L` of the LN.
   Items 5–7 are literal `∨`-disjunctions of items 2–4.

2. **Match the LN macro names.**  The Lean def names (`tuh`, `hut`,
   `huh`, `suh`, `hus`, `sus`) are exactly the LN macro names, so a
   reader of the LN can grep them and find the Lean counterpart
   without a translation table.  Under the `CDMG` namespace,
   dot-notation `G.tuh v1 v2` reads like `$v_1 \tuh v_2 \in G$` from
   left to right.

3. **Six separate `Prop` predicates, not a single inductive `EdgeType`
   with a `G.edgeOf` function.**  An ADT
   `inductive EdgeType := tailHead | headTail | headHead`
   paired with `def G.edgeOf : Node → Node → Option EdgeType` would
   collapse the three primitive shapes into one constructor sum.
   Rejected: every downstream consumer writes set-builder forms like
   `Pa^G(v) := {w | w \tuh v \in G}` (`def_3_5`), walk-edge predicates
   `a_k = (v_k, v_{k+1}) \in E` (`def_3_4`), and acyclicity conditions
   `v_0 \tuh v_1 \tuh ... \tuh v_n` (`def_3_6`) that pattern-match
   against individual edge symbols.  Centralising into `EdgeType`
   would force a `match … | EdgeType.tailHead => …` constructor split
   at every use site — text the LN never writes — and would obscure
   the symbol-per-relation grep correspondence above.  Mirroring the
   LN's enumeration 1-to-1 is *one-shot* in this file and trivialises
   every downstream rewrite.  The cost (six declarations instead of
   one) is paid once, here.

No `notation` macros are introduced here.  An infix form such as
`v1 →[G] v2` was considered (see the per-item design notes) but
rejected: every infix would have to carry an explicit `[G]` annotation
to track which CDMG the edge lives in (downstream rows in `def_3_10`
hard intervention and `def_3_11` node splitting compare a graph to
its rewritten copy), and the resulting `v1 →[G] v2` is visually
heavier than `G.tuh v1 v2`.  Dot-notation also makes the grep-match
to the LN macro names exact.  Downstream chapter-3 rows (`def_3_3`
edge relations, `def_3_4` walks, `def_3_5` family relationships,
`def_3_6` acyclicity, `def_3_10` hard intervention, `def_3_11` node
splitting) pattern-match on `G.tuh / G.hut / G.huh / G.suh / G.hus /
G.sus` via plain dot-notation.
-/

namespace CDMG

-- def_3_2 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_2 --- end helper

-- ref: def_3_2 (item 1)
--
-- Membership of a node in a CDMG: `v ∈ G` unfolds to `v ∈ G.J ∪ G.V`,
-- i.e. `v` is either an input node (`J`) or an output node (`V`) of
-- `G`.  Defined as a `Membership Node (CDMG Node)` instance so the
-- literal LN syntax `v ∈ G` parses on the nose.
/-
LN tex (item 1 of `not-cdmg`):

  $v \in G$ to mean $v \in J \cup V$.
-/
-- ## Design choice
--
-- *Why a `Membership` instance, not a plain `def CDMG.Mem`.*  The LN
--   writes `v \in G` verbatim — both in the definition block itself
--   and at every downstream use site (`def_3_5`'s
--   `Pa^G(v) := {w ∈ G | w → v ∈ G}`, `def_3_4`'s walk endpoint
--   constraints `v, w ∈ G`, the `v_1 \tuh v_2 \in G` phrasing of items
--   2–7 below).  A plain `def` would force every consumer to write
--   `G.Mem v` or `CDMG.Mem G v`, neither of which mirrors the LN.
--   Lean's `Membership` typeclass dispatches `∈` to our `mem`
--   function, so `v ∈ G` becomes the literal Lean text downstream —
--   no notation macro needed, no name clash with mathlib's `∈`.
--
-- *No collision with `Finset.instMembership`.*  Mathlib already
--   provides `Membership α (Finset α)`; ours is
--   `Membership Node (CDMG Node)`.  The second type argument differs
--   (`Finset Node` vs `CDMG Node`), so Lean's typeclass resolution
--   picks the right instance at each call site with no need for
--   ascriptions or `@`-spelled-out invocations.  Inside the body
--   `v ∈ G.J ∪ G.V` itself uses `Finset.instMembership` — Lean sees a
--   `Finset Node` on the right of `∈` and dispatches to the mathlib
--   instance, while the outer `v ∈ G` on a `CDMG Node` dispatches to
--   ours.  Both coexist transparently.
--
-- *Why `v ∈ G.J ∪ G.V`, not a pair of disjoint membership tests.*
--   The LN says `v \in J \cup V`; `Finset.instMembership` already
--   gives `Finset` the same `∈` symbol, and `G.J ∪ G.V` is the
--   standard `Finset.union`.  The disjointness `G.hJV_disj` is *not*
--   threaded here — membership only asks "is `v` in either set", not
--   "in exactly one".  Downstream rows that need the exclusive form
--   (e.g. `def_3_10` hard intervention rewriting `V \ W` to `J ∪ W`)
--   invoke `hJV_disj` directly at the use site.
--
-- *Downstream consumers.*  Every later row that quantifies over
--   "vertices of `G`" uses `v ∈ G`: `def_3_3` (adjacency), `def_3_4`
--   (walk endpoint membership), `def_3_5` (every family set is
--   `{w ∈ G | …}`), `def_3_6` (acyclicity: "for any node `v ∈ G`"),
--   `def_3_7` onwards (CDMG-type predicates).  Making this an
--   `instance` rather than a `def` is what lets all those use sites
--   read verbatim from the LN.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: instMembership
-- def_3_2 -- start statement
instance instMembership : Membership Node (CDMG Node) where
  mem G v := v ∈ G.J ∪ G.V
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: instMembership

-- ref: def_3_2 (item 2)
--
-- Directed edge `v1 → v2` in `G`: `G.tuh v1 v2` unfolds to the literal
-- `(v1, v2) ∈ G.E`, i.e. the ordered pair belongs to the directed-edge
-- finset of `G`.
/-
LN tex (item 2 of `not-cdmg`):

  $v_1 \tuh v_2 \in G$ to mean $(v_1,v_2) \in E$.
-/
-- ## Design choice
--
-- *Why a plain `def`, not a `notation` macro or an `abbrev`.*  Plain
--   `def` plus dot-notation `G.tuh v1 v2` reads from left to right
--   exactly like the LN's `$v_1 \tuh v_2 \in G$`.  A unicode
--   `notation v1 →ᵍ v2` macro was considered and rejected: it would
--   either need the graph `G` baked in (creating a `notation3` with a
--   graph slot) or be parameterless and lose the graph context.  An
--   `abbrev` was rejected because we want stable rewriting behaviour
--   — downstream proofs in `def_3_3 / def_3_4 / def_3_6 / claim_3_2`
--   `unfold CDMG.tuh` to reach the underlying `Finset` membership
--   only when they need to; an `abbrev` would always unfold and could
--   mask intent.
--
-- *Why `(v1, v2) ∈ G.E`, not `Prod.mk v1 v2 ∈ G.E` or a custom
--   pair type.*  `CDMG.E : Finset (Node × Node)` (see `CDMG.lean`),
--   so `(v1, v2)` is the literal element of `G.E` — same syntax as
--   the LN's `(v_1, v_2) \in E`.  Switching to a sum-of-edge-types
--   ADT was rejected at the `def_3_1` design stage (see the design
--   block in `CDMG.lean`).
--
-- *Downstream consumers.*  `def_3_5`'s
--   `Pa^G(v) := {w | w \tuh v \in G}` and
--   `Ch^G(v) := {w | v \tuh w \in G}` pattern-match on this;
--   `def_3_4`'s walk-edge case `a_k = (v_k, v_{k+1}) \in E` is the
--   same membership, just spelled differently; `def_3_6`'s
--   non-trivial directed walk uses chains of `tuh`; `def_3_10` hard
--   intervention's `E_{do(W)} := E \ {v → w | v ∈ G, w ∈ W}` rewrites
--   `tuh` edges in bulk.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: tuh
-- def_3_2 -- start statement
def tuh (G : CDMG Node) (v1 v2 : Node) : Prop := (v1, v2) ∈ G.E
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: tuh

-- ref: def_3_2 (item 3)
--
-- Backwards directed edge `v1 ← v2` in `G`: `G.hut v1 v2` unfolds to
-- `(v2, v1) ∈ G.E` — the directed-edge finset is the same `G.E` as
-- for `tuh`, only the argument order is swapped.  So `G.hut v1 v2`
-- and `G.tuh v2 v1` are definitionally equal.
/-
LN tex (item 3 of `not-cdmg`):

  $v_1 \hut v_2 \in G$ to mean $(v_2,v_1) \in E$.
-/
-- ## Design choice
--
-- *Why a primitive `def`, not `G.tuh v2 v1`.*  `hut` is a primitive
--   LN macro and the LN's `def_3_3` distinguishes "edges of the form
--   `v_1 \hut v_2`" as a syntactic shape, not as an `iff`-rewrite of
--   `v_2 \tuh v_1`.  Giving `hut` its own def name matches the LN
--   surface form; the definitional equality
--   `G.hut v1 v2 = G.tuh v2 v1` is then a one-line lemma any
--   consumer can use.
--
-- *Why not `def hut := tuh ∘ swap` (or any composition-style
--   spelling).*  A direct
--   `def hut (G) (v1 v2) := (v2, v1) ∈ G.E` keeps unfolding behaviour
--   predictable: `simp only [CDMG.hut]` lands on the literal `Finset`
--   membership, no intermediate `Function.comp` or `Prod.swap` to
--   peel off.  A composition spelling would force every consumer to
--   chain `Function.comp_apply` and `Prod.swap_apply` rewrites before
--   the `Finset` lemma can fire.  That price is paid at every walk /
--   parent / acyclicity proof downstream — not worth saving one line
--   of `def`.
--
-- *No asymmetry between `tuh` and `hut` in the underlying `E`.*  The
--   ordered pair stored in `G.E` is always head-pointing-from-first
--   `(source, target)`; whether the LN writes `\tuh` (read left-to-
--   right) or `\hut` (read right-to-left) is purely a *reading
--   direction*.  Both refer to the same edge in `G.E`.  This is the
--   reason we did not split `E` into "forward" and "backward"
--   sub-finsets at the `def_3_1` stage.
--
-- *Downstream consumers.*  `def_3_3` item 3 ("edges of the form
--   `v_1 \tuh v_2` or `v_2 \hut v_1` are out of `v_1`") matches on
--   `hut`; `def_3_4` walk's `a_k = (v_{k+1}, v_k) \in E` is
--   `G.hut v_k v_{k+1}` after rewriting; `def_3_4` collider-walk and
--   bifurcation patterns use `hut` for the "incoming-from-the-right"
--   half.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: hut
-- def_3_2 -- start statement
def hut (G : CDMG Node) (v1 v2 : Node) : Prop := (v2, v1) ∈ G.E
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: hut

-- ref: def_3_2 (item 4)
--
-- Bidirected edge `v1 ↔ v2` in `G`: `G.huh v1 v2` unfolds to
-- `(v1, v2) ∈ G.L`.  Symmetric as a graph-theoretic relation because
-- of `CDMG.hL_symm`, even though the Lean definition itself picks an
-- ordered pair.
/-
LN tex (item 4 of `not-cdmg`):

  $v_1 \huh v_2 \in G$ to mean $(v_1,v_2) \in L$.
-/
-- ## Design choice
--
-- *Symmetry is a consequence of `hL_symm`, not baked into `huh`.*
--   Per operator clarification
--   `[huh_visual_symmetry_vs_ordered_pair_in_L]` the LN intends
--   `v_1 \huh v_2 \in G ⟺ v_2 \huh v_1 \in G`.  Our Lean encoding
--   stores `L : Finset (Node × Node)` with the symmetry constraint
--   `hL_symm` on the `CDMG` structure (see `CDMG.lean`'s design
--   block on `[l_quotient_vs_ordered_pair_typing_inconsistent]`).
--   So `G.huh v1 v2 → G.huh v2 v1` holds by `hL_symm`, and the iff
--   form is then a trivial corollary.  Inlining the symmetry into
--   the `def` (e.g. `(v1, v2) ∈ G.L ∨ (v2, v1) ∈ G.L`) was rejected:
--   it would make `huh` and the underlying `L`-membership lemmas
--   drift apart, forcing every `def_3_1`-level `hL_symm` invocation
--   to also rewrite through `huh`.
--
-- *Why `(v1, v2) ∈ G.L`, not a quotient `Quot _ / _`.*  The
--   underlying `def_3_1` design picked the ordered-pair encoding
--   with explicit symmetry (rationale in `CDMG.lean`), and `huh`
--   simply echoes that choice.  Using a quotient here would require
--   `Quot.mk` at the use site every time.  A welcome side effect:
--   because `G.L : Finset (Node × Node)` is a plain `Finset`, all
--   mathlib `Finset` machinery — `Finset.card` (counting bidirected
--   edges), `Finset.filter` / `Finset.image` (selecting / projecting
--   sub-relations), `Finset.union` / `Finset.inter` / `Finset.sdiff`
--   (set algebra for `def_3_10` / `def_3_11` edge-rewriting), and
--   the auto-derived `DecidableMem` — lift to `huh` with zero glue.
--   A `Quot` encoding would have surrendered most of that machinery
--   and forced bespoke lifts at every use site.
--
-- *Irreflexivity is *not* part of `huh`.*  `G.hL_irrefl` lives on
--   the `CDMG` structure and is exposed by `huh` indirectly:
--   `G.huh v v → False` follows from `hL_irrefl`.  Bundling
--   irreflexivity into `huh` itself would obscure the distinction
--   between "is in `L`" (data) and "self-loops excluded" (axiom).
--
-- *Downstream consumers.*  `def_3_4` bidirected walk uses chains of
--   `huh`; `def_3_5`'s `Sib^G(v) := {w | v \huh w \in G}` pattern-
--   matches on this; `def_3_5`'s district relation uses bidirected
--   walks built from `huh`; `def_3_10`'s
--   `L_{do(W)} := L \ {v \huh w | v ∈ G, w ∈ W}` and `def_3_11`'s
--   split-graph `L`-rewriting both rewrite `huh` edges.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: huh
-- def_3_2 -- start statement
def huh (G : CDMG Node) (v1 v2 : Node) : Prop := (v1, v2) ∈ G.L
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: huh

-- ref: def_3_2 (item 5)
--
-- Star-head edge `v1 *→ v2` in `G`: `G.suh v1 v2` is the disjunction
-- `G.tuh v1 v2 ∨ G.huh v1 v2`, i.e. an arrowhead at `v2` and either
-- an arrowhead or a tail at `v1`.
/-
LN tex (item 5 of `not-cdmg`):

  $v_1 \suh v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$ or
  $v_1 \huh v_2 \in G$.
-/
-- ## Design choice
--
-- *Why the literal `tuh ∨ huh`, not a derived predicate over
--   `E ∪ L`.*  The LN's "the star stands for `arrowhead or tail`"
--   rule, applied to `\suh` (star on the left, head on the right),
--   produces exactly two cases — `\tuh` (tail-head) and `\huh`
--   (head-head) — and the LN enumerates exactly those two.
--   Mirroring that disjunction literally is what makes case analysis
--   on `G.suh v1 v2` reduce to `obtain h | h := h`.  A "merged"
--   version like `(v1, v2) ∈ G.E ∪ G.L` was rejected because `E` and
--   `L` are *not* disjoint as subsets of `Node × Node` (see
--   `[edge_set_disjointness_under_specified]` in `CDMG.lean`'s
--   design block): the same ordered pair `(v, w)` may belong to
--   both, and the merged form would lose the LN's two-case
--   decomposition.
--
-- *Why `def`, not `abbrev`.*  An `abbrev` would auto-unfold to the
--   `tuh ∨ huh` body at every elaboration site, eliminating the
--   named abstraction the LN introduces.  The LN treats `\suh` as a
--   named relation (it reappears under that name in `def_3_3`'s
--   "into-`v_2`" classification and in `def_3_4` collider-walk
--   endpoint constraints), not as a shorthand for its two cases.
--   The formalization preserves that: downstream proofs that *want*
--   the disjunction explicit invoke `unfold CDMG.suh` or
--   `simp only [CDMG.suh]` on demand, while other proofs can carry
--   `G.suh v1 v2` opaquely.  Same rationale as `tuh` (item 2 above)
--   but here the abstraction has explicit logical content (a
--   disjunction), so the elaboration-time cost of an over-eager
--   `abbrev` would be more visible.
--
-- *Symmetry propagation from `huh`.*  Per
--   `[huh_visual_symmetry_vs_ordered_pair_in_L]`, the `huh` disjunct
--   of `suh` is symmetric in its two arguments (consequence of
--   `hL_symm`).  The `tuh` disjunct is *not* symmetric.  So
--   `G.suh v1 v2` and `G.suh v2 v1` are logically different in
--   general (the former requires `v1 \tuh v2` or `v1 \huh v2`; the
--   latter requires `v2 \tuh v1` or `v2 \huh v1 ≡ v1 \huh v2`).  The
--   matched-pair identity is `G.suh v1 v2 ↔ G.hus v2 v1`, used as a
--   one-line lemma by consumers that need it.
--
-- *Downstream consumers.*  `def_3_3` item 2's "edges of the form
--   `v_1 \tuh v_2` or `v_1 \huh v_2` are called into `v_2`" is the
--   same shape (read with arguments swapped); `def_3_4`'s collider-
--   walk endpoint constraint `a_0 = v_0 \suh v_1` pattern-matches
--   directly; `def_3_5`'s d-Markov-blanket commented-out form uses
--   `\suh`; `claim_3_2` (acyclic ⟺ topological order) does not need
--   `suh` directly but `def_3_6` acyclicity is stated over `tuh`-only
--   walks.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: suh
-- def_3_2 -- start statement
def suh (G : CDMG Node) (v1 v2 : Node) : Prop :=
  G.tuh v1 v2 ∨ G.huh v1 v2
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: suh

-- ref: def_3_2 (item 6)
--
-- Head-star edge `v1 ←* v2` in `G`: `G.hus v1 v2` is the disjunction
-- `G.hut v1 v2 ∨ G.huh v1 v2`, i.e. an arrowhead at `v1` and either
-- an arrowhead or a tail at `v2`.
/-
LN tex (item 6 of `not-cdmg`):

  $v_1 \hus v_2 \in G$ to mean that either $v_1 \hut v_2 \in G$ or
  $v_1 \huh v_2 \in G$.
-/
-- ## Design choice
--
-- *Mirror of `suh`.*  `hus` is the LN's "into `v_1`" relation, where
--   `suh` was "into `v_2`".  Same two-disjunct shape, only the
--   directed half is `hut` (arrow pointing at `v_1`) rather than
--   `tuh` (arrow pointing at `v_2`).
--
-- *Why `def`, not `abbrev`.*  Same rationale as `suh` (item 5
--   above): the LN treats `\hus` as a named relation, not as
--   shorthand for `\hut ∨ \huh`.  An `abbrev` would over-eagerly
--   unfold to the disjunction at every elaboration site, erasing the
--   abstraction.  Downstream proofs unfold on demand.
--
-- *Symmetry propagation.*  Per
--   `[huh_visual_symmetry_vs_ordered_pair_in_L]`, the `huh` disjunct
--   is symmetric.  So `G.hus v1 v2 ↔ G.suh v2 v1` holds by combining
--   `hut`/`tuh` reversal with `huh` symmetry — a one-line corollary,
--   not part of the def.
--
-- *Downstream consumers.*  `def_3_3` item 2's "edges of the form
--   `v_1 \hut v_2` or `v_1 \huh v_2` are called into `v_1`" is
--   exactly this; `def_3_4`'s walk-into-`v_n` predicate uses `\suh`
--   on the last edge while walk-into-`v_0` uses `\hus`; `def_3_4`'s
--   collider walk has `a_{n-1} = v_{n-1} \hus v_n` for the closing
--   half-edge; `def_3_4`'s bifurcation has `v_{k-1} \hus v_k` as the
--   middle "tip" edge.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: hus
-- def_3_2 -- start statement
def hus (G : CDMG Node) (v1 v2 : Node) : Prop :=
  G.hut v1 v2 ∨ G.huh v1 v2
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: hus

-- ref: def_3_2 (item 7)
--
-- Star-star (adjacency) edge `v1 *−* v2` in `G`: `G.sus v1 v2` is
-- the three-disjunct relation
-- `G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2`.  This is the "any edge
-- type" predicate used to define adjacency.
/-
LN tex (item 7 of `not-cdmg`):

  $v_1 \sus v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$ or
  $v_1 \hut v_2 \in G$ or $v_1 \huh v_2 \in G$.
-/
-- ## Design choice
--
-- *Three disjuncts, not four — the `tut` case is excluded by CDMG
--   definition.*  Per addition
--   `[sus_omits_tail_tail_despite_star_eq_head_or_tail]`, the
--   placeholder rule "the star stands for arrowhead or tail" would
--   mechanically suggest four cases for the compound `\sus`:
--     tail-tail  (`\tut`, undirected)
--     tail-head  (`\tuh`)
--     head-tail  (`\hut`)
--     head-head  (`\huh`)
--   But CDMGs admit only directed (`E`) and bidirected (`L`) edges;
--   there is no tail-tail / undirected edge type.  The LN therefore
--   correctly enumerates three disjuncts and the operator clarifies
--   the missing `\tut` is excluded by definition, not by oversight.
--   Any case analysis on `G.sus v1 v2` downstream is exhaustive over
--   exactly these three alternatives.
--
-- *Refactor warning — keep in sync if CDMGs ever gain a tail-tail
--   edge type.*  If a future revision of `def_3_1` adds a fourth
--   edge field (e.g. `T : Finset (Node × Node)` for undirected
--   `\tut` edges), this `sus` def MUST be updated to add the
--   corresponding `G.tut v1 v2` disjunct, and every downstream
--   proof that case-analyses `G.sus` (currently assumed exhaustive
--   over three cases) becomes incomplete and must be revisited.
--   The `addition_to_the_LN` clause referenced above is the
--   load-bearing reason these proofs are sound today; surface this
--   comment at refactor time so the exhaustiveness contract is
--   renegotiated explicitly rather than silently broken.
--
-- *Disjunction order matches the LN.*  `tuh ∨ hut ∨ huh`, in that
--   left-to-right order, mirrors item 7 of the tex block verbatim.
--   Reordering (e.g. `tuh ∨ huh ∨ hut`) was rejected — preserving
--   the order keeps `rcases` patterns and case names in step with
--   the LN reading.
--
-- *Why `def`, not `abbrev`.*  Same rationale as `suh` / `hus` above:
--   `\sus` is a named LN relation, in particular the basis for the
--   "adjacency" predicate in `def_3_3`.  Allowing `abbrev` to
--   auto-unfold to the three-disjunct body at every use site would
--   replace each "vertices `v_1` and `v_2` are adjacent" appeal with
--   a three-way `∨` — exploding adjacency-driven proofs in
--   `def_3_3` onwards.  Downstream rcases on `sus` unfolds the
--   three cases on demand.
--
-- *Symmetry propagation.*  Per
--   `[huh_visual_symmetry_vs_ordered_pair_in_L]`, the `huh` disjunct
--   is symmetric.  The pair `tuh ∨ hut` is *jointly* symmetric:
--   `G.tuh v1 v2 ∨ G.hut v1 v2 ↔ G.tuh v2 v1 ∨ G.hut v2 v1`
--   (reversing arguments swaps the two disjuncts).  Combined,
--   `G.sus v1 v2 ↔ G.sus v2 v1` — `sus` is a *symmetric* relation,
--   which is why `def_3_3` item 1 uses it for "adjacency".  The
--   symmetry is again a corollary, not part of the def.
--
-- *Downstream consumers.*  `def_3_3` item 1 (adjacency: "if
--   `v_1 \sus v_2 \in G` then we call `v_1` and `v_2` adjacent in
--   `G`"); `def_3_4` walk definition's "alternating sequence of
--   adjacent nodes and edges" appeals to `sus` implicitly;
--   `def_3_4` collider-walk note "for `n=1` this reads
--   `v \sus w \in G`"; later d-/σ-separation chapters use
--   `sus`-adjacency to define "active paths" in CDMGs.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: sus
-- def_3_2 -- start statement
def sus (G : CDMG Node) (v1 v2 : Node) : Prop :=
  G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: sus

end CDMG

namespace refactor_CDMG

-- def_3_2 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_2 --- end helper

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: instMembership (was: refactor_instMembership)
-- ref: def_3_2 (item 1) — refactor
--
-- Membership of a node in a CDMG: `v ∈ G` unfolds to `v ∈ G.J ∪ G.V`,
-- i.e. `v` is either an input node (`J`) or an output node (`V`) of
-- `G`.  Defined as a `Membership Node (CDMG Node)` instance so the
-- literal LN syntax `v ∈ G` parses on the nose.
/-
LN tex (item 1 of `not-cdmg`):

  $v \in G$ to mean $v \in J \cup V$.
-/
-- ## Design choice
--
-- *Why a `Membership` instance, not a plain `def CDMG.Mem`.*  The LN
--   writes `v \in G` verbatim — both in the definition block itself
--   and at every downstream use site (`def_3_5`'s
--   `Pa^G(v) := {w ∈ G | w → v ∈ G}`, `def_3_4`'s walk endpoint
--   constraints `v, w ∈ G`, the `v_1 \tuh v_2 \in G` phrasing of items
--   2–7 below).  A plain `def` would force every consumer to write
--   `G.Mem v` or `CDMG.Mem G v`, neither of which mirrors the LN.
--   Lean's `Membership` typeclass dispatches `∈` to our `mem`
--   function, so `v ∈ G` becomes the literal Lean text downstream —
--   no notation macro needed, no name clash with mathlib's `∈`.
--
-- *No collision with `Finset.instMembership`.*  Mathlib already
--   provides `Membership α (Finset α)`; ours is
--   `Membership Node (CDMG Node)`.  The second type argument differs
--   (`Finset Node` vs `CDMG Node`), so Lean's typeclass resolution
--   picks the right instance at each call site with no need for
--   ascriptions or `@`-spelled-out invocations.  Inside the body
--   `v ∈ G.J ∪ G.V` itself uses `Finset.instMembership` — Lean sees a
--   `Finset Node` on the right of `∈` and dispatches to the mathlib
--   instance, while the outer `v ∈ G` on a `CDMG Node` dispatches to
--   ours.  Both coexist transparently.
--
-- *Why an `instance`, not a `Coe (refactor_CDMG Node) (Finset Node)`
--   coercion to "the vertex set".*  A coercion routing
--   `(G : refactor_CDMG Node)` to `G.J ∪ G.V` was considered and
--   rejected on two grounds.  First, it would collide with — or at
--   best shadow — `Finset.instMembership`: at every `v ∈ G` site Lean
--   would have to *decide* whether to coerce `G` to a `Finset Node`
--   and then dispatch through `Finset.instMembership`, or to dispatch
--   directly through our `Membership Node (refactor_CDMG Node)`
--   instance, with the choice depending on elaboration order at each
--   call site.  Second, a coercion type-erases the distinction
--   between "node mentioned by graph `G`" (the semantic concept) and
--   "element of an opaque `Finset Node` carrier" (an arbitrary
--   `Finset` happening to equal `G.J ∪ G.V`); downstream lemmas
--   reading `v ∈ G` mean the former, and a coercion would silently
--   allow rewrites that mix the two.  The `Membership` instance
--   keeps `refactor_CDMG Node` a distinct logical category whose `∈`
--   is *defined* to be vertex membership — no ambiguity, no
--   precedence races.
--
-- *Why `v ∈ G.J ∪ G.V`, not a pair of disjoint membership tests.*
--   The LN says `v \in J \cup V`; `Finset.instMembership` already
--   gives `Finset` the same `∈` symbol, and `G.J ∪ G.V` is the
--   standard `Finset.union`.  Downstream consumers iterate over "all
--   nodes of `G`" via `Finset.filter` / `Finset.biUnion` /
--   `Finset.image` on `G.J ∪ G.V` directly (`def_3_5`'s family-set
--   definitions, `def_3_8`'s topological-order quantifications), so
--   keeping the body as the single Finset `G.J ∪ G.V` rather than a
--   `Prop`-level disjunction `v ∈ G.J ∨ v ∈ G.V` plugs straight into
--   that idiom.  The `J` and `V` fields are unchanged by the
--   `Sym2`-based encoding of bidirected edges, so this membership
--   instance reads identically to its pre-`Sym2` shape.  The
--   disjointness `G.hJV_disj` is *not* threaded here — membership
--   only asks "is `v` in either set", not "in exactly one".
--   Downstream rows that need the exclusive form (e.g. `def_3_10`
--   hard intervention rewriting `V \ W` to `J ∪ W`) invoke
--   `hJV_disj` directly at the use site.
--
-- *Downstream consumers.*  Every later row that quantifies over
--   "vertices of `G`" uses `v ∈ G`: `def_3_3` (adjacency), `def_3_4`
--   (walk endpoint membership), `def_3_5` (every family set is
--   `{w ∈ G | …}`), `def_3_6` (acyclicity: "for any node `v ∈ G`"),
--   `def_3_7` onwards (CDMG-type predicates).  Making this an
--   `instance` rather than a `def` is what lets all those use sites
--   read verbatim from the LN.
-- def_3_2 -- start statement
instance refactor_instMembership : Membership Node (refactor_CDMG Node) where
  mem G v := v ∈ G.J ∪ G.V
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: instMembership

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: tuh (was: refactor_tuh)
-- ref: def_3_2 (item 2) — refactor
--
-- Directed edge `v1 → v2` in `G`: `G.tuh v1 v2` unfolds to the literal
-- `(v1, v2) ∈ G.E`, i.e. the ordered pair belongs to the directed-edge
-- finset of `G`.
/-
LN tex (item 2 of `not-cdmg`):

  $v_1 \tuh v_2 \in G \;:\Longleftrightarrow\; (v_1, v_2) \in E$.
-/
-- ## Design choice
--
-- *Why a plain `def`, not a `notation` macro, an `abbrev`, or an
--   `instance`.*  Plain `def` plus dot-notation `G.tuh v1 v2` reads
--   from left to right exactly like the LN's `$v_1 \tuh v_2 \in G$`.
--   A unicode `notation v1 →ᵍ v2` macro was considered and rejected:
--   it would either need the graph `G` baked in (creating a
--   `notation3` with a graph slot) or be parameterless and lose the
--   graph context.  An `abbrev` was rejected because we want stable
--   rewriting behaviour — downstream proofs in
--   `def_3_3 / def_3_4 / def_3_6 / claim_3_2` `unfold CDMG.tuh` to
--   reach the underlying `Finset` membership only when they need to;
--   an `abbrev` would always unfold and could mask intent.  An
--   `instance`-as-typeclass spelling (e.g. parametrising a
--   `class HasDirectedEdge (G : refactor_CDMG Node) (v1 v2 : Node)`)
--   was rejected too: `tuh` is a binary `Prop` *predicate* about a
--   specific ordered triple `(G, v1, v2)`, not a typeclass-resolvable
--   property of some single type, so typeclass synthesis has no
--   sensible search target.  A `def` with a fixed name is the right
--   shape — downstream consumers rewrite by name (`G.refactor_tuh`)
--   rather than relying on instance resolution, which keeps the
--   rewriting predictable.
--
-- *Why `(v1, v2) ∈ G.E`, not `Prod.mk v1 v2 ∈ G.E` or a custom
--   pair type.*  `CDMG.E : Finset (Node × Node)` (the `E` field is
--   unchanged by the `Sym2`-based encoding of bidirected edges; only
--   `L` was reshaped), so `(v1, v2)` is the literal element of `G.E`
--   — same syntax as the LN's `(v_1, v_2) \in E`.  Switching to a
--   sum-of-edge-types ADT was rejected at the `def_3_1` design stage
--   (see the design block in `CDMG.lean`).
--
-- *Downstream consumers.*  `def_3_5`'s
--   `Pa^G(v) := {w | w \tuh v \in G}` and
--   `Ch^G(v) := {w | v \tuh w \in G}` pattern-match on this;
--   `def_3_4`'s walk-edge case `a_k = (v_k, v_{k+1}) \in E` is the
--   same membership, just spelled differently; `def_3_6`'s
--   non-trivial directed walk uses chains of `tuh`; `def_3_10` hard
--   intervention's `E_{do(W)} := E \ {v → w | v ∈ G, w ∈ W}` rewrites
--   `tuh` edges in bulk.
-- def_3_2 -- start statement
def refactor_tuh (G : refactor_CDMG Node) (v1 v2 : Node) : Prop := (v1, v2) ∈ G.E
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: tuh

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: hut (was: refactor_hut)
-- ref: def_3_2 (item 3) — refactor
--
-- Backwards directed edge `v1 ← v2` in `G`: `G.hut v1 v2` unfolds to
-- `(v2, v1) ∈ G.E` — the directed-edge finset is the same `G.E` as
-- for `tuh`, only the argument order is swapped.  So `G.hut v1 v2`
-- and `G.tuh v2 v1` are definitionally equal.
/-
LN tex (item 3 of `not-cdmg`):

  $v_1 \hut v_2 \in G \;:\Longleftrightarrow\; (v_2, v_1) \in E$.
-/
-- ## Design choice
--
-- *Why a primitive `def`, not `G.tuh v2 v1`.*  `hut` is a primitive
--   LN macro and the LN's `def_3_3` distinguishes "edges of the form
--   `v_1 \hut v_2`" as a syntactic shape, not as an `iff`-rewrite of
--   `v_2 \tuh v_1`.  Giving `hut` its own def name matches the LN
--   surface form; the definitional equality
--   `G.hut v1 v2 = G.tuh v2 v1` is then a one-line lemma any
--   consumer can use.  As with `tuh` (item 2 above), `def` is also
--   preferred over `abbrev` (over-eager unfolding) and over an
--   `instance`-style typeclass spelling (a binary `Prop` predicate
--   over `(G, v1, v2)` has no sensible typeclass-resolution target).
--
-- *Why not `def hut := tuh ∘ swap` (or any composition-style
--   spelling).*  A direct
--   `def hut (G) (v1 v2) := (v2, v1) ∈ G.E` keeps unfolding behaviour
--   predictable: `simp only [CDMG.hut]` lands on the literal `Finset`
--   membership, no intermediate `Function.comp` or `Prod.swap` to
--   peel off.  A composition spelling would force every consumer to
--   chain `Function.comp_apply` and `Prod.swap_apply` rewrites before
--   the `Finset` lemma can fire.  That price is paid at every walk /
--   parent / acyclicity proof downstream — not worth saving one line
--   of `def`.
--
-- *Why not introduce a separate reverse-edge field or
--   `Finset.image Prod.swap G.E`.*  Two related "store the reversal
--   explicitly" alternatives were considered and rejected.  A
--   structure field `E_rev : Finset (Node × Node)` (or
--   `E_in : ...` indexed by target) would have to be re-derived on
--   every graph operation that mutates `E` — `def_3_10` hard
--   intervention's edge-removal, `def_3_11` node-splitting's
--   edge-rewrite, `def_3_14` marginalisation's edge synthesis would
--   each need a matching `E_rev` update plus a coherence lemma
--   `E_rev = Finset.image Prod.swap E`.  Equivalently, defining
--   `hut` via `(v1, v2) ∈ Finset.image Prod.swap G.E` was rejected
--   on the same grounds: `Finset.image` builds an entirely new
--   `Finset` whose membership proof routes through
--   `Finset.mem_image` (`∃ x ∈ G.E, Prod.swap x = (v1, v2)`), adding
--   an existential layer downstream consumers would have to unpack
--   at every use.  Storing `E` once and swapping the argument order
--   in the *predicate* — `(v2, v1) ∈ G.E` — keeps `G.E` as the
--   single source of truth and makes the asymmetry between `tuh`
--   and `hut` *just* a coordinate swap on the same underlying set,
--   not two sets to keep in sync.
--
-- *No asymmetry between `tuh` and `hut` in the underlying `E`.*  The
--   ordered pair stored in `G.E` is always head-pointing-from-first
--   `(source, target)`; whether the LN writes `\tuh` (read left-to-
--   right) or `\hut` (read right-to-left) is purely a *reading
--   direction*.  Both refer to the same edge in `G.E`.  The `E` field
--   is unchanged by the `Sym2`-based encoding of bidirected edges, so
--   the ordered-pair shape underpinning both `tuh` and `hut` survives
--   the refactor untouched.  This is the reason we did not split `E`
--   into "forward" and "backward" sub-finsets at the `def_3_1` stage.
--
-- *Downstream consumers.*  `def_3_3` item 3 ("edges of the form
--   `v_1 \tuh v_2` or `v_2 \hut v_1` are out of `v_1`") matches on
--   `hut`; `def_3_4` walk's `a_k = (v_{k+1}, v_k) \in E` is
--   `G.hut v_k v_{k+1}` after rewriting; `def_3_4` collider-walk and
--   bifurcation patterns use `hut` for the "incoming-from-the-right"
--   half.
-- def_3_2 -- start statement
def refactor_hut (G : refactor_CDMG Node) (v1 v2 : Node) : Prop := (v2, v1) ∈ G.E
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: hut

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: huh (was: refactor_huh)
-- ref: def_3_2 (item 4) — refactor
--
-- Bidirected edge `v1 ↔ v2` in `G`: `G.huh v1 v2` unfolds to
-- `s(v1, v2) ∈ G.L`, where `s(v1, v2)` is Mathlib's notation for the
-- unordered pair `Sym2.mk (v1, v2)`.  Symmetric as a graph-theoretic
-- relation *and* as a Lean definition: `s(v1, v2) = s(v2, v1)` holds
-- definitionally under the `Sym2` swap quotient, so
-- `G.huh v1 v2 ↔ G.huh v2 v1` collapses to `rfl` after unfolding.
/-
LN tex (item 4 of `not-cdmg`):

  $v_1 \huh v_2 \in G \;:\Longleftrightarrow\; (v_1, v_2) \in L$.
  Because $L$ is required to be symmetric by the CDMG definition
  (def \ref{def-cdmg}: $(v_1, v_2) \in L \Longleftrightarrow
  (v_2, v_1) \in L$ for all $v_1, v_2$), this abbreviation is itself
  symmetric in its two arguments:
  \[ v_1 \huh v_2 \in G \;\Longleftrightarrow\; v_2 \huh v_1 \in G. \]
-/
-- ## Design choice
--
-- *Why `s(v1, v2) ∈ G.L`, not `(v1, v2) ∈ G.L`.*  `CDMG.L` is now
--   `Finset (Sym2 Node)` — Mathlib's `Sym2 Node` is the quotient of
--   `Node × Node` by the swap relation `(a, b) ∼ (b, a)`, so
--   `Finset (Sym2 Node)` is *literally* the LN's
--   `(V × V) / ((v_1, v_2) \sim (v_2, v_1))` (addition
--   `[l_quotient_vs_ordered_pair_typing_inconsistent]` in the
--   `def_3_1` design block records the commitment).  The ordered-pair
--   membership `(v1, v2) ∈ G.L` is no longer well-typed: `G.L`'s
--   carrier is `Sym2 Node`, not `Node × Node`.  `s(v1, v2)` is
--   Mathlib's notation for `Sym2.mk (v1, v2)` (the canonical
--   constructor on the quotient), so `s(v1, v2) ∈ G.L` is the literal
--   "the unordered pair `{v1, v2}` is recorded in `L`".
--
-- *Symmetry is now definitional.*  Under the `Sym2` quotient,
--   `s(v1, v2) = s(v2, v1)` holds *by construction*: the quotient
--   identifies the two ordered pairs (the underlying equality is
--   `Sym2.eq_swap : s(a, b) = s(b, a)` in Mathlib, propositional via
--   `Quot.sound` and proof-irrelevant).  So
--   `G.huh v1 v2 ↔ G.huh v2 v1` collapses to `rfl` after
--   `unfold refactor_CDMG.huh` (literally the same `s(v1, v2) ∈ G.L`
--   on both sides) — a one-line `huh_symm` lemma any consumer can
--   invoke without any `hL_symm` machinery to chain.  Addition
--   `[huh_visual_symmetry_vs_ordered_pair_in_L]` — which articulated
--   the LN's intended symmetry in the ordered-pair era — is now a
--   *structural* property of the encoding, not an axiom routed
--   through a `hL_symm` field.
--
-- *`claim_3_22` (σ-separation symmetry) is the load-bearing
--   downstream payoff.*  Under the pre-refactor ordered-pair-plus-
--   `hL_symm` encoding the symmetry of σ-separation hit an
--   irreducible obstruction on writing-mirror CDMGs (where some
--   `(v, w)` sits simultaneously in `G.E` and `G.L`): a forced swap
--   on walk reversal could land the swapped pair in `G.E`
--   coincidentally, and any downstream predicate reading the channel
--   off the stored pair (`def_3_16` blockable / non-collider
--   classification, `def_3_17` σ-blocked walks) would misclassify
--   the L-step.  Under the `Sym2` encoding, walk reversal and
--   channel classification are structurally orientation-free, and
--   `claim_3_22`'s symmetry argument reduces to a straightforward
--   induction over the typed `WalkStep`.  The cascade —
--   `huh ↔ Sym2.mk membership` ⇒ definitional symmetry ⇒
--   orientation-free walk reversal in `def_3_4` ⇒ symmetric
--   σ-separation in `claim_3_22` — is the *driving* downstream
--   reason `def_3_1` was reshaped at all; see the root's design
--   block for the full justification chain.
--
-- *Why we still take ordered `(v1 v2 : Node)` arguments rather than
--   a single `(s : Sym2 Node)`.*  The LN's surface form
--   `v_1 \huh v_2 \in G` is binary in two *named* vertices, and every
--   downstream consumer (`def_3_3` adjacency, `def_3_5`'s `Sib`,
--   `def_3_4`'s `.bidir` walk constructor, `def_3_15`–`def_3_18`
--   collider/blockable patterns) reaches `refactor_huh` from a
--   context where the two endpoints `v1` and `v2` are named
--   separately and case-analysed individually.  Taking
--   `(s : Sym2 Node)` directly would force a
--   `Sym2.mk (v1, v2)` (or destructure-through-`Sym2.lift`) at every
--   such use site instead of in one centralised place inside `huh`.
--   The ordered-argument signature `G.refactor_huh v1 v2` is the
--   binary-predicate idiom the LN intends; the `Sym2` quotient lives
--   *inside* the body, hidden from every downstream binary call.
--   That keeps the LN-to-Lean mapping syntactically uniform across
--   items 2–7 of this row (each is a binary predicate over two
--   named vertices) without re-litigating the `Sym2` choice at every
--   `huh` site.
--
-- *Irreflexivity is *not* part of `huh`.*  `G.hL_irrefl` lives on
--   the `CDMG` structure and is now phrased as `¬ s.IsDiag` (Mathlib's
--   canonical "this unordered pair is a self-pair" predicate).
--   `G.huh v v → False` follows from `hL_irrefl` plus the basic
--   `Sym2` fact `(s(v, v)).IsDiag` (a one-line invocation of
--   `Sym2.diag_isDiag` / `Sym2.IsDiag.mk` from Mathlib).  Bundling
--   irreflexivity into `huh` itself would obscure the distinction
--   between "is in `L`" (data) and "self-loops excluded" (axiom);
--   keeping them separate keeps the LN-to-Lean mapping faithful.
--
-- *Downstream `Sym2`-API consumers.*  `def_3_4` typed `WalkStep`'s
--   `.bidir` constructor stores an `s(u, v) ∈ G.L` witness directly;
--   walk reversal trades the constructor's order with no `hL_symm`
--   appeal.  `def_3_5`'s `Sib^G(v) := {w | v \huh w \in G}` threads
--   through `Sym2.lift` / `Sym2.mk` to enumerate siblings.
--   `def_3_10`'s `L_{do(W)} := L \ {v \huh w | v ∈ G, w ∈ W}` and
--   `def_3_11`'s split-graph `L`-rewriting both rewrite `huh` edges
--   via `Finset.filter` / `Finset.image` over `Sym2 Node`.  The
--   `Sym2` boilerplate at L-manipulation sites is the explicit price
--   of the orientation-free encoding; the structural symmetry that
--   `huh` now enjoys is the payoff.
-- def_3_2 -- start statement
def refactor_huh (G : refactor_CDMG Node) (v1 v2 : Node) : Prop := s(v1, v2) ∈ G.L
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: huh

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: suh (was: refactor_suh)
-- ref: def_3_2 (item 5) — refactor
--
-- Star-head edge `v1 *→ v2` in `G`: `G.suh v1 v2` is the disjunction
-- `G.tuh v1 v2 ∨ G.huh v1 v2`, i.e. an arrowhead at `v2` and either
-- an arrowhead or a tail at `v1`.
/-
LN tex (item 5 of `not-cdmg`):

  $v_1 \suh v_2 \in G \;:\Longleftrightarrow\;
  \bigl(v_1 \tuh v_2 \in G\bigr) \,\lor\, \bigl(v_1 \huh v_2 \in G\bigr)$,
  equivalently $(v_1, v_2) \in E \,\lor\, (v_1, v_2) \in L$.
-/
-- ## Design choice
--
-- *Why the literal `tuh ∨ huh`, not a derived predicate over
--   `E ∪ L`.*  The LN's "the star stands for `arrowhead or tail`"
--   rule, applied to `\suh` (star on the left, head on the right),
--   produces exactly two cases — `\tuh` (tail-head) and `\huh`
--   (head-head) — and the LN enumerates exactly those two.
--   Mirroring that disjunction literally is what makes case analysis
--   on `G.suh v1 v2` reduce to `obtain h | h := h`.  A "merged"
--   version like `(v1, v2) ∈ G.E ∪ G.L` is now also *ill-typed*:
--   `G.E : Finset (Node × Node)` and `G.L : Finset (Sym2 Node)` live
--   over different carriers, so their union is not even formed.
--   Even with type-bridging, the merged form would lose the LN's
--   two-case decomposition.  (Addition
--   `[edge_set_disjointness_under_specified]` in the `def_3_1` design
--   block records that the type-level disjointness between `E` and
--   `L` is *carrier-level only*; the underlying vertex-pair
--   admissibility is unchanged.)
--
-- *Why `def`, not `abbrev`.*  An `abbrev` would auto-unfold to the
--   `tuh ∨ huh` body at every elaboration site, eliminating the
--   named abstraction the LN introduces.  The LN treats `\suh` as a
--   named relation (it reappears under that name in `def_3_3`'s
--   "into-`v_2`" classification and in `def_3_4` collider-walk
--   endpoint constraints), not as a shorthand for its two cases.
--   The formalization preserves that: downstream proofs that *want*
--   the disjunction explicit invoke `unfold refactor_CDMG.suh` or
--   `simp only [refactor_CDMG.suh]` on demand, while other proofs can
--   carry `G.suh v1 v2` opaquely.  Same rationale as `tuh` (item 2
--   above) but here the abstraction has explicit logical content (a
--   disjunction), so the elaboration-time cost of an over-eager
--   `abbrev` would be more visible.
--
-- *Why a `Prop`-level `Or`, not a `Bool`-valued
--   `decide`-friendly function.*  A `Bool`-coded
--   `def suh (G) (v1 v2) : Bool := (G.tuh v1 v2 : Bool) ||
--   (G.huh v1 v2 : Bool)` was considered and rejected.  `suh`'s
--   downstream consumers are mathematical case-analyses
--   (`obtain h_tuh | h_huh := h_suh`, `rcases h_suh with h_tuh |
--   h_huh`), not boolean dispatch — they reason about which
--   disjunct *holds* propositionally, not which boolean *evaluates*
--   to `true`.  A `Bool` encoding would force every consumer to
--   thread `Bool.or_eq_true_iff` (or `decide_eq_true_iff`) at the
--   case-split site to reconstruct the propositional disjunction
--   that the LN already speaks in.  Conversely, `Or` carries no
--   computational baggage: it never forces `Decidable` synthesis,
--   it case-splits with `Or.elim` / `rcases` / `obtain` directly,
--   and it composes with `↔` rewrites and `simp` lemmas on the
--   nose.  The `suh` predicate has no runtime use site that needs
--   to *compute* its value as a `Bool` — every consumer is a proof
--   manipulating it as a `Prop`.
--
-- *Symmetry propagation from `huh`.*  The `huh` disjunct is now
--   *structurally* symmetric (consequence of the `Sym2` swap
--   quotient: `s(v1, v2) = s(v2, v1)` by `rfl` after unfolding).  The
--   `tuh` disjunct is *not* symmetric.  So `G.suh v1 v2` and
--   `G.suh v2 v1` are logically different in general (the former
--   requires `v1 \tuh v2` or `v1 \huh v2`; the latter requires
--   `v2 \tuh v1` or `v2 \huh v1 ≡ v1 \huh v2`).  The matched-pair
--   identity is `G.suh v1 v2 ↔ G.hus v2 v1`, used as a one-line lemma
--   by consumers that need it.
--
-- *Why the body uses `G.refactor_tuh` / `G.refactor_huh`, not
--   `G.tuh` / `G.huh`.*  Pre-cleanup, the namespace contains the
--   `refactor_*`-prefixed copies of items 2 and 4.  Dot-notation
--   `G.refactor_tuh` / `G.refactor_huh` resolves in
--   `refactor_CDMG.refactor_tuh` / `refactor_CDMG.refactor_huh`,
--   matching the names defined just above.  After Phase 7 cleanup
--   strips the `refactor_` prefix globally, the body reads
--   `G.tuh v1 v2 ∨ G.huh v1 v2` — identical to the original.
--
-- *Downstream consumers.*  `def_3_3` item 2's "edges of the form
--   `v_1 \tuh v_2` or `v_1 \huh v_2` are called into `v_2`" is the
--   same shape (read with arguments swapped); `def_3_4`'s collider-
--   walk endpoint constraint `a_0 = v_0 \suh v_1` pattern-matches
--   directly; `def_3_5`'s d-Markov-blanket commented-out form uses
--   `\suh`; `claim_3_2` (acyclic ⟺ topological order) does not need
--   `suh` directly but `def_3_6` acyclicity is stated over `tuh`-only
--   walks.
-- def_3_2 -- start statement
def refactor_suh (G : refactor_CDMG Node) (v1 v2 : Node) : Prop :=
  G.refactor_tuh v1 v2 ∨ G.refactor_huh v1 v2
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: suh

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: hus (was: refactor_hus)
-- ref: def_3_2 (item 6) — refactor
--
-- Head-star edge `v1 ←* v2` in `G`: `G.hus v1 v2` is the disjunction
-- `G.hut v1 v2 ∨ G.huh v1 v2`, i.e. an arrowhead at `v1` and either
-- an arrowhead or a tail at `v2`.
/-
LN tex (item 6 of `not-cdmg`):

  $v_1 \hus v_2 \in G \;:\Longleftrightarrow\;
  \bigl(v_1 \hut v_2 \in G\bigr) \,\lor\, \bigl(v_1 \huh v_2 \in G\bigr)$,
  equivalently $(v_2, v_1) \in E \,\lor\, (v_1, v_2) \in L$.
-/
-- ## Design choice
--
-- *Mirror of `suh`.*  `hus` is the LN's "into `v_1`" relation, where
--   `suh` was "into `v_2`".  Same two-disjunct shape, only the
--   directed half is `hut` (arrow pointing at `v_1`) rather than
--   `tuh` (arrow pointing at `v_2`).
--
-- *Why `def`, not `abbrev`.*  Same rationale as `suh` (item 5
--   above): the LN treats `\hus` as a named relation, not as
--   shorthand for `\hut ∨ \huh`.  An `abbrev` would over-eagerly
--   unfold to the disjunction at every elaboration site, erasing the
--   abstraction.  Downstream proofs unfold on demand.
--
-- *Why a `Prop`-level `Or`, not a `Bool`-valued function.*  Same
--   rationale as `suh` (item 5 above): downstream consumers do
--   `rcases` / `obtain` propositional case-splits on which disjunct
--   *holds*, never a runtime `Bool` dispatch on which evaluates to
--   `true`.  A `Bool`-coded encoding would force every consumer
--   through `Bool.or_eq_true_iff` (or `decide_eq_true_iff`) to
--   recover the propositional disjunction that is the LN's intended
--   form.  `Or` keeps `hus` purely `Prop`-level with no `Decidable`
--   plumbing imposed on consumers — every `Decidable` instance can
--   still be derived locally when needed (`Finset` membership is
--   decidable, so `Decidable (G.hus v1 v2)` is one Mathlib lemma
--   away whenever a consumer needs it).
--
-- *Symmetry propagation.*  The `huh` disjunct is structurally
--   symmetric under the `Sym2` swap quotient (see item 4 above).  So
--   `G.hus v1 v2 ↔ G.suh v2 v1` holds by combining `hut`/`tuh`
--   reversal with the now-definitional `huh` symmetry — a one-line
--   corollary, not part of the def.
--
-- *Why the body uses `G.refactor_hut` / `G.refactor_huh`, not
--   `G.hut` / `G.huh`.*  Pre-cleanup, the namespace contains the
--   `refactor_*`-prefixed copies of items 3 and 4; dot-notation
--   resolves there.  Phase 7 cleanup strips the prefix globally.
--
-- *Downstream consumers.*  `def_3_3` item 2's "edges of the form
--   `v_1 \hut v_2` or `v_1 \huh v_2` are called into `v_1`" is
--   exactly this; `def_3_4`'s walk-into-`v_n` predicate uses `\suh`
--   on the last edge while walk-into-`v_0` uses `\hus`; `def_3_4`'s
--   collider walk has `a_{n-1} = v_{n-1} \hus v_n` for the closing
--   half-edge; `def_3_4`'s bifurcation has `v_{k-1} \hus v_k` as the
--   middle "tip" edge.
-- def_3_2 -- start statement
def refactor_hus (G : refactor_CDMG Node) (v1 v2 : Node) : Prop :=
  G.refactor_hut v1 v2 ∨ G.refactor_huh v1 v2
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: hus

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: sus (was: refactor_sus)
-- ref: def_3_2 (item 7) — refactor
--
-- Star-star (adjacency) edge `v1 *−* v2` in `G`: `G.sus v1 v2` is
-- the three-disjunct relation
-- `G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2`.  This is the "any edge
-- type" predicate used to define adjacency.
/-
LN tex (item 7 of `not-cdmg`):

  $v_1 \sus v_2 \in G \;:\Longleftrightarrow\;
  \bigl(v_1 \tuh v_2 \in G\bigr) \,\lor\, \bigl(v_1 \hut v_2 \in G\bigr)
  \,\lor\, \bigl(v_1 \huh v_2 \in G\bigr)$,
  equivalently $(v_1, v_2) \in E \,\lor\, (v_2, v_1) \in E \,\lor\,
  (v_1, v_2) \in L$.
-/
-- ## Design choice
--
-- *Three disjuncts, not four — the `tut` case is excluded by CDMG
--   definition.*  Per addition
--   `[sus_omits_tail_tail_despite_star_eq_head_or_tail]`, the
--   placeholder rule "the star stands for arrowhead or tail" would
--   mechanically suggest four cases for the compound `\sus`:
--     tail-tail  (`\tut`, undirected)
--     tail-head  (`\tuh`)
--     head-tail  (`\hut`)
--     head-head  (`\huh`)
--   But CDMGs admit only directed (`E`) and bidirected (`L`) edges;
--   there is no tail-tail / undirected edge type.  The LN therefore
--   correctly enumerates three disjuncts and the operator clarifies
--   the missing `\tut` is excluded by definition, not by oversight.
--   Any case analysis on `G.sus v1 v2` downstream is exhaustive over
--   exactly these three alternatives.
--
-- *Working-phase wording-check cross-reference
--   `star_placeholder_omits_tail_tail_in_sus`.*  The LN-critic
--   working-phase wording report registered exactly this tension —
--   the meta-rule "star = arrowhead or tail" predicts four
--   left/right combinations, but the enumeration lists only three —
--   as a documented subtlety of the LN block.  The report's
--   resolution is the same as the operator's
--   `[sus_omits_tail_tail_despite_star_eq_head_or_tail]` addition:
--   the fourth case is *semantically vacuous* for CDMG (no edge
--   type carries two tails), so the three-disjunct enumeration is
--   correct for CDMG even though it diverges from a literal
--   placeholder-expansion of the meta-rule.  This Lean encoding
--   tracks the enumeration literally (three disjuncts), not the
--   meta-rule (which would suggest defining `sus` via a four-case
--   `match` over a `Star` inductive with one vacuous arm); the
--   addition is the load-bearing clarification.
--
-- *Refactor warning — keep in sync if CDMGs ever gain a tail-tail
--   edge type.*  If a future revision of `def_3_1` adds a fourth
--   edge field (e.g. `T : Finset (Sym2 Node)` for undirected
--   `\tut` edges), this `sus` def MUST be updated to add the
--   corresponding `G.tut v1 v2` disjunct, and every downstream
--   proof that case-analyses `G.sus` (currently assumed exhaustive
--   over three cases) becomes incomplete and must be revisited.
--   The `addition_to_the_LN` clause referenced above is the
--   load-bearing reason these proofs are sound today; surface this
--   comment at refactor time so the exhaustiveness contract is
--   renegotiated explicitly rather than silently broken.
--
-- *Disjunction order matches the LN.*  `tuh ∨ hut ∨ huh`, in that
--   left-to-right order, mirrors item 7 of the tex block verbatim.
--   Reordering (e.g. `tuh ∨ huh ∨ hut`) was rejected — preserving
--   the order keeps `rcases` patterns and case names in step with
--   the LN reading.
--
-- *Why `def`, not `abbrev`.*  Same rationale as `suh` / `hus` above:
--   `\sus` is a named LN relation, in particular the basis for the
--   "adjacency" predicate in `def_3_3`.  Allowing `abbrev` to
--   auto-unfold to the three-disjunct body at every use site would
--   replace each "vertices `v_1` and `v_2` are adjacent" appeal with
--   a three-way `∨` — exploding adjacency-driven proofs in
--   `def_3_3` onwards.  Downstream rcases on `sus` unfolds the
--   three cases on demand.
--
-- *Symmetry propagation.*  The `huh` disjunct is structurally
--   symmetric under the `Sym2` swap quotient (item 4).  The pair
--   `tuh ∨ hut` is *jointly* symmetric:
--   `G.tuh v1 v2 ∨ G.hut v1 v2 ↔ G.tuh v2 v1 ∨ G.hut v2 v1`
--   (reversing arguments swaps the two disjuncts).  Combined,
--   `G.sus v1 v2 ↔ G.sus v2 v1` — `sus` is a *symmetric* relation,
--   which is why `def_3_3` item 1 uses it for "adjacency".  The
--   `huh`-disjunct's symmetry contribution is now a definitional
--   `rfl` after unfolding rather than an `hL_symm` invocation; the
--   overall symmetry of `sus` reduces accordingly.
--
-- *Why the body uses `G.refactor_tuh` / `G.refactor_hut` /
--   `G.refactor_huh`, not their unprefixed counterparts.*  Pre-cleanup
--   naming convention (see items 5 and 6 above); Phase 7 cleanup
--   strips the prefix globally so the body ends up reading
--   `G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2`.
--
-- *Downstream consumers.*  `def_3_3` item 1 (adjacency: "if
--   `v_1 \sus v_2 \in G` then we call `v_1` and `v_2` adjacent in
--   `G`"); `def_3_4` walk definition's "alternating sequence of
--   adjacent nodes and edges" appeals to `sus` implicitly;
--   `def_3_4` collider-walk note "for `n=1` this reads
--   `v \sus w \in G`"; later d-/σ-separation chapters use
--   `sus`-adjacency to define "active paths" in CDMGs.
-- def_3_2 -- start statement
def refactor_sus (G : refactor_CDMG Node) (v1 v2 : Node) : Prop :=
  G.refactor_tuh v1 v2 ∨ G.refactor_hut v1 v2 ∨ G.refactor_huh v1 v2
-- def_3_2 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: sus

end refactor_CDMG

end Causality
