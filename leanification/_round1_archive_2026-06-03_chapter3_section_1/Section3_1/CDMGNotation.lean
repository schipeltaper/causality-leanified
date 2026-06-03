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

The substantive design discussion for every item lives in the comment
block immediately above its `start statement` marker; read those before
modifying the file.  Two design pillars are common to all seven:

1. **Stay literal w.r.t. the LN.**  Item 1 is a `Membership` instance
   (so that `v ∈ G` parses verbatim, with no need for a custom
   `G.Mem v` call site).  Items 2–4 unfold to the literal
   `(v1, v2) ∈ G.E` / `(v2, v1) ∈ G.E` / `(v1, v2) ∈ G.L` of the LN.
   Items 5–7 are literal `∨`-disjunctions of items 2–4.

2. **Match the LN macro names.**  The Lean def names (`tuh`, `hut`,
   `huh`, `suh`, `hus`, `sus`) are exactly the LN macro names, so a
   reader of the LN can grep them and find the Lean counterpart without
   a translation table.  Under the `CDMG` namespace, dot-notation
   `G.tuh v1 v2` reads like `$v_1 \tuh v_2 \in G$` from left to right.

Two operator clarifications from `addition_to_the_LN` shape items 5–7:

* `[sus_omits_tail_tail_despite_star_eq_head_or_tail]` — `sus` is the
  three-disjunct `tuh ∨ hut ∨ huh`, not the four-disjunct `tuh ∨ hut
  ∨ huh ∨ tut` that the placeholder rule would suggest.  CDMGs have no
  tail-tail edge type, so the missing `tut` case is excluded by
  definition, not by oversight.  Any case-analysis on `G.sus v1 v2`
  downstream may treat the three listed disjuncts as exhaustive.
* `[huh_visual_symmetry_vs_ordered_pair_in_L]` — `huh` is symmetric in
  its two arguments as a *graph-theoretic* relation, because `CDMG`'s
  `hL_symm` field forces `(v1, v2) ∈ L ↔ (v2, v1) ∈ L`.  The Lean
  definition is *literally* `(v1, v2) ∈ G.L` (asymmetric in shape), and
  the symmetry is a consequence of `hL_symm` rather than baked into the
  definition.  This propagates to `suh`, `hus`, `sus`, whose `huh`
  disjuncts inherit the same property.

No `notation` macros are introduced here (see the per-item design notes
for why).  Downstream chapter-3 rows (`def_3_3` edge relations,
`def_3_4` walks, `def_3_5` family relationships, `def_3_6` acyclicity,
`def_3_10` hard intervention, `def_3_11` node splitting) pattern-match
on `G.tuh / G.hut / G.huh / G.suh / G.hus / G.sus` via plain
dot-notation.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

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
--   and at every downstream use site (`def_3_5`'s `Pa^G(v) := {w ∈ G
--   | w → v ∈ G}`, `def_3_4`'s walk endpoint constraints `v, w ∈ G`,
--   the `v_1 \tuh v_2 \in G` phrasing of items 2–7 below).  A plain
--   `def` would force every consumer to write `G.Mem v` or
--   `CDMG.Mem G v`, neither of which mirrors the LN.  Lean's
--   `Membership` typeclass dispatches `∈` to our `mem` function, so
--   `v ∈ G` becomes the literal Lean text downstream — no notation
--   macro needed, no name clash with mathlib's `∈`.
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
--   (e.g.  `def_3_10` hard intervention rewriting `V \ W` to `J ∪ W`)
--   invoke `hJV_disj` directly at the use site.
--
-- *Downstream consumers.*  Every later row that quantifies over
--   "vertices of `G`" uses `v ∈ G`: `def_3_3` (adjacency), `def_3_4`
--   (walk endpoint membership), `def_3_5` (every family set is `{w ∈
--   G | …}`), `def_3_6` (acyclicity: "for any node `v ∈ G`"),
--   `def_3_7` onwards (CDMG-type predicates).  Making this an
--   `instance` rather than a `def` is what lets all those use sites
--   read verbatim from the LN.
-- def_3_2 -- start statement
instance instMembership : Membership Node (CDMG Node) where
  mem G v := v ∈ G.J ∪ G.V
-- def_3_2 -- end statement

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
--   exactly like the LN's `$v_1 \tuh v_2 \in G$`.  A unicode `notation
--   v1 →ᵍ v2` macro was considered and rejected: it would either need
--   the graph `G` baked in (creating a `notation3` with a graph slot)
--   or be parameterless and lose the graph context.  An `abbrev` was
--   rejected because we want stable rewriting behaviour — downstream
--   proofs in `def_3_3 / def_3_4 / def_3_6 / claim_3_2` `unfold
--   CDMG.tuh` to reach the underlying `Finset` membership only when
--   they need to; an `abbrev` would always unfold and could mask
--   intent.
--
-- *Why `(v1, v2) ∈ G.E`, not `Prod.mk v1 v2 ∈ G.E` or a custom
--   pair type.*  `CDMG.E : Finset (Node × Node)` (see `CDMG.lean`),
--   so `(v1, v2)` is the literal element of `G.E` — same syntax as the
--   LN's `(v_1, v_2) \in E`.  Switching to a sum-of-edge-types ADT
--   was rejected at the `def_3_1` design stage (see the design block
--   in `CDMG.lean`).
--
-- *Downstream consumers.*  `def_3_5`'s `Pa^G(v) := {w | w \tuh v \in
--   G}` and `Ch^G(v) := {w | v \tuh w \in G}` pattern-match on this;
--   `def_3_4`'s walk-edge case `a_k = (v_k, v_{k+1}) \in E` is the
--   same membership, just spelled differently; `def_3_6`'s
--   non-trivial directed walk uses chains of `tuh`; `def_3_10` hard
--   intervention's `E_{do(W)} := E \ {v → w | v ∈ G, w ∈ W}` rewrites
--   `tuh` edges in bulk.
-- def_3_2 -- start statement
def tuh (G : CDMG Node) (v1 v2 : Node) : Prop := (v1, v2) ∈ G.E
-- def_3_2 -- end statement

-- ref: def_3_2 (item 3)
--
-- Backwards directed edge `v1 ← v2` in `G`: `G.hut v1 v2` unfolds to
-- `(v2, v1) ∈ G.E` — the directed-edge finset is the same `G.E` as for
-- `tuh`, only the argument order is swapped.  So `G.hut v1 v2` and
-- `G.tuh v2 v1` are definitionally equal.
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
--   surface form; the definitional equality `G.hut v1 v2 = G.tuh v2
--   v1` is then a one-line lemma any consumer can use.
--
-- *Why not `def hut := tuh ∘ swap` (or any composition-style spelling).*
--   A direct `def hut (G) (v1 v2) := (v2, v1) ∈ G.E` keeps unfolding
--   behaviour predictable: `simp only [CDMG.hut]` lands on the literal
--   `Finset` membership, no intermediate `Function.comp` or `Prod.swap`
--   to peel off.  A composition spelling would force every consumer to
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
-- *Downstream consumers.*  `def_3_3` item 3 ("edges of the form `v_1
--   \tuh v_2` or `v_2 \hut v_1` are out of `v_1`") matches on `hut`;
--   `def_3_4` walk's `a_k = (v_{k+1}, v_k) \in E` is `G.hut v_k
--   v_{k+1}` after rewriting; `def_3_4` collider-walk and bifurcation
--   patterns use `hut` for the "incoming-from-the-right" half.
-- def_3_2 -- start statement
def hut (G : CDMG Node) (v1 v2 : Node) : Prop := (v2, v1) ∈ G.E
-- def_3_2 -- end statement

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
--   `hL_symm` on the `CDMG` structure (see `CDMG.lean`'s design block
--   on `[l_quotient_vs_ordered_pair_typing_inconsistent]`).  So
--   `G.huh v1 v2 → G.huh v2 v1` holds by `hL_symm`, and the iff form
--   is then a trivial corollary.  Inlining the symmetry into the `def`
--   (e.g. `(v1, v2) ∈ G.L ∨ (v2, v1) ∈ G.L`) was rejected: it would
--   make `huh` and the underlying `L`-membership lemmas drift apart,
--   forcing every `def_3_1`-level `hL_symm` invocation to also rewrite
--   through `huh`.
--
-- *Why `(v1, v2) ∈ G.L`, not a quotient `Quot _ / _`.*  The
--   underlying `def_3_1` design picked the ordered-pair encoding with
--   explicit symmetry (rationale in `CDMG.lean`), and `huh` simply
--   echoes that choice.  Using a quotient here would require
--   `Quot.mk` at the use site every time.  A welcome side effect:
--   because `G.L : Finset (Node × Node)` is a plain `Finset`, all
--   mathlib `Finset` machinery — `Finset.card` (counting bidirected
--   edges), `Finset.filter` / `Finset.image` (selecting / projecting
--   sub-relations), `Finset.union` / `Finset.inter` / `Finset.sdiff`
--   (set algebra for `def_3_10` / `def_3_11` edge-rewriting), and the
--   auto-derived `DecidableMem` — lift to `huh` with zero glue.  A
--   `Quot` encoding would have surrendered most of that machinery and
--   forced bespoke lifts at every use site.
--
-- *Irreflexivity is *not* part of `huh`.*  `G.hL_irrefl` lives on the
--   `CDMG` structure and is exposed by `huh` indirectly: `G.huh v v →
--   False` follows from `hL_irrefl`.  Bundling irreflexivity into
--   `huh` itself would obscure the distinction between "is in `L`"
--   (data) and "self-loops excluded" (axiom).
--
-- *Downstream consumers.*  `def_3_4` bidirected walk uses chains of
--   `huh`; `def_3_5`'s `Sib^G(v) := {w | v \huh w \in G}` pattern-
--   matches on this; `def_3_5`'s district relation uses bidirected
--   walks built from `huh`; `def_3_10`'s `L_{do(W)} := L \ {v \huh w
--   | v ∈ G, w ∈ W}` and `def_3_11`'s split-graph `L`-rewriting both
--   rewrite `huh` edges.
-- def_3_2 -- start statement
def huh (G : CDMG Node) (v1 v2 : Node) : Prop := (v1, v2) ∈ G.L
-- def_3_2 -- end statement

-- ref: def_3_2 (item 5)
--
-- Star-head edge `v1 *→ v2` in `G`: `G.suh v1 v2` is the disjunction
-- `G.tuh v1 v2 ∨ G.huh v1 v2`, i.e. an arrowhead at `v2` and either an
-- arrowhead or a tail at `v1`.
/-
LN tex (item 5 of `not-cdmg`):

  $v_1 \suh v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$ or
  $v_1 \huh v_2 \in G$.
-/
-- ## Design choice
--
-- *Why the literal `tuh ∨ huh`, not a derived predicate over `E ∪ L`.*
--   The LN's "the star stands for `arrowhead or tail`" rule, applied
--   to `\suh` (star on the left, head on the right), produces exactly
--   two cases — `\tuh` (tail-head) and `\huh` (head-head) — and the
--   LN enumerates exactly those two.  Mirroring that disjunction
--   literally is what makes case analysis on `G.suh v1 v2` reduce to
--   `obtain h | h := h`.  A "merged" version like `(v1, v2) ∈ G.E ∪
--   G.L` was rejected because `E` and `L` are *not* disjoint as
--   subsets of `Node × Node` (see `[edge_set_disjointness_under_
--   specified]` in `CDMG.lean`'s design block): the same ordered
--   pair `(v, w)` may belong to both, and the merged form would lose
--   the LN's two-case decomposition.
--
-- *Symmetry propagation from `huh`.*  Per `[huh_visual_symmetry_vs_
--   ordered_pair_in_L]`, the `huh` disjunct of `suh` is symmetric in
--   its two arguments (consequence of `hL_symm`).  The `tuh` disjunct
--   is *not* symmetric.  So `G.suh v1 v2` and `G.suh v2 v1` are
--   logically different in general (the former requires `v1 \tuh v2`
--   or `v1 \huh v2`; the latter requires `v2 \tuh v1` or `v2 \huh v1
--   ≡ v1 \huh v2`).
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
def suh (G : CDMG Node) (v1 v2 : Node) : Prop :=
  G.tuh v1 v2 ∨ G.huh v1 v2
-- def_3_2 -- end statement

-- ref: def_3_2 (item 6)
--
-- Head-star edge `v1 ←* v2` in `G`: `G.hus v1 v2` is the disjunction
-- `G.hut v1 v2 ∨ G.huh v1 v2`, i.e. an arrowhead at `v1` and either an
-- arrowhead or a tail at `v2`.
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
-- *Symmetry propagation.*  Per `[huh_visual_symmetry_vs_ordered_pair_
--   in_L]`, the `huh` disjunct is symmetric.  So `G.hus v1 v2 ↔ G.suh
--   v2 v1` holds by combining `hut`/`tuh` reversal with `huh`
--   symmetry — a one-line corollary, not part of the def.
--
-- *Downstream consumers.*  `def_3_3` item 2's "edges of the form
--   `v_1 \hut v_2` or `v_1 \huh v_2` are called into `v_1`" is
--   exactly this; `def_3_4`'s walk-into-`v_n` predicate uses `\suh`
--   on the last edge while walk-into-`v_0` uses `\hus`; `def_3_4`'s
--   collider walk has `a_{n-1} = v_{n-1} \hus v_n` for the closing
--   half-edge; `def_3_4`'s bifurcation has `v_{k-1} \hus v_k` as the
--   middle "tip" edge.
-- def_3_2 -- start statement
def hus (G : CDMG Node) (v1 v2 : Node) : Prop :=
  G.hut v1 v2 ∨ G.huh v1 v2
-- def_3_2 -- end statement

-- ref: def_3_2 (item 7)
--
-- Star-star (adjacency) edge `v1 *−* v2` in `G`: `G.sus v1 v2` is the
-- three-disjunct relation `G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2`.
-- This is the "any edge type" predicate used to define adjacency.
/-
LN tex (item 7 of `not-cdmg`):

  $v_1 \sus v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$ or
  $v_1 \hut v_2 \in G$ or $v_1 \huh v_2 \in G$.
-/
-- ## Design choice
--
-- *Three disjuncts, not four — the `tut` case is excluded by CDMG
--   definition.*  Per addition `[sus_omits_tail_tail_despite_star_eq_
--   head_or_tail]`, the placeholder rule "the star stands for
--   arrowhead or tail" would mechanically suggest four cases for the
--   compound `\sus`:
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
--   corresponding `G.tut v1 v2` disjunct, and every downstream proof
--   that case-analyses `G.sus` (currently assumed exhaustive over
--   three cases) becomes incomplete and must be revisited.  The
--   `addition_to_the_LN` clause referenced above is the load-bearing
--   reason these proofs are sound today; surface this comment at
--   refactor time so the exhaustiveness contract is renegotiated
--   explicitly rather than silently broken.
--
-- *Disjunction order matches the LN.*  `tuh ∨ hut ∨ huh`, in that
--   left-to-right order, mirrors item 7 of the tex block verbatim.
--   Reordering (e.g. `tuh ∨ huh ∨ hut`) was rejected — preserving the
--   order keeps `rcases` patterns and case names in step with the LN
--   reading.
--
-- *Symmetry propagation.*  Per `[huh_visual_symmetry_vs_ordered_pair_
--   in_L]`, the `huh` disjunct is symmetric.  The pair `tuh ∨ hut` is
--   *jointly* symmetric: `G.tuh v1 v2 ∨ G.hut v1 v2 ↔ G.tuh v2 v1 ∨
--   G.hut v2 v1` (reversing arguments swaps the two disjuncts).
--   Combined, `G.sus v1 v2 ↔ G.sus v2 v1` — `sus` is a *symmetric*
--   relation, which is why `def_3_3` item 1 uses it for "adjacency".
--   The symmetry is again a corollary, not part of the def.
--
-- *Downstream consumers.*  `def_3_3` item 1 (adjacency: "if `v_1
--   \sus v_2 \in G` then we call `v_1` and `v_2` adjacent in `G`");
--   `def_3_4` walk definition's "alternating sequence of adjacent
--   nodes and edges" appeals to `sus` implicitly; `def_3_4`
--   collider-walk note "for `n=1` this reads `v \sus w \in G`";
--   later d-/σ-separation chapters use `sus`-adjacency to define
--   "active paths" in CDMGs.
-- def_3_2 -- start statement
def sus (G : CDMG Node) (v1 v2 : Node) : Prop :=
  G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2
-- def_3_2 -- end statement

end CDMG

end Causality
