import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations
import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Family relationships in CDMGs (`def_3_5`)

This file formalises the eight family-relationship operators of the LN
definition block `def_3_5` (`\label{def:family-relationships}` in
`graphs.tex`).  The block introduces, for a CDMG `G = (J, V, E, L)`, a
vertex `v ∈ J ∪ V`, and a subset `A ⊆ J ∪ V`:

* `Pa G v` / `PaSet G A` — parents.
* `Ch G v` / `ChSet G A` — children.
* `Sib G v` — siblings (per-vertex only; the LN does not define a set form).
* `Anc G v` / `AncSet G A` — ancestors.
* `Desc G v` / `DescSet G A` — descendants.
* `NonDesc G A` — non-descendants (set form only; the LN does not define
  a per-vertex form).
* `Sc G v` / `ScSet G A` — strongly connected component(s).
* `Dist G v` / `DistSet G A` — district(s).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_5_FamilyRelationships.tex`,
verified equivalent to the LN block augmented with three operator
clarifications:

* `[self_membership_notes_require_length_zero_walks]` — the self-membership
  notes `v ∈ Anc G v`, `v ∈ Desc G v`, `v ∈ Sc G v`, `v ∈ Dist G v` hold
  unconditionally because the length-0 trivial walk at `v` (admitted by
  `Walks.Walk.nil`, `def_3_4` item i) witnesses each.
* `[type_mismatch_individual_vs_set_versions]` — the per-vertex forms
  range over `v ∈ J ∪ V` (not just `v ∈ V`); the set forms are then
  well-typed for `A ⊆ J ∪ V`.
* `[district_walk_indexing_ambiguous_for_small_n]` — `w ∈ Dist G v` iff
  there exists a (length `≥ 0`) bidirected walk from `v` to `w`; the LN's
  indexed display `v ↔ v₁ ↔ ⋯ ↔ vₙ₋₁ ↔ w` is syntactic sugar with no lower
  bound on length.

The per-vertex form is the primitive in every case; the set form is the
indexed union over `v ∈ A`.  Self-membership in `Anc / Desc / Sc / Dist`
falls out from `Walk.nil` being a directed (resp. bidirected) walk
vacuously (`Walks.Walk.IsDirectedWalk` / `IsBidirectedWalk` return `True`
on `nil`) — no `∪ {v}` patch is added on top of the walk-based
definition.

## Section-wide design choices (apply to every declaration below)

* **`Set Node`-valued, not `Finset Node`-valued.** Three of the eight
  operators (`Anc`, `Desc`, `Dist`) are defined by *existence of a walk*,
  which is not immediately decidable on a general CDMG (the walk
  inductive `def_3_4` ranges over arbitrary lengths even though the node
  set is finite — a uniform decidability proof needs a separate cycle /
  bound argument).  Picking `Set Node` for the entire family keeps the
  API uniform: every operator returns the same carrier, every Boolean
  algebra identity (`Pa(A ∪ B) = Pa A ∪ Pa B`, `NonDesc = (J ∪ V) \
  Desc`, `Sc = Anc ∩ Desc`) lands inside Mathlib's `Set` API with no
  `Finset.coe` round-trips.  Downstream finiteness lemmas — every family
  set is contained in `(G.J ∪ G.V : Finset Node) : Set Node` and is
  therefore finite by transfer — are proved separately as the chapter
  needs them, rather than being forced into the type now.  A `Finset`
  alternative was rejected: it would have demanded a `Decidable` proof
  for the walk-existence predicate at the definition site, and threading
  that decidability instance into every later use of `Anc` / `Desc` /
  `Dist` (or proving it pointwise via reachability bounds) is exactly
  the work this `Set`-valued primitive defers to the point of use.

* **`Pa G v` and friends are *per-vertex* primitives; the set form is
  the indexed union `⋃ v ∈ A, Pa G v`.**  The LN consistently builds set
  forms by union over the per-vertex form (see addition
  `[type_mismatch_individual_vs_set_versions]`).  Keeping the same
  layering in Lean means downstream proofs can lift the LN's algebraic
  identities directly via `Set.biUnion_union`, `Set.biUnion_mono`,
  `Set.biUnion_singleton` and the rest of Mathlib's biUnion API, with no
  custom set-form lemmas needed.  Inverting the primitive (defining the
  set form first, then the per-vertex form as `Pa G {v}`) would force
  every per-vertex use site to peel off a singleton biUnion.

* **The per-vertex forms range over `v ∈ J ∪ V`, not `v ∈ V`** (LN
  addition `[type_mismatch_individual_vs_set_versions]`).  The LN's
  preamble `v, w ∈ V` is *too narrow* to type-check the set forms `Pa
  G(A) := ⋃_{v ∈ A} Pa G(v)` for `A ⊆ J ∪ V`; the rewritten tex spec
  fixes this by uniformly admitting `v ∈ J ∪ V` for every per-vertex
  operator.  The CDMG axiom `hE_subset : e ∈ E → e.1 ∈ J ∪ V ∧ e.2 ∈ V`
  ensures input nodes have empty `Pa` / `Anc` (no edge ends at them, no
  directed walk reaches them from another node) — but the *definitions*
  remain well-typed regardless.  In Lean we don't carry a `v ∈ G`
  hypothesis on the function argument: the set-builder body already
  conjoins `w ∈ G` on the *output* side, so out-of-graph `v` simply
  return the empty set (or, in `Anc G v` / `Desc G v` / `Dist G v`, the
  singleton `{v}` if walks at out-of-graph vertices ever existed — they
  do not, because `Walk.nil` requires `v ∈ G`).
-/

namespace CDMG

-- def_3_5 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_5 --- end helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Pa
-- ref: def_3_5 (item i, parents of a vertex)
-- The set of parents of `v` in `G`: nodes `w ∈ J ∪ V` such that `(w, v) ∈ E`.
--
-- ## Design choice
--
-- *Why the LN's literal set-builder, NOT `Pa G v := { w | w ∈ G ∧ w ≠
--   v ∧ (w, v) ∈ G.E }`.*  The LN defines `Pa^G(v) := { w ∈ G | w → v
--   ∈ G }` and the source explicitly *considers and rejects* the
--   alternative `Pa^G(v) := { w | w → v ∈ G } \ {v}` in a commented-out
--   note ("maybe better for sets … but then if `v → v ∈ E` then `v ∉
--   Pa^G({v}) ≠ Pa^G(v) ∋ v`").  The LN deliberately keeps `v ∈ Pa^G(v)`
--   when a directed self-loop `(v, v) ∈ G.E` is present, precisely so
--   the singleton identity `Pa^G({v}) = Pa^G(v)` holds — i.e. so the
--   set form and per-vertex form agree on singletons.  This is the
--   load-bearing reason we do not patch out `v` from `Pa G v`; surface
--   it here so a future reader does not silently re-add `\ {v}` and
--   break the singleton identity.  Wording-check subtlety
--   `self_loop_makes_v_its_own_parent_child_sibling` documents the same
--   point.
--
-- *`w ∈ G` is on the output side, redundantly with `(w, v) ∈ G.E`.*
--   The CDMG axiom `hE_subset` already forces `e.1 ∈ J ∪ V` for every
--   `e ∈ G.E`, so the `w ∈ G` conjunct is provable from `(w, v) ∈ G.E`
--   alone.  We keep it for two reasons: (i) it mirrors the LN's `\{ w
--   \in J \cup V \mid (w, v) \in E \}` verbatim, so a reader greps the
--   tex and finds the matching Lean; (ii) downstream lemmas often
--   destructure `h : w ∈ Pa G v` as `⟨hw_mem, hw_edge⟩` and want
--   `hw_mem : w ∈ G` immediately, without an `hE_subset` invocation.
--   The redundancy is paid once at the def site, not at every use site.
--
-- *Why no decidability on `(w, v) ∈ G.E`.*  Inherited from the
--   section-wide `Set Node` choice (see preamble).  `G.E` is a `Finset`
--   so `(w, v) ∈ G.E` is decidable; consumers that need the decidable
--   form invoke `Finset.decidableMem` directly.
-- def_3_5 -- start statement
def Pa (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (w, v) ∈ G.E}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Pa

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: PaSet
-- ref: def_3_5 (item i, parents of a set)
-- The set of parents of `A` in `G`: the indexed union of `Pa G v` over `v ∈ A`.
--
-- ## Design choice
--
-- *Mathlib `⋃ v ∈ A, ...` (`Set.biUnion`), not a custom recursive
--   definition.*  The LN writes the set form as `Pa^G(A) := ⋃_{v ∈ A}
--   Pa^G(v)` — a literal indexed union over `A`, no further structure.
--   Mathlib's `Set.biUnion` is exactly this construction, and exposes
--   the algebraic identities the chapter will need: `Set.biUnion_union`
--   (`Pa(A ∪ B) = Pa(A) ∪ Pa(B)`), `Set.biUnion_mono` (monotonicity in
--   `A`), `Set.biUnion_singleton` (`Pa({v}) = Pa(v)`, which is what
--   makes the `v ∈ Pa(v)` self-loop convention from `Pa` coherent on
--   singletons — see the design note on `Pa`), `Set.mem_biUnion` for
--   case analysis.  Re-implementing this as a `Finset`-style fold or a
--   list-recursion would force re-proving each identity from scratch
--   and break compatibility with Mathlib `Set` rewriting.
--
-- *Why `A : Set Node`, not `A : Finset Node` or `A ⊆ G`.*  The LN's
--   set forms range over arbitrary `A ⊆ J ∪ V`, never restricting to
--   the finite case.  Downstream chapters that *do* require finiteness
--   (CBN factorisations over a finite ancestor set, topological orders,
--   d-separation reductions) will receive `A : Finset Node` and pass
--   `(A : Set Node)` to `PaSet G` via the `Finset → Set` coercion; the
--   `Set` definition is then strictly more general than a `Finset`
--   variant.  Requiring `A ⊆ G` was rejected: the LN's `A ⊆ J ∪ V`
--   constraint is satisfied harmlessly when violated, since
--   out-of-graph `v ∈ A` contribute `Pa G v = ∅` (see `Pa`'s design
--   note); pre-filtering would just duplicate the set-builder's `w ∈ G`
--   guard.
--
-- *Set form = union form on singletons.*  By `Set.biUnion_singleton`,
--   `PaSet G {v} = Pa G v`.  This is the singleton identity the LN
--   deliberately preserved by NOT excluding `v` from `Pa G v` when a
--   self-loop is present (see the `Pa` design note for the LN's
--   commented-out alternative).  Future consumers can use either form
--   interchangeably on singletons; the choice between `Pa G v` and
--   `PaSet G {v}` should be guided by which downstream identity is
--   handier (the per-vertex form is sharper for case analysis on `v`,
--   the set form lifts directly through `Set.biUnion_union`).
-- def_3_5 -- start statement
def PaSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Pa v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: PaSet

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Ch
-- ref: def_3_5 (item ii, children of a vertex)
-- The set of children of `v` in `G`: nodes `w ∈ J ∪ V` such that `(v, w) ∈ E`.
--
-- ## Design choice
--
-- *Same shape as `Pa G v`, with `(v, w) ∈ G.E` instead of `(w, v) ∈
--   G.E`.*  The LN treats parents and children as the two directional
--   reflections of the same underlying edge set `E`; mirroring the
--   shape in Lean means downstream proofs that establish identities for
--   one (e.g. monotonicity in the graph, behaviour under intervention)
--   transfer to the other by swapping a single argument-order.
--
-- *Self-loop convention propagates from `Pa`.*  As with `Pa`, if a
--   directed self-loop `(v, v) ∈ G.E` is present then `v ∈ Ch G v`.
--   The LN does NOT comment on this case explicitly for `Ch` (it does
--   for `Pa`), but the wording-check subtlety
--   `self_loop_makes_v_its_own_parent_child_sibling` flags that the
--   same convention applies by symmetry of the literal definition.  We
--   follow the literal LN — patching `Ch G v` to exclude `v` would
--   break the singleton identity `ChSet G {v} = Ch G v` for the same
--   reason it would break the analogous identity for `Pa` (see `Pa`'s
--   design note).  Surface here so a future reader does not silently
--   "fix" the asymmetric LN commentary.
--
-- *No alternative `Ch G v := { w | G.tuh v w }` rewriting.*  We could
--   equivalently spell the body as `{ w | w ∈ G ∧ G.tuh v w }` using
--   `def_3_2`'s notation; we keep the literal `(v, w) ∈ G.E` to mirror
--   the LN tex character-for-character.  Either form unfolds to the
--   same `Finset` membership in one step — pick `G.tuh` at the use site
--   when the proof should be `def_3_2`-named, pick the literal form
--   when it should be `Finset`-mechanical.
-- def_3_5 -- start statement
def Ch (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (v, w) ∈ G.E}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Ch

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: ChSet
-- ref: def_3_5 (item ii, children of a set)
-- The set of children of `A` in `G`: the indexed union of `Ch G v` over `v ∈ A`.
--
-- ## Design choice
--
-- *Same `Set.biUnion` shape as `PaSet`.*  See `PaSet`'s design block
--   for the full rationale; only the per-vertex primitive differs.  The
--   identity `ChSet G {v} = Ch G v` (via `Set.biUnion_singleton`) is
--   what makes the self-loop convention on `Ch G v` (see `Ch`'s design
--   note) coherent on singletons — same load-bearing reason as in `Pa`
--   / `PaSet`.
-- def_3_5 -- start statement
def ChSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Ch v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: ChSet

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Sib
-- ref: def_3_5 (item iii, siblings of a vertex)
-- The set of siblings of `v` in `G`: nodes `w ∈ J ∪ V` such that `(v, w) ∈ L`.
--
-- ## Design choice
--
-- *Mirror of `Ch` with `G.L` in place of `G.E`.*  The LN's sibling
--   relation is the bidirected analogue of the directed parent/child
--   pair: `w` is a sibling of `v` iff there is a bidirected edge `v ↔
--   w` in `G`, i.e. `(v, w) ∈ G.L`.  Same `Set Node` carrier as `Pa` /
--   `Ch`, same `w ∈ G` guard on the output side.  The CDMG axiom
--   `hL_subset : e ∈ L → e.1 ∈ V ∧ e.2 ∈ V` makes the `w ∈ G` guard
--   provable from `(v, w) ∈ G.L` alone, so the conjunct is again
--   redundant-but-kept (same rationale as in `Pa` — LN-grep parity and
--   immediate `⟨_, _⟩` destructuring at use sites).
--
-- *`v ∉ Sib G v` always, by `hL_irrefl`.*  Unlike the directed self-
--   loop convention for `Pa` / `Ch`, `Sib G v` cannot contain `v`: the
--   CDMG structure field `hL_irrefl : (v, v) ∈ G.L → False` (see
--   `CDMG.lean`'s design note on `hL_irrefl`) rules out bidirected
--   self-loops.  The surface shape of the def *looks* like it could
--   admit `w = v` — and a careless reader of the LN might think the
--   self-loop subtlety from `Pa` / `Ch` propagates here — but it does
--   not, because the CDMG axiom excludes it a priori.  Wording-check
--   subtlety `self_loop_makes_v_its_own_parent_child_sibling` flagged
--   this asymmetry; we record it here so the asymmetry is visible.
--
-- *`Sib` has NO set form in the LN, and so no `SibSet` in Lean.*  The
--   LN's def block lists per-vertex *and* set forms for every other
--   operator (Pa, Ch, Anc, Desc, Sc, Dist) but offers `Sib` only in
--   per-vertex form.  We mirror the asymmetry — adding `SibSet` would
--   either silently introduce a definition the LN does not have, or
--   pre-empt a downstream chapter's decision to use a different shape.
--   Future consumers that need a set-of-siblings will write `⋃ v ∈ A,
--   Sib G v` locally; the LN's algebraic identities for set forms (via
--   `Set.biUnion_union` etc.) lift transparently.
--
-- *Symmetry of the relation is graph-theoretic, not definitional.*  By
--   `hL_symm`, `w ∈ Sib G v ↔ v ∈ Sib G w` — i.e. siblinghood is
--   symmetric as a *relation on `J ∪ V`*, even though our Lean encoding
--   stores it asymmetrically as `(v, w) ∈ G.L`.  This propagates from
--   `def_3_2`'s `huh` (see its design note on
--   `[huh_visual_symmetry_vs_ordered_pair_in_L]`).  Downstream proofs
--   that need the symmetry invoke `hL_symm` directly.
-- def_3_5 -- start statement
def Sib (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (v, w) ∈ G.L}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Sib

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Anc
-- ref: def_3_5 (item iv, ancestors of a vertex)
-- The set of ancestors of `v` in `G`: nodes `w ∈ J ∪ V` for which there
-- exists a directed walk (of any length `≥ 0`, including the trivial
-- length-0 walk when `w = v`) from `w` to `v` in `G`.
--
-- ## Design choice
--
-- *Built on `def_3_4`'s `Walk G w v` + `Walk.IsDirectedWalk`
--   predicate, NOT a separate `DirectedWalk` inductive nor a custom
--   transitive closure.*  This is the design pillar (2) of
--   `Walks.lean`: the LN's "directed walk" is a *predicate on `Walk`*,
--   not its own type.  Re-using that predicate here means: (i) every
--   `Walk.nil` / `Walk.cons` case-analysis lemma we prove for plain
--   walks lifts to directed walks via the `IsDirectedWalk` hypothesis,
--   no constructor duplication; (ii) `w ∈ Anc G v` carries the *walk
--   itself*, so downstream proofs that need to extract a parent (e.g.
--   `def_3_5`'s `Pa G v ⊆ Anc G v` proof, or an induction on walk
--   length) destructure the existential and recurse on the `cons` /
--   `nil` shape.  A roll-your-own `Relation.TransGen G.tuh` was
--   considered and rejected: `TransGen` is irreflexive by default (its
--   reflexive-transitive closure `ReflTransGen` would handle the
--   self-membership note correctly), but it loses the walk-as-data we
--   actively need for downstream proofs (paths, m-separation, …),
--   forcing a re-introduction of the walk later anyway.
--
-- *Self-membership `v ∈ Anc G v` is unconditional, witnessed by
--   `Walk.nil v hv`.*  Addition
--   `[self_membership_notes_require_length_zero_walks]` makes this
--   load-bearing: the LN's note `v ∈ Anc^G(v)` must hold *regardless
--   of whether any directed self-loop at `v` exists*.  In Lean this
--   falls out of two facts from `def_3_4`: (i) `Walk.nil v hv` is a
--   legal walk for any `v ∈ G` (the constructor takes a `v ∈ G`
--   hypothesis), and (ii) `IsDirectedWalk (Walk.nil _ _) = True` by
--   the trivial-walk branch of `IsDirectedWalk`'s recursion (see
--   `Walks.lean:599-601`).  Combined, `⟨Walk.nil v hv, trivial⟩`
--   directly witnesses `v ∈ Anc G v` for any `v ∈ G`.  *No `∪ {v}`
--   patch is added on top of the walk-based definition* — the
--   self-membership note is a consequence of the `Walk`/`IsDirectedWalk`
--   conventions, not an extra constructor.
--
-- *Wording-check `trivial_walk_implicit_in_self_membership_notes`
--   resolved.*  A naive reader of the LN's pictorial walk syntax `w →
--   ⋯ → v` might think the body of `Anc^G(v)` requires at least one
--   edge, contradicting the note `v ∈ Anc^G(v)`.  Addition (1) above
--   resolves this by *globally admitting length-0 walks* in the
--   ancestor / descendant / district body, not by *adding* a `∪ {v}`
--   to the note.  Our Lean encoding makes this choice explicit and
--   verifiable: search for `Walk.nil` in this file to see the witness
--   used downstream.
--
-- *The body's `w ∈ G` guard is redundant for `w ≠ v` but required for
--   `w = v`.*  For `w ≠ v` with a non-trivial walk, the head edge of
--   the walk pins `w` to `J ∪ V` via `hE_subset`.  For the trivial walk
--   `w = v`, no edge exists and `Walk.nil`'s `hv : v ∈ G` is the only
--   source of `w ∈ G`.  Keeping the conjunct here mirrors the LN tex
--   uniformly (matching `Pa` / `Ch` / `Sib`'s shape) and avoids a
--   case-split on walk length at the def site.
-- def_3_5 -- start statement
def Anc (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : Walk G w v, p.IsDirectedWalk}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Anc

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: AncSet
-- ref: def_3_5 (item iv, ancestors of a set)
-- The set of ancestors of `A` in `G`: the indexed union of `Anc G v` over `v ∈ A`.
--
-- ## Design choice
--
-- *Same `Set.biUnion` shape as `PaSet` / `ChSet`.*  Per the
--   section-wide design preamble, every set form in this row is the
--   indexed union over the per-vertex form.  Mathlib's `Set.biUnion`
--   gives us the LN's `A ⊆ Anc^G(A)` note (item iv, trailing line) as
--   `Set.subset_biUnion_of_mem` composed with the self-membership `v ∈
--   Anc G v` from `Anc`'s design block — i.e. the set-form note is a
--   one-line consequence of the per-vertex note, no extra constructor.
--
-- *The LN's `A ⊆ Anc^G(A)` note follows from `Anc`'s self-membership,
--   unconditionally.*  Since `v ∈ Anc G v` for any `v ∈ A` (regardless
--   of self-loops; see `Anc`'s design block), and `Anc G v ⊆ AncSet G
--   A`, we get `v ∈ AncSet G A` for any `v ∈ A`, i.e. `A ⊆ AncSet G A`.
--   This is a corollary, not a separate axiom — the LN explicitly notes
--   it ("$A ⊆ Anc^G(A)$ unconditionally") and our encoding makes it
--   provable in two `Set` lemmas.
-- def_3_5 -- start statement
def AncSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Anc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: AncSet

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Desc
-- ref: def_3_5 (item v, descendants of a vertex)
-- The set of descendants of `v` in `G`: nodes `w ∈ J ∪ V` for which there
-- exists a directed walk (of any length `≥ 0`, including the trivial
-- length-0 walk when `w = v`) from `v` to `w` in `G`.
--
-- ## Design choice
--
-- *Mirror of `Anc` with the walk direction reversed: `Walk G v w`
--   instead of `Walk G w v`.*  The LN treats ancestors and descendants
--   as the two directional reflections of the same directed-walk
--   relation.  Reusing `Walk` + `IsDirectedWalk` with swapped endpoints
--   means `Anc G v` and `Desc G v` share *every* downstream lemma
--   (transitivity, monotonicity, behaviour under intervention) up to a
--   walk-reversal lemma — `Anc / Desc` are not independent design
--   surfaces.
--
-- *Self-membership `v ∈ Desc G v` is unconditional, same argument as
--   `Anc`.*  Witnessed by `⟨Walk.nil v hv, trivial⟩` (`hv : v ∈ G`).
--   Addition `[self_membership_notes_require_length_zero_walks]` is the
--   load-bearing reason; see `Anc`'s design block for the full
--   discussion.
--
-- *Why `Walk G v w`, not a separate `DirectedReachability G v w`
--   inductive.*  Same `def_3_4` reuse argument as in `Anc`: walks
--   carry data we need downstream (path extraction, length, vertex
--   list).  A reachability-only predicate would force re-introducing
--   the walk later — but `def_3_5` already needs the walk for
--   `Dist`, so the infrastructure is paid for once.
--
-- *Downstream pattern.*  `Desc G v` is the natural carrier for
--   "post-intervention support" (chapter 5 do-calculus), "topological
--   future" (chapter 6 σ-separation), and "identifiable effect set"
--   (chapter 14+ ID algorithm).  Several of those chapters intersect
--   `Desc G v` with `NonDesc G A` (item vi below), so the `Set Node`
--   carrier is what makes `Set.inter` / `Set.diff` reductions sharp.
-- def_3_5 -- start statement
def Desc (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : Walk G v w, p.IsDirectedWalk}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Desc

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: DescSet
-- ref: def_3_5 (item v, descendants of a set)
-- The set of descendants of `A` in `G`: the indexed union of `Desc G v` over `v ∈ A`.
--
-- ## Design choice
--
-- *Same `Set.biUnion` shape as `AncSet`.*  The LN's `A ⊆ Desc^G(A)`
--   note (item v, trailing line) is again a one-line consequence of
--   `Desc`'s unconditional self-membership composed with
--   `Set.subset_biUnion_of_mem` — no extra constructor needed.
--
-- *Load-bearing for `NonDesc` below.*  `NonDesc G A := (J ∪ V) \
--   DescSet G A` (item vi) uses *this* set form, not the per-vertex
--   `Desc G v`.  Keeping `DescSet` as the indexed union (rather than a
--   monolithic `{ w | ∃ v ∈ A, ∃ p : Walk G v w, p.IsDirectedWalk }`
--   spelling) lets `NonDesc` decompositions reduce via
--   `Set.compl_biUnion` / `Set.diff_biUnion` instead of a custom
--   walk-quantifier lemma.
-- def_3_5 -- start statement
def DescSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Desc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: DescSet

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: NonDesc
-- ref: def_3_5 (item vi, non-descendants of a set)
-- The set of non-descendants of `A` in `G`: the complement of `DescSet G A`
-- inside the ambient node set `J ∪ V` of `G`.
--
-- ## Design choice
--
-- *No per-vertex `NonDesc G v` form, matching the LN.*  The LN's
--   def block lists per-vertex *and* set forms for every other walk-
--   based operator (`Anc`, `Desc`, `Sc`, `Dist`), but `NonDesc` is
--   *set-only* — the LN never writes `NonDesc^G(v)`.  Wording-check
--   subtlety `nondesc_only_defined_for_sets` flagged the asymmetry:
--   `NonDesc G {v}` is the natural per-vertex form and downstream
--   consumers that want it write `NonDesc G {v}` explicitly via the
--   singleton-coercion.  Pre-defining `NonDesc G v := (J ∪ V) \ Desc G
--   v` would silently introduce a definition the LN does not have, and
--   would invite the subtle confusion that `NonDesc G v ≠ NonDesc G
--   {v}` (they ARE equal by `Set.biUnion_singleton`, but the
--   pre-defined name would obscure why).  We follow the literal LN.
--
-- *Complement is taken inside `(J ∪ V : Finset)`, NOT inside `V`
--   alone or `Set.univ`.*  The LN explicitly writes `NonDesc^G(A) :=
--   (J ∪ V) \ Desc^G(A)`.  Taking the complement inside `V` would
--   wrongly exclude input nodes from "non-descendants" — but `j ∈ J`
--   with `j ∉ Desc^G(A)` *is* a non-descendant of `A` by the LN's
--   reading (input nodes have no incoming directed edges per
--   `hE_subset`, so they sit in `NonDesc^G(A)` for any non-empty `A`
--   that does not happen to contain them).  Taking the complement
--   inside `Set.univ` would wrongly include every node of the ambient
--   `Node : Type*` (not just the CDMG's vertices) — a subtle but
--   load-bearing distinction for downstream chapters that quantify
--   over "non-descendants in `G`" rather than "non-descendants in the
--   ambient type".  Following the LN literally fixes the complement to
--   `J ∪ V`, the CDMG's vertex set.
--
-- *Coercion `((G.J ∪ G.V : Finset Node) : Set Node)`, NOT a manual
--   `{ w | w ∈ G }` set-builder.*  Both denote the same set; the
--   coercion form lifts every `Finset` lemma about `G.J ∪ G.V` (e.g.
--   `Finset.mem_union`, `Finset.union_eq_left`) to `Set` automatically
--   via `Finset.coe_union`, while the set-builder form would force
--   unfolding the `Membership` instance from `CDMGNotation.lean` at
--   every use site.  Both are LN-faithful — the LN writes `(J ∪ V) \
--   Desc^G(A)`, which is literally the `Finset` union coerced to a
--   `Set` and then `\`-ed.
--
-- *`A ⊆ (J ∪ V)` is NOT enforced at the def site.*  An `A : Set Node`
--   that escapes `J ∪ V` simply has its out-of-graph elements ignored
--   by `DescSet G A` (their `Desc G v` is empty by the `w ∈ G` guard),
--   so `NonDesc G A = (J ∪ V) \ DescSet G A` is well-typed and gives
--   the "right" answer (all of `J ∪ V` minus the actual descendants of
--   `A ∩ (J ∪ V)`).  Pre-filtering `A` was rejected as redundant.
--
-- *Downstream pattern.*  `NonDesc G A` is the *Markov-blanket complement*
--   used throughout chapters 5–8: local Markov property "every node is
--   independent of its non-descendants given its parents", do-calculus
--   rule 2 (action / observation exchange), adjustment criteria
--   (chapter 14+) all phrase their conditioning sets via `NonDesc`.
--   The `Set Node` carrier here matches the conditioning-set carrier
--   used by `def_3_7`-and-later, so the chain `NonDesc → conditioning
--   set → CI statement` lifts with no coercions.
-- def_3_5 -- start statement
def NonDesc (G : CDMG Node) (A : Set Node) : Set Node :=
  ((G.J ∪ G.V : Finset Node) : Set Node) \ G.DescSet A
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: NonDesc

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Sc
-- ref: def_3_5 (item vii, strongly connected component of a vertex)
-- The strongly connected component of `v` in `G`: the intersection of the
-- ancestors and descendants of `v` in `G`.
--
-- ## Design choice
--
-- *Literal LN formula `Anc G v ∩ Desc G v`, not a re-rolled
--   "bidirectional reachability" predicate.*  The LN defines `Sc^G(v)`
--   directly as the intersection of `Anc^G(v)` and `Desc^G(v)`; our
--   Lean encoding is the character-for-character translation, using
--   `Set.inter`.  Rolling our own "there exists a directed walk from
--   `v` to `w` and from `w` to `v`" would force a fresh existential
--   pair witness at every use site, instead of reusing the existentials
--   already inside `Anc` / `Desc` separately.  The intersection form
--   composes much better with downstream `Set.mem_inter_iff`-style
--   case analyses.
--
-- *Self-membership `v ∈ Sc G v` is a corollary, NOT a new axiom.*
--   The LN's note `v ∈ Sc^G(v)` (item vii) is *not* a separate
--   convention layered on top — it follows immediately from `v ∈ Anc
--   G v` (item iv, unconditional via `Walk.nil`) and `v ∈ Desc G v`
--   (item v, same) combined via `Set.mem_inter`.  So all the load-
--   bearing work happens in `Anc` / `Desc`'s design block (addition
--   `[self_membership_notes_require_length_zero_walks]`); `Sc` inherits
--   self-membership transparently.  Surface this here so a reader does
--   not look for a third `Walk.nil`-style witness inside `Sc` — the
--   inheritance via `Anc ∩ Desc` is the whole mechanism.
--
-- *Mathlib `Set.inter`, not a custom intersection.*  `Set.inter` is
--   the canonical Mathlib intersection; rewriting via `Set.mem_inter`,
--   `Set.inter_subset_left`, and the universal-property API is what
--   downstream chapter-3 lemmas (e.g. `Sc` is `def_3_3`-adjacent-
--   closed under `tuh`) will use.  No re-definition needed.
--
-- *Downstream pattern.*  `Sc G v` is the "strongly connected component"
--   used by chapter 3's acyclification (`def_3_6` + later), the
--   ID-algorithm's component decomposition, and the σ-AMP construction
--   of chapter 7.  Keeping it as `Anc ∩ Desc` (rather than a wider
--   bidirectional-walk closure) is what makes the LN's identity
--   `Sc^G(v) = { v }` *for acyclic G* a one-line `Anc`/`Desc` reduction.
-- def_3_5 -- start statement
def Sc (G : CDMG Node) (v : Node) : Set Node :=
  G.Anc v ∩ G.Desc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Sc

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: ScSet
-- ref: def_3_5 (item vii, strongly connected components of a set)
-- The (union of) strongly connected components of `A` in `G`: the indexed
-- union of `Sc G v` over `v ∈ A`.
--
-- ## Design choice
--
-- *Same `Set.biUnion` shape as `AncSet` / `DescSet`.*  Per the
--   section-wide design preamble.  The LN's `A ⊆ Sc^G(A)` note (item
--   vii, trailing line) follows from `v ∈ Sc G v` and
--   `Set.subset_biUnion_of_mem` — same one-line corollary pattern as
--   `AncSet` / `DescSet`.
--
-- *Note on terminology vs single-component reading.*  The LN names this
--   "the (union of) strongly connected components of `A`", explicitly
--   parenthesising "(union of)".  `ScSet G A` is the *union* of the
--   per-vertex strongly-connected components for each `v ∈ A`; it is
--   NOT a single strongly-connected component of `A` (in general no
--   such component exists when `A` straddles multiple components).
--   Downstream chapters that want the equivalence-class partition view
--   will construct it locally from `Sc G v` rather than from `ScSet G
--   A`.
-- def_3_5 -- start statement
def ScSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Sc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: ScSet

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Dist
-- ref: def_3_5 (item viii, district of a vertex)
-- The district of `v` in `G`: nodes `w ∈ J ∪ V` for which there exists a
-- bidirected walk (of any length `≥ 0`, including the trivial length-0
-- walk when `w = v`) from `v` to `w` in `G`.
--
-- ## Design choice
--
-- *Same `Walk G v w` carrier as `Anc` / `Desc`, only the predicate
--   switches from `IsDirectedWalk` to `IsBidirectedWalk`.*  This is
--   the design pillar (2) of `Walks.lean` paying off again: a single
--   `Walk` inductive carries every walk flavour the chapter needs, and
--   each flavour is a `Prop`-predicate.  A separate `BidirectedWalk`
--   inductive was rejected at the `def_3_4` design stage — see
--   `Walks.lean:604-619` for the rationale.  Reusing the same carrier
--   means downstream lemmas about walks (concatenation, reversal,
--   restriction, intervention behaviour) lift uniformly across
--   `Anc / Desc / Dist`.
--
-- *`Walk G v w` with `IsBidirectedWalk`, NOT a custom recursion
--   `v ↔ v₁ ↔ ⋯ ↔ vₙ₋₁ ↔ w`.*  The LN's pictorial display
--   "$v \huh v_1 \huh \cdots \huh v_{n-1} \huh w$" suggests an indexed
--   sequence of intermediate vertices; addition
--   `[district_walk_indexing_ambiguous_for_small_n]` clarifies this is
--   syntactic sugar for "walk all of whose edges lie in `L`", with no
--   lower bound on length.  Encoding via `Walk + IsBidirectedWalk`
--   sidesteps the indexing ambiguity entirely: `Walk.nil v hv` is a
--   walk of length 0, `Walk.cons v a h p` adds one edge at a time, and
--   the indexing "for `n = 0` or `n = 1`" question simply does not
--   arise — the inductive shape replaces the LN's index counting.
--
-- *Self-membership `v ∈ Dist G v` is unconditional, same Walk.nil
--   witness as `Anc` / `Desc`.*  Witnessed by `⟨Walk.nil v hv, trivial⟩`
--   (`IsBidirectedWalk (Walk.nil _ _) = True` from `Walks.lean:632-634`).
--   Addition `[self_membership_notes_require_length_zero_walks]` is
--   load-bearing — neither a bidirected self-loop at `v` (excluded
--   anyway by `hL_irrefl`) nor a length-2 bidirected cycle through `v`
--   is required.  The wording-check subtlety
--   `district_walk_indexing_ambiguous_for_small_n` is resolved by the
--   same `Walk.nil` mechanism that handles the ambiguous `n = 0` /
--   `n = 1` indexing on the LN pictorial form.
--
-- *Why `Walk G v w` and not `Walk G w v`.*  Bidirected walks are
--   reversible (by `hL_symm`, the reverse of a bidirected walk is again
--   a bidirected walk), so the direction is *graph-theoretically*
--   irrelevant for `Dist`.  We pick `Walk G v w` (start at the source
--   `v`, end at the candidate sibling `w`) to mirror `Desc G v`'s
--   shape — making the `Anc / Desc / Dist` family visually uniform and
--   their downstream lemmas (transitivity, monotonicity) shareable.
--   The "obvious" symmetry `w ∈ Dist G v ↔ v ∈ Dist G w` is a one-line
--   corollary via walk reversal + `hL_symm`.
--
-- *Downstream pattern.*  `Dist G v` is the "district" used by the ID
--   algorithm (chapter 14+) and the c-component decomposition (chapter
--   16): in ADMGs, the partition of vertices into districts (= maximal
--   bidirected-connected components) is what makes the identification
--   formula factorise.  Keeping `Dist G v` as `Set Node` (not `Finset
--   Node`) matches the conditioning-set carrier expected by those
--   chapters; the `Finset` cast happens at the use site where it is
--   needed.
-- def_3_5 -- start statement
def Dist (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : Walk G v w, p.IsBidirectedWalk}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Dist

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: DistSet
-- ref: def_3_5 (item viii, district of a set)
-- The district of `A` in `G`: the indexed union of `Dist G v` over `v ∈ A`.
--
-- ## Design choice
--
-- *Same `Set.biUnion` shape as the other set forms.*  Per the
--   section-wide design preamble.  The LN's `A ⊆ Dist^G(A)` note (item
--   viii, trailing line) is again a one-line corollary of `Dist`'s
--   unconditional self-membership + `Set.subset_biUnion_of_mem`.
--
-- *Known limitation: `DistSet G A` is NOT the same as "the district
--   that contains `A`" when `A` straddles multiple districts.*  In
--   ADMG literature, the "district of `A`" sometimes means the unique
--   maximal bidirected-connected component containing `A` (when one
--   exists).  Here `DistSet G A` is the *union* of the per-vertex
--   districts of each `v ∈ A` — it agrees with the literature's
--   maximal-component reading iff `A` lies in a single component.
--   Downstream chapters that need the partition view will state the
--   "single component" hypothesis explicitly.  This is the LN's
--   convention, not a Lean artefact.
-- def_3_5 -- start statement
def DistSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Dist v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: DistSet

end CDMG

namespace refactor_CDMG

-- def_3_5 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_5 --- end helper

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Pa (was: refactor_Pa)
-- ref: def_3_5 (item i, parents of a vertex) — refactor
--
-- One-line cross-ref: see the `Pa` design block above for the
-- load-bearing rationale (LN-faithful set-builder, deliberate
-- inclusion of `v` on directed self-loops, redundant-but-kept
-- `w ∈ G` guard).  This twin shares all of it; the only shift is
-- the upstream type `CDMG Node → refactor_CDMG Node`.  `G.E`'s
-- carrier `Finset (Node × Node)` is unchanged by the refactor, so
-- the body `(w, v) ∈ G.E` reads verbatim.
-- def_3_5 -- start statement
def refactor_Pa (G : refactor_CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (w, v) ∈ G.E}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Pa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: PaSet (was: refactor_PaSet)
-- ref: def_3_5 (item i, parents of a set) — refactor
--
-- One-line cross-ref: see the `PaSet` design block above for the
-- `Set.biUnion` rationale, the `A : Set Node` choice, and the
-- singleton identity `PaSet G {v} = Pa G v`.  This twin shares all
-- of it; only the upstream type and the inner per-vertex primitive
-- `G.Pa v → G.refactor_Pa v` change.
-- def_3_5 -- start statement
def refactor_PaSet (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.refactor_Pa v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: PaSet

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Ch (was: refactor_Ch)
-- ref: def_3_5 (item ii, children of a vertex) — refactor
--
-- One-line cross-ref: see the `Ch` design block above for the
-- mirror-of-`Pa` rationale and the self-loop convention.  This
-- twin shares all of it; only the upstream type shifts.  `G.E` is
-- unchanged by the refactor, so the body `(v, w) ∈ G.E` reads
-- verbatim.
-- def_3_5 -- start statement
def refactor_Ch (G : refactor_CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (v, w) ∈ G.E}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Ch

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: ChSet (was: refactor_ChSet)
-- ref: def_3_5 (item ii, children of a set) — refactor
--
-- One-line cross-ref: see the `ChSet` design block above for the
-- `Set.biUnion` rationale shared with `PaSet`.  This twin shares
-- all of it; only the upstream type and the inner per-vertex
-- primitive `G.Ch v → G.refactor_Ch v` change.
-- def_3_5 -- start statement
def refactor_ChSet (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.refactor_Ch v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: ChSet

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Sib (was: refactor_Sib)
-- ref: def_3_5 (item iii, siblings of a vertex) — refactor
--
-- One-line cross-ref: see the `Sib` design block above for the
-- mirror-of-`Ch`-with-`L` rationale, the `w ∈ G` redundancy, the
-- no-set-form decision, and the graph-theoretic symmetry note.
-- This twin shares all of it; the upstream encoding shift is more
-- substantive than for `Pa` / `Ch` because the L-channel carrier
-- changed.
--
-- Encoded against `G.L : Finset (Sym2 Node)` via `s(v, w) ∈ G.L`;
-- symmetry is now definitional (`s(v, w) = s(w, v)` by `Sym2`'s
-- swap quotient), so the `[huh_visual_symmetry_vs_ordered_pair_in_L]`
-- concern from the original's design block is structurally
-- discharged — `Sib`'s symmetry no longer routes through
-- `hL_symm` and is instead an identity on `Sym2`.  Wording-check
-- `self_loop_makes_v_its_own_parent_child_sibling`: `Sym2.IsDiag
-- s(v, v)` together with `hL_irrefl` still rules out `v ∈ Sib G v`
-- — `hL_irrefl` is the refactor's `s ∈ L → ¬ s.IsDiag` form, which
-- on `s(v, v)` reads "if `s(v, v) ∈ G.L` then `¬ s(v, v).IsDiag`",
-- but `s(v, v).IsDiag = True`, so `s(v, v) ∉ G.L` and `v ∉ Sib G
-- v`.  The asymmetry with `Pa` / `Ch` (where self-loops are
-- admitted) is preserved.
-- def_3_5 -- start statement
def refactor_Sib (G : refactor_CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ s(v, w) ∈ G.L}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Sib

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Anc (was: refactor_Anc)
-- ref: def_3_5 (item iv, ancestors of a vertex) — refactor
--
-- One-line cross-ref: see the `Anc` design block above for the
-- `Walk + IsDirectedWalk` rationale, the unconditional self-
-- membership argument via `Walk.nil`, and the resolution of the
-- `trivial_walk_implicit_in_self_membership_notes` wording-check
-- subtlety.  This twin shares all of it; the upstream witness
-- `Walk.nil v hv` becomes `refactor_Walk.nil v hv` and the
-- predicate `IsDirectedWalk` becomes `refactor_IsDirectedWalk` —
-- same structural argument (the refactored `refactor_IsDirectedWalk
-- (.nil _ _) = True` branch is unchanged from the original
-- `IsDirectedWalk (.nil _ _) = True`), no semantic change.
-- def_3_5 -- start statement
def refactor_Anc (G : refactor_CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : refactor_Walk G w v, p.refactor_IsDirectedWalk}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Anc

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: AncSet (was: refactor_AncSet)
-- ref: def_3_5 (item iv, ancestors of a set) — refactor
--
-- One-line cross-ref: see the `AncSet` design block above for the
-- `Set.biUnion` rationale and the LN's `A ⊆ Anc^G(A)` corollary.
-- This twin shares all of it; only the upstream type and the inner
-- per-vertex primitive `G.Anc v → G.refactor_Anc v` change.
-- def_3_5 -- start statement
def refactor_AncSet (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.refactor_Anc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: AncSet

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Desc (was: refactor_Desc)
-- ref: def_3_5 (item v, descendants of a vertex) — refactor
--
-- One-line cross-ref: see the `Desc` design block above for the
-- mirror-of-`Anc`-with-reversed-walk-direction rationale and the
-- unconditional self-membership via `Walk.nil`.  This twin shares
-- all of it; the upstream witness `Walk.nil v hv` becomes
-- `refactor_Walk.nil v hv` and the predicate `IsDirectedWalk`
-- becomes `refactor_IsDirectedWalk` — same structural argument
-- (the refactored `refactor_IsDirectedWalk (.nil _ _) = True`
-- branch is unchanged), no semantic change.
-- def_3_5 -- start statement
def refactor_Desc (G : refactor_CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : refactor_Walk G v w, p.refactor_IsDirectedWalk}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Desc

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: DescSet (was: refactor_DescSet)
-- ref: def_3_5 (item v, descendants of a set) — refactor
--
-- One-line cross-ref: see the `DescSet` design block above for the
-- `Set.biUnion` rationale and the load-bearing role this set form
-- plays for `NonDesc` below.  This twin shares all of it; only the
-- upstream type and the inner per-vertex primitive `G.Desc v →
-- G.refactor_Desc v` change.
-- def_3_5 -- start statement
def refactor_DescSet (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.refactor_Desc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: DescSet

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: NonDesc (was: refactor_NonDesc)
-- ref: def_3_5 (item vi, non-descendants of a set) — refactor
--
-- One-line cross-ref: see the `NonDesc` design block above for the
-- no-per-vertex-form decision, the complement-inside-`J ∪ V`
-- rationale, the `Finset → Set` coercion choice, and the downstream
-- Markov-blanket pattern.  This twin shares all of it; only the
-- upstream type and the inner `G.DescSet A → G.refactor_DescSet A`
-- reference change.  `G.J`, `G.V` are unchanged by the refactor, so
-- the `((G.J ∪ G.V : Finset Node) : Set Node)` form reads verbatim.
-- def_3_5 -- start statement
def refactor_NonDesc (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ((G.J ∪ G.V : Finset Node) : Set Node) \ G.refactor_DescSet A
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: NonDesc

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Sc (was: refactor_Sc)
-- ref: def_3_5 (item vii, strongly connected component of a vertex) — refactor
--
-- One-line cross-ref: see the `Sc` design block above for the
-- literal-`Anc ∩ Desc` rationale, the corollary-not-axiom shape of
-- the `v ∈ Sc G v` self-membership note, and the downstream
-- acyclification / ID-algorithm pattern.  This twin shares all of
-- it; only the upstream type and the inner cross-references
-- `G.Anc v → G.refactor_Anc v`, `G.Desc v → G.refactor_Desc v`
-- change.
-- def_3_5 -- start statement
def refactor_Sc (G : refactor_CDMG Node) (v : Node) : Set Node :=
  G.refactor_Anc v ∩ G.refactor_Desc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Sc

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: ScSet (was: refactor_ScSet)
-- ref: def_3_5 (item vii, strongly connected components of a set) — refactor
--
-- One-line cross-ref: see the `ScSet` design block above for the
-- `Set.biUnion` rationale and the union-of-components-vs-single-
-- component terminology note.  This twin shares all of it; only the
-- upstream type and the inner per-vertex primitive `G.Sc v →
-- G.refactor_Sc v` change.
-- def_3_5 -- start statement
def refactor_ScSet (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.refactor_Sc v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: ScSet

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Dist (was: refactor_Dist)
-- ref: def_3_5 (item viii, district of a vertex) — refactor
--
-- One-line cross-ref: see the `Dist` design block above for the
-- shared-walk-carrier-with-`Anc`/`Desc` rationale, the resolution
-- of the `district_walk_indexing_ambiguous_for_small_n` wording-
-- check subtlety, the unconditional self-membership argument, and
-- the downstream ID-algorithm pattern.  This twin shares all of
-- it; the upstream witness `Walk.nil v hv` becomes
-- `refactor_Walk.nil v hv` and the predicate `IsBidirectedWalk`
-- becomes `refactor_IsBidirectedWalk` — same structural argument
-- (the refactored `refactor_IsBidirectedWalk (.nil _ _) = True`
-- branch is unchanged), no semantic change.  The graph-theoretic
-- symmetry `w ∈ Dist G v ↔ v ∈ Dist G w` now follows from `Sym2`'s
-- definitional swap symmetry plus walk reversal, rather than from
-- `hL_symm` — see the `refactor_Sib` block for the analogous
-- discharge of the `hL_symm` route.
-- def_3_5 -- start statement
def refactor_Dist (G : refactor_CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : refactor_Walk G v w, p.refactor_IsBidirectedWalk}
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Dist

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: DistSet (was: refactor_DistSet)
-- ref: def_3_5 (item viii, district of a set) — refactor
--
-- One-line cross-ref: see the `DistSet` design block above for the
-- `Set.biUnion` rationale and the union-vs-maximal-component
-- terminology note.  This twin shares all of it; only the upstream
-- type and the inner per-vertex primitive `G.Dist v →
-- G.refactor_Dist v` change.
-- def_3_5 -- start statement
def refactor_DistSet (G : refactor_CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.refactor_Dist v
-- def_3_5 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: DistSet

end refactor_CDMG

end Causality
