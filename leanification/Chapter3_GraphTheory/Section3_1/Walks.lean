import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations

namespace Causality

/-!
# Walks in CDMGs

This file formalises the six items of the LN definition block
`def_3_4` (`\label{def:walks}`).  The block introduces:

* `Walk G u v` — a finite alternating sequence of vertices and edges
  from `u` to `v` in `G`, with each edge constrained to be either a
  forward `E`-edge, a forward `L`-edge, or a backward `E`-edge.
* `Walk.intoStart / outOfStart / intoEnd / outOfEnd` — the four
  end-node behaviour classifiers (LN item~i).
* `Walk.IsDirectedWalk` (item~ii), `Walk.IsBidirectedWalk` (item~iii),
  `Walk.IsColliderWalk` (item~iv), `Walk.IsPath` (item~v),
  `Walk.IsBifurcation` (item~vi) — derived predicates on walks.
* `Walk.IsBifurcationSource` — the "source of a bifurcation" predicate
  from the trailing sentence of item~vi.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_4_Walks.tex`,
verified equivalent to the LN block (`graphs.tex`, `\label{def:walks}`)
augmented with two operator clarifications:

* `[bifurcation_right_chain_trivial_is_just_directed_walk]` — both
  end-nodes of a bifurcation must have exactly one arrowhead pointing
  toward them; the `k = n` directed-hinge degeneracy (which reduces to
  a plain directed walk) is excluded.
* `[collider_walk_n1_form_contradicts_inline_note]` — for `n = 1` a
  collider walk requires its single edge to be **bidirected**.  Purely
  directed edges `v → w` or `v ← w` do NOT qualify as collider walks of
  length 1.

## Design pillars

1. **`Walk` is an `inductive` (à la mathlib `SimpleGraph.Walk`), not a
   list+coherence record.**  The two constructors `nil` and `cons`
   mirror the LN's "$v_0$" (trivial walk) and "$v_0, a_0, v_1, \dots$"
   (cons one edge in front of an existing walk) presentations.  The
   middle vertex `v` of `cons` is made an *explicit* parameter — every
   pattern match below would otherwise need named-implicit syntax
   `(v := …)` to reach it, which is brittle across Lean versions.  The
   small ergonomic cost (one extra arg per `cons` call site) is paid
   by downstream constructors, not by this file.
2. **The five derived walk-type notions are `Prop`-predicates on
   `Walk`, not separate inductives.**  Wrapping each into its own
   inductive (`DirectedWalk`, `BidirectedWalk`, …) would duplicate the
   structural recursion and force lift-up lemmas in every downstream
   row that wants to view a directed walk as a generic walk.  Defining
   them as predicates lets a `(p : Walk G u v) (hp : p.IsDirectedWalk)`
   pair carry exactly the data the LN names — the walk itself plus the
   constraint that distinguishes its sub-class.
3. **Two helper recursions, `IsColliderRest` and
   `IsBifurcationWithSplit`, encode the LN's positional case splits.**
   `IsColliderRest` carries the interior+last-edge half of an
   `n ≥ 2` collider walk; `IsBifurcationWithSplit p i` says "`p` is a
   bifurcation walk whose left arm has exactly `i` reverse-directed
   edges (so the hinge is at edge position `i = k - 1`)".  The
   alternative — quantifying over an integer split index `k` and
   indexing into the edge list `p.edges` — would force the bifurcation
   predicate to thread `k ≤ length p` everywhere; recursing on `Walk`'s
   structure with an explicit Nat counter trivialises that bound.
4. **The four end-node classifiers (`intoStart` / `outOfStart` /
   `intoEnd` / `outOfEnd`) reuse `CDMG.into` and `CDMG.outOf` from
   `EdgeRelations.lean` rather than re-spelling the underlying
   set-theoretic disjunctions.**  The LN's "$a_0 = v_0 \hus v_1$" /
   "$a_{n-1} = v_{n-1} \suh v_n$" patterns are precisely "`a_0` is into
   `v_0`" / "`a_{n-1}` is into `v_n`" in the sense of def_3_3 item~ii.,
   and the rewritten tex makes this connection explicit.  Re-inlining
   the disjunctions would duplicate `into`/`outOf`'s body and break
   the LN-macro-grep correspondence the chapter has been built on.
5. **Trivial walks are vacuously *not* into nor out of either
   end-node.**  Matches the LN wording-check observation
   `into_out_of_undefined_for_trivial_walk` (resolved in the rewritten
   tex): on the trivial walk all four classifiers return `False`
   because neither `a_0` nor `a_{n-1}` exists.

The substantive per-declaration design rationale lives in the comment
block immediately above each `-- def_3_4 -- start statement` marker.
-/

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches the
--   chapter convention set by `CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean`, `CDMGRestrictions.lean`.  Fixing `Node` to a
--   concrete carrier (`Fin n`, `ℕ`) here would force renumbering at
--   every downstream operation that rewrites the vertex set —
--   intervention (`def_3_10`), node-splitting (`def_3_11`), the chains
--   of CDMG-restriction lemmas in chapters 4–10.  `[DecidableEq Node]`
--   is the minimal typeclass inherited from `def_3_1`: it is needed to
--   talk about `Finset`-membership of nodes/edges inside `WalkStep`,
--   `Walk.vertices`, and `Walk.edges`, and to decide vertex equality
--   inside `List.Nodup` for `IsPath` and `List.head?` / `getLast?`
--   for the bifurcation predicate.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds
--   these implicit binders into every declaration below — they are
--   load-bearing infrastructure, not throwaway local sugar.  The
--   three-dash flavour tags this as helper-level wrapping (distinct
--   from the per-statement `-- start statement` markers used by
--   `Walk`, `Walk.intoStart`, …) for the tex/Lean reconciliation
--   tooling and any future refactor.  Matches the wrapping used by
--   `CDMGNotation.lean`, `EdgeRelations.lean`, and
--   `CDMGRestrictions.lean` on the identical `variable` line.
-- def_3_4 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_4 --- end helper

-- ref: def_3_4 (helper, walk-step predicate)
--
-- `G.WalkStep u a v` says the ordered pair `a` is a valid walk-step
-- from `u` to `v` in `G`.  Concretely, `a` is either a *forward*
-- `E`-edge or `L`-edge `(u, v)` (LN's `\tuh` / `\huh`), or a
-- *backward* `E`-edge `(v, u)` (LN's `\hut`).  This is exactly the
-- two-way disjunction the LN imposes on each `a_k` of a walk
-- (LN item~i, clause (b): "$a_k = (v_k, v_{k+1}) \in E \cup L$ or
-- $a_k = (v_{k+1}, v_k) \in E$").  Used as the index of `Walk.cons`
-- to bake the LN's per-edge constraint into the inductive's data.
--
-- ## Design choice
--
-- *Why factor the single-edge constraint into its own named helper.*
--   The LN's per-edge condition is the *atomic* law that every walk
--   constructor must satisfy.  Pulling it out as `WalkStep` and
--   feeding it to `Walk.cons` as a single hypothesis `h` keeps the
--   inductive readable, mirrors the LN's "edge constraint per step"
--   reading, and lets downstream proofs that need to manipulate one
--   walk-edge at a time (the four end-node classifiers below,
--   `def_3_5`'s parent-from-walk recovery, `def_3_6`'s acyclicity
--   case analyses) destructure `h : WalkStep …` once rather than
--   re-splitting the disjunction inline at every site.  Inlining the
--   disjunction into `Walk.cons` was rejected: every pattern match on
--   a walk would then expose the two-way `Or` in the `cons`-arg
--   position, doubling the case count of every downstream recursion.
--
-- *Why exactly two disjuncts — the canonical LN form
--   `(a = (u, v), edge ∈ E ∪ L) ∨ (a = (v, u), edge ∈ E)`.*  The LN
--   writes the per-step constraint as a two-way disjunction that
--   already factors over the direction of `a`: the *forward* writing
--   `(u, v)` admits both directed and bidirected edges (`E ∪ L`),
--   while the *backward* writing `(v, u)` admits only directed edges
--   (`E`).  A fourth case "backward `L`-edge `(v, u) ∈ L`" is
--   *collapsed* into the forward `L`-disjunct by `CDMG.hL_symm`
--   (`(v, u) ∈ G.L ↔ (u, v) ∈ G.L`), so listing it would be
--   redundant.  We follow the LN's two-disjunct enumeration literally
--   — the LN already absorbed the bidirected backward writing into
--   the forward `L`-case via the symmetry of `L`.
--
-- *Why `Prop`, not a `Bool` decidable predicate.*  Walks live in
--   `Type _` for their inductive data; their step predicate lives in
--   `Prop` for its logical role as a hypothesis.  Lifting to `Bool`
--   would require deciding `(u, v) ∈ G.E ∨ (u, v) ∈ G.L ∨ (v, u) ∈
--   G.E` at every constructor site — possible (the underlying
--   `Finset` memberships are decidable) but it would force every
--   `Walk.cons` to carry a coerced `Bool`-witness instead of a clean
--   `Prop`-hypothesis, making downstream rewrites uglier.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: WalkStep
-- def_3_4 --- start helper
def WalkStep (G : CDMG Node) (u : Node) (a : Node × Node) (v : Node) : Prop :=
  (a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∨ (a = (v, u) ∧ a ∈ G.E)
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: WalkStep

-- ref: def_3_4 (item~i, Walk)
--
-- A *walk* from `u` to `v` in `G`.  Inductive type, two constructors:
--
-- * `Walk.nil v hv` — the *trivial walk* `(v_0)` consisting of a
--   single node `v ∈ G`.  Lives at type `Walk G v v` (so the LN's
--   "$v = w$" precondition for the trivial walk is enforced at the
--   type level).  The membership witness `hv` is data on the
--   constructor because for `n = 0` there is no edge from which the
--   `J ∪ V` membership of `v` could be recovered.
-- * `Walk.cons v a h p` — prepend the alternating step "$v_0, a_0,
--   v_1$" in front of an existing walk `p` from `v_1` to `w`.  The
--   middle vertex `v_1` is the explicit `v` parameter; the LN edge
--   constraint `a_0 ∈ E ∪ L$ or $a_0 = (v_1, v_0) \in E$" is the
--   `h : G.WalkStep u a v` hypothesis.
--
-- For `n ≥ 1`, each new vertex is the head of an `E ∪ L`-edge, so its
-- `J ∪ V` membership follows from `CDMG.hE_subset` / `hL_subset` and
-- need not be threaded explicitly through `cons`.
--
-- ## Design choice — `Walk` is an inductive Type, not a list+coherence record
--
-- *Mirrors mathlib's `SimpleGraph.Walk`, adapted to CDMGs.*  Mathlib
--   formalises walks in an undirected `SimpleGraph` as an `inductive
--   SimpleGraph.Walk` with `nil`/`cons` constructors indexed by
--   endpoints.  Our `Walk G u v` is the direct analogue for CDMGs:
--   the per-edge constraint is widened to `WalkStep` (covering
--   forward `E`, forward `L`, and backward `E` writings — exactly the
--   LN item~i clause (b) disjunction) but the inductive *shape* is
--   the same.  Re-using the mathlib-shape lets readers familiar with
--   `SimpleGraph.Walk` orient themselves; we depart only where CDMGs
--   genuinely differ (the three-way edge disjunction, the disjoint
--   `J`/`V` partition).
--
-- *`inductive Type _`, not `List (Node × Node) × <coherence proof>`.*
--   Walks carry *data* that downstream chapters consume.  `def_3_5`'s
--   ancestral-set definition recurses on walks; `def_3_6` acyclicity
--   talks about the *count* of non-trivial directed walks `v → v`;
--   `def_3_8` (topological order) constructs explicit walks
--   witnessing reachability; chapters 6–7 (σ-/d-separation) pattern
--   match on walks at every active-path inductive step.  A `List` +
--   coherence proof would force every such consumer to repeatedly
--   destructure the `(p, hp)` pair and unpack the coherence proof
--   one edge at a time.  Pattern matching on `Walk.cons` directly
--   reads exactly like the LN's "$v_0, a_0, v_1, \dots$" — every
--   downstream proof can case-split on `nil` vs `cons` and obtain
--   the LN's natural induction hypothesis for free.
--
-- *Two-vertex index `Walk G u v`, endpoints in the type.*  Mirrors
--   the LN's "*walk from $v$ to $w$*" phrasing (LN item~i clause
--   (a): `v_0 = v` and `v_n = w`): both endpoints are part of the
--   type, the trivial walk has type `Walk G v v` enforcing the
--   "$v = w$" precondition at the type level, and the constructor
--   types enforce edge-endpoint coherence by construction.  An
--   un-indexed `Walk G` paired with explicit "endpoints" fields was
--   rejected — it would force every consumer that quantifies over
--   "walks from `u` to `v`" to thread two `≠`-equalities through
--   every proof.
--
-- *Middle vertex `v` is explicit in `cons`, not implicit.*  Implicit
--   `{u v w}` (as in `SimpleGraph.Walk`) is more ergonomic at
--   construction sites but forces every predicate in this file to use
--   the `(v := …)` named-pattern syntax to reach the middle vertex.
--   The seven `def`s below pattern-match on `.cons v a _ p` and refer
--   to `v` directly (the LN's `v_1` in the cons-cell); we pick the
--   simpler patterns at the small cost of one extra explicit arg per
--   `cons` call.
--
-- *Vertex-membership witness `hv` on `nil`, none on `cons`.*  For
--   `n = 0` the trivial walk has no edge from which the
--   `J ∪ V`-membership of `v` could be recovered, so `nil`'s
--   constructor carries the witness directly.  For `n ≥ 1`, each new
--   vertex sits at the head of an `E ∪ L`-edge — `hE_subset` and
--   `hL_subset` recover its membership without an extra field on
--   `cons`.  Asymmetric, but minimal: data is added exactly where it
--   cannot be inferred.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk
-- def_3_4 -- start statement
inductive Walk (G : CDMG Node) : Node → Node → Type _ where
  | nil (v : Node) (hv : v ∈ G) : Walk G v v
  | cons {u w : Node} (v : Node) (a : Node × Node)
      (h : G.WalkStep u a v) (p : Walk G v w) : Walk G u w
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: Walk

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : CDMG Node}`.*  Every
--   declaration in this namespace — `vertices`, `edges`, the four
--   end-node classifiers, the five walk-class predicates, the two
--   bifurcation helpers, `IsBifurcation`, `IsBifurcationSource` —
--   takes (or recurses over) a walk `p : Walk G u v`.  Without the
--   namespace-wide `variable`, every signature would carry an
--   explicit `{G : CDMG Node}` binder; the auto-binding keeps the
--   signatures readable and matches the LN's "Let $G = (J, V, E, L)$
--   be a CDMG" once-at-the-top quantifier.
--
-- *Why `{G}` is implicit, not explicit `(G)`.*  Downstream consumers
--   reach into `G` via dot-notation on the walk (`p.vertices` rather
--   than `Walk.vertices G p`).  Lean infers `G` from the walk's type
--   `Walk G u v`, so making `G` explicit at every call site would be
--   noise.  The chapter convention throughout `def_3_2`–`def_3_4`
--   keeps `G` implicit wherever it can be inferred from another arg.
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the file-top `variable {Node}` helper: this `{G}`
--   binder is load-bearing infrastructure that the tex/Lean
--   reconciliation tooling must recognise as helper-flavour.
-- def_3_4 --- start helper
variable {G : CDMG Node}
-- def_3_4 --- end helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: length
/-- Length of a walk: the number `n` of edges (matches the LN's `n`). -/
-- def_3_6 --- start helper
def length : ∀ {u v : Node}, Walk G u v → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ _ p => p.length + 1
-- def_3_6 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: length

-- ref: def_3_4 (helper, vertex sequence)
--
-- `Walk.vertices p` is the list `[v_0, v_1, …, v_n]` from LN item~i,
-- i.e.\ the ordered sequence of vertices traversed by `p`.  Used by
-- `IsPath` (vertices form a `Nodup` list) and by `IsBifurcation` /
-- `IsBifurcationSource` (the LN's "each end-node occurs exactly once"
-- condition is `u ∉ p.vertices.tail` and `v ∉ p.vertices.dropLast`).
--
-- ## Design choice
--
-- *Why a `List Node` helper, not a `Finset Node` or a function
--   `Fin (n+1) → Node`.*  The LN's tuple `(v_0, v_1, …, v_n)` is
--   *ordered* and may *repeat* (item~i explicitly says: "the same
--   node may appear multiple times in a walk"), so a `Finset` (no
--   order, no duplicates) is wrong on both counts.  A length-indexed
--   function `Fin (n+1) → Node` would preserve order and duplicates
--   but force `Fin`-arithmetic plumbing at every use site
--   (`IsPath` would have to spell `∀ i j, i ≠ j → f i ≠ f j` rather
--   than `vertices.Nodup`).  `List Node` is the cheapest carrier
--   that matches the LN's tuple verbatim and unlocks the mathlib
--   `List`-API (`Nodup`, `head?`, `getLast?`, `tail`, `dropLast`)
--   for free — each of which is invoked downstream below.
--
-- *Why recurse on the `Walk` constructors directly, not on
--   `Walk.length`.*  Pattern matching on `nil` / `cons` makes the
--   defining equations `(.nil v _).vertices = [v]` and
--   `(.cons _ _ _ p).vertices = u :: p.vertices` definitionally
--   equal to the natural reading; downstream proofs can chain
--   `simp [Walk.vertices]` once and obtain the expected list literal.
--   A `Walk.length`-driven recursion (`Walk.vertices_aux p (length p)`)
--   would force every consumer to first compute the length and
--   thread it through, with no readability gain.
--
-- *Asymmetry: the `nil` case carries `v` in the list (it *is* the
--   walk's only vertex); the `cons` case prepends `u` (the new tail
--   vertex) and recurses on `p` (which already contains the middle
--   vertex `v` as its first element).*  This avoids double-counting
--   the middle vertex `v` and matches the LN's "$v_0, v_1, …, v_n$"
--   convention: each vertex appears exactly once in the index list
--   (though may appear multiple times in *value*).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: vertices
-- def_3_4 --- start helper
def vertices : ∀ {u v : Node}, Walk G u v → List Node
  | _, _, .nil v _ => [v]
  | u, _, .cons _ _ _ p => u :: p.vertices
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: vertices

-- ref: def_3_4 (helper, edge sequence)
--
-- `Walk.edges p` is the list `[a_0, a_1, …, a_{n-1}]` from LN
-- item~i, i.e.\ the ordered sequence of ordered-pair edges
-- traversed by `p`.  Used by `intoStart` / `outOfStart` (via
-- `cons`-pattern on the head) and `intoEnd` / `outOfEnd` (via
-- `List.getLast?`).
--
-- ## Design choice
--
-- *Why a `List (Node × Node)`, parallel to `vertices`.*  The LN's
--   tuple `(a_0, a_1, …, a_{n-1})` is one element shorter than the
--   vertex tuple (`n` edges vs `n+1` vertices) and is also ordered
--   and may repeat (the LN does not forbid re-using an edge in a
--   walk).  A `List (Node × Node)` matches the LN's edge tuple
--   exactly.  An indexed function `Fin n → Node × Node` would
--   impose length-tracking obligations on every consumer; we choose
--   `List` for the same reasons as `vertices`.
--
-- *Why we don't bundle vertices and edges into a single
--   `List (Node × (Node × Node) × Node)` "alternating" list.*  The
--   LN presentation keeps the two tuples parallel, and the
--   predicates that consume them (`intoStart` reads only the first
--   edge; `IsPath` reads only the vertex list's `Nodup`; the
--   bifurcation predicates read `vertices.tail` and
--   `vertices.dropLast`) only ever need one side or the other.
--   Splitting matches the LN reading and lets each predicate touch
--   only the data it cares about — no `List.map Prod.fst`
--   projections at every use site.
--
-- *Why `nil.edges = []`, not `[(v, v)]` or some sentinel.*  The
--   trivial walk has *no* edges; the LN says "no edges, and
--   condition (b) vacuously satisfied".  An empty list is the
--   literal carrier for that vacuity; downstream `getLast? = none`
--   on the trivial walk is what makes the end-node classifiers
--   return `False` (see `intoEnd` / `outOfEnd`), exactly matching
--   the LN's "neither $a_0$ nor $a_{n-1}$ exists" reading.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: edges
-- def_3_4 --- start helper
def edges : ∀ {u v : Node}, Walk G u v → List (Node × Node)
  | _, _, .nil _ _ => []
  | _, _, .cons _ a _ p => a :: p.edges
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: edges

-- ref: def_3_4 (item~i, end-node classifier "into v_0")
--
-- `p.intoStart` iff `p` is non-trivial AND its first edge `a_0` is an
-- edge into `v_0` in the sense of def_3_3 item~ii.  Concretely (per
-- the rewritten tex item~i):
--   `(a_0 = (v_1, v_0) ∈ E) ∨ (a_0 = (v_0, v_1) ∈ L)`.
-- The trivial walk is *not* into its (single) end-node — `False`,
-- matching the LN's vacuous behaviour at `n = 0`.
--
-- ## Design choice — design block also covers the three sibling
-- classifiers `outOfStart`, `intoEnd`, `outOfEnd` below
--
-- *Why four independent `Prop`-predicates, NOT a four-way enum
--   `inductive EndNodeBehaviour := intoStart | outOfStart | intoEnd
--   | outOfEnd` (or a `Bool × Bool` "into?, out?" classifier).*  The
--   four classifications are *not a partition* — the LN-critic's
--   `into_out_of_undefined_for_trivial_walk` subtlety surfaces this
--   directly.  Two non-partition shapes coexist:
--   * The *trivial walk* ($n = 0$) is neither into nor out of either
--     end-node — *all four predicates return `False`* (the LN's
--     rewrite item~i, last paragraph: "On the trivial walk ($n = 0$)
--     all four classifications are vacuously false").  An enum would
--     force a fifth `none` constructor or a `Option EndNodeBehaviour`,
--     either of which would be ad-hoc.
--   * A *bidirected first edge* ($a_0 = (v_0, v_1) \in L$) makes the
--     walk `intoStart` (matching the `\hus`/`\huh` half of "into
--     `v_0`") but NOT `outOfStart` (since `outOf` excludes `L`-edges
--     entirely, per `def_3_3` item~iii).  Mutually exclusive yet not
--     jointly exhaustive — the LN's rewrite item~i, last paragraph
--     makes this explicit.  A `Bool × Bool` classifier could express
--     this but would compress two genuinely-distinct LN clauses
--     (`\hus` for "into", `\tuh` for "out of") into bit positions,
--     losing the LN-macro-grep correspondence.
--   Four independent `Prop`-predicates faithfully encode the LN's
--   four symbolic definitions ($\hus$, $\tuh$, $\suh$, $\hut$) one
--   for one, and let downstream consumers conjoin / negate them
--   freely (`def_3_5`'s parent recovery needs "out of `v_0` and
--   directed", chapters 6–7's d-/σ-separation collider conditions
--   need "into `v_k` from *both* sides").
--
-- *Why reuse `G.into` and `G.outOf` from `EdgeRelations.lean`
--   rather than re-spelling the underlying disjunctions.*  The LN's
--   "$a_0 = v_0 \hus v_1$" pattern is *precisely* "$a_0$ is an edge
--   into `v_0`" in the sense of `def_3_3` item~ii. (item~iii for
--   "out of"), and the rewritten tex of `def_3_4` item~i makes the
--   connection explicit ("$a_0$ is an edge into $v_0$ in the sense
--   of def \ref{def-edge-relations}, item~ii.").  Re-inlining the
--   set-theoretic disjunctions `(a = (v_1, v_0) ∈ E) ∨ (a = (v_0,
--   v_1) ∈ L)` here would duplicate `into`'s body, break the LN-
--   macro-grep correspondence the chapter has been built on, and
--   force every downstream proof that mentions both "edge into `v`"
--   and "walk into `v_0`" to chain two unfoldings instead of one.
--
-- *Why the trivial walk is encoded as `False` (vacuously not into),
--   not `True` (vacuously into) or a third option.*  The LN's
--   classifiers are existentially loaded: "$a_0 = \dots$" requires
--   `a_0` to exist.  On the trivial walk no `a_0` exists, so the
--   matching pattern `cons _ a _ _ => …` simply does not fire and
--   the `nil` branch is forced to a definite value.  `False`
--   matches the LN's "neither into nor out of" reading; `True`
--   would silently include trivial walks in *both* the "into" and
--   "out of" categories, breaking the rewrite's explicit "vacuously
--   false" claim and corrupting downstream conditional checks
--   ("walk is into `v_0` ⇒ walk has at least one edge").
--
-- *Recursion shape: pattern-match on `Walk` directly, not on
--   `p.edges.head?`.*  Both are equivalent (a `cons` walk's first
--   edge is exactly `edges.head?` returning `some a`), but the
--   direct match keeps unfolding behaviour predictable for `simp`
--   and avoids a needless `Option`-traversal in the `nil` case.
--   See `intoEnd` / `outOfEnd` below, which *do* go through
--   `edges.getLast?` because the LN classifier reaches the *last*
--   edge — for which there is no direct constructor pattern.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: intoStart
-- def_3_4 -- start statement
def intoStart : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | u, _, .cons _ a _ _ => G.into u a
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: intoStart

-- ref: def_3_4 (item~i, end-node classifier "out of v_0")
--
-- `p.outOfStart` iff `p` is non-trivial AND its first edge is an edge
-- out of `v_0` (def_3_3 item~iii).  Concretely: `a_0 = (v_0, v_1) ∈
-- E`.  Trivial walk is `False`.  Mutually exclusive with `intoStart`
-- on `E`-edges, but jointly *not* exhaustive — a bidirected first
-- edge `a_0 = (v_0, v_1) ∈ L` is `intoStart` but *not* `outOfStart`.
--
-- ## Design choice
--
-- *Mirror of `intoStart`.*  Same rationale as `intoStart` above:
--   four independent `Prop`s, reuse `G.outOf` from `EdgeRelations`,
--   trivial walk vacuously `False`, pattern-match on `Walk`
--   directly.  See `intoStart`'s design block for the full
--   justification.  The single semantic difference here is that
--   `G.outOf` excludes `L`-edges entirely (per `def_3_3` item~iii's
--   "no $L$-edge is out of any vertex"), so a bidirected first edge
--   produces `intoStart ∧ ¬outOfStart` — the non-partition shape
--   surfaced by the LN-critic's
--   `into_out_of_undefined_for_trivial_walk` subtlety.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: outOfStart
-- def_3_4 -- start statement
def outOfStart : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | u, _, .cons _ a _ _ => G.outOf u a
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: outOfStart

-- ref: def_3_4 (item~i, end-node classifier "into v_n")
--
-- `p.intoEnd` iff `p` is non-trivial AND its last edge `a_{n-1}` is
-- an edge into `v_n` (def_3_3 item~ii).  Implemented via
-- `p.edges.getLast?`; on the trivial walk `edges = []` so
-- `getLast? = none` and the predicate is `False`.
--
-- ## Design choice
--
-- *Mirror of `intoStart`, reaching the last edge instead of the
--   first.*  Same partition-vs-independent-`Prop`s reasoning as
--   `intoStart`; same reuse of `G.into` from `EdgeRelations`; same
--   `False` on the trivial walk.  The only structural difference is
--   the access path: the last edge is reached via
--   `p.edges.getLast?` (returning `none` on the trivial walk and
--   `some a` on a non-trivial walk), rather than by a `cons`-pattern
--   on the head — there is no direct constructor pattern for the
--   *last* `cons` cell in an inductively-built walk.  The `match`
--   on `Option` is one line longer than `intoStart`'s pattern but
--   keeps definitional-equality lemmas (`edges_getLast?_nil = none`,
--   etc.) within `List`-API reach.
--
-- *Why not recurse over the walk to peel down to the last edge.*
--   A direct recursion would have shape `intoEnd (cons v a _ (nil _
--   _)) = G.into v a; intoEnd (cons _ _ _ (p@(cons …))) = intoEnd
--   p`, mirroring `IsColliderRest`.  Both forms are equivalent.  We
--   pick the `getLast?` form here because the LN classifier is
--   defined *purely* in terms of "the last edge `a_{n-1}`" — no
--   inductive structure on `p` is required, so the predicate's
--   definitional unfolding is one `List.getLast?` lookup instead of
--   `Walk.length p` recursion steps.  Downstream proofs that need
--   `intoEnd` on a specific walk simply `simp [Walk.intoEnd,
--   Walk.edges, List.getLast?]` to reach the underlying edge.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: intoEnd
-- def_3_4 -- start statement
def intoEnd {u v : Node} (p : Walk G u v) : Prop :=
  match p.edges.getLast? with
  | none => False
  | some a => G.into v a
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: intoEnd

-- ref: def_3_4 (item~i, end-node classifier "out of v_n")
--
-- `p.outOfEnd` iff `p` is non-trivial AND its last edge is an edge
-- out of `v_n` (def_3_3 item~iii).  Concretely: `a_{n-1} = (v_n,
-- v_{n-1}) ∈ E`.  Trivial walk is `False`.
--
-- ## Design choice
--
-- *Mirror of `intoEnd`, with `G.outOf` instead of `G.into`.*  Same
--   `List.getLast?`-driven access to the last edge, same trivial-
--   walk-`False` convention, same independent-`Prop`s rationale as
--   `intoStart` / `outOfStart` / `intoEnd`.  As with `outOfStart`,
--   `G.outOf` excludes `L`-edges per `def_3_3` item~iii, so a
--   bidirected last edge produces `intoEnd ∧ ¬outOfEnd` — the same
--   non-partition shape at the right end of the walk.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: outOfEnd
-- def_3_4 -- start statement
def outOfEnd {u v : Node} (p : Walk G u v) : Prop :=
  match p.edges.getLast? with
  | none => False
  | some a => G.outOf v a
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: outOfEnd

-- ref: def_3_4 (item~ii, directed walk)
--
-- `p.IsDirectedWalk` iff every edge of `p` is a *forward* `E`-edge:
-- for each step `cons v a _ p'` we require `a = (u, v) ∧ a ∈ G.E`.
-- The trivial walk satisfies the predicate vacuously, matching the
-- LN's "the trivial walk … is admitted as a directed walk".
--
-- ## Design choice — design block also covers `IsBidirectedWalk` /
-- `IsColliderWalk` / `IsPath` / `IsBifurcation` below
--
-- *Why a `Prop`-predicate on `Walk G u v`, not a separate inductive
--   `inductive DirectedWalk (G : CDMG Node) : Node → Node → Type _`.*
--   The LN items (ii)–(vi) all introduce *sub-classes* of walks, not
--   new walk-flavoured types: "a directed walk … is a walk that, in
--   addition, satisfies … " (item~ii of the rewrite).  Encoding each
--   sub-class as a `Prop`-predicate on the existing `Walk` lets a
--   `(p : Walk G u v) (hp : p.IsDirectedWalk)` pair carry exactly
--   the LN's data: the walk itself plus the constraint that selects
--   its sub-class.  Crucially, "every directed walk is a walk"
--   becomes the literal identity function — no forgetful coercion,
--   no lift-up lemma, no duplicated structural recursion.
--
-- *Alternatives considered and rejected.*  (a) A separate inductive
--   `DirectedWalk` would force a forgetful map `DirectedWalk → Walk`
--   and every downstream lemma that mixes walk-class predicates
--   (e.g.\ chapters 6–7's d-separation: "active path = no consecutive
--   *directed* sub-walks of opposite orientation crossing a non-
--   collider") would have to reason about both inductive types
--   simultaneously.  (b) A subtype `{p : Walk G u v // p.IsDirected}`
--   is closer to our `(p, hp)`-pair form but introduces an extra
--   coercion layer and changes the equality theory of walks
--   (subtype-equality requires both the data and the proof to
--   match); we use the unbundled pair form everywhere downstream.
--   (c) Storing the constraint flag *inside* `Walk` (a Boolean field
--   on each `cons`) would force every walk to carry a directedness
--   tag even when no consumer cares.
--
-- *Trivial walk satisfies vacuously (`nil _ _ => True`).*  The LN's
--   rewrite item~ii explicitly admits the trivial walk: "The trivial
--   walk ($n = 0$, $v = w$) is admitted as a directed walk from $v$
--   to itself."  An over-strict `False` on `nil` would force every
--   downstream proof that needs "the trivial walk is directed" to
--   carry a special-case hypothesis.
--
-- *Why `a = (u, v) ∧ a ∈ G.E`, not `G.tuh u v` from
--   `CDMGNotation.lean`.*  `G.tuh` unfolds to `(u, v) ∈ G.E`, which
--   is the second conjunct here.  But the LN-faithful constraint at
--   each walk step pins down *two* pieces of data: (i) the
--   *direction* of the edge (`a = (u, v)`, the forward writing) and
--   (ii) its membership in `E`.  Direction (i) is what
--   distinguishes a directed walk from the backward `E`-edge case
--   of `WalkStep`.  Stating the conjunction explicitly here makes
--   the contrast with `WalkStep`'s general two-way disjunction
--   visible — a directed walk is precisely the case where only the
--   forward `E`-disjunct of `WalkStep` is taken at every step.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsDirectedWalk
-- def_3_4 -- start statement
def IsDirectedWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ p => a = (u, v) ∧ a ∈ G.E ∧ p.IsDirectedWalk
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsDirectedWalk

-- ref: def_3_4 (item~iii, bidirected walk)
--
-- `p.IsBidirectedWalk` iff every edge is a *forward* `L`-edge:
-- `a = (u, v) ∧ a ∈ G.L`.  Note that `hL_symm` makes the *backward*
-- writing `(v, u) ∈ L` an equivalent shape, but we pin the forward
-- representative to stay close to the LN's "$v_0 \huh v_1 \huh \cdots
-- \huh v_n$" left-to-right reading.  Trivial walk satisfies vacuously.
--
-- ## Design choice
--
-- *Mirror of `IsDirectedWalk` with `G.L` in place of `G.E`.*  Same
--   `Prop`-predicate-on-`Walk` shape, same vacuous-`True` on the
--   trivial walk, same direction-pin in `a = (u, v)`.  See
--   `IsDirectedWalk`'s design block above for the four-way
--   alternative rejection (separate inductive, subtype, Boolean
--   tag, etc.).
--
-- *Why pin `a = (u, v)` (forward writing) rather than admit `a =
--   (u, v) ∨ a = (v, u)` (either writing).*  The LN's rewrite
--   item~iii enumerates only the forward writing; the parenthetical
--   "equivalently, by the symmetry of $L$ from def \ref{def-cdmg},
--   $(v_{k+1}, v_k) \in L$ for every such $k$" makes clear that the
--   backward writing *is* automatically admitted via `hL_symm`,
--   but as a derived equivalence, not as a primary disjunct.  Our
--   `def` matches the LN's primary form (forward writing) — the
--   symmetric reading is a one-line corollary `(a = (v, u) ∧ a ∈
--   G.L) ↔ (a = (u, v) ∧ a ∈ G.L)` via `hL_symm`.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsBidirectedWalk
-- def_3_4 -- start statement
def IsBidirectedWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ p => a = (u, v) ∧ a ∈ G.L ∧ p.IsBidirectedWalk
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsBidirectedWalk

-- ref: def_3_4 (helper, collider-walk "interior+last" tail)
--
-- `p.IsColliderRest` carries the trailing constraint of an `n ≥ 2`
-- collider walk after its first edge has been consumed.  Concretely:
-- * if `p` has length 1 (the remaining edge is the LN's `a_{n-1}`):
--   the edge places an arrowhead at the *current* start vertex `u`
--   (= `v_{n-1}` in LN), i.e.\ `(v, u) ∈ E` or `(u, v) ∈ L`;
-- * if `p` has length ≥ 2 (a true interior edge `a_k`, 1 ≤ k ≤ n-2):
--   the edge is forward-bidirected, `a = (u, v) ∧ a ∈ G.L`, and the
--   tail recursively satisfies the same predicate.
-- The `nil` branch is set to `True` for totality; it is not reached
-- from the only call site (the `n ≥ 2` branch of `IsColliderWalk`).
--
-- ## Design choice
--
-- *Why a separate auxiliary recursive predicate, not an inline
--   constraint inside `IsColliderWalk`.*  The LN's item~iv (rewrite
--   case $n \ge 2$) has a *positional* structure:
--     (a) first edge places arrowhead at `v_1`,
--     (b) every interior edge $a_k$ for $1 \le k \le n-2$ is bidirected,
--     (c) last edge places arrowhead at `v_{n-1}`.
--   Spelling this out inline as a single recursion on `Walk` would
--   need to distinguish three positions per `cons`-cell (first edge,
--   interior, last) using auxiliary boolean flags or length
--   comparisons — clumsy and brittle.  Factoring the "interior +
--   last" half into `IsColliderRest` and letting `IsColliderWalk`
--   handle only the first edge keeps each predicate's recursion
--   shape one-shaped: `IsColliderWalk`'s only job is "consume the
--   first edge, hand the rest to `IsColliderRest`"; `IsColliderRest`
--   recurses pattern-matching "this is the *last* `cons`" (one
--   special case) vs "still interior" (the recursive case).
--
-- *Why three branches: `nil` (`True`), `cons _ _ _ (.nil _ _)`
--   (last-edge constraint), `cons _ _ _ (cons …)` (interior +
--   recurse).*  The middle branch is what makes the predicate work
--   — pattern-matching on the *next* constructor inside the tail
--   `p` directly distinguishes "I am at the last edge" from "I am
--   in the interior".  The alternative (matching only on the top
--   `cons` and checking `p.length = 0`) would inflate every
--   downstream proof with a length-tracking obligation.
--
-- *Why the `nil` branch is `True` (and unreachable from the only
--   call site).*  Lean's structural recursion needs *some* answer
--   for the `nil` constructor for the function to be total.
--   `IsColliderRest` is called only from the `n ≥ 2` branch of
--   `IsColliderWalk` (where the first edge has already been
--   consumed, so the *original* walk had length ≥ 2 and the tail
--   has length ≥ 1 — never `nil`).  Setting the `nil` branch to
--   `True` makes the predicate vacuous on that unreachable case
--   and never appears in any downstream proof.  `False` would
--   work definitionally for the same reason (also unreachable) but
--   would risk a future consumer mistakenly invoking
--   `IsColliderRest` on a trivial walk and getting an unsoundness-
--   suggestive `False` for no real reason.
--
-- *Why the last-edge branch is a disjunction `(v, u) ∈ E ∨ (u, v) ∈
--   L`, encoding the LN's `\suh` ("arrowhead at the right
--   endpoint") at the *last edge*.*  The LN's item~iv clause (c)
--   says the last edge places an arrowhead at `v_{n-1}` — which is
--   the *current* start vertex `u` at this recursion depth
--   (because the first edges have been peeled off).  The two
--   admissible writings are `(v_{n-1}, v_n) ∈ E` (i.e. `(u, v) ∈
--   E` in the local naming, but wait — that's the *forward*
--   writing with `v` as the head, not the LN's intended "arrowhead
--   at `v_{n-1} = u`") versus … re-read the LN.  The LN
--   item~iv (c) says: $a_{n-1} = (v_n, v_{n-1}) \in E$ *or*
--   $a_{n-1} = (v_{n-1}, v_n) \in L$.  In local naming with the
--   `cons u :: v :: nil`-cell at the last step, `v_{n-1} = u` and
--   `v_n = v`, so the LN forms are `(v, u) ∈ E` and `(u, v) ∈ L`
--   — exactly the two-way disjunction encoded here.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsColliderRest
-- def_3_4 --- start helper
def IsColliderRest : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ (.nil _ _) =>
      (a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)
  | u, _, .cons v a _ (p@(.cons _ _ _ _)) =>
      a = (u, v) ∧ a ∈ G.L ∧ p.IsColliderRest
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: IsColliderRest

-- ref: def_3_4 (item~iv, collider walk)
--
-- `p.IsColliderWalk` encodes the case-distinguished spec from the
-- rewritten tex:
-- * `n = 0` (trivial walk): no constraint — `True`.
-- * `n = 1` (single edge): the lone edge is **bidirected**,
--   `a_0 = (v_0, v_1) ∈ L`.  Purely directed edges `(v, w) ∈ E`
--   or `(w, v) ∈ E` are *not* admitted as collider walks of length 1
--   (addition `[collider_walk_n1_form_contradicts_inline_note]`).
-- * `n ≥ 2`: the first edge places an arrowhead at `v_1`
--   (`a_0 = (v_0, v_1) ∧ (a_0 ∈ E ∨ a_0 ∈ L)`), and the rest
--   (interior edges bidirected + last edge into `v_{n-1}`) satisfies
--   `IsColliderRest`.
--
-- ## Design choice
--
-- *Why the `n = 1` case is `a = (u, v) ∧ a ∈ G.L` (a single
--   bidirected edge), NOT the LN's inline note's "$v \sus w \in G$"
--   reading.*  Addition `[collider_walk_n1_form_contradicts_inline_note]`
--   is load-bearing here.  The LN's source block has the inline
--   note "Note that for $n = 1$ this reads: $v \sus w \in G$" — i.e.
--   *any* adjacency.  But the LN's *symbolic pattern* `v_0 \suh v_1
--   \huh \cdots \huh v_{n-1} \hus v_n`, read literally for $n = 1$,
--   identifies $v_{n-1} = v_0$ and $v_n = v_1$, so the lone edge
--   must satisfy *both* `\suh` at $v_0$ ($v_1$ has arrowhead) AND
--   `\hus` at $v_1$ ($v_0$ has arrowhead) — i.e. arrowheads at both
--   endpoints, i.e. a bidirected edge in `L`.  The LN-critic's
--   `collider_walk_n1_literal_pattern_vs_note` subtlety flagged this
--   inconsistency; the operator addition resolved it in favour of
--   the stricter symbolic reading (which also matches the verbal
--   "every node strictly between $v$ and $w$ has two arrowheads
--   pointing toward it" — for $n = 1$ this is vacuous, and the
--   *endpoint* arrowhead constraint becomes the binding clause).
--   Purely directed edges `(v, w) ∈ E` or `(w, v) ∈ E` are *not*
--   admitted as collider walks of length 1 under this resolution.
--
-- *Why a three-way case-distinguished `def`, mirroring the LN
--   rewrite's "$n = 0$", "$n = 1$", "$n \ge 2$" structure exactly.*
--   The rewritten tex case-distinguishes on `n` because the LN's
--   symbolic pattern collapses in two degenerate small-`n`
--   regimes ($n = 1$ is the bidirected-edge case; $n = 0$ is
--   vacuous).  Encoding the same three cases as three Lean
--   pattern branches makes definitional unfolding match the
--   rewrite's section headings.  An alternative single-recursion
--   form (treat $n = 0$ and $n = 1$ as degeneracies of the general
--   `IsColliderRest` recursion) was rejected: it would force the
--   `n = 1` branch through the unreachable `nil`-case of
--   `IsColliderRest` and obscure the addition's intent.
--
-- *Why the `n \ge 2` first-edge constraint is `a = (u, v) ∧ (a ∈
--   G.E ∨ a ∈ G.L)` ("arrowhead at `v_1`, any tail at `v_0`").*  The
--   LN rewrite item~iv clause (a) ("the first edge places an
--   arrowhead at $v_1$") covers two cases: `a_0 = (v_0, v_1) ∈ E`
--   (i.e. `\tuh` at `v_1`) or `a_0 = (v_0, v_1) ∈ L` (i.e. `\huh`
--   at `v_1`).  Both share the forward-writing `a = (u, v)` and
--   differ only in which finset the edge belongs to — encoded as
--   the disjunction `a ∈ G.E ∨ a ∈ G.L`.  The constraint at the
--   *other* end (arrowhead at `v_{n-1}`) is carried by
--   `IsColliderRest` (the last-edge case), keeping the symmetry
--   between left and right endpoints visible.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsColliderWalk
-- def_3_4 -- start statement
def IsColliderWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ (.nil _ _) => a = (u, v) ∧ a ∈ G.L
  | u, _, .cons v a _ (p@(.cons _ _ _ _)) =>
      (a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∧ p.IsColliderRest
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsColliderWalk

-- ref: def_3_4 (item~v, path)
--
-- `p.IsPath` iff the vertex sequence `[v_0, v_1, …, v_n]` is
-- duplicate-free.  The LN's "no node occurs more than once" is the
-- straightforward `List.Nodup` predicate on `p.vertices`.  The
-- trivial walk's singleton vertex list `[v_0]` is vacuously `Nodup`,
-- so the trivial walk is a path (matching the rewritten tex's
-- "vacuously a path").
--
-- ## Design choice
--
-- *Why a one-liner over `Walk.vertices`, not a structural recursion
--   on `Walk` directly.*  The LN item~v says "no node occurs more
--   than once", and the rewrite's "equivalently, the tuple $(v_0,
--   v_1, \dots, v_n)$ consists of $n + 1$ pairwise distinct entries"
--   makes the connection to a `Nodup` list predicate explicit.
--   `Walk.vertices` already extracts the LN's vertex tuple as a
--   `List Node`; combining with `List.Nodup` from mathlib makes
--   `IsPath` a single line and inherits every mathlib `Nodup`
--   lemma (decidability, monotonicity under sub-lists, …) for free.
--   A structural recursion `IsPath (cons v _ _ p) = v ∉ p.vertices
--   ∧ p.IsPath` would be equivalent but duplicate the body of
--   `List.Nodup` and re-derive its lemmas in the walk-specific
--   namespace.
--
-- *Trivial walk vacuously a path (`vertices = [v]` is `Nodup`).*
--   The LN explicitly admits this; `List.nodup_singleton` makes it
--   `rfl`-true in Lean.  No special case in `IsPath` is needed.
--
-- *Why the LN's "$v_i \ne v_j$ for $0 \le i < j \le n$" form is
--   not used directly.*  Index-based pairwise-distinctness would
--   force every consumer to reason about `List.get?`-indexing and
--   `Fin (n+1)`-arithmetic.  `List.Nodup` is the standard
--   index-free encoding, equivalent (`List.nodup_iff_get?_ne_get?`
--   in mathlib) and the consensus mathlib idiom.
--
-- *Downstream consumers.*  `def_3_6` acyclicity defines a CDMG as
--   acyclic iff there is no non-trivial directed walk `v → v`; the
--   "path" form is used in `def_3_7`+ (when the chapter introduces
--   shortest walks / longest paths) and chapters 6–7 (active paths
--   for d-/σ-separation).  Centralising `IsPath` here lets every
--   consumer write `(p : Walk …) (hp : p.IsPath)` uniformly.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsPath
-- def_3_4 -- start statement
def IsPath {u v : Node} (p : Walk G u v) : Prop := p.vertices.Nodup
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsPath

-- ref: def_3_4 (helper, bifurcation "left arm + hinge + right arm")
--
-- `p.IsBifurcationWithSplit i` says: `p` is a bifurcation walk in
-- which the left arm has exactly `i` reverse-directed edges (so the
-- hinge edge is at edge position `i`, corresponding to the LN's
-- split index `k = i + 1`).  Recursively:
-- * `nil`, any `i`: `False` — a bifurcation has at least the hinge
--   edge, so an empty walk cannot satisfy any split.
-- * `cons v a _ p, 0` — the *first* edge is the hinge.  Two sub-cases:
--   - `p = nil` (so `n = 1`, LN's `k = n` case): per addition
--     `[bifurcation_right_chain_trivial_is_just_directed_walk]`, the
--     hinge must be bidirected for `v_n` to have its required
--     arrowhead — `a = (u, v) ∧ a ∈ G.L`.
--   - `p = cons …` (so `n ≥ 2`, right arm non-trivial): both hinge
--     alternatives are admitted, `(v, u) ∈ E` (directed backward) or
--     `(u, v) ∈ L` (bidirected), and the right arm `p` must be a
--     directed walk.
-- * `cons v a _ p, i+1` — the first edge is a *left-arm* edge,
--   reverse-directed: `a = (v, u) ∧ a ∈ G.E`.  Recurse on `p` with
--   index `i`.
--
-- ## Design choice
--
-- *Why a helper indexed by a split position `i : ℕ`, rather than
--   inlining the LN's "$\exists k$" into `IsBifurcation` directly.*
--   The LN's item~vi quantifies over a split index $k$ with $1 \le
--   k \le n$ and case-splits the walk into a *left arm* ($v_0
--   \hut \cdots \hut v_{k-1}$), a *hinge* ($v_{k-1} \hus v_k$),
--   and a *right arm* ($v_k \tuh \cdots \tuh v_n$).  Spelling this
--   out as a single inline predicate quantifying over `k` would
--   need to *index into the edge list* `p.edges[k]` and carry the
--   bound `k ≤ length p` everywhere.  Recursing on `Walk`'s
--   structure with an explicit `ℕ` counter `i` (one less than the
--   LN's `k`, so `k = i + 1`) trivialises that bound: each `cons`
--   step decrements `i`, and the `nil`-case rules out
--   out-of-bounds splits via `False`.  No `Fin (length p + 1)`
--   plumbing, no list-indexing lemmas in downstream proofs.
--
-- *Why `IsBifurcation` then existentially quantifies over the
--   split, `∃ i, p.IsBifurcationWithSplit i`.*  The LN's split $k$
--   is determined by `p` alone (uniquely, given the structure), so
--   carrying it as a `ℕ`-parameter on the helper is purely a
--   recursion vehicle.  `IsBifurcation` is the LN's "is a
--   bifurcation" predicate (no split index visible); pushing the
--   `∃` to the outer layer keeps the LN naming clean while letting
--   downstream predicates that *do* care about the split index
--   (`IsBifurcationSource`, `IsBifurcationDirectedHingeWithSplit`)
--   reach into the helper directly.
--
-- *Why the `n = 1` hinge case is restricted to bidirected only
--   (`a = (u, v) ∧ a ∈ G.L`), excluding the directed backward
--   `(v, u) ∈ E` alternative.*  This is addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
--   load-bearing.  The LN-critic's
--   `bifurcation_admits_n1_k1_single_backward_or_bidirected_edge`
--   subtlety surfaced the degenerate $n = 1$, $k = 1$ case: under
--   the literal LN pattern, a single edge $v_0 \hus v_1$ could be
--   either $v_0 \hut v_1$ (directed backward, i.e. $w \to v$) or
--   $v_0 \huh v_1$ (bidirected).  Neither visually "bifurcates" —
--   the directed case is literally a directed walk of length 1.
--   The operator addition closes the directed-backward case via
--   the "both end-nodes have exactly one arrowhead pointing toward
--   them" constraint: for $a = v_n \to v_{n-1}$ ($n = 1$), the
--   arrowhead is at $v_{n-1} = v_0$, NOT at $v_n = v_1$ — so $v_n$
--   has no arrowhead, contradicting the addition.  Only the
--   bidirected hinge survives.  Same reasoning for the general
--   $k = n$ case (handled implicitly by the recursion: the
--   `cons … (.nil _ _), 0` branch is the only path that reaches
--   the hinge at the last edge of the walk).
--
-- *Why the `n ≥ 2` first-edge / hinge case admits both alternatives
--   `(v, u) ∈ E` and `(u, v) ∈ L`.*  When the right arm is
--   non-trivial (`p = cons …` matched), the LN rewrite item~vi
--   clause (d) — "the edge $a_{k-1}$ between $v_{k-1}$ and $v_k$
--   satisfies ($a_{k-1} = (v_k, v_{k-1}) \in E$) or ($a_{k-1} =
--   (v_{k-1}, v_k) \in L$)" — admits both writings.  The clause (e)
--   addition does *not* exclude either: both produce an arrowhead
--   at $v_{k-1}$ (directed `(v_k, v_{k-1}) ∈ E`: arrowhead at
--   $v_{k-1}$ by direction; bidirected `(v_{k-1}, v_k) ∈ L`:
--   arrowhead at $v_{k-1}$ by `\huh`).  The recursive right-arm
--   constraint `p.IsDirectedWalk` encodes clause (c)'s "$v_k \tuh
--   \cdots \tuh v_n$" verbatim.
--
-- *Why the left-arm step (`cons v a _ p, k + 1`) requires `a = (v,
--   u) ∧ a ∈ G.E` (reverse-directed `E`-edge).*  LN rewrite
--   item~vi clause (b): for every $j \in \{0, \dots, k-2\}$,
--   $a_j = (v_{j+1}, v_j) \in E$, i.e. each left-arm edge points
--   from $v_{j+1}$ to $v_j$ (away from the hinge, toward $v_0$).
--   In local naming, the first edge of a recursive call is at
--   position $j$, with `u = v_j` and `v = v_{j+1}`, so the LN form
--   `(v_{j+1}, v_j) = (v, u)` is exactly the pin `a = (v, u)`.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsBifurcationWithSplit
-- def_3_4 --- start helper
def IsBifurcationWithSplit : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | u, _, .cons v a _ (.nil _ _), 0 => a = (u, v) ∧ a ∈ G.L
  | u, _, .cons v a _ (p@(.cons _ _ _ _)), 0 =>
      ((a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)) ∧ p.IsDirectedWalk
  | u, _, .cons v a _ p, k + 1 =>
      a = (v, u) ∧ a ∈ G.E ∧ p.IsBifurcationWithSplit k
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: IsBifurcationWithSplit

-- ref: def_3_4 (item~vi, bifurcation)
--
-- `p.IsBifurcation` iff `p` is a bifurcation between its end-nodes
-- `u` and `v`.  Combines:
-- * the LN's "$v \ne w$" — `u ≠ v`;
-- * the LN's "both end-nodes occur exactly once" — `u ∉
--   p.vertices.tail` and `v ∉ p.vertices.dropLast`;
-- * the existence of a split index — `∃ i, p.IsBifurcationWithSplit
--   i` (this packages clauses (b)-(d) plus the (e) addition's
--   exclusion of `k = n` with directed hinge).
--
-- ## Design choice
--
-- *Why retain the split index `k` (as `i + 1`) inside
--   `IsBifurcationWithSplit`, even though `IsBifurcation` itself
--   only existentially quantifies it away.*  Downstream "source"
--   terminology — "the bifurcation has source $v_k$" (LN item~vi
--   final sentence) — depends on knowing *which* split realises
--   the bifurcation.  Without the helper carrying $i$, downstream
--   predicates like `IsBifurcationSource` would have to either
--   re-derive `k` from `p` (a non-trivial recursion identifying
--   the unique direction-reversal point) or carry an auxiliary
--   "split index" argument throughout chapter 3.  The helper
--   form lets `IsBifurcation` stay clean (LN-faithful, no $k$
--   visible) while `IsBifurcationSource` reaches into the same
--   helper with the directed-hinge restriction.
--
-- *Why "end-nodes appear exactly once" is encoded as `u ∉
--   p.vertices.tail` (`u` does not appear after position 0) and
--   `v ∉ p.vertices.dropLast` (`v` does not appear before the last
--   position).*  The LN rewrite item~vi clause (a) reads "$v_0
--   \notin \{v_1, \dots, v_n\}$ and $v_n \notin \{v_0, \dots,
--   v_{n-1}\}$" — exactly these two non-membership claims, encoded
--   via `List.tail` (drops the first element) and `List.dropLast`
--   (drops the last element).  This is *weaker* than `IsPath`'s
--   `Nodup` — interior vertices may repeat in a bifurcation (e.g.
--   the same vertex may appear in both the left and right arms
--   when one arm visits a node that the other passes through);
--   the LN bifurcation predicate explicitly only constrains the
--   end-nodes.  Encoding it as full `Nodup` would be a strict
--   over-restriction.
--
-- *Why `u ≠ v` is its own conjunct (clause (a) first half).*  The
--   LN says "$v \ne w$" explicitly.  Without this, the trivial
--   walk would satisfy the vertex-uniqueness clauses vacuously
--   (single-element list `[v]` has empty `tail` and empty
--   `dropLast`).  We follow the LN literally; the existence of
--   a split index `∃ i, …` independently rules out the trivial
--   walk (because `nil → False` for all `i`), but `u ≠ v`
--   strengthens the predicate to also rule out non-trivial cycles
--   `Walk G v v`.
--
-- *Why `IsBifurcation` is a top-level `def` returning `Prop`,
--   not a `structure` bundling the witness.*  A `structure`
--   `Bifurcation G u v` with fields for the split index, the two
--   arms, and the hinge would be closer to a "categorical" reading
--   ("a bifurcation *is* its decomposition") but would force every
--   consumer to construct or destructure the bundle.  The LN
--   treats "is a bifurcation" as a yes/no classification of the
--   walk; we match that, and downstream consumers who *need* the
--   split index can invoke `IsBifurcationWithSplit` directly.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsBifurcation
-- def_3_4 -- start statement
def IsBifurcation {u v : Node} (p : Walk G u v) : Prop :=
  u ≠ v ∧
  u ∉ p.vertices.tail ∧
  v ∉ p.vertices.dropLast ∧
  ∃ i, p.IsBifurcationWithSplit i
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsBifurcation

-- ref: def_3_4 (helper, bifurcation with directed hinge)
--
-- `p.IsBifurcationDirectedHingeWithSplit i` is the variant of
-- `IsBifurcationWithSplit` restricted to a *directed* hinge (clause
-- (d)'s first alternative `a_{k-1} = (v_k, v_{k-1}) ∈ E`), which is
-- the precondition for the LN's "source $v_k$" to be defined.  The
-- `n = 1` `k = n` branch is therefore `False` here — a length-1 walk
-- with a directed hinge has its arrowhead at `v_0` (so `v_n = v_1`
-- has none), excluded by clause (e).
--
-- ## Design choice
--
-- *Why a separate helper, not a flag on `IsBifurcationWithSplit`.*
--   The LN's "source" naming applies only when the hinge edge is
--   *directed* (clause (d)'s first alternative); the bidirected
--   alternative produces a bifurcation with *no* source defined.
--   Encoding this as a boolean `hingeIsDirected : Bool` parameter
--   on `IsBifurcationWithSplit` would conflate two predicates that
--   differ in the `n = 1` case (the general predicate admits the
--   bidirected hinge there; the directed-hinge variant rejects all
--   $n = 1$ cases per the clause (e) addition).  Keeping them as
--   two helpers keeps each predicate's unfolding pattern clean.
--
-- *Why the `n = 1` directed-hinge case is `False` (the second
--   `cons _ _ _ (.nil _ _), 0` branch).*  Per addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
--   when $n = k = 1$ with directed hinge $v_0 \hut v_1$ (i.e.\ the
--   edge $v_1 \to v_0$), the arrowhead is at $v_0$, NOT at
--   $v_1 = v_n$.  The addition's "both end-nodes have exactly one
--   arrowhead pointing toward them" requires $v_n$ to have its
--   arrowhead — failing here.  So this branch is unreachable
--   *under the addition*; encoding it as `False` makes the
--   predicate sound by construction.
--
-- *Why the `n ≥ 2` first-edge / hinge case pins the directed
--   form `a = (v, u) ∧ a ∈ G.E` (not the bidirected alternative).*
--   This is the *defining* difference from `IsBifurcationWithSplit`:
--   the directed-hinge variant restricts clause (d) to its first
--   alternative.  The right arm `p` (after the hinge) is still
--   required to be a directed walk (clause (c)), encoded as
--   `p.IsDirectedWalk`.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsBifurcationDirectedHingeWithSplit
-- def_3_4 --- start helper
def IsBifurcationDirectedHingeWithSplit : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ _ (.nil _ _), 0 => False
  | u, _, .cons v a _ (p@(.cons _ _ _ _)), 0 =>
      a = (v, u) ∧ a ∈ G.E ∧ p.IsDirectedWalk
  | u, _, .cons v a _ p, k + 1 =>
      a = (v, u) ∧ a ∈ G.E ∧ p.IsBifurcationDirectedHingeWithSplit k
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: IsBifurcationDirectedHingeWithSplit

-- ref: def_3_4 (item~vi, source of a bifurcation)
--
-- `p.IsBifurcationSource x` iff `p` is a bifurcation between `u`
-- and `v` AND there is a split index `i` for which the hinge is
-- directed AND `x = v_{i+1}` (LN's `v_k` for `k = i + 1`).  Combining
-- the "directed-hinge" restriction with clause (e), the source `x`
-- is automatically distinct from both end-nodes (`1 ≤ k ≤ n - 1` in
-- LN, i.e.\ `0 ≤ i ≤ n - 2` here), so it is an interior vertex.
--
-- Predicate form (not `Option Node`): the LN says "we say that the
-- bifurcation has source $v_k$", which reads as "`v_k` *is* a
-- source", not "the source is `v_k`".  A predicate keeps the
-- definition partial *and* match-friendly downstream (proofs use
-- `obtain ⟨i, h_hinge, h_eq⟩ := …` rather than `match Option …`).
--
-- ## Design choice
--
-- *Why a `Prop`-predicate on `x` (rather than an `Option Node`
--   accessor or a field on a bundled `Bifurcation` structure).*
--   The LN-critic's `bifurcation_source_can_be_endnode` subtlety
--   surfaced a real partiality concern: the LN's literal definition
--   ("if the edge $v_{k-1} \hus v_k$ is directed, we call $v_k$ the
--   source") would assign a "source" even in degenerate cases
--   (e.g.\ $k = n$ with directed hinge), making the source equal
--   an endnode and contradicting the intuitive Y-shape.  Addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`
--   closes those degenerate cases by excluding $k = n$ with
--   directed hinge — implemented here by
--   `IsBifurcationDirectedHingeWithSplit`'s `cons _ _ _ (.nil _ _),
--   0` branch returning `False`.  Combined with the addition,
--   whenever `IsBifurcationSource p x` holds, the split index
--   satisfies $1 \le k \le n - 1$ ($0 \le i \le n - 2$ here),
--   so the source is automatically an interior vertex distinct
--   from both endnodes.  An `Option Node` accessor would force a
--   "no source defined" sentinel value in every consumer; a
--   `Prop`-predicate `x is a source` reads more naturally and
--   makes the partiality structural.
--
-- *Why depending on `IsBifurcationDirectedHingeWithSplit` (and not
--   on `IsBifurcationWithSplit` plus a directed-hinge filter).*  A
--   single-helper variant
--   `∃ i, p.IsBifurcationWithSplit i ∧ <hinge edge is directed at
--   position i> ∧ p.vertices[i + 1]? = some x` is equivalent but
--   would need to spell out "hinge edge is directed at position
--   $i$" by re-traversing the walk to position $i$ — duplicating
--   the recursion already encoded in `IsBifurcationWithSplit`.
--   The separate `IsBifurcationDirectedHingeWithSplit` helper
--   factors out exactly the directed-hinge variant in one place;
--   `IsBifurcationSource` then just composes "directed-hinge
--   bifurcation at $i$" with "$x$ is at position $i + 1$" via the
--   list lookup `p.vertices[i + 1]?`.
--
-- *Why `p.vertices[i + 1]?` (the `Option`-valued indexed lookup),
--   not `p.vertices.get ⟨i + 1, h⟩`.*  Lean's `[i + 1]?`
--   accessor returns `Option Node` and unifies cleanly with the
--   `some x`-match.  The `.get` form would require an in-bounds
--   proof `i + 1 < p.vertices.length` threaded explicitly — but
--   the bound *is* a consequence of `IsBifurcationDirectedHingeWithSplit
--   i` (which constrains `i + 1 ≤ length p`), and forcing every
--   consumer to materialise this proof would add noise.  The
--   `Option`-form is the standard mathlib idiom for partial list
--   lookups.
--
-- *Why the endnode-uniqueness clauses (`u ≠ v`, `u ∉ vertices.tail`,
--   `v ∉ vertices.dropLast`) are repeated here from `IsBifurcation`,
--   rather than `IsBifurcationSource` being defined as
--   `p.IsBifurcation ∧ ∃ i, …`.*  Equivalent in content, but the
--   inlined form lets the predicate stand on its own — downstream
--   consumers that only care about "$x$ is a source of $p$" don't
--   need to chain through `IsBifurcation`'s existential.  The
--   redundancy is shallow (four conjuncts; the existential payload
--   is the only substantive difference).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsBifurcationSource
-- def_3_4 -- start statement
def IsBifurcationSource {u v : Node} (p : Walk G u v) (x : Node) : Prop :=
  u ≠ v ∧
  u ∉ p.vertices.tail ∧
  v ∉ p.vertices.dropLast ∧
  ∃ i, p.IsBifurcationDirectedHingeWithSplit i ∧ p.vertices[i + 1]? = some x
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsBifurcationSource

end Walk

end CDMG

end Causality

namespace Causality

namespace refactor_CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same
--   chapter convention used by the original `CDMG` namespace above
--   and by every other `refactor_CDMG`-opening file in the chapter
--   (`EdgeRelations.lean:357`, `CDMGNotation.lean`, etc.).  The
--   refactor does not alter the carrier-type discipline — only the
--   shape of the per-step walk-edge data and the `cons`-cell of
--   `Walk` — so the binders below are byte-identical to the original
--   `CDMG`-namespace variable line at `Walks.lean:114`.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds
--   these implicit binders into every refactored declaration below
--   exactly as it does for the originals.  The three-dash flavour
--   tags this as helper-level wrapping, consistent with how the
--   original `variable` line at `Walks.lean:113-115` and the
--   `EdgeRelations.lean:356-358` refactor variable line are tagged.
--   The Phase 7 cleanup-script's whole-word rename
--   (`refactor_<Name>` → `<Name>`) leaves the `def_3_4` marker text
--   inside this block untouched (the marker is a documentation
--   comment, not a declaration name).
-- def_3_4 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_4 --- end helper

-- ref: def_3_4 (item~i, WalkStep) — refactor
--
-- `G.refactor_WalkStep u v` is the **typed** carrier of "a valid
-- walk-edge from `u` to `v` in `G`": a `Type`-level inductive whose
-- three constructors enumerate the three LN-admissible channel /
-- direction combinations a walk-edge can take.  Replaces the original
-- `WalkStep : Prop`-level two-disjunct from `Walks.lean:166-168`.
--
-- ```
-- inductive refactor_WalkStep (G : refactor_CDMG Node) : Node → Node → Type _ where
--   | forwardE  {u v : Node} (h : (u, v) ∈ G.E)   : refactor_WalkStep G u v
--   | backwardE {u v : Node} (h : (v, u) ∈ G.E)   : refactor_WalkStep G u v
--   | bidir     {u v : Node} (h : s(u, v) ∈ G.L)  : refactor_WalkStep G u v
-- ```
--
-- The three constructors map directly onto the LN-item~i clause (b)
-- disjunction `a_k = (v_k, v_{k+1}) \in E \cup L  \lor  a_k =
-- (v_{k+1}, v_k) \in E`, but with the channel (`E` vs `L`) and
-- direction (forward vs backward, for the `E`-channel only) baked into
-- the constructor *tag* instead of recoverable only by destructuring a
-- stored ordered pair.  The driving rationale is documented in
-- `leanification/refactors/refactor_cdmg_typed_edges.md`; the rest of
-- the comment block records the local design decisions.
--
-- ## Design choice — `WalkStep` is a typed `Type`-level inductive, not a `Prop`-level disjunction
--
-- *Why a `Type`-level inductive with three constructors, not the
--   original `Prop`-level
--   `(a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∨ (a = (v, u) ∧ a ∈ G.E)`.*
--   The original encoding stored the walk-edge as an *ordered pair*
--   `a : Node × Node` plus a `Prop`-level witness that `a` was a valid
--   `E`/`L`-channel inhabitant — the channel and direction were
--   *implicit* in the witness's disjunct.  Three distinct problems
--   cascade out of this packaging, and the typed inductive resolves
--   all three at once:
--
--   - **Channel preservation under walk reversal.**  In the original
--     encoding, reversing a walk required *swapping the stored pair*
--     `(u, v) ↔ (v, u)` to keep the per-step disjunction satisfied
--     under the reversed traversal direction.  For an `L`-step
--     `(u, v) ∈ G.L`, the swap forced a `hL_symm` invocation to
--     re-establish `(v, u) ∈ G.L` on the reversed step.  On the
--     *writing-mirror* class of CDMGs admitted by the pre-refactor
--     `def_3_1` shape (where `(v, u) ∈ G.E` and `(u, v) ∈ G.L \ G.E`
--     can coexist), the swapped pair could *also* satisfy the
--     `E`-disjunct of the reversed walk-step, so downstream predicates
--     reading the channel off the stored pair (`def_3_16`'s
--     `IsBlockableNonCollider` E-check) would silently
--     misclassify an `L`-step as an `E`-step after reversal.  Under
--     the typed inductive, the channel is a *constructor tag* —
--     `.bidir h` stays `.bidir h` across `reverse`, and the
--     `.bidir`/`.forwardE`/`.backwardE` cases of any downstream
--     pattern match are structurally exclusive.  No pair swap, no
--     `hL_symm` invocation, no possibility of channel confusion.
--
--   - **Definitional pattern-matching on channel + direction.**
--     Downstream walk-class predicates (`refactor_IsDirectedWalk`,
--     `refactor_IsBidirectedWalk`, `refactor_IsColliderRest`, the
--     bifurcation hinge classifier, …) all need to ask "what channel
--     and direction is this walk-edge?" at every cons-cell.  Under
--     the original `Prop`-disjunction encoding the question is
--     phrased as `a = (u, v) ∧ a ∈ G.E`-style equalities that the
--     definition must `Or.inl`/`Or.inr`-case-split through.  Under
--     the typed inductive the question is phrased as `match s with
--     | .forwardE _ => ... | .backwardE _ => ... | .bidir _ => ...`,
--     which is exactly the LN's "this step is a directed-forward /
--     directed-backward / bidirected step" reading.  Every walk-class
--     predicate downstream collapses to a one-line pattern match.
--
--   - **`Type _`, not `Prop`.**  `Walk` itself lives at `Type _` (its
--     constructors carry edge witnesses + recursion).  Carrying the
--     per-step constraint at `Prop` and the walk inductive at `Type _`
--     forced every `Walk.cons` cell to thread a separate `WalkStep`
--     proof field whose two-way `Or` then surfaced in every
--     destructuring.  Promoting `WalkStep` to `Type _` aligns the two
--     types — the cons-cell now carries a single typed datum that *is*
--     the channel tag, and `Walk` consumers no longer have to thread
--     a separate `Prop`-witness alongside the walk data.
--
-- *Why three constructors `.forwardE` / `.backwardE` / `.bidir`, not
--   four (`+ .backwardL`).*  The LN's clause (b) admits four naïve
--   patterns: forward-`E`, backward-`E`, forward-`L`, backward-`L`.
--   Under the `def_3_1` refactor `L : Finset (Sym2 Node)` is now an
--   unordered-pair carrier — `s(u, v) = s(v, u)` *definitionally* via
--   Mathlib's `Sym2` swap quotient.  So a putative `.backwardL h` with
--   `h : s(v, u) ∈ G.L` would be byte-identical to `.bidir h` with
--   `h : s(u, v) ∈ G.L`.  Collapsing the two `L`-channel constructors
--   into a single `.bidir` is *not* a semantic concession — it reflects
--   the LN's own treatment of bidirected edges as channel-symmetric
--   ("$v \huh w$") and the `Sym2` typing's definitional swap symmetry.
--   The `E`-channel, by contrast, *does* carry direction information
--   (`(u, v) ∈ G.E` and `(v, u) ∈ G.E` are independent ordered-pair
--   memberships under `def_3_1`'s `E : Finset (Node × Node)`), so the
--   `forwardE` / `backwardE` split is preserved.  The asymmetry is a
--   direct consequence of the `def_3_1` root: directed edges are
--   ordered pairs, bidirected edges are quotiented pairs.
--
-- *Why `(h : (u, v) ∈ G.E)` and `(h : (v, u) ∈ G.E)` as constructor
--   arguments, not a stored pair `a` plus a separate membership
--   witness.*  The constructor's *type indices* `u v : Node` already
--   pin the source and target of the step at the type level — no
--   stored `a : Node × Node` is needed because `a` is recoverable
--   from the indices (for the `E`-cases) or canonical-up-to-swap
--   (for the `.bidir` case).  Dropping the stored pair makes the
--   `cons`-cell of `refactor_Walk` strictly leaner (the channel +
--   endpoints are *all* now part of the cons-cell's type indices,
--   not a runtime field).  See the design block above
--   `refactor_Walk` below for the downstream consequence.
--
-- *Why the `.bidir` argument is `s(u, v) ∈ G.L`, not `(u, v) ∈ G.L`
--   or `{u, v} ⊆ G.V ∧ ...`.*  Under the refactor `G.L : Finset
--   (Sym2 Node)` (see `CDMG.lean:389` and the `def_3_1` design block
--   for the rationale), so the canonical membership query on `L` is
--   `s(u, v) ∈ G.L` where `s(u, v)` is Mathlib's notation for
--   `Sym2.mk (u, v)` — the unordered pair viewed as an element of the
--   quotient.  This is the *literal* type of the L-channel argument;
--   any other formulation would force a re-derivation through `Sym2`'s
--   API at every L-step construction site.  The notation is the same
--   `s(...)` Mathlib uses elsewhere for `Sym2`, and the same notation
--   `refactor_huh` in `CDMGNotation.lean:833` uses to express
--   `v_1 \huh v_2 \in G`.  The cross-reference to `EdgeRelations.lean`'s
--   `refactor_E` (still `Finset (Node × Node)`, retained verbatim) and
--   `refactor_L` (now `Finset (Sym2 Node)`) is exactly the asymmetry
--   that motivates the channel-split of the constructors above.
--
-- *Why implicit `{u v : Node}` on every constructor, not explicit.*
--   The walk-step constructors are consumed primarily by pattern
--   matches inside `refactor_Walk.cons` and the walk-class
--   predicates downstream, where the endpoints are *already*
--   determined by the surrounding `Walk` type indices (the cons-cell
--   types its WalkStep as `refactor_WalkStep G u v` with `u` and `v`
--   pinned by the outer match).  Making `u v` explicit would force
--   every construction site to spell them out (`.forwardE (u := …)
--   (v := …) h`), even when they could be inferred from the membership
--   witness's type.  Implicit is the right default.
--
-- *Why a single inductive type, not three separate inductives
--   (`ForwardEStep`, `BackwardEStep`, `BidirStep`).*  Splitting would
--   force `refactor_Walk.cons` to be a higher-rank constructor taking
--   one of three differently-typed step witnesses — either via a
--   coproduct or via three `cons` constructors.  Either choice
--   explodes the cons-cell pattern surface area: every walk-class
--   predicate would have to enumerate three constructor cases per
--   cons-cell instead of one cons-cell + an inner three-way step
--   match.  The single-inductive shape factorises the cons + step
--   case analyses cleanly.  Mirrors how Mathlib's `Quiver.Path`
--   keeps the path's `cons` constructor uniform and lets the path's
--   *hom* type vary.
--
-- *Net-new declaration with no original counterpart at the markered
--   level.*  The original `def WalkStep` was a `Prop`-level helper
--   `def_3_4 --- start/end helper`-wrapped; the refactor replaces it
--   with a `Type _`-level inductive — same role (walk-step constraint
--   carrier) but a different syntactic category.  The
--   `REFACTOR-BLOCK-REPLACEMENT` marker pair wraps the entire
--   inductive declaration; the Phase 7 cleanup script will rename
--   `refactor_WalkStep` to `WalkStep` (whole-word) across every file
--   the refactor touches, leaving an inductive named `WalkStep` in the
--   final tree — which is exactly the LN's intended object.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: WalkStep (was: refactor_WalkStep)
-- def_3_4 -- start statement
inductive refactor_WalkStep (G : refactor_CDMG Node) : Node → Node → Type _ where
  | forwardE  {u v : Node} (h : (u, v) ∈ G.E) : refactor_WalkStep G u v
  | backwardE {u v : Node} (h : (v, u) ∈ G.E) : refactor_WalkStep G u v
  | bidir     {u v : Node} (h : s(u, v) ∈ G.L) : refactor_WalkStep G u v
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: WalkStep

-- ref: def_3_4 (item~i, Walk) — refactor
--
-- A *walk* from `u` to `v` in `G`, with the per-step constraint
-- carried by `refactor_WalkStep` instead of the original
-- `(a : Node × Node) + (h : G.WalkStep u a v)` ordered-pair-plus-Prop
-- pairing.  Inductive type with two constructors:
--
-- * `refactor_Walk.nil v hv` — the *trivial walk* `(v_0)` consisting
--   of a single node `v ∈ G`.  Identical to the original `Walk.nil`
--   modulo the `G` type retarget; `hv` remains as a stored membership
--   witness (see the design block below for why).
-- * `refactor_Walk.cons v s p` — prepend the alternating step
--   "$v_0, a_0, v_1$" in front of an existing walk `p` from `v_1` to
--   `w`.  The middle vertex `v_1` is the explicit `v` parameter (same
--   as the original); the LN-edge-constraint is now the *typed
--   WalkStep* `s : refactor_WalkStep G u v`.  No stored ordered pair
--   `a : Node × Node` — the channel and pair (where applicable) are
--   recovered from `s`'s constructor tag.
--
-- ```
-- inductive refactor_Walk (G : refactor_CDMG Node) : Node → Node → Type _ where
--   | nil  (v : Node) (hv : v ∈ G) : refactor_Walk G v v
--   | cons {u w : Node} (v : Node)
--       (s : refactor_WalkStep G u v) (p : refactor_Walk G v w)
--       : refactor_Walk G u w
-- ```
--
-- ## Design choice — `cons` no longer stores `a : Node × Node`
--
-- *Why drop the original `(a : Node × Node)` field on `cons`.*  Under
--   the typed `refactor_WalkStep`, the endpoints `u` and `v` of a
--   single walk-step are *already* present as the WalkStep's type
--   indices.  Storing them again as a runtime field `a = (u, v)` (or
--   `a = (v, u)`) would be (i) redundant — the indices pin the
--   endpoints; (ii) ambiguous on the `.bidir` constructor — `s(u, v)
--   = s(v, u)` *definitionally* under the `Sym2` quotient, so there
--   is no canonical ordered-pair representative to store (`def_3_1`'s
--   refactor design block at `CDMG.lean:281-336` and the workspace's
--   decision (1) record this rationale).  Pattern-matches downstream
--   that previously read `a` off `Walk.cons` now read the
--   constructor tag + indices off the WalkStep — cleaner and
--   misclassification-free.
--
-- *Why drop the original `(h : G.WalkStep u a v)` Prop field on
--   `cons`.*  Same point in reverse: the typed `WalkStep` *replaces*
--   the (`a`, `h`) pair with a single `s : refactor_WalkStep G u v`
--   datum.  The constructor tag of `s` *is* the channel; the
--   constructor's argument *is* the LN-membership witness
--   (`(u, v) ∈ G.E` / `(v, u) ∈ G.E` / `s(u, v) ∈ G.L`).  No proof
--   field is left orphaned — every bit of information the original
--   `Prop` witness carried is now carried by the typed step's data.
--
-- *Why keep `(hv : v ∈ G)` on `nil`.*  Same rationale as the
--   original `Walk.nil` (preserved verbatim from `Walks.lean:248`'s
--   design block): for the trivial walk (`n = 0`, single node `v`),
--   there is no edge from which the `J ∪ V`-membership of `v` could
--   be recovered, so `nil`'s constructor carries the witness
--   directly.  For `n ≥ 1`, each new vertex sits at the head of an
--   `E` or `L` edge — `refactor_CDMG.hE_subset` and `hL_subset`
--   recover its membership from the cons-cell's WalkStep without an
--   extra field on `cons`.  The asymmetry is the same as in the
--   original and is minimal: data is added exactly where it cannot
--   be inferred.  The `v ∈ G` notation here resolves via
--   `CDMGNotation.lean:587`'s `refactor_instMembership`
--   (`Membership Node (refactor_CDMG Node)`), so the `nil`
--   constructor's membership check unfolds to `v ∈ G.J ∪ G.V` as in
--   the LN.
--
-- *Why keep the explicit middle vertex `v` on `cons`, not switch to
--   the implicit `{u v w}` SimpleGraph.Walk-style convention.*  This
--   matches the original's choice at `Walks.lean:249`.  The seven
--   Walk-namespace predicates in Phases B-E (`refactor_length`,
--   `refactor_vertices`, `refactor_intoStart`, `refactor_outOfStart`,
--   `refactor_intoEnd`, `refactor_outOfEnd`, `refactor_IsDirectedWalk`,
--   `refactor_IsBidirectedWalk`, `refactor_IsColliderRest`,
--   `refactor_IsColliderWalk`, `refactor_IsPath`,
--   `refactor_IsBifurcationWithSplit`, `refactor_IsBifurcation`,
--   `refactor_IsBifurcationDirectedHingeWithSplit`,
--   `refactor_IsBifurcationSource`) all pattern-match on `.cons v s p`
--   and refer to `v` (the LN's `v_1` in the cons-cell) by name.
--   Promoting `v` to explicit lets those patterns continue to read
--   naturally; the small ergonomic cost (one extra arg per `cons`
--   call site) is paid by downstream constructors, not by this file.
--   `{u w}` *do* stay implicit because they are pinned by the outer
--   walk's type indices — every consumer of a walk has them
--   determined by the walk type and never needs to spell them out
--   in a pattern.  The shape mirrors the original's
--   `{u w : Node} (v : Node) (a : Node × Node) (h : G.WalkStep u a v)
--   (p : Walk G v w)` exactly, with `(a, h)` replaced by the single
--   typed step `s`.
--
-- *Why `inductive Type _`, not `List (refactor_WalkStep G u v) +
--   coherence`.*  Same rationale as the original (`Walks.lean:204-216`
--   design block).  Walks carry data that downstream chapters consume
--   by recursion; pattern-matching on `nil` vs `cons` reads exactly
--   like the LN's "$v_0, a_0, v_1, \dots$".  A `List`-plus-coherence
--   encoding would force every consumer to thread a coherence proof
--   one edge at a time.  The inductive shape factorises the LN's
--   alternating-sequence recursion structurally.
--
-- *Two-vertex index `refactor_Walk G u v`, endpoints in the type.*
--   Unchanged from the original; the LN's "*walk from $v$ to $w$*"
--   phrasing pins both endpoints into the type, and the trivial walk
--   has type `refactor_Walk G v v` enforcing the "$v = w$"
--   precondition at the type level.  No regression on this front.
--   The refactor keeps this discipline because it is *load-bearing*
--   for the typed `refactor_WalkStep`: the cons-cell's WalkStep
--   `s : refactor_WalkStep G u v` *requires* the outer walk's start
--   index `u` and the middle vertex `v` at the type level (the
--   WalkStep's own indices are pinned to these), so the type-level
--   start/end indexing is what makes the WalkStep refactor coherent
--   in the first place.  Downstream consequence: an entire class of
--   "walk start/end mismatch" proof obligations is eliminated by
--   construction — pattern matches on `.cons _ s p` cannot produce
--   ill-typed cons cells (Lean's typechecker rejects them at
--   elaboration), and no separate `Walk.start = u` /
--   `Walk.end = w` accessor lemmas are needed.  The walk-class
--   predicates and bifurcation helpers below all rely on this:
--   every pattern match `cons _ (.forwardE _) p` has `p : Walk G v w`
--   with `v` and `w` pinned by the outer walk's indices, so the
--   recursive call `p.refactor_…` typechecks without any explicit
--   endpoint arithmetic.
--
-- *Net-new declaration shape; ORIGINAL still compiles.*  The original
--   `inductive Walk` (at `Walks.lean:247-251`) remains in place under
--   the original `CDMG` namespace, so any not-yet-refactored downstream
--   consumer (`def_3_5`, `def_3_6`, etc.) continues to compile against
--   the original shape until its own refactor row lands.  The
--   `REFACTOR-BLOCK-REPLACEMENT` marker pair wraps the entire
--   replacement inductive; Phase 7 cleanup renames `refactor_Walk`
--   to `Walk` globally across every refactored file, leaving an
--   inductive named `Walk` in the final tree.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk (was: refactor_Walk)
-- def_3_4 -- start statement
inductive refactor_Walk (G : refactor_CDMG Node) : Node → Node → Type _ where
  | nil  (v : Node) (hv : v ∈ G) : refactor_Walk G v v
  | cons {u w : Node} (v : Node)
      (s : refactor_WalkStep G u v) (p : refactor_Walk G v w) : refactor_Walk G u w
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk

namespace refactor_Walk

-- ## Design choice — refactor_Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : refactor_CDMG Node}`.*  Every
--   declaration in this namespace recurses over a walk
--   `p : refactor_Walk G u v`.  Without the namespace-wide `variable`,
--   every signature would carry an explicit `{G : refactor_CDMG Node}`
--   binder.  Mirrors the original `namespace Walk` opening at
--   `Walks.lean:282-284` byte-for-byte modulo the `CDMG → refactor_CDMG`
--   type retarget — neither the implicit-vs-explicit convention nor
--   the marker shape needed adjustment in the refactor.  Downstream
--   consumers reach into `G` via dot-notation on the walk
--   (`p.refactor_length`, `p.refactor_vertices`), so the `{G}`
--   implicit-binder convention from the original carries over verbatim.
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the original (`Walks.lean` `namespace Walk` block) and
--   as the refactor section's section-wide `variable` at
--   `Walks.lean:1169-1171`: this `{G}` binder is load-bearing
--   infrastructure that the tex/Lean reconciliation tooling and the
--   Phase 7 cleanup script must recognise as helper-flavour.
-- def_3_4 --- start helper
variable {G : refactor_CDMG Node}
-- def_3_4 --- end helper

-- ref: def_3_4 / def_3_6 (helper, walk length) — refactor
--
-- `Walk.refactor_length p` is the number `n` of edges in `p` (matches
-- the LN's `n`).  Body identical to the original `Walk.length`
-- (`Walks.lean` `def length` ORIGINAL block) modulo the `cons`-cell
-- pattern change: the original `.cons _ _ _ p` skipped four
-- constructor arguments (`v`, `a`, `h`, `p`); the refactored
-- `.cons _ _ p` skips three (`v`, `s`, `p`), reflecting the new
-- constructor signature of `refactor_Walk.cons` documented in the
-- design block at `Walks.lean:1462-1469`.
--
-- ## Design choice — refactor_length
--
-- *Why the refactor needs to touch this helper.*  `length` is a pure
--   structural recursion on the `Walk` constructors.  Phase A changed
--   the `cons`-cell signature — dropped the stored `(a : Node × Node)`
--   and re-typed the per-step witness from `WalkStep`-Prop to the
--   typed inductive `refactor_WalkStep`.  So every recursion on
--   `refactor_Walk` that previously matched `.cons _ _ _ p` (four
--   args) now matches `.cons _ _ p` (three args).  The cons-cell
--   shape change is the *only* delta; the recursion structure, the
--   natural-number return type, the LN-correspondence `n` (the LN's
--   "$v_0, a_0, v_1, \dots, v_n$"), and the `length` semantics are
--   unchanged.  Decision (5) in the workspace plan confirms this is
--   a pure structural-port helper.
--
-- *Why the inner `def_3_6 --- start/end helper` markers are preserved
--   verbatim inside the REPLACEMENT block.*  `length` is conceptually
--   a helper for `def_3_6` acyclicity (which counts non-trivial
--   directed walks `v → v`), but it lives in `Walks.lean` because
--   `Walk` must exist for `length` to typecheck.  The
--   `def_3_6 --- start/end helper` marker records *concept ownership*
--   (the LN reference for the helper's role), not *refactor scope*.
--   Per workspace decision (5), we keep these inner markers untouched;
--   the REFACTOR-BLOCK-REPLACEMENT markers wrap *around* them.  After
--   Phase 7 cleanup, the renamed `length` ends up at this same
--   position with its `def_3_6 --- start/end helper` markers still
--   pointing at the def_3_6 ownership reference.
--
-- *Recursion via `p.refactor_length`, not a sigma-typed helper or
--   auxiliary length counter.*  The recursive call `p.refactor_length`
--   resolves through dot-notation on `p : refactor_Walk G v w` (the
--   `cons` constructor's third argument).  The dot-notation lookup
--   finds `refactor_Walk.refactor_length` in this namespace, exactly
--   as the original `p.length` finds `Walk.length`.  Lean 4's
--   structural-recursion checker accepts the recursion directly on
--   `refactor_Walk` — no `termination_by` annotation, no
--   sigma-typed intermediary, no auxiliary walk-length helper.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: length (was: refactor_length)
-- def_3_6 --- start helper
def refactor_length : ∀ {u v : Node}, refactor_Walk G u v → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ p => p.refactor_length + 1
-- def_3_6 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: length

-- ref: def_3_4 (helper, vertex sequence) — refactor
--
-- `Walk.refactor_vertices p` is the list `[v_0, v_1, …, v_n]` from
-- LN item~i, i.e.\ the ordered sequence of vertices traversed by `p`.
-- Body identical to the original `Walk.vertices` (`Walks.lean`
-- `def vertices` ORIGINAL block) modulo the `cons`-cell pattern
-- change: `.cons _ _ _ p` becomes `.cons _ _ p`, matching the new
-- constructor signature of `refactor_Walk.cons` documented at
-- `Walks.lean:1462-1469`.
--
-- ## Design choice — refactor_vertices
--
-- *Why the refactor needs to touch this helper.*  Same cons-cell
--   signature change as `refactor_length` above: the original
--   `.cons _ _ _ p` four-arg pattern becomes the refactor's
--   `.cons _ _ p` three-arg pattern.  The recursion structure, the
--   `List Node` return type, and the LN-traversal semantics
--   ("$v_0, v_1, …, v_n$") are unchanged.  Decision (5) in the
--   workspace plan confirms this is a pure structural-port helper.
--
-- *Why `List Node` and not `Finset` / `Fin (n+1) → Node`.*  Unchanged
--   from the original (`Walks.lean` `def vertices` ORIGINAL block's
--   design notes).  The LN's tuple is ordered and may repeat, ruling
--   out `Finset`; a length-indexed function would impose
--   `Fin`-arithmetic plumbing on every consumer of `refactor_IsPath`
--   (which wants `vertices.Nodup` directly).  The Mathlib `List`-API
--   (`Nodup`, `head?`, `getLast?`, `tail`, `dropLast`) is the natural
--   toolkit and remains so under the refactor.
--
-- *Asymmetry: `nil` case carries `v` in the list; `cons` case
--   prepends `u` and recurses on `p`.*  Unchanged from the original.
--   Avoids double-counting the middle vertex `v` (which already
--   appears as `p`'s head element) and matches the LN's
--   "$v_0, v_1, …, v_n$" convention exactly.
--
-- ## Why no `refactor_edges`
--
-- *The original `Walk.edges` is dropped entirely under the refactor;
--   no `refactor_edges` REPLACEMENT counterpart exists.*  The original
--   `Walk.edges : Walk G u v → List (Node × Node)` (the wrapped
--   ORIGINAL block above) projected the stored ordered pair
--   `a : Node × Node` out of each `cons`-cell.  Under the typed
--   `refactor_WalkStep` refactor, the `cons`-cell no longer stores
--   `a` — the channel comes from the WalkStep constructor tag and
--   the endpoints come from the WalkStep's type indices.  There is
--   nothing to project: the original ordered-pair carrier has been
--   dissolved into the WalkStep's typed structure.
--
-- *Why not synthesise a canonical `(u, v)` per constructor (option
--   b).*  Considered and rejected.  The `.forwardE` and `.backwardE`
--   cases admit a canonical ordered-pair representative (`(u, v)`
--   resp. `(v, u)`), but the `.bidir` case does not: its membership
--   witness is `s(u, v) ∈ G.L` with `Sym2 Node` carrier, and
--   `s(u, v) = s(v, u)` *definitionally* under the `Sym2` quotient.
--   No canonical ordered-pair representative is available for the
--   bidirected channel without arbitrarily picking one of the two
--   orderings, and any downstream consumer reading the synthesised
--   pair would have to handle the `.bidir` case as "either ordering
--   acceptable", reintroducing the channel-confusion the typed
--   refactor was designed to eliminate.
--
-- *Why not a sigma-typed `List (Σ u v, refactor_WalkStep G u v)`
--   (option c).*  Considered and rejected as heavyweight.  Every
--   downstream consumer of the edge list would have to thread
--   `Sigma.fst` / `Sigma.snd` plumbing to recover the endpoints from
--   each element; the sigma wrapping adds boilerplate at every use
--   site for no semantic gain (the same information is already
--   accessible on the cons-cell at the point of recursion, without
--   any wrapping).
--
-- *Decision: drop entirely (option a).*  The only in-file consumers
--   of `p.edges.getLast?` are the end-node classifiers `intoEnd` and
--   `outOfEnd` (originals in this file).  Both are refactored in
--   Phase C to recurse on `refactor_Walk` directly: peel cons-cells
--   until the tail is `nil`, then read the WalkStep on the last
--   `cons`.  Channel + endpoints come from the WalkStep constructor
--   at the point of use — no intermediate `List` carrier is needed.
--   This is the canonical record of decision (1) in the workspace
--   plan (`workspace_def_3_4.md` §"Recommendations on the 7 design
--   decisions" item 1) and the driving rationale in
--   `leanification/refactors/refactor_cdmg_typed_edges.md`.
--
-- *External consumer impact.*  Any future row downstream of this
--   file that grepped for `p.edges` will need to switch to direct
--   `Walk` recursion (the Phase C pattern) or, if it genuinely needs
--   an edge list, build one locally over `refactor_vertices` zipped
--   with WalkStep constructor projections.  The find_dependents scan
--   logged at refactor init flagged the in-file consumers
--   (`intoEnd`, `outOfEnd`) handled by Phase C; cross-file consumers
--   are addressed by their own refactor rows.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: vertices (was: refactor_vertices)
-- def_3_4 --- start helper
def refactor_vertices : ∀ {u v : Node}, refactor_Walk G u v → List Node
  | _, _, .nil v _ => [v]
  | u, _, .cons _ _ p => u :: p.refactor_vertices
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: vertices

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: edges
-- The pre-refactor `Walk.edges` accessor returned a `List (Node × Node)`
-- by reading off the explicit `a : Node × Node` field of each `cons`
-- step.  Under `cdmg_typed_edges` the new `Walk` keeps no such field —
-- the `WalkStep` constructor itself carries the typed witness
-- (`.forwardE` / `.backwardE` / `.bidir`) — so a single uniform "edges"
-- projection no longer makes sense at the walk level; every consumer
-- that previously inspected `p.edges` has been ported (or is being
-- ported) to pattern-match on the typed `WalkStep` directly.  This
-- empty REPLACEMENT block exists only so the finalize-time marker
-- validator can pair the ORIGINAL `edges` block with a same-named
-- REPLACEMENT.
-- REFACTOR-BLOCK-REPLACEMENT-END: edges

-- ref: def_3_4 (item~i, end-node classifier "into v_0") — refactor
--
-- `refactor_Walk.refactor_intoStart p` iff `p` is non-trivial AND its
-- first WalkStep places an arrowhead at v_0 (the LN's `\hus` at the
-- start node).  Reads the cons-cell's typed WalkStep directly: a
-- `.forwardE` first-step is "out of v_0" (LN `\tuh`), NOT into v_0 →
-- `False`; a `.backwardE` first-step encodes `(v_1, v_0) ∈ E`,
-- placing an arrowhead at v_0 → `True`; a `.bidir` first-step encodes
-- `s(v_0, v_1) ∈ L`, also placing an arrowhead at v_0 → `True`.  The
-- trivial walk is vacuously `False`.
--
-- ## Design choice — refactor_intoStart
--
-- *Why the refactor needs to touch this classifier.*  Same `cons`-cell
--   shape change that drove `refactor_length` / `refactor_vertices`
--   above.  The original `intoStart` (`Walks.lean` `intoStart`
--   ORIGINAL block) read the LN's "$a_0 = \dots$" disjunction off the
--   stored `(a : Node × Node)` field via `G.into u a`.  Under the
--   typed `refactor_WalkStep` (Phase A), the channel and the arrowhead
--   direction are *already* encoded in the WalkStep's constructor
--   tag — there is no stored ordered pair to consult, and `G.into`
--   (which took an ordered-pair argument) is not directly applicable
--   to a typed step.  The natural rewrite is a constructor case-split
--   on the cons-cell's WalkStep, returning `Prop`-valued `True` /
--   `False` per constructor.
--
-- *Decision (2) — single unified Prop, no per-channel split.*  Per
--   workspace plan (`workspace_def_3_4.md` §"Recommendations on the
--   7 design decisions", item 2) we keep ONE Prop matching all three
--   constructor cases, rather than mirroring `EdgeRelations`'
--   upstream `refactor_intoE` / `refactor_intoL` split.  The upstream
--   `intoE` / `intoL` split was forced because L's *carrier type*
--   changed from `Node × Node` to `Sym2 Node` — a single ordered-pair
--   argument could no longer typecheck for both channels.  No such
--   pressure exists at walk-step level: the typed `refactor_WalkStep`
--   already absorbs all three channel cases into one inductive, so a
--   unified Prop on `refactor_Walk` consumes a single WalkStep through
--   a uniform constructor case-analysis.  A channel-split here
--   (`refactor_intoStartE` / `refactor_intoStartL`) would double the
--   predicate count without semantic gain and would break the LN's
--   channel-neutral "into v_0" phrasing.  Decision (2) carries to
--   `refactor_outOfStart`, `refactor_intoEnd`, and `refactor_outOfEnd`
--   below for the same reason.
--
-- *Why `.bidir → True` — bidirected first edge qualifies as "into
--   v_0".*  The LN's symbolic pattern for "into v_0" is `a_0 = v_0
--   \hus v_1`.  The macro `\hus` matches both `\hut` (backward-E,
--   arrowhead at v_0 from the right) AND `\huh` (bidirected, arrowhead
--   at both endpoints) — both place an arrowhead at v_0.  The LN-
--   critic's `into_out_of_undefined_for_trivial_walk` subtlety
--   surfaces this convention explicitly: a bidirected first edge
--   makes the walk "into v_0" (`\hus`-matched) but NOT "out of v_0"
--   (which requires `\tuh`, E-only).  So `.bidir → True` here is the
--   canonical encoding of `\hus`'s admittance of bidirected edges;
--   downstream consumers can rely on this without re-deriving from
--   the LN's macro semantics.  This produces a *non-partition* shape
--   on bidirected first edges: `refactor_intoStart p ∧
--   ¬ refactor_outOfStart p` — see `refactor_outOfStart` below for
--   the contrasting `.bidir → False` branch.
--
-- *Why the trivial walk is `False`.*  Same vacuity reading as the
--   original (`Walks.lean` `intoStart` ORIGINAL design block): on the
--   trivial walk no `a_0` exists, so the LN's existentially-loaded
--   "$a_0 = \dots$" clause is vacuously false.  An `nil → True`
--   reading would silently include trivial walks in BOTH the "into"
--   and "out of" categories, breaking downstream conditional checks
--   ("walk is into v_0 ⇒ walk has at least one edge").
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: intoStart (was: refactor_intoStart)
-- def_3_4 -- start statement
def refactor_intoStart : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) _ => False
  | _, _, .cons _ (.backwardE _) _ => True
  | _, _, .cons _ (.bidir _) _ => True
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: intoStart

-- ref: def_3_4 (item~i, end-node classifier "out of v_0") — refactor
--
-- `refactor_Walk.refactor_outOfStart p` iff `p` is non-trivial AND its
-- first WalkStep is a *forward*-E edge `(v_0, v_1) ∈ E` (the LN's
-- `\tuh` at v_0 — tail at v_0 with arrowhead at v_1).  Reads the
-- cons-cell's typed WalkStep directly: only `.forwardE` qualifies →
-- `True`; `.backwardE` puts an arrowhead at v_0 (no tail there) →
-- `False`; `.bidir` is `\huh`, with arrowheads at both endpoints →
-- `False` (LN's "out of" is E-only `\tuh`, NOT bidirected).  The
-- trivial walk is vacuously `False`.
--
-- ## Design choice — refactor_outOfStart
--
-- *Mirror of `refactor_intoStart`.*  Same rationale on all structural
--   points: the typed-WalkStep refactor dissolves the original's
--   stored `(a : Node × Node)` carrier (so `G.outOf u a` has no direct
--   counterpart), so the rewrite case-splits on the cons-cell's
--   WalkStep constructor; we keep a single unified Prop (decision 2)
--   rather than a per-channel split, since the typed WalkStep already
--   absorbs the channel distinction; trivial walk is vacuously
--   `False`.  See `refactor_intoStart`'s design block above for the
--   full justification of the unified-Prop choice and the trivial-
--   walk convention.
--
-- *Why `.bidir → False` — bidirected first edge is NOT "out of v_0".*
--   The LN's symbolic pattern for "out of v_0" is `a_0 = v_0 \tuh
--   v_1` — strictly `\tuh` (tail at v_0, arrowhead at v_1, E-only).
--   The bidirected macro `\huh` does NOT match `\tuh`: `\huh` places
--   an arrowhead at v_0, where `\tuh` requires a tail.  Equivalently,
--   the LN's "out of" relation (def_3_3 item~iii) excludes L-edges
--   entirely.  So `.bidir → False` is the canonical encoding: a
--   bidirected first edge produces `refactor_intoStart p ∧
--   ¬ refactor_outOfStart p`, the same non-partition shape flagged
--   by the LN-critic's `into_out_of_undefined_for_trivial_walk`
--   subtlety and recorded in the `refactor_intoStart` block above.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: outOfStart (was: refactor_outOfStart)
-- def_3_4 -- start statement
def refactor_outOfStart : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) _ => True
  | _, _, .cons _ (.backwardE _) _ => False
  | _, _, .cons _ (.bidir _) _ => False
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: outOfStart

-- ref: def_3_4 (item~i, end-node classifier "into v_n") — refactor
--
-- `refactor_Walk.refactor_intoEnd p` iff `p` is non-trivial AND its
-- *last* WalkStep places an arrowhead at v_n (the LN's `\suh` at the
-- end node).  Walks the cons chain via direct recursion until the
-- tail is `.nil _ _`, at which point the outer cons-cell's WalkStep
-- IS the last edge; case-splits on the constructor tag:
-- `.forwardE` encodes `(v_{n-1}, v_n) ∈ E` with arrowhead at v_n →
-- `True`; `.backwardE` encodes `(v_n, v_{n-1}) ∈ E` with tail at v_n
-- → `False`; `.bidir` encodes `s(v_{n-1}, v_n) ∈ L` with arrowhead
-- at v_n → `True`.  The trivial walk is vacuously `False`.
--
-- ## Design choice — refactor_intoEnd
--
-- *Decision (3) — direct `refactor_Walk` recursion, NO separate
--   `refactor_lastStep` helper.*  The original `intoEnd` reached the
--   last edge via `p.edges.getLast?`.  Under the refactor, `edges`
--   is dropped entirely — see the WHY-no-`refactor_edges` block above
--   the `refactor_vertices` REPLACEMENT for the full rationale; the
--   short version is that under the typed `refactor_WalkStep` the
--   original ordered-pair carrier is dissolved into the WalkStep's
--   typed structure and no canonical `(u, v)` representative is
--   recoverable from the `.bidir` case (Sym2 has no canonical
--   ordering), so `getLast?` has no direct counterpart.  Per workspace
--   decision (3), the natural replacement is direct recursion on
--   `refactor_Walk`: peel cons-cells until the tail is `nil`, then
--   read the WalkStep on the last `cons`.  A separate
--   `refactor_lastStep` sigma-typed helper (`Σ u', refactor_WalkStep
--   G u' v`) was considered and rejected — it forces a
--   wrap/unwrap pass and adds a net-new declaration with no
--   downstream re-use; inline recursion is simpler and keeps the
--   predicate self-contained.
--
-- *Cost the design pays.*  The "peel-cons-until-nil" recursion is
--   duplicated structurally in two predicates: this one
--   (`refactor_intoEnd`) and the mirror `refactor_outOfEnd` below.
--   Both share the same five-branch pattern (`nil`, three
--   constructor-tagged length-1-tail branches, one recursion case)
--   and differ only in the `True` / `False` assignments per
--   constructor tag.  The duplication was accepted (over factoring
--   the recursion through a hypothetical `refactor_Walk.last` /
--   `refactor_lastStep` helper) because (i) a helper that returns a
--   sigma-typed last step would need its own correctness lemma
--   ("`p.last = .cons _ s (.nil _ _) ↔ s = …`") and the two end-
--   classifier predicates would gain nothing simpler in exchange;
--   (ii) the duplicated recursion is shallow (one pattern per
--   constructor tag, no nested logic), so the maintenance burden is
--   bounded by the three-constructor count of `refactor_WalkStep`
--   and does not grow as new walk-class predicates are added; (iii)
--   keeping the two predicates self-contained makes the LN-
--   correspondence ("`refactor_intoEnd` encodes `\suh` at $v_n$";
--   "`refactor_outOfEnd` encodes `\hut` at $v_n$") readable in a
--   single-file local view, without having to follow a helper's
--   indirection.  The cost is real but small and localised.
--
-- *Recursion structurally bottoms out on `.cons _ _ (.nil _ _)`.*
--   The pattern `.cons _ step (.nil _ _)` matches a cons whose tail
--   is `nil` — i.e. the cons we just matched IS the last cons-cell,
--   and `step` IS the last WalkStep.  The recursive case
--   `.cons _ _ (p@(.cons _ _ _))` peels the outer cons (whose step we
--   ignore — only the last step matters) and recurses on `p` (the
--   strictly-smaller inner cons walk).  This shape mirrors
--   `IsColliderRest`'s "match on the next cons" idiom at
--   `Walks.lean:719-726` byte-for-byte modulo the cons-arg count
--   change (4 → 3); naming the bottoming-out pattern keeps future
--   readers from rebuilding the structure from scratch and serves as
--   the template for `refactor_outOfEnd` below.
--
-- *Decision (2) reapplied — single unified Prop on the last
--   WalkStep.*  Same rationale as `refactor_intoStart`: the typed
--   `refactor_WalkStep` already absorbs the three channel cases, so
--   a uniform constructor case-analysis on the last step suffices.
--   No `refactor_intoEndE` / `refactor_intoEndL` split needed.
--
-- *Why the three "last edge" branches encode the LN's `\suh` at
--   v_n.*  The LN's symbolic pattern for "into v_n" is `a_{n-1} =
--   v_{n-1} \suh v_n` — `\suh` matches `\tuh` (forward-E, arrowhead
--   at v_n) and `\huh` (bidirected, arrowhead at v_n) but NOT `\hut`
--   (backward-E, arrowhead at v_{n-1}, tail at v_n).  At the *last*
--   edge under the refactor, the constructor cases map: `.forwardE`
--   → forward-E `(v_{n-1}, v_n)`, arrowhead at v_n → `True`;
--   `.backwardE` → backward-E `(v_n, v_{n-1})`, tail at v_n →
--   `False`; `.bidir` → bidirected `s(v_{n-1}, v_n)`, arrowhead at
--   v_n → `True`.
--
-- *Why the trivial walk is `False`.*  Same vacuity reading as
--   `refactor_intoStart` above: on the trivial walk no `a_{n-1}`
--   exists, so the LN's existentially-loaded clause is vacuously
--   false.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: intoEnd (was: refactor_intoEnd)
-- def_3_4 -- start statement
def refactor_intoEnd : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _) => True
  | _, _, .cons _ (.backwardE _) (.nil _ _) => False
  | _, _, .cons _ (.bidir _) (.nil _ _) => True
  | _, _, .cons _ _ (p@(.cons _ _ _)) => p.refactor_intoEnd
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: intoEnd

-- ref: def_3_4 (item~i, end-node classifier "out of v_n") — refactor
--
-- `refactor_Walk.refactor_outOfEnd p` iff `p` is non-trivial AND its
-- *last* WalkStep is a *backward*-E edge `(v_n, v_{n-1}) ∈ E` (the
-- LN's `\hut` at v_n — tail at v_n with arrowhead at v_{n-1}).  Same
-- direct-recursion access path as `refactor_intoEnd`: peel cons-cells
-- until the tail is `.nil _ _`, then case-split on the last cons-
-- cell's WalkStep: `.forwardE` puts an arrowhead at v_n → `False`;
-- `.backwardE` puts a tail at v_n → `True`; `.bidir` puts an arrowhead
-- at v_n → `False` (LN's "out of v_n" is E-only `\hut`, NOT
-- bidirected).  The trivial walk is vacuously `False`.
--
-- ## Design choice — refactor_outOfEnd
--
-- *Mirror of `refactor_intoEnd`.*  Same recursion shape (decision 3,
--   direct `refactor_Walk` recursion replacing `getLast?`), same
--   bottoming-out pattern `.cons _ _ (.nil _ _)` and recursion case
--   `.cons _ _ (p@(.cons _ _ _))`, same unified-Prop choice
--   (decision 2), same trivial-walk-`False` convention.  See
--   `refactor_intoEnd`'s design block above for the full
--   justification of the recursion structure, the no-`refactor_edges`
--   rationale (which forced the `getLast?` replacement), the
--   `IsColliderRest` template the bottoming-out pattern mirrors,
--   *and the cost paid by direct recursion vs a hypothetical
--   `refactor_lastStep` helper* (the "peel-cons-until-nil"
--   recursion is shared structurally between this predicate and
--   `refactor_intoEnd` above; the duplication is shallow and self-
--   contained, and was preferred over a sigma-typed `last`-helper
--   that would need its own correctness lemma).  The only semantic
--   difference is that `refactor_outOfEnd` encodes the LN's `\hut`
--   at v_n (E-only, tail at v_n) instead of `\suh` (any-tail with
--   arrowhead at v_n).
--
-- *Why `.bidir → False` — bidirected last edge is NOT "out of v_n".*
--   The LN's symbolic pattern for "out of v_n" is `a_{n-1} = v_{n-1}
--   \hut v_n` — strictly `\hut` (tail at v_n, E-only).  The
--   bidirected macro `\huh` does NOT match `\hut`: `\huh` places an
--   arrowhead at v_n, where `\hut` requires a tail.  Equivalently,
--   the LN's "out of" relation (def_3_3 item~iii) excludes L-edges
--   entirely.  So `.bidir → False` here mirrors `refactor_outOfStart`'s
--   `.bidir → False` branch — a bidirected last edge produces
--   `refactor_intoEnd p ∧ ¬ refactor_outOfEnd p`, the same non-
--   partition shape on the right end of the walk.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: outOfEnd (was: refactor_outOfEnd)
-- def_3_4 -- start statement
def refactor_outOfEnd : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _) => False
  | _, _, .cons _ (.backwardE _) (.nil _ _) => True
  | _, _, .cons _ (.bidir _) (.nil _ _) => False
  | _, _, .cons _ _ (p@(.cons _ _ _)) => p.refactor_outOfEnd
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: outOfEnd

-- ref: def_3_4 (item~ii, directed walk) — refactor
--
-- `refactor_Walk.refactor_IsDirectedWalk p` iff every WalkStep of `p`
-- is a `.forwardE _` (the LN's clause~ii in
-- `tex/def_3_4_Walks.tex`: "$a_k = (v_k, v_{k+1}) \in E$ for every
-- $k \in \{0, 1, \dots, n - 1\}$").  Reads the cons-cell's typed
-- WalkStep directly: `.forwardE _` (the forward-E WalkStep encoding
-- `(u, v) ∈ G.E`) advances the recursion on the tail; `.backwardE _`
-- (backward-E, `(v, u) ∈ G.E`) is rejected because the LN constraint
-- pins the *forward* writing only; `.bidir _` (bidirected, L-channel)
-- is rejected because L-channel edges are not E-channel.  The trivial
-- walk satisfies vacuously (`tex/def_3_4_Walks.tex` clause~ii final
-- sentence: "The trivial walk … is admitted as a directed walk from
-- $v$ to itself").
--
-- ## Design choice — refactor_IsDirectedWalk
--
-- *Why the refactor needs to touch this predicate.*  The original
--   `IsDirectedWalk` (`Walks.lean` `IsDirectedWalk` ORIGINAL block)
--   used a stored-pair conjunction `a = (u, v) ∧ a ∈ G.E ∧
--   p.IsDirectedWalk` at every cons-cell — the ordered-pair `a : Node
--   × Node` field of the original `Walk.cons` was the channel and
--   direction carrier.  Under the typed `refactor_WalkStep` refactor
--   (Phase A), the channel and direction are baked into the WalkStep's
--   constructor tag, so the original's `a = (u, v) ∧ ...` disjunction
--   collapses to a single constructor case-match: "this step is
--   `.forwardE _`".  No stored pair to consult, no `a = (u, v)`
--   equality to verify — the type-level encoding does the work.
--
-- *Encoding map LN → constructor.*  Clause~ii's "$a_k = (v_k,
--   v_{k+1}) \in E$" maps directly to `.forwardE _`: the forward-E
--   WalkStep encodes exactly this constraint (its `h : (u, v) ∈ G.E`
--   constructor argument *is* the LN's membership witness, with
--   endpoints baked into the WalkStep's type indices `u v`).  The
--   other two constructor tags are LN-rejected: `.backwardE` encodes
--   the *reverse* writing `(v, u) ∈ G.E`, which the directed-walk
--   clause explicitly excludes (clause~ii pins the *forward* writing,
--   not the WalkStep disjunction's two-way union); `.bidir` encodes
--   an L-channel edge `s(u, v) ∈ G.L`, also excluded.
--
-- *Why a four-way pattern match (one nil + three constructor cases),
--   not `cons _ s p => (∃ h, s = .forwardE h) ∧ p.refactor_IsDirectedWalk`.*
--   An existential encoding is logically equivalent but introduces an
--   ∃ quantifier that every downstream proof would have to eliminate
--   at every use site (`obtain ⟨_, rfl⟩ := ...`).  Direct
--   constructor case-splitting keeps the definitional unfolding flat:
--   `simp` on `refactor_IsDirectedWalk` against a walk with known
--   constructor patterns reduces in one step, no existential to
--   discharge.  This mirrors the Phase C precedent
--   (`refactor_intoStart`, `refactor_outOfStart`, … above) of
--   case-splitting on the WalkStep constructor directly.
--
-- *Why the trivial walk is `True`.*  Unchanged from the original
--   (`Walks.lean` `IsDirectedWalk` ORIGINAL design block).  LN
--   clause~ii's "the trivial walk … is admitted as a directed walk"
--   is load-bearing: an `nil → False` reading would force every
--   downstream consumer that needs "the trivial walk is directed"
--   (e.g.\ `def_3_6` acyclicity's "no non-trivial directed walk
--   $v \to v$" formulation, which counts on the trivial walk
--   `Walk G v v` being directed by default) to carry a special-case
--   hypothesis.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsDirectedWalk (was: refactor_IsDirectedWalk)
-- def_3_4 -- start statement
def refactor_IsDirectedWalk : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) p => p.refactor_IsDirectedWalk
  | _, _, .cons _ (.backwardE _) _ => False
  | _, _, .cons _ (.bidir _) _ => False
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsDirectedWalk

-- ref: def_3_4 (item~iii, bidirected walk) — refactor
--
-- `refactor_Walk.refactor_IsBidirectedWalk p` iff every WalkStep of
-- `p` is a `.bidir _` (the LN's clause~iii in
-- `tex/def_3_4_Walks.tex`: "$a_k = (v_k, v_{k+1}) \in L$ for every
-- $k \in \{0, 1, \dots, n - 1\}$").  Reads the cons-cell's typed
-- WalkStep directly: `.bidir _` (the bidirected WalkStep encoding
-- `s(u, v) ∈ G.L`) advances the recursion on the tail; both
-- `.forwardE _` and `.backwardE _` (the two E-channel WalkStep tags)
-- are rejected because E-channel edges are not L-channel.  The
-- trivial walk satisfies vacuously
-- (`tex/def_3_4_Walks.tex` clause~iii final sentence).
--
-- ## Design choice — refactor_IsBidirectedWalk
--
-- *Mirror of `refactor_IsDirectedWalk`.*  Same shape: nil branch
--   `True` (LN admits the trivial walk as bidirected), one
--   constructor case advances the recursion (`.bidir _` here vs
--   `.forwardE _` above), the other two reject.  See
--   `refactor_IsDirectedWalk`'s design block above for the full
--   justification of the constructor-case-split shape (over
--   `∃ h, s = .bidir h`) and the trivial-walk-vacuous-`True` choice.
--
-- *Encoding map LN → constructor.*  Clause~iii's "$a_k = (v_k,
--   v_{k+1}) \in L$" maps directly to `.bidir _`: the bidirected
--   WalkStep's `h : s(u, v) ∈ G.L` constructor argument *is* the
--   LN's membership witness, with the unordered-pair carrier matching
--   the refactored `G.L : Finset (Sym2 Node)`.  The two E-channel
--   tags (`.forwardE`, `.backwardE`) are LN-rejected — they encode
--   directed-E edges, not bidirected ones.  Note that under the
--   typed refactor there is no `.forwardL` / `.backwardL` distinction
--   (the `Sym2` quotient makes those byte-identical to `.bidir`); so
--   the LN's parenthetical "equivalently, by the symmetry of $L$ …
--   $(v_{k+1}, v_k) \in L$ for every such $k$" is automatic — the
--   bidirected channel is direction-symmetric by construction.
--
-- *Trivial walk `True`.*  Same vacuity reading as the original
--   (`Walks.lean` `IsBidirectedWalk` ORIGINAL design block).  LN
--   clause~iii's final sentence explicitly admits the trivial walk
--   as bidirected; an `nil → False` reading would impose the same
--   special-case burden flagged in `refactor_IsDirectedWalk`'s
--   design block.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBidirectedWalk (was: refactor_IsBidirectedWalk)
-- def_3_4 -- start statement
def refactor_IsBidirectedWalk : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) _ => False
  | _, _, .cons _ (.backwardE _) _ => False
  | _, _, .cons _ (.bidir _) p => p.refactor_IsBidirectedWalk
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsBidirectedWalk

-- ref: def_3_4 (helper, collider-walk "interior+last" tail) — refactor
--
-- `refactor_Walk.refactor_IsColliderRest p` carries the trailing
-- constraint of an $n \ge 2$ collider walk after its first edge has
-- been consumed.  Concretely:
-- * if the tail has length 1 (i.e.\ the outer cons is the LN's
--   $a_{n-1}$ last edge): the WalkStep places an arrowhead at the
--   *current* start vertex (= LN $v_{n-1}$ at this recursion depth),
--   so `.backwardE _` (encoding `(v, u) ∈ G.E`, arrowhead at the
--   current start `u`) and `.bidir _` (encoding `s(u, v) ∈ G.L`,
--   arrowhead at both endpoints) are admitted, but `.forwardE _`
--   (encoding `(u, v) ∈ G.E`, no arrowhead at `u`) is rejected;
-- * if the tail has length $\ge 2$ (a true interior edge $a_k$ with
--   $1 \le k \le n - 2$): the WalkStep must be `.bidir _` (LN
--   clause~iv(b): every interior edge is bidirected), and the deeper
--   tail recursively satisfies the same predicate.
-- The `nil` branch is `True` for totality; it is not reached from the
-- only call sites (the $n \ge 2$ branches of `refactor_IsColliderWalk`,
-- where the first edge has already been consumed, so the original
-- walk had length $\ge 2$ and the tail has length $\ge 1$ — never
-- `nil`).
--
-- ## Design choice — refactor_IsColliderRest
--
-- *Why the refactor needs to touch this helper.*  The original
--   `IsColliderRest` (`Walks.lean` `IsColliderRest` ORIGINAL block)
--   used a stored-pair *disjunction* at the last-edge branch
--   `(a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)` and a stored-pair
--   conjunction at the interior branch `a = (u, v) ∧ a ∈ G.L ∧
--   p.IsColliderRest`.  Both phrasings read the channel and direction
--   off the cons-cell's stored ordered pair `a : Node × Node`.  Under
--   the typed `refactor_WalkStep` refactor (Phase A), the stored pair
--   is dissolved into the WalkStep's typed structure, so both
--   disjunction and conjunction collapse into constructor case-splits
--   that read the channel and direction directly from the WalkStep's
--   tag — no `a = ...` equality to verify, no `Or.inl`/`Or.inr` to
--   case-split through.
--
-- *Encoding map LN → constructor at the last edge.*  The original's
--   `(a = (v, u) ∧ a ∈ G.E)` disjunct (the LN's "$a_{n-1} = (v_n,
--   v_{n-1}) \in E$", arrowhead at the current start `u = v_{n-1}`
--   in local naming) maps to `.backwardE _` — the backward-E WalkStep
--   from `u` to `v` encodes the underlying edge `(v, u) ∈ G.E`.  The
--   original's `(a = (u, v) ∧ a ∈ G.L)` disjunct (the LN's "$a_{n-1}
--   = (v_{n-1}, v_n) \in L$", bidirected) maps to `.bidir _` — the
--   bidirected WalkStep from `u` to `v` encodes `s(u, v) ∈ G.L`.
--   `.forwardE _` (forward-E, `(u, v) ∈ G.E`) places no arrowhead at
--   `u = v_{n-1}` and is therefore rejected.  This matches
--   `tex/def_3_4_Walks.tex` clause~iv(c) exactly.
--
-- *Encoding map LN → constructor at interior edges.*  The original's
--   `a = (u, v) ∧ a ∈ G.L` conjunction (LN clause~iv(b): "every
--   interior edge $a_k = (v_k, v_{k+1}) \in L$ for $k \in \{1, …,
--   n-2\}$") maps to `.bidir _`.  Both directed cases (`.forwardE`,
--   `.backwardE`) are LN-rejected at interior edges — an interior
--   node $v_k$ ($1 \le k \le n - 1$) must have arrowheads from BOTH
--   incident walk-edges $a_{k-1}$ and $a_k$, and only the bidirected
--   channel places arrowheads at both endpoints simultaneously
--   (`tex/def_3_4_Walks.tex` clause~iv item-text after (a)–(c)).
--
-- *Why a seven-branch pattern match.*  Three constructor tags for the
--   outer WalkStep × two cases for the tail (`.nil` vs `.cons …`)
--   gives six covered cases; the seventh branch is the `nil` for the
--   *outer* walk (the `refactor_Walk G u v` argument).  Lean's
--   exhaustiveness checker requires all six (constructor, tail) pairs
--   to be covered explicitly under the case-split-on-constructor
--   convention; lumping them into fewer branches via wildcards
--   (`.cons _ _ (.nil _ _) => …`) was rejected because it would
--   silently admit the rejected last-edge `.forwardE` case (the
--   wildcard would match any WalkStep, including the rejected one).
--   The seven-branch shape is the natural manifest of the
--   constructor-by-constructor LN-rejection rules.
--
-- *Why the `nil` branch is `True` (unreachable from the only call
--   sites).*  Same rationale as the original (`Walks.lean`
--   `IsColliderRest` ORIGINAL design block).  Lean's structural
--   recursion needs *some* answer for the `nil` constructor.
--   `refactor_IsColliderRest` is called only from the $n \ge 2$
--   branches of `refactor_IsColliderWalk` below (where the outer
--   walk had at least two edges, so the tail handed to
--   `refactor_IsColliderRest` has length $\ge 1$ — never `nil`).
--   Setting the `nil` branch to `True` makes the predicate vacuous
--   on this unreachable case.
--
-- *Why a separate auxiliary recursive predicate, not an inline
--   constraint inside `refactor_IsColliderWalk`.*  Unchanged
--   rationale from the original: the LN's clause~iv (the $n \ge 2$
--   case) has a *positional* structure (first edge / interior /
--   last) that would be clumsy to express in a single recursion on
--   the outer walk.  Factoring the "interior + last" half into
--   `refactor_IsColliderRest` and letting `refactor_IsColliderWalk`
--   handle only the first edge keeps each predicate's recursion
--   shape simple.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsColliderRest (was: refactor_IsColliderRest)
-- def_3_4 --- start helper
def refactor_IsColliderRest : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) (.nil _ _) => False
  | _, _, .cons _ (.backwardE _) (.nil _ _) => True
  | _, _, .cons _ (.bidir _) (.nil _ _) => True
  | _, _, .cons _ (.forwardE _) (.cons _ _ _) => False
  | _, _, .cons _ (.backwardE _) (.cons _ _ _) => False
  | _, _, .cons _ (.bidir _) (p@(.cons _ _ _)) => p.refactor_IsColliderRest
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: IsColliderRest

-- ref: def_3_4 (item~iv, collider walk) — refactor
--
-- `refactor_Walk.refactor_IsColliderWalk p` encodes the case-
-- distinguished spec of `tex/def_3_4_Walks.tex` clause~iv:
-- * Case $n = 0$ (trivial walk): no constraint — `True`.
-- * Case $n = 1$ (single edge): the lone WalkStep is *bidirected*
--   (`.bidir _`).  Purely directed edges (`.forwardE _`, `.backwardE _`)
--   are **rejected** — this is the
--   `[collider_walk_n1_form_contradicts_inline_note]` addition_to_
--   the_LN clause, load-bearing here (the relaxed inline reading
--   "$v \sus w \in G$" is OVERRIDDEN).
-- * Case $n \ge 2$: the first WalkStep places an arrowhead at $v_1$
--   (`.forwardE _` or `.bidir _` — both put an arrowhead at the head
--   vertex `v`; `.backwardE _` puts the arrowhead at the tail vertex
--   `u = v_0` and is rejected), and the rest of the walk satisfies
--   `refactor_IsColliderRest` (interior edges bidirected + last
--   edge places an arrowhead at $v_{n-1}$).
--
-- ## Design choice — refactor_IsColliderWalk
--
-- *Why the refactor needs to touch this predicate.*  The original
--   `IsColliderWalk` (`Walks.lean` `IsColliderWalk` ORIGINAL block)
--   used a stored-pair conjunction at the $n = 1$ branch
--   (`a = (u, v) ∧ a ∈ G.L`) and a stored-pair disjunction at the
--   $n \ge 2$ first-edge branch (`a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)`).
--   Under the typed `refactor_WalkStep` refactor, both phrasings
--   collapse to constructor case-splits.
--
-- *$n = 1$ branch: only `.bidir _` admitted.*  Load-bearing addition
--   `[collider_walk_n1_form_contradicts_inline_note]` (the second
--   addition_to_the_LN clause in the row task — see
--   `tex/def_3_4_Walks.tex` lines 80–81 "Reconciliation with the
--   source block's $n = 1$ inline note").  The LN's source block has
--   the inline remark "Note that for $n = 1$ this reads:
--   $v \sus w \in G$" — i.e.\ *any* adjacency.  The rewritten tex
--   OVERRIDES this remark: for $n = 1$, the lone edge is required to
--   be bidirected, $a_0 = (v_0, v_1) \in L$.  Purely directed edges
--   `(v, w) \in E` (`.forwardE _`) or `(w, v) \in E` (`.backwardE _`)
--   are *not* admitted as collider walks of length 1 under this
--   stricter resolution.  The refactor preserves this exactly: the
--   $n = 1$ case-split admits only `.bidir _`, rejecting both
--   directed-E constructor tags.  Without the strict $n = 1$ branch,
--   downstream proofs relying on "every length-1 collider walk
--   admits a bidirected edge between the endpoints" would break on
--   misclassified directed-E edges.
--
-- *$n \ge 2$ branch: first step `.forwardE _ \/ .bidir _`, then
--   `refactor_IsColliderRest`.*  LN clause~iv(a) ("the first edge
--   places an arrowhead at $v_1$") covers `(a_0 = (v_0, v_1) \in E)`
--   — i.e.\ `.forwardE _` in the refactor — OR `(a_0 = (v_0, v_1)
--   \in L)` — i.e.\ `.bidir _`.  The third constructor tag
--   `.backwardE _` would encode `(v_1, v_0) \in E`, placing the
--   arrowhead at $v_0$ (the tail vertex), not at $v_1$ — LN-rejected.
--   The trailing constraint on the rest of the walk is delegated to
--   `refactor_IsColliderRest`, which enforces interior-edge-
--   bidirected + last-edge-arrowhead-at-$v_{n-1}$.
--
-- *Why a seven-branch pattern match (nil + three $n = 1$ + three
--   $n \ge 2$).*  The three-case LN structure ($n = 0$, $n = 1$,
--   $n \ge 2$) maps onto the cons-tail-shape pattern: `nil` outer
--   walk is $n = 0$; `cons _ s (.nil _ _)` is $n = 1$ (lone edge);
--   `cons _ s (.cons …)` is $n \ge 2$ (at least one more edge).
--   For the $n = 1$ and $n \ge 2$ cases, the constructor case-split
--   on `s` (three tags) gives three branches each — six total, plus
--   the one `nil` for $n = 0$.  Lumping branches via `_` wildcards
--   was rejected (same rationale as `refactor_IsColliderRest`): the
--   wildcard would silently admit the rejected constructor tags
--   (`.backwardE` at $n = 1$, etc.).
--
-- *Why a three-way case-distinguished `def`, mirroring the LN
--   rewrite's structure exactly.*  Unchanged from the original
--   (`Walks.lean` `IsColliderWalk` ORIGINAL design block).  The
--   rewritten tex case-distinguishes on $n$ because the LN's
--   symbolic pattern collapses in two degenerate small-$n$ regimes
--   ($n = 1$ is the bidirected-edge case per the addition; $n = 0$
--   is vacuous).  Encoding the same three cases as Lean pattern
--   branches makes definitional unfolding match the rewrite's
--   structure.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsColliderWalk (was: refactor_IsColliderWalk)
-- def_3_4 -- start statement
def refactor_IsColliderWalk : ∀ {u v : Node}, refactor_Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) (.nil _ _) => False
  | _, _, .cons _ (.backwardE _) (.nil _ _) => False
  | _, _, .cons _ (.bidir _) (.nil _ _) => True
  | _, _, .cons _ (.forwardE _) (p@(.cons _ _ _)) => p.refactor_IsColliderRest
  | _, _, .cons _ (.backwardE _) (.cons _ _ _) => False
  | _, _, .cons _ (.bidir _) (p@(.cons _ _ _)) => p.refactor_IsColliderRest
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsColliderWalk

-- ref: def_3_4 (item~v, path) — refactor
--
-- `refactor_Walk.refactor_IsPath p` iff the vertex sequence
-- `[v_0, v_1, …, v_n]` is duplicate-free.  Body identical to the
-- original `Walk.IsPath` (`Walks.lean` `IsPath` ORIGINAL block)
-- modulo the `refactor_vertices` retarget — the LN-level semantics
-- (clause~v of `tex/def_3_4_Walks.tex`: "the vertex sequence
-- contains no repetitions, $v_i \ne v_j$ whenever $0 \le i < j \le
-- n$") and the `List.Nodup` encoding are unchanged.  The trivial
-- walk's singleton vertex list `[v]` is vacuously `Nodup`, so the
-- trivial walk is a path (matching `tex/def_3_4_Walks.tex` clause~v
-- "The trivial walk $n = 0$ is vacuously a path").
--
-- ## Design choice — refactor_IsPath
--
-- *Why the refactor needs to touch this predicate.*  Only one
--   surface change: `p.vertices.Nodup` retargets to
--   `p.refactor_vertices.Nodup`.  The typed `refactor_WalkStep`
--   refactor doesn't affect the vertex extraction (the cons-cell's
--   middle vertex `v` and the tail's vertices form the vertex list
--   the same way under both encodings), so the LN-level Nodup
--   constraint is byte-identical.  This is the simplest of the five
--   Phase D predicates — a one-line retarget, no constructor case-
--   splits required.
--
-- *Why a one-liner over `refactor_vertices`, not a structural
--   recursion on `refactor_Walk` directly.*  Unchanged rationale
--   from the original (`Walks.lean` `IsPath` ORIGINAL design block).
--   `refactor_vertices` already extracts the LN's vertex tuple as
--   `List Node`; combining with `List.Nodup` from mathlib makes
--   `refactor_IsPath` a one-liner and inherits every mathlib `Nodup`
--   lemma (decidability, sub-list monotonicity, …) for free.  A
--   structural recursion `refactor_IsPath (cons v _ p) = v ∉
--   p.refactor_vertices ∧ p.refactor_IsPath` would be equivalent
--   but duplicate `List.Nodup`'s body in the walk-specific namespace.
--
-- *Trivial walk vacuously a path (`refactor_vertices = [v]` is
--   `Nodup`).*  Same as the original — `List.nodup_singleton` makes
--   it `rfl`-true.  No special case in `refactor_IsPath` is needed.
--
-- *Why the LN's index-based pairwise-distinctness form is not used
--   directly.*  Index-based pairwise-distinctness would force every
--   consumer to reason about `List.get?`-indexing and `Fin
--   (n+1)`-arithmetic.  `List.Nodup` is the standard index-free
--   encoding, equivalent (`List.nodup_iff_get?_ne_get?` in mathlib)
--   and the consensus mathlib idiom.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsPath (was: refactor_IsPath)
-- def_3_4 -- start statement
def refactor_IsPath {u v : Node} (p : refactor_Walk G u v) : Prop := p.refactor_vertices.Nodup
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsPath

-- ref: def_3_4 (helper, bifurcation "left arm + hinge + right arm") — refactor
--
-- `refactor_Walk.refactor_IsBifurcationWithSplit p k` says: `p` is a
-- bifurcation walk in which the left arm has exactly `k` reverse-
-- directed edges (so the hinge edge is at edge position `k`,
-- corresponding to the LN's split index `k = k + 1`).  The original
-- (`Walks.lean` `IsBifurcationWithSplit` ORIGINAL block) encoded each
-- branch's per-edge constraint as a stored-pair equality + channel-
-- membership disjunction (`a = (v, u) ∧ a ∈ G.E ∨ a = (u, v) ∧ a ∈ G.L`);
-- under the typed `refactor_WalkStep` (Phase A), these disjunctions
-- collapse to constructor-pattern case-splits per workspace decision (4)'s
-- hinge mapping.
--
-- ## Design choice — refactor_IsBifurcationWithSplit
--
-- *Why the refactor needs to touch this helper.*  The original carried
--   the per-step channel + direction information in a stored ordered
--   pair `a : Node × Node` plus `Prop`-level membership predicates.
--   Under the typed-WalkStep refactor, the cons-cell no longer stores
--   `a` — the channel comes from the WalkStep constructor tag and the
--   endpoints come from the type indices.  Every original branch that
--   read `a = (…, …) ∧ a ∈ G.E` (or `G.L`) translates to a constructor
--   case-split on the WalkStep.
--
-- *Encoding map LN → constructor per workspace decision (4).*
--   - LN "directed hinge $v_{k-1} \hut v_k$" (i.e. $(v_k, v_{k-1}) \in
--     E$, the edge running from $v_k$ backward to $v_{k-1}$) → the
--     refactored hinge step from `u = v_{k-1}` to the middle vertex
--     `v = v_k` is `.backwardE _` with `h : (v, u) ∈ G.E`.
--   - LN "bidirected hinge $v_{k-1} \huh v_k$" (i.e. $s(v_{k-1}, v_k)
--     \in L$) → `.bidir _` with `h : s(u, v) ∈ G.L`.
--   - LN left-arm step "$a_j = (v_{j+1}, v_j) \in E$" (the LN's
--     `\hut`, edge pointing backward toward $v_0$) → at the recursive
--     `cons _ s p, k + 1` branch the step is `.backwardE _`; the
--     forward and bidir tags are LN-rejected (clause~vi(b) of the LN
--     rewrite pins the *backward*-E writing only for left-arm edges).
--   - LN right-arm "$p.IsDirectedWalk$" constraint → recurse via
--     `refactor_IsDirectedWalk`, which requires every right-arm step
--     to be `.forwardE _` (the LN's `\tuh`, edge pointing forward
--     toward $v_n$).
--
-- *Why the $n = 1, k = 0$ branch (`cons _ s (.nil _ _), 0`) admits
--   only `.bidir _`.*  Per addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`
--   (load-bearing).  At $n = k = 1$ the right arm is empty (the LN's
--   right subwalk degenerates to the trivial walk on $v_n$), so the
--   hinge edge is also the last edge.  Per the addition, both
--   endnodes $v_0$ and $v_n$ must have exactly one arrowhead pointing
--   towards them.  For the directed hinge `.backwardE _` (encoding
--   $(v, u) \in E$, i.e. $v_n \to v_0$), the arrowhead is at $v_0$
--   only — $v_n$ has *no* arrowhead, violating the addition.  Only
--   `.bidir _` (arrowhead at both endpoints) survives.  `.forwardE _`
--   is rejected because forward-E at the hinge would encode $v_0 \to
--   v_n$ — a directed walk of length 1, not a bifurcation.  This
--   matches the original's `nil`-tail branch `a = (u, v) ∧ a ∈ G.L`
--   pinning the bidirected-only resolution, encoded constructor-side.
--
-- *Why the $n \ge 2, k = 0$ branch (`cons _ s (.cons _ _ _), 0`)
--   admits both `.backwardE _` and `.bidir _`.*  When the right arm is
--   non-trivial, the right-arm's first `.forwardE _` step (forced by
--   `refactor_IsDirectedWalk`) gives $v_n$ an inbound arrowhead, so
--   the addition's "$v_n$ has exactly one arrowhead" constraint is
--   automatically satisfied at $v_n$ by the right arm.  At the hinge,
--   either `.backwardE _` (directed) or `.bidir _` (bidirected) is
--   admissible — both place an arrowhead at $v_{k-1} = u$ (the LN's
--   `\hus` reading).  `.forwardE _` is rejected because forward-E
--   would put the hinge's arrowhead at $v_k$, not $v_{k-1}$ —
--   contradicting clause~vi(d)'s "$a_{k-1} \hus v_k$" requires the
--   arrowhead at $v_{k-1}$.  The trailing `p.refactor_IsDirectedWalk`
--   pins the right arm as a directed walk per clause~vi(c).
--
-- *Why the $k + 1$ branches (`cons _ s p, k + 1`) admit only
--   `.backwardE _`.*  LN clause~vi(b): every left-arm step is
--   $a_j = (v_{j+1}, v_j) \in E$, i.e. an `E`-edge running backward
--   (from $v_{j+1}$ toward $v_j$).  At the recursive cons-cell, the
--   step from `u` to the middle vertex `v` encodes an underlying edge
--   $(v, u) \in G.E$ (running from $v$ back to $u$) iff the WalkStep
--   tag is `.backwardE _`.  `.forwardE _` would put the arrowhead
--   *forward* (away from $v_0$, contradicting the LN's "all left-arm
--   arrowheads point toward $v_0$" reading); `.bidir _` would
--   introduce a bidirected edge in the left arm, also LN-rejected
--   (clause~vi(b) pins E-channel only).  The recursion descends on
--   the tail with `k` decremented, matching the original's
--   `a = (v, u) ∧ a ∈ G.E ∧ p.IsBifurcationWithSplit k` structure.
--
-- *Why a ten-branch pattern match.*  Three cons-step constructor tags
--   × two tail shapes (`.nil` / `.cons`) × two k-shapes (`0` / `k+1`)
--   would naively give twelve branches, but at the $k+1$ recursion
--   layer the tail-shape distinction collapses (the tail recursion
--   `p.refactor_IsBifurcationWithSplit k` handles both nil and cons
--   tails uniformly — the tail being `nil` yields `False` via the
--   nil-branch of the recursion, which is exactly the original's
--   behaviour at $k > n$ degenerations).  So the ten branches are:
--   one `nil` outer-walk + three constructor-tagged length-1-tail
--   branches at $k = 0$ + three constructor-tagged length-≥2-tail
--   branches at $k = 0$ + three constructor-tagged $k + 1$ branches.
--   Lumping branches via `_` wildcards on the step constructor was
--   rejected (same rationale as `refactor_IsColliderRest`'s seven-
--   branch design): the wildcard would silently admit LN-rejected
--   constructor tags and break the load-bearing addition.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBifurcationWithSplit (was: refactor_IsBifurcationWithSplit)
-- def_3_4 --- start helper
def refactor_IsBifurcationWithSplit : ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.bidir _) (.nil _ _), 0 => True
  | _, _, .cons _ (.forwardE _) (.cons _ _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.refactor_IsDirectedWalk
  | _, _, .cons _ (.bidir _) (p@(.cons _ _ _)), 0 => p.refactor_IsDirectedWalk
  | _, _, .cons _ (.forwardE _) _, _ + 1 => False
  | _, _, .cons _ (.backwardE _) p, k + 1 => p.refactor_IsBifurcationWithSplit k
  | _, _, .cons _ (.bidir _) _, _ + 1 => False
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: IsBifurcationWithSplit

-- ref: def_3_4 (item~vi, bifurcation) — refactor
--
-- `refactor_Walk.refactor_IsBifurcation p` iff `p` is a bifurcation
-- between its end-nodes `u` and `v`.  Body identical to the original
-- `Walk.IsBifurcation` (`Walks.lean` `IsBifurcation` ORIGINAL block)
-- modulo two surface retargets: `p.vertices` → `p.refactor_vertices`,
-- and the existential `∃ i, p.IsBifurcationWithSplit i` →
-- `∃ i, p.refactor_IsBifurcationWithSplit i`.  The four-conjunct
-- decomposition (LN's "$v \ne w$" + "$v_0 \notin \{v_1, \dots, v_n\}$"
-- + "$v_n \notin \{v_0, \dots, v_{n-1}\}$" + existence of a split
-- index) is unchanged — only the helper-level encoding shifts to the
-- typed-WalkStep refactor through the existential.
--
-- ## Design choice — refactor_IsBifurcation
--
-- *Why the refactor needs to touch this predicate.*  Two of the four
--   conjuncts reach into refactor-affected helpers: `refactor_vertices`
--   (Phase B) is the typed-WalkStep refactor of the vertex extractor,
--   and `refactor_IsBifurcationWithSplit` (the previous REPLACEMENT
--   block above) is the typed-WalkStep refactor of the split-index
--   helper.  The other two conjuncts (`u ≠ v` and the
--   `tail`/`dropLast`-based non-membership clauses) are at the
--   list-shape layer and are byte-identical to the original modulo
--   the `refactor_vertices` retarget.  No constructor case-splits
--   appear here — the WalkStep refactor's surface effects are
--   delegated entirely to the helper.
--
-- *Why retain the four-conjunct shape verbatim.*  The original's
--   design-comment block (`Walks.lean` `IsBifurcation` ORIGINAL block)
--   justified each conjunct against the LN's clause~vi reading:
--   `u ≠ v` for "$v \ne w$"; `u ∉ vertices.tail` /
--   `v ∉ vertices.dropLast` for "both end-nodes occur exactly once"
--   (weaker than `Nodup` because interior vertices may repeat); the
--   existential for clauses (b)-(d) plus the (e) addition.  None of
--   these readings change under the refactor — the LN-level semantics
--   are untouched, only the helper-level encoding shifts.  Mirrors
--   how `refactor_IsPath` is a one-line retarget of the original
--   `IsPath`.
--
-- *Why no per-conjunct design-comment block restating each clause.*
--   The original's design-comment block above
--   `IsBifurcation` already records the per-conjunct rationale; the
--   refactor inherits that rationale wholesale because the conjuncts
--   are byte-identical (modulo the helper retargets).  Duplicating
--   the prose here would be churn — the Phase 7 cleanup script's
--   whole-word rename leaves the original's design-comment block
--   wrapping the renamed `IsBifurcation` in the final tree, and this
--   refactor-section block is removed alongside the `refactor_*`
--   prefix.
--
-- *Where the addition `[bifurcation_right_chain_trivial_is_just_
--   directed_walk]` is enforced.*  The addition's two requirements —
--   "both endnodes have exactly one arrowhead pointing toward them"
--   and the explicit exclusion of the degenerate $n = k = 1$ case
--   with a directed hinge — are NOT enforced at this four-conjunct
--   level.  They are enforced inside the existential conjunct
--   `∃ i, p.refactor_IsBifurcationWithSplit i`, specifically by the
--   helper's $n = 1, k = 0$ branch (which admits ONLY `.bidir _` for
--   the hinge, rejecting both `.forwardE _` and `.backwardE _`) —
--   see the helper's design block above for the constructor-by-
--   constructor cross-walking of the addition's text into Lean's
--   pattern-match cases.  Phrasing the enforcement at the helper
--   level (and not duplicating it here) keeps `refactor_IsBifurcation`
--   itself as a thin four-conjunct list; the load-bearing addition
--   text appears in exactly one place.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBifurcation (was: refactor_IsBifurcation)
-- def_3_4 -- start statement
def refactor_IsBifurcation {u v : Node} (p : refactor_Walk G u v) : Prop :=
  u ≠ v ∧
  u ∉ p.refactor_vertices.tail ∧
  v ∉ p.refactor_vertices.dropLast ∧
  ∃ i, p.refactor_IsBifurcationWithSplit i
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsBifurcation

-- ref: def_3_4 (helper, bifurcation with directed hinge) — refactor
--
-- `refactor_Walk.refactor_IsBifurcationDirectedHingeWithSplit p k` is
-- the variant of `refactor_IsBifurcationWithSplit` restricted to a
-- *directed* hinge (clause~vi(d)'s first alternative
-- $a_{k-1} = (v_k, v_{k-1}) \in E$, encoded as `.backwardE _` per
-- decision (4)).  The precondition for the LN's "source $v_k$" to be
-- defined.  Per addition
-- `[bifurcation_right_chain_trivial_is_just_directed_walk]`, the
-- $n = 1, k = 0$ branch with directed hinge collapses to a directed
-- walk where $v_n$ has no arrowhead — explicitly excluded — so this
-- branch is `False` here.
--
-- ## Design choice — refactor_IsBifurcationDirectedHingeWithSplit
--
-- *Why the refactor needs to touch this helper.*  Same as
--   `refactor_IsBifurcationWithSplit` above: the original encoded the
--   directed-hinge constraint as a stored-pair conjunction
--   `a = (v, u) ∧ a ∈ G.E ∧ …`; under the typed-WalkStep refactor
--   this collapses to a constructor-pattern pin on `.backwardE _`.
--   The hinge-constraint specialisation (directed-only, no bidir
--   alternative) is the *defining* difference from
--   `refactor_IsBifurcationWithSplit`.
--
-- *Encoding map LN → constructor — directed-hinge specialisation.*
--   Same as `refactor_IsBifurcationWithSplit`'s decision (4) mapping
--   except: at $k = 0$ with non-trivial right arm, only `.backwardE _`
--   is admissible (not `.bidir _`); at $k = 0$ with trivial right arm
--   (`.nil _ _`), all three step constructors are `False` (the
--   addition rules out the directed-hinge case at $n = 1$ via the
--   "$v_n$ has no arrowhead" constraint, and `.bidir _` is excluded
--   because this helper is the *directed*-hinge specialisation).
--
-- *Why the $n = 1, k = 0$ branch is uniformly `False`.*  Per addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`: at
--   $n = k = 1$ with a directed hinge, the arrowhead is at $v_0$,
--   NOT at $v_n = v_1$ — so $v_n$ has no inbound arrowhead, violating
--   the addition's "both endnodes have exactly one arrowhead pointing
--   towards them" constraint.  So the directed-hinge variant rejects
--   ALL length-1 walks (regardless of constructor tag).  The original
--   encoded this as `cons _ _ _ (.nil _ _), 0 => False` for all three
--   step writings; the refactor enumerates the three constructor cases
--   explicitly (`.forwardE`, `.backwardE`, `.bidir`, all `False`) for
--   exhaustiveness without wildcards.
--
-- *Why the $n \ge 2, k = 0$ branch admits only `.backwardE _`.*  This
--   is the *defining* hinge restriction of the directed-hinge variant:
--   clause~vi(d)'s first alternative
--   $a_{k-1} = (v_k, v_{k-1}) \in E$ — encoded as `.backwardE _` per
--   decision (4).  The other two constructor tags are rejected:
--   `.forwardE _` would put the hinge in the wrong direction (forward,
--   not backward as the LN requires for the left-end of the hinge);
--   `.bidir _` is the bidirected-hinge alternative, *excluded* here
--   by construction (this helper is the directed-hinge variant).
--   The trailing `p.refactor_IsDirectedWalk` pins the right arm as a
--   directed walk per clause~vi(c).
--
-- *Why the $k + 1$ branches admit only `.backwardE _`.*  Same
--   rationale as `refactor_IsBifurcationWithSplit`'s $k + 1$ case
--   (LN clause~vi(b): every left-arm step is an `E`-edge running
--   backward).  No difference between the bifurcation and
--   directed-hinge bifurcation at left-arm steps — both inherit the
--   clause~vi(b) constraint.
--
-- *Why a ten-branch pattern match.*  Same structure as
--   `refactor_IsBifurcationWithSplit` above: one `nil` outer-walk +
--   three constructor-tagged length-1-tail branches at $k = 0$ +
--   three constructor-tagged length-≥2-tail branches at $k = 0$ +
--   three constructor-tagged $k + 1$ branches.  Lean's
--   exhaustiveness checker requires all (constructor, tail-shape, k-
--   shape) combinations to be covered explicitly; wildcards on the
--   step constructor were rejected (same rationale as
--   `refactor_IsBifurcationWithSplit`).
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBifurcationDirectedHingeWithSplit (was: refactor_IsBifurcationDirectedHingeWithSplit)
-- def_3_4 --- start helper
def refactor_IsBifurcationDirectedHingeWithSplit :
    ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.bidir _) (.nil _ _), 0 => False
  | _, _, .cons _ (.forwardE _) (.cons _ _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.refactor_IsDirectedWalk
  | _, _, .cons _ (.bidir _) (.cons _ _ _), 0 => False
  | _, _, .cons _ (.forwardE _) _, _ + 1 => False
  | _, _, .cons _ (.backwardE _) p, k + 1 =>
      p.refactor_IsBifurcationDirectedHingeWithSplit k
  | _, _, .cons _ (.bidir _) _, _ + 1 => False
-- def_3_4 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: IsBifurcationDirectedHingeWithSplit

-- ref: def_3_4 (item~vi, source of a bifurcation) — refactor
--
-- `refactor_Walk.refactor_IsBifurcationSource p x` iff `p` is a
-- bifurcation between `u` and `v` AND there is a split index `i` for
-- which the hinge is *directed* AND `x = v_{i + 1}` (LN's `v_k` for
-- `k = i + 1`).  Body identical to the original
-- `Walk.IsBifurcationSource` (`Walks.lean` `IsBifurcationSource`
-- ORIGINAL block) modulo three surface retargets: `p.vertices` →
-- `p.refactor_vertices` (twice), and
-- `p.IsBifurcationDirectedHingeWithSplit i` →
-- `p.refactor_IsBifurcationDirectedHingeWithSplit i`.  No constructor
-- case-splits appear here — the WalkStep refactor's surface effects
-- are delegated to the helpers.
--
-- ## Design choice — refactor_IsBifurcationSource
--
-- *Why the refactor needs to touch this predicate.*  Two reaching
--   dependencies: the `refactor_vertices` Phase B helper (used twice,
--   for the `tail`/`dropLast` non-membership clauses AND the
--   `[i + 1]?` indexed lookup of $v_k$) and the
--   `refactor_IsBifurcationDirectedHingeWithSplit` helper (the
--   previous REPLACEMENT block).  The four-conjunct shape and the
--   semantics (combining "directed-hinge bifurcation at index $i$"
--   with "$x$ is at vertex position $i + 1$") are unchanged.
--
-- *Why retain the four-conjunct shape verbatim.*  Same rationale as
--   `refactor_IsBifurcation`'s design block above.  The original's
--   per-conjunct design-comment block (`Walks.lean`
--   `IsBifurcationSource` ORIGINAL block) records: why a
--   `Prop`-predicate on `x` rather than an `Option Node` accessor;
--   why depending on `IsBifurcationDirectedHingeWithSplit` rather
--   than `IsBifurcationWithSplit` plus a directed-hinge filter; why
--   `vertices[i + 1]?` (`Option`-valued indexed lookup) rather than
--   `vertices.get ⟨i + 1, h⟩` (in-bounds proof); why the endnode-
--   uniqueness clauses are repeated here rather than delegating to
--   `IsBifurcation`.  None of these readings change under the
--   refactor — the LN-level semantics are untouched, only the
--   helper-level encoding shifts.
--
-- *Where the addition `[bifurcation_right_chain_trivial_is_just_
--   directed_walk]` is enforced.*  Same delegation pattern as
--   `refactor_IsBifurcation`: the addition's exclusion of the
--   degenerate $n = k = 1$ case is enforced INSIDE
--   `refactor_IsBifurcationDirectedHingeWithSplit`'s $n = 1, k = 0$
--   branches, which return `False` for ALL three constructor tags
--   (not just `.bidir _`, because this helper is the *directed-
--   hinge* specialisation and `.bidir _` is the bidirected-hinge
--   alternative, excluded here by construction).  So if `p` is a
--   length-1 walk, the existential `∃ i, p.refactor_
--   IsBifurcationDirectedHingeWithSplit i ∧ …` is `False` — no
--   length-1 walk has a "source" in the LN sense.  See the helper's
--   design block above for the constructor-by-constructor cross-
--   walking.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBifurcationSource (was: refactor_IsBifurcationSource)
-- def_3_4 -- start statement
def refactor_IsBifurcationSource {u v : Node} (p : refactor_Walk G u v)
    (x : Node) : Prop :=
  u ≠ v ∧
  u ∉ p.refactor_vertices.tail ∧
  v ∉ p.refactor_vertices.dropLast ∧
  ∃ i, p.refactor_IsBifurcationDirectedHingeWithSplit i ∧
       p.refactor_vertices[i + 1]? = some x
-- def_3_4 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsBifurcationSource

end refactor_Walk

end refactor_CDMG

end Causality
