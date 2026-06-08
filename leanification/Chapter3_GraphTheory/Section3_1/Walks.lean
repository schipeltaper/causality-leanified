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
--   tooling.  Matches the wrapping used by
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
-- def_3_4 --- start helper
def WalkStep (G : CDMG Node) (u : Node) (a : Node × Node) (v : Node) : Prop :=
  (a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∨ (a = (v, u) ∧ a ∈ G.E)
-- def_3_4 --- end helper

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
-- def_3_4 -- start statement
inductive Walk (G : CDMG Node) : Node → Node → Type _ where
  | nil (v : Node) (hv : v ∈ G) : Walk G v v
  | cons {u w : Node} (v : Node) (a : Node × Node)
      (h : G.WalkStep u a v) (p : Walk G v w) : Walk G u w
-- def_3_4 -- end statement

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

/-- Length of a walk: the number `n` of edges (matches the LN's `n`). -/
def length : ∀ {u v : Node}, Walk G u v → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ _ p => p.length + 1

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
-- def_3_4 --- start helper
def vertices : ∀ {u v : Node}, Walk G u v → List Node
  | _, _, .nil v _ => [v]
  | u, _, .cons _ _ _ p => u :: p.vertices
-- def_3_4 --- end helper

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
-- def_3_4 --- start helper
def edges : ∀ {u v : Node}, Walk G u v → List (Node × Node)
  | _, _, .nil _ _ => []
  | _, _, .cons _ a _ p => a :: p.edges
-- def_3_4 --- end helper

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
-- def_3_4 -- start statement
def intoStart : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | u, _, .cons _ a _ _ => G.into u a
-- def_3_4 -- end statement

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
-- def_3_4 -- start statement
def outOfStart : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | u, _, .cons _ a _ _ => G.outOf u a
-- def_3_4 -- end statement

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
-- def_3_4 -- start statement
def intoEnd {u v : Node} (p : Walk G u v) : Prop :=
  match p.edges.getLast? with
  | none => False
  | some a => G.into v a
-- def_3_4 -- end statement

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
-- def_3_4 -- start statement
def outOfEnd {u v : Node} (p : Walk G u v) : Prop :=
  match p.edges.getLast? with
  | none => False
  | some a => G.outOf v a
-- def_3_4 -- end statement

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
-- def_3_4 -- start statement
def IsDirectedWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ p => a = (u, v) ∧ a ∈ G.E ∧ p.IsDirectedWalk
-- def_3_4 -- end statement

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
-- def_3_4 -- start statement
def IsBidirectedWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ p => a = (u, v) ∧ a ∈ G.L ∧ p.IsBidirectedWalk
-- def_3_4 -- end statement

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
-- def_3_4 --- start helper
def IsColliderRest : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ (.nil _ _) =>
      (a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)
  | u, _, .cons v a _ (p@(.cons _ _ _ _)) =>
      a = (u, v) ∧ a ∈ G.L ∧ p.IsColliderRest
-- def_3_4 --- end helper

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
-- def_3_4 -- start statement
def IsColliderWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | u, _, .cons v a _ (.nil _ _) => a = (u, v) ∧ a ∈ G.L
  | u, _, .cons v a _ (p@(.cons _ _ _ _)) =>
      (a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∧ p.IsColliderRest
-- def_3_4 -- end statement

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
-- def_3_4 -- start statement
def IsPath {u v : Node} (p : Walk G u v) : Prop := p.vertices.Nodup
-- def_3_4 -- end statement

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
-- def_3_4 --- start helper
def IsBifurcationWithSplit : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | u, _, .cons v a _ (.nil _ _), 0 => a = (u, v) ∧ a ∈ G.L
  | u, _, .cons v a _ (p@(.cons _ _ _ _)), 0 =>
      ((a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)) ∧ p.IsDirectedWalk
  | u, _, .cons v a _ p, k + 1 =>
      a = (v, u) ∧ a ∈ G.E ∧ p.IsBifurcationWithSplit k
-- def_3_4 --- end helper

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
-- def_3_4 -- start statement
def IsBifurcation {u v : Node} (p : Walk G u v) : Prop :=
  u ≠ v ∧
  u ∉ p.vertices.tail ∧
  v ∉ p.vertices.dropLast ∧
  ∃ i, p.IsBifurcationWithSplit i
-- def_3_4 -- end statement

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
-- def_3_4 --- start helper
def IsBifurcationDirectedHingeWithSplit : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ _ (.nil _ _), 0 => False
  | u, _, .cons v a _ (p@(.cons _ _ _ _)), 0 =>
      a = (v, u) ∧ a ∈ G.E ∧ p.IsDirectedWalk
  | u, _, .cons v a _ p, k + 1 =>
      a = (v, u) ∧ a ∈ G.E ∧ p.IsBifurcationDirectedHingeWithSplit k
-- def_3_4 --- end helper

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
-- def_3_4 -- start statement
def IsBifurcationSource {u v : Node} (p : Walk G u v) (x : Node) : Prop :=
  u ≠ v ∧
  u ∉ p.vertices.tail ∧
  v ∉ p.vertices.dropLast ∧
  ∃ i, p.IsBifurcationDirectedHingeWithSplit i ∧ p.vertices[i + 1]? = some x
-- def_3_4 -- end statement

end Walk

end CDMG

end Causality
