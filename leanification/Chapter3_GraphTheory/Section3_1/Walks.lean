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

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same
--   chapter convention used by the original `CDMG` namespace above
--   and by every other `CDMG`-opening file in the chapter
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
-- `G.WalkStep u v` is the **typed** carrier of "a valid
-- walk-edge from `u` to `v` in `G`": a `Type`-level inductive whose
-- three constructors enumerate the three LN-admissible channel /
-- direction combinations a walk-edge can take.  Replaces the original
-- `WalkStep : Prop`-level two-disjunct from `Walks.lean:166-168`.
--
-- ```
-- inductive WalkStep (G : CDMG Node) : Node → Node → Type _ where
--   | forwardE  {u v : Node} (h : (u, v) ∈ G.E)   : WalkStep G u v
--   | backwardE {u v : Node} (h : (v, u) ∈ G.E)   : WalkStep G u v
--   | bidir     {u v : Node} (h : s(u, v) ∈ G.L)  : WalkStep G u v
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
--     Downstream walk-class predicates (`IsDirectedWalk`,
--     `IsBidirectedWalk`, `IsColliderRest`, the
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
--   `cons`-cell of `Walk` strictly leaner (the channel +
--   endpoints are *all* now part of the cons-cell's type indices,
--   not a runtime field).  See the design block above
--   `Walk` below for the downstream consequence.
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
--   `huh` in `CDMGNotation.lean:833` uses to express
--   `v_1 \huh v_2 \in G`.  The cross-reference to `EdgeRelations.lean`'s
--   `refactor_E` (still `Finset (Node × Node)`, retained verbatim) and
--   `refactor_L` (now `Finset (Sym2 Node)`) is exactly the asymmetry
--   that motivates the channel-split of the constructors above.
--
-- *Why implicit `{u v : Node}` on every constructor, not explicit.*
--   The walk-step constructors are consumed primarily by pattern
--   matches inside `Walk.cons` and the walk-class
--   predicates downstream, where the endpoints are *already*
--   determined by the surrounding `Walk` type indices (the cons-cell
--   types its WalkStep as `WalkStep G u v` with `u` and `v`
--   pinned by the outer match).  Making `u v` explicit would force
--   every construction site to spell them out (`.forwardE (u := …)
--   (v := …) h`), even when they could be inferred from the membership
--   witness's type.  Implicit is the right default.
--
-- *Why a single inductive type, not three separate inductives
--   (`ForwardEStep`, `BackwardEStep`, `BidirStep`).*  Splitting would
--   force `Walk.cons` to be a higher-rank constructor taking
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
--   `WalkStep` to `WalkStep` (whole-word) across every file
--   the refactor touches, leaving an inductive named `WalkStep` in the
--   final tree — which is exactly the LN's intended object.
-- def_3_4 -- start statement
inductive WalkStep (G : CDMG Node) : Node → Node → Type _ where
  | forwardE  {u v : Node} (h : (u, v) ∈ G.E) : WalkStep G u v
  | backwardE {u v : Node} (h : (v, u) ∈ G.E) : WalkStep G u v
  | bidir     {u v : Node} (h : s(u, v) ∈ G.L) : WalkStep G u v
-- def_3_4 -- end statement

-- ref: def_3_4 (item~i, Walk) — refactor
--
-- A *walk* from `u` to `v` in `G`, with the per-step constraint
-- carried by `WalkStep` instead of the original
-- `(a : Node × Node) + (h : G.WalkStep u a v)` ordered-pair-plus-Prop
-- pairing.  Inductive type with two constructors:
--
-- * `Walk.nil v hv` — the *trivial walk* `(v_0)` consisting
--   of a single node `v ∈ G`.  Identical to the original `Walk.nil`
--   modulo the `G` type retarget; `hv` remains as a stored membership
--   witness (see the design block below for why).
-- * `Walk.cons v s p` — prepend the alternating step
--   "$v_0, a_0, v_1$" in front of an existing walk `p` from `v_1` to
--   `w`.  The middle vertex `v_1` is the explicit `v` parameter (same
--   as the original); the LN-edge-constraint is now the *typed
--   WalkStep* `s : WalkStep G u v`.  No stored ordered pair
--   `a : Node × Node` — the channel and pair (where applicable) are
--   recovered from `s`'s constructor tag.
--
-- ```
-- inductive Walk (G : CDMG Node) : Node → Node → Type _ where
--   | nil  (v : Node) (hv : v ∈ G) : Walk G v v
--   | cons {u w : Node} (v : Node)
--       (s : WalkStep G u v) (p : Walk G v w)
--       : Walk G u w
-- ```
--
-- ## Design choice — `cons` no longer stores `a : Node × Node`
--
-- *Why drop the original `(a : Node × Node)` field on `cons`.*  Under
--   the typed `WalkStep`, the endpoints `u` and `v` of a
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
--   the (`a`, `h`) pair with a single `s : WalkStep G u v`
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
--   `E` or `L` edge — `CDMG.hE_subset` and `hL_subset`
--   recover its membership from the cons-cell's WalkStep without an
--   extra field on `cons`.  The asymmetry is the same as in the
--   original and is minimal: data is added exactly where it cannot
--   be inferred.  The `v ∈ G` notation here resolves via
--   `CDMGNotation.lean:587`'s `instMembership`
--   (`Membership Node (CDMG Node)`), so the `nil`
--   constructor's membership check unfolds to `v ∈ G.J ∪ G.V` as in
--   the LN.
--
-- *Why keep the explicit middle vertex `v` on `cons`, not switch to
--   the implicit `{u v w}` SimpleGraph.Walk-style convention.*  This
--   matches the original's choice at `Walks.lean:249`.  The seven
--   Walk-namespace predicates in Phases B-E (`length`,
--   `vertices`, `intoStart`, `outOfStart`,
--   `intoEnd`, `outOfEnd`, `IsDirectedWalk`,
--   `IsBidirectedWalk`, `IsColliderRest`,
--   `IsColliderWalk`, `IsPath`,
--   `IsBifurcationWithSplit`, `IsBifurcation`,
--   `IsBifurcationDirectedHingeWithSplit`,
--   `IsBifurcationSource`) all pattern-match on `.cons v s p`
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
-- *Why `inductive Type _`, not `List (WalkStep G u v) +
--   coherence`.*  Same rationale as the original (`Walks.lean:204-216`
--   design block).  Walks carry data that downstream chapters consume
--   by recursion; pattern-matching on `nil` vs `cons` reads exactly
--   like the LN's "$v_0, a_0, v_1, \dots$".  A `List`-plus-coherence
--   encoding would force every consumer to thread a coherence proof
--   one edge at a time.  The inductive shape factorises the LN's
--   alternating-sequence recursion structurally.
--
-- *Two-vertex index `Walk G u v`, endpoints in the type.*
--   Unchanged from the original; the LN's "*walk from $v$ to $w$*"
--   phrasing pins both endpoints into the type, and the trivial walk
--   has type `Walk G v v` enforcing the "$v = w$"
--   precondition at the type level.  No regression on this front.
--   The refactor keeps this discipline because it is *load-bearing*
--   for the typed `WalkStep`: the cons-cell's WalkStep
--   `s : WalkStep G u v` *requires* the outer walk's start
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
--   replacement inductive; Phase 7 cleanup renames `Walk`
--   to `Walk` globally across every refactored file, leaving an
--   inductive named `Walk` in the final tree.
-- def_3_4 -- start statement
inductive Walk (G : CDMG Node) : Node → Node → Type _ where
  | nil  (v : Node) (hv : v ∈ G) : Walk G v v
  | cons {u w : Node} (v : Node)
      (s : WalkStep G u v) (p : Walk G v w) : Walk G u w
-- def_3_4 -- end statement

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : CDMG Node}`.*  Every
--   declaration in this namespace recurses over a walk
--   `p : Walk G u v`.  Without the namespace-wide `variable`,
--   every signature would carry an explicit `{G : CDMG Node}`
--   binder.  Mirrors the original `namespace Walk` opening at
--   `Walks.lean:282-284` byte-for-byte modulo the `CDMG → CDMG`
--   type retarget — neither the implicit-vs-explicit convention nor
--   the marker shape needed adjustment in the refactor.  Downstream
--   consumers reach into `G` via dot-notation on the walk
--   (`p.length`, `p.vertices`), so the `{G}`
--   implicit-binder convention from the original carries over verbatim.
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the original (`Walks.lean` `namespace Walk` block) and
--   as the refactor section's section-wide `variable` at
--   `Walks.lean:1169-1171`: this `{G}` binder is load-bearing
--   infrastructure that the tex/Lean reconciliation tooling and the
--   Phase 7 cleanup script must recognise as helper-flavour.
-- def_3_4 --- start helper
variable {G : CDMG Node}
-- def_3_4 --- end helper

-- ref: def_3_4 / def_3_6 (helper, walk length) — refactor
--
-- `Walk.length p` is the number `n` of edges in `p` (matches
-- the LN's `n`).  Body identical to the original `Walk.length`
-- (`Walks.lean` `def length` ORIGINAL block) modulo the `cons`-cell
-- pattern change: the original `.cons _ _ _ p` skipped four
-- constructor arguments (`v`, `a`, `h`, `p`); the refactored
-- `.cons _ _ p` skips three (`v`, `s`, `p`), reflecting the new
-- constructor signature of `Walk.cons` documented in the
-- design block at `Walks.lean:1462-1469`.
--
-- ## Design choice — length
--
-- *Why the refactor needs to touch this helper.*  `length` is a pure
--   structural recursion on the `Walk` constructors.  Phase A changed
--   the `cons`-cell signature — dropped the stored `(a : Node × Node)`
--   and re-typed the per-step witness from `WalkStep`-Prop to the
--   typed inductive `WalkStep`.  So every recursion on
--   `Walk` that previously matched `.cons _ _ _ p` (four
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
-- *Recursion via `p.length`, not a sigma-typed helper or
--   auxiliary length counter.*  The recursive call `p.length`
--   resolves through dot-notation on `p : Walk G v w` (the
--   `cons` constructor's third argument).  The dot-notation lookup
--   finds `Walk.length` in this namespace, exactly
--   as the original `p.length` finds `Walk.length`.  Lean 4's
--   structural-recursion checker accepts the recursion directly on
--   `Walk` — no `termination_by` annotation, no
--   sigma-typed intermediary, no auxiliary walk-length helper.
-- def_3_6 --- start helper
def length : ∀ {u v : Node}, Walk G u v → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ p => p.length + 1
-- def_3_6 --- end helper

-- ref: def_3_4 (helper, vertex sequence) — refactor
--
-- `Walk.vertices p` is the list `[v_0, v_1, …, v_n]` from
-- LN item~i, i.e.\ the ordered sequence of vertices traversed by `p`.
-- Body identical to the original `Walk.vertices` (`Walks.lean`
-- `def vertices` ORIGINAL block) modulo the `cons`-cell pattern
-- change: `.cons _ _ _ p` becomes `.cons _ _ p`, matching the new
-- constructor signature of `Walk.cons` documented at
-- `Walks.lean:1462-1469`.
--
-- ## Design choice — vertices
--
-- *Why the refactor needs to touch this helper.*  Same cons-cell
--   signature change as `length` above: the original
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
--   `Fin`-arithmetic plumbing on every consumer of `IsPath`
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
-- ## Why no `edges`
--
-- *The original `Walk.edges` is dropped entirely under the refactor;
--   no `edges` REPLACEMENT counterpart exists.*  The original
--   `Walk.edges : Walk G u v → List (Node × Node)` (the wrapped
--   ORIGINAL block above) projected the stored ordered pair
--   `a : Node × Node` out of each `cons`-cell.  Under the typed
--   `WalkStep` refactor, the `cons`-cell no longer stores
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
-- *Why not a sigma-typed `List (Σ u v, WalkStep G u v)`
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
--   Phase C to recurse on `Walk` directly: peel cons-cells
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
--   an edge list, build one locally over `vertices` zipped
--   with WalkStep constructor projections.  The find_dependents scan
--   logged at refactor init flagged the in-file consumers
--   (`intoEnd`, `outOfEnd`) handled by Phase C; cross-file consumers
--   are addressed by their own refactor rows.
-- def_3_4 --- start helper
def vertices : ∀ {u v : Node}, Walk G u v → List Node
  | _, _, .nil v _ => [v]
  | u, _, .cons _ _ p => u :: p.vertices
-- def_3_4 --- end helper

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

-- ref: def_3_4 (item~i, end-node classifier "into v_0") — refactor
--
-- `Walk.intoStart p` iff `p` is non-trivial AND its
-- first WalkStep places an arrowhead at v_0 (the LN's `\hus` at the
-- start node).  Reads the cons-cell's typed WalkStep directly: a
-- `.forwardE` first-step is "out of v_0" (LN `\tuh`), NOT into v_0 →
-- `False`; a `.backwardE` first-step encodes `(v_1, v_0) ∈ E`,
-- placing an arrowhead at v_0 → `True`; a `.bidir` first-step encodes
-- `s(v_0, v_1) ∈ L`, also placing an arrowhead at v_0 → `True`.  The
-- trivial walk is vacuously `False`.
--
-- ## Design choice — intoStart
--
-- *Why the refactor needs to touch this classifier.*  Same `cons`-cell
--   shape change that drove `length` / `vertices`
--   above.  The original `intoStart` (`Walks.lean` `intoStart`
--   ORIGINAL block) read the LN's "$a_0 = \dots$" disjunction off the
--   stored `(a : Node × Node)` field via `G.into u a`.  Under the
--   typed `WalkStep` (Phase A), the channel and the arrowhead
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
--   upstream `intoE` / `intoL` split.  The upstream
--   `intoE` / `intoL` split was forced because L's *carrier type*
--   changed from `Node × Node` to `Sym2 Node` — a single ordered-pair
--   argument could no longer typecheck for both channels.  No such
--   pressure exists at walk-step level: the typed `WalkStep`
--   already absorbs all three channel cases into one inductive, so a
--   unified Prop on `Walk` consumes a single WalkStep through
--   a uniform constructor case-analysis.  A channel-split here
--   (`refactor_intoStartE` / `refactor_intoStartL`) would double the
--   predicate count without semantic gain and would break the LN's
--   channel-neutral "into v_0" phrasing.  Decision (2) carries to
--   `outOfStart`, `intoEnd`, and `outOfEnd`
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
--   on bidirected first edges: `intoStart p ∧
--   ¬ outOfStart p` — see `outOfStart` below for
--   the contrasting `.bidir → False` branch.
--
-- *Why the trivial walk is `False`.*  Same vacuity reading as the
--   original (`Walks.lean` `intoStart` ORIGINAL design block): on the
--   trivial walk no `a_0` exists, so the LN's existentially-loaded
--   "$a_0 = \dots$" clause is vacuously false.  An `nil → True`
--   reading would silently include trivial walks in BOTH the "into"
--   and "out of" categories, breaking downstream conditional checks
--   ("walk is into v_0 ⇒ walk has at least one edge").
-- def_3_4 -- start statement
def intoStart : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) _ => False
  | _, _, .cons _ (.backwardE _) _ => True
  | _, _, .cons _ (.bidir _) _ => True
-- def_3_4 -- end statement

-- ref: def_3_4 (item~i, end-node classifier "out of v_0") — refactor
--
-- `Walk.outOfStart p` iff `p` is non-trivial AND its
-- first WalkStep is a *forward*-E edge `(v_0, v_1) ∈ E` (the LN's
-- `\tuh` at v_0 — tail at v_0 with arrowhead at v_1).  Reads the
-- cons-cell's typed WalkStep directly: only `.forwardE` qualifies →
-- `True`; `.backwardE` puts an arrowhead at v_0 (no tail there) →
-- `False`; `.bidir` is `\huh`, with arrowheads at both endpoints →
-- `False` (LN's "out of" is E-only `\tuh`, NOT bidirected).  The
-- trivial walk is vacuously `False`.
--
-- ## Design choice — outOfStart
--
-- *Mirror of `intoStart`.*  Same rationale on all structural
--   points: the typed-WalkStep refactor dissolves the original's
--   stored `(a : Node × Node)` carrier (so `G.outOf u a` has no direct
--   counterpart), so the rewrite case-splits on the cons-cell's
--   WalkStep constructor; we keep a single unified Prop (decision 2)
--   rather than a per-channel split, since the typed WalkStep already
--   absorbs the channel distinction; trivial walk is vacuously
--   `False`.  See `intoStart`'s design block above for the
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
--   bidirected first edge produces `intoStart p ∧
--   ¬ outOfStart p`, the same non-partition shape flagged
--   by the LN-critic's `into_out_of_undefined_for_trivial_walk`
--   subtlety and recorded in the `intoStart` block above.
-- def_3_4 -- start statement
def outOfStart : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) _ => True
  | _, _, .cons _ (.backwardE _) _ => False
  | _, _, .cons _ (.bidir _) _ => False
-- def_3_4 -- end statement

-- ref: def_3_4 (item~i, end-node classifier "into v_n") — refactor
--
-- `Walk.intoEnd p` iff `p` is non-trivial AND its
-- *last* WalkStep places an arrowhead at v_n (the LN's `\suh` at the
-- end node).  Walks the cons chain via direct recursion until the
-- tail is `.nil _ _`, at which point the outer cons-cell's WalkStep
-- IS the last edge; case-splits on the constructor tag:
-- `.forwardE` encodes `(v_{n-1}, v_n) ∈ E` with arrowhead at v_n →
-- `True`; `.backwardE` encodes `(v_n, v_{n-1}) ∈ E` with tail at v_n
-- → `False`; `.bidir` encodes `s(v_{n-1}, v_n) ∈ L` with arrowhead
-- at v_n → `True`.  The trivial walk is vacuously `False`.
--
-- ## Design choice — intoEnd
--
-- *Decision (3) — direct `Walk` recursion, NO separate
--   `refactor_lastStep` helper.*  The original `intoEnd` reached the
--   last edge via `p.edges.getLast?`.  Under the refactor, `edges`
--   is dropped entirely — see the WHY-no-`edges` block above
--   the `vertices` REPLACEMENT for the full rationale; the
--   short version is that under the typed `WalkStep` the
--   original ordered-pair carrier is dissolved into the WalkStep's
--   typed structure and no canonical `(u, v)` representative is
--   recoverable from the `.bidir` case (Sym2 has no canonical
--   ordering), so `getLast?` has no direct counterpart.  Per workspace
--   decision (3), the natural replacement is direct recursion on
--   `Walk`: peel cons-cells until the tail is `nil`, then
--   read the WalkStep on the last `cons`.  A separate
--   `refactor_lastStep` sigma-typed helper (`Σ u', WalkStep
--   G u' v`) was considered and rejected — it forces a
--   wrap/unwrap pass and adds a net-new declaration with no
--   downstream re-use; inline recursion is simpler and keeps the
--   predicate self-contained.
--
-- *Cost the design pays.*  The "peel-cons-until-nil" recursion is
--   duplicated structurally in two predicates: this one
--   (`intoEnd`) and the mirror `outOfEnd` below.
--   Both share the same five-branch pattern (`nil`, three
--   constructor-tagged length-1-tail branches, one recursion case)
--   and differ only in the `True` / `False` assignments per
--   constructor tag.  The duplication was accepted (over factoring
--   the recursion through a hypothetical `Walk.last` /
--   `refactor_lastStep` helper) because (i) a helper that returns a
--   sigma-typed last step would need its own correctness lemma
--   ("`p.last = .cons _ s (.nil _ _) ↔ s = …`") and the two end-
--   classifier predicates would gain nothing simpler in exchange;
--   (ii) the duplicated recursion is shallow (one pattern per
--   constructor tag, no nested logic), so the maintenance burden is
--   bounded by the three-constructor count of `WalkStep`
--   and does not grow as new walk-class predicates are added; (iii)
--   keeping the two predicates self-contained makes the LN-
--   correspondence ("`intoEnd` encodes `\suh` at $v_n$";
--   "`outOfEnd` encodes `\hut` at $v_n$") readable in a
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
--   the template for `outOfEnd` below.
--
-- *Decision (2) reapplied — single unified Prop on the last
--   WalkStep.*  Same rationale as `intoStart`: the typed
--   `WalkStep` already absorbs the three channel cases, so
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
--   `intoStart` above: on the trivial walk no `a_{n-1}`
--   exists, so the LN's existentially-loaded clause is vacuously
--   false.
-- def_3_4 -- start statement
def intoEnd : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _) => True
  | _, _, .cons _ (.backwardE _) (.nil _ _) => False
  | _, _, .cons _ (.bidir _) (.nil _ _) => True
  | _, _, .cons _ _ (p@(.cons _ _ _)) => p.intoEnd
-- def_3_4 -- end statement

-- ref: def_3_4 (item~i, end-node classifier "out of v_n") — refactor
--
-- `Walk.outOfEnd p` iff `p` is non-trivial AND its
-- *last* WalkStep is a *backward*-E edge `(v_n, v_{n-1}) ∈ E` (the
-- LN's `\hut` at v_n — tail at v_n with arrowhead at v_{n-1}).  Same
-- direct-recursion access path as `intoEnd`: peel cons-cells
-- until the tail is `.nil _ _`, then case-split on the last cons-
-- cell's WalkStep: `.forwardE` puts an arrowhead at v_n → `False`;
-- `.backwardE` puts a tail at v_n → `True`; `.bidir` puts an arrowhead
-- at v_n → `False` (LN's "out of v_n" is E-only `\hut`, NOT
-- bidirected).  The trivial walk is vacuously `False`.
--
-- ## Design choice — outOfEnd
--
-- *Mirror of `intoEnd`.*  Same recursion shape (decision 3,
--   direct `Walk` recursion replacing `getLast?`), same
--   bottoming-out pattern `.cons _ _ (.nil _ _)` and recursion case
--   `.cons _ _ (p@(.cons _ _ _))`, same unified-Prop choice
--   (decision 2), same trivial-walk-`False` convention.  See
--   `intoEnd`'s design block above for the full
--   justification of the recursion structure, the no-`edges`
--   rationale (which forced the `getLast?` replacement), the
--   `IsColliderRest` template the bottoming-out pattern mirrors,
--   *and the cost paid by direct recursion vs a hypothetical
--   `refactor_lastStep` helper* (the "peel-cons-until-nil"
--   recursion is shared structurally between this predicate and
--   `intoEnd` above; the duplication is shallow and self-
--   contained, and was preferred over a sigma-typed `last`-helper
--   that would need its own correctness lemma).  The only semantic
--   difference is that `outOfEnd` encodes the LN's `\hut`
--   at v_n (E-only, tail at v_n) instead of `\suh` (any-tail with
--   arrowhead at v_n).
--
-- *Why `.bidir → False` — bidirected last edge is NOT "out of v_n".*
--   The LN's symbolic pattern for "out of v_n" is `a_{n-1} = v_{n-1}
--   \hut v_n` — strictly `\hut` (tail at v_n, E-only).  The
--   bidirected macro `\huh` does NOT match `\hut`: `\huh` places an
--   arrowhead at v_n, where `\hut` requires a tail.  Equivalently,
--   the LN's "out of" relation (def_3_3 item~iii) excludes L-edges
--   entirely.  So `.bidir → False` here mirrors `outOfStart`'s
--   `.bidir → False` branch — a bidirected last edge produces
--   `intoEnd p ∧ ¬ outOfEnd p`, the same non-
--   partition shape on the right end of the walk.
-- def_3_4 -- start statement
def outOfEnd : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _) => False
  | _, _, .cons _ (.backwardE _) (.nil _ _) => True
  | _, _, .cons _ (.bidir _) (.nil _ _) => False
  | _, _, .cons _ _ (p@(.cons _ _ _)) => p.outOfEnd
-- def_3_4 -- end statement

-- ref: def_3_4 (item~ii, directed walk) — refactor
--
-- `Walk.IsDirectedWalk p` iff every WalkStep of `p`
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
-- ## Design choice — IsDirectedWalk
--
-- *Why the refactor needs to touch this predicate.*  The original
--   `IsDirectedWalk` (`Walks.lean` `IsDirectedWalk` ORIGINAL block)
--   used a stored-pair conjunction `a = (u, v) ∧ a ∈ G.E ∧
--   p.IsDirectedWalk` at every cons-cell — the ordered-pair `a : Node
--   × Node` field of the original `Walk.cons` was the channel and
--   direction carrier.  Under the typed `WalkStep` refactor
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
--   not `cons _ s p => (∃ h, s = .forwardE h) ∧ p.IsDirectedWalk`.*
--   An existential encoding is logically equivalent but introduces an
--   ∃ quantifier that every downstream proof would have to eliminate
--   at every use site (`obtain ⟨_, rfl⟩ := ...`).  Direct
--   constructor case-splitting keeps the definitional unfolding flat:
--   `simp` on `IsDirectedWalk` against a walk with known
--   constructor patterns reduces in one step, no existential to
--   discharge.  This mirrors the Phase C precedent
--   (`intoStart`, `outOfStart`, … above) of
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
-- def_3_4 -- start statement
def IsDirectedWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) p => p.IsDirectedWalk
  | _, _, .cons _ (.backwardE _) _ => False
  | _, _, .cons _ (.bidir _) _ => False
-- def_3_4 -- end statement

-- ref: def_3_4 (item~iii, bidirected walk) — refactor
--
-- `Walk.IsBidirectedWalk p` iff every WalkStep of
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
-- ## Design choice — IsBidirectedWalk
--
-- *Mirror of `IsDirectedWalk`.*  Same shape: nil branch
--   `True` (LN admits the trivial walk as bidirected), one
--   constructor case advances the recursion (`.bidir _` here vs
--   `.forwardE _` above), the other two reject.  See
--   `IsDirectedWalk`'s design block above for the full
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
--   special-case burden flagged in `IsDirectedWalk`'s
--   design block.
-- def_3_4 -- start statement
def IsBidirectedWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) _ => False
  | _, _, .cons _ (.backwardE _) _ => False
  | _, _, .cons _ (.bidir _) p => p.IsBidirectedWalk
-- def_3_4 -- end statement

-- ref: def_3_4 (helper, collider-walk "interior+last" tail) — refactor
--
-- `Walk.IsColliderRest p` carries the trailing
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
-- only call sites (the $n \ge 2$ branches of `IsColliderWalk`,
-- where the first edge has already been consumed, so the original
-- walk had length $\ge 2$ and the tail has length $\ge 1$ — never
-- `nil`).
--
-- ## Design choice — IsColliderRest
--
-- *Why the refactor needs to touch this helper.*  The original
--   `IsColliderRest` (`Walks.lean` `IsColliderRest` ORIGINAL block)
--   used a stored-pair *disjunction* at the last-edge branch
--   `(a = (v, u) ∧ a ∈ G.E) ∨ (a = (u, v) ∧ a ∈ G.L)` and a stored-pair
--   conjunction at the interior branch `a = (u, v) ∧ a ∈ G.L ∧
--   p.IsColliderRest`.  Both phrasings read the channel and direction
--   off the cons-cell's stored ordered pair `a : Node × Node`.  Under
--   the typed `WalkStep` refactor (Phase A), the stored pair
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
--   *outer* walk (the `Walk G u v` argument).  Lean's
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
--   `IsColliderRest` is called only from the $n \ge 2$
--   branches of `IsColliderWalk` below (where the outer
--   walk had at least two edges, so the tail handed to
--   `IsColliderRest` has length $\ge 1$ — never `nil`).
--   Setting the `nil` branch to `True` makes the predicate vacuous
--   on this unreachable case.
--
-- *Why a separate auxiliary recursive predicate, not an inline
--   constraint inside `IsColliderWalk`.*  Unchanged
--   rationale from the original: the LN's clause~iv (the $n \ge 2$
--   case) has a *positional* structure (first edge / interior /
--   last) that would be clumsy to express in a single recursion on
--   the outer walk.  Factoring the "interior + last" half into
--   `IsColliderRest` and letting `IsColliderWalk`
--   handle only the first edge keeps each predicate's recursion
--   shape simple.
-- def_3_4 --- start helper
def IsColliderRest : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) (.nil _ _) => False
  | _, _, .cons _ (.backwardE _) (.nil _ _) => True
  | _, _, .cons _ (.bidir _) (.nil _ _) => True
  | _, _, .cons _ (.forwardE _) (.cons _ _ _) => False
  | _, _, .cons _ (.backwardE _) (.cons _ _ _) => False
  | _, _, .cons _ (.bidir _) (p@(.cons _ _ _)) => p.IsColliderRest
-- def_3_4 --- end helper

-- ref: def_3_4 (item~iv, collider walk) — refactor
--
-- `Walk.IsColliderWalk p` encodes the case-
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
--   `IsColliderRest` (interior edges bidirected + last
--   edge places an arrowhead at $v_{n-1}$).
--
-- ## Design choice — IsColliderWalk
--
-- *Why the refactor needs to touch this predicate.*  The original
--   `IsColliderWalk` (`Walks.lean` `IsColliderWalk` ORIGINAL block)
--   used a stored-pair conjunction at the $n = 1$ branch
--   (`a = (u, v) ∧ a ∈ G.L`) and a stored-pair disjunction at the
--   $n \ge 2$ first-edge branch (`a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)`).
--   Under the typed `WalkStep` refactor, both phrasings
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
--   `IsColliderRest`.*  LN clause~iv(a) ("the first edge
--   places an arrowhead at $v_1$") covers `(a_0 = (v_0, v_1) \in E)`
--   — i.e.\ `.forwardE _` in the refactor — OR `(a_0 = (v_0, v_1)
--   \in L)` — i.e.\ `.bidir _`.  The third constructor tag
--   `.backwardE _` would encode `(v_1, v_0) \in E`, placing the
--   arrowhead at $v_0$ (the tail vertex), not at $v_1$ — LN-rejected.
--   The trailing constraint on the rest of the walk is delegated to
--   `IsColliderRest`, which enforces interior-edge-
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
--   was rejected (same rationale as `IsColliderRest`): the
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
-- def_3_4 -- start statement
def IsColliderWalk : ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.forwardE _) (.nil _ _) => False
  | _, _, .cons _ (.backwardE _) (.nil _ _) => False
  | _, _, .cons _ (.bidir _) (.nil _ _) => True
  | _, _, .cons _ (.forwardE _) (p@(.cons _ _ _)) => p.IsColliderRest
  | _, _, .cons _ (.backwardE _) (.cons _ _ _) => False
  | _, _, .cons _ (.bidir _) (p@(.cons _ _ _)) => p.IsColliderRest
-- def_3_4 -- end statement

-- ref: def_3_4 (item~v, path) — refactor
--
-- `Walk.IsPath p` iff the vertex sequence
-- `[v_0, v_1, …, v_n]` is duplicate-free.  Body identical to the
-- original `Walk.IsPath` (`Walks.lean` `IsPath` ORIGINAL block)
-- modulo the `vertices` retarget — the LN-level semantics
-- (clause~v of `tex/def_3_4_Walks.tex`: "the vertex sequence
-- contains no repetitions, $v_i \ne v_j$ whenever $0 \le i < j \le
-- n$") and the `List.Nodup` encoding are unchanged.  The trivial
-- walk's singleton vertex list `[v]` is vacuously `Nodup`, so the
-- trivial walk is a path (matching `tex/def_3_4_Walks.tex` clause~v
-- "The trivial walk $n = 0$ is vacuously a path").
--
-- ## Design choice — IsPath
--
-- *Why the refactor needs to touch this predicate.*  Only one
--   surface change: `p.vertices.Nodup` retargets to
--   `p.vertices.Nodup`.  The typed `WalkStep`
--   refactor doesn't affect the vertex extraction (the cons-cell's
--   middle vertex `v` and the tail's vertices form the vertex list
--   the same way under both encodings), so the LN-level Nodup
--   constraint is byte-identical.  This is the simplest of the five
--   Phase D predicates — a one-line retarget, no constructor case-
--   splits required.
--
-- *Why a one-liner over `vertices`, not a structural
--   recursion on `Walk` directly.*  Unchanged rationale
--   from the original (`Walks.lean` `IsPath` ORIGINAL design block).
--   `vertices` already extracts the LN's vertex tuple as
--   `List Node`; combining with `List.Nodup` from mathlib makes
--   `IsPath` a one-liner and inherits every mathlib `Nodup`
--   lemma (decidability, sub-list monotonicity, …) for free.  A
--   structural recursion `IsPath (cons v _ p) = v ∉
--   p.vertices ∧ p.IsPath` would be equivalent
--   but duplicate `List.Nodup`'s body in the walk-specific namespace.
--
-- *Trivial walk vacuously a path (`vertices = [v]` is
--   `Nodup`).*  Same as the original — `List.nodup_singleton` makes
--   it `rfl`-true.  No special case in `IsPath` is needed.
--
-- *Why the LN's index-based pairwise-distinctness form is not used
--   directly.*  Index-based pairwise-distinctness would force every
--   consumer to reason about `List.get?`-indexing and `Fin
--   (n+1)`-arithmetic.  `List.Nodup` is the standard index-free
--   encoding, equivalent (`List.nodup_iff_get?_ne_get?` in mathlib)
--   and the consensus mathlib idiom.
-- def_3_4 -- start statement
def IsPath {u v : Node} (p : Walk G u v) : Prop := p.vertices.Nodup
-- def_3_4 -- end statement

-- ref: def_3_4 (helper, bifurcation "left arm + hinge + right arm") — refactor
--
-- `Walk.IsBifurcationWithSplit p k` says: `p` is a
-- bifurcation walk in which the left arm has exactly `k` reverse-
-- directed edges (so the hinge edge is at edge position `k`,
-- corresponding to the LN's split index `k = k + 1`).  The original
-- (`Walks.lean` `IsBifurcationWithSplit` ORIGINAL block) encoded each
-- branch's per-edge constraint as a stored-pair equality + channel-
-- membership disjunction (`a = (v, u) ∧ a ∈ G.E ∨ a = (u, v) ∧ a ∈ G.L`);
-- under the typed `WalkStep` (Phase A), these disjunctions
-- collapse to constructor-pattern case-splits per workspace decision (4)'s
-- hinge mapping.
--
-- ## Design choice — IsBifurcationWithSplit
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
--     `IsDirectedWalk`, which requires every right-arm step
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
--   `IsDirectedWalk`) gives $v_n$ an inbound arrowhead, so
--   the addition's "$v_n$ has exactly one arrowhead" constraint is
--   automatically satisfied at $v_n$ by the right arm.  At the hinge,
--   either `.backwardE _` (directed) or `.bidir _` (bidirected) is
--   admissible — both place an arrowhead at $v_{k-1} = u$ (the LN's
--   `\hus` reading).  `.forwardE _` is rejected because forward-E
--   would put the hinge's arrowhead at $v_k$, not $v_{k-1}$ —
--   contradicting clause~vi(d)'s "$a_{k-1} \hus v_k$" requires the
--   arrowhead at $v_{k-1}$.  The trailing `p.IsDirectedWalk`
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
--   `p.IsBifurcationWithSplit k` handles both nil and cons
--   tails uniformly — the tail being `nil` yields `False` via the
--   nil-branch of the recursion, which is exactly the original's
--   behaviour at $k > n$ degenerations).  So the ten branches are:
--   one `nil` outer-walk + three constructor-tagged length-1-tail
--   branches at $k = 0$ + three constructor-tagged length-≥2-tail
--   branches at $k = 0$ + three constructor-tagged $k + 1$ branches.
--   Lumping branches via `_` wildcards on the step constructor was
--   rejected (same rationale as `IsColliderRest`'s seven-
--   branch design): the wildcard would silently admit LN-rejected
--   constructor tags and break the load-bearing addition.
-- def_3_4 --- start helper
def IsBifurcationWithSplit : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.bidir _) (.nil _ _), 0 => True
  | _, _, .cons _ (.forwardE _) (.cons _ _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.IsDirectedWalk
  | _, _, .cons _ (.bidir _) (p@(.cons _ _ _)), 0 => p.IsDirectedWalk
  | _, _, .cons _ (.forwardE _) _, _ + 1 => False
  | _, _, .cons _ (.backwardE _) p, k + 1 => p.IsBifurcationWithSplit k
  | _, _, .cons _ (.bidir _) _, _ + 1 => False
-- def_3_4 --- end helper

-- ref: def_3_4 (item~vi, bifurcation) — refactor
--
-- `Walk.IsBifurcation p` iff `p` is a bifurcation
-- between its end-nodes `u` and `v`.  Body identical to the original
-- `Walk.IsBifurcation` (`Walks.lean` `IsBifurcation` ORIGINAL block)
-- modulo two surface retargets: `p.vertices` → `p.vertices`,
-- and the existential `∃ i, p.IsBifurcationWithSplit i` →
-- `∃ i, p.IsBifurcationWithSplit i`.  The four-conjunct
-- decomposition (LN's "$v \ne w$" + "$v_0 \notin \{v_1, \dots, v_n\}$"
-- + "$v_n \notin \{v_0, \dots, v_{n-1}\}$" + existence of a split
-- index) is unchanged — only the helper-level encoding shifts to the
-- typed-WalkStep refactor through the existential.
--
-- ## Design choice — IsBifurcation
--
-- *Why the refactor needs to touch this predicate.*  Two of the four
--   conjuncts reach into refactor-affected helpers: `vertices`
--   (Phase B) is the typed-WalkStep refactor of the vertex extractor,
--   and `IsBifurcationWithSplit` (the previous REPLACEMENT
--   block above) is the typed-WalkStep refactor of the split-index
--   helper.  The other two conjuncts (`u ≠ v` and the
--   `tail`/`dropLast`-based non-membership clauses) are at the
--   list-shape layer and are byte-identical to the original modulo
--   the `vertices` retarget.  No constructor case-splits
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
--   how `IsPath` is a one-line retarget of the original
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
--   `∃ i, p.IsBifurcationWithSplit i`, specifically by the
--   helper's $n = 1, k = 0$ branch (which admits ONLY `.bidir _` for
--   the hinge, rejecting both `.forwardE _` and `.backwardE _`) —
--   see the helper's design block above for the constructor-by-
--   constructor cross-walking of the addition's text into Lean's
--   pattern-match cases.  Phrasing the enforcement at the helper
--   level (and not duplicating it here) keeps `IsBifurcation`
--   itself as a thin four-conjunct list; the load-bearing addition
--   text appears in exactly one place.
-- def_3_4 -- start statement
def IsBifurcation {u v : Node} (p : Walk G u v) : Prop :=
  u ≠ v ∧
  u ∉ p.vertices.tail ∧
  v ∉ p.vertices.dropLast ∧
  ∃ i, p.IsBifurcationWithSplit i
-- def_3_4 -- end statement

-- ref: def_3_4 (helper, bifurcation with directed hinge) — refactor
--
-- `Walk.IsBifurcationDirectedHingeWithSplit p k` is
-- the variant of `IsBifurcationWithSplit` restricted to a
-- *directed* hinge (clause~vi(d)'s first alternative
-- $a_{k-1} = (v_k, v_{k-1}) \in E$, encoded as `.backwardE _` per
-- decision (4)).  The precondition for the LN's "source $v_k$" to be
-- defined.  Per addition
-- `[bifurcation_right_chain_trivial_is_just_directed_walk]`, the
-- $n = 1, k = 0$ branch with directed hinge collapses to a directed
-- walk where $v_n$ has no arrowhead — explicitly excluded — so this
-- branch is `False` here.
--
-- ## Design choice — IsBifurcationDirectedHingeWithSplit
--
-- *Why the refactor needs to touch this helper.*  Same as
--   `IsBifurcationWithSplit` above: the original encoded the
--   directed-hinge constraint as a stored-pair conjunction
--   `a = (v, u) ∧ a ∈ G.E ∧ …`; under the typed-WalkStep refactor
--   this collapses to a constructor-pattern pin on `.backwardE _`.
--   The hinge-constraint specialisation (directed-only, no bidir
--   alternative) is the *defining* difference from
--   `IsBifurcationWithSplit`.
--
-- *Encoding map LN → constructor — directed-hinge specialisation.*
--   Same as `IsBifurcationWithSplit`'s decision (4) mapping
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
--   The trailing `p.IsDirectedWalk` pins the right arm as a
--   directed walk per clause~vi(c).
--
-- *Why the $k + 1$ branches admit only `.backwardE _`.*  Same
--   rationale as `IsBifurcationWithSplit`'s $k + 1$ case
--   (LN clause~vi(b): every left-arm step is an `E`-edge running
--   backward).  No difference between the bifurcation and
--   directed-hinge bifurcation at left-arm steps — both inherit the
--   clause~vi(b) constraint.
--
-- *Why a ten-branch pattern match.*  Same structure as
--   `IsBifurcationWithSplit` above: one `nil` outer-walk +
--   three constructor-tagged length-1-tail branches at $k = 0$ +
--   three constructor-tagged length-≥2-tail branches at $k = 0$ +
--   three constructor-tagged $k + 1$ branches.  Lean's
--   exhaustiveness checker requires all (constructor, tail-shape, k-
--   shape) combinations to be covered explicitly; wildcards on the
--   step constructor were rejected (same rationale as
--   `IsBifurcationWithSplit`).
set_option linter.style.longLine false in
-- def_3_4 --- start helper
def IsBifurcationDirectedHingeWithSplit :
    ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ (.forwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (.nil _ _), 0 => False
  | _, _, .cons _ (.bidir _) (.nil _ _), 0 => False
  | _, _, .cons _ (.forwardE _) (.cons _ _ _), 0 => False
  | _, _, .cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.IsDirectedWalk
  | _, _, .cons _ (.bidir _) (.cons _ _ _), 0 => False
  | _, _, .cons _ (.forwardE _) _, _ + 1 => False
  | _, _, .cons _ (.backwardE _) p, k + 1 =>
      p.IsBifurcationDirectedHingeWithSplit k
  | _, _, .cons _ (.bidir _) _, _ + 1 => False
-- def_3_4 --- end helper

-- ref: def_3_4 (item~vi, source of a bifurcation) — refactor
--
-- `Walk.IsBifurcationSource p x` iff `p` is a
-- bifurcation between `u` and `v` AND there is a split index `i` for
-- which the hinge is *directed* AND `x = v_{i + 1}` (LN's `v_k` for
-- `k = i + 1`).  Body identical to the original
-- `Walk.IsBifurcationSource` (`Walks.lean` `IsBifurcationSource`
-- ORIGINAL block) modulo three surface retargets: `p.vertices` →
-- `p.vertices` (twice), and
-- `p.IsBifurcationDirectedHingeWithSplit i` →
-- `p.IsBifurcationDirectedHingeWithSplit i`.  No constructor
-- case-splits appear here — the WalkStep refactor's surface effects
-- are delegated to the helpers.
--
-- ## Design choice — IsBifurcationSource
--
-- *Why the refactor needs to touch this predicate.*  Two reaching
--   dependencies: the `vertices` Phase B helper (used twice,
--   for the `tail`/`dropLast` non-membership clauses AND the
--   `[i + 1]?` indexed lookup of $v_k$) and the
--   `IsBifurcationDirectedHingeWithSplit` helper (the
--   previous REPLACEMENT block).  The four-conjunct shape and the
--   semantics (combining "directed-hinge bifurcation at index $i$"
--   with "$x$ is at vertex position $i + 1$") are unchanged.
--
-- *Why retain the four-conjunct shape verbatim.*  Same rationale as
--   `IsBifurcation`'s design block above.  The original's
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
--   `IsBifurcation`: the addition's exclusion of the
--   degenerate $n = k = 1$ case is enforced INSIDE
--   `IsBifurcationDirectedHingeWithSplit`'s $n = 1, k = 0$
--   branches, which return `False` for ALL three constructor tags
--   (not just `.bidir _`, because this helper is the *directed-
--   hinge* specialisation and `.bidir _` is the bidirected-hinge
--   alternative, excluded here by construction).  So if `p` is a
--   length-1 walk, the existential `∃ i, p.refactor_
--   IsBifurcationDirectedHingeWithSplit i ∧ …` is `False` — no
--   length-1 walk has a "source" in the LN sense.  See the helper's
--   design block above for the constructor-by-constructor cross-
--   walking.
-- def_3_4 -- start statement
def IsBifurcationSource {u v : Node} (p : Walk G u v)
    (x : Node) : Prop :=
  u ≠ v ∧
  u ∉ p.vertices.tail ∧
  v ∉ p.vertices.dropLast ∧
  ∃ i, p.IsBifurcationDirectedHingeWithSplit i ∧
       p.vertices[i + 1]? = some x
-- def_3_4 -- end statement

end Walk

end CDMG

end Causality
