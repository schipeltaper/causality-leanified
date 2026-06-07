import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation

namespace Causality

/-!
# Predecessors of a vertex under a (topological) order (`def_3_9`)

This file formalises the LN definition block `def_3_9`
(`\label{def-predecessors}` in `graphs.tex`):

> Let `G = (J, V, E, L)` be a CDMG and `<` a total order of `J ∪ V`.
> The set of *predecessors* of `v` in `G` are:
>   `Pred^G_<(v) := {w ∈ G | w < v}`.
> We also put:
>   `Pred^G_≤(v) := {w ∈ G | w < v} ∪ {v}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_9_Predecessors.tex`,
which passed both `verify_tex_statement_only` (structural) and
`verify_tex_statement_equivalence` (semantic) against the LN block.
No `addition_to_the_LN` clauses are attached.  The rewrite folded
three working-phase wording-check subtleties directly into the
canonical tex as non-load-bearing clarifications:

* `ambiguous_w_in_G_notation` — the LN's "$w \in G$" is read as
  $w \in J \cup V$ via `def_3_2`'s `Membership Node (CDMG Node)`
  instance; the rewritten tex spells the set-builder body with
  $w \in J \cup V$ verbatim.
* `v_not_required_to_be_in_J_union_V` — the LN does *not* constrain
  $v$ to lie in $J \cup V$.  We follow the literal LN stance and take
  `v : Node` (unconstrained) below.  Corner case `v ∉ J ∪ V`: the
  strict body is empty (`<` is only supplied on `J ∪ V`), and the
  non-strict body degenerates to `{v}` (so `v ∈ Pred_≤ G lt v` even
  when `v` lies outside `J ∪ V`).  Downstream consumers that
  pattern-match on the shape of an element may add `v ∈ G` as a
  separate hypothesis at the point of use.
* `subscript_le_body_uses_strict` — the LN writes the non-strict
  variant's body as `{w | w < v} ∪ {v}` (strict comparison plus the
  singleton) rather than `{w | w ≤ v}`.  We implement the literal LN
  body `Pred lt v ∪ {v}`; the two forms coincide whenever
  `v ∈ J ∪ V` (irreflexivity of `<` keeps `v` out of the strict body
  while `w ≤ v` would pick it up via `v ≤ v`), and diverge only in
  the corner case above.

The strict order `<` is taken as a raw external argument
`lt : Node → Node → Prop`, matching the parameter convention of
`def_3_8`'s `IsTopologicalOrder` (`TopologicalOrder.lean`): the LN's
"Let `<` be a total order of `J ∪ V`" is realised by *passing* such
an `lt` to `Pred` / `PredLE`, not by carrying it on a `[LT Node]`
typeclass (which would force a single canonical `<` per `Node`
type — see the design block in `TopologicalOrder.lean` for the full
rejection of typeclass / structure encodings of "the order").
`Pred` / `PredLE` are *predecessor-set* primitives that *any* strict
relation may be plugged into; downstream consumers will typically
pass an `lt` carrying `G.IsTopologicalOrder lt`, but the
definitional shape does not require it.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim
--   from `def_3_1` (`CDMG.lean`).  Load-bearing for this row's
--   statement: the `Membership Node (CDMG Node)` instance from
--   `def_3_2` (`CDMGNotation.lean`) — driving the `w ∈ G` conjunct
--   of the set-builder body — reduces to `Finset.mem` on
--   `G.J ∪ G.V`, which needs `DecidableEq Node`.  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed and are
--   deferred to use sites that consume them.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention established in
--   `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
--   `EdgeRelations.lean`, `CDMGRestrictions.lean`,
--   `Acyclicity.lean`, `CDMGTypes.lean`, `TopologicalOrder.lean`.
--   The two-dash marker is reserved for declarations whose body is
--   the formalised LN content of the row.  This `variable` line is
--   statement-typing infrastructure — it binds the implicit
--   parameters that the `Pred` / `PredLE` defs below rely on, but is
--   not itself part of the LN definition.
-- def_3_9 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_9 --- end helper

-- ref: def_3_9 (strict predecessors)
--
-- The set of *strict* predecessors of `v` in `G` under the order
-- `lt`: nodes `w ∈ J ∪ V` (i.e.\ `w ∈ G` via `def_3_2`'s
-- `Membership` instance) with `lt w v`.  Mirrors the LN's
-- `Pred^G_<(v) := {w ∈ J ∪ V | w < v}`.
/-
LN tex (rewritten canonical statement for `def_3_9`, strict form):

  The set of *predecessors* of `v` in `G` is
    Pred^G_<(v) := {w ∈ J ∪ V | w < v}.
-/
-- ## Design choice
--
-- *`lt : Node → Node → Prop` as an explicit argument, mirroring
--   `def_3_8`.*  The LN reads "Let `<` be a total order of `J ∪ V`"
--   and then writes `Pred^G_<(v)` — the subscript `<` is the
--   parameter the predecessor set is computed against.  We expose
--   `lt` exactly the same way `IsTopologicalOrder` does: as an
--   explicit `Node → Node → Prop` argument, *not* a `[LT Node]`
--   typeclass or a structure field.  Same rationale as
--   `TopologicalOrder.lean`'s design block — locking `<` to the
--   type level would force a single canonical order per `Node`
--   type, and a structure-field encoding would conflate this row's
--   *predecessor-set computation* with downstream existence
--   statements about topological orders.  `Pred G lt v` reads on
--   the nose as the LN's "predecessors of `v` in `G` under `<`".
--
-- *`v : Node` unconstrained.*  Per the rewritten tex spec, the LN
--   does *not* impose `v ∈ J ∪ V`.  We follow the literal stance and
--   take `v : Node` raw.  When `v ∉ G` the body is vacuously empty
--   (the conjunct `lt w v` is never witnessed by the `<` we ever
--   actually plug in — typically a topological order whose domain
--   is `J ∪ V`), which is the natural reading.  Adding a
--   `(hv : v ∈ G)` hypothesis was considered and rejected: it would
--   force every downstream call site to supply the witness, even
--   sites that only ever pass `v` coming from `G.V` or `G.J ∪ G.V`
--   by construction — extra threading for no logical gain.
--
-- *`Set Node` return type.*  Matches the chapter's `def_3_5`
--   family-set convention (`Pa`, `Ch`, `Sib`, `Anc`, `Desc`, `Sc`,
--   `Dist` in `FamilyRelationships.lean` are all `Set Node`-valued).
--   Predecessor sets compose naturally with the family sets in
--   downstream chapters (CBN factorisation conditions on
--   `Pred^G_<(v) ∩ V`, do-calculus on `Pred^G_<(v) ∩ Pa^G(v)`); all
--   such intersections land inside Mathlib's `Set` API (`∩`, `⊆`,
--   `↥`-subtype coercion, measurable-family indexing) with no
--   `Finset.coe` round-trips.  Two alternative carriers were
--   considered and rejected: (a) `Finset Node` — needs decidability
--   of `lt w v` threaded through every call site, and the LN never
--   picks a decidable representative `<` anyway; (b) the subtype
--   `↥(G.J ∪ G.V) → Set ↥(G.J ∪ G.V)` (i.e.\ bundling the carrier
--   restriction into the type) — would force every downstream
--   consumer through a `Subtype.val` coercion to compare against
--   ambient `Set Node` quantities like `Pa^G(v)`, and would also
--   make `PredLE`'s adjoined `{v}` ill-typed in the literal LN
--   corner case `v ∉ J ∪ V`.  Keeping the membership clause inside
--   the set-builder body (rather than baking it into the carrier)
--   keeps everything in `Set Node` and matches the family-set
--   precedent.
--
-- *`w ∈ G` conjunct on the output side, mirroring the LN's literal
--   `{w ∈ J ∪ V | w < v}`.*  By the `Membership Node (CDMG Node)`
--   instance from `def_3_2` (`CDMGNotation.lean`), `w ∈ G`
--   transparently unfolds to `w ∈ G.J ∪ G.V` — so the LN shorthand
--   "$w \in G$" (subtlety `ambiguous_w_in_G_notation` in the wording
--   check) reads literally through the Lean syntax with no further
--   convention to smuggle in.  We could have written
--   `{w | lt w v}` and relied on the consumer to intersect with
--   `(G.J ∪ G.V : Set Node)` later, but the LN's body restricts to
--   `J ∪ V` *at the set-builder level*.  Keeping the `w ∈ G`
--   conjunct in the body (i) preserves the literal LN grep
--   correspondence and (ii) makes downstream destructuring of
--   `h : w ∈ Pred G lt v` as `⟨hw_mem, hw_lt⟩` deliver
--   `hw_mem : w ∈ G` immediately, with no separate intersection
--   step.  Matches the precedent set by `Pa`, `Ch`, `Sib` in
--   `FamilyRelationships.lean`.
--
-- *Downstream consumers.*  Chapter 4 CBN factorisation reads
--   "for each `v ∈ V`, condition on the values at
--   `Pred^G_<(v) ∩ V`"; do-calculus (chapter 5) uses
--   `Pred^G_<(v)` to identify the temporal-ordering context of an
--   intervention; σ-/d-separation (chapters 6–7) take a
--   topological order from `claim_3_2` and quantify over
--   predecessors; iSCMs (chapters 8–10) recursively compute
--   values at `v` from values at `Pred^G_<(v)`.
-- def_3_9 -- start statement
def Pred (G : CDMG Node) (lt : Node → Node → Prop) (v : Node) : Set Node :=
  {w | w ∈ G ∧ lt w v}
-- def_3_9 -- end statement

-- ref: def_3_9 (non-strict predecessors)
--
-- The set of *non-strict* predecessors of `v` in `G` under `lt`:
-- the strict predecessor set `G.Pred lt v` together with `v`
-- itself.  Mirrors the LN's literal
-- `Pred^G_≤(v) := {w ∈ J ∪ V | w < v} ∪ {v}` — the body is the
-- strict form plus a singleton, *not* `{w | w ≤ v}`.
/-
LN tex (rewritten canonical statement for `def_3_9`, non-strict form):

  We also put
    Pred^G_≤(v) := {w ∈ J ∪ V | w < v} ∪ {v}.
-/
-- ## Design choice
--
-- *Literal LN body `G.Pred lt v ∪ {v}`, NOT `{w | w ∈ G ∧
--   (lt w v ∨ w = v)}` or `{w | w ∈ G ∧ Relation.ReflGen lt w v}`.*
--   The LN subscript reads "$\le$" but the body the LN writes is
--   strict: `{w < v} ∪ {v}`, with `{v}` adjoined unconditionally.
--   We mirror the literal LN spelling, taking `Pred lt v ∪ {v}` as
--   the body.  This is *not* equivalent to `{w | lt w v ∨ w = v}`
--   in the corner case `v ∉ G`: the strict body filters by `w ∈ G`,
--   so `v` is admitted into `PredLE G lt v` *only* via the adjoined
--   singleton — and the singleton has no `v ∈ G` guard.  Hence
--   `v ∈ PredLE G lt v` *unconditionally*, even for `v ∉ G`.  This
--   is the literal LN reading (subtlety
--   `v_not_required_to_be_in_J_union_V` from the wording check) and
--   the rewritten tex spec spells it out explicitly.  Any
--   downstream consumer that needs the cleaner form `{w | w ≤ v}`
--   can prove a one-step equivalence under the hypothesis
--   `v ∈ G` (plus irreflexivity of `lt`).
--
-- *`G.Pred lt v ∪ {v}` spelled with the named `G.Pred`, NOT
--   unfolded to `{w | w ∈ G ∧ lt w v} ∪ {v}`.*  Two reasons:
--   (i) it reads on the nose as the LN's "the strict predecessor
--   set plus `v`" semantic story; (ii) downstream proofs that
--   already have `h : w ∈ G.Pred lt v` in scope can use `Or.inl h`
--   directly to obtain `w ∈ G.PredLE lt v`, without an
--   intermediate `Set.mem_setOf` unfolding step.  Mathlib's
--   `Set.mem_union` and `Set.mem_singleton_iff` are the natural
--   destructors for `w ∈ G.PredLE lt v`.
--
-- *`{v}` parses as the `Set Node` singleton via
--   `Set.instSingleton`.*  Lean's elaboration sees `∪` on a
--   `Set Node` left-hand side and resolves the singleton brace
--   notation to the matching `Set` instance.  No explicit
--   ascription `({v} : Set Node)` is needed.
--
-- *Downstream consumers.*  Every chapter that reasons modulo "the
--   nodes up to and including `v`" (CBN factorisation's
--   conditioning argument, do-calculus's "earlier-than" context,
--   iSCM recursion's "values determined by `Pred_≤`") uses
--   `PredLE`.  The split between `Pred` and `PredLE` is purely the
--   strict-vs-non-strict variant the LN explicitly introduces; we
--   formalise both because both names appear under that
--   distinction in later chapters.
-- def_3_9 -- start statement
def PredLE (G : CDMG Node) (lt : Node → Node → Prop) (v : Node) : Set Node :=
  G.Pred lt v ∪ {v}
-- def_3_9 -- end statement

end CDMG

end Causality
