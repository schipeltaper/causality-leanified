import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.TopologicalOrder

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

## Refactor `total_order_helper` (in progress)

The *original* `Pred` / `PredLE` — wrapped below in
`-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Pred` /
`-- REFACTOR-BLOCK-ORIGINAL-END: Pred` and
`-- REFACTOR-BLOCK-ORIGINAL-BEGIN: PredLE` /
`-- REFACTOR-BLOCK-ORIGINAL-END: PredLE` marker pairs — took a raw
`lt : Node → Node → Prop` argument with **no** total-order
hypothesis on the type contract.  The Lean was well-typed for *any*
binary relation `lt`, but the LN's `Pred^G_<(v)` is only well-defined
when `<` is a total order on `J ∪ V` (the LN block opens with "*Let
`<` be a total order of `J ∪ V`*").  This is exactly the failure
pattern `verify_equivalence` item~1a flags ("hypothesis dropped from
Lean's type contract; only documented in design comments") and
`verify_equivalence_strict`'s CONTENT example calls "loosening a
quantifier's domain": the LN's premise lived in the 60+ lines of
design-choice comments above each of the original `def Pred` /
`def PredLE` lines, where the type checker could not enforce it on
consumers.  `G.Pred lt v` and `G.Pred^G_<(v)` were not the same
mathematical object, even though they coincide on the LN's intended
inputs.

The *replacement* — wrapped below in matching `REFACTOR-BLOCK`
marker pairs for `Pred` and `PredLE` (see the actual markers around
the new defs further down the file) —
introduces an explicit `(h : G.refactor_IsTotalOrder lt)` hypothesis
sitting between `lt` and `v` on both signatures.  The hypothesis is
*not used* in either body (the bodies are textually identical to the
originals' — `{w | w ∈ G ∧ lt w v}` and `Pred lt v ∪ {v}`
respectively); it is there purely as a type-level enforcement of the
LN's "*Let `<` be a total order of `J ∪ V`*" premise.  Closing the
leak at the source forces every downstream consumer to supply the
total-order witness rather than smuggling the LN premise in at the
use site.  The helper name `refactor_IsTotalOrder` matches the one
exposed by `def_3_8`'s REPLACEMENT block (the refactor's first root,
see `TopologicalOrder.lean`); the helper is deliberately
`IsTotalOrder` and **not** the full `IsTopologicalOrder` — the
parent-precedence conjunct is not needed for predecessor sets to be
well-defined (e.g.\ chapter 5's ID-algorithm "preceding Markov
blanket" slice carves `J ∪ V` purely via total-order content,
without parent-precedence).

**Coexistence during the refactor.**  Both the original and the
replacement definitions live in this file as top-level declarations
of `Causality.CDMG` until Phase~7 cleanup.  The replacement
`refactor_PredLE` calls `G.refactor_Pred lt h v` (prefixed) so that
the file type-checks during the refactor — the cleanup script flips
every `refactor_Pred` / `refactor_PredLE` / `refactor_IsTotalOrder`
occurrence to the unprefixed form across all touched files, after
which the unprefixed `PredLE` will call the unprefixed `Pred`,
identical to the original wiring but with the threaded `h`.
Consumers that have not yet been re-validated keep calling the
original `G.Pred` / `G.PredLE` (no §3.1 row currently consumes
`Pred` / `PredLE` — the refactor's `claim_3_2` DEPENDENT row is
included for `def_3_8`'s shape change, not for `def_3_9`), so the
build stays green throughout.
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

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Pred
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
-- REFACTOR-BLOCK-ORIGINAL-END: Pred

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: PredLE
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
-- REFACTOR-BLOCK-ORIGINAL-END: PredLE

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Pred (was: refactor_Pred)
-- ref: def_3_9 (refactor: total_order_helper, strict predecessors)
--
-- `G.refactor_Pred lt h v` (post-refactor shape) is the set of
-- *strict* predecessors of `v` in `G` under the order `lt`: nodes
-- `w ∈ J ∪ V` (i.e.\ `w ∈ G` via `def_3_2`'s `Membership` instance)
-- with `lt w v`.  The body is *textually identical* to the original
-- (the `REFACTOR-BLOCK-ORIGINAL: Pred` block earlier in this file);
-- the only difference is the signature, which now takes an explicit
-- `(h : G.refactor_IsTotalOrder lt)` hypothesis sitting between `lt`
-- and `v`.  The hypothesis enforces the LN's "*Let `<` be a total
-- order of `J ∪ V`*" premise at the type level.
/-
LN tex (rewritten canonical statement for `def_3_9`, strict form):

  Pred^G_<(v) := {w ∈ J ∪ V | w < v}.
-/
-- ## Design choice
--
-- *Why add `(h : G.refactor_IsTotalOrder lt)` to the signature.*
--   Pre-refactor, `Pred G lt v` was well-typed for *any* binary
--   relation `lt`, but the LN's `Pred^G_<(v)` is only well-defined
--   when `<` is a total order on `J ∪ V` (the LN block opens
--   "*Let `<` be a total order of `J ∪ V`*").  This is exactly the
--   failure pattern `verify_equivalence` item~1a flags ("hypothesis
--   dropped from Lean's type contract; only documented in design
--   comments") and `verify_equivalence_strict`'s CONTENT example
--   calls "loosening a quantifier's domain": the original `Pred`'s
--   "let `<` be a total order" premise lived only in the 60+ lines
--   of design-choice comments above the `REFACTOR-BLOCK-ORIGINAL:
--   Pred` block, where the type checker cannot enforce it on
--   downstream consumers.  Adding `h` to the type contract closes
--   the leak at the source: every downstream consumer is now forced
--   to supply the total-order witness, rather than smuggling the LN
--   premise in at the use site or relying on documentation the type
--   system cannot inspect.  The pre-refactor `G.Pred lt v` and the
--   LN's `Pred^G_<(v)` were not the same mathematical object, even
--   though they coincide on the LN's intended inputs; the
--   post-refactor signature makes them coincide *by construction*.
--
-- *Why the helper is `refactor_IsTotalOrder` (not the full
--   `refactor_IsTopologicalOrder`).*  The LN's premise in this row
--   reads "*Let `<` be a total order of `J ∪ V`*" — nothing more.
--   The parent-precedence conjunct of `IsTopologicalOrder`
--   (`∀ v w, v ∈ G.Pa w → lt v w`) is *not* required for `Pred` to
--   be well-defined: the predecessor-set computation
--   `{w ∈ G | lt w v}` makes sense for any total order on `J ∪ V`,
--   topological or not.  Demanding the full `IsTopologicalOrder`
--   here would over-constrain consumers that legitimately want
--   predecessor sets for non-topological total orders — for example
--   chapter 5's ID-algorithm "preceding Markov blanket" slice
--   (id-algorithm.tex §"preceding Markov blanket", around lines
--   227–240), which carves `J ∪ V` into `{w | w < v}`, `{v}`,
--   `{w | v < w}` purely via the total-order content, and chapter
--   5's factorisation reverse-ordering step (id-algorithm.tex line
--   466).  Downstream consumers that *do* have a
--   `G.IsTopologicalOrder lt` witness in scope reach the
--   `IsTotalOrder` premise via the first projection
--   `(h_topo : G.IsTopologicalOrder lt).1 : G.IsTotalOrder lt` —
--   one-step, no plumbing.  Matches the helper-vs-full-predicate
--   split spelled out in the `IsTotalOrder` REPLACEMENT block in
--   `TopologicalOrder.lean`.
--
-- *LN-vs-downstream-usage tension worth flagging explicitly.*  A
--   future reader skimming the chapter-4+ call sites of `\Pred` will
--   notice that *every* downstream LN consumer — CBN factorisation
--   (chapter 4), do-calculus (chapter 5), σ-/d-separation (chapters
--   6–7), iSCM recursion (chapters 8–10), and most slices of the
--   ID-algorithm (chapter 5, e.g.\ id-algorithm.tex around lines
--   228, 248, 284, 348) — opens with "Let `<` be a *topological*
--   order of `G`", strictly stronger than def_3_9's own "Let `<` be
--   a *total order* of `J ∪ V`".  A reader inspecting that
--   chapter-4+ usage may therefore expect *this* signature to
--   require the full `G.IsTopologicalOrder lt` premise.  We
--   deliberately keep it at the weaker `IsTotalOrder` because
--   def_3_9's *own* LN block — the row being formalised here — asks
--   for nothing more.  Closing the loosened-domain leak without
--   silently *over*-tightening beyond def_3_9's literal phrasing is
--   what keeps the `Pred` primitive LN-faithful to *this row*, not
--   to its typical downstream call context.  Concrete consumers
--   where the weaker hypothesis genuinely matters: chapter 5's
--   ID-algorithm "preceding Markov blanket" slice
--   (id-algorithm.tex §lines 227–240, which carves `J ∪ V` purely
--   via total-order content with no parent-precedence) and the
--   factorisation reverse-ordering step (id-algorithm.tex line 466,
--   which reverses a total order — an operation on the total-order
--   content alone).  Every other chapter-4+ consumer with a
--   topological-order witness projects to `IsTotalOrder` via `.1`
--   at zero cost, so the weaker premise costs them nothing.
--
-- *Why the hypothesis is unused in the body (and named `_h`).*  The
--   hypothesis exists purely as a type-level contract.  The body is
--   unchanged from the original block (`{w | w ∈ G ∧ lt w v}` is the
--   literal LN spelling), and intentionally so: the strict-checker's
--   diagnosis was not that the body was wrong, but that the type
--   signature was too permissive.  Closing the type-level hole does
--   not require changing the predecessor-set computation itself,
--   which always made sense as `{w ∈ G | lt w v}` regardless of
--   whether `lt` carried the total-order content — the computation
--   just was not *justified* without that content.  The parameter
--   is bound with the leading-underscore name `_h` (the standard
--   Lean / Mathlib convention for "explicitly unused but
--   load-bearing in the type contract"): this silences the
--   `unusedVariables` linter while keeping the parameter positional
--   for callers (callers pass it as the third positional argument
--   regardless of the binder name, e.g.\
--   `refactor_PredLE` below writes `G.refactor_Pred lt h v` where
--   its own `h` flows into `refactor_Pred`'s `_h` slot).
--   `refactor_PredLE`'s own body *does* reference its `h` (to
--   forward it through the call to `refactor_Pred`), so there the
--   binder name stays `h` without a leading underscore.
--
-- *Carry-over rationales (from the ORIGINAL block above; cited
--   rather than full-restated — see that block for the long form).*
--   (a) `Set Node` return type: matches the chapter's `def_3_5`
--   family-set convention (`Pa`, `Ch`, `Sib`, `Anc`, `Desc`, `Sc`,
--   `Dist` are all `Set Node`-valued); composes naturally with
--   downstream `Pa^G(v)`, `Sib^G(v)` etc.\ via Mathlib's `Set` API
--   without `Finset.coe` round-trips.  `Finset Node` and
--   `↥(G.J ∪ G.V) → Set ↥(G.J ∪ G.V)` were considered and rejected
--   for decidability-threading and `Subtype.val` coercion reasons
--   spelled out in the ORIGINAL block.
--   (b) `w ∈ G` conjunct in the body: mirrors the LN's literal
--   `{w ∈ J ∪ V | w < v}`, makes the membership witness available
--   immediately on destructuring `h_w : w ∈ G.refactor_Pred lt h v`
--   as `⟨hw_mem, hw_lt⟩`, and preserves the literal LN grep
--   correspondence.  Wording-check subtlety
--   `ambiguous_w_in_G_notation` is resolved on the nose via
--   `def_3_2`'s `Membership Node (CDMG Node)` instance.
--   (c) `Prop`-valued `(h : G.refactor_IsTotalOrder lt)`, not a
--   typeclass `[G.IsTotalOrder lt]` or structure-field encoding:
--   matches the `lt` argument's own `Prop`-shape and avoids forcing
--   every consumer to thread `[G.IsTotalOrder lt]` brackets through
--   every signature.  The LN's reading is "*let `<` be a total
--   order*" — a *named property* of a chosen relation, not an
--   instance the resolver surfaces silently.  Same rationale as
--   the helper's own `def : Prop` shape in `TopologicalOrder.lean`'s
--   `IsTotalOrder` REPLACEMENT block (no-instance-plumbing,
--   no-wrapper-relation, no-bracket-threading at every use site).
--   (d) `v : Node` unconstrained: per the rewritten tex spec, the LN
--   does *not* impose `v ∈ J ∪ V`.  We follow the literal stance
--   and take `v : Node` raw.  Corner case `v ∉ G`: the strict body
--   is empty (no `w` has `lt w v` because `lt` is supplied only as
--   a total order on `J ∪ V` by `h`).  Adding a `(hv : v ∈ G)`
--   hypothesis was considered and rejected for the same reasons as
--   the ORIGINAL block: it would force every downstream call site
--   to supply the witness even when `v` lies in `G.J ∪ G.V` by
--   construction.
--
-- *Refactor coexistence note.*  Both the prefixed `refactor_Pred`
--   here and the unprefixed `Pred` in the `REFACTOR-BLOCK-ORIGINAL`
--   block above coexist as top-level declarations of
--   `Causality.CDMG` until Phase~7 cleanup.  No §3.1 row currently
--   consumes `Pred` / `PredLE` outside this refactor table — the
--   refactor's `claim_3_2` DEPENDENT row is included for `def_3_8`'s
--   shape change (the iff theorem's destructure / construct
--   pattern), not for `def_3_9` (the iff theorem does not touch
--   predecessor sets) — so the build stays green throughout the
--   refactor.  At cleanup, the original block is deleted and every
--   occurrence of `refactor_Pred` / `refactor_IsTotalOrder` across
--   the codebase is renamed to the unprefixed form.  After cleanup,
--   `G.IsTotalOrder` is the (now unique) name of the total-order
--   helper introduced by `def_3_8`.
--
-- *Downstream consumers (post-refactor).*  Chapter 4 CBN
--   factorisation reads "for each `v ∈ V`, condition on the values
--   at `Pred^G_<(v) ∩ V`"; do-calculus (chapter 5) uses
--   `Pred^G_<(v)` to identify the temporal-ordering context of an
--   intervention; σ-/d-separation (chapters 6–7) take a topological
--   order from `claim_3_2`'s existential and quantify over
--   predecessors; iSCMs (chapters 8–10) recursively compute values
--   at `v` from values at `Pred^G_<(v)`.  Post-refactor, every such
--   consumer threads `h` through the call to `G.Pred lt h v`,
--   typically obtained via the first projection
--   `(h_topo : G.IsTopologicalOrder lt).1` from a topological-order
--   hypothesis already in scope.
-- def_3_9 -- start statement
def refactor_Pred (G : CDMG Node) (lt : Node → Node → Prop)
    (_h : G.refactor_IsTotalOrder lt) (v : Node) : Set Node :=
  {w | w ∈ G ∧ lt w v}
-- def_3_9 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Pred

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: PredLE (was: refactor_PredLE)
-- ref: def_3_9 (refactor: total_order_helper, non-strict predecessors)
--
-- `G.refactor_PredLE lt h v` (post-refactor shape) is the set of
-- *non-strict* predecessors of `v` in `G` under `lt`: the strict
-- predecessor set `G.refactor_Pred lt h v` together with `v`
-- itself.  The body's semantic content is unchanged from the
-- original (`REFACTOR-BLOCK-ORIGINAL: PredLE` above) — still
-- `Pred lt v ∪ {v}` semantically — but now wired to the
-- post-refactor `refactor_Pred` (which itself carries the threaded
-- `h`).  The signature adds the same explicit
-- `(h : G.refactor_IsTotalOrder lt)` hypothesis as `refactor_Pred`,
-- sitting between `lt` and `v`.
/-
LN tex (rewritten canonical statement for `def_3_9`, non-strict form):

  Pred^G_≤(v) := {w ∈ J ∪ V | w < v} ∪ {v}.
-/
-- ## Design choice
--
-- *Why add `(h : G.refactor_IsTotalOrder lt)` to the signature.*
--   Same root cause as `refactor_Pred` above (see that REPLACEMENT
--   block for the full discussion): pre-refactor, `PredLE G lt v`
--   was well-typed for any binary relation `lt`, but the LN's
--   `Pred^G_≤(v)` is only well-defined when `<` is a total order on
--   `J ∪ V`.  This is the `verify_equivalence` item~1a /
--   `verify_equivalence_strict` "loosening a quantifier's domain"
--   failure: the LN premise lived in the 60+ lines of original
--   design comments rather than in the type contract.  Adding `h`
--   closes the leak at the source — and propagates through
--   `refactor_Pred`'s own signature, since the body calls
--   `G.refactor_Pred lt h v`.
--
-- *Why the helper is `refactor_IsTotalOrder`, not
--   `refactor_IsTopologicalOrder`.*  Same as `refactor_Pred`: the
--   LN's premise here is just "let `<` be a total order of
--   `J ∪ V`", not "let `<` be a topological order".  Demanding the
--   full topological-order shape would over-constrain consumers
--   that want non-strict predecessor sets purely under total-order
--   content (chapter 5's ID-algorithm "preceding Markov blanket"
--   slice; CBN factorisation's "earlier-than" context under an
--   analytical non-topological detour ordering).  Downstream
--   consumers with a topological-order witness project via `.1`.
--
-- *LN-vs-downstream-usage tension worth flagging (same point as
--   `refactor_Pred`'s LN-vs-downstream bullet above; cited rather
--   than full-restated).*  Every downstream LN consumer of
--   `\Pred_{≤}` opens with "Let `<` be a *topological* order" —
--   strictly stronger than def_3_9's own "Let `<` be a *total*
--   order of `J ∪ V`".  A reader inspecting chapter-4+ usage may
--   expect the stronger hypothesis here; we deliberately keep it
--   at the weaker `IsTotalOrder` because def_3_9's *own* LN block
--   — this row — asks for nothing more.  Consumers with a
--   topological-order witness project to `IsTotalOrder` via `.1`
--   at zero cost, so the weaker premise costs them nothing while
--   keeping `PredLE` LN-faithful to *this row*'s literal phrasing.
--
-- *Why `h` is unused in `refactor_PredLE`'s body, yet still
--   threaded through `refactor_Pred`.*  The hypothesis is purely a
--   type-level contract at the `refactor_PredLE` signature — its
--   role is to *force the caller* to supply a total-order witness,
--   not to be inspected in the body.  But the body calls
--   `G.refactor_Pred lt h v`, and the post-refactor `Pred` *does*
--   demand `h` on its own signature (same hypothesis, same role).
--   So `h` is forwarded through the call.  No inspection happens
--   on either side — the witness is plumbing, not data — but the
--   type contract is preserved end-to-end.
--
-- *Why the replacement calls `G.refactor_Pred lt h v` (prefixed),
--   not `G.Pred lt v` (unprefixed).*  During the refactor, both
--   the legacy `Pred` (no `h`) and the post-refactor
--   `refactor_Pred` (with `h`) coexist as top-level declarations of
--   `Causality.CDMG`.  The post-refactor `refactor_PredLE` must
--   wire to the post-refactor `refactor_Pred`, for two reasons.
--   (i) **Signature consistency:**  the legacy `G.Pred lt v` takes
--   no `h` argument, so calling it would not type-check with the
--   `h` we have in scope (it would leave `h` unused, but more
--   importantly would silently re-couple the post-refactor `PredLE`
--   to a no-hypothesis strict-predecessor primitive — defeating the
--   refactor's purpose, since every downstream `PredLE` proof would
--   then silently reach the leaky `Pred` rather than the
--   type-enforced `refactor_Pred`).
--   (ii) **Cleanup symmetry:**  cleanup renames `refactor_Pred`
--   → `Pred` and `refactor_PredLE` → `PredLE` globally; after that,
--   the unprefixed `PredLE`'s body will read `G.Pred lt h v`,
--   identical to the original wiring but with the threaded `h`.
--   Using the prefixed name *now* keeps the post-cleanup body
--   correct by construction.
--
-- *Carry-over rationales (from the ORIGINAL block above; cited,
--   not full-restated).*
--   (a) Literal LN body `G.refactor_Pred lt h v ∪ {v}`, NOT
--   `{w | w ∈ G ∧ (lt w v ∨ w = v)}` or `{w | w ∈ G ∧
--   Relation.ReflGen lt w v}`: the LN subscript reads "≤" but the
--   body it writes is strict, with `{v}` adjoined unconditionally.
--   Wording-check subtleties `v_not_required_to_be_in_J_union_V`
--   and `subscript_le_body_uses_strict` apply unchanged: in the
--   corner case `v ∉ G`, the strict body filters by `w ∈ G`, so
--   `v` is admitted into `PredLE G lt v` only via the adjoined
--   singleton — and the singleton has no `v ∈ G` guard.  Hence
--   `v ∈ PredLE G lt v` *unconditionally*, even for `v ∉ G`.  The
--   total-order hypothesis `h` does not change this corner-case
--   behaviour: `h` constrains `lt` on `J ∪ V`, not the surrounding
--   ambient `Node` type, so the body's set-theoretic semantics on
--   nodes outside `G` is identical to the pre-refactor reading.
--   Any downstream consumer that needs the cleaner form
--   `{w | w ≤ v}` can prove a one-step equivalence under the
--   additional hypothesis `v ∈ G` (plus irreflexivity of `lt`,
--   available via `h.1`).
--   (b) `G.refactor_Pred lt h v ∪ {v}` spelled with the named
--   strict predecessor, NOT unfolded to
--   `{w | w ∈ G ∧ lt w v} ∪ {v}`: reads on the nose as the LN's
--   "the strict predecessor set plus `v`" semantic story;
--   downstream proofs with `h_w : w ∈ G.refactor_Pred lt h v` in
--   scope use `Or.inl h_w` directly to obtain
--   `w ∈ G.refactor_PredLE lt h v` (Mathlib's `Set.mem_union` and
--   `Set.mem_singleton_iff` are the natural destructors).
--   (c) `Set Node` return type, `Prop`-valued `h`: same rationale
--   as `refactor_Pred` above.
--   (d) `{v}` parses as the `Set Node` singleton via
--   `Set.instSingleton`: Lean's elaboration sees `∪` on a
--   `Set Node` left-hand side and resolves the brace notation to
--   the matching `Set` instance, no explicit ascription needed.
--
-- *Refactor coexistence note.*  Both the prefixed `refactor_PredLE`
--   and the unprefixed `PredLE` (in the `REFACTOR-BLOCK-ORIGINAL`
--   block above) live in this file as top-level declarations of
--   `Causality.CDMG` until Phase~7 cleanup.  Cleanup deletes the
--   originals and renames `refactor_Pred` → `Pred`,
--   `refactor_PredLE` → `PredLE` globally; after that, the
--   unprefixed `PredLE` will call the unprefixed `Pred`, identical
--   to the original wiring but with the threaded `h`.  No §3.1
--   row currently consumes `PredLE` (the refactor's `claim_3_2`
--   DEPENDENT row is included for `def_3_8`'s shape change, not
--   for `def_3_9` — `claim_3_2` does not touch `PredLE`), so the
--   build stays green throughout.
--
-- *Downstream consumers (post-refactor).*  Every chapter that
--   reasons modulo "the nodes up to and including `v`" — CBN
--   factorisation's conditioning argument (chapter 4),
--   do-calculus's "earlier-than" context (chapter 5), iSCM
--   recursion's "values determined by `Pred_≤`" (chapters 8–10) —
--   uses `PredLE`.  Post-refactor, those consumers thread the same
--   `h` (typically obtained via `.1` from a topological-order
--   hypothesis) that `Pred` requires.  The split between `Pred`
--   and `PredLE` is purely the strict-vs-non-strict variant the LN
--   explicitly introduces; both names appear under that
--   distinction in later chapters.
-- def_3_9 -- start statement
def refactor_PredLE (G : CDMG Node) (lt : Node → Node → Prop)
    (h : G.refactor_IsTotalOrder lt) (v : Node) : Set Node :=
  G.refactor_Pred lt h v ∪ {v}
-- def_3_9 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: PredLE

end CDMG

end Causality
