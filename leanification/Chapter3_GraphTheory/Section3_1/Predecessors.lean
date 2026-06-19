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
-- `G.Pred lt h v` is the set of *strict* predecessors of `v` in `G`
-- under the order `lt`: nodes `w ∈ J ∪ V` (i.e.\ `w ∈ G` via
-- `def_3_2`'s `Membership` instance) with `lt w v`.  The signature
-- takes an explicit `(h : G.IsTotalOrder lt)` hypothesis sitting
-- between `lt` and `v`, enforcing the LN's "*Let `<` be a total
-- order of `J ∪ V`*" premise at the type level.
/-
LN tex (rewritten canonical statement for `def_3_9`, strict form):

  Pred^G_<(v) := {w ∈ J ∪ V | w < v}.
-/
-- ## Design choice
--
-- *Why `Pred` takes `(h : G.IsTotalOrder lt)` explicitly.*
--   The LN's `Pred^G_<(v)` is only well-defined when `<` is a total
--   order on `J ∪ V` (the LN block opens "*Let `<` be a total order
--   of `J ∪ V`*").  Without a hypothesis carrying that premise,
--   `Pred G lt v` would be well-typed for *any* binary relation
--   `lt`, loosening the LN quantifier's domain and pushing the
--   total-order premise off the type contract and into prose the
--   type checker cannot inspect.  Threading `h` through the
--   signature closes the leak at the source: every downstream
--   consumer must supply the total-order witness, so `G.Pred lt h v`
--   and the LN's `Pred^G_<(v)` coincide *by construction*.
--
-- *Why the helper is `IsTotalOrder` (not the full
--   `IsTopologicalOrder`).*  The LN's premise in this row
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
--   split spelled out in the `IsTotalOrder` block in
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
--   hypothesis exists purely as a type-level contract.  The body
--   `{w | w ∈ G ∧ lt w v}` is the literal LN spelling and does not
--   need to inspect `h` — the role of `h` is to force the caller to
--   supply the total-order witness, not to feed the set-builder.
--   The parameter is bound with the leading-underscore name `_h`
--   (the standard Lean / Mathlib convention for "explicitly unused
--   but load-bearing in the type contract"): this silences the
--   `unusedVariables` linter while keeping the parameter positional
--   for callers (callers pass it as the third positional argument
--   regardless of the binder name, e.g.\ `PredLE` below writes
--   `G.Pred lt h v` where its own `h` flows into `Pred`'s `_h`
--   slot).  `PredLE`'s own body *does* reference its `h` (to forward
--   it through the call to `Pred`), so there the binder name stays
--   `h` without a leading underscore.
--
-- *Further rationales for the chosen shape.*
--   (a) `Set Node` return type: matches the chapter's `def_3_5`
--   family-set convention (`Pa`, `Ch`, `Sib`, `Anc`, `Desc`, `Sc`,
--   `Dist` are all `Set Node`-valued); composes naturally with
--   downstream `Pa^G(v)`, `Sib^G(v)` etc.\ via Mathlib's `Set` API
--   without `Finset.coe` round-trips.  `Finset Node` and
--   `↥(G.J ∪ G.V) → Set ↥(G.J ∪ G.V)` were considered and rejected
--   for decidability-threading and `Subtype.val` coercion reasons.
--   (b) `w ∈ G` conjunct in the body: mirrors the LN's literal
--   `{w ∈ J ∪ V | w < v}`, makes the membership witness available
--   immediately on destructuring `h_w : w ∈ G.Pred lt h v`
--   as `⟨hw_mem, hw_lt⟩`, and preserves the literal LN grep
--   correspondence.  Wording-check subtlety
--   `ambiguous_w_in_G_notation` is resolved on the nose via
--   `def_3_2`'s `Membership Node (CDMG Node)` instance.
--   (c) `Prop`-valued `(h : G.IsTotalOrder lt)`, not a
--   typeclass `[G.IsTotalOrder lt]` or structure-field encoding:
--   matches the `lt` argument's own `Prop`-shape and avoids forcing
--   every consumer to thread `[G.IsTotalOrder lt]` brackets through
--   every signature.  The LN's reading is "*let `<` be a total
--   order*" — a *named property* of a chosen relation, not an
--   instance the resolver surfaces silently.  Same rationale as
--   the helper's own `def : Prop` shape in `TopologicalOrder.lean`'s
--   `IsTotalOrder` block (no-instance-plumbing, no-wrapper-relation,
--   no-bracket-threading at every use site).
--   (d) `v : Node` unconstrained: per the canonical tex spec, the LN
--   does *not* impose `v ∈ J ∪ V`.  We follow the literal stance
--   and take `v : Node` raw.  Corner case `v ∉ G`: the strict body
--   is empty (no `w` has `lt w v` because `lt` is supplied only as
--   a total order on `J ∪ V` by `h`).  Adding a `(hv : v ∈ G)`
--   hypothesis was considered and rejected: it would force every
--   downstream call site to supply the witness even when `v` lies
--   in `G.J ∪ G.V` by construction.
--
-- *Downstream consumers.*  Chapter 4 CBN factorisation reads "for
--   each `v ∈ V`, condition on the values at `Pred^G_<(v) ∩ V`";
--   do-calculus (chapter 5) uses `Pred^G_<(v)` to identify the
--   temporal-ordering context of an intervention; σ-/d-separation
--   (chapters 6–7) take a topological order from `claim_3_2`'s
--   existential and quantify over predecessors; iSCMs (chapters
--   8–10) recursively compute values at `v` from values at
--   `Pred^G_<(v)`.  Every such consumer threads `h` through the
--   call to `G.Pred lt h v`, typically obtained via the first
--   projection `(h_topo : G.IsTopologicalOrder lt).1` from a
--   topological-order hypothesis already in scope.

-- ref: def_3_9 (non-strict predecessors)
--
-- `G.PredLE lt h v` is the set of *non-strict* predecessors of `v`
-- in `G` under `lt`: the strict predecessor set `G.Pred lt h v`
-- together with `v` itself, i.e.\ `Pred lt v ∪ {v}`.  The signature
-- carries the same explicit `(h : G.IsTotalOrder lt)` hypothesis as
-- `Pred`, sitting between `lt` and `v`, and the body forwards `h`
-- into the call to `Pred`.
/-
LN tex (rewritten canonical statement for `def_3_9`, non-strict form):

  Pred^G_≤(v) := {w ∈ J ∪ V | w < v} ∪ {v}.
-/
-- ## Design choice
--
-- *Why `PredLE` takes `(h : G.IsTotalOrder lt)` explicitly.*
--   Same root cause as `Pred` above (see that block for the full
--   discussion): the LN's `Pred^G_≤(v)` is only well-defined when
--   `<` is a total order on `J ∪ V`, so without `h` the signature
--   would be too permissive and the total-order premise would live
--   off the type contract.  Threading `h` closes the leak at the
--   source and propagates naturally through `Pred`'s own signature,
--   since the body calls `G.Pred lt h v`.
--
-- *Why the helper is `IsTotalOrder`, not
--   `IsTopologicalOrder`.*  Same as `Pred`: the
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
--   `Pred`'s LN-vs-downstream bullet above; cited rather
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
-- *Why `h` is unused in `PredLE`'s body, yet still threaded
--   through `Pred`.*  The hypothesis is purely a type-level
--   contract at the `PredLE` signature — its role is to *force the
--   caller* to supply a total-order witness, not to be inspected in
--   the body.  But the body calls `G.Pred lt h v`, and `Pred` *does*
--   demand `h` on its own signature (same hypothesis, same role).
--   So `h` is forwarded through the call.  No inspection happens
--   on either side — the witness is plumbing, not data — but the
--   type contract is preserved end-to-end.
--
-- *Further rationales for the chosen shape.*
--   (a) Literal LN body `G.Pred lt h v ∪ {v}`, NOT
--   `{w | w ∈ G ∧ (lt w v ∨ w = v)}` or `{w | w ∈ G ∧
--   Relation.ReflGen lt w v}`: the LN subscript reads "≤" but the
--   body it writes is strict, with `{v}` adjoined unconditionally.
--   Wording-check subtleties `v_not_required_to_be_in_J_union_V`
--   and `subscript_le_body_uses_strict` apply: in the corner case
--   `v ∉ G`, the strict body filters by `w ∈ G`, so `v` is admitted
--   into `PredLE G lt v` only via the adjoined singleton — and the
--   singleton has no `v ∈ G` guard.  Hence `v ∈ PredLE G lt v`
--   *unconditionally*, even for `v ∉ G`.  The total-order
--   hypothesis `h` constrains `lt` on `J ∪ V`, not the surrounding
--   ambient `Node` type, so it leaves the body's set-theoretic
--   semantics on nodes outside `G` untouched.  Any downstream
--   consumer that needs the cleaner form `{w | w ≤ v}` can prove a
--   one-step equivalence under the additional hypothesis `v ∈ G`
--   (plus irreflexivity of `lt`, available via `h.1`).
--   (b) `G.Pred lt h v ∪ {v}` spelled with the named
--   strict predecessor, NOT unfolded to
--   `{w | w ∈ G ∧ lt w v} ∪ {v}`: reads on the nose as the LN's
--   "the strict predecessor set plus `v`" semantic story;
--   downstream proofs with `h_w : w ∈ G.Pred lt h v` in
--   scope use `Or.inl h_w` directly to obtain
--   `w ∈ G.PredLE lt h v` (Mathlib's `Set.mem_union` and
--   `Set.mem_singleton_iff` are the natural destructors).
--   (c) `Set Node` return type, `Prop`-valued `h`: same rationale
--   as `Pred` above.
--   (d) `{v}` parses as the `Set Node` singleton via
--   `Set.instSingleton`: Lean's elaboration sees `∪` on a
--   `Set Node` left-hand side and resolves the brace notation to
--   the matching `Set` instance, no explicit ascription needed.
--
-- *Downstream consumers.*  Every chapter that reasons modulo "the
--   nodes up to and including `v`" — CBN factorisation's
--   conditioning argument (chapter 4), do-calculus's "earlier-than"
--   context (chapter 5), iSCM recursion's "values determined by
--   `Pred_≤`" (chapters 8–10) — uses `PredLE`.  Those consumers
--   thread the same `h` (typically obtained via `.1` from a
--   topological-order hypothesis) that `Pred` requires.  The split
--   between `Pred` and `PredLE` is purely the strict-vs-non-strict
--   variant the LN explicitly introduces; both names appear under
--   that distinction in later chapters.

end CDMG

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- Three-dash `--- start helper` markers match the convention used
-- across `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
-- `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
-- `CDMGTypes.lean`, `FamilyRelationships.lean`, and
-- `TopologicalOrder.lean` for the `variable` line that binds the
-- implicit parameters into the predicates wrapped below.  Both
-- `Node : Type*` and `[DecidableEq Node]` are inherited verbatim
-- from `def_3_1`'s refactor twin (`CDMG`): the
-- `Membership Node (CDMG Node)` instance from `def_3_2`'s
-- refactor twin (`instMembership` in `CDMGNotation.lean`) —
-- driving the `w ∈ G` conjunct of the `Pred` set-builder
-- body below — reduces to `Finset.mem` on `G.J ∪ G.V`, which needs
-- `DecidableEq Node`.
-- def_3_9 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_9 --- end helper

-- ref: def_3_9 — refactor twin (strict predecessors)
-- `G.Pred lt h v` is the set of *strict* predecessors of
-- `v` in `G` under the order `lt`: nodes `w ∈ J ∪ V` (i.e.\ `w ∈ G`
-- via `def_3_2`'s refactor-twin `Membership` instance) with
-- `lt w v`.  The signature carries an explicit
-- `(h : G.IsTotalOrder lt)` hypothesis sitting between
-- `lt` and `v`, enforcing the LN's "*Let `<` be a total order of
-- `J ∪ V`*" premise at the type level.  See the `Pred` design block
-- above (`namespace CDMG`) for the full rationale — the
-- explicit-`h`-for-domain-anchoring choice, the
-- `IsTotalOrder`-not-`IsTopologicalOrder` premise level, the
-- `_h`-unused-yet-load-bearing convention, the `Set Node` return
-- type with set-builder body (`Finset.filter` and `Subtype`-coerced
-- variants were rejected for decidability-threading and coercion
-- reasons), the `lt : Node → Node → Prop` external-argument shape
-- (vs `[LT Node]` typeclass / structure-field encoding), the
-- `Prop`-valued-`h`-not-typeclass parallel, the literal-LN
-- `w ∈ G ∧ lt w v` body, the deliberate non-constraint on `v`, and
-- the downstream-consumer survey (ch.\ 4 CBN factorisation, ch.\ 5
-- do-calculus / ID-algorithm, ch.\ 6–7 σ/d-separation, ch.\ 8–10
-- iSCM recursion).  All carry over verbatim.
/-
LN tex (rewritten canonical statement for `def_3_9`, strict form,
unchanged by refactor):

  Pred^G_<(v) := {w ∈ J ∪ V | w < v}.
-/
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `Pred`* (`namespace CDMG`, lines
-- above) onto the `cdmg_typed_edges` refactor's new upstream types
-- (DEPENDENT row; root `def_3_1`).  The mathematical content —
-- strict reading of `<`, set-builder body `{w | w ∈ G ∧ lt w v}`,
-- domain restriction via `w ∈ G`, `Set Node` return type,
-- `Prop`-valued explicit `(_h : G.…IsTotalOrder lt)` hypothesis,
-- raw-`lt`-argument shape, and the deliberate non-constraint on `v`
-- — is **unchanged** (byte-identical to the original modulo the
-- type-shifts listed below).  All three wording-check subtleties
-- carried by this row remain resolved exactly as before:
-- `ambiguous_w_in_G_notation` via the `instMembership`
-- instance (`CDMGNotation.lean`'s refactor twin of `def_3_2`)
-- reducing `w ∈ G` to `w ∈ G.J ∪ G.V`,
-- `v_not_required_to_be_in_J_union_V` via the literal LN stance on
-- `v : Node`, and `subscript_le_body_uses_strict` deferred to the
-- `PredLE` block below (the strict body here is unaffected).
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node       → CDMG Node`
--   `G.IsTotalOrder  → G.IsTotalOrder`  (the `h`-hypothesis
--                      premise, retyped onto the refactor namespace
--                      via `TopologicalOrder.lean`'s refactor twin)
-- No other change.  In particular, the `w ∈ G` conjunct of the
-- set-builder body ports verbatim because the
-- `instMembership` instance gives the same `w ∈ G.J ∪ G.V`
-- reduction on `CDMG Node` as the original `instMembership`
-- does on `CDMG Node`.  This predicate does not reach into the `L`
-- field at all — neither directly nor through any of its sub-terms
-- (`G.J ∪ G.V`, `lt`, `h`) — so the
-- `Finset (Node × Node) → Finset (Sym2 Node)` retyping at root
-- `def_3_1` flows through transparently; this is precisely the
-- natural-port property that makes the row a mechanical DEPENDENT.
-- def_3_9 -- start statement
def Pred (G : CDMG Node) (lt : Node → Node → Prop)
    (_h : G.IsTotalOrder lt) (v : Node) : Set Node :=
  {w | w ∈ G ∧ lt w v}
-- def_3_9 -- end statement

-- ref: def_3_9 — refactor twin (non-strict predecessors)
-- `G.PredLE lt h v` is the set of *non-strict* predecessors
-- of `v` in `G` under `lt`: the strict predecessor set
-- `G.Pred lt h v` together with `v` itself, i.e.\
-- `Pred lt v ∪ {v}`.  The signature carries the same
-- explicit `(h : G.IsTotalOrder lt)` hypothesis as
-- `Pred`, sitting between `lt` and `v`, and the body
-- forwards `h` into the call to `Pred`.  See the `PredLE`
-- design block above (`namespace CDMG`) for the full rationale — the
-- literal-LN `Pred lt v ∪ {v}` body (strict body adjoined with the
-- bare singleton, *not* the reflexive-closure `{w | w ≤ v}` form
-- and *not* an independent set-builder), the
-- `PredLE = Pred ∪ {v}`-recursion-on-`Pred` choice (vs unfolding to
-- `{w | w ∈ G ∧ lt w v} ∪ {v}`), the `h`-forwarded-not-inspected
-- pattern (binder named `h` not `_h` because the body references it
-- to forward into `Pred`), the
-- `IsTotalOrder`-not-`IsTopologicalOrder` premise level, the
-- `Set Node` return type with set-builder / `Set`-union body
-- (`Finset`-valued alternatives rejected for the same
-- decidability-threading reasons as `Pred`), the `Prop`-valued-`h`
-- and raw-`lt`-argument shapes, and the downstream-consumer survey
-- (CBN factorisation conditioning, do-calculus's "earlier-than"
-- context, iSCM `Pred_≤`-recursion in ch.\ 8–10).  All carry over
-- verbatim, including the literal-LN corner-case semantics on
-- `v ∉ G` (`v` is admitted into `PredLE G lt v` purely via the
-- adjoined singleton, unconditionally).
/-
LN tex (rewritten canonical statement for `def_3_9`, non-strict
form, unchanged by refactor):

  Pred^G_≤(v) := {w ∈ J ∪ V | w < v} ∪ {v}.
-/
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `PredLE`* (`namespace CDMG`,
-- lines above) onto the `cdmg_typed_edges` refactor's new upstream
-- types (DEPENDENT row; root `def_3_1`, via `def_3_8`'s
-- `IsTotalOrder` and this file's `Pred` just
-- above).  The mathematical content — literal LN body
-- `G.…Pred lt h v ∪ {v}` (strict-set-plus-singleton, not the
-- reflexive-closure `{w | w ≤ v}` form, not unfolded into an
-- independent set-builder), the `h`-forwarded-through-the-call
-- pattern, the `Set Node` return type, and the literal-LN
-- corner-case `v ∈ PredLE lt h v` unconditionally — is
-- **unchanged** (byte-identical to the original modulo the type
-- shifts listed below).  All three wording-check subtleties remain
-- resolved as before: `ambiguous_w_in_G_notation` via the
-- `instMembership` instance (reached transitively through
-- the `Pred` call), `v_not_required_to_be_in_J_union_V` via
-- the unconstrained `v : Node`, and `subscript_le_body_uses_strict`
-- via the literal LN body spelled with the strict `Pred`
-- plus the bare singleton `{v}` (so `v` lands in the non-strict set
-- through `{v}`, not through `lt`; under the corner case `v ∉ G`,
-- the strict half is empty and the singleton carries `v` alone).
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node       → CDMG Node`
--   `G.IsTotalOrder  → G.IsTotalOrder`  (the `h`-hypothesis
--                      premise)
--   `G.Pred          → G.Pred`          (the cross-call to
--                      the strict predecessor set just above, retyped
--                      onto the refactor namespace)
-- No other change.  The literal LN body `G.Pred lt h v ∪
-- {v}` ports verbatim — Lean elaborates the brace notation `{v}` to
-- the `Set Node` singleton via `Set.instSingleton` exactly as in the
-- original, and `∪` resolves to `Set.union` on the same return type.
-- This predicate does not reach into the `L` field at all (neither
-- directly nor through `Pred` — see that block above for
-- the same property at one remove), so the
-- `Finset (Node × Node) → Finset (Sym2 Node)` retyping at root
-- `def_3_1` flows through transparently; this is the natural-port
-- property that lets `PredLE` track its strict cousin as a
-- mechanical DEPENDENT.
-- def_3_9 -- start statement
def PredLE (G : CDMG Node) (lt : Node → Node → Prop)
    (h : G.IsTotalOrder lt) (v : Node) : Set Node :=
  G.Pred lt h v ∪ {v}
-- def_3_9 -- end statement

end CDMG

end Causality
