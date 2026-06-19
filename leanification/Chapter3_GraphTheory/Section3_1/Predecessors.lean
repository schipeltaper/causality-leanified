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
