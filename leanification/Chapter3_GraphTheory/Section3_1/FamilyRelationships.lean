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

-- ref: def_3_5 (item i, parents of a vertex) — refactor
--
-- One-line cross-ref: see the `Pa` design block above for the
-- load-bearing rationale (LN-faithful set-builder, deliberate
-- inclusion of `v` on directed self-loops, redundant-but-kept
-- `w ∈ G` guard).  This twin shares all of it; the only shift is
-- the upstream type `CDMG Node → CDMG Node`.  `G.E`'s
-- carrier `Finset (Node × Node)` is unchanged by the refactor, so
-- the body `(w, v) ∈ G.E` reads verbatim.
-- def_3_5 -- start statement
def Pa (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (w, v) ∈ G.E}
-- def_3_5 -- end statement

-- ref: def_3_5 (item i, parents of a set) — refactor
--
-- One-line cross-ref: see the `PaSet` design block above for the
-- `Set.biUnion` rationale, the `A : Set Node` choice, and the
-- singleton identity `PaSet G {v} = Pa G v`.  This twin shares all
-- of it; only the upstream type and the inner per-vertex primitive
-- `G.Pa v → G.Pa v` change.
-- def_3_5 -- start statement
def PaSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Pa v
-- def_3_5 -- end statement

-- ref: def_3_5 (item ii, children of a vertex) — refactor
--
-- One-line cross-ref: see the `Ch` design block above for the
-- mirror-of-`Pa` rationale and the self-loop convention.  This
-- twin shares all of it; only the upstream type shifts.  `G.E` is
-- unchanged by the refactor, so the body `(v, w) ∈ G.E` reads
-- verbatim.
-- def_3_5 -- start statement
def Ch (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ (v, w) ∈ G.E}
-- def_3_5 -- end statement

-- ref: def_3_5 (item ii, children of a set) — refactor
--
-- One-line cross-ref: see the `ChSet` design block above for the
-- `Set.biUnion` rationale shared with `PaSet`.  This twin shares
-- all of it; only the upstream type and the inner per-vertex
-- primitive `G.Ch v → G.Ch v` change.
-- def_3_5 -- start statement
def ChSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Ch v
-- def_3_5 -- end statement

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
def Sib (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ s(v, w) ∈ G.L}
-- def_3_5 -- end statement

-- ref: def_3_5 (item iv, ancestors of a vertex) — refactor
--
-- One-line cross-ref: see the `Anc` design block above for the
-- `Walk + IsDirectedWalk` rationale, the unconditional self-
-- membership argument via `Walk.nil`, and the resolution of the
-- `trivial_walk_implicit_in_self_membership_notes` wording-check
-- subtlety.  This twin shares all of it; the upstream witness
-- `Walk.nil v hv` becomes `Walk.nil v hv` and the
-- predicate `IsDirectedWalk` becomes `IsDirectedWalk` —
-- same structural argument (the refactored `IsDirectedWalk
-- (.nil _ _) = True` branch is unchanged from the original
-- `IsDirectedWalk (.nil _ _) = True`), no semantic change.
-- def_3_5 -- start statement
def Anc (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : Walk G w v, p.IsDirectedWalk}
-- def_3_5 -- end statement

-- ref: def_3_5 (item iv, ancestors of a set) — refactor
--
-- One-line cross-ref: see the `AncSet` design block above for the
-- `Set.biUnion` rationale and the LN's `A ⊆ Anc^G(A)` corollary.
-- This twin shares all of it; only the upstream type and the inner
-- per-vertex primitive `G.Anc v → G.Anc v` change.
-- def_3_5 -- start statement
def AncSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Anc v
-- def_3_5 -- end statement

-- ref: def_3_5 (item v, descendants of a vertex) — refactor
--
-- One-line cross-ref: see the `Desc` design block above for the
-- mirror-of-`Anc`-with-reversed-walk-direction rationale and the
-- unconditional self-membership via `Walk.nil`.  This twin shares
-- all of it; the upstream witness `Walk.nil v hv` becomes
-- `Walk.nil v hv` and the predicate `IsDirectedWalk`
-- becomes `IsDirectedWalk` — same structural argument
-- (the refactored `IsDirectedWalk (.nil _ _) = True`
-- branch is unchanged), no semantic change.
-- def_3_5 -- start statement
def Desc (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : Walk G v w, p.IsDirectedWalk}
-- def_3_5 -- end statement

-- ref: def_3_5 (item v, descendants of a set) — refactor
--
-- One-line cross-ref: see the `DescSet` design block above for the
-- `Set.biUnion` rationale and the load-bearing role this set form
-- plays for `NonDesc` below.  This twin shares all of it; only the
-- upstream type and the inner per-vertex primitive `G.Desc v →
-- G.Desc v` change.
-- def_3_5 -- start statement
def DescSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Desc v
-- def_3_5 -- end statement

-- ref: def_3_5 (item vi, non-descendants of a set) — refactor
--
-- One-line cross-ref: see the `NonDesc` design block above for the
-- no-per-vertex-form decision, the complement-inside-`J ∪ V`
-- rationale, the `Finset → Set` coercion choice, and the downstream
-- Markov-blanket pattern.  This twin shares all of it; only the
-- upstream type and the inner `G.DescSet A → G.DescSet A`
-- reference change.  `G.J`, `G.V` are unchanged by the refactor, so
-- the `((G.J ∪ G.V : Finset Node) : Set Node)` form reads verbatim.
-- def_3_5 -- start statement
def NonDesc (G : CDMG Node) (A : Set Node) : Set Node :=
  ((G.J ∪ G.V : Finset Node) : Set Node) \ G.DescSet A
-- def_3_5 -- end statement

-- ref: def_3_5 (item vii, strongly connected component of a vertex) — refactor
--
-- One-line cross-ref: see the `Sc` design block above for the
-- literal-`Anc ∩ Desc` rationale, the corollary-not-axiom shape of
-- the `v ∈ Sc G v` self-membership note, and the downstream
-- acyclification / ID-algorithm pattern.  This twin shares all of
-- it; only the upstream type and the inner cross-references
-- `G.Anc v → G.Anc v`, `G.Desc v → G.Desc v`
-- change.
-- def_3_5 -- start statement
def Sc (G : CDMG Node) (v : Node) : Set Node :=
  G.Anc v ∩ G.Desc v
-- def_3_5 -- end statement

-- ref: def_3_5 (item vii, strongly connected components of a set) — refactor
--
-- One-line cross-ref: see the `ScSet` design block above for the
-- `Set.biUnion` rationale and the union-of-components-vs-single-
-- component terminology note.  This twin shares all of it; only the
-- upstream type and the inner per-vertex primitive `G.Sc v →
-- G.Sc v` change.
-- def_3_5 -- start statement
def ScSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Sc v
-- def_3_5 -- end statement

-- ref: def_3_5 (item viii, district of a vertex) — refactor
--
-- One-line cross-ref: see the `Dist` design block above for the
-- shared-walk-carrier-with-`Anc`/`Desc` rationale, the resolution
-- of the `district_walk_indexing_ambiguous_for_small_n` wording-
-- check subtlety, the unconditional self-membership argument, and
-- the downstream ID-algorithm pattern.  This twin shares all of
-- it; the upstream witness `Walk.nil v hv` becomes
-- `Walk.nil v hv` and the predicate `IsBidirectedWalk`
-- becomes `IsBidirectedWalk` — same structural argument
-- (the refactored `IsBidirectedWalk (.nil _ _) = True`
-- branch is unchanged), no semantic change.  The graph-theoretic
-- symmetry `w ∈ Dist G v ↔ v ∈ Dist G w` now follows from `Sym2`'s
-- definitional swap symmetry plus walk reversal, rather than from
-- `hL_symm` — see the `Sib` block for the analogous
-- discharge of the `hL_symm` route.
-- def_3_5 -- start statement
def Dist (G : CDMG Node) (v : Node) : Set Node :=
  {w | w ∈ G ∧ ∃ p : Walk G v w, p.IsBidirectedWalk}
-- def_3_5 -- end statement

-- ref: def_3_5 (item viii, district of a set) — refactor
--
-- One-line cross-ref: see the `DistSet` design block above for the
-- `Set.biUnion` rationale and the union-vs-maximal-component
-- terminology note.  This twin shares all of it; only the upstream
-- type and the inner per-vertex primitive `G.Dist v →
-- G.Dist v` change.
-- def_3_5 -- start statement
def DistSet (G : CDMG Node) (A : Set Node) : Set Node :=
  ⋃ v ∈ A, G.Dist v
-- def_3_5 -- end statement

end CDMG

end Causality
