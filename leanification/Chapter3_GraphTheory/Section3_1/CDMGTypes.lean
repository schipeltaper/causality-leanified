import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.Acyclicity

namespace Causality

/-!
# Named CDMG sub-types (`def_3_7`)

This file formalises the LN definition block `def_3_7`
(`CDMGTypes` in `graphs.tex`):

> A Conditional Directed Mixed Graph (CDMG) `G = (J, V, E, L)` is called:
>   i.   CADMG iff `G` is acyclic;
>   ii.  DMG   iff `J = ∅`;
>   iii. ADMG  iff `G` is acyclic and `J = ∅`;
>   iv.  CDG   iff `L = ∅`;
>   v.   DG    iff `J = ∅` and `L = ∅`;
>   vi.  CDAG  iff `G` is acyclic and `L = ∅`;
>   vii. DAG   iff `G` is acyclic, `J = ∅`, and `L = ∅`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_7_CDMGTypes.tex`,
verified equivalent to the LN block with *no* `addition_to_the_LN`
clarifications — the LN-critic returned `NO_SUBTLETIES` and the rewrite
only made the three atomic conditions and the nested-name semantics
fully explicit.

The seven names below are *attributes* a CDMG may bear, not a
partition: a graph satisfying the DAG conjunction (vii) simultaneously
satisfies every weaker conjunction (i)–(vi) and the base attribute
`CDMG` of `def_3_1`.  The three atomic conditions

* `G.IsAcyclic`            (from `def_3_6`, `Acyclicity.lean`)
* `G.J = ∅`                (Finset equality on `def_3_1`'s `J` field)
* `G.L = ∅`                (Finset equality on `def_3_1`'s `L` field)

are independent boolean predicates on `G : CDMG Node`, yielding
`2³ = 8` combinations; the seven names plus the bare `CDMG` (no
condition) exhaust them.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim
--   from `def_3_1` (`CDMG.lean`) and re-asserted here because every
--   wrapped statement below mentions a `CDMG Node` whose underlying
--   `Finset` and `Membership` machinery need decidable equality on
--   the node universe.  Concretely: (i) `G.J = ∅` and `G.L = ∅` are
--   `Finset` equalities, which decompose to per-element decidable
--   membership tests, and (ii) `G.IsAcyclic` (`def_3_6`) carries the
--   same `[DecidableEq Node]` requirement (its body's `Walk` /
--   `Walk.IsDirectedWalk` / `v ∈ G` machinery all depend on it).
--   Dropping the typeclass would make every predicate below fail to
--   type-check.
--
-- *Three-dash `--- start helper` marker, not the two-dash
--   `-- start statement`.*  Matches the convention established in
--   `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
--   `EdgeRelations.lean`, `CDMGRestrictions.lean`, and
--   `Acyclicity.lean`.  The two-dash marker is reserved for the
--   actual LN definition content; this `variable` line is statement-
--   typing infrastructure, not formalised LN content.
-- def_3_7 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_7 --- end helper

-- ## Shared design choices — apply to all seven predicates below
--
-- *Seven separate `Prop` predicates on `CDMG Node`, one per LN item,
--   not a single `inductive CDMGType` enum.*  The LN's "is called"
--   semantics are *nested membership*: a CDMG satisfying the DAG
--   conjunction (item vii) simultaneously bears each of the names
--   i–vi (and the base `CDMG` attribute of `def_3_1`) — see the tex
--   spec's "Nested-name semantics" paragraph.  An `inductive` /
--   sum-type encoding would force exactly one constructor per graph
--   and could not express this overlap; seven independent
--   `Prop`-valued predicates do, on the nose.  Downstream chapters
--   that quantify over "every DAG" / "every ADMG" then take a single
--   `(h : G.IsDAG)` / `(h : G.IsADMG)` hypothesis without any tag
--   case-split.
--
-- *Predicate names `IsCADMG`, `IsDMG`, `IsADMG`, `IsCDG`, `IsDG`,
--   `IsCDAG`, `IsDAG` — the LN acronyms verbatim, `Is`-prefixed.*
--   `Is`-prefix matches the chapter convention (`IsAcyclic` in
--   `def_3_6`) and mathlib's broader `Is…` predicate naming
--   (`IsAcyclic`, `IsDirected`, `IsConnected`, …).  Capitalisation
--   mirrors the LN acronym exactly so a reader can grep `CADMG` /
--   `ADMG` / `DAG` / etc.\ from the LN and find each Lean
--   counterpart without a translation table.  Order of declaration
--   below matches LN items i–vii left-to-right.
--
-- *Each predicate is the literal conjunction of the LN's stated
--   atomic conditions — `G.IsAcyclic`, `G.J = ∅`, `G.L = ∅` — in the
--   order the LN writes them, with no derived simplifications.*  The
--   LN's item iii reads "acyclic and `J = ∅`"; we encode it as
--   `G.IsAcyclic ∧ G.J = ∅`, in that order, not `G.J = ∅ ∧
--   G.IsAcyclic`.  Items v, vi, vii likewise preserve LN order.
--   Rationale: keeps the `And.intro` / `obtain ⟨h₁, h₂⟩` shape of
--   downstream proofs syntactically aligned with the LN reading.
--   Logically the order is irrelevant; preserving it is a pure
--   readability gain.
--
-- *`def`, not `abbrev`.*  Same rationale as the LN-named relations
--   in `CDMGNotation.lean`: the LN treats `CADMG`, `ADMG`, `DAG`, …
--   as *named* attributes that reappear under those names in later
--   theorems (e.g. claim_3_2 acyclic ⟺ topological order will
--   consume `IsDAG`-shaped hypotheses; the iSCM chapters 8–10
--   quantify over `IsADMG` graphs; do-calculus chapter 5 quantifies
--   over `IsADMG` / `IsDAG` graphs).  An `abbrev` would auto-unfold
--   to the conjunction at every elaboration site, erasing the named
--   abstraction.  Downstream consumers that *want* the underlying
--   conjunction explicit can `unfold CDMG.IsDAG` (or `simp only
--   [CDMG.IsDAG]`) on demand.
--
-- *`G.J = ∅` / `G.L = ∅` as the LN-literal `Finset` equality, not
--   `G.J.card = 0` or `∀ v, v ∉ G.J`.*  The LN writes `J = ∅`
--   verbatim; `def_3_1`'s `CDMG.J : Finset Node` makes this a literal
--   `Finset Node` equality.  Mathlib's `Finset.empty` (denoted `∅`
--   via `EmptyCollection`) is the canonical empty `Finset`, so the
--   spelling `G.J = ∅` reads identically to the LN.  Alternative
--   spellings (`G.J.Nonempty.elim`, `G.J = (∅ : Finset Node)` with
--   explicit annotation, `∀ v ∈ G.J, False`) were rejected as
--   farther from the LN; cardinality- or quantifier-based forms
--   would also force a one-line bridge lemma at every downstream
--   site that case-splits on emptiness.
--
-- *Reuse `IsAcyclic` from `def_3_6` verbatim.*  Every "G is acyclic"
--   clause is exactly `G.IsAcyclic` — no re-definition, no
--   re-statement.  The LN explicitly cross-references `def_3_6` for
--   the meaning of "acyclic"; mirroring that cross-reference in Lean
--   is what keeps the dependency graph between chapter-3 rows
--   visible.
--
-- *No `Decidable` instances exposed here.*  Each predicate is a
--   conjunction of `G.IsAcyclic` (whose decidability is deferred per
--   `Acyclicity.lean`'s design block) and `Finset` equalities
--   (decidable in principle, but only useful when `G.IsAcyclic` is
--   also decidable, which it currently is not).  Decidability
--   plumbing is deferred to use sites that consume it (e.g.\
--   causal-discovery algorithms in chapters 11+).
--
-- *Downstream consumers.*  `IsADMG` is the hypothesis carried by
--   every iSCM / do-calculus / d-separation result in chapters 4–10
--   (CBNs assume an ADMG, do-calculus operates on ADMGs, iSCMs are
--   built on ADMGs).  `IsDAG` is the foundational assumption for
--   classical SCMs / Pearlian causality (chapters 8+ historical
--   discussion).  `IsCADMG` appears whenever a downstream operation
--   moves nodes between `J` and `V` (hard intervention `def_3_10`
--   takes a CADMG to another CADMG by moving `W ⊆ V` into `J`).  The
--   other four (`IsDMG`, `IsCDG`, `IsDG`, `IsCDAG`) appear less
--   often but complete the taxonomy and let downstream cross-
--   references read off the LN.

-- ref: def_3_7 (item i)
-- A CDMG `G = (J, V, E, L)` is a *CADMG* (Conditional Acyclic Directed
-- Mixed Graph) iff `G` is acyclic in the sense of `def_3_6`.
/-
LN tex (item i of `def_3_7`):

  $G$ is called a CADMG iff $G$ is acyclic in the sense of
  def \ref{def-acylic}.
-/
-- ## Design choice
-- Atomic single-condition predicate, an alias for `def_3_6`'s
-- `G.IsAcyclic` packaged under the LN's acronym `CADMG`.  See the
-- shared design block above for the choice of a named `def` over
-- either inlining `G.IsAcyclic` at every chapter-4+ use site or
-- collapsing the alias with an `abbrev` (which would auto-unfold and
-- erase the LN-named abstraction).  CADMGs are notably the target /
-- source shape of hard intervention `def_3_10` (which moves `W ⊆ V`
-- into `J` while preserving acyclicity), so the named hypothesis
-- `(h : G.IsCADMG)` pays off as soon as intervention enters scope.

-- ref: def_3_7 (item ii)
-- A CDMG `G = (J, V, E, L)` is a *DMG* (Directed Mixed Graph) iff
-- `J = ∅` (the input-node `Finset` is empty).
/-
LN tex (item ii of `def_3_7`):

  $G$ is called a DMG iff $J = \emptyset$.
-/
-- ## Design choice
-- Atomic single-condition predicate, an alias for the literal LN
-- equation `J = ∅` written as the `Finset Node` equality
-- `G.J = ∅` on `def_3_1.J`.  See the shared design block above for
-- the `def`-not-`abbrev` and "literal Finset equality over cardinality
-- / quantifier reformulations" rationales.  DMG is the no-input-node
-- root of the M-suffixed (Mixed = bidirected-edges-allowed) taxonomy
-- branch DMG ⊃ ADMG ⊃ DAG.

-- ref: def_3_7 (item iii)
-- A CDMG `G = (J, V, E, L)` is an *ADMG* (Acyclic Directed Mixed
-- Graph) iff `G` is acyclic in the sense of `def_3_6` and `J = ∅`.
/-
LN tex (item iii of `def_3_7`):

  $G$ is called an ADMG iff $G$ is acyclic in the sense of
  def \ref{def-acylic} and $J = \emptyset$.
-/
-- ## Design choice
-- Literal two-conjunct `G.IsAcyclic ∧ G.J = ∅` in LN order (acyclic
-- first, `J = ∅` second).  See the shared design block above for the
-- choice of a plain `Prop` conjunction over a structure / typeclass /
-- `inductive` constructor, and for the rationale of preserving LN
-- conjunction order so that `obtain ⟨hac, hJ⟩ := h` reads back as
-- "acyclic and `J = ∅`".  ADMG is the workhorse hypothesis of
-- chapters 4–10: every CBN, do-calculus, d-separation, and iSCM
-- result in those chapters quantifies over `IsADMG` graphs, so a
-- one-line `unfold CDMG.IsADMG at h` (or `obtain` destructuring)
-- restores the two atomic conditions whenever a proof needs them.

-- ref: def_3_7 (item iv)
-- A CDMG `G = (J, V, E, L)` is a *CDG* (Conditional Directed Graph)
-- iff `L = ∅` (the bidirected-edge `Finset` is empty).
/-
LN tex (item iv of `def_3_7`):

  $G$ is called a CDG iff $L = \emptyset$.
-/
-- ## Design choice
-- Atomic single-condition predicate, an alias for the literal LN
-- equation `L = ∅` written as the `Finset (Node × Node)` equality
-- `G.L = ∅` on `def_3_1.L`.  Same rationale as `IsDMG` above (see
-- shared design block).  CDG is the no-bidirected-edge root of the
-- G-suffixed (Graph, "no Mixed" — no confounding) taxonomy branch
-- CDG ⊃ CDAG ⊃ DAG and CDG ⊃ DG ⊃ DAG.

-- ref: def_3_7 (item v)
-- A CDMG `G = (J, V, E, L)` is a *DG* (Directed Graph) iff
-- `J = ∅` and `L = ∅`.
/-
LN tex (item v of `def_3_7`):

  $G$ is called a DG iff $J = \emptyset$ and $L = \emptyset$.
-/
-- ## Design choice
-- Literal two-conjunct `G.J = ∅ ∧ G.L = ∅` in LN order (`J = ∅`
-- first, `L = ∅` second).  See the shared design block above for the
-- `Prop`-conjunction-in-LN-order rationale.  *Distinctive feature.*
-- Unlike `IsDAG` (item vii), `IsDG` does *not* require acyclicity —
-- the LN's "directed graph" vs.\ "directed acyclic graph" distinction
-- (items v vs.\ vii) makes a DG a graph with only ordinary directed
-- edges (no `J`, no bidirected `L`) but which may still contain
-- directed cycles.  A reader expecting "DG implies DAG" is wrong;
-- the implication only runs the other direction.

-- ref: def_3_7 (item vi)
-- A CDMG `G = (J, V, E, L)` is a *CDAG* (Conditional Directed Acyclic
-- Graph) iff `G` is acyclic in the sense of `def_3_6` and `L = ∅`.
/-
LN tex (item vi of `def_3_7`):

  $G$ is called a CDAG iff $G$ is acyclic in the sense of
  def \ref{def-acylic} and $L = \emptyset$.
-/
-- ## Design choice
-- Literal two-conjunct `G.IsAcyclic ∧ G.L = ∅` in LN order (acyclic
-- first, `L = ∅` second).  See the shared design block above.  CDAG
-- is the conditional analogue of `IsDAG`: input nodes (`J`) are
-- allowed, but bidirected edges (`L = ∅`) and cycles (acyclic) are
-- not.  Sits between `IsCDG` (drop the acyclicity conjunct) and
-- `IsDAG` (add `G.J = ∅` as a third conjunct).

-- ref: def_3_7 (item vii)
-- A CDMG `G = (J, V, E, L)` is a *DAG* (Directed Acyclic Graph) iff
-- `G` is acyclic in the sense of `def_3_6`, `J = ∅`, and `L = ∅`.
-- A DAG simultaneously satisfies every weaker conjunction above
-- (CADMG, DMG, ADMG, CDG, DG, CDAG) plus the base `CDMG` attribute.
/-
LN tex (item vii of `def_3_7`):

  $G$ is called a DAG iff $G$ is acyclic in the sense of
  def \ref{def-acylic}, $J = \emptyset$, and $L = \emptyset$.
-/
-- ## Design choice
-- Right-associated three-conjunct `G.IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅`
-- in LN order.  Lean's `∧` is right-associative, so this parses as
-- `G.IsAcyclic ∧ (G.J = ∅ ∧ G.L = ∅)` and `obtain ⟨hac, hJ, hL⟩ := h`
-- (anonymous-constructor chained destructuring) unpacks all three
-- atomic conditions in one move, mirroring the LN's "acyclic, `J =
-- ∅`, and `L = ∅`" enumeration.  See the shared design block above
-- for the broader `Prop`-conjunction-in-LN-order rationale.
-- *Distinctive feature.*  `IsDAG` is the strongest predicate in the
-- taxonomy: a `G : CDMG Node` with `G.IsDAG` simultaneously bears
-- every weaker name `IsCADMG`, `IsDMG`, `IsADMG`, `IsCDG`, `IsDG`,
-- `IsCDAG` plus the base `CDMG` attribute of `def_3_1` (so all 8 of
-- the 2³ truth-tuples are "≤" DAG in the implication ordering).  This
-- powers downstream consumption pattern "let `G` be a DAG, then …":
-- classical-SCM / Pearlian causality results in later chapters take a
-- single `(h : G.IsDAG)` hypothesis and dispatch every weaker named
-- attribute from `h` directly — no case split, no extra hypotheses.
-- *Anchoring for `claim_3_2`.*  The acyclic ⟺ topological-order
-- result (`claim_3_2`, `def_3_8`) reaches into `G.IsAcyclic` via the
-- first conjunct, so the LN-order choice (acyclic first) keeps the
-- topological-order proof's `obtain ⟨hac, _, _⟩` shape syntactically
-- aligned with the LN reading.

end CDMG

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim
--   from `def_3_1`'s refactor twin `CDMG` (`CDMG.lean`).
--   The typeclass is load-bearing for the same reasons it was in
--   the original `namespace CDMG` block above: (i) `G.J = ∅` and
--   `G.L = ∅` are `Finset` equalities (over `Finset Node` and
--   `Finset (Sym2 Node)` respectively — see the per-predicate
--   notes below for the L-type change) that decompose to per-
--   element decidable membership tests, and (ii) the refactor
--   twin's `G.IsAcyclic` (`Acyclicity.lean`) carries the
--   same `[DecidableEq Node]` requirement (its body's
--   `Walk` / `IsDirectedWalk` / `v ∈ G`
--   machinery all depend on it).  Dropping the typeclass would
--   make every predicate below fail to type-check.
--
-- *Three-dash `--- start helper` marker, not the two-dash
--   `-- start statement`.*  Same convention used above for the
--   original `namespace CDMG` block and across `CDMG.lean`,
--   `CDMGNotation.lean`, `Walks.lean`, `EdgeRelations.lean`,
--   `CDMGRestrictions.lean`, and `Acyclicity.lean`'s refactor
--   twin.  This `variable` line is statement-typing
--   infrastructure, not formalised LN content.
-- def_3_7 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_7 --- end helper

-- ## Shared design choices (refactor twin) — apply to all seven
-- predicates below
--
-- The design is a *structural port* of the original
-- `namespace CDMG` block (see lines ~69–154 above for the full
-- per-choice rationale): seven separate `Prop` predicates on
-- `CDMG Node`, one per LN item; `Is`-prefixed acronyms
-- in LN order; literal conjunctions of the LN's atomic
-- conditions in LN-stated order (acyclic first; `J = ∅` before
-- `L = ∅` where both appear); `def`, not `abbrev`, to preserve
-- the LN-named abstraction across downstream chapter-4+
-- consumption; `G.J = ∅` / `G.L = ∅` as the literal LN `Finset`
-- equality; reuse of the refactor twin `IsAcyclic`
-- (`Acyclicity.lean`'s `namespace CDMG`) verbatim where
-- the LN says "G is acyclic"; no `Decidable` instances exposed
-- here.  All of those choices carry over unchanged.
--
-- ## Refactor-specific notes (only the upstream-type shifts)
--
-- The `cdmg_typed_edges` refactor touches the upstream types
-- `def_3_1` (CDMG → CDMG, with `L : Finset (Sym2 Node)`
-- instead of `Finset (Node × Node)`, no `hL_symm` field, and the
-- `hL_irrefl` field rephrased via `¬ s.IsDiag` on `Sym2 Node`)
-- and `def_3_6` (`IsAcyclic` → `IsAcyclic`, built on
-- `def_3_4`'s typed `Walk` / `IsDirectedWalk` /
-- `length`).  For *this* row's seven predicates the only
-- shifts are:
--
--   * Type annotation `(G : CDMG Node) → (G : CDMG Node)`
--     on every predicate (all 7 / 7).
--   * `G.IsAcyclic → G.IsAcyclic` on the four predicates
--     that mention acyclicity (`IsCADMG`,
--     `IsADMG`, `IsCDAG`, `IsDAG`).
--   * The remaining three (`IsDMG`, `IsCDG`,
--     `IsDG`) port with only the type-annotation change.
--
-- *The `G.L = ∅` spelling is identical despite `L`'s type
-- change.*  In the original, `G.L : Finset (Node × Node)`; in
-- the refactor twin, `G.L : Finset (Sym2 Node)`.  In both cases
-- `∅` resolves via `EmptyCollection` to `Finset.empty` at the
-- relevant element type, so the literal text `G.L = ∅` reads
-- identically on either side of the refactor.  The four
-- predicates that touch `L` (`IsCDG`, `IsDG`,
-- `IsCDAG`, `IsDAG`) therefore have *no*
-- visible textual change to the `L = ∅` conjunct relative to
-- their originals — the entire shift is type-level, sitting on
-- the upstream `CDMG.L` field.
--
-- *Why the refactor's upstream changes don't open new
-- encodings here.*  The `cdmg_typed_edges` refactor's
-- substantive changes — `L : Finset (Sym2 Node)` instead of
-- `Finset (Node × Node)`, the dropped `hL_symm` axiom, the
-- `hL_irrefl` rephrasing via `¬ s.IsDiag`, and the typed
-- `WalkStep` / `Walk` /
-- `IsDirectedWalk` chain underpinning
-- `IsAcyclic` — all sit *beneath* the level at which
-- these seven predicates operate.  Each predicate only tests
-- (i) the *emptiness* of the `J` and / or `L` `Finset` carriers
-- (encoded identically across the L-type change via the
-- `EmptyCollection`-resolved `∅` literal — see the previous
-- paragraph) and (ii) the LN-meaning of
-- `CDMG.IsAcyclic`, which `Acyclicity.lean`'s
-- refactor-twin design block (`namespace CDMG`,
-- "Structural port of the original `IsAcyclic`") establishes
-- as the behavioural port of `CDMG.IsAcyclic` modulo the
-- upstream `Walk` retyping: the universal-quantifier
-- structure `∀ v ∈ G, ¬ ∃ p : Walk G v v, …` carries through
-- verbatim with `Walk` / `IsDirectedWalk` /
-- `length` substituted pointwise.  The seven
-- predicates therefore see no new design surface to consume:
-- none of them reaches into `L`'s carrier shape, the `hL_*`
-- field set, the typed-step constructors, or the inductive
-- structure of `Walk`.
--
-- *Mathematical design fully unchanged.*  No new alternative
-- formulations were considered.  Every per-predicate design
-- choice from the original block (nested-name semantics over an
-- enum, named-`def` over `abbrev` or inlined conjunction,
-- LN-order on conjuncts, `Is`-prefixed acronyms verbatim from
-- the LN, atomic-condition encoding via `Finset` equality and
-- via the chapter's own `IsAcyclic`) carries through
-- verbatim — no per-predicate encoding here would be *more
-- natural* against the new upstream than against the old.

-- ref: def_3_7 (item i) — refactor twin
-- A CDMG `G = (J, V, E, L)` is a *CADMG* (Conditional Acyclic
-- Directed Mixed Graph) iff `G` is acyclic in the sense of
-- `def_3_6`.
/-
LN tex (item i of `def_3_7`):

  $G$ is called a CADMG iff $G$ is acyclic in the sense of
  def \ref{def-acylic}.
-/
-- ## Design choice
-- Structural port of the original `IsCADMG` (see
-- `namespace CDMG` block above for the full rationale): atomic
-- single-condition predicate, an alias for `def_3_6`'s
-- acyclicity packaged under the LN's acronym `CADMG`.  Design
-- unchanged — same `def`-not-`abbrev` choice, same named-
-- abstraction rationale, same downstream-consumer payoff via
-- hard intervention (`def_3_10`).
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node       → CDMG Node`
--   `G.IsAcyclic     → G.IsAcyclic`
-- No other change.
-- def_3_7 -- start statement
def IsCADMG (G : CDMG Node) : Prop := G.IsAcyclic
-- def_3_7 -- end statement

-- ref: def_3_7 (item ii) — refactor twin
-- A CDMG `G = (J, V, E, L)` is a *DMG* (Directed Mixed Graph)
-- iff `J = ∅` (the input-node `Finset` is empty).
/-
LN tex (item ii of `def_3_7`):

  $G$ is called a DMG iff $J = \emptyset$.
-/
-- ## Design choice
-- Structural port of the original `IsDMG` (see
-- `namespace CDMG` block above for the full rationale): atomic
-- single-condition predicate, an alias for the literal LN
-- equation `J = ∅` written as the `Finset Node` equality on
-- `def_3_1`'s refactor twin's `J` field.  Design unchanged —
-- same `def`-not-`abbrev`, same "literal `Finset` equality over
-- cardinality / quantifier reformulations" rationale, same role
-- as the no-input-node root of the M-suffixed taxonomy branch
-- DMG ⊃ ADMG ⊃ DAG.
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node → CDMG Node`
-- The `G.J = ∅` spelling is unchanged: `J : Finset Node` on
-- both the original `CDMG` and on `CDMG` (the
-- `cdmg_typed_edges` refactor leaves the `J` field shape
-- untouched).
-- def_3_7 -- start statement
def IsDMG (G : CDMG Node) : Prop := G.J = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item iii) — refactor twin
-- A CDMG `G = (J, V, E, L)` is an *ADMG* (Acyclic Directed
-- Mixed Graph) iff `G` is acyclic in the sense of `def_3_6` and
-- `J = ∅`.
/-
LN tex (item iii of `def_3_7`):

  $G$ is called an ADMG iff $G$ is acyclic in the sense of
  def \ref{def-acylic} and $J = \emptyset$.
-/
-- ## Design choice
-- Structural port of the original `IsADMG` (see
-- `namespace CDMG` block above for the full rationale): literal
-- two-conjunct `G.IsAcyclic ∧ G.J = ∅` in LN order
-- (acyclic first, `J = ∅` second).  Design unchanged — same
-- LN-order-preserving rationale so that
-- `obtain ⟨hac, hJ⟩ := h` reads back as "acyclic and `J = ∅`",
-- same workhorse-hypothesis role for the chapter-4–10 CBN /
-- do-calculus / d-separation / iSCM results.
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node       → CDMG Node`
--   `G.IsAcyclic     → G.IsAcyclic`
-- The `G.J = ∅` conjunct ports unchanged at the spelling level.
-- def_3_7 -- start statement
def IsADMG (G : CDMG Node) : Prop := G.IsAcyclic ∧ G.J = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item iv) — refactor twin
-- A CDMG `G = (J, V, E, L)` is a *CDG* (Conditional Directed
-- Graph) iff `L = ∅` (the bidirected-edge `Finset` is empty).
/-
LN tex (item iv of `def_3_7`):

  $G$ is called a CDG iff $L = \emptyset$.
-/
-- ## Design choice
-- Structural port of the original `IsCDG` (see `namespace CDMG`
-- block above for the full rationale): atomic single-condition
-- predicate, an alias for the literal LN equation `L = ∅`
-- written as the empty-`Finset` equality on `def_3_1`'s
-- refactor twin's `L` field.  Design unchanged — same
-- `def`-not-`abbrev`, same role as the no-bidirected-edge root
-- of the G-suffixed taxonomy branch CDG ⊃ CDAG ⊃ DAG and
-- CDG ⊃ DG ⊃ DAG.
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node → CDMG Node`
-- The `G.L = ∅` spelling is *textually identical* to the
-- original even though the underlying type of `L` changed from
-- `Finset (Node × Node)` to `Finset (Sym2 Node)`: in both cases
-- `∅` resolves via `EmptyCollection` to `Finset.empty` at the
-- relevant element type, so the literal `G.L = ∅` reads the
-- same on either side of the refactor.
-- def_3_7 -- start statement
def IsCDG (G : CDMG Node) : Prop := G.L = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item v) — refactor twin
-- A CDMG `G = (J, V, E, L)` is a *DG* (Directed Graph) iff
-- `J = ∅` and `L = ∅`.
/-
LN tex (item v of `def_3_7`):

  $G$ is called a DG iff $J = \emptyset$ and $L = \emptyset$.
-/
-- ## Design choice
-- Structural port of the original `IsDG` (see `namespace CDMG`
-- block above for the full rationale): literal two-conjunct
-- `G.J = ∅ ∧ G.L = ∅` in LN order (`J = ∅` first, `L = ∅`
-- second).  Design unchanged — same `Prop`-conjunction-in-LN-
-- order rationale, same distinctive-feature note that `IsDG`
-- does *not* require acyclicity (a DG may still contain
-- directed cycles), so the implication only runs from `IsDAG`
-- to `IsDG`, not the other direction.
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node → CDMG Node`
-- Both `G.J = ∅` and `G.L = ∅` port unchanged at the spelling
-- level: `J : Finset Node` on both sides of the refactor, and
-- `G.L = ∅` reads identically even though the underlying type
-- of `L` changed from `Finset (Node × Node)` to
-- `Finset (Sym2 Node)` (`∅` resolves via `EmptyCollection` at
-- whichever element type).
-- def_3_7 -- start statement
def IsDG (G : CDMG Node) : Prop := G.J = ∅ ∧ G.L = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item vi) — refactor twin
-- A CDMG `G = (J, V, E, L)` is a *CDAG* (Conditional Directed
-- Acyclic Graph) iff `G` is acyclic in the sense of `def_3_6`
-- and `L = ∅`.
/-
LN tex (item vi of `def_3_7`):

  $G$ is called a CDAG iff $G$ is acyclic in the sense of
  def \ref{def-acylic} and $L = \emptyset$.
-/
-- ## Design choice
-- Structural port of the original `IsCDAG` (see
-- `namespace CDMG` block above for the full rationale): literal
-- two-conjunct `G.IsAcyclic ∧ G.L = ∅` in LN order
-- (acyclic first, `L = ∅` second).  Design unchanged — same
-- conditional-analogue-of-`IsDAG` role, sitting between
-- `IsCDG` (drop the acyclicity conjunct) and
-- `IsDAG` (add `G.J = ∅` as a third conjunct).
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node       → CDMG Node`
--   `G.IsAcyclic     → G.IsAcyclic`
-- The `G.L = ∅` conjunct ports unchanged at the spelling level
-- despite `L`'s type changing from `Finset (Node × Node)` to
-- `Finset (Sym2 Node)` — `∅` resolves via `EmptyCollection` at
-- whichever element type.
-- def_3_7 -- start statement
def IsCDAG (G : CDMG Node) : Prop := G.IsAcyclic ∧ G.L = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item vii) — refactor twin
-- A CDMG `G = (J, V, E, L)` is a *DAG* (Directed Acyclic Graph)
-- iff `G` is acyclic in the sense of `def_3_6`, `J = ∅`, and
-- `L = ∅`.  A DAG simultaneously satisfies every weaker
-- conjunction above (CADMG, DMG, ADMG, CDG, DG, CDAG) plus the
-- base `CDMG` attribute.
/-
LN tex (item vii of `def_3_7`):

  $G$ is called a DAG iff $G$ is acyclic in the sense of
  def \ref{def-acylic}, $J = \emptyset$, and $L = \emptyset$.
-/
-- ## Design choice
-- Structural port of the original `IsDAG` (see `namespace CDMG`
-- block above for the full rationale): right-associated three-
-- conjunct `G.IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅` in LN
-- order.  Design unchanged — same right-associative parse via
-- Lean's `∧`-associativity giving
-- `G.IsAcyclic ∧ (G.J = ∅ ∧ G.L = ∅)` and
-- `obtain ⟨hac, hJ, hL⟩ := h` chained destructuring, same
-- distinctive-feature role as the strongest predicate in the
-- taxonomy (bears every weaker name), same anchoring for
-- `claim_3_2` (acyclic ⟺ topological order) via the
-- LN-order-preserving "acyclic first" choice.
--
-- Upstream-type shifts that apply to this predicate:
--   `CDMG Node       → CDMG Node`
--   `G.IsAcyclic     → G.IsAcyclic`
-- Both `G.J = ∅` and `G.L = ∅` conjuncts port unchanged at the
-- spelling level: `J : Finset Node` on both sides, and the
-- `G.L = ∅` text reads identically across the `L`-type change
-- from `Finset (Node × Node)` to `Finset (Sym2 Node)` for the
-- same `EmptyCollection`-resolution reason noted on
-- `IsCDG` above.
-- def_3_7 -- start statement
def IsDAG (G : CDMG Node) : Prop := G.IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅
-- def_3_7 -- end statement

end CDMG

end Causality
