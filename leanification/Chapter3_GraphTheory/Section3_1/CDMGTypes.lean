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
