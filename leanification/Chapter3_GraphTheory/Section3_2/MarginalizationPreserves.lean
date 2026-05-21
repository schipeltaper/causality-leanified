import Chapter3_GraphTheory.Section3_2.Marginalization
import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder

-- TeX statement: tex/claim_3_16_statement_MarginalizationPreserves.tex
-- TeX proof:    tex/claim_3_16_proof_MarginalizationPreserves.tex (to be written)

/-!
# Marginalization preserves ancestral relations, bifurcations, acyclicity (claim_3_16)

This file formalises the lecture notes' remark
`rem:marg_preserves_ancestors_bifurcations_acyclicity`
(`lecture-notes/lecture_notes/graphs.tex` around line 964, the
`\begin{Rem}\label{rem:marg_preserves_ancestors_bifurcations_acyclicity}`
claimmark) for a CDMG `G = (J, V, E, L)` and a set `W ⊆ α` of output
nodes. The remark bundles *three* structural preservation properties
of marginalization (def_3_14, `Section3_2/Marginalization.lean`):

1. **Ancestors** -- for `v_1, v_2 ∉ W`,
   `v_1 ∈ Anc^G(v_2)  ↔  v_1 ∈ Anc^{G^{\sm W}}(v_2)`.
2. **Bifurcations** -- for `v_1, v_2 ∈ G \ W` (and, optionally, a
   third `v_3 ∈ G \ W` named as the *source*), there is a bifurcation
   between `v_1` and `v_2` (with source `v_3`) in `G` iff there is one
   in `G^{\sm W}`. The LN's "between" reading is symmetric, which we
   carry through to Lean via the disjunction-of-both-walk-directions
   reading (see the `Marginalization.lean` design block on
   `mem_marginalize_L` and risk §5.2 of
   `workspace_claim_3_16.md`).
3. **Acyclicity and topological orders** -- if `G` is acyclic, so is
   `G^{\sm W}`; and any topological order of `G` is a topological
   order of `G^{\sm W}` (by just ignoring the nodes from `W`).

## Scope of this file (formalize-phase, statements only)

This file currently holds **four** theorems, each with `:= sorry` for
the proof body. Item 2 is split into a *no-source* variant (here) and
a *with-source* variant (deferred to a follow-up dispatch, see risk
§5.2 in `workspace_claim_3_16.md`):

* `marginalize_anc_iff`            — item 1.
* `marginalize_bifurcation_iff`    — item 2 (no source).
* `marginalize_isAcyclic`          — item 3a (acyclicity).
* `marginalize_isTopologicalOrder` — item 3b (topological order).

The with-source variant (`marginalize_bifurcation_source_iff`) is
intentionally absent: the `L^{\sm W}` exclusion clause in
`mem_marginalize_L` can turn a bidir-hinge bifurcation in `G`
(no source) into a backward-hinge bifurcation in `G^{\sm W}` (with
source), which complicates the LN's "(with source `v_3`)"
preservation in subtle ways. We defer the with-source statement until
the no-source proof has surfaced the exclusion-clause friction
concretely. See risk §5.2 in `workspace_claim_3_16.md` for the
recommended mitigation candidates (R1–R3).

## Why we do *not* introduce `Walk.IsBifurcationWithSource` here

The workspace plan §1 calls for a helper predicate
`Walk.IsBifurcationWithSource π v₃` to support the with-source
biconditional cleanly (avoiding the `Classical.choice` fragility of
`bifurcationSource`). That helper most naturally lives in
`Section3_1/Bifurcation.lean` alongside `Walk.IsBifurcation` and
`Walk.bifurcationSource`. Adding it touches a different subsection,
which `claude.md` rule 4 reserves for manager approval. Since we are
also deferring theorem 3 to a follow-up dispatch, we punt the helper
to that dispatch too: it is the natural place to ask the manager
whether to land the helper in `Bifurcation.lean` (cleaner long-term,
since claim_3_17 / 3_18 / 3_19 will likely want it) or to define it
locally in the with-source theorem's file. Flagged in the formalizer's
report-back.

## Why the LN remark is split into four Lean theorems

A single bundled `Prop` ("all three preservation properties hold")
would force every consumer to destructure or to chain irrelevant
hypotheses (e.g. the topological-order half quoted by chapter 5's
do-calculus has no need for the bifurcation conjunct). We split:

* by sub-item, because downstream consumers cite different parts
  separately (claim_3_17 quotes items 1 + 2; claim_3_18 / 3_19 and
  chapter 4 quote item 3a; chapter 5 quotes item 3b);
* within item 2, into no-source / with-source variants because the
  with-source refinement interacts non-trivially with the
  `L^{\sm W}`-exclusion (risk §5.2) while the no-source variant
  absorbs the exclusion cleanly via the symmetric-`∨` reading of
  bifurcation existence;
* within item 3, into acyclicity / topological order because the two
  are logically independent — item 3a is provable directly by walk
  concatenation without going through claim_3_2 (avoiding a
  circular-feeling dependency), and item 3b carries the *same*
  relation `r` rather than re-extracting an order via classical
  choice. Downstream callers genuinely want them separately
  (claim_3_17 / chapter 4 want acyclicity preservation without a
  named order; chapter 5 wants the order itself).

## Naming convention: `marginalize_*` prefix throughout

All four theorems use the `marginalize_*` prefix, *deviating* from
the project's `<conclusion>_<construction>` convention used by the
sibling rows (e.g. `isAcyclic_nodeSplittingOn`,
`isTopologicalOrder_nodeSplittingOn`,
`isAcyclic_extendingCDMGWithInterventionNodes`). The deviation is
deliberate and local: this file studies a *single operation* —
marginalization — and the four theorems are unified by what they
study, not by the conclusion each draws. A shared prefix groups
them visually and matches `Marginalization.lean`'s own projection
names (`marginalize_J`, `marginalize_V`, `mem_marginalize_E`,
`mem_marginalize_L`), so the dot-notation reading
`G.marginalize_isAcyclic W h` parallels `G.marginalize_J W` at call
sites in this section. Each theorem's per-block comment carries the
individual name's local justification.

## Where this gets used downstream

The four theorems below are the entry-level membership-level
preservation results that the next three rows in Section 3.2 build
on, and chapters 4 – 16 quote via latent-projection arguments:

* **claim_3_17** (`graphs.tex` Lem 997, "Marginalizations commute")
  — items 1 + 2 are quoted directly to assemble / disassemble
  iterated marginalizations.
* **claim_3_18 / claim_3_19** — items 1 + 3a underpin the
  intervention-commute and SWIG-marginalization equivalences.
* **`lem:stability_separation_marginalization`** (`graphs.tex` line
  1416, Section 3.3) — item 2 (no source) is the bifurcation-level
  invariance that yields `iσ`-separation stability under
  marginalization; item 1 the ancestor-level invariance.
* **Chapters 4 – 16** — every latent-projection argument in CBNs,
  do-calculus, iSCMs, FCI / ICDF rests on items 1 and 3.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

-- claim_3_16 (part 1/4) -- item 1 of the LN remark
-- title: MarginalizationPreserves -- ancestral relations
--
-- For `v_1, v_2 ∉ W`, `v_1` is an ancestor of `v_2` in `G` iff `v_1`
-- is an ancestor of `v_2` in the marginalization `G^{\sm W}`.
-- Direct biconditional translation of LN item 1; both directions are
-- routed through a walk translator that uses `mem_marginalize_E` to
-- shrink a directed walk through `W` in `G` to a single edge in
-- `G^{\sm W}` (and conversely expand a directed edge of `G^{\sm W}`
-- back to a directed walk in `G` whose intermediate vertices lie in
-- `W`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 1:

  For $v_1,v_2 \in G$ with $v_1,v_2 \notin W$ we have the equivalence:
    $v_1 \in \Anc^G(v_2)\quad \iff \quad v_1 \in \Anc^{G^{\sm W}}(v_2).$
-/
--
-- ## Design choice
--
-- * **Plain English statement.** The set of ancestors of `v_2` (in
--   the `Anc^G` sense — directed-walk reachable) is preserved by
--   marginalization on vertices outside `W`. Equivalently, for any
--   target `v_2 ∉ W`, the marginalization preserves which `v_1 ∉ W`
--   reach `v_2` along a directed walk.
--
-- * **Preconditions `v_i ∉ W` only, no explicit `v_i ∈ G`.** The LN
--   writes "$v_1, v_2 \in G$ with $v_1, v_2 \notin W$" — the
--   `v_1 \in G` precondition is implicit in the LHS `v_1 ∈ Anc^G(v_2)`
--   (the `Anc` def in `Section3_1/FamilyReachability.lean` line 119
--   carries a `w ∈ G` clause as the first conjunct of its
--   set-builder), so we do not repeat it. The `v_2 ∈ G` precondition
--   is not strictly needed either: if `v_2 ∉ G`, both sides degenerate
--   in the same way (length-`≥ 1` directed walks force their
--   endpoints into `G.V ⊆ G` via `G.E_subset`; the length-`0` case
--   only fires when `v_1 = v_2`, in which case the `Anc` membership
--   on each side reduces to `v_2 ∈ G` resp.
--   `v_2 ∈ G.marginalize W`, and `v_2 ∉ W` plus `v_2 ∈ G ↔ v_2 ∈
--   G.marginalize W` make the biconditional discharge cleanly). We
--   accept the very mild discrepancy with the LN's literal preamble
--   for the simpler statement; see also risk §5.4 in
--   `workspace_claim_3_16.md`.
--
-- * **`v_i ∉ W` rather than `v_i ∈ G.marginalize W`.** These are not
--   equivalent in the presence of `W ∩ G.J ≠ ∅`: an input node
--   `v ∈ G.J ∩ W` belongs to `G` (via `G.J ⊆ G`) and also to
--   `G.marginalize W` (since `G.marginalize W` has the *same* `J`,
--   see `marginalize_J`), so `v ∈ G.marginalize W` is a *weaker*
--   precondition than `v ∉ W`. The LN says "$v_1, v_2 \notin W$",
--   not "$v_1, v_2 \in G \sm W$", so we stay literal. See risk §5.4
--   in `workspace_claim_3_16.md` and the `Marginalization.lean`
--   no-precondition design block for why `G.marginalize` admits any
--   `W : Set α` (and the LN's set-relative reading is at the use
--   site, not at the operator definition).
--
-- * **Why an `iff` and not two separate `_of_` lemmas.** Both
--   directions are needed by claim_3_17 (in opposite directions on
--   different sides of its commute equality), and the LN states it
--   as an equivalence. Bundling as `↔` matches the LN and keeps the
--   single-citation form simple.
--
-- * **Naming `marginalize_anc_iff`.** Follows the project's
--   `<construction>_<preserved property>_iff` convention for
--   biconditional preservation results; mirrors the soon-to-be-named
--   `marginalize_bifurcation_iff` (item 2), `marginalize_isAcyclic`
--   (item 3a), `marginalize_isTopologicalOrder` (item 3b).

/-- claim_3_16 part 1/4 (LN remark item 1): for any CDMG `G` and any
set `W`, marginalization preserves ancestral relations on vertices
outside `W`. For `v₁, v₂ ∉ W`, `v₁` is an ancestor of `v₂` in `G` iff
`v₁` is an ancestor of `v₂` in the marginalization `G.marginalize W`.

The implicit `v₁ ∈ G` precondition of the LN's "$v_1, v_2 \in G$"
preamble is already carried by the `mem_Anc` membership on each side
(both `G.Anc v₂` and `(G.marginalize W).Anc v₂` are set-builders
guarded by `_ ∈ G` resp. `_ ∈ G.marginalize W`); the explicit
`v_i ∉ W` hypotheses bridge the two memberships. The proof (to be
filled in by `prove_claim_in_lean`) shuttles a directed walk through
`W` in `G` to / from a single directed edge in `G^{\sm W}` via
`mem_marginalize_E`. -/
theorem marginalize_anc_iff (G : CDMG α) (W : Set α) {v₁ v₂ : α}
    (h₁ : v₁ ∉ W) (h₂ : v₂ ∉ W) :
    v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W).Anc v₂ := sorry

-- claim_3_16 (part 2/4) -- item 2 of the LN remark (no source)
-- title: MarginalizationPreserves -- bifurcations
--
-- For `v_1, v_2 ∈ G \ W`, there is a bifurcation between `v_1` and
-- `v_2` in `G` iff there is a bifurcation between them in
-- `G^{\sm W}`. The LN's "between" is symmetric in the two endpoints;
-- we encode that symmetry as `(∃ π : Walk … v₁ v₂, …) ∨ (∃ π : Walk
-- … v₂ v₁, …)` on both sides of the iff. The with-source variant
-- ("with source `v_3`") is *deliberately deferred* to a follow-up
-- dispatch — see the file docstring's "Scope of this file" section
-- and risk §5.2 in `workspace_claim_3_16.md`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 2
(no-source half; the parenthetical "(with source $v_3$)" half is the
deferred variant):

  For $v_1,v_2 \in G \sm W$ (and, optionally, $v_3 \in G\sm W$):
  there is a bifurcation between $v_1$ and $v_2$ (with source $v_3$)
  in $G$ if and only if there is a bifurcation between $v_1$ and
  $v_2$ (with source $v_3$) in $G^{\sm W}$.
-/
--
-- ## Design choice
--
-- * **Plain English statement.** The existence of a bifurcation
--   between two vertices `v_1, v_2 ∈ G \ W` is invariant under
--   marginalization: a bifurcation in `G` whose intermediate
--   vertices are absorbed into `W`-shortcuts becomes a bifurcation
--   in `G^{\sm W}` (and vice versa).
--
-- * **Symmetric `∨` reading of "between".** The LN's word "between"
--   is symmetric in `v_1, v_2`, but a `Walk G v w` is *directional*
--   (start at `v`, end at `w`). The clean Lean encoding of "there
--   exists a bifurcation between `v_1` and `v_2`" is therefore the
--   disjunction
--     `(∃ π : Walk G v₁ v₂, π.IsBifurcation) ∨
--      (∃ π : Walk G v₂ v₁, π.IsBifurcation)`,
--   which is what we use on both sides of the iff. Note this is
--   *not* equivalent to a single direction-quantified existential
--   because `Walk.IsBifurcation` is *not* symmetric across reversal
--   in our encoding (the witness's `leftArm`/`rightArm` split is
--   direction-aware). See the long design block in
--   `Section3_2/Marginalization.lean` (around the `disjoint_EL` and
--   `mem_marginalize_L` definitions) for the same symmetric-`∨`
--   convention applied to the `L^{\sm W}` membership; this row is
--   the first downstream consumer.
--
-- * **Why splitting "no source" and "with source" matters.** The
--   `L^{\sm W}` *exclusion clause* in `mem_marginalize_L`
--   (`Section3_2/Marginalization.lean` line 597) removes pairs that
--   are already in `E^{\sm W}` in either direction (a Lean-encoding
--   deviation, justified by the design block on `disjoint_EL` in
--   `Marginalization.lean`). When this exclusion fires on a bidir
--   hinge of a bifurcation in `G`, the absorbing shortcut edge is
--   directed in `G^{\sm W}` — so the resulting bifurcation in
--   `G^{\sm W}` is forced to use a `.backward` hinge in the
--   *opposite* walk direction, introducing a *source* where the LN
--   bifurcation had none. The no-source biconditional absorbs this
--   cleanly via the symmetric-`∨` reading (the reverse-direction
--   bifurcation lives in the second disjunct). The with-source
--   biconditional does not absorb it cleanly: an LHS no-source
--   bifurcation in `G` would relate to an RHS *with-source* `v_3`
--   bifurcation in `G^{\sm W}`, which is not what
--   `IsBifurcationWithSource v_3` reads as on both sides. Risk §5.2
--   in `workspace_claim_3_16.md` discusses three mitigation
--   candidates; we defer the with-source theorem until the no-source
--   proof has surfaced the exclusion-clause friction concretely.
--
-- * **Preconditions `v_i ∈ G ∧ v_i ∉ W`, four hypotheses.** The LN
--   writes "$v_1, v_2 \in G \sm W$" which unfolds to `v_i ∈ G ∧
--   v_i ∉ W` for both `i`. The asymmetry with `marginalize_anc_iff`
--   (which carries only `v_i ∉ W`) is one of *literal-LN adherence*,
--   not of mathematical content: for `Anc`, the set-builder
--   `Anc^G(v_2) = {w | w ∈ G ∧ ...}` (`Section3_1/FamilyReachability.lean`
--   line 119) embeds `v_1 ∈ G` *syntactically* into the LHS
--   membership, so the LN's "v_1 ∈ G" preamble is redundant with
--   the iff's LHS and we drop it. For `IsBifurcation` the analogous
--   `v_i ∈ G` is *derivable* (the predicate forces `v_1 ≠ v_2` and
--   thus at least one edge, whose endpoints lie in `G.V ⊆ G` via
--   `G.E_subset`) but not embedded in the existential's syntactic
--   shape, so we hoist the LN's preamble into explicit hypotheses
--   here to keep the statement literal. See risk §5.4 in
--   `workspace_claim_3_16.md` for the precondition shape discussion
--   (and why we use `v_i ∈ G ∧ v_i ∉ W` rather than
--   `v_i ∈ G.marginalize W` — the latter would be a *weaker*
--   hypothesis when `W ∩ G.J ≠ ∅`, because `G.J ⊆ G.marginalize W`
--   is preserved by `marginalize_J`).
--
-- * **No `v_1 ≠ v_2` hypothesis added.** `IsBifurcation` already
--   includes `v ≠ w` as its first conjunct (`Section3_1/Bifurcation.lean`
--   line 309), so each existential side of the iff implicitly forces
--   `v_1 ≠ v_2` when nonempty. Adding it as a hypothesis would
--   duplicate that constraint without changing the truth value of
--   the iff (the `v_1 = v_2` case has both sides false).
--
-- * **Naming `marginalize_bifurcation_iff`.** The no-source default
--   takes the unadorned name (matches the LN's flat sentence "there
--   is a bifurcation between `v_1` and `v_2`"); the with-source
--   variant — once added — will be named
--   `marginalize_bifurcation_source_iff` to mirror the LN's
--   parenthetical refinement.

/-- claim_3_16 part 2/4 (LN remark item 2, no-source half): for any
CDMG `G` and any set `W`, marginalization preserves the existence of
bifurcations between two vertices `v₁, v₂ ∈ G \ W`. The LN's "between"
is read symmetrically in `v₁, v₂` and encoded as a disjunction over
the two walk directions; the disjunction shape is also what makes the
biconditional handle the `L^{\sm W}` exclusion clause cleanly (a bidir
hinge in `G` absorbed by the exclusion still gives a `.backward`-hinge
bifurcation in `G^{\sm W}` *in the opposite walk direction*).

The with-source variant ("with source `v_3`") is intentionally
*deferred* to a follow-up dispatch — see the file docstring and risk
§5.2 in `workspace_claim_3_16.md`. The proof (to be filled in by
`prove_claim_in_lean`) shuttles a bifurcation's arms and hinge through
`W` via `mem_marginalize_E` (for the directed arms) and
`mem_marginalize_L` (for the bidir hinge), with the symmetric `∨`
absorbing the exclusion-clause case-split. -/
theorem marginalize_bifurcation_iff (G : CDMG α) (W : Set α)
    {v₁ v₂ : α} (h₁v : v₁ ∈ G) (h₂v : v₂ ∈ G)
    (h₁W : v₁ ∉ W) (h₂W : v₂ ∉ W) :
    ((∃ π : Walk G v₁ v₂, π.IsBifurcation) ∨
     (∃ π : Walk G v₂ v₁, π.IsBifurcation)) ↔
    ((∃ π : Walk (G.marginalize W) v₁ v₂, π.IsBifurcation) ∨
     (∃ π : Walk (G.marginalize W) v₂ v₁, π.IsBifurcation)) := sorry

-- claim_3_16 (part 3/4) -- item 3a of the LN remark (acyclicity)
-- title: MarginalizationPreserves -- acyclicity
--
-- If `G` is acyclic, so is `G^{\sm W}`. Direct walk-concatenation
-- argument: a non-trivial directed cycle in `G^{\sm W}` expands
-- (via `mem_marginalize_E` step-by-step) to a non-trivial directed
-- cycle in `G`, contradicting `G.IsAcyclic`. No claim_3_2 dependency.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 3
(acyclicity half; the topological-order half is item 3b below):

  If the CDMG $G$ is acyclic then so is $G^{\sm W}$ and a topological
  order of $G$ induces a topological order on $G^{\sm W}$ (by just
  ignoring the nodes from $W$).
-/
--
-- ## Design choice
--
-- * **Plain English statement.** Marginalization cannot manufacture
--   a directed cycle out of an acyclic graph: every edge of
--   `G^{\sm W}` represents a directed walk through `W` in `G`, so a
--   cycle in `G^{\sm W}` expands to a cycle in `G`. Acyclicity is
--   therefore preserved.
--
-- * **Split from item 3b (topological order).** Item 3a and item 3b
--   are logically independent: 3a is provable directly by walk
--   concatenation through `mem_marginalize_E` (the existential
--   directed-walk shortcut characterization), without invoking
--   claim_3_2's "acyclic iff has topological order" equivalence.
--   Splitting them avoids the (apparent) circular dependency feel
--   "3a follows from 3b via claim_3_2"; it also matches downstream
--   needs (claim_3_17, chapter 4 want preservation of acyclicity
--   without a specific named topological order, and would otherwise
--   have to invent one just to invoke item 3b). Mirrors the
--   precedent in `SwigAcyclicTopologicalOrder.lean` (claim_3_9) and
--   `AcyclicityUnderInterventionNodes.lean` (claim_3_13), both of
--   which split their LN `\Rem` block into two theorems for the same
--   reason.
--
-- * **No vertex-membership precondition.** `IsAcyclic` is itself a
--   `∀ v ∈ G, …` statement, so there is no specific vertex hypothesis
--   needed at the outer level. The proof case-splits on a
--   hypothetical cycle vertex `v ∈ G.marginalize W` (which yields
--   `v ∈ G` via `marginalize_J` / `marginalize_V` plus `mem_iff`).
--
-- * **No `W ⊆ G.V` precondition.** `marginalize` is well-defined for
--   *every* `W : Set α` (see the no-precondition design block in
--   `Marginalization.lean` and the iteration-clean rationale in its
--   docstring). The acyclicity preservation does not need `W ⊆ G.V`
--   either — the argument is structural on walks and the `\ W`
--   restriction handles overshoot.
--
-- * **Naming `marginalize_isAcyclic`.** Mirrors
--   `isAcyclic_hardInterventionOn` (claim_3_3 part A),
--   `isAcyclic_nodeSplittingOn` (claim_3_6 part B),
--   `isAcyclic_nodeSplittingHardInterventionOn` (claim_3_9 part B),
--   `isAcyclic_extendingCDMGWithInterventionNodes` (claim_3_13 part A),
--   following Mathlib's `<conclusion>_<construction>` convention.
--   We use `marginalize_isAcyclic` here (rather than
--   `isAcyclic_marginalize`) to keep the prefix matching the other
--   `marginalize_*` lemmas in this row — same flip as `marginalize_J`
--   / `marginalize_V` / `mem_marginalize_E` / `mem_marginalize_L`
--   in `Marginalization.lean`. The dot-notation reading
--   `G.marginalize_isAcyclic W h` then parallels
--   `G.marginalize_J W` / etc.

/-- claim_3_16 part 3/4 (LN remark item 3a): for any CDMG `G` and any
set `W`, if `G` is acyclic then so is the marginalization
`G.marginalize W`.

The mathematical content is that every directed edge of `G.marginalize
W` shortcuts a length-`≥ 1` directed walk through `W` in `G` (by
`mem_marginalize_E`), so a non-trivial directed cycle in
`G.marginalize W` expands to a non-trivial directed cycle in `G`,
contradicting `G.IsAcyclic`. This route is independent of claim_3_2
(no topological-order extraction); the topological-order
preservation half is the sibling theorem
`marginalize_isTopologicalOrder` below.

The proof will be filled in by `prove_claim_in_lean`; this dispatch
covers the statement only. -/
theorem marginalize_isAcyclic (G : CDMG α) (W : Set α)
    (h : G.IsAcyclic) : (G.marginalize W).IsAcyclic := sorry

-- claim_3_16 (part 4/4) -- item 3b of the LN remark (topological order)
-- title: MarginalizationPreserves -- topological order
--
-- A topological order `r` of `G` is also a topological order of
-- `G^{\sm W}`. The LN's "induces a topological order on `G^{\sm W}`
-- (by just ignoring the nodes from `W`)" reads as "same relation
-- `r`, restricted to the smaller vertex set `G^{\sm W}`". Each of
-- the four `IsTopologicalOrder` fields lifts: `irrefl`, `trans`,
-- `trichotomous` use that `v ∈ G.marginalize W ⇒ v ∈ G` (since
-- `marginalize_J` keeps `G.J` and `marginalize_V` restricts to
-- `G.V \ W ⊆ G.V`); `parent_lt` chains `r` along the directed walk
-- through `W` underlying each `G.marginalize W` edge.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 3
(topological-order half; same block as item 3a):

  If the CDMG $G$ is acyclic then so is $G^{\sm W}$ and a topological
  order of $G$ induces a topological order on $G^{\sm W}$ (by just
  ignoring the nodes from $W$).
-/
--
-- ## Design choice
--
-- * **Plain English statement.** Marginalization does not require
--   re-sorting: the *same* total-order relation `r` (a parameter,
--   not bundled into a structure) that linearises the vertices of
--   `G` still linearises the vertices of `G^{\sm W}`. The LN's
--   prose "by just ignoring the nodes from `W`" is captured by the
--   fact that `IsTopologicalOrder` quantifies its fields over
--   `v ∈ G.marginalize W` — a strict subset of `v ∈ G` (modulo `G.J
--   ∩ W` overlap; see the `mem_iff` / `marginalize_J` / `marginalize_V`
--   interplay below), so the `r`-axioms on the smaller domain follow
--   from the `r`-axioms on the larger domain by restriction.
--
-- * **Why a fresh theorem and not a corollary of item 3a + claim_3_2.**
--   Item 3a + claim_3_2's `→` direction would give us
--   *some* topological order of `G^{\sm W}`, but the LN explicitly
--   says "*a topological order* of `G` *induces* a topological order
--   on `G^{\sm W}`" — same relation, no re-extraction. Mirroring the
--   LN's constructive content with the same `r` carrying through
--   matches downstream uses (chapter 5 do-calculus picks a
--   topological order once and re-uses it under marginalization;
--   re-extracting via claim_3_2 would force a `Classical.choice`).
--
-- * **`r : α → α → Prop` implicit, `hr` explicit.** Same binder
--   convention as `isTopologicalOrder_nodeSplittingOn` (claim_3_6
--   part A), `isTopologicalOrder_nodeSplittingHardInterventionOn`
--   (claim_3_9 part A), `isTopologicalOrder_extendingCDMGWithInterv
--   entionNodes_extend` (claim_3_13). `r` is implicit because it is
--   unifiable from `hr` (and from the conclusion); `hr` is explicit
--   because it is the mathematical hypothesis under transport.
--
-- * **No `W ⊆ G.V` precondition.** Same as item 3a:
--   `marginalize` accepts any `W : Set α`, and the topological-order
--   preservation argument does not need overlap to be ruled out.
--
-- * **No `[Finite α]` instance hypothesis.** The argument is
--   purely relational (per-field transport on `r`); finiteness does
--   not enter. Mirrors `isTopologicalOrder_nodeSplittingOn` and the
--   other `isTopologicalOrder_*` precedents.
--
-- * **`marginalize_isTopologicalOrder` naming.** Same `marginalize_*`
--   prefix as the rest of this row, paralleling `marginalize_J` /
--   `marginalize_V` / `marginalize_isAcyclic`. The flip from the
--   sibling-row convention `isTopologicalOrder_<construction>`
--   (claim_3_6 / claim_3_9 / claim_3_13) is a local cosmetic choice
--   to keep this row's four theorems prefix-aligned and to read as
--   `G.marginalize_isTopologicalOrder W hr` at the call site —
--   matching how the file's other `marginalize_*` lemmas are quoted.

/-- claim_3_16 part 4/4 (LN remark item 3b): for any CDMG `G` and any
set `W`, a topological order `r` of `G` is also a topological order of
the marginalization `G.marginalize W`. The same relation `r` carries
through — the LN's "by just ignoring the nodes from `W`" — because
`IsTopologicalOrder` quantifies its fields over the (smaller) vertex
set of `G.marginalize W`.

The four `IsTopologicalOrder` fields (irreflexivity, transitivity,
trichotomy, parent-precedence) all reduce field-by-field to the
corresponding statement on `G`: the first three by restriction along
`v ∈ G.marginalize W → v ∈ G`, the fourth by chaining `r` along the
directed walk through `W` that underlies each `G.marginalize W` edge
(via `mem_marginalize_E`). See `marginalize_isAcyclic` above for the
acyclicity preservation half of the LN remark.

The proof will be filled in by `prove_claim_in_lean`; this dispatch
covers the statement only. -/
theorem marginalize_isTopologicalOrder (G : CDMG α) (W : Set α)
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    (G.marginalize W).IsTopologicalOrder r := sorry

end CDMG

end Causality
