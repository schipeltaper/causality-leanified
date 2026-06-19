import Chapter3_GraphTheory.Section3_2.Marginalization
import Chapter3_GraphTheory.Section3_3.ISigmaSeparation
import Chapter3_GraphTheory.Section3_3.SigmaBlockedReversal
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

-- TeX statement: claim_3_25_statement_ISigmaSeparation.tex
-- TeX proof:     claim_3_25_proof_ISigmaSeparation.tex

/-!
# $i\sigma$-separation under marginalization (claim_3_25)

This file formalises *claim 3.25* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1414 -- 1423, label `lem:stability_separation_marginalization`):
the central *stability* lemma of section 3.3 -- marginalising
out a set $D \subseteq V$ of output nodes disjoint from
$A \cup B \cup C$ leaves the $i\sigma$-separation
$A \isPerp_G B \given C$ unchanged. The LN block reads:

> Let $G = (J, V, E, L)$ be a CDMG, $A, B, C \subseteq J \cup V$
> and $D \subseteq V$ subsets of nodes such that
> $D \cap (A \cup B \cup C) = \emptyset$. Then we have the
> equivalence:
>   $A \isPerp_G B \given C \iff A \isPerp_{G^{\sm D}} B
>   \given C$.

The LN intermixes the *statement* (the `\iff`) with a complete
proof in a `\Claude{...}` wrapper at `graphs.tex` lines
1424 -- 1579. This file formalises **the statement only**; the
proof body is `sorry`. The proof is the future Manager-B
prover's job, and follows the LN: reduce to the single-node
case `|D| = 1` via `marginalize_marginalize` (claim_3_17) plus
an induction on the cardinality of $D$, then for each
direction contrapose through `IsNotISigmaSeparated`, extract a
$C$-$\sigma$-open walk via `isNotISigmaSeparated_TFAE`
(claim_3_24, item 2), and lift / contract that walk between
the original and marginalised graph using the ancestor- and
bifurcation-preservation results of claim_3_16
(`marginalize_anc_iff`, `marginalize_bifurcation_iff`).

## What this file contributes

A single `theorem`, `isISigmaSeparated_marginalize_iff`, with
the marginalization-stability $\iff$:

```
(G : CDMG α) (A B C D : Set α)
    (hDV : D ⊆ G.V) (hDdisj : Disjoint D (A ∪ B ∪ C)) :
  G.IsISigmaSeparated A B C ↔
    (G.marginalize D).IsISigmaSeparated A B C
```

The body is `sorry`. Pair-extraction at the call site is the
standard `.mp` / `.mpr` projection on the `Iff`.

## Downstream usage

This is *the* foundational stability theorem of section 3.3:
$i\sigma$-separation invariance under "throwing away
unobserved variables disjoint from the statement". Every
chapter from 4 onwards that restricts attention to a relevant
sub-CDMG funnels through this lemma:

* **Chapter 5 (do-calculus, `do-calculus.tex` +
  `proof-do-calculus.tex`)** -- Rule 1 of the do-calculus
  ("insertion / deletion of observations") states that, under
  $i\sigma$-separation in the latent-projected graph, an
  observation can be inserted or deleted from a conditional
  distribution. The graphical side of Rule 1 is exactly the
  `(G.marginalize D).IsISigmaSeparated A B C` surface produced
  here -- the do-calculus proof composes this stability lemma
  with the CBN-Markov property of chapter 4 to derive the
  Rule-1 conclusion. Rules 2 and 3 also reduce, via their own
  graphical premises, to separation-on-a-latent-projection
  arguments that consume this lemma.
* **Chapters 6 -- 7 (identification,
  `adjustment-criteria.tex` / `id-algorithm.tex`)** -- the ID
  algorithm's recursive case-splits hinge on rewriting causal
  effects in terms of marginal sub-graphs (the latent
  projection onto the relevant subset of variables). The
  algorithm's *correctness* proof reduces each recursive step
  to a graphical separation on a marginalised graph, then
  pulls it back to a separation on the original via this
  lemma. Adjustment criteria (backdoor / front-door / general
  adjustment) are likewise stated and verified on marginal
  sub-graphs; the lemma is the bridge that lifts the
  graphical condition to the original CDMG.
* **Chapters 8 -- 10 (iSCMs, `scms.tex` -- `scms4.tex`)** --
  marginal iSCMs inherit graphical separation properties from
  their ambient iSCM via the underlying CDMG's
  marginalisation; counterfactual identification arguments
  use the lemma to translate counterfactual graphical
  conditions between a "context" sub-iSCM and its embedding.
* **Chapters 11 -- 16 (discovery,
  `causal_relations.tex` / `minimal_sep_sets.tex` /
  `fci.tex`)** -- FCI's correctness proof reasons about
  $i\sigma$-separation on the *latent-projected* graph
  (because FCI operates on observed variables and treats
  unobserved ones as latents to be marginalised out); the
  lemma is the load-bearing translation step between the
  observed-marginal graph FCI sees and the full CDMG where
  the LN's separation predicate is defined.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.SigmaSeparationSymmetric`
  (claim_3_22) -- the immediately-preceding one-row claim file
  in this subsection: module-level docstring with
  "What this file contributes" / "Downstream usage" /
  "Style precedents" sections, per-declaration `-- claim_*`
  comment header, LN block reproduced verbatim in a
  `/- ... -/` quote, design-choice block above the theorem,
  body `sorry` at the formalizer-worker stage.
* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation`
  (def_3_18) -- source of `IsISigmaSeparated`. The
  per-`def` design block at `IsISigmaSeparated` (lines
  259 -- 274 in that file) explicitly anticipates *this*
  row in its `Downstream consequences` enumeration:
  *"claim_3_25 ($i\sigma$-separation under marginalization,
  `graphs.tex` lines 1414 -- 1422): equates
  `IsISigmaSeparated G A B C` with
  `IsISigmaSeparated (G.marginalize D) A B C` under suitable
  side conditions. The proof in the LN constructs walks in
  one graph from walks in the other -- exactly the
  three-witness slicing we chose."*
* `Chapter3_GraphTheory.Section3_2.Marginalization`
  (def_3_14) -- source of `CDMG.marginalize`; the per-`def`
  design block lists this very lemma
  (`lem:stability_separation_marginalization`,
  `graphs.tex` line 1416) as a primary downstream consumer
  of marginalization.
* `Chapter3_GraphTheory.Section3_2.MarginalizationsCommute`
  (claim_3_17) -- the lemma the LN proof inducts through,
  source of the `Disjoint W₁ W₂` precedent we mirror here
  (with `D` in place of `W₁ ∪ W₂` against
  `A ∪ B ∪ C`). The `marginalize_marginalize` /
  `marginalize_comm` fusion-and-commute idiom will drive the
  future prover's reduction to the single-node `|D| = 1`
  base case.
* `Chapter3_GraphTheory.Section3_2.MarginalizationPreserves`
  (claim_3_16) -- source of `marginalize_anc_iff` (the
  ancestor-preservation lemma the LN proof's
  `eq:anc_preserved` cites) and `marginalize_bifurcation_iff`
  (the bifurcation-preservation lemma at the heart of the
  bifurcation edge-lifting in `eq:sc_preserved`). The future
  prover will pivot through both.

## Infrastructure note for the future prover

The bulk of the heavy lifting for this row lives in *other*
files. The statement here is intentionally light:

* The LN's `Disjoint D (A ∪ B ∪ C)` side-condition is a
  mathlib `Disjoint` -- same precedent as
  `MarginalizationsCommute.lean`'s `Disjoint W₁ W₂`. The
  hypothesis `hDV : D ⊆ G.V` is the LN's `D ⊆ V`.
* The future prover will mostly compose existing lemmas:
  `marginalize_marginalize` (collapse iterated
  marginalisations); `marginalize_anc_iff` (ancestor
  invariance); `marginalize_bifurcation_iff` (bifurcation
  invariance, no source); `isNotISigmaSeparated_TFAE`
  (contrapositive extraction of a $\sigma$-open walk);
  `sigmaOpens_TFAE` (path/walk conversion). New
  infrastructure that may be needed: a per-walk
  "lift through a single marginalised vertex" / "contract a
  run of one vertex" pair of helpers; the LN proof's
  structure (`graphs.tex` lines 1462 -- 1577) suggests these
  belong in a new helper file
  `Section3_3/SigmaOpenWalkMarginalization.lean` or similar,
  at the prover's discretion.
* No new typeclasses, no new data types: the statement is
  pure proposition-level glue over the existing
  `IsISigmaSeparated` predicate and the `marginalize`
  operator.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

-- claim_3_25
-- title: ISigmaSeparation -- $i\sigma$-separation under
-- marginalization (the LN's
-- `lem:stability_separation_marginalization`)
--
-- `G.IsISigmaSeparated A B C ↔ (G.marginalize D).IsISigmaSeparated A B C`
-- whenever `D ⊆ G.V` and `D` is disjoint from `A ∪ B ∪ C`.
-- The LN frames this as the *stability* of $i\sigma$-separation
-- under "throwing away unobserved variables disjoint from the
-- statement": marginalising over output nodes outside the
-- statement neither creates new separation (forward direction)
-- nor destroys existing separation (backward direction).
-- Three nested universals over walks in the original graph
-- correspond (via edge-lifting / edge-contracting through `D`)
-- to three nested universals over walks in the marginalised
-- graph, and this lemma is the explicit two-way bridge.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_25, lines 1414 -- 1423):

  % claim_3_25
  \begin{claimmark}
  \begin{Lem}[$i\sigma$-separation under marginalization]
      \label{lem:stability_separation_marginalization}
          Let $G=(J,V,E,L)$ be a CDMG,
          $A,B,C \ins J \cup V$ and $D \ins V$
          be subsets of nodes such that:
          \[ D \cap \lp A \cup B \cup C\rp = \emptyset.\]
          Then we have the equivalence:
          \[ A \isPerp_G B \given C \qquad \iff
             \qquad  A \isPerp_{G^{\sm D} }B \given C. \]
  \end{Lem}
  \end{claimmark}
-/
--
-- ## Design choice
--
-- * **Stated on `IsISigmaSeparated`, not on a path / walk
--   universal.** The LN literally writes "$A \isPerp_G B \given
--   C \iff A \isPerp_{G^{\sm D}} B \given C$" -- the
--   *predicate-level* equivalence. Downstream chapters
--   (do-calculus Rule 1, ID algorithm, adjustment criteria,
--   FCI) consume the result at this surface, never at the
--   unfolded walk-universal level. Stating the theorem on
--   `IsISigmaSeparated` directly keeps the LN's $\isPerp_G$
--   symbol visible in goal states and lets call sites compose
--   it with the rest of section 3.3's separation API
--   (claim_3_22's symmetry, claim_3_24's path/walk
--   equivalences, claim_3_27's walk-replacement) without
--   shuffling through `isISigmaSeparated_iff`. Downstream
--   chapter-5+ consumers who *do* need to descend to walks
--   (e.g. to extract a specific $\sigma$-open walk witness
--   from `¬IsISigmaSeparated`) pivot through claim_3_24's
--   `isNotISigmaSeparated_TFAE` -- *not* through this lemma's
--   statement, which stays at the predicate level. The future
--   prover of *this* lemma will of course *open up*
--   `IsISigmaSeparated` inside the proof body (the LN
--   argument contraposes to `IsNotISigmaSeparated` and pivots
--   through `isNotISigmaSeparated_TFAE` of claim_3_24, item 2,
--   to extract a $C$-$\sigma$-open walk witness; see the
--   module docstring above for the full proof skeleton) --
--   that's a proof-side concern, not a statement-side one.
--
-- * **Explicit `(A B C D : Set α)` binders, not strict-implicit
--   `⦃ ⦄` or plain implicit `{ }`.** Matches every other
--   Section 3.3 separation theorem
--   (`isSigmaSeparated_symm`, `isISigmaSeparated_TFAE`,
--   `isNotISigmaSeparated_TFAE`, `sigmaOpens_TFAE`): the LN
--   names $A, B, C$ explicitly in every statement they appear
--   in, callers always know the four sets at the call site
--   (do-calculus Rule 1 hands in *specific* sets, never
--   "Lean-figure-this-out" placeholders), and the
--   `intro` / `obtain` rhythm at downstream call sites reads
--   cleanest when the four sets are explicit arguments. The
--   alternative (implicit `{A B C D}`) would force every
--   caller to either pass them positionally or use
--   `(A := _) (B := _) (C := _) (D := _)` named-arguments
--   syntax to avoid Lean's unification fishing in the four
--   `Set α`-typed positions of the goal -- both noisier than
--   four explicit binders. The strict-implicit `⦃ ⦄` is
--   reserved for the *internal* universals of
--   `IsISigmaSeparated`'s definition (the per-walk
--   `⦃v w : α⦄`); top-level theorem binders use plain
--   explicit `( )` per the rest of the subsection.
--
-- * **`Disjoint D (A ∪ B ∪ C)`, not `D ∩ (A ∪ B ∪ C) = ∅`.**
--   The LN writes "$D \cap (A \cup B \cup C) = \emptyset$";
--   mathlib's `Disjoint` from `Mathlib.Order.Disjoint` is the
--   idiomatic equivalent and is the form already used in this
--   chapter -- `Section3_2.MarginalizationsCommute.lean`'s
--   `Disjoint W₁ W₂` precedent (the lemma the LN proof of
--   *this* row inducts through). Using `Disjoint` over the
--   raw `∩ = ∅` form gives us the standard mathlib API
--   (`Disjoint.symm`, `Disjoint.mono_left` /
--   `_mono_right`, `Set.disjoint_iff_inter_eq_empty` if
--   needed) without manual set-theoretic massaging.
--   `Set.disjoint_iff_inter_eq_empty` recovers the LN's
--   literal form at any call site that wants it.
--
-- * **`hDV : D ⊆ G.V` is kept as an explicit hypothesis, not
--   baked into `marginalize`'s signature.** `marginalize` is
--   designed to be well-defined for *every* `W : Set α`
--   (see the design block on `marginalize` in
--   `Section3_2/Marginalization.lean`, lines 258 -- 286,
--   which spells out the iteration / composition reasons for
--   the no-precondition design). The LN's "$D \subseteq V$"
--   condition is a load-bearing *intent* marker (the LN
--   marginalises over output nodes, not input nodes -- the
--   `J` / `V` distinction is the whole point of the CDMG
--   paradigm), and every `marginalize_*_iff` consumer in
--   `Section3_2/MarginalizationPreserves.lean` carries an
--   equivalent `v ∉ W` / endpoint-in-`G.V \ W` hypothesis as
--   the LN's $D \subseteq V$ side-condition. Threading
--   `hDV : D ⊆ G.V` as an explicit hypothesis here matches
--   that precedent and signals the *intended* domain to
--   readers of the statement; the proof will use it directly
--   (e.g. to discharge ancestor / bifurcation arguments
--   restricted to `G.V \ D`).
--
-- * **`A, B, C ⊆ G.J ∪ G.V` is *not* a hypothesis.** Same
--   convention as `IsISigmaSeparated`'s definition: the LN
--   preamble "$A, B, C \subseteq J \cup V$" is a *caller's*
--   side-condition, not a type-level guard, and the rest of
--   section 3.3 (the symmetric / TFAE / path-walk
--   equivalence claims, all in the same subsection) follows
--   that same convention -- none of them carry an
--   `A, B, C ⊆ G.J ∪ G.V` hypothesis at the type level. The
--   bridging value is zero: any set-member of $A$ / $B$ / $C$
--   outside $G.J \cup G.V$ contributes no walk-endpoint
--   witnesses to either side of the `↔` (walks of length
--   $\ge 1$ are confined to nodes by the `E_subset` /
--   `L_subset` CDMG fields, and length-0 walks are
--   self-loops which the marginalisation preserves
--   componentwise on `G.J ∪ (G.V \ D)`). Adding the
--   hypothesis would clutter the signature without producing
--   any new proof-content; omitting it keeps the surface
--   uniform with `IsISigmaSeparated`'s own definition (where
--   the convention was originally chosen, see the design
--   block at `ISigmaSeparation.lean` lines 322 -- 332) and
--   with every other claim of section 3.3.
--
-- * **`Iff`, not two separate `→`s.** Mirrors the LN's
--   $\iff$. The contrapositive form
--   "$A \nisPerp_G B \given C \iff A \nisPerp_{G^{\sm D}}
--   B \given C$" follows by `Iff.not` (`not_congr`) at the
--   call site; we do not also expose it as a second
--   theorem. The LN's single $\iff$ statement collapses
--   both directions into one, and a `not_congr` rewrite is
--   a one-liner downstream.
--
-- * **Naming `isISigmaSeparated_marginalize_iff`.** Snake-case,
--   the `_iff` suffix marks the result as a biconditional
--   (mathlib convention, e.g. `Set.mem_union_iff`,
--   `Nat.lt_succ_iff`). Mirrors the
--   `marginalize_anc_iff` / `marginalize_bifurcation_iff`
--   precedents in `Section3_2/MarginalizationPreserves.lean`
--   on the "predicate-iff under marginalization" pattern;
--   the only naming difference is the predicate prefix
--   (`isISigmaSeparated_` here vs. `marginalize_anc_`
--   /`marginalize_bifurcation_` there), reflecting that
--   *this* row's predicate is itself a Section 3.3 surface
--   while claim_3_16's predicates live in Section 3.1.
--   Putting the predicate name *first* and the
--   construction (`marginalize`) *after* matches the
--   "<conclusion>_<construction>" project convention used
--   elsewhere in chapter 3
--   (`isAcyclic_nodeSplittingOn`,
--   `isTopologicalOrder_nodeSplittingOn`, ...).
--
-- * **`G`-first signature for dot-notation.** Matches every
--   other `CDMG`-level theorem in the file
--   (`G.IsISigmaSeparated`, `G.marginalize`,
--   `G.isSigmaSeparated_symm`, ...). Callers write
--   `G.isISigmaSeparated_marginalize_iff A B C D hDV
--   hDdisj` in the same prose order as the LN's
--   "$A \isPerp_G B \given C \iff A \isPerp_{G^{\sm D}}
--   B \given C$".
--
-- * **Minimal imports.** Only `Section3_3.ISigmaSeparation`
--   (for `IsISigmaSeparated`) and `Section3_2.Marginalization`
--   (for `marginalize`) are needed at the *statement* stage.
--   The proof worker will add `MarginalizationsCommute`,
--   `MarginalizationPreserves`, `SigmaSeparationEquivalences`,
--   `SigmaOpenPathWalk` as needed; importing them now would
--   bloat the dependency graph for no statement-side
--   benefit.
--
-- * **No mathlib re-use at the statement level.** Mathlib has
--   no graphical-separation API; the predicate
--   `IsISigmaSeparated`, the operator `marginalize`, and the
--   subset / disjoint side-conditions are all our own
--   bespoke surface over mathlib's `Set` and `Disjoint`.
--   The only mathlib pieces visible in the signature are
--   `Set`, `Disjoint`, `⊆`, `↔`, and `∪` -- standard logical
--   glue.
--
-- ## Constraints / known limitations
--
-- * **`hDV : D ⊆ G.V` is the caller's responsibility, not
--   enforced at the type level.** This is the LN's
--   "$D \subseteq V$" side-condition, and a caller stating
--   the lemma with `D ⊆ G.J ∪ G.V` (allowing some `D`-members
--   to be input nodes) would produce a goal Lean accepts but
--   the LN does not endorse: `marginalize` does not touch
--   input nodes, so the input-node members of `D` are inert
--   on the marginalisation side, but the LN's proof
--   (via ancestor / bifurcation tracking on $V \sm D$)
--   silently relies on $D$ being *output*-only. Callers
--   that want a `D` mixed across $J \cup V$ should split it
--   and apply the lemma to the $V$-restricted part.
--
-- * **`hDdisj : Disjoint D (A ∪ B ∪ C)` is the LN's only
--   load-bearing side-condition.** Without it, the LN's
--   contraposition argument breaks: a $\sigma$-open walk in
--   one graph that has an endpoint in `D` would have no
--   corresponding walk in the other graph (the endpoint
--   isn't in the marginalised graph at all). The hypothesis
--   captures both this endpoint-preservation and the
--   ancestor-set / bifurcation-set preservation arguments at
--   the level of $A$, $B$, $C$.
--
-- * **No quantitative content -- pure invariance lemma.**
--   This row's statement is the bare $\iff$; it says nothing
--   about *how* the witnesses on the two sides relate (e.g.
--   "the shortest $\sigma$-open walk on one side lifts to a
--   $\sigma$-open walk of bounded length on the other"). The
--   LN's proof constructs such walk-lifts / walk-contractions
--   explicitly, but they are proof-side scaffolding and not
--   part of the named statement. Downstream consumers that
--   need the walk-level translation can either peel into the
--   proof (poor abstraction) or, in the unlikely event such
--   a quantitative version is wanted, add a separate named
--   theorem at proof time; the LN does not state one.

/-! ## DISPROVE MODE -- the LN's lemma is false under the Lean
encoding of marginalization.

The LN's lemma `lem:stability_separation_marginalization`
(`graphs.tex` lines 1414 -- 1577) asserts the `↔`. Independent
investigation (see `workspace_claim_3_25.md` and the verified
TeX proof of the negation at
`tex/claim_3_25_proof_ISigmaSeparation.tex`) shows that the
LN's proof of the $(\Longleftarrow)$ direction relies on a
bidirected-edge inclusion that **fails** under our Lean
encoding of `CDMG.marginalize`. Specifically:

  * The LN's proof, at `graphs.tex:1559`, asserts that a fork
    bifurcation $w \hut u \tuh b_{j+1}$ in $G$ yields a
    bidirected edge $w \huh b_{j+1} \in L^{\sm u}$.
  * Under our encoding of `CDMG.marginalize` (see
    `Section3_2/Marginalization.lean:530 -- 535`), the
    $L^{\sm W}$ set has **two exclusion clauses** that remove
    a candidate pair $(\ul v, \ol v)$ if there is any directed
    walk in $G$ from $\ul v$ to $\ol v$ (or vice versa) with
    interior in $W$. These exclusion clauses are forced by
    `def_3_1.CDMG`'s `disjoint_EL` field (`Disjoint E L`),
    which prevents a pair from being simultaneously a directed
    and a bidirected edge of the marginalized graph.
  * On the witness below the directed walk
    $w \tuh u \tuh b_{j+1}$ supplies $(w, b_{j+1}) \in E^{\sm u}$
    and consequently kicks $(w, b_{j+1})$ out of $L^{\sm u}$.
    The LN's rerouting step is unavailable.

We therefore prove the **negation**: there exists a CDMG with
sets `A`, `B`, `C`, `D` satisfying the disjointness hypothesis
for which the `↔` fails. The witness, encoded over `Fin 6`
with labels `v_0 = 0`, `b_j = 1`, `u = 2`, `w = 3`,
`b_{j+1} = 4`, `v_n = 5`, has:

  * $J := \emptyset$, $V := \{0,1,2,3,4,5\}$, $L := \emptyset$,
  * $E := \{(0,1), (1,2), (2,4), (4,5), (2,3), (3,2), (3,1)\}$,
  * $A := \{0\}$, $B := \{5\}$, $C := \{1, 3\}$, $D := \{2\}$.

The TeX proof exhaustively verifies:
  * `¬ G.IsISigmaSeparated A B C` via the $C$-$\sigma$-open
    walk $0 \to 1 \to 2 \to 4 \to 5$ (position 1 is the
    unblockable non-collider with $u = 2 \in \Sc^G(b_j) = \{1, 2, 3\}$).
  * `(G.marginalize {2}).IsISigmaSeparated A B C` via the
    forced-final-two-steps case analysis: every walk in
    $G^{\sm 2}$ from `0` to `5` has its penultimate edge
    forced to be a forward step from $\{1, 3\}$ to `4`
    (Case A: blockable non-collider in `C` at the
    third-from-last position) or from `5` back to `4`
    (Case B: collider at `5` outside `Anc^{G^{\sm 2}}(C) =
    \{0, 1, 3\}`). The body that follows mirrors that case
    analysis. -/

/-! ### The witness CDMG over `Fin 6` -/

/-- The witness CDMG `G_witness : CDMG (Fin 6)` showing that
the LN's `lem:stability_separation_marginalization` is false
under the Lean encoding of `CDMG.marginalize`. The labelling
`v_0 = 0, b_j = 1, u = 2, w = 3, b_{j+1} = 4, v_n = 5` mirrors
the TeX proof at
`tex/claim_3_25_proof_ISigmaSeparation.tex`. -/
def G_witness : CDMG (Fin 6) where
  J := ∅
  V := {0, 1, 2, 3, 4, 5}
  disjoint_JV := by
    rw [Set.disjoint_left]; intro _ hJ _; exact hJ
  E := {(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)}
  E_subset := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h | h | h | h | h | h | h <;>
      (subst h; refine ⟨Or.inr ?_, ?_⟩ <;>
        simp [Set.mem_insert_iff, Set.mem_singleton_iff])
  L := ∅
  L_subset := by intro _ h; exact h.elim
  L_irrefl := by intro _ _ h; exact h.elim
  L_symm := by intro _ _ h; exact h.elim
  disjoint_EL := by
    rw [Set.disjoint_left]; intro _ _ hL; exact hL.elim

/-- The labels used in the witness; aliasing for readability. -/
abbrev v0 : Fin 6 := 0
abbrev bj : Fin 6 := 1
abbrev u  : Fin 6 := 2
abbrev w_  : Fin 6 := 3
abbrev bj1 : Fin 6 := 4
abbrev vn : Fin 6 := 5

/-- The conditioning set `C = {1, 3}` (LN's `{b_j, w}`). -/
abbrev C_witness : Set (Fin 6) := {1, 3}

/-! ### LHS direction: `¬ G_witness.IsISigmaSeparated {0} {5} C_witness`

We exhibit the walk $0 \to 1 \to 2 \to 4 \to 5$ in $G$ and
verify it is $C$-$\sigma$-open by checking each position. The
key fact is that position 1 ($b_j = 1$) is an **unblockable**
non-collider because its forward-out target $u = 2$ lies in
$\Sc^G(1) = \{1, 2, 3\}$ (witnessed by the directed walks
$1 \to 2$ and $2 \to 3 \to 1$). The other interior positions
have nodes outside $C = \{1, 3\}$, so their blockable-or-not
status does not block the walk. There are no colliders since
every step is forward. -/

/-- Membership in `G_witness.E` for `(0, 1)`. -/
private lemma G_witness_E_01 : (0, 1) ∈ G_witness.E := by
  show (0, 1) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership in `G_witness.E` for `(1, 2)`. -/
private lemma G_witness_E_12 : (1, 2) ∈ G_witness.E := by
  show (1, 2) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership in `G_witness.E` for `(2, 4)`. -/
private lemma G_witness_E_24 : (2, 4) ∈ G_witness.E := by
  show (2, 4) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership in `G_witness.E` for `(4, 5)`. -/
private lemma G_witness_E_45 : (4, 5) ∈ G_witness.E := by
  show (4, 5) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership in `G_witness.E` for `(2, 3)`. -/
private lemma G_witness_E_23 : (2, 3) ∈ G_witness.E := by
  show (2, 3) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership in `G_witness.E` for `(3, 2)`. -/
private lemma G_witness_E_32 : (3, 2) ∈ G_witness.E := by
  show (3, 2) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership in `G_witness.E` for `(3, 1)`. -/
private lemma G_witness_E_31 : (3, 1) ∈ G_witness.E := by
  show (3, 1) ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6))
  simp

/-- Membership characterisation of `G_witness.E`. -/
private lemma G_witness_mem_E_iff (p : Fin 6 × Fin 6) :
    p ∈ G_witness.E ↔
      p = (0, 1) ∨ p = (1, 2) ∨ p = (2, 4) ∨ p = (4, 5) ∨
      p = (2, 3) ∨ p = (3, 2) ∨ p = (3, 1) := by
  show p ∈ ({(0, 1), (1, 2), (2, 4), (4, 5), (2, 3), (3, 2), (3, 1)} : Set (Fin 6 × Fin 6)) ↔ _
  simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

/-- `G_witness.V` membership characterisation. -/
private lemma G_witness_mem_V_iff (v : Fin 6) :
    v ∈ G_witness.V ↔ v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by
  show v ∈ ({0, 1, 2, 3, 4, 5} : Set (Fin 6)) ↔ _
  simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

/-- Every `Fin 6` element is in `G_witness.V`. -/
private lemma G_witness_V_univ (v : Fin 6) : v ∈ G_witness.V := by
  rw [G_witness_mem_V_iff]
  -- `decide` over Fin 6 should work: just enumerate the cases.
  have h6 : v.val < 6 := v.isLt
  match v, h6 with
  | ⟨0, _⟩, _ => left; rfl
  | ⟨1, _⟩, _ => right; left; rfl
  | ⟨2, _⟩, _ => right; right; left; rfl
  | ⟨3, _⟩, _ => right; right; right; left; rfl
  | ⟨4, _⟩, _ => right; right; right; right; left; rfl
  | ⟨5, _⟩, _ => right; right; right; right; right; rfl

/-- `G_witness.J = ∅`, so `v ∈ G_witness ↔ v ∈ G_witness.V`. -/
private lemma G_witness_mem (v : Fin 6) : v ∈ G_witness := by
  show v ∈ G_witness.J ∪ G_witness.V
  exact Or.inr (G_witness_V_univ v)

/-- Directed walk `1 → 2` in `G_witness`. -/
private def walk_1_2 : Walk G_witness 1 2 :=
  .cons (.forward G_witness_E_12) (.nil 2)

/-- Directed walk `2 → 3 → 1` in `G_witness`. -/
private def walk_2_3_1 : Walk G_witness 2 1 :=
  .cons (.forward G_witness_E_23) (.cons (.forward G_witness_E_31) (.nil 1))

/-- `2 ∈ G_witness.Anc 1`: there is a directed walk from `2` to `1`. -/
private lemma two_mem_anc_one : (2 : Fin 6) ∈ G_witness.Anc 1 := by
  refine ⟨G_witness_mem 2, walk_2_3_1, ?_⟩
  unfold walk_2_3_1
  simp [Walk.IsDirected]

/-- `2 ∈ G_witness.Desc 1`: there is a directed walk from `1` to `2`. -/
private lemma two_mem_desc_one : (2 : Fin 6) ∈ G_witness.Desc 1 := by
  refine ⟨G_witness_mem 2, walk_1_2, ?_⟩
  unfold walk_1_2
  simp [Walk.IsDirected]

/-- `2 ∈ G_witness.Sc 1` — the unblockability fact for position 1
on the LHS walk. -/
private lemma two_mem_Sc_one : (2 : Fin 6) ∈ G_witness.Sc 1 :=
  ⟨two_mem_anc_one, two_mem_desc_one⟩

/-- The LHS witness walk: $0 \to 1 \to 2 \to 4 \to 5$ in `G_witness`. -/
private def disproof_walk : Walk G_witness 0 5 :=
  .cons (.forward G_witness_E_01)
    (.cons (.forward G_witness_E_12)
      (.cons (.forward G_witness_E_24)
        (.cons (.forward G_witness_E_45) (.nil 5))))

/-- The LHS walk is $C$-$\sigma$-open in `G_witness`. -/
private lemma disproof_walk_isSigmaOpen :
    disproof_walk.IsSigmaOpen C_witness := by
  refine ⟨?_, ?_⟩
  · -- No colliders: every step is forward, so each interior joint has
    -- (HasArrowheadAtTarget True) ∧ (HasArrowheadAtSource False) = False.
    intro k hcoll
    -- For colliders to be possible, position k must be 1, 2, or 3 (interior).
    -- Otherwise IsColliderAt is False.
    exfalso
    revert hcoll
    unfold disproof_walk
    match k with
    | 0 => simp
    | 1 => simp [WalkStep.HasArrowheadAtSource]
    | 2 => simp [WalkStep.HasArrowheadAtSource]
    | 3 => simp [WalkStep.HasArrowheadAtSource]
    | n + 4 => simp
  · -- Blockable non-colliders are not in C.
    intro k hblk
    -- Position 0 (vertex 0), 1 (vertex 1, unblockable), 2 (vertex 2),
    -- 3 (vertex 4), 4 (vertex 5). Need nodeAt ∉ {1, 3}.
    have hlen : k ≤ disproof_walk.length := hblk.1.1
    have hlen' : k ≤ 4 := by
      unfold disproof_walk at hlen
      simpa [Walk.length] using hlen
    match k, hlen' with
    | 0, _ =>
      -- vertex 0, not in C.
      simp [disproof_walk, Walk.nodeAt, C_witness,
            Set.mem_insert_iff, Set.mem_singleton_iff]
    | 1, _ =>
      -- vertex 1, but position 1 is UNBLOCKABLE.
      exfalso
      apply hblk.2
      -- Show IsUnblockableNonColliderAt at position 1.
      show (disproof_walk).IsUnblockableNonColliderAt 1
      unfold disproof_walk
      simp only [Walk.isUnblockableNonColliderAt_cons_cons_one]
      refine ⟨?_, ?_, ?_⟩
      · -- ¬ collider: forward in forward out has False source-arrow.
        simp [WalkStep.HasArrowheadAtSource]
      · -- IsBackward s → ...: forward isn't backward.
        intro h
        simp [WalkStep.IsBackward] at h
      · -- IsForward s' → target ∈ Sc(1).
        intro _
        exact two_mem_Sc_one
    | 2, _ =>
      simp [disproof_walk, Walk.nodeAt, C_witness,
            Set.mem_insert_iff, Set.mem_singleton_iff]
    | 3, _ =>
      simp [disproof_walk, Walk.nodeAt, C_witness,
            Set.mem_insert_iff, Set.mem_singleton_iff]
    | 4, _ =>
      simp [disproof_walk, Walk.nodeAt, C_witness,
            Set.mem_insert_iff, Set.mem_singleton_iff]

/-- The LHS direction of the disproof:
`¬ G_witness.IsISigmaSeparated {0} {5} C_witness`. -/
private lemma not_isISigmaSeparated_G_witness :
    ¬ G_witness.IsISigmaSeparated {0} {5} C_witness := by
  intro h
  have h0 : (0 : Fin 6) ∈ ({0} : Set (Fin 6)) := Set.mem_singleton 0
  have h5 : (5 : Fin 6) ∈ G_witness.J ∪ ({5} : Set (Fin 6)) :=
    Or.inr (Set.mem_singleton 5)
  have hblock := h h0 h5 disproof_walk
  rw [Walk.isSigmaBlocked_iff_not_isSigmaOpen] at hblock
  exact hblock disproof_walk_isSigmaOpen

/-! ### RHS direction: `(G_witness.marginalize {2}).IsISigmaSeparated {0} {5} C_witness`

Every walk in `G^{∖2}` from `0` to `5` is $C$-$\sigma$-blocked.
The proof follows the TeX proof's forced-final-two-steps case
analysis. We use a number of structural lemmas about edges in
`G^{∖2}` that touch the relevant vertices `5`, `4`, `0`. -/

/-- Edges touching `5` in `G_witness`: only `(4, 5)` and the
reverse direction would require `5 → ?`, but no edge in `G.E`
has source `5`. The forward-direction successor of `5` is empty,
and no length-≥1 walk from `5` exists. So the only edge in
`G^{∖2}.E` of the form `(_, 5)` is `(4, 5)`. -/
private lemma G_witness_E_into_5 (a : Fin 6) (h : (a, 5) ∈ G_witness.E) :
    a = 4 := by
  rw [G_witness_mem_E_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ |
                ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact h1
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

/-- No edge in `G_witness` has `5` as its source. -/
private lemma G_witness_E_out_of_5 (b : Fin 6) :
    ¬ (5, b) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
                ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    exact absurd h1 (by decide)

/-- Edges in `G_witness` with target `4`: `(2, 4)` only. -/
private lemma G_witness_E_into_4 (a : Fin 6) (h : (a, 4) ∈ G_witness.E) :
    a = 2 := by
  rw [G_witness_mem_E_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ |
                ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact h1
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

/-- Edges in `G_witness` with source `4`: `(4, 5)` only. -/
private lemma G_witness_E_out_of_4 (b : Fin 6) (h : (4, b) ∈ G_witness.E) :
    b = 5 := by
  rw [G_witness_mem_E_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ |
                ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact h2
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- `(2, 2) ∉ G_witness.E` — there is no self-loop at vertex 2. -/
private lemma G_witness_E_no_22 : ¬ (2, 2) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp at h

/-- `(0, 2) ∉ G_witness.E`. -/
private lemma G_witness_E_no_02 : ¬ (0, 2) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp at h

/-- `(4, 2) ∉ G_witness.E`. -/
private lemma G_witness_E_no_42 : ¬ (4, 2) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp at h

/-- `(5, 2) ∉ G_witness.E`. -/
private lemma G_witness_E_no_52 : ¬ (5, 2) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp at h

/-- `(2, 5) ∉ G_witness.E`. -/
private lemma G_witness_E_no_25 : ¬ (2, 5) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp at h

/-- `(2, 0) ∉ G_witness.E`. -/
private lemma G_witness_E_no_20 : ¬ (2, 0) ∈ G_witness.E := by
  intro h
  rw [G_witness_mem_E_iff] at h
  simp at h

/-- Successors of `2` in `G_witness.E`: only `3` and `4`. -/
private lemma G_witness_E_out_of_2 (b : Fin 6) (h : (2, b) ∈ G_witness.E) :
    b = 3 ∨ b = 4 := by
  rw [G_witness_mem_E_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ |
                ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact Or.inr h2
  · exact absurd h1 (by decide)
  · exact Or.inl h2
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

/-- Predecessors of `2` in `G_witness.E`: only `1` and `3`. -/
private lemma G_witness_E_into_2 (a : Fin 6) (h : (a, 2) ∈ G_witness.E) :
    a = 1 ∨ a = 3 := by
  rw [G_witness_mem_E_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ |
                ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd h2 (by decide)
  · exact Or.inl h1
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact Or.inr h1
  · exact absurd h2 (by decide)

/-! ### Structure of directed walks with interior in `{2}` in `G_witness`

Any directed walk in `G_witness` with interior in `{2}` has length ≤ 2,
since longer walks would require `(2, 2) ∈ G_witness.E`, which fails. -/

/-- Helper: a walk's support is always nonempty. -/
private lemma Walk_support_ne_nil {α : Type*} {G : CDMG α} {v w : α}
    (π : Walk G v w) : π.support ≠ [] := by
  cases π with
  | nil _ => simp [Walk.support]
  | cons _ _ => simp [Walk.support]

/-- Helper: in a walk of the shape `cons s (cons s' p)`, the
joint vertex `w₁` between `s` and `s'` lies in the walk's
interior (`support.tail.dropLast`). -/
private lemma support_tail_dropLast_cons_cons
    {α : Type*} {G : CDMG α} {v w₁ w₂ u : α}
    (s : WalkStep G v w₁) (s' : WalkStep G w₁ w₂) (p : Walk G w₂ u) :
    w₁ ∈ (Walk.cons s (Walk.cons s' p)).support.tail.dropLast := by
  -- support = v :: w₁ :: support p; tail = w₁ :: support p; dropLast = w₁ :: dropLast (support p)
  rw [Walk.support_cons, List.tail_cons, Walk.support_cons,
      List.dropLast_cons_of_ne_nil (Walk_support_ne_nil p)]
  simp

/-- Helper: in a walk of the shape `cons s (cons s' (cons s'' p))`, the
joint vertex `w₂` (after step `s'`) lies in the walk's interior. -/
private lemma support_tail_dropLast_cons_cons_cons
    {α : Type*} {G : CDMG α} {v w₁ w₂ w₃ u : α}
    (s : WalkStep G v w₁) (s' : WalkStep G w₁ w₂) (s'' : WalkStep G w₂ w₃)
    (p : Walk G w₃ u) :
    w₂ ∈ (Walk.cons s (Walk.cons s' (Walk.cons s'' p))).support.tail.dropLast := by
  have h_inner_ne : ((Walk.cons s'' p) : Walk _ w₂ u).support ≠ [] :=
    Walk_support_ne_nil _
  rw [Walk.support_cons, List.tail_cons, Walk.support_cons,
      List.dropLast_cons_of_ne_nil h_inner_ne]
  -- now goal: w₂ ∈ w₁ :: (Walk.cons s'' p).support.dropLast
  -- (Walk.cons s'' p).support = w₂ :: p.support, so its dropLast = w₂ :: p.support.dropLast
  -- (if p.support is nonempty, which it is).
  rw [show ((Walk.cons s'' p) : Walk _ w₂ u).support =
        w₂ :: p.support from rfl]
  rw [List.dropLast_cons_of_ne_nil (Walk_support_ne_nil p)]
  -- now goal: w₂ ∈ w₁ :: w₂ :: p.support.dropLast
  right
  exact List.mem_cons_self

/-- The structure of a directed walk in `G_witness` with interior
in `{2}`: it has length 0, 1, or 2. The length-2 case has middle
vertex `2`. -/
private lemma directed_interior_2_structure :
    ∀ {a b : Fin 6} (π : Walk G_witness a b),
      π.IsDirected → π.InteriorIn {2} →
      (π.length = 0 ∧ a = b) ∨
      (π.length = 1 ∧ (a, b) ∈ G_witness.E) ∨
      (π.length = 2 ∧ (a, 2) ∈ G_witness.E ∧ (2, b) ∈ G_witness.E) := by
  intro a b π hdir hint
  induction π with
  | nil _ =>
    -- length 0, a = b automatically.
    exact Or.inl ⟨rfl, rfl⟩
  | @cons v m _ s p ih =>
    -- v = a; we induct via the tail p : Walk G m b.
    match s, hdir with
    | .backward _, hd => simp [Walk.IsDirected] at hd
    | .bidir _, hd => simp [Walk.IsDirected] at hd
    | .forward hvm, hd =>
      -- s = forward, hvm : (v, m) ∈ G_witness.E. p : Walk G m b.
      -- The walk is (cons (forward hvm) p) : Walk G v b of length p.length + 1.
      -- Case on p.
      cases p with
      | nil _ =>
        -- length 1: (v, b) ∈ E. m = b.
        exact Or.inr (Or.inl ⟨by simp [Walk.length], hvm⟩)
      | @cons _ m' _ s' p' =>
        -- length ≥ 2. m is in the interior. So m = 2.
        have hm : m = 2 := by
          have := hint m (support_tail_dropLast_cons_cons (.forward hvm) s' p')
          exact Set.mem_singleton_iff.mp this
        subst hm
        -- Now s : forward, hvm : (v, 2) ∈ E. p = cons s' p' : Walk G 2 b.
        -- s' : WalkStep G 2 m'. Need s' forward (since hd is directed).
        have hd_tail : (Walk.cons s' p').IsDirected := by
          simp [Walk.IsDirected] at hd
          exact hd
        match s', hd_tail with
        | .backward _, hd' => simp [Walk.IsDirected] at hd'
        | .bidir _, hd' => simp [Walk.IsDirected] at hd'
        | .forward h2m', hd' =>
          -- h2m' : (2, m') ∈ E. m' ∈ {3, 4}.
          -- Case on p'.
          cases p' with
          | nil _ =>
            -- length 2 walk: v → 2 → m' = b. So (v, 2), (2, b) ∈ E.
            exact Or.inr (Or.inr ⟨by simp [Walk.length], hvm, h2m'⟩)
          | @cons _ m'' _ s'' p'' =>
            -- length ≥ 3. Interior contains m' (just after 2).
            -- So m' = 2.
            have hm' : m' = 2 := by
              have hm'_in := support_tail_dropLast_cons_cons_cons
                (WalkStep.forward hvm) (WalkStep.forward h2m') s'' p''
              have := hint m' hm'_in
              exact Set.mem_singleton_iff.mp this
            subst hm'
            -- Now we have a forward step from 2 to 2: (2, 2) ∈ E.
            -- But (2, 2) ∉ E.
            exact absurd h2m' G_witness_E_no_22

/-! ### Edge characterizations in `G_witness.marginalize {2}` -/

/-- If `(a, 5) ∈ (G_witness.marginalize {2}).E`, then `a = 4`. -/
private lemma marg_E_into_5 (a : Fin 6)
    (h : (a, 5) ∈ (G_witness.marginalize {2}).E) : a = 4 := by
  rw [CDMG.mem_marginalize_E] at h
  obtain ⟨_, _, π, hdir, hint, hlen⟩ := h
  rcases directed_interior_2_structure π hdir hint with
    ⟨hlen0, _⟩ | ⟨_, hab⟩ | ⟨_, _, h2b⟩
  · omega
  · exact G_witness_E_into_5 _ hab
  · exact absurd h2b G_witness_E_no_25

/-- No edge in `(G_witness.marginalize {2}).E` has source `5`. -/
private lemma marg_E_out_of_5 (b : Fin 6) :
    ¬ (5, b) ∈ (G_witness.marginalize {2}).E := by
  intro h
  rw [CDMG.mem_marginalize_E] at h
  obtain ⟨_, _, π, hdir, hint, hlen⟩ := h
  rcases directed_interior_2_structure π hdir hint with
    ⟨hlen0, _⟩ | ⟨_, hab⟩ | ⟨_, h5_2, _⟩
  · omega
  · exact G_witness_E_out_of_5 _ hab
  · exact G_witness_E_no_52 h5_2

/-- If `(a, 4) ∈ (G_witness.marginalize {2}).E`, then `a ∈ {1, 3}`. -/
private lemma marg_E_into_4 (a : Fin 6)
    (h : (a, 4) ∈ (G_witness.marginalize {2}).E) : a = 1 ∨ a = 3 := by
  rw [CDMG.mem_marginalize_E] at h
  obtain ⟨ha_J_or_V, _, π, hdir, hint, hlen⟩ := h
  have ha_ne_2 : a ≠ 2 := by
    intro h_eq
    subst h_eq
    rcases ha_J_or_V with hJ | hV
    · exact hJ
    · exact hV.2 rfl
  rcases directed_interior_2_structure π hdir hint with
    ⟨hlen0, _⟩ | ⟨_, hab⟩ | ⟨_, ha2, _⟩
  · omega
  · -- (a, 4) ∈ G.E means a = 2 (only predecessor of 4), but a ≠ 2.
    have ha_eq_2 := G_witness_E_into_4 _ hab
    exact absurd ha_eq_2 ha_ne_2
  · -- a → 2 → 4: (a, 2), (2, 4) ∈ E. a ∈ {1, 3}.
    exact G_witness_E_into_2 _ ha2

/-- If `(4, b) ∈ (G_witness.marginalize {2}).E`, then `b = 5`. -/
private lemma marg_E_out_of_4 (b : Fin 6)
    (h : (4, b) ∈ (G_witness.marginalize {2}).E) : b = 5 := by
  rw [CDMG.mem_marginalize_E] at h
  obtain ⟨_, _, π, hdir, hint, hlen⟩ := h
  rcases directed_interior_2_structure π hdir hint with
    ⟨hlen0, _⟩ | ⟨_, hab⟩ | ⟨_, h4_2, _⟩
  · omega
  · exact G_witness_E_out_of_4 _ hab
  · exact absurd h4_2 G_witness_E_no_42

/-! ### Generalized walk-length bound for `InteriorIn {2}` -/

/-- Any walk in `G_witness` whose interior lies in `{2}` has
length at most 2: a length-≥3 walk would have two consecutive
interior vertices both equal to `2`, requiring a step between
`2` and `2`, which would need `(2, 2) ∈ G_witness.E` (false)
or `(2, 2) ∈ G_witness.L` (also false since `G_witness.L = ∅`). -/
private lemma walk_interior_2_length_le_2 :
    ∀ {a b : Fin 6} (π : Walk G_witness a b),
      π.InteriorIn {2} → π.length ≤ 2 := by
  intro a b π hint
  induction π with
  | nil _ => simp [Walk.length]
  | @cons v m _ s p ih =>
    cases p with
    | nil _ => simp [Walk.length]
    | @cons _ m' _ s' p' =>
      cases p' with
      | nil _ => simp [Walk.length]
      | @cons _ m'' _ s'' p'' =>
        -- π = cons s (cons s' (cons s'' p'')). Length ≥ 3.
        -- Positions 1 and 2 of π are m and m'.
        have hm : m = 2 := Set.mem_singleton_iff.mp
          (hint m (support_tail_dropLast_cons_cons s
            s' (Walk.cons s'' p'')))
        have hm' : m' = 2 := Set.mem_singleton_iff.mp
          (hint m' (support_tail_dropLast_cons_cons_cons s s' s'' p''))
        subst hm; subst hm'
        -- Now s' : WalkStep _ 2 2.
        match s' with
        | .forward h => exact absurd h G_witness_E_no_22
        | .backward h => exact absurd h G_witness_E_no_22
        | .bidir h => exact h.elim

/-! ### `marg.L = ∅` for `G_witness`

Every candidate bidirected edge in `G_witness.marginalize {2}` is
excluded by one of the two directed-walk clauses of
`mem_marginalize_L`. Bifurcation walks with interior in `{2}` have
length ≤ 2 (by `walk_interior_2_length_le_2`), and each
length-≤-2 bifurcation produces a directed walk in some direction
with interior in `{2}`, contradicting the exclusion. -/

/-- Helper: extract a directed walk from a single edge
`(x, y) ∈ G_witness.E`. -/
private lemma directed_walk_of_edge {x y : Fin 6}
    (h : (x, y) ∈ G_witness.E) :
    ∃ ρ : Walk G_witness x y, ρ.IsDirected ∧ ρ.InteriorIn {2} := by
  refine ⟨Walk.cons (WalkStep.forward h) (Walk.nil y), ?_, ?_⟩
  · simp [Walk.IsDirected]
  · intro v hv
    simp [Walk.support, List.dropLast] at hv

/-- Helper: extract a directed walk `x → 2 → y` from edges
`(x, 2), (2, y) ∈ G_witness.E`. -/
private lemma directed_walk_through_2 {x y : Fin 6}
    (h1 : (x, 2) ∈ G_witness.E) (h2 : (2, y) ∈ G_witness.E) :
    ∃ ρ : Walk G_witness x y, ρ.IsDirected ∧ ρ.InteriorIn {2} := by
  refine ⟨Walk.cons (WalkStep.forward h1)
            (Walk.cons (WalkStep.forward h2) (Walk.nil y)), ?_, ?_⟩
  · simp [Walk.IsDirected]
  · intro v hv
    -- support = [x, 2, y], tail.dropLast = [2]. So v = 2.
    simp [Walk.support, List.dropLast] at hv
    exact hv ▸ rfl

/-- A bifurcation walk in `G_witness` with interior in `{2}`
gives a directed walk in some direction. Combined with
`walk_interior_2_length_le_2`, this handles all bifurcation
cases. -/
private lemma bifurcation_interior_2_gives_directed :
    ∀ {a b : Fin 6} (π : Walk G_witness a b),
      π.IsBifurcation → π.InteriorIn {2} →
      (∃ ρ : Walk G_witness a b, ρ.IsDirected ∧ ρ.InteriorIn {2}) ∨
      (∃ ρ : Walk G_witness b a, ρ.IsDirected ∧ ρ.InteriorIn {2}) := by
  intro a b π hbif hint
  obtain ⟨_, _, _, ⟨bw⟩⟩ := hbif
  -- Destructure the BifurcationWitness fields explicitly.
  obtain ⟨m, m', leftArm, hinge, rightArm, decompose, leftBackward,
          hingeIntoSource, rightDirected⟩ := bw
  -- π = leftArm.append (Walk.cons hinge rightArm).
  -- Bound length via walk_interior_2_length_le_2.
  have hlen_le : π.length ≤ 2 := walk_interior_2_length_le_2 π hint
  have hπ_eq_len : π.length = leftArm.length + 1 + rightArm.length := by
    have h_eq := congrArg Walk.length decompose
    simp [Walk.length_append, Walk.length_cons] at h_eq
    omega
  have h_la_le : leftArm.length ≤ 1 := by omega
  have h_ra_le : rightArm.length ≤ 1 := by omega
  -- Case on leftArm.
  cases leftArm with
  | nil v' =>
    -- leftArm = nil v'. So m = v' = a.
    -- Case on rightArm.
    cases rightArm with
    | nil _ =>
      -- Total walk is just the hinge step.
      -- hinge : WalkStep G_witness a b (since m = a, m' = b).
      -- HasArrowheadAtSource → backward or bidir; bidir impossible (L = ∅).
      cases hinge with
      | forward _ => simp [WalkStep.HasArrowheadAtSource] at hingeIntoSource
      | bidir hL => exact hL.elim
      | backward h_hinge =>
        -- h_hinge : a ⟵[G_witness] b, i.e., (b, a) ∈ G_witness.E.
        right
        exact directed_walk_of_edge h_hinge
    | @cons _ m_ra _ s_ra p_ra =>
      -- rightArm = cons s_ra p_ra, length ≥ 1. p_ra must have length 0.
      have h_pra_len : p_ra.length = 0 := by
        simp [Walk.length_cons] at h_ra_le; omega
      -- s_ra : WalkStep G_witness m' m_ra, forward (rightArm directed).
      cases s_ra with
      | backward _ => simp [Walk.IsDirected] at rightDirected
      | bidir _ => simp [Walk.IsDirected] at rightDirected
      | forward h_sra =>
        -- p_ra has length 0, so p_ra = nil m_ra, forcing m_ra = b.
        cases p_ra with
        | nil _ =>
          -- m_ra = b (from nil's typing). h_sra : (m', b) ∈ G_witness.E.
          -- Hinge from a to m', backward (forced by L = ∅).
          cases hinge with
          | forward _ => simp [WalkStep.HasArrowheadAtSource] at hingeIntoSource
          | bidir hL => exact hL.elim
          | backward h_hinge =>
            -- h_hinge : a ⟵[G_witness] m', i.e., (m', a) ∈ E.
            -- m' is in the interior of π. Show m' = 2.
            have hm'_in : m' ∈ π.support.tail.dropLast := by
              rw [decompose]
              simp only [Walk.nil_append]
              -- π reduced to cons (backward h_hinge) (cons (forward h_sra) (nil b))
              exact support_tail_dropLast_cons_cons
                (WalkStep.backward h_hinge) (WalkStep.forward h_sra) (Walk.nil b)
            have hm'_2 : m' = 2 := Set.mem_singleton_iff.mp (hint _ hm'_in)
            subst hm'_2
            -- Now: (2, a) ∈ E, (2, b) ∈ E. Fork case.
            have ha_in : a = 3 ∨ a = 4 := G_witness_E_out_of_2 _ h_hinge
            have hb_in : b = 3 ∨ b = 4 := G_witness_E_out_of_2 _ h_sra
            rcases ha_in with rfl | rfl
            · rcases hb_in with rfl | rfl
              · -- a = b = 3. Use 3 → 2 → 3.
                left
                exact directed_walk_through_2 G_witness_E_32 G_witness_E_23
              · -- a = 3, b = 4. Use 3 → 2 → 4.
                left
                exact directed_walk_through_2 G_witness_E_32 G_witness_E_24
            · rcases hb_in with rfl | rfl
              · -- a = 4, b = 3. Use 3 → 2 → 4 in the b → a direction.
                right
                exact directed_walk_through_2 G_witness_E_32 G_witness_E_24
              · -- a = b = 4. nil 4 is a length-0 directed walk.
                left
                refine ⟨Walk.nil 4, ?_, ?_⟩
                · simp [Walk.IsDirected]
                · intro v hv
                  simp [Walk.support, List.dropLast] at hv
        | @cons _ _ _ _ _ =>
          -- p_ra length ≥ 1, contradicts h_pra_len = 0.
          simp [Walk.length_cons] at h_pra_len
  | @cons _ m_la _ s_la p_la =>
    -- leftArm = cons s_la p_la, length ≥ 1.
    -- s_la : WalkStep G_witness a m_la, backward (leftArm all-backward).
    cases s_la with
    | forward _ => simp [Walk.IsAllBackward] at leftBackward
    | bidir _ => simp [Walk.IsAllBackward] at leftBackward
    | backward h_sla =>
      -- h_sla : a ⟵[G_witness] m_la, i.e., (m_la, a) ∈ E.
      -- leftArm.length ≤ 1, so p_la.length = 0.
      have h_pla_len : p_la.length = 0 := by
        simp [Walk.length_cons] at h_la_le; omega
      cases p_la with
      | nil _ =>
        -- p_la = nil, so m = m_la (the cases unifies them; m_la is replaced by m).
        -- Total length = 1 + 1 + rightArm.length ≤ 2 → rightArm.length = 0.
        have h_ra_zero : rightArm.length = 0 := by
          rw [Walk.length_cons, Walk.length_nil] at hπ_eq_len
          omega
        cases rightArm with
        | nil _ =>
          -- rightArm = nil, so m' = b.
          -- Hinge : WalkStep G_witness m b, backward.
          cases hinge with
          | forward _ => simp [WalkStep.HasArrowheadAtSource] at hingeIntoSource
          | bidir hL => exact hL.elim
          | backward h_hinge =>
            -- h_hinge : m ⟵[G_witness] b, i.e., (b, m) ∈ E.
            -- m is interior: extract m = 2.
            have hm_in : m ∈ π.support.tail.dropLast := by
              rw [decompose]
              -- π = (cons (.backward h_sla) (nil m)).append (cons (.backward h_hinge) (nil b))
              -- = cons (.backward h_sla) (cons (.backward h_hinge) (nil b))
              simp only [Walk.cons_append, Walk.nil_append]
              exact support_tail_dropLast_cons_cons
                (WalkStep.backward h_sla) (WalkStep.backward h_hinge) (Walk.nil b)
            have hm_2 : m = 2 := Set.mem_singleton_iff.mp (hint _ hm_in)
            subst hm_2
            -- Now: h_sla : (2, a) ∈ E, h_hinge : (b, 2) ∈ E.
            -- Directed walk b → 2 → a.
            right
            exact directed_walk_through_2 h_hinge h_sla
        | @cons _ _ _ _ _ =>
          -- rightArm length ≥ 1, contradicts h_ra_zero.
          simp [Walk.length_cons] at h_ra_zero
      | @cons _ _ _ _ _ =>
        -- p_la length ≥ 1, contradicts h_pla_len.
        simp [Walk.length_cons] at h_pla_len

/-- `(G_witness.marginalize {2}).L = ∅`: no bidirected edges in
the marginalization. Every candidate pair is excluded by a
directed-walk clause via `bifurcation_interior_2_gives_directed`. -/
private lemma marg_L_empty :
    ∀ (p : Fin 6 × Fin 6), p ∉ (G_witness.marginalize {2}).L := by
  intro p hp
  rw [CDMG.mem_marginalize_L] at hp
  obtain ⟨_, _, _, hno12, hno21, hbif_or⟩ := hp
  rcases hbif_or with ⟨π, hbif, hint⟩ | ⟨π, hbif, hint⟩
  · -- Bifurcation π : Walk G_witness p.1 p.2 with interior in {2}.
    rcases bifurcation_interior_2_gives_directed π hbif hint with
      ⟨ρ, hρdir, hρint⟩ | ⟨ρ, hρdir, hρint⟩
    · exact hno12 ⟨ρ, hρdir, hρint⟩
    · exact hno21 ⟨ρ, hρdir, hρint⟩
  · -- Bifurcation π : Walk G_witness p.2 p.1.
    rcases bifurcation_interior_2_gives_directed π hbif hint with
      ⟨ρ, hρdir, hρint⟩ | ⟨ρ, hρdir, hρint⟩
    · exact hno21 ⟨ρ, hρdir, hρint⟩
    · exact hno12 ⟨ρ, hρdir, hρint⟩

/-! ### `AncSet^marg({1, 3})` characterization

We need `5 ∉ G_witness.marginalize {2}).AncSet {1, 3}`. Since
the only way for `5` to be in this set is for `5 ∈ Anc^marg(v)`
for `v ∈ {1, 3}`, which requires a directed walk from `5` to
`v`. But `5` has no outgoing edges in `marg.E` (proven via
`marg_E_out_of_5`), so no directed walk of length ≥ 1 from `5`
exists. The trivial walk `nil 5` reaches only `5`, not `1` or `3`. -/

/-- `5 ∉ AncSet^{marg{2}}({1, 3})`. -/
private lemma five_not_in_AncSet_C :
    (5 : Fin 6) ∉ (G_witness.marginalize {2}).AncSet C_witness := by
  intro h
  rw [CDMG.mem_AncSet] at h
  obtain ⟨v, hvC, hv⟩ := h
  rw [CDMG.mem_Anc] at hv
  obtain ⟨_, π, hπ_dir⟩ := hv
  -- π : Walk (marg{2}) 5 v with π.IsDirected. v ∈ {1, 3}.
  -- A directed walk from 5 has first step forward (5, _) ∈ marg.E.
  -- But marg_E_out_of_5 says no such edge. So π has length 0.
  -- Length 0 means v = 5. But v ∈ {1, 3}, so v ≠ 5.
  cases π with
  | nil _ =>
    -- v = 5 (from nil's typing).
    simp [C_witness, Set.mem_insert_iff, Set.mem_singleton_iff] at hvC
  | @cons _ m _ s p =>
    -- First step s : WalkStep _ 5 m. IsDirected requires s = forward.
    cases s with
    | backward _ => simp [Walk.IsDirected] at hπ_dir
    | bidir _ => simp [Walk.IsDirected] at hπ_dir
    | forward h_5m =>
      -- h_5m : (5, m) ∈ (marg{2}).E. Contradicts marg_E_out_of_5.
      exact marg_E_out_of_5 _ h_5m

/-! ### `Sc^{marg{2}}` characterization at `1` and `3` -/

/-- Generalized: no directed walk exists in `(G_witness.marginalize {2})`
from `4` to any vertex that is neither `4` nor `5`. The walk is forced
to start with the forward step `4 → 5` (only outgoing edge from `4` in
`marg.E`), after which it can only end at `5` (no outgoing edges from
`5` in `marg.E`). -/
private lemma not_directed_marg_walk_from_4_to_non_45
    {v : Fin 6} (hv4 : v ≠ 4) (hv5 : v ≠ 5)
    (π : Walk (G_witness.marginalize {2}) 4 v) (hdir : π.IsDirected) :
    False := by
  cases π with
  | nil _ => exact hv4 rfl
  | @cons _ m _ s p =>
    cases s with
    | backward _ => simp [Walk.IsDirected] at hdir
    | bidir _ => simp [Walk.IsDirected] at hdir
    | forward h_4m =>
      have hm5 := marg_E_out_of_4 _ h_4m
      subst hm5
      have hp_dir : p.IsDirected := by
        simp [Walk.IsDirected] at hdir; exact hdir
      cases p with
      | nil _ => exact hv5 rfl
      | @cons _ m' _ s' _ =>
        cases s' with
        | backward _ => simp [Walk.IsDirected] at hp_dir
        | bidir _ => simp [Walk.IsDirected] at hp_dir
        | forward h_5m' => exact marg_E_out_of_5 _ h_5m'

/-- `4 ∉ Sc^{marg{2}}(1)`: if `4 ∈ Anc^marg(1)`, then there's a directed
walk from `4` to `1` in `marg`. But by
`not_directed_marg_walk_from_4_to_non_45` (`1 ≠ 4` and `1 ≠ 5`), no
such walk exists. -/
private lemma four_not_in_Sc_one_marg :
    (4 : Fin 6) ∉ (G_witness.marginalize {2}).Sc 1 := by
  intro h
  rw [CDMG.mem_Sc] at h
  obtain ⟨h_anc, _⟩ := h
  rw [CDMG.mem_Anc] at h_anc
  obtain ⟨_, π, hπ_dir⟩ := h_anc
  exact not_directed_marg_walk_from_4_to_non_45 (by decide) (by decide) π hπ_dir

/-- `4 ∉ Sc^{marg{2}}(3)`: analogous via the same generalized helper
applied at vertex `3`. -/
private lemma four_not_in_Sc_three_marg :
    (4 : Fin 6) ∉ (G_witness.marginalize {2}).Sc 3 := by
  intro h
  rw [CDMG.mem_Sc] at h
  obtain ⟨h_anc, _⟩ := h
  rw [CDMG.mem_Anc] at h_anc
  obtain ⟨_, π, hπ_dir⟩ := h_anc
  exact not_directed_marg_walk_from_4_to_non_45 (by decide) (by decide) π hπ_dir

/-! ### The RHS proof: every walk in `marg{2}` from `0` to `5` is σ-blocked

We use `Walk.reverse` and `isSigmaBlocked_reverse_iff`: it
suffices to show `π.reverse : Walk (marg{2}) 5 0` is σ-blocked.
We then analyze `π.reverse`'s first two steps.

- Step `s_0 : WalkStep _ 5 m_0`: forward and bidir are impossible
  (no outgoing from 5 in marg.E; no L). Backward forces `m_0 = 4`.
- Step `s_1 : WalkStep _ 4 m_1`: forward forces `m_1 = 5` (Case B);
  backward forces `m_1 ∈ {1, 3}` (Case A); bidir impossible.

**Case A** (`m_1 ∈ {1, 3}`): Position 2 of `π.reverse` = `m_1 ∈ C`.
The step out is backward (`s_1`), so it has source-arrow at `m_1`.
The step in is `s_0` (backward), with target arrow at... wait,
`s_0` is the step INTO position 1, not position 2. Let me re-trace:
position 2 of `π_rev` has step-in = `s_1` and step-out = `s_2`.

Actually `s_1.HasArrowheadAtTarget` is False (backward step), so
position 2 is NOT a collider. It's a non-collider. For
unblockability: step-out `s_2.IsForward` would require target ∈
`Sc^marg(m_1)`. We use the SCC lemmas. Step-in `s_1.IsBackward`
requires `s_0_predecessor` ∈ `Sc^marg(m_1)`. Either way, since
`4 ∉ Sc^marg(1)` and `4 ∉ Sc^marg(3)`, position 2 is blockable.
And `m_1 ∈ C`. So σ-BLOCKED.

**Case B** (`m_1 = 5`): position 2 of `π_rev` = `5`. Step-in `s_1`
forward, target arrow at 5. Step-out `s_2` from 5: must be
backward to 4 (other options impossible). So position 2 is a
collider. But `5 ∉ AncSet^marg(C)`. σ-BLOCKED. -/

/-- The key RHS lemma: any walk `π : Walk (marg{2}) 0 5` is
`{1, 3}`-σ-blocked. -/
private lemma walk_0_to_5_marg_isSigmaBlocked
    (π : Walk (G_witness.marginalize {2}) 0 5) :
    π.IsSigmaBlocked C_witness := by
  -- Strategy: reverse π and analyze π.reverse's first two steps.
  rw [← Walk.isSigmaBlocked_reverse_iff]
  -- Goal: π.reverse.IsSigmaBlocked C_witness.
  -- π.reverse : Walk (marg{2}) 5 0. nil case impossible (5 ≠ 0).
  cases π.reverse with
  | @cons _ m_0 _ s_0 p_0 =>
    -- s_0 : WalkStep (marg{2}) 5 m_0.
    cases s_0 with
    | forward h_50 =>
      exact absurd h_50 (marg_E_out_of_5 _)
    | bidir h_50L =>
      exact absurd h_50L (marg_L_empty _)
    | backward h_m0_5 =>
      -- h_m0_5 : (m_0, 5) ∈ marg.E. By marg_E_into_5, m_0 = 4.
      have hm0 : m_0 = 4 := marg_E_into_5 _ h_m0_5
      subst hm0
      -- Now p_0 : Walk (marg{2}) 4 0. nil case impossible (4 ≠ 0).
      cases p_0 with
      | @cons _ m_1 _ s_1 p_1 =>
        -- s_1 : WalkStep (marg{2}) 4 m_1.
        cases s_1 with
        | bidir h_4L =>
          exact absurd h_4L (marg_L_empty _)
        | backward h_m1_4 =>
          -- h_m1_4 : (m_1, 4) ∈ marg.E. By marg_E_into_4, m_1 ∈ {1, 3}.
          -- Case A.
          have hm1 := marg_E_into_4 _ h_m1_4
          -- Position 2 of πr (in reversed walk) corresponds to nodeAt 2 = m_1.
          -- Show position 2 is a blockable non-collider in C.
          right
          refine ⟨2, ?_, ?_⟩
          · -- π_rev.IsBlockableNonColliderAt 2.
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · -- 2 ≤ length: walk has at least 3 vertices (5, 4, m_1, ...).
              -- cons (backward h_m0_5) (cons (backward h_m1_4) p_1) has length ≥ 2.
              -- So 2 ≤ this length.
              simp [Walk.length]
            · -- Not a collider.
              -- Position 2 of (cons s_0 (cons s_1 p_1)) → cons _ p_1 at position 1 → ...
              -- Use `isColliderAt_cons_cons_succ_succ`: position 2 = (k+2 with k=0)
              -- shifts to position 1 of (cons s_1 p_1).
              -- We need ¬ collider at position 1 of (cons (backward h_m1_4) p_1).
              -- For this to be a non-collider, we need step_in (s_1 = backward)
              -- has HasArrowheadAtTarget = False. So we're a non-collider.
              -- Hmm wait, "collider at position 1 of cons s_1 p_1" requires
              -- s_1.HasArrowheadAtTarget AND first_step_of_p_1.HasArrowheadAtSource.
              -- s_1 = backward has HasArrowheadAtTarget = False.
              -- So the conjunction is False → not a collider.
              -- Let's break out cases of p_1.
              -- Use rcases hm1 first to fix m_1, then nil case becomes auto-impossible.
              rcases hm1 with rfl | rfl
              · -- m_1 = 1. cases p_1: nil impossible (1 ≠ 0).
                cases p_1 with
                | @cons _ m_2 _ s_2 p_2 =>
                  simp only [Walk.isColliderAt_cons_cons_succ_succ,
                             Walk.isColliderAt_cons_cons_one]
                  intro ⟨h1, _⟩
                  simp [WalkStep.HasArrowheadAtTarget] at h1
              · -- m_1 = 3. cases p_1: nil impossible (3 ≠ 0).
                cases p_1 with
                | @cons _ m_2 _ s_2 p_2 =>
                  simp only [Walk.isColliderAt_cons_cons_succ_succ,
                             Walk.isColliderAt_cons_cons_one]
                  intro ⟨h1, _⟩
                  simp [WalkStep.HasArrowheadAtTarget] at h1
            · -- ¬ Unblockable: need the unblockable conjunct to fail.
              intro h_unblock
              rcases hm1 with rfl | rfl
              · -- m_1 = 1.
                cases p_1 with
                | @cons _ m_2 _ s_2 p_2 =>
                  simp only [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ,
                             Walk.isUnblockableNonColliderAt_cons_cons_one] at h_unblock
                  obtain ⟨_, h_bw_clause, _⟩ := h_unblock
                  have h_4_in_Sc : (4 : Fin 6) ∈ (G_witness.marginalize {2}).Sc 1 :=
                    h_bw_clause (by simp [WalkStep.IsBackward])
                  exact four_not_in_Sc_one_marg h_4_in_Sc
              · -- m_1 = 3.
                cases p_1 with
                | @cons _ m_2 _ s_2 p_2 =>
                  simp only [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ,
                             Walk.isUnblockableNonColliderAt_cons_cons_one] at h_unblock
                  obtain ⟨_, h_bw_clause, _⟩ := h_unblock
                  have h_4_in_Sc : (4 : Fin 6) ∈ (G_witness.marginalize {2}).Sc 3 :=
                    h_bw_clause (by simp [WalkStep.IsBackward])
                  exact four_not_in_Sc_three_marg h_4_in_Sc
          · -- nodeAt 2 ∈ C_witness.
            -- Position 2 of (cons s_0 (cons s_1 p_1)) reduces to p_1.nodeAt 0 = m_1.
            simp only [Walk.nodeAt_cons_succ]
            rw [Walk.nodeAt_zero]
            rcases hm1 with rfl | rfl
            · -- m_1 = 1.
              simp [C_witness, Set.mem_insert_iff, Set.mem_singleton_iff]
            · -- m_1 = 3.
              simp [C_witness, Set.mem_insert_iff, Set.mem_singleton_iff]
        | forward h_4m1 =>
          -- h_4m1 : (4, m_1) ∈ marg.E. By marg_E_out_of_4, m_1 = 5. Case B.
          have hm1 := marg_E_out_of_4 _ h_4m1
          subst hm1
          -- Now p_1 : Walk (marg{2}) 5 0. nil case impossible (5 ≠ 0).
          cases p_1 with
          | @cons _ m_2 _ s_2 p_2 =>
            -- s_2 : WalkStep (marg{2}) 5 m_2. Force backward.
            cases s_2 with
            | forward h_5m2 =>
              exact absurd h_5m2 (marg_E_out_of_5 _)
            | bidir h_5L =>
              exact absurd h_5L (marg_L_empty _)
            | backward h_m2_5 =>
              -- h_m2_5 : (m_2, 5) ∈ marg.E. By marg_E_into_5, m_2 = 4.
              have hm2 := marg_E_into_5 _ h_m2_5
              subst hm2
              -- Position 2 of the full reversed walk is the joint between s_1 and s_2.
              -- nodeAt 2 = 5. s_1 forward (target arrow at 5). s_2 backward (source arrow at 5).
              -- COLLIDER at 5. 5 ∉ AncSet^marg(C).
              left
              refine ⟨2, ?_, ?_⟩
              · -- Collider at position 2.
                simp only [Walk.isColliderAt_cons_cons_succ_succ,
                           Walk.isColliderAt_cons_cons_one]
                refine ⟨?_, ?_⟩
                · simp [WalkStep.HasArrowheadAtTarget]
                · simp [WalkStep.HasArrowheadAtSource]
              · -- nodeAt 2 ∉ AncSet^marg(C_witness). Position 2 of the walk = 5.
                simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero]
                exact five_not_in_AncSet_C



/-- The RHS direction of the disproof:
`(G_witness.marginalize {2}).IsISigmaSeparated {0} {5} C_witness`.
Every walk in `(G_witness.marginalize {2})` from `0` to `5` is
`C_witness`-σ-blocked by `walk_0_to_5_marg_isSigmaBlocked`. -/
private lemma marg_isISigmaSeparated_G_witness :
    (G_witness.marginalize {2}).IsISigmaSeparated {0} {5} C_witness := by
  -- IsISigmaSeparated unfolds to: ∀ v w, v ∈ A → w ∈ J ∪ B → ∀ π, π.IsSigmaBlocked C.
  intro v w hv hw π
  -- v ∈ {0}: v = 0. w ∈ (marg{2}).J ∪ {5} = ∅ ∪ {5} = {5}: w = 5.
  rw [Set.mem_singleton_iff] at hv
  subst hv
  -- (marg{2}).J = G.J = ∅. So hw : w ∈ ∅ ∪ {5}, hence w = 5.
  have hw5 : w = 5 := by
    rw [CDMG.marginalize_J] at hw
    simp at hw
    rcases hw with h5 | hJ
    · exact h5
    · exact hJ.elim
  subst hw5
  exact walk_0_to_5_marg_isSigmaBlocked π

/-- claim_3_25 (`ISigmaSeparation` row): the LN's
`lem:stability_separation_marginalization` is **false** under
the Lean encoding of `CDMG.marginalize`. See the `## DISPROVE
MODE` section above for the audit trail. The proof here exhibits
the existential counter-example. -/
theorem isISigmaSeparated_marginalize_iff_disproved :
    ∃ (G : CDMG (Fin 6)) (A B C D : Set (Fin 6)),
      D ⊆ G.V ∧ Disjoint D (A ∪ B ∪ C) ∧
      ¬ (G.IsISigmaSeparated A B C ↔
           (G.marginalize D).IsISigmaSeparated A B C) := by
  refine ⟨G_witness, {0}, {5}, C_witness, {2}, ?_, ?_, ?_⟩
  · -- D = {2} ⊆ G_witness.V = {0, 1, 2, 3, 4, 5}.
    intro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact G_witness_V_univ 2
  · -- Disjoint {2} ({0} ∪ {5} ∪ {1, 3}).
    rw [Set.disjoint_singleton_left]
    simp [C_witness, Set.mem_insert_iff, Set.mem_singleton_iff]
  · -- ¬ (LHS ↔ RHS). LHS-side: ¬ G.IsISigmaSeparated. RHS-side:
    -- marg.IsISigmaSeparated. iff forces RHS → LHS, contradicting both.
    intro hiff
    exact not_isISigmaSeparated_G_witness (hiff.mpr marg_isISigmaSeparated_G_witness)

end CDMG

end Causality
