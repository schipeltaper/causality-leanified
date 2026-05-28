import Chapter3_GraphTheory.Section3_2.Marginalization
import Chapter3_GraphTheory.Section3_3.ISigmaSeparation

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

/-- claim_3_25 (`ISigmaSeparation` row, file
`ISigmaSeparationMarginalization.lean`): $i\sigma$-separation
is *stable* under marginalisation by any set $D \subseteq G.V$
of output nodes disjoint from $A \cup B \cup C$.

That is, with `hDV : D ⊆ G.V` and `hDdisj : Disjoint D
(A ∪ B ∪ C)`,
`G.IsISigmaSeparated A B C ↔
  (G.marginalize D).IsISigmaSeparated A B C`. The LN's
notation is "$A \isPerp_G B \given C \iff
A \isPerp_{G^{\sm D}} B \given C$"; the LN's
$D \cap (A \cup B \cup C) = \emptyset$ side-condition is
encoded as mathlib's `Disjoint` (matching the
`Disjoint W₁ W₂` precedent of `marginalize_marginalize`).
The contrapositive
"$A \nisPerp_G B \given C \iff A \nisPerp_{G^{\sm D}} B \given C$"
follows by `Iff.not` (`not_congr`) at the call site and is
not stated separately.

This is the foundational stability theorem of section 3.3;
chapters 5 (do-calculus Rule 1), 6 -- 7 (ID algorithm and
adjustment criteria), 8 -- 10 (iSCMs and counterfactual
identification), and 11 -- 16 (FCI / ICDF discovery) all
pivot through it when restricting attention to relevant
sub-CDMGs. -/
theorem isISigmaSeparated_marginalize_iff (G : CDMG α)
    (A B C D : Set α) (hDV : D ⊆ G.V)
    (hDdisj : Disjoint D (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C ↔
      (G.marginalize D).IsISigmaSeparated A B C := by
  sorry

end CDMG

end Causality
