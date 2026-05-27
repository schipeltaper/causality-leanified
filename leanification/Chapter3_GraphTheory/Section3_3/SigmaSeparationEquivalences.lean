import Mathlib.Data.List.TFAE
import Chapter3_GraphTheory.Section3_3.ISigmaSeparation
import Chapter3_GraphTheory.Section3_3.SigmaOpenPathWalk

-- TeX statement: claim_3_24_statement_SigmaSeparationEquivalences.tex
-- TeX proof:     claim_3_24_proof_SigmaSeparationEquivalences.tex

/-!
# $i\sigma$-separation equivalences (claim_3_24)

This file formalises *claim 3.24* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1395 -- 1412): a `\begin{claimmark}` *Remark* sitting
immediately after Proposition `prp:sigma_opens` (= claim_3_23,
`Causality.CDMG.sigmaOpens_TFAE`) and drawing two corollaries
from it. The block reads:

> 1. By Proposition `prp:sigma_opens` we have that
>    $A \isPerp_G B \given C$ is equivalent to either of the
>    following:
>    (a) every walk from a node in $A$ to a node in $J \cup B$
>        is $C$-$\sigma$-blocked by $C$;
>    (b) every path from a node in $A$ to a node in $J \cup B$
>        is $C$-$\sigma$-blocked by $C$.
> 2. Proposition `prp:sigma_opens` also shows that if
>    $A \nisPerp_G B \given C$ holds then:
>    (a) there exists a (shortest) $C$-$\sigma$-open path from
>        a node in $A$ to a node in $J \cup B$;
>    (b) there exists a (shortest) $C$-$\sigma$-open walk from
>        a node in $A$ to a node in $J \cup B$ such that all
>        its colliders lie in $C$.
> In practice we usually check if every path is $C$-$\sigma$-
> blocked or not. ...

The LN's two numbered items each contain three semantically-
distinct surfaces (the predicate name `IsISigmaSeparated` /
`IsNotISigmaSeparated`, the LN-prose "every walk" /
"$\sigma$-open path" universal, and the LN-prose "every path"
/ "$\sigma$-open walk with colliders in $C$" universal); we
encode each item as a single `List.TFAE` of three clauses, in
the LN's order. That keeps the LN's "is equivalent to either of
the following" / "shows that ... [any of these three things
hold]" idiom one-to-one with the Lean shape and lets call sites
extract any pair-equivalence via `.out i j` projections on a
single named theorem.

This file formalises **the statements only**; both proof
bodies are `sorry`. The proof is the future Manager-B prover's
job; the substantive direction in each TFAE -- "every walk
universal $\leftrightarrow$ every path universal" in item 1,
and "$\sigma$-open path existence $\leftrightarrow$ $\sigma$-
open-walk-with-colliders-in-$C$ existence" in item 2 -- factors
through the corresponding clause-pair extraction on
`sigmaOpens_TFAE`. The first clause of each TFAE (the predicate
name vs. its unfolded universal) is `Iff.rfl` against the
defining-equation `isISigmaSeparated_iff` /
`isNotISigmaSeparated_iff`.

## What this file contributes

Two `theorem`s in `namespace Causality.CDMG`, both stated as
`List.TFAE` of three clauses, both bodies `sorry`:

* `isISigmaSeparated_TFAE` (LN item 1): the three-way
  equivalence between
  (i) `G.IsISigmaSeparated A B C`,
  (ii) the unfolded "every walk from $A$ to $G.J \cup B$ is
       $C$-$\sigma$-blocked" universal -- definitionally
       identical to (i),
  (iii) the "every *path* from $A$ to $G.J \cup B$ is
        $C$-$\sigma$-blocked" universal -- the LN's clause 1(b).
* `isNotISigmaSeparated_TFAE` (LN item 2): the three-way
  equivalence between
  (i) `G.IsNotISigmaSeparated A B C`,
  (ii) existence of a $C$-$\sigma$-open *path* from a node in
       $A$ to a node in $G.J \cup B$ -- the LN's clause 2(a),
  (iii) existence of a $C$-$\sigma$-open *walk* from a node in
        $A$ to a node in $G.J \cup B$ all of whose colliders
        lie in $C$ -- the LN's clause 2(b).

The LN's parenthetical "(shortest)" in item 2(a) / 2(b) is a
strengthening that follows trivially from existence by
`Nat`-well-foundedness on `Walk.length`; we deliberately
encode existence only and document the deferral in the
per-theorem design block. Downstream consumers that need a
shortest witness can derive it via `Nat.find` on
`Walk.length`.

## Downstream usage

* **claim_3_25** ($i\sigma$-separation under marginalization,
  `graphs.tex` lines 1414 -- 1422) -- the LN's proof of the
  marginalization equivalence operates on $\sigma$-open
  *walks* in the marginalized graph and reads them back as
  $\sigma$-open walks (and then paths) in the original; the
  "every path is $\sigma$-blocked" clause of item 1 here is
  what lets the marginalization theorem be *stated* on the
  pragmatic-to-check path side while *proved* on the
  composable walk side. Item 2's existential-of-walk-with-
  colliders-in-$C$ clause is what the LN's proof actually
  hands the walk-splicing argument.
* **claim_3_26 / claim_3_27** ($i\sigma$-separation on acyclic
  graphs + `lem:replace_walk`, `graphs.tex` lines 1581 -- 1652)
  -- the acyclic-simplification corollary and the walk-
  replacement lemma both reason about $\sigma$-open walks
  with colliders in $C$ (the LN's item 2(b) surface), which
  is exactly clause 3 of `isNotISigmaSeparated_TFAE`.
* **Chapter 4 (CBNs, `causal_bayesian_networks.tex`)** -- the
  Markov property for a CBN equates conditional independence
  in the joint distribution to graphical $i\sigma$-separation.
  The CBN-Markov theorems are stated in terms of paths
  (rather than walks) because the path formulation is the one
  practitioners check (the LN's own pragmatic remark at
  `graphs.tex` line 1410: "in practice we usually check if
  every path is $C$-$\sigma$-blocked"); item 1 here is the
  bridge that lets those statements ride on top of
  `IsISigmaSeparated`'s walk universal.
* **Chapter 5 (do-calculus, `do-calculus.tex` +
  `proof-do-calculus.tex`)** -- the three do-calculus rules
  are stated *in terms of* `IsISigmaSeparated`. Whenever a
  rule is applied by exhibiting / refuting a $\sigma$-open
  path, item 1's "every path" surface is the natural target
  and item 2's "exists $\sigma$-open path" surface is the
  natural source.
* **Chapter 6 -- 7 (identification,
  `adjustment-criteria.tex` / `id-algorithm.tex`)** -- the
  backdoor / front-door / general adjustment criteria are
  most naturally stated as the *absence* of a $\sigma$-open
  path satisfying particular constraints; item 1's "every
  path" universal is precisely that absence.
* **Chapters 8 -- 10 (iSCMs, `scms.tex` -- `scms4.tex`)** --
  iSCMs inherit the CI-vs-separation equivalence through
  their CDMG; counterfactual identification builds on top
  and pivots through these equivalences whenever the
  separation premise is checked path-wise instead of
  walk-wise.
* **Chapters 11 -- 16 (discovery,
  `causal_relations.tex` / `minimal_sep_sets.tex` /
  `fci.tex`)** -- FCI's skeleton-phase and orientation-phase
  reasoning operate on *paths*, because there are only
  finitely many of them in a finite graph (the LN's own
  pragmatic remark). The path-side surface in both items is
  what FCI's algorithmic phases consume; the walk-side
  surface is what the LN's correctness proofs reason about.
  This row is the load-bearing bridge between the two.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.SigmaOpenPathWalk`
  (claim_3_23) -- the immediately preceding row in this
  subsection. Same one-row claim-file pattern with a
  `List.TFAE` of three clauses; this row's two TFAEs are
  *derived from* its single TFAE and inherit its naming
  conventions (`_TFAE` suffix, explicit `G C ...` argument
  order for dot-projection, clauses listed in the LN's
  numbered order). The substantive direction in each of our
  TFAEs eventually pivots through one of
  `sigmaOpens_TFAE`'s pair-extractions.
* `Chapter3_GraphTheory.Section3_3.SigmaSeparationSymmetric`
  (claim_3_22) -- another one-row claim-file in this
  subsection. Same module-docstring template
  ("What this file contributes" / "Downstream usage" /
  "Style precedents") and per-declaration design-block
  convention.
* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation`
  (def_3_18) -- source of `IsISigmaSeparated` /
  `IsNotISigmaSeparated` and their `_iff` `rfl`-lemmas. The
  per-`def` design block at `IsNotISigmaSeparated` (lines
  428 -- 462 in that file) explicitly anticipates this row
  in its "Downstream consequences" enumeration:
  *"claim_3_24: if $A \nisPerp_G B \given C$ holds, then
  there exists a (shortest) $C$-$\sigma$-open path from a
  node in $A$ to a node in $J \cup B$"*.
* Mathlib `Mathlib.Data.List.TFAE` -- source of `List.TFAE`,
  the formal embodiment of the LN's "the following are
  equivalent" idiom and the same TFAE machinery
  `sigmaOpens_TFAE` is stated on. Pairwise extraction at the
  call site is `.out i j`.

## Infrastructure note for the future prover

Both TFAEs reduce to `sigmaOpens_TFAE` plus boolean glue
(`isSigmaBlocked_iff_not_isSigmaOpen` for the De Morgan
between "every walk is $\sigma$-blocked" and "no $\sigma$-open
walk exists"; `not_not` / `Classical.not_forall` /
`not_exists` for pushing the negation through). No new
auxiliary lemma is needed:

* **`isISigmaSeparated_TFAE`** -- clauses 0 $\leftrightarrow$ 1
  is `Iff.rfl` against `isISigmaSeparated_iff`; clauses
  1 $\leftrightarrow$ 2 contraposes through the dual
  `isSigmaBlocked_iff_not_isSigmaOpen` and then through
  `(sigmaOpens_TFAE _ _ _ _).out 0 1`
  (path-existence $\leftrightarrow$ walk-existence).
* **`isNotISigmaSeparated_TFAE`** -- clauses 0 $\leftrightarrow$ 1
  pushes `¬ G.IsISigmaSeparated A B C` through
  `Classical.not_forall` three times (one for each of the
  three universals `v, w, π` in `IsISigmaSeparated`'s
  definition) and one application of
  `isSigmaBlocked_iff_not_isSigmaOpen`'s contrapositive to
  flip "not (every walk $\sigma$-blocked)" into "exists
  $\sigma$-open walk", then `(sigmaOpens_TFAE _ _ _ _).out 1 0`
  to convert that to "exists $\sigma$-open *path*"; clauses
  1 $\leftrightarrow$ 2 is `(sigmaOpens_TFAE _ _ _ _).out 0 2`
  composed with the surrounding existentials.

All infrastructure cited here -- `sigmaOpens_TFAE`,
`isSigmaBlocked_iff_not_isSigmaOpen`, the `_iff` `rfl`-lemmas
for `IsISigmaSeparated` and `IsNotISigmaSeparated` -- already
exists and is fully proved.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

-- claim_3_24 (item 1)
-- title: SigmaSeparationEquivalences -- the predicate-vs-walk-
--        universal-vs-path-universal three-way equivalence
--
-- `G.IsISigmaSeparated A B C` is equivalent to either of
-- (a) the unfolded "every walk from $A$ to $G.J \cup B$ is
--     $C$-$\sigma$-blocked" universal, which is *definitionally
--     identical* to the predicate (the `Iff.rfl` redundancy
--     between TFAE positions 0 and 1, see design block); or
-- (b) the corresponding "every *path* from $A$ to $G.J \cup B$
--     is $C$-$\sigma$-blocked" universal -- the LN's clause
--     1(b), the substantive equivalence of this item.
--
-- We package the three clauses as a single `List.TFAE` so the
-- LN's "is equivalent to either of the following" reads
-- structure-for-structure with the Lean shape; pair-extraction
-- at the call site is `.out i j`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_24, lines 1395 -- 1402, item 1 of the Remark):

  \begin{claimmark}
  \begin{Rem}
      \begin{enumerate}
          \item By Proposition \ref{prp:sigma_opens} we have
            that $A \isPerp_G B \given C$ is equivalent to
            either of the following:
    \begin{enumerate}
        \item every walk from a node in $A$ to a node in
              $J \cup B$ is $C$-$\sigma$-blocked by $C$;
        \item every path from a node in $A$ to a node in
              $J \cup B$ is $C$-$\sigma$-blocked by $C$.
    \end{enumerate}
  ...
  \end{Rem}
  \end{claimmark}
-/
--
-- ## Design choice
--
-- * **`List.TFAE` over three clauses, not a single
--   biconditional.** The LN's "is equivalent to either of the
--   following" lists two clauses (a) and (b) that are *both*
--   equivalent to the named predicate; `List.TFAE` over three
--   entries (the named predicate + both clauses) captures the
--   "any pair is mutually equivalent" reading directly, in the
--   same numbered-list shape the LN uses. A single biconditional
--   `IsISigmaSeparated ↔ (every path is $\sigma$-blocked)`
--   would discard clause (a) entirely or force an awkward
--   conjunction in the right-hand side. TFAE matches the LN
--   surface, scales to the future $id$-separation analogue
--   (`graphs.tex` line 1745 explicitly cites "a similar result"
--   for $d$-separation), and gives the same `.out i j`
--   call-site ergonomics that `sigmaOpens_TFAE` already
--   established for claim_3_23.
--
-- * **Position 0 = predicate name, position 1 = unfolded
--   universal -- the `Iff.rfl` redundancy.** Positions 0 and 1
--   in the TFAE are *definitionally* equivalent
--   (`isISigmaSeparated_iff` is `Iff.rfl`); we include the
--   unfolded form anyway because the LN's clause 1(a) "every
--   walk from a node in $A$ to a node in $J \cup B$ is
--   $C$-$\sigma$-blocked" is a *named clause of the LN's
--   numbered list* -- dropping it would silently weaken the
--   correspondence between the LN's item-1 structure and the
--   Lean shape. The hard rule "no `True` substitute for any
--   clause; if a clause is `Iff.rfl` against the predicate,
--   still include it as a list entry" is what binds us here.
--   The redundancy is a *feature*: callers wanting the
--   "unfolded" surface can write `.out 0 1` and receive a
--   one-line `Iff.rfl` lemma, while callers wanting the
--   substantive path-version write `.out 0 2` (or `.out 1 2`).
--
-- * **Strict-implicit `⦃v w : α⦄` vertex binders in clauses
--   1 and 2.** Mirrors `IsISigmaSeparated`'s own signature in
--   `ISigmaSeparation.lean` line 351 -- the unfolded clause
--   should be *literally* the same expression as the predicate
--   body so that `Iff.rfl` discharges the 0 $\leftrightarrow$ 1
--   pair. Plain `{ }`-implicit would type-check but break
--   `Iff.rfl` reduction.
--
-- * **Dropping "(shortest)" -- not in this item.** This item
--   is the "every walk / every path is $\sigma$-blocked"
--   surface, which has no shortest-witness analogue (a
--   universal, not an existential). The "(shortest)"
--   parenthetical lives only in item 2; see the design block
--   on `isNotISigmaSeparated_TFAE` for the deferral rationale.
--
-- * **Why *two* `TFAE`s in this file, not one bundled
--   five-clause `TFAE` and not four separate `Iff`s.** The LN
--   Remark's items 1 and 2 are about *complementary* predicates
--   -- item 1 about `IsISigmaSeparated`, item 2 about
--   `IsNotISigmaSeparated` -- and a single bundled "the
--   following five are equivalent" TFAE would conflate the
--   two: a `Prop` and its negation are never pairwise
--   equivalent, so the resulting list would not satisfy
--   `List.TFAE`'s "all entries mutually equivalent" semantics.
--   Conversely, dissolving each item into separately-named
--   biconditionals (one for "predicate ↔ unfolded universal",
--   one for "predicate ↔ unfolded path universal") would
--   proliferate the API for no reuse gain and lose the LN's
--   "is equivalent to either of the following" reading -- the
--   LN's enumeration names a *single* numbered item with two
--   sub-clauses, which a single `List.TFAE` mirrors 1:1. The
--   chosen mid-ground -- two TFAEs, one per LN-numbered-item
--   -- is the unique shape that preserves both the LN's local
--   structure and the `.out i j` call-site ergonomics already
--   established by `sigmaOpens_TFAE` (claim_3_23), on which
--   both of this file's TFAEs are downstream.
--
-- * **`G.J ∪ B`, not `B ∪ G.J`.** Mirrors the LN's "from a
--   node in $A$ to a node in $J \cup B$" verbatim and mirrors
--   `IsISigmaSeparated`'s own body (`ISigmaSeparation.lean`
--   line 351). The 0 $\leftrightarrow$ 1 `Iff.rfl` collapse
--   only works when the *literal expression* on both sides
--   matches; a `Set.union_comm`-rewritten `B ∪ G.J` form would
--   still be `Iff`-equivalent but no longer definitionally
--   equal to the predicate's body, breaking the `rfl` and
--   forcing a `simp` step into every downstream `.out 0 1`
--   consumer. The LN-verbatim union order is therefore
--   load-bearing, not cosmetic. Position 2's "every path"
--   clause inherits the same `G.J ∪ B` form for visual
--   consistency with positions 0 and 1.
--
-- * **Bridging note -- this Remark is a direct corollary of
--   `sigmaOpens_TFAE` (claim_3_23).** The substantive
--   1 $\leftrightarrow$ 2 direction (the LN's "every walk ↔
--   every path" content) contraposes through
--   `(sigmaOpens_TFAE _ _ _ _).out 0 1` together with the
--   De Morgan dual `isSigmaBlocked_iff_not_isSigmaOpen`; no
--   new auxiliary infrastructure is needed. The LN's own
--   "By Proposition `\ref{prp:sigma_opens}` we have that ..."
--   framing makes the dependency explicit, and the Lean shape
--   preserves it: a reader scanning this file should expect
--   the future proof to be straightforward TFAE chasing on
--   top of claim_3_23. See the module docstring's
--   "Infrastructure note for the future prover" section for
--   the full proof sketch.

/-- claim_3_24 (item 1, `SigmaSeparationEquivalences`): the
three-way equivalence between the `IsISigmaSeparated` predicate,
the unfolded "every walk from a node in `A` to a node in
`G.J ∪ B` is $C$-$\sigma$-blocked" universal (definitionally
identical to the predicate), and the LN's substantive "every
*path* from a node in `A` to a node in `G.J ∪ B` is
$C$-$\sigma$-blocked" universal. The 0 $\leftrightarrow$ 1
direction is `Iff.rfl` against `isISigmaSeparated_iff`; the
substantive 1 $\leftrightarrow$ 2 direction follows from
`sigmaOpens_TFAE`. Pairwise extraction is
`(G.isISigmaSeparated_TFAE A B C).out i j` for `i, j ∈ {0, 1, 2}`. -/
theorem isISigmaSeparated_TFAE (G : CDMG α) (A B C : Set α) :
    List.TFAE
      [ G.IsISigmaSeparated A B C,
        ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w),
          π.IsSigmaBlocked C,
        ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w),
          π.IsPath → π.IsSigmaBlocked C ] := by
  classical
  -- (0) ↔ (1): the predicate `IsISigmaSeparated` is definitionally
  -- the unfolded "every walk" universal -- `isISigmaSeparated_iff`
  -- is `Iff.rfl`. We record both directions explicitly so that
  -- `tfae_finish` can compose them.
  tfae_have h₁₂ : 1 → 2 := fun h => h
  tfae_have h₂₁ : 2 → 1 := fun h => h
  -- (1) ⇒ (2): a path is in particular a walk, so the universal
  -- over walks restricts to the universal over paths.
  tfae_have _h₂₃ : 2 → 3 := fun h v w hv hw π _hPath => h hv hw π
  -- (2) ⇒ (1): contrapositive via `sigmaOpens_TFAE` (the LN's
  -- prp:sigma_opens, walk-existence → path-existence -- here used
  -- in the "if any walk is σ-open then some path is σ-open" form).
  tfae_have _h₃₂ : 3 → 2 := by
    intro h v w hv hw π
    rw [Walk.isSigmaBlocked_iff_not_isSigmaOpen]
    intro hOpen
    have hWalk : ∃ π : Walk G v w, π.IsSigmaOpen C := ⟨π, hOpen⟩
    obtain ⟨π', hPath', hOpen'⟩ :=
      ((G.sigmaOpens_TFAE C v w).out 1 0).mp hWalk
    have hBlocked := h hv hw π' hPath'
    rw [Walk.isSigmaBlocked_iff_not_isSigmaOpen] at hBlocked
    exact hBlocked hOpen'
  tfae_finish

-- claim_3_24 (item 2)
-- title: SigmaSeparationEquivalences -- under negation, the
--        $\sigma$-open path / walk-with-colliders-in-$C$
--        existence equivalences
--
-- `G.IsNotISigmaSeparated A B C` (the LN's $\nisPerp_G$) is
-- equivalent to either of
-- (a) the existence of a $C$-$\sigma$-open *path* from a node
--     in $A$ to a node in $G.J \cup B$ -- the LN's clause 2(a);
-- (b) the existence of a $C$-$\sigma$-open *walk* from a node
--     in $A$ to a node in $G.J \cup B$ all of whose colliders
--     lie in $C$ -- the LN's clause 2(b).
--
-- The LN's parenthetical "(shortest)" is *not* baked in; see
-- the design block. Both substantive directions factor through
-- `sigmaOpens_TFAE`. We package the three clauses as a single
-- `List.TFAE`, paralleling item 1.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_24, lines 1404 -- 1412, item 2 of the Remark):

      \item Proposition \ref{prp:sigma_opens} also shows that
        if $A \nisPerp_G B \given C$ holds then:
    \begin{enumerate}
        \item there exists a (shortest) $C$-$\sigma$-open path
              from a node in $A$ to a node in $J \cup B$;
        \item there exists a (shortest) $C$-$\sigma$-open walk
              from a node in $A$ to a node in $J \cup B$ such
              that all its colliders lie in $C$.
    \end{enumerate}
    \end{enumerate}
    In practice we usually check if every path is
    $C$-$\sigma$-blocked or not. ...
-/
--
-- ## Design choice
--
-- * **TFAE over three clauses, not a one-way implication.** The
--   LN's "if $A \nisPerp_G B \given C$ holds then [either of
--   2(a), 2(b)]" reads on its face as a one-way implication
--   ("then there exists ..."). But the converse direction is
--   trivially true (a $\sigma$-open walk from $A$ to $J \cup B$
--   witnesses the failure of "every walk is $\sigma$-blocked",
--   which is exactly `¬ IsISigmaSeparated`); both clauses 2(a)
--   and 2(b) are full $\iff$'s with the negation predicate,
--   not just $\impliedby$'s. The LN's prose elides this because
--   it focuses on the *useful* direction (extracting a witness
--   from non-separation), but the underlying logical content is
--   bidirectional. Stating it as TFAE makes both directions
--   first-class and avoids the down-stream pattern of having
--   to re-derive the trivial converse at every call site.
--
-- * **Position 0 = `IsNotISigmaSeparated`, not the unfolded
--   `¬ IsISigmaSeparated`.** Mirrors item 1's "predicate name
--   in slot 0" convention. The `_iff` `rfl`-lemma
--   `isNotISigmaSeparated_iff` reduces the predicate to the
--   raw negation on demand inside the proof; the goal surface
--   keeps the LN's $\nisPerp_G$ symbol visible. (The
--   per-`def` design block on `IsNotISigmaSeparated` in
--   `ISigmaSeparation.lean` argues at length for the named-
--   negation surface; we honour that choice here.)
--
-- * **"(shortest)" deliberately dropped.** The LN's
--   parenthetical "(shortest)" in clauses 2(a) and 2(b) is a
--   *downstream strengthening* of plain existence: given any
--   $\sigma$-open path / collider-restricted walk, the
--   shortest one exists by `Nat`-well-foundedness on
--   `Walk.length` (well-ordering principle / `Nat.find` on
--   the set of lengths of witnesses). Baking "shortest" into
--   the existential here would (i) force every downstream
--   consumer who only needs *some* witness to discharge the
--   length-minimality side-condition, (ii) make the TFAE
--   shape non-uniform with `sigmaOpens_TFAE` (which is
--   stated on plain existence), and (iii) double-count the
--   well-foundedness derivation -- the LN's parenthetical
--   reads as "incidentally, one can sharpen this to the
--   shortest", not as "the substantive content is shortest-
--   existence". Downstream consumers needing minimality
--   derive it themselves via `Nat.find` on the length-of-
--   witness predicate; the chapter-$\ge 4$ discovery
--   algorithms (FCI's path-enumeration phases) that *do*
--   reason about shortest paths instantiate it on demand.
--
-- * **`∃ (v w : α) (π : Walk G v w), v ∈ A ∧ w ∈ G.J ∪ B
--   ∧ ...` for the existential clauses.** Explicit `(v w : α)`
--   binders on the existential (rather than strict-implicit
--   `⦃ ⦄` as in item 1's universal) because the existential
--   produces *witnesses* the call site destructures
--   (`obtain ⟨v, w, π, hv, hw, hOpen⟩ := ...`); strict-
--   implicit on an existential would force callers to fish
--   the vertices out of `π`'s type, which is awkward. The
--   membership-hypothesis order (`v ∈ A` before `w ∈ G.J ∪ B`)
--   mirrors the LN's "from a node in $A$ to a node in
--   $J \cup B$" reading.
--
-- * **Three nested existentials `∃ v, ∃ w, ∃ π, ...`,
--   *not* `∃ (vwπ : ...), ...` over a bundled triple.** Keeps
--   each witness destructurable separately at the call site
--   and avoids introducing a new bundled type. The triple is
--   "natural" only with the membership-hypotheses attached,
--   which is what the `∧` conjunctions in the body capture;
--   bundling without the hypotheses would be useless and
--   bundling with them would obscure the structure.
--
-- * **Position 0 $\leftrightarrow$ 1 is *not* `Iff.rfl`
--   here -- in contrast to item 1.** Item 1's positions 0
--   (`IsISigmaSeparated`) and 1 (the unfolded "every walk"
--   universal) reduce by `Iff.rfl` because the predicate body
--   literally *is* the universal. Item 2's positions 0
--   (`IsNotISigmaSeparated`, which is `Iff.rfl`-equal to
--   `¬ IsISigmaSeparated` -- see `isNotISigmaSeparated_iff`)
--   and 1 (∃ $\sigma$-open path) are *not* definitionally
--   equal: the bridge requires (a) pushing the negation
--   through the three nested universals of `IsISigmaSeparated`
--   via `Classical.not_forall`, (b) flipping "not every walk
--   $\sigma$-blocked" into "exists $\sigma$-open walk" via the
--   contrapositive of `isSigmaBlocked_iff_not_isSigmaOpen`,
--   then (c) converting "exists $\sigma$-open walk" to
--   "exists $\sigma$-open *path*" via
--   `(sigmaOpens_TFAE _ _ _ _).out 1 0`. We *deliberately*
--   keep the "position 0 = predicate name" convention so the
--   two TFAEs in this file feel symmetric at call sites
--   (both expose `.out 0 1` as "predicate ↔ first LN
--   sub-clause" and `.out 0 2` as "predicate ↔ second LN
--   sub-clause"). A reader following the future proof needs
--   to know that the cost is asymmetric across the two
--   TFAEs: item 1's `.out 0 1` is `Iff.rfl`, item 2's
--   `.out 0 1` carries the full substantive content of
--   `sigmaOpens_TFAE` together with three negation-through-
--   universal pushes.
--
-- * **`G.J ∪ B`, not `B ∪ G.J`.** Same as item 1 -- matches
--   the LN's "from a node in $A$ to a node in $J \cup B$"
--   verbatim and matches `IsISigmaSeparated`'s body, so when
--   the `Classical.not_forall` unfolding of position 0
--   exposes `∃ v w, v ∈ A ∧ w ∈ G.J ∪ B ∧ ¬...`, the
--   resulting structure aligns with positions 1 and 2
--   without an intervening `Set.union_comm` rewrite. Cross-
--   item visual consistency also matters: a reader pattern-
--   matching by eye between item 1's universal and item 2's
--   existential expects the `G.J ∪ B` clause to appear in the
--   same order on both sides, so the LN-faithful order is
--   load-bearing here too.
--
-- * **LN's collider-control asymmetry between clauses 2(a)
--   and 2(b) preserved exactly.** Clause 2(a) of the LN
--   ("there exists a (shortest) $C$-$\sigma$-open *path*")
--   asks *only* for $\sigma$-openness on the path witness;
--   clause 2(b) ("there exists a (shortest) $C$-$\sigma$-open
--   *walk* ... such that all its colliders lie in $C$") adds
--   the collider-control conjunct on the walk witness. This
--   asymmetry is not editorial -- it traces back to
--   `sigmaOpens_TFAE`'s own clauses: clauses (1)/(2) are
--   plain $\sigma$-open path / $\sigma$-open walk (no
--   collider-control), clause (3) is the $\sigma$-open walk
--   *with colliders-in-$C$* strengthening. Position 1 of
--   this TFAE mirrors `sigmaOpens_TFAE`'s position 0,
--   position 2 mirrors its position 2 -- so the LN's "path =
--   plain, walk = collider-controlled" pairing is preserved
--   literally. We do *not* (i) bake collider-control onto
--   position 1 (which would over-strengthen the path clause
--   beyond what the LN claims, and beyond what
--   `sigmaOpens_TFAE` directly delivers via `.out 0 1`),
--   nor (ii) drop it from position 2 (which would under-
--   state the walk clause and lose the downstream content
--   that `LabelRoman` / claim_3_27 and the acyclic-graph
--   corollary claim_3_26 explicitly consume -- both reason
--   about $\sigma$-open walks with colliders in $C$, never
--   plain $\sigma$-open walks).
--
-- * **Bridging note -- this Remark is a direct corollary of
--   `sigmaOpens_TFAE` (claim_3_23).** Both substantive
--   directions factor through claim_3_23: position 1
--   $\leftrightarrow$ 2 is `(sigmaOpens_TFAE _ _ _ _).out 0 2`
--   (path-existence ↔ walk-with-colliders-in-$C$-existence)
--   composed with the surrounding
--   `∃ v w, v ∈ A ∧ w ∈ G.J ∪ B ∧ ...` wrapper, and
--   position 0 $\leftrightarrow$ 1 unwinds
--   `¬ IsISigmaSeparated` to "exists $\sigma$-open walk"
--   (via `Classical.not_forall` and
--   `isSigmaBlocked_iff_not_isSigmaOpen`) then converts to
--   "exists $\sigma$-open path" via
--   `(sigmaOpens_TFAE _ _ _ _).out 1 0`. No new auxiliary
--   infrastructure is needed -- the proof is straightforward
--   TFAE chasing on top of claim_3_23 plus boolean glue. The
--   LN's "Proposition `\ref{prp:sigma_opens}` also shows that
--   if $A \nisPerp_G B \given C$ holds then ..." framing
--   makes this dependency explicit; the Lean shape preserves
--   it. See the module docstring's "Infrastructure note for
--   the future prover" section for the full proof sketch.

/-- claim_3_24 (item 2, `SigmaSeparationEquivalences`): under
the LN's $\nisPerp_G$ (`IsNotISigmaSeparated`), the three-way
equivalence between the negation predicate, the existence of a
$C$-$\sigma$-open *path* from a node in `A` to a node in
`G.J ∪ B`, and the existence of a $C$-$\sigma$-open *walk* from
a node in `A` to a node in `G.J ∪ B` all of whose colliders lie
in `C`. Substantive direction follows from `sigmaOpens_TFAE`
via De Morgan on `isSigmaBlocked_iff_not_isSigmaOpen`. The LN's
parenthetical "(shortest)" is dropped; downstream consumers
derive minimality via `Nat.find` on `Walk.length`. Pairwise
extraction is `(G.isNotISigmaSeparated_TFAE A B C).out i j` for
`i, j ∈ {0, 1, 2}`. -/
theorem isNotISigmaSeparated_TFAE (G : CDMG α) (A B C : Set α) :
    List.TFAE
      [ G.IsNotISigmaSeparated A B C,
        ∃ (v w : α) (π : Walk G v w),
          v ∈ A ∧ w ∈ G.J ∪ B ∧ π.IsPath ∧ π.IsSigmaOpen C,
        ∃ (v w : α) (π : Walk G v w),
          v ∈ A ∧ w ∈ G.J ∪ B ∧ π.IsSigmaOpen C ∧
            ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C ] := by
  classical
  -- (0) ⇒ (1): the substantive direction. Push the negation
  -- inside `IsNotISigmaSeparated` through `IsISigmaSeparated`'s
  -- three nested universals, flip "not σ-blocked" to "σ-open"
  -- via De Morgan, then promote σ-open walk to σ-open path via
  -- `sigmaOpens_TFAE.out 1 0`.
  tfae_have _h₁₂ : 1 → 2 := by
    intro hNot
    simp only [isNotISigmaSeparated_iff, isISigmaSeparated_iff] at hNot
    push Not at hNot
    obtain ⟨v, w, hv, hw, π, hNotBlocked⟩ := hNot
    rw [Walk.isSigmaBlocked_iff_not_isSigmaOpen, not_not] at hNotBlocked
    have hWalk : ∃ π : Walk G v w, π.IsSigmaOpen C := ⟨π, hNotBlocked⟩
    obtain ⟨π', hPath', hOpen'⟩ :=
      ((G.sigmaOpens_TFAE C v w).out 1 0).mp hWalk
    exact ⟨v, w, π', hv, hw, hPath', hOpen'⟩
  -- (1) ⇒ (0): the trivial converse. A σ-open path is in
  -- particular a σ-open walk between `v ∈ A` and `w ∈ G.J ∪ B`,
  -- witnessing the failure of `IsISigmaSeparated`.
  tfae_have _h₂₁ : 2 → 1 := by
    rintro ⟨v, w, π, hv, hw, _hPath, hOpen⟩
    rw [isNotISigmaSeparated_iff]
    intro hSep
    have hBlocked := hSep hv hw π
    rw [Walk.isSigmaBlocked_iff_not_isSigmaOpen] at hBlocked
    exact hBlocked hOpen
  -- (1) ⇔ (2): pointwise application of `sigmaOpens_TFAE.out 0 2`
  -- distributed through the surrounding `∃ v ∈ A, ∃ w ∈ G.J ∪ B`
  -- existentials.
  tfae_have _h₂₃ : 2 → 3 := by
    rintro ⟨v, w, π, hv, hw, hPath, hOpen⟩
    have hPathPair :
        ∃ π : Walk G v w, π.IsPath ∧ π.IsSigmaOpen C := ⟨π, hPath, hOpen⟩
    obtain ⟨π', hOpen', hColl⟩ :=
      ((G.sigmaOpens_TFAE C v w).out 0 2).mp hPathPair
    exact ⟨v, w, π', hv, hw, hOpen', hColl⟩
  tfae_have _h₃₂ : 3 → 2 := by
    rintro ⟨v, w, π, hv, hw, hOpen, hColl⟩
    have hWalkColl :
        ∃ π : Walk G v w, π.IsSigmaOpen C ∧
          ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C := ⟨π, hOpen, hColl⟩
    obtain ⟨π', hPath', hOpen'⟩ :=
      ((G.sigmaOpens_TFAE C v w).out 2 0).mp hWalkColl
    exact ⟨v, w, π', hv, hw, hPath', hOpen'⟩
  tfae_finish

end CDMG

end Causality
