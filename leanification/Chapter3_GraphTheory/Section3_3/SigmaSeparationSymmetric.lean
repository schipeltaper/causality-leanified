import Chapter3_GraphTheory.Section3_3.ISigmaSeparation

-- TeX statement: claim_3_22_statement_SigmaSeparationSymmetric.tex
-- TeX proof:     claim_3_22_proof_SigmaSeparationSymmetric.tex

/-!
# $\sigma$-separation is symmetric (claim_3_22)

This file formalises *claim 3.22* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1366 -- 1369): a `\begin{claimmark}` note sitting *inside* the
def_3_18 ($i\sigma$-separation) defmark, immediately after
clause (4) (the $\sigma$-separation rename for $J = \emptyset$):

> Note that $\sigma$-separation is symmetric:
> $A \sPerp_G B \given C \iff B \sPerp_G A \given C$, since when
> $J = \emptyset$ the set of walks between $A$ and $B$ is the
> same regardless of direction, and the $\sigma$-blocking
> conditions are invariant under walk reversal.

The LN intermixes the *statement* (the `\iff`) with its own
proof sketch ("since when $J = \emptyset$ ... walk reversal").
This file formalises **the statement only**; the proof sketch
is the future Manager-B job, expanded into a `\begin{proof}`
TeX block and translated to Lean tactics.

## What this file contributes

A single `theorem`, `isSigmaSeparated_symm`, with the
$\sigma$-separation symmetry statement under the
$G.J = \emptyset$ side-condition:

```
(G : CDMG α) (hJ : G.J = ∅) (A B C : Set α) :
  G.IsSigmaSeparated A B C ↔ G.IsSigmaSeparated B A C
```

The body is `sorry` -- the proof is out of scope for the
formalizer worker and is the Manager-B prover's job. The future
proof will pivot through `IsISigmaSeparated` (since
`IsSigmaSeparated` is `abbrev`-equal to it), use `hJ` to
collapse `G.J ∪ B` and `G.J ∪ A` to `B` and `A` respectively,
and invoke a (not-yet-existing) `Walk.isSigmaBlocked_reverse_iff`
helper lemma capturing the LN's "the $\sigma$-blocking
conditions are invariant under walk reversal".

## Downstream usage

* **def_3_18** ($i\sigma$-separation, `graphs.tex` lines
  1351 -- 1372) -- the very definition this claim is the
  trailing note of. The per-`abbrev` design block on
  `IsSigmaSeparated` in `ISigmaSeparation.lean` (lines
  710 -- 728) explicitly anticipates this claim: it identifies
  `IsSigmaSeparated` (with `G.J = ∅` as a caller's
  side-condition rather than a baked-in guard) as the surface
  on which claim_3_22's symmetry is stated.
* **Chapter 4 (CBNs, `causal_bayesian_networks.tex`)** -- the
  Markov property for a CBN on a *no-input* graph
  ($G.J = \emptyset$) reads in the LN as "$X_A \Indep X_B
  \given X_C \iff A \sPerp_G B \given C$"; the symmetry of the
  graphical side (this claim) lets CBN-Markov theorems be
  stated and consumed with $A$ and $B$ swapped at the call
  site without an extra translation step.
* **Chapter 5 (do-calculus, `do-calculus.tex` +
  `proof-do-calculus.tex`)** -- the three do-calculus rules are
  stated *in terms of* $i\sigma$-separation (which collapses to
  $\sigma$-separation when applied to the no-input graph cuts
  in chapters 5 -- 7). The "if $A \sPerp_{G_*} B \given C$"
  premise of every rule is consumed symmetrically through this
  result.
* **Chapters 6 -- 7 (identification,
  `adjustment-criteria.tex` / `id-algorithm.tex`)** -- the
  backdoor / front-door / general adjustment criteria are
  $\sigma$-separation conditions on a modified
  ($J = \emptyset$) graph; symmetry of the graphical side is
  used implicitly whenever the criterion is stated with $A$
  and $B$ swapped (the "$A$ is the cause set, $B$ is the effect
  set" vs the dual reading).
* **Chapters 8 -- 10 (iSCMs)** -- inherit $\sigma$-separation
  symmetry through their underlying CBN/CDMG; counterfactual
  identification builds on top.
* **Chapters 11 -- 16 (discovery,
  `causal_relations.tex` / `minimal_sep_sets.tex` / `fci.tex`)**
  -- FCI's skeleton phase tests separation on $A$-$B$ pairs
  with no inherent ordering; the symmetry result is the
  graphical justification for not double-testing each pair in
  both orders.

Note that the *asymmetric* $i\sigma$-separation predicate
`IsISigmaSeparated` is **not** symmetric in general (the
$J$-on-the-target-side footnote of def_3_18 clause 1 breaks the
symmetry whenever $G.J \neq \emptyset$); see the
`ISigmaSeparation.lean` module docstring's "Footnote rationale"
section. claim_3_22's symmetry is *only* about the special-case
$\sigma$-separation surface under the $G.J = \emptyset$
side-condition. Conflating the two would silently break every
chapter-$\ge 4$ CI-vs-separation equivalence that exists
precisely to keep the $J$-asymmetry in `IsISigmaSeparated`
aligned with the asymmetric CI rules for Markov kernels.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.UnblockableNonCollidersOpen`
  -- the immediately preceding claim in this subsection
  (claim_3_21). Same one-row "trailing-claimmark note" file
  pattern: module-level docstring with
  "What this file contributes" / "Downstream usage" /
  "Style precedents" sections; per-declaration
  `-- claim_3_22 / title / ...` comment header; LN block
  reproduced verbatim in a `/- ... -/` quote; design-choice
  block above the theorem.
* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation` -- source
  of `IsSigmaSeparated` (the `abbrev` surface this theorem is
  stated on) and `IsISigmaSeparated` (the underlying
  three-nested-universal `def` the future proof will pivot
  through). The per-`abbrev` design block on `IsSigmaSeparated`
  there explicitly anticipates this claim and motivates the
  `abbrev` choice partly for the sake of this row.
* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks` -- source
  of `Walk.IsSigmaOpen` / `Walk.IsSigmaBlocked` (the per-walk
  predicates that `IsISigmaSeparated` universally quantifies
  over). The statement here does *not* literally mention them,
  but the future proof's "walk reversal preserves
  $\sigma$-blocking" pivot is a property of `IsSigmaBlocked`,
  so the conceptual dependency is recorded here even though
  the import is transitive through `ISigmaSeparation.lean`.
* `Chapter3_GraphTheory.Section3_1.Walks` -- source of
  `Walk.reverse`, the data-level walk-reversal operation the
  future proof will hand to its (not-yet-existing) per-walk
  $\sigma$-blocking-invariance helper. Again, the *statement*
  does not mention `Walk.reverse`; it lives in the proof.

## Infrastructure note for the future prover

The walk-reversal data is already in place (`Walk.reverse`,
`WalkStep.reverse`, `length_reverse`, the three
`reverse_forward` / `reverse_backward` / `reverse_bidir`
`@[simp]` lemmas; see `Chapter3_GraphTheory.Section3_1.Walks`).
The walk-reversal *invariance* lemma at the
$\sigma$-blocking level -- i.e.
`π.IsSigmaBlocked C ↔ π.reverse.IsSigmaBlocked C` and/or its
position-wise primitives
(`IsColliderAt`, `IsBlockableNonColliderAt`,
`IsUnblockableNonColliderAt` all unchanged under reversal
modulo the `nodeAt k ↔ nodeAt (length - k)` re-indexing) --
**does not yet exist**. Manager B's prover will need to
introduce it; the natural home is
`Section3_3/SigmaBlockedWalks.lean` (or an adjacent file
`SigmaBlockedReversal.lean`), and the decision is the prover's
to make. This file does *not* depend on that infrastructure --
the statement is purely about `IsSigmaSeparated`'s symmetry.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

-- claim_3_22
-- title: SigmaSeparationSymmetric -- $\sigma$-separation is
-- symmetric under the $G.J = \emptyset$ side-condition
--
-- `G.IsSigmaSeparated A B C ↔ G.IsSigmaSeparated B A C` when
-- `G.J = ∅`. The LN's $\sPerp_G$ (def_3_18 clause 4) is an
-- `abbrev` rename of $\isPerp_G$ for the no-input case; the
-- symmetry observed by this claim is *not* a property of
-- $\isPerp_G$ in general (which is asymmetric due to the
-- $J$-on-the-target-side footnote, see
-- `ISigmaSeparation.lean`'s module docstring "Footnote
-- rationale" section). It is specifically a property of the
-- $J = \emptyset$ specialisation, whose proof factors through
-- two LN-stated observations:
--
--   1. when $J = \emptyset$, the set of walks between $A$ and
--      $B$ is the same regardless of direction (the
--      $J$-summand on the target side collapses to ∅, and
--      walks are reversible via `Walk.reverse`);
--   2. the $\sigma$-blocking conditions are invariant under
--      walk reversal (a per-walk fact about `IsSigmaBlocked`
--      not yet formalised; future-prover's responsibility).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_22, lines 1366 -- 1369, the trailing claimmark inside
the def_3_18 defmark):

  % claim_3_22
  \begin{claimmark}
  Note that $\sigma$-separation is symmetric:
  $A \sPerp_G B \given C \iff B \sPerp_G A \given C$,
  since when $J = \emptyset$ the set of walks between $A$ and
  $B$ is the same regardless of direction, and the
  $\sigma$-blocking conditions are invariant under walk
  reversal.
  \end{claimmark}
-/
--
-- ## Design choice
--
-- * **Stated on `IsSigmaSeparated`, not on `IsISigmaSeparated`.**
--   The LN claim is phrased on the LN's $\sPerp_G$ surface, not
--   on $\isPerp_G$, and the surface that *appears* in the goal
--   is the one downstream consumers (chapter 4+ CBN-Markov, do-
--   calculus, identification) pattern on. Because
--   `IsSigmaSeparated` is `abbrev`-equal to `IsISigmaSeparated`
--   (def_3_18 clause 4 in `ISigmaSeparation.lean`, declaration
--   at line 763), the future proof gets `IsISigmaSeparated`'s
--   three-nested-universal shape "for free" by `abbrev`-
--   reduction; no translation lemma is needed, and the LN's
--   $\sPerp_G$ symbol remains visible in the goal. The
--   `abbrev` was *deliberately introduced anticipating this
--   very row* -- the per-`abbrev` design block at
--   `ISigmaSeparation.lean` lines 710 -- 757 calls this abbrev
--   "the *exact* surface that claim_3_22's symmetry theorem is
--   stated on" and lists "claim_3_22 ($\sigma$-symmetry) -- the
--   principal consumer, the entire point of having the alias"
--   as its first downstream consequence; the design coherence
--   across the two files is therefore by construction, not
--   coincidence. Stating the theorem on `IsISigmaSeparated`
--   directly would be (i) literally false in general (the
--   $J$-on-target footnote of def_3_18 clause 1 breaks the
--   symmetry whenever $G.J \neq \emptyset$ -- only the
--   `hJ : G.J = ∅` specialisation is symmetric at all), and
--   (ii) mis-aligned with the LN's prose, which only writes
--   "$\sigma$-separation is symmetric", never "$i\sigma$-
--   separation is symmetric".
--
-- * **`hJ : G.J = ∅` is an *explicit* caller's hypothesis.** The
--   LN says "since *when $J = \emptyset$* ..."; the $J$-summand
--   on the target side of `IsISigmaSeparated`'s universal (the
--   load-bearing footnote of def_3_18 clause 1) is what creates
--   the asymmetry between $A$ and $B$, so the symmetry result
--   genuinely needs $G.J = \emptyset$ to discharge that summand.
--   We keep it as an explicit hypothesis -- not a typeclass, not
--   a `variable` baked into the namespace -- because (i) the
--   `IsSigmaSeparated` `abbrev` deliberately does *not* bake
--   $G.J = \emptyset$ into its signature (see the per-`abbrev`
--   design block in `ISigmaSeparation.lean`, lines 710 -- 757,
--   which spells out why $G.J = \emptyset$ stays a caller's
--   side-condition rather than a type-level guard),
--   (ii) downstream consumers in chapters 4 -- 7 will already
--   have a $G.J = \emptyset$ hypothesis in scope (e.g. when
--   working with the no-input graph cut $G_{V}$ in do-calculus),
--   so threading it as an explicit argument is the natural
--   composition pattern, and (iii) typeclass-resolving on
--   "no-input graph" would force a new structure-level wrapper
--   for zero proof-ergonomic gain.
--
-- * **`Iff`, not two separate `→`s.** The LN writes "$\iff$".
--   The contrapositive form
--   "$A \nsPerp_G B \given C \iff B \nsPerp_G A \given C$"
--   under the same `hJ` follows from `Iff.not` of the main
--   statement; we do **not** also expose it as a second theorem.
--   The LN does not list two claims here, and
--   `IsNotSigmaSeparated` is `abbrev`-equal to
--   `¬ IsISigmaSeparated` (via `IsNotISigmaSeparated`), so
--   `not_congr` applied to `isSigmaSeparated_symm` discharges
--   the negation form in a single line at the call site.
--   Duplicating the statement would clutter the API.
--
-- * **`A B C : Set α`, no $\subseteq G.J \cup G.V$
--   side-condition.** Same caller's-side-condition convention
--   as `IsISigmaSeparated` (and the rest of section 3.3); the
--   LN preamble "$A, B, C \ins J \cup V$" is a side-condition
--   on the inputs, not a type-level guard. Symmetry holds for
--   any `A, B, C : Set α` (vacuously for parts of $A$ or $B$
--   outside the node set, since no walks exist between
--   non-node "vertices"); the $\subseteq G.J \cup G.V$
--   condition would be inert here and is omitted.
--
-- * **No walk-reversal helper in the statement.** The LN's
--   "the $\sigma$-blocking conditions are invariant under
--   walk reversal" is the *justification* for symmetry, not
--   part of the statement. Exposing a walk-reversal lemma in
--   the theorem signature would conflate the
--   statement-level "what" with the proof-level "why"; that
--   lemma belongs in the proof (and, since it does not yet
--   exist as infrastructure, in the future prover's helper
--   introduction). The statement as written reads
--   word-for-word as the LN's $\iff$ clause.
--
-- * **Alternative shape considered and rejected: a unified
--   `theorem isISigmaSeparated_symm_of_J_empty` stated on
--   `IsISigmaSeparated` directly.** This would force every
--   downstream consumer who reads $\sPerp_G$ in the LN to
--   unfold the `abbrev` before applying the result -- an
--   extra step at every call site, and a divergence from the
--   LN's prose surface. By stating the theorem on
--   `IsSigmaSeparated`, the `abbrev` reduction does the
--   unfolding *inside* the proof (where it is harmless), not
--   at every call site (where it would be noise). The
--   `review_design` verifier on `ISigmaSeparation.lean`
--   explicitly validated this `abbrev`-surface choice for
--   precisely this row.
--
-- * **Alternative shape considered and rejected: bake
--   $G.J = \emptyset$ into a `structure NoInputCDMG α extends
--   CDMG α (hJ : J = ∅)` wrapper.** This would type-level-
--   enforce the side-condition but at the cost of duplicating
--   every $i\sigma$-separation lemma's signature on the
--   wrapper (or carrying coercions everywhere), and would
--   diverge from the LN's "same notion, different name"
--   reading of clause 4. Keeping `hJ` as an explicit
--   hypothesis is the LN-faithful choice.
--
-- * **Naming `isSigmaSeparated_symm`.** Standard Mathlib
--   convention: the `_symm` suffix for symmetry results (cf.
--   `Iff.symm`, `Eq.symm`, `Set.union_comm` -- the latter
--   uses `_comm` for commutativity of a *binary operation*,
--   but here we have a *3-argument relation symmetric in the
--   first two arguments*, which mathlib consistently names
--   `_symm`).
--
-- * **`G`-first signature for dot-notation.** Matches every
--   other `CDMG`-level theorem (`G.IsISigmaSeparated`,
--   `G.IsSigmaSeparated`, ...). Callers write
--   `G.isSigmaSeparated_symm hJ A B C` (or with `A B C`
--   implicit from context, just `G.isSigmaSeparated_symm hJ`).
--
-- * **No mathlib re-use at the statement level.** Mathlib has
--   no graphical-separation API in the neighbourhood
--   (`SimpleGraph` carries no $\sigma$-blocking / collider /
--   non-collider data and `Quiver` is too thin), so this
--   theorem is stated on our own `CDMG` namespace over the
--   bespoke `IsISigmaSeparated` three-nested-universal. The
--   only mathlib pieces visible in the signature are `Set`,
--   `Iff`, and `∅` -- standard logical glue. The future proof
--   will reach for mathlib's `Set.empty_union` (and friends)
--   to discharge the $G.J \cup A = A$ / $G.J \cup B = B$
--   rewrites under `hJ`, but the *shape* of the theorem is
--   end-to-end project-local. Rolling our own here is forced,
--   not preferred -- there is simply no mathlib counterpart
--   to lean on.
--
-- ## Constraints / known limitations
--
-- * **`hJ : G.J = ∅` must be threaded by callers, whereas the
--   LN encodes the same side-condition *in the notation
--   itself*.** In the LN, callers who know $G.J = \emptyset$
--   write $\sPerp_G$ and callers who do not write $\isPerp_G$;
--   the symbol *is* the condition, and the LN never has to
--   invoke it explicitly. In Lean, since `IsSigmaSeparated` is
--   `abbrev`-equal to `IsISigmaSeparated`, the symbol-level
--   signal is lost (both names reduce to the same term); the
--   explicit `hJ` hypothesis is the only carrier of the
--   side-condition. This is the price of keeping `abbrev`-
--   reduction transparent, and the pattern will recur for
--   every chapter-4+ theorem that consumes
--   `IsSigmaSeparated` -- so the cost is amortised, but it
--   is real.
--
-- * **The contrapositive form is not exposed by name.** The
--   LN-symmetric "$A \nsPerp_G B \given C \iff B \nsPerp_G A
--   \given C$" follows in one line via
--   `not_congr isSigmaSeparated_symm` (since
--   `IsNotSigmaSeparated` is `abbrev`-equal to
--   `IsNotISigmaSeparated`, itself the `def`-named negation of
--   `IsISigmaSeparated`). Downstream consumers searching for an
--   `isNotSigmaSeparated_symm` by name will not find one and
--   will have to reach for `not_congr` instead. The LN does
--   not list two claims here, so we do not either.
--
-- * **The "walk-reversal preserves $\sigma$-blocking" lemma
--   that the future proof needs does not yet exist.** This is
--   a *proof-side* limitation, not a statement-side one (the
--   statement is symmetric and well-typed on its own), but it
--   matters for downstream planning: Manager B's prover must
--   introduce e.g. `Walk.isSigmaBlocked_reverse_iff` (most
--   likely in `Section3_3/SigmaBlockedWalks.lean`, or a new
--   `SigmaBlockedReversal.lean`, at the prover's discretion).
--   See the module docstring's "Infrastructure note for the
--   future prover" section above for the enumeration of what
--   *does* already exist (`Walk.reverse`, `WalkStep.reverse`,
--   the three `reverse_*` `@[simp]` lemmas) and what does not.

/-- claim_3_22 (`SigmaSeparationSymmetric`): under the
side-condition $G.J = \emptyset$, the LN's $\sigma$-separation
relation is symmetric in its first two arguments. The LN
statement is "$A \sPerp_G B \given C \iff B \sPerp_G A \given
C$"; the side-condition $G.J = \emptyset$ is the LN's
"$\sigma$-separation" qualifier from def_3_18 clause 4. The
contrapositive "$A \nsPerp_G B \given C \iff B \nsPerp_G A
\given C$" follows by `Iff.not` (`not_congr`) at the call site
and is not stated separately. -/
theorem isSigmaSeparated_symm (G : CDMG α) (hJ : G.J = ∅)
    (A B C : Set α) :
    G.IsSigmaSeparated A B C ↔ G.IsSigmaSeparated B A C := by
  sorry

end CDMG

end Causality
