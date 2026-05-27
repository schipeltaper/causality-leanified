import Mathlib.Data.List.TFAE
import Chapter3_GraphTheory.Section3_1.WalkPredicates
import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

-- TeX statement: claim_3_23_statement_SigmaOpenPathWalk.tex
-- TeX proof:     claim_3_23_proof_SigmaOpenPathWalk.tex

/-!
# $\sigma$-open path / walk / walk-with-colliders-in-$C$ equivalence (claim_3_23)

This file formalises *claim 3.23* (the LN's Proposition
`prp:sigma_opens` / `\restateprpsigmaopens`) of the lecture
notes (Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`,
lines 1382 -- 1393): a `\begin{claimmark}` Proposition sitting
between def_3_18 ($i\sigma$-separation) and claim_3_24
(the consumer Remark that cites this proposition twice).

The LN block reads:

> Let $G = (J, V, E, L)$ be a CDMG. For $C \subseteq J \cup V$
> and $w_1, w_2 \in J \cup V$, the following are equivalent:
> 1. there exists a $C$-$\sigma$-open *path* between $w_1$ and
>    $w_2$ in $G$;
> 2. there exists a $C$-$\sigma$-open *walk* between $w_1$ and
>    $w_2$ in $G$;
> 3. there exists a $C$-$\sigma$-open *walk* between $w_1$ and
>    $w_2$ in $G$ such that all its colliders lie in $C$ (and
>    not just in $\Anc^G(C)$).

The statement itself encodes the LN's "the following are
equivalent" surface using Mathlib's `List.TFAE`, the canonical
Lean idiom for an $n$-way equivalence between numbered clauses.

This file formalises **the statement only**; the proof body is
`sorry`. The proof is the future Manager-B prover's job; the
LN's proof (`graphs.tex` lines 1655 -- 1673) discharges
`3 → 2` and `1 → 2` trivially ("paths are walks"), `2 → 3` by
expanding each $\Anc^G(C) \setminus C$ collider through a
directed-path-to-$C$-and-back insertion, and `2 → 1` by
*invoking `lem:replace_walk`*, the major lemma of claim_3_27
(title `LabelRoman`) which sits *later* in `data.json` than
this row. The prover will either reorder the dependency or
discharge the (more easily-proven) `1 → 2` / `3 → 2` halves
first.

## What this file contributes

A single `theorem`, `sigmaOpens_TFAE`, expressing the
three-way equivalence as `List.TFAE` of three existentials:

```
(G : CDMG α) (C : Set α) (w₁ w₂ : α) :
  List.TFAE
    [ (∃ π : Walk G w₁ w₂, π.IsPath ∧ π.IsSigmaOpen C),
      (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C),
      (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C ∧
         ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) ]
```

The three list entries are direct one-to-one transliterations
of the LN's clauses 1, 2, 3. None of them are wrapped in a
named `def`; see the design block below for why inlining is
the deliberate choice.

The body is `sorry`. Per-pair extractions at the call site
read `((G.sigmaOpens_TFAE C w₁ w₂).out 0 1)` for the
path $\leftrightarrow$ walk equivalence (clauses 1 and 2) and
`.out 1 2` for the walk $\leftrightarrow$
walk-with-colliders-in-$C$ equivalence (clauses 2 and 3) --
exactly the two equivalences that claim_3_24's Remark cites
by name.

## Downstream usage

* **claim_3_24** (`graphs.tex` lines 1395 -- 1412) -- the
  Remark immediately following this proposition. It cites
  `prp:sigma_opens` *twice*:
    - once to rewrite `IsISigmaSeparated`'s
      universal-over-walks as a universal-over-paths
      ("$A \isPerp_G B \given C$ is equivalent to ... every
      *path* from a node in $A$ to a node in $J \cup B$ is
      $C$-$\sigma$-blocked"), which contraposes through
      `(sigmaOpens_TFAE _ _ _ _).out 0 1`; and
    - once to extract a shortest $C$-$\sigma$-open path / a
      shortest $C$-$\sigma$-open walk-with-colliders-in-$C$
      from a `IsNotISigmaSeparated` hypothesis, which uses
      `.out 0 1` and `.out 1 2` in sequence.
  Both extractions are first-class projections on a single
  TFAE theorem -- which is the principal ergonomic reason
  we picked the TFAE shape over two separate biconditionals
  (see the design block).
* **claim_3_25** ($i\sigma$-separation under marginalization,
  `graphs.tex` lines 1414 -- 1422) -- the LN's proof
  constructs $\sigma$-open walks on a marginalized graph
  from $\sigma$-open walks on the original, and then converts
  between path-existence and walk-existence at the boundary;
  consumes `(sigmaOpens_TFAE _ _ _ _).out 0 1`.
* **Chapter 4 (CBNs,
  `causal_bayesian_networks.tex`)** -- the Markov property
  for a CBN equates conditional independence in the joint
  distribution to graphical $i\sigma$-separation. Several
  statements of the CBN-Markov property and its corollaries
  are stated in terms of paths (rather than walks) because
  the path formulation is the one practitioners check; the
  equivalence here is the bridge.
* **Chapter 5 (do-calculus, `do-calculus.tex` +
  `proof-do-calculus.tex`)** -- the do-calculus rules cite
  $i\sigma$-separation premises; whenever a rule is applied
  by exhibiting a $\sigma$-open path, this proposition is
  the translation step.
* **Chapter 6 -- 7 (identification,
  `adjustment-criteria.tex` / `id-algorithm.tex`)** -- the
  backdoor / front-door / general adjustment criteria are
  most naturally stated as the *absence* of a $\sigma$-open
  path satisfying particular constraints; this proposition
  lets those statements ride on top of
  `IsISigmaSeparated`'s walk universal without re-deriving
  the path / walk equivalence in each criterion's proof.
* **Chapters 11 -- 16 (discovery,
  `causal_relations.tex` / `minimal_sep_sets.tex` /
  `fci.tex`)** -- FCI's skeleton-phase and orientation-phase
  reasoning operate on *paths*, because there are only
  finitely many of them in a finite graph (the LN's own
  pragmatic remark at `graphs.tex` line 1410: "in practice
  we usually check if every path is $C$-$\sigma$-blocked").
  This proposition lets the FCI-side path reasoning
  interoperate with the chapter-3 walk-based separation
  predicates.
* **Mirror in subsection 3.4** -- claim_3_30 (`graphs.tex`
  line 1745) explicitly cites "a similar result from
  Proposition \ref{prp:sigma_opens} holds for
  $id$-separation as well", i.e. the same three-way TFAE
  but with $d$-blocking in place of $\sigma$-blocking. The
  shape we pick here propagates to that future $id$-version.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.SigmaSeparationSymmetric`
  (claim_3_22) -- the immediately preceding claim in this
  subsection. Same one-row claim-file pattern: module-level
  docstring with "What this file contributes" /
  "Downstream usage" / "Style precedents" sections;
  per-declaration `-- claim_*` comment header; LN block
  reproduced verbatim in a `/- ... -/` quote; design-choice
  block above the theorem; body `sorry` at the
  formalizer-worker stage. Stays in `namespace CDMG` so the
  theorem dot-projects on the CDMG argument
  (`G.sigmaOpens_TFAE`).
* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation`
  (def_3_18) -- source of the surrounding
  $i\sigma$-separation surface; the per-`abbrev` design
  block at `IsSigmaSeparated` flags claim_3_23 / claim_3_24
  as principal consumers and the `Footnote rationale`
  paragraph in the module docstring is *why* the walk
  universals in `IsISigmaSeparated` are stated the way they
  are, which then licenses the existentials in *this* claim
  to be stated symmetrically across the three clauses.
* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks`
  (def_3_17) -- source of `Walk.IsSigmaOpen`,
  `Walk.IsColliderAt`, `Walk.nodeAt` -- the three per-walk
  primitives this proposition's clauses inline.
* `Chapter3_GraphTheory.Section3_1.WalkPredicates`
  (def_3_4, item 5) -- source of `Walk.IsPath` (defined as
  `support.Nodup`), which clause 1 inlines alongside
  `IsSigmaOpen`.
* Mathlib `Mathlib.Data.List.TFAE` -- source of
  `List.TFAE`, the formal embodiment of the LN's "the
  following are equivalent" idiom. The `tfae_have` /
  `tfae_finish` tactics (in `Mathlib.Tactic.TFAE`, *not*
  imported here -- the future prover will import them) are
  the standard discharge mechanism for a TFAE goal and let
  the LN proof's "3 → 2 trivial", "1 → 2 trivial",
  "2 → 3 (collider-replacement)", "2 → 1 (`lem:replace_walk`)"
  structure be transcribed implication-by-implication into
  Lean tactics.

## Infrastructure note for the future prover

The LN's proof (`graphs.tex` lines 1655 -- 1673) opens with
`3 → 2` and `1 → 2` as trivial ("paths are walks"); these
two implications need only that a path is a special case of
a walk -- the existential witness in clauses 1 / 3 is
literally usable as the existential witness in clause 2
because `π.IsPath ∧ π.IsSigmaOpen C → π.IsSigmaOpen C` and
`(π.IsSigmaOpen C ∧ ∀ k, ...) → π.IsSigmaOpen C` are pure
projections.

The substantive directions are:

* **`2 → 3`** -- given a $C$-$\sigma$-open walk $\pi$, walk
  each collider $v_k \in \Anc^G(C) \setminus C$ on $\pi$
  *out* to $C$ via a directed path
  $v_k \tuh \cdots \tuh c_k \in C$ and back, replacing the
  collider with a longer sub-walk in which $v_k$ still
  appears as a collider but now sits *strictly inside* a
  $\Anc^G(C)$-witness with $c_k \in C$ on either side as a
  non-collider. Iterating over all such colliders produces a
  walk with every collider in $C$. The infrastructure needed
  is (i) the existence of the directed-path-to-$C$ witness
  ("a node in $\Anc^G(C)$ is the start of a directed walk to
  $C$"; this is the definitional content of
  `Section3_1.FamilyReachability.AncSet`'s reverse direction
  and is likely already available as a single-line lemma in
  that file or in `FamilyDirect`), and (ii) a walk-splicing
  /concatenation operation that preserves the per-position
  collider / non-collider / arrowhead structure
  (`Walk.append` from `Section3_1.Walks` is the foundation;
  the prover may need a `Walk.spliceAtPosition` helper that
  does not yet exist).
* **`2 → 1`** -- given a $C$-$\sigma$-open walk $\pi$ that
  is not yet a path, the LN's proof invokes
  `lem:replace_walk` (= claim_3_27, title `LabelRoman`):
  for any node $w$ appearing more than once on $\pi$, the
  subwalk between the first and last occurrences of $w$ can
  be replaced by a directed path within $\Sc^G(w)$,
  preserving $\sigma$-openness. The replacement strictly
  reduces the number of repeated nodes (by at least one),
  and iterating terminates with a $\sigma$-open *path*.
  **`lem:replace_walk` / claim_3_27 is currently
  unformalized and sits *later* in `data.json` than this
  row.** The prover has two options:
    1. **Reorder.** Move claim_3_27 ahead of claim_3_23 in
       the working sequence (the data.json's natural-order
       sequencing is not a hard dependency; reordering is
       the planner's call).
    2. **Push forward.** Prove `1 ↔ 2` and `2 ↔ 3` as
       far as possible without `lem:replace_walk`. Both
       directions of `1 ↔ 2` are immediate one-way
       (`1 → 2` is "paths are walks"; `2 → 1` needs
       `lem:replace_walk`), so this option only discharges
       the *trivial* halves. The TFAE proof would still
       need a `sorry` for the `2 → 1` arrow until
       claim_3_27 lands.

The `lem:replace_walk` dependency is also the reason the
workspace's `Critical dependency` section flagged this row
as a non-blocker for the *statement* phase but a real
question for the proof phase. This file is the statement;
the dependency is the prover's to navigate.

The infrastructure that *is* already in place:
`Walk.IsPath`, `Walk.IsSigmaOpen`, `Walk.IsColliderAt`,
`Walk.nodeAt`, `Walk.append`, `CDMG.AncSet`, plus the
chapter-3 `IsDirected` and `Sc^G` infrastructure (in
`Section3_1.FamilyReachability` /
`Section3_1.FamilyDistrict`) -- enough for the prover to
state every helper lemma the LN's proof relies on, given
`lem:replace_walk`.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

-- claim_3_23
-- title: SigmaOpenPathWalk -- three-way TFAE between
-- $\sigma$-open path, $\sigma$-open walk, and $\sigma$-open
-- walk with all colliders in $C$
--
-- `G.sigmaOpens_TFAE C w₁ w₂` packages the LN's "the
-- following are equivalent" enumeration over three
-- $\sigma$-open-existence clauses into a single
-- `List.TFAE`. The clauses, in the LN's order:
--
--   1. there exists a $C$-$\sigma$-open *path* from $w_1$ to
--      $w_2$ in $G$;
--   2. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
--      $w_2$ in $G$;
--   3. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
--      $w_2$ in $G$ all of whose colliders lie in $C$ (i.e.
--      strictly in $C$, not merely in $\Anc^G(C)$).
--
-- All three propositions inline their per-walk content; no
-- intermediate "is a $\sigma$-open path" / "is a $\sigma$-open
-- walk with colliders in $C$" predicates are introduced (see
-- the design block).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_23, lines 1382 -- 1393):

  % claim_3_23
  \begin{claimmark}
  \begin{restatable}{Prp}{restateprpsigmaopens}\label{prp:sigma_opens}
    Let $G=(J,V,E,L)$ be a CDMG. For $C \subseteq J \cup V$, and
    $w_1, w_2 \in J \cup V$, the following are equivalent:
    \begin{enumerate}
        \item there exists a $C$-$\sigma$-open \emph{path}
          between $w_1$ and $w_2$ in $G$;
        \item there exists a $C$-$\sigma$-open \emph{walk}
          between $w_1$ and $w_2$ in $G$;
        \item there exists a $C$-$\sigma$-open \emph{walk}
          between $w_1$ and $w_2$ in $G$ such that all its
          colliders lie in $C$ (and not just in $\Anc^G(C)$).
    \end{enumerate}
  \end{restatable}
  \end{claimmark}
-/
--
-- ## Design choice
--
-- * **Status flag (post-`add_design_choice_comments`).** The
--   declaration below is **statement-only**: the body is
--   exactly `sorry`. `review_design` and `verify_equivalence`
--   both PASSed on the statement; the design-rationale
--   comments in this block are now filled in (this pass).
--   The *proof* is the next manager's job and is gated on
--   `lem:replace_walk` / claim_3_27 (`LabelRoman`) for the
--   `2 → 1` arrow -- see the module docstring's
--   "Infrastructure note for the future prover" section. A
--   reader pattern-matching on `solved=yes` for this row
--   should know: statement formalised, design recorded,
--   proof pending.
--
-- * **`List.TFAE` over three propositions, not a chain of
--   `Iff`s, not a conjunction of two `Iff`s, not two
--   separately-named biconditionals.** The LN's prose
--   "the following are equivalent" followed by a numbered
--   enumeration is *exactly* the mathematical idiom that
--   Mathlib's `List.TFAE` is built to formalise (cf.
--   `Mathlib.Data.List.TFAE`'s opening docstring: "The
--   Following Are Equivalent ... TFAE l means
--   `∀ x ∈ l, ∀ y ∈ l, x ↔ y`"). Three alternatives were
--   considered:
--     (A) a chain `(P₁ ↔ P₂) ↔ (P₂ ↔ P₃)` -- *not* the same
--         logical content as TFAE; the chained-`↔` form is
--         well-known *not* to associate the way mathematical
--         "the following are equivalent" prose does
--         (`Iff.trans` does not chain through a third `Iff`
--         in the obvious way). Ruled out as a transcription
--         error of the LN.
--     (B) two separately-named biconditionals,
--         e.g. `sigma_open_path_iff_walk` (= LN clauses
--         1 $\Leftrightarrow$ 2) and
--         `sigma_open_walk_iff_all_colliders_in_C`
--         (= LN clauses 2 $\Leftrightarrow$ 3). This mirrors
--         the LN proof's pivot structure (proves
--         `2 → 1`, `1 → 2`, `2 → 3`, `3 → 2`), and was the
--         tied-runner-up. Rejected because (i) it loses the
--         LN's "*the following are equivalent*" surface
--         (the LN names a single proposition, not two);
--         (ii) it forces a privileged-pivot reading
--         (clause 2 = the always-LHS of both bicons), which
--         the LN's flat enumeration does not endorse; and
--         (iii) downstream consumers cite the proposition
--         *by name* and by *clause number* -- not as two
--         distinct theorems. Concretely:
--           - claim_3_24's Remark (`graphs.tex` lines
--             1395 -- 1412) cites "by Proposition
--             \ref{prp:sigma_opens}" *twice*, once
--             projecting (1) $\Leftrightarrow$ (2) and once
--             projecting (2) $\Leftrightarrow$ (3) -- the
--             ergonomic move on a single-named TFAE is
--             `.out 0 1` and `.out 1 2`;
--           - claim_3_25's proof (`graphs.tex` line 1495)
--             cites "Proposition \ref{prp:sigma_opens}(3)"
--             literally by clause number to extract a walk
--             with colliders in $C$;
--           - claim_3_28's acyclification proof
--             (`graphs.tex` lines 2140, 2178) cites
--             "Proposition \ref{prp:sigma_opens}(3)" twice
--             (once for each direction of an equivalence),
--             again by clause number.
--         Every one of these consumers is a literal
--         transliteration of `(G.sigmaOpens_TFAE C w₁ w₂)
--         .out i j` with `i, j ∈ {0, 1, 2}`. Two separately-
--         named theorems would (a) force the consumer
--         pattern to choose *which* theorem name to invoke
--         per citation, and (b) silently lose the
--         clause-number labelling on which the LN's `(3)`-
--         style citations ride. The TFAE shape preserves
--         both.
--     (C) a single bundled `theorem sigmaOpens` returning a
--         conjunction `(P₁ ↔ P₂) ∧ (P₂ ↔ P₃)`. Equivalent
--         in content to TFAE for `n = 3`, but loses (i) the
--         "the following are equivalent" *surface*
--         (the conjunction-of-`Iff`s reads as "we have two
--         unrelated equivalences"), and (ii) the
--         `tfae_have` / `tfae_finish` tactic ecosystem that
--         lets the future prover discharge each implication
--         arrow in the LN's order without manually
--         assembling the `And.intro`. Rejected as a
--         strictly worse rendering of the same content.
--   `List.TFAE` is the LN-faithful choice: literally
--   "the following are equivalent", literally a list of the
--   three propositions, and *symmetric* across all three
--   clauses (no clause privileged as a pivot in the
--   *statement* -- the LN proof picks clause 2 as the
--   pivot, but the statement does not bake that in). The
--   `review_design` verifier downstream is the natural
--   place to sanity-check the choice; the workspace's plan
--   explicitly flagged this as the design decision deferred
--   to the formalizer, with `List.TFAE` as the manager's
--   weak prior. We confirm.
--
-- * **Clause order in the `List.TFAE` argument matches the
--   LN's enumeration literally (path / walk / walk-with-
--   colliders-in-$C$), with a 0-based offset on the
--   `.out` projection.** Mathlib's `List.TFAE` indexes into
--   its argument list starting at `0`; the LN's enumerated
--   clauses are 1-based. Concretely:
--     - LN clause (1) (path) = list index `0`;
--     - LN clause (2) (walk) = list index `1`;
--     - LN clause (3) (walk-colliders-in-$C$) = list index `2`.
--   So a downstream caller transliterating
--   "by Proposition \ref{prp:sigma_opens}(1) $\Leftrightarrow$
--   (2)" writes `(G.sigmaOpens_TFAE C w₁ w₂).out 0 1`;
--   "(2) $\Leftrightarrow$ (3)" is `.out 1 2`; and
--   "(1) $\Leftrightarrow$ (3)" is `.out 0 2`. The
--   alternative -- reordering the list as walk / path /
--   walk-colliders-in-$C$ to put the LN's "pivot" clause
--   first -- was rejected because it would break the
--   citation pattern: every downstream `\ref{prp:sigma_opens}
--   (3)` (e.g. `graphs.tex` lines 1495, 2140, 2178) would
--   silently project the *wrong* list entry. Keeping the
--   list literal-LN-order means the 0-based offset is the
--   *only* thing a reader has to remember, and the LN-clause
--   $\leftrightarrow$ Lean-index correspondence is a single
--   subtraction.
--
-- * **Each clause inlined as an `∃ π : Walk G w₁ w₂, ...`,
--   no named auxiliary predicates.** Three obvious helper
--   `def`s suggest themselves -- `IsSigmaOpenPath`,
--   `IsSigmaOpenWalk`, `IsSigmaOpenWalkAllCollidersIn` --
--   and were considered. Rejected because:
--     (i) the LN's clauses are already short, readable
--         compositions of *existing* predicates
--         (`Walk.IsPath`, `Walk.IsSigmaOpen`,
--         `Walk.IsColliderAt`, `Walk.nodeAt`); adding a
--         third layer would force downstream consumers to
--         unfold the wrapper before applying the existing
--         per-walk lemmas (claim_3_24's Remark in particular
--         needs to *negate* clause 1 into a universal-
--         over-paths to get the LN's "every path is
--         $\sigma$-blocked" phrasing -- the negation reads
--         cleanly off the inlined `∃ π, π.IsPath ∧ ...`
--         but would require a `simp`/`unfold` step against
--         a wrapper);
--     (ii) clause 3's "all colliders in $C$" predicate is a
--         *single-use* universal -- this is the *only*
--         place in chapters 3 -- 16 where the LN reasons
--         about it. A named `def` for a single-use predicate
--         pollutes the namespace and adds a layer of
--         indirection for no reuse gain;
--     (iii) the formalizer prompt explicitly directs
--         "do not introduce new definitions ... unless you
--         find a strong design-choice reason". No such
--         reason exists for any of the three.
--   If a downstream chapter ever wants the named wrapper
--   (e.g. chapter 16 reasoning about "the set of
--   $\sigma$-open paths"), it can introduce a local `def`
--   then -- *after* observing actual reuse.
--   Pointers to where the inlined predicates live, so a
--   reader of clause 1 / 3 does not have to grep:
--     - `Walk.IsPath` (clause 1) is `π.support.Nodup` -- a
--       one-line `def` at
--       `Section3_1/WalkPredicates.lean` line 466.
--     - `Walk.IsSigmaOpen` (clauses 1 / 2 / 3) is the
--       def_3_17 conjunction (collider / blockable / non-
--       unblockable conditions) at
--       `Section3_3/SigmaBlockedWalks.lean`.
--     - `Walk.IsColliderAt` (clause 3) is the position-
--       indexed collider predicate at
--       `Section3_3/CollidersAndNon.lean` line 189.
--     - `Walk.nodeAt` (clause 3) is the position-indexed
--       node accessor at
--       `Section3_3/SigmaBlockedWalks.lean` line 258.
--
-- * **Naming `sigmaOpens_TFAE`.** Three considerations
--   converge:
--     (i) the LN's LaTeX label is `prp:sigma_opens` /
--         macro `\restateprpsigmaopens`, which camelCases to
--         `sigmaOpens` -- matching the LN's name surface
--         literally;
--     (ii) Mathlib's TFAE-theorem convention adds a
--         `_TFAE` / `_tfae` suffix
--         (cf. `t1Space_TFAE`, `isLoop_tfae`,
--         `isColoop_tfae`) so the shape is recognisable in
--         the goal display and the consumer's `.out`
--         indexing reads as a TFAE projection;
--     (iii) downstream consumers cite the proposition by
--         the LN-name "Proposition \ref{prp:sigma_opens}";
--         keeping the LN name in the Lean identifier (with
--         the `_TFAE` suffix tagging the shape) makes the
--         citation chain obvious.
--   The capital-`TFAE` variant matches `t1Space_TFAE`
--   (Topology) over the lowercase `isLoop_tfae`
--   (Combinatorics) for no strong reason beyond
--   topology-side polish; either would work.
--
-- * **`G`-first, then `C`, then `w₁`, `w₂` -- explicit binders.**
--   `G : CDMG α` first matches every other `CDMG`-level
--   declaration (`G.IsISigmaSeparated`, `G.IsSigmaSeparated`,
--   `G.isSigmaSeparated_symm`, ...) and lets callers write
--   `G.sigmaOpens_TFAE C w₁ w₂` in dot-projection. `C` comes
--   second to match the LN prose order ("For
--   $C \subseteq J \cup V$, and $w_1, w_2 \in J \cup V$") and
--   the per-walk `IsSigmaOpen C` argument order. `w₁` and
--   `w₂` are explicit because no membership hypothesis pins
--   them down (compare `IsISigmaSeparated` where strict-
--   implicit `⦃v w⦄` are pinned by `v ∈ A` / `w ∈ G.J ∪ B`);
--   here the endpoints are part of the proposition's data,
--   not derivable from a hypothesis.
--
-- * **Subscript names `w₁ w₂`, not `v w` or `w₁' w₂'`.**
--   The LN uses $w_1, w_2$ explicitly; Lean's Unicode
--   subscripts render the LN notation literally
--   (`w₁` ↔ $w_1$, `w₂` ↔ $w_2$). Subscript binders are
--   precedented in `Section3_2` (e.g.
--   `Marginalization.lean` uses `v₁ v₂` elsewhere in the
--   chapter). Renaming to `v w` would diverge from the LN
--   surface at zero formal cost.
--
-- * **`w₁, w₂ ∈ G.J ∪ G.V` is a caller's side-condition,
--   not a type-level guard.** Same paradigm as
--   `IsSigmaBlocked` / `IsSigmaOpen` / `IsISigmaSeparated`:
--   the LN's preamble "$w_1, w_2 \in J \cup V$" is a
--   side-condition on the inputs, not a baked-in
--   restriction. The `verify_equivalence` verifier
--   explicitly endorsed *not* lifting it into a subtype.
--   There are two off-graph cases to track, and TFAE holds
--   vacuously in both:
--     - **Different off-graph endpoints
--       ($w_1 \neq w_2$).** No `Walk G w₁ w₂` inhabitant
--       exists -- every `WalkStep` constructor carries an
--       `EdgeOutOf` / `EdgeInto` / `L`-proof that pins both
--       endpoints into $G.J \cup G.V$, so the existential
--       in each clause is empty. All three propositions are
--       vacuously `False`; TFAE on three `False`s is `True`.
--     - **Same off-graph endpoint ($w_1 = w_2$, neither in
--       $G.J \cup G.V$).** The reflexive walk `Walk.nil`
--       (zero edges) inhabits `Walk G w₁ w₁` even for an
--       off-graph `w₁`. But `Walk.nil` has zero colliders
--       (vacuous over `IsColliderAt k`), is a path (its
--       support is a singleton, hence `Nodup`), and is
--       trivially $\sigma$-open (no positions to fail any
--       collider / non-collider check). It therefore
--       witnesses *all three* clauses simultaneously, and
--       TFAE again holds (this time with all three clauses
--       vacuously `True`).
--   Either way the statement is well-typed and logically
--   valid without the LN's preamble; the LN preamble does
--   no work at the statement level. Downstream consumers
--   that *use* the proposition non-vacuously will already
--   have $w_1, w_2 \in G.J \cup G.V$ in scope (e.g.
--   claim_3_24 gets it from `IsISigmaSeparated`'s `v ∈ A`
--   and `w ∈ G.J ∪ B` hypotheses).
--
-- * **`C : Set α`, not `{C : Set α // C ⊆ G.J ∪ G.V}`.**
--   Same convention as `IsSigmaBlocked` / `IsSigmaOpen` /
--   `IsISigmaSeparated`; see the design block on
--   `IsISigmaSeparated` (`ISigmaSeparation.lean` lines
--   206 -- 219). Carrying a subtype on every separation-
--   related signature pollutes downstream consumers for no
--   proof-ergonomic gain.
--
-- * **Clause 3's "all colliders in $C$" predicate uses
--   `π.nodeAt k ∈ C`, not `π.nodeAt k ∈ G.AncSet C`.** The
--   LN deliberately contrasts the two: "all its colliders
--   lie in $C$ (and not just in $\Anc^G(C)$)". Clause 2's
--   collider condition (from `IsSigmaOpen`) is
--   `π.nodeAt k ∈ G.AncSet C`; clause 3 *strengthens* it
--   to membership in $C$ itself. The strengthening is the
--   *only* difference between clauses 2 and 3 (both still
--   require `π.IsSigmaOpen C` overall, so the
--   blockable-non-collider condition is shared); we encode
--   that exactly. Wrapping clause 3 in a single
--   `π.IsSigmaOpen C ∧ (∀ k, π.IsColliderAt k → π.nodeAt k
--   ∈ C)` makes the relationship to clause 2 visible at the
--   surface -- clause 2 plus the extra collider tightening.
--
-- * **`∀ k, π.IsColliderAt k → π.nodeAt k ∈ C` is the
--   universal-implication rendering of the LN's "all its
--   colliders lie in $C$".** The natural-language phrase
--   "every collider $c$ on $\pi$ satisfies $c \in C$" is a
--   universal over collider positions; the Lean idiom for
--   "universal over a subset, gated by a predicate" is
--   `∀ k, IsColliderAt k → ...`, i.e. an implication-
--   guarded universal over all positions. Alternatives
--   (e.g. a `∀ k : {k // π.IsColliderAt k}` subtype-bound
--   universal, or quantifying over a `Fin π.length` with
--   an `IsColliderAt` guard) would force the consumer to
--   either coerce out of a subtype or unpack a `Fin` --
--   pure noise relative to the implication-guarded form.
--   The shape matches `IsSigmaOpen`'s clause-(i) exactly
--   (cf. `SigmaBlockedWalks.lean` line 427: the collider
--   conjunct of `IsSigmaOpen` is
--   `∀ k, π.IsColliderAt k → π.nodeAt k ∈ G.AncSet C`),
--   so clause 3 reads as "the same universal as `IsSigmaOpen`
--   but with $C$ in place of $\Anc^G(C)$" -- precisely the
--   LN's "all its colliders lie in $C$ (and not just in
--   $\Anc^G(C)$)" contrast at the surface. `IsColliderAt`
--   itself is the position-indexed predicate from
--   `Section3_3/CollidersAndNon.lean` line 189; `nodeAt`
--   is the position-indexed node accessor from
--   `Section3_3/SigmaBlockedWalks.lean` line 258. The
--   `k : ℕ` is gated by `IsColliderAt k` (which returns
--   `False` at out-of-range positions, see the position-
--   indexing convention in `SigmaBlockedWalks.lean`'s
--   module docstring), so the quantifier is correctly
--   restricted to actual collider positions on $\pi$
--   without needing a `Fin` bound.
--
-- * **Body is exactly `sorry`.** Per the formalizer-worker
--   prompt (`scaffold/claude_prompts/row_workers/`
--   `formalize_claim_in_lean.md`): "Body is exactly one
--   `sorry` per declaration. Do not attempt the proof here
--   -- that's `prove_claim_in_lean`, which runs *after* the
--   tex proof has been written and verified." The future
--   prover will pivot through `lem:replace_walk` (=
--   claim_3_27) for the `2 → 1` arrow; see the module
--   docstring's "Infrastructure note for the future
--   prover" section.
--
-- ## Downstream consequences
--
-- * **claim_3_24** (Remark, `graphs.tex` lines 1395 -- 1412):
--   the principal consumer. Cites this proposition twice:
--   once via `.out 0 1` to bridge between path-existence
--   and walk-existence (rewriting `IsISigmaSeparated`'s
--   walk universal as a path universal), and once via
--   `.out 1 2` to bridge between walk-existence and
--   walk-with-colliders-in-$C$-existence (extracting a
--   stronger witness from a `IsNotISigmaSeparated`
--   hypothesis). Both extractions are first-class
--   projections on `sigmaOpens_TFAE`.
-- * **claim_3_25** ($i\sigma$-separation under
--   marginalization, `graphs.tex` lines 1414 -- 1422): the
--   LN proof translates between walks on $G$ and walks on
--   $G^{\setminus D}$; some of its steps are cleaner stated
--   on paths, so `.out 0 1` is the bridge.
-- * **Chapter 4+ Markov-property theorems**: whenever
--   "every path from $A$ to $J \cup B$ is $\sigma$-blocked"
--   shows up (e.g. CBN-Markov consequences stated for
--   practitioners), the equivalence here is the bridge to
--   the walk-based `IsISigmaSeparated`.
-- * **Chapter 5 -- 7 (do-calculus / identification)**: rule
--   premises and adjustment criteria are most ergonomic
--   in the *path* formulation; theorems are proved in the
--   *walk* formulation. The TFAE bridges between the two.
-- * **Chapters 11 -- 16 (discovery, FCI / ICDF)**: path-based
--   separation tests live inside FCI's main loop; this
--   bridge is invoked at every test.
-- * **Mirror in subsection 3.4** (claim_3_30, `graphs.tex`
--   line 1745): "a similar result from Proposition
--   \ref{prp:sigma_opens} holds for $id$-separation as
--   well", i.e. the $d$-blocking version. Picking the
--   TFAE shape here propagates verbatim to the future
--   `dOpens_TFAE`.
--
-- ## Constraints / known limitations
--
-- * **The proof body is `sorry`** -- this row is at the
--   formalizer stage. Manager B's prover will fill it,
--   navigating the `lem:replace_walk` / claim_3_27
--   dependency (see the module docstring's "Infrastructure
--   note for the future prover" section). Until the proof
--   lands, every downstream consumer is also gated on
--   `sorry` -- a single point of unsoundness, easy to
--   audit, easy to discharge in one place.
-- * **`w₁, w₂ ∈ G.J ∪ G.V` is a caller's side-condition,
--   not a type-level guard.** Stating
--   `G.sigmaOpens_TFAE C w₁ w₂` with $w_1 \notin G.J \cup
--   G.V$ is *not a type error* -- it just makes all three
--   list entries vacuously `False`, hence TFAE is `True`.
--   Callers that rely on the proposition's content need
--   $w_1, w_2 \in G.J \cup G.V$ in scope (which they will,
--   if they got here via `IsISigmaSeparated`'s membership
--   hypotheses).
-- * **No `Decidable` instance.** Like `IsISigmaSeparated`
--   and the rest of the LN's separation predicates, the
--   propositions here are classical-existential over
--   walks (which form an infinite type for general
--   graphs); we provide no decidability infrastructure.
--   Finite-graph specialisations may be added downstream
--   when chapters 11 -- 16's FCI implementation needs them.
-- * **The `tfae_have` / `tfae_finish` tactics are not yet
--   imported here**, only `Mathlib.Data.List.TFAE` (the
--   type and its API). The future prover will pull
--   `Mathlib.Tactic.TFAE` into this file (or whichever
--   file Lake routes the proof through) -- a small import
--   pinned by the proof's pivot through `tfae_have`.

/-- claim_3_23 (`SigmaOpenPathWalk`,
LN `\restateprpsigmaopens` / `prp:sigma_opens`): for a CDMG
$G$, a conditioning set $C \subseteq J \cup V$, and two
nodes $w_1, w_2 \in J \cup V$, the following three
propositions are equivalent:
1. there exists a $C$-$\sigma$-open *path* from $w_1$ to
   $w_2$ in $G$;
2. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
   $w_2$ in $G$;
3. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
   $w_2$ in $G$ all of whose colliders lie in $C$ (not just
   in $\Anc^G(C)$).
Packaged as a `List.TFAE`; pairwise extractions are
`(G.sigmaOpens_TFAE C w₁ w₂).out i j` for `i, j ∈ {0, 1, 2}`.

The proof body is `sorry`; the LN's proof pivots through
clause 2 and uses `lem:replace_walk` (= claim_3_27,
`LabelRoman`) for the `2 → 1` direction, see this file's
module docstring's "Infrastructure note for the future
prover". -/
theorem sigmaOpens_TFAE (G : CDMG α) (C : Set α) (w₁ w₂ : α) :
    List.TFAE
      [ (∃ π : Walk G w₁ w₂, π.IsPath ∧ π.IsSigmaOpen C),
        (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C),
        (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C ∧
          ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) ] := by
  sorry

end CDMG

end Causality
