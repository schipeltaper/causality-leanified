import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

/-!
# $i\sigma$-separation (def 3.18)

This file formalises *definition 3.18* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1351 -- 1372): $i\sigma$-separation between three node-sets
$A$, $B$, $C$ in a CDMG $G = (J, V, E, L)$, the principal
graphical-separation criterion of the LN. Subsequent chapters
(do-calculus ch. 5, identification ch. 6 -- 7, iSCMs ch. 8 -- 10,
discovery ch. 11 -- 16) all consume this predicate through every
CI-vs-separation result.

## Predicates exposed (under `Causality.CDMG`)

Mirroring the LN's four numbered clauses:

* `IsISigmaSeparated G A B C` (LN clause 1, the *primary*
  asymmetric notion) -- every walk from a node in `A` to a node
  in `G.J ∪ B` is `C`-$\sigma$-blocked.
* `IsNotISigmaSeparated G A B C` (LN clause 2) -- definitional
  alias for `¬ G.IsISigmaSeparated A B C`, matching the LN's
  $\nisPerp_G$ shorthand.
* `IsISigmaSeparatedEmpty G A B` (LN clause 3) -- definitional
  alias for `G.IsISigmaSeparated A B ∅`, matching the LN's
  "$A \isPerp_G B := A \isPerp_G B \given \emptyset$" special
  case.
* `IsSigmaSeparated G A B C` / `IsNotSigmaSeparated G A B C`
  (LN clause 4) -- `abbrev` aliases for the $J = \emptyset$
  special case, matching the LN's "for the special case
  $J = \emptyset$, ... we write $A \sPerp_G B \given C :=
  A \isPerp_G B \given C$" notation. We deliberately do **not**
  bake `G.J = ∅` into the definition: the LN treats
  $\sigma$-separation as the *same notion under a different
  name* when $G.J = \emptyset$, with the side-condition
  $G.J = \emptyset$ supplied (silently in the LN, explicitly in
  Lean) by callers.

## Footnote rationale ($J$-inclusion in the target set)

The LN's clause 1 conspicuously includes $J$ in the target set
of the universal -- "every walk from $A$ to $J \cup B$" rather
than just to $B$. The LN's own footnote acknowledges this is
*non-standard in the literature*; the justification is that with
$J$ included, the asymmetric separoid rules for
`id`/`i$\sigma$`-separation match the Markov-kernel CI rules
formalised in chapters $\ge 4$. Without it, the separoid rules
would diverge from CI's and force extra translation lemmas at
every CI-vs-graphical equivalence theorem downstream. We mirror
the LN's choice verbatim: the universal in `IsISigmaSeparated`
ends in `G.J ∪ B`, not just `B`.

## Conventions inherited from `SigmaBlockedWalks`

* `A`, `B`, `C : Set α`, *not* subtypes carrying `⊆ G.J ∪ G.V`.
  The LN preamble "$A, B, C \ins J \cup V$" is a side-condition
  on the inputs, *not* a type-level restriction: callers state
  it as a separate hypothesis when needed (e.g. when reflexivity
  of `Anc^G` on the set is required). Same paradigm as
  `IsSigmaBlocked` / `IsSigmaOpen`, which keep `C : Set α` and
  let callers state the side-condition. Carrying subtypes on
  every separation signature would pollute every downstream
  consumer (every claim of section 3.3, every chapter-$\ge 4$
  CI-vs-graphical equivalence) for zero proof-ergonomic gain.

* `G`-first signature with `A`, `B`, `C` after -- matches every
  other `CDMG`-level predicate (`G.Anc v`, `G.Desc v`,
  `G.IsAcyclic`, ...) and lets callers write
  `G.IsISigmaSeparated A B C` in the same prose order as the
  LN's "$A \isPerp_G B \given C$".

## Downstream usage

* **claim_3_22** ($\sigma$-separation symmetry, `graphs.tex`
  lines 1366 -- 1369) -- proves
  $A \sPerp_G B \given C \iff B \sPerp_G A \given C$ when
  $G.J = \emptyset$, consuming `IsSigmaSeparated` defined here.
* **claim_3_23 / claim_3_24** (the $\sigma$-open path
  equivalences, `graphs.tex` lines 1383 -- 1412) -- rewrite the
  universal over walks here in terms of an existential over
  $\sigma$-open paths.
* Chapters $\ge 4$ (CBNs, do-calculus, iSCMs, discovery) --
  consume `IsISigmaSeparated` as the principal graphical-
  separation predicate, paired with conditional independence on
  the associated kernels.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks` (def_3_17)
  -- same module-docstring + per-declaration design-block
  convention, source of the `Walk.IsSigmaBlocked` per-walk
  predicate we universally quantify over here.
* `Chapter3_GraphTheory.Section3_1.FamilyReachability` --
  precedent for `def CDMG.Foo (G : CDMG α) ...` shape inside
  `namespace CDMG`, enabling dot-notation `G.Foo`.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

/-! ### Clause 1: $i\sigma$-separation -/

-- def_3_18 (clause 1)
-- title: ISigmaSeparation -- the i-σ-separation predicate
--
-- `G.IsISigmaSeparated A B C` says "$A$ is $i\sigma$-separated
-- from $B$ given $C$ in $G$" (LN notation $A \isPerp_G B \given C$):
-- *every* walk from a node in $A$ to a node in $J \cup B$ is
-- $\sigma$-blocked by $C$. Three nested universal quantifiers
-- mirror the LN's "every walk from a node in $A$ to a node in
-- $J \cup B$": the start vertex $v \in A$, the end vertex
-- $w \in J \cup B$, and the walk $\pi : \text{Walk}\,G\,v\,w$.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.18,
clause 1):

  Let $G=(J,V,E,L)$ be a CDMG and $A,B,C \ins J \cup V$ (not
  necessarily disjoint) subset of nodes. We then say that:
    (1) \emph{$A$ is $i\sigma$-separated from $B$ given $C$ in $G$},
        in symbols:
          \[ A \isPerp_G B \given C, \]
        if every walk from a node in $A$ to a node in $J \cup B$
        (sic!) is $\sigma$-blocked by $C$.
  ...
  footnote: The choice to include $J$ here in this place is
    non-standard in the literature. However, if we include $J$
    in this definition here the implied (asymmetric) separoid
    rules for $id$/$i\sigma$-separation will be of the same
    form as those for Markov kernels regarding conditional
    independence. This is the reason we include $J$ here.
-/
--
-- ## Design choice
--
-- * **Three nested universals, in the LN's order.** "Every walk
--   from a node in $A$ to a node in $J \cup B$" unfolds to
--   three universals: the start vertex $v$ (in $A$), the end
--   vertex $w$ (in $J \cup B$), and the walk
--   $\pi : Walk\,G\,v\,w$. We mirror this exactly. This is the
--   slicing every downstream separoid-axiom proof reaches for:
--   in `proof-separoid-s-sep.tex` (the chapter-3 source of the
--   separoid lemmas) the proofs of *Left Decomposition*, *Right
--   Decomposition*, *J-Inverted Right Decomposition*, *Left
--   Weak Union*, *Right Weak Union*, *Extended Left Redundancy*,
--   and *J-Restricted Right Redundancy* all open with "let
--   $\pi$ be a walk from $v \in A$ to $w \in J \cup B$" and
--   proceed by manipulating exactly those three witnesses.
--   The Lean shape lets each such proof `intro v w hv hw π`
--   verbatim; a curried "exists a witness function" or a
--   bundled `WalkBetween` `structure` would force a destructure
--   on every line. The `review_design` verifier explicitly
--   validated this slicing as the obvious one for the LN's
--   separoid axioms.
--
-- * **Strict-implicit `⦃v w : α⦄` vertex binders.** The endpoint
--   vertices `v`, `w` are determined by the types of the
--   membership-hypothesis arguments `v ∈ A` and `w ∈ G.J ∪ B`;
--   strict-implicit binders let callers feed
--   `(h hv hw π)` and have Lean fill `v, w` from the
--   hypothesis types without a separate elaboration step. Plain
--   `{ }`-implicit would also work but is less robust when `A`
--   / `B` are themselves under unification (e.g. inside a
--   higher-order goal whose target is `G.IsISigmaSeparated _ _ _`),
--   where strict-implicit forces Lean to *wait* for the
--   hypothesis arguments before unifying the endpoints.
--   `(v w : α)` explicit binders would force every separoid
--   proof to name the endpoints manually before producing the
--   hypothesis -- the noisier `intro v; intro w; intro hv; ...`
--   pattern -- for no payoff. The `review_design` verifier
--   explicitly validated `⦃ ⦄` as the right convention here.
--
-- * **`Walk G v w` as the per-walk quantifier's domain.** `Walk`
--   is the def_3_4 walk-as-data type from `Section3_1.Walks`;
--   the LN's "every walk" universal becomes `∀ (π : Walk G v w)`.
--   `Walk.IsSigmaBlocked C` (def_3_17, item 2) is the per-walk
--   $\sigma$-blocking predicate from
--   `Section3_3.SigmaBlockedWalks`; we apply it via dot-notation.
--   No mathlib re-use is in play: mathlib's `SimpleGraph` has no
--   notion of bidirected edges, no input/output partition `J ∪ V`,
--   and no graphical-separation API; the entire CDMG /
--   walk / $\sigma$-blocking stack (`Section3_1.CDMG`,
--   `Section3_1.Walks`, `Section3_3.SigmaBlockedWalks`) is bespoke
--   for the LN's paradigm, so the separation predicate built on
--   top of it must be too.
--
-- * **`w ∈ G.J ∪ B`, not `w ∈ B`.** The LN's "$J \cup B$" is
--   the load-bearing footnote: including $J$ on the target side
--   makes the asymmetric separoid rules for `id`/`i$\sigma$`-
--   separation match Markov-kernel CI rules in chapters
--   $\ge 4$. We transliterate verbatim; see the module
--   docstring's "Footnote rationale" section. Dropping the
--   $J$ summand here would (i) silently break the `J-Inverted
--   Right Decomposition` and `J-Restricted Right Redundancy`
--   lemmas of `proof-separoid-s-sep.tex`, both of which *use*
--   the $J$-inclusion in their statements; and (ii) force
--   chapters $\ge 4$ to carry a "if $G.J = \emptyset$ then ..."
--   guard on every CI-vs-separation equivalence, which is the
--   exact divergence the LN's footnote is written to prevent.
--
-- * **`A B C : Set α`, not subtypes carrying `⊆ G.J ∪ G.V`.**
--   Same convention as `IsSigmaBlocked` / `IsSigmaOpen` keep on
--   `C`; we extend it to `A` and `B`. The LN preamble "$A, B, C
--   \ins J \cup V$" is a side-condition on the inputs, not a
--   type-level restriction. Carrying subtypes on every
--   separation signature would pollute every downstream
--   consumer (every claim of section 3.3, every chapter-$\ge 4$
--   CI-vs-graphical equivalence, every separoid-axiom proof in
--   `proof-separoid-s-sep.tex`) for no proof-ergonomic gain --
--   the side-condition is only ever consumed when a specific
--   lemma needs `Anc^G`-reflexivity on the set, at which point
--   the caller states it as a separate hypothesis. The
--   `review_design` verifier explicitly validated this choice.
--
-- * **`def`, not `abbrev` or `Prop` `inductive`.** A plain `def`
--   keeps the predicate opaque under standard `simp`/`rfl`
--   reductions while letting downstream rows unfold it on
--   demand via the `isISigmaSeparated_iff` `rfl`-lemma below.
--   An `abbrev` would force unfolding everywhere -- noisy in
--   downstream goals where we'd rather treat
--   $i\sigma$-separation as an atomic relation (e.g.
--   claim_3_22's $\sigma$-symmetry pivot, claim_3_25's
--   marginalization equivalence, every separoid-axiom statement
--   in chapter 4+). An `inductive` would lose the direct-
--   quantifier shape the LN writes and force every consumer
--   to destructure rather than directly `intro` the three
--   witnesses.
--
-- * **`G`-first signature for dot-notation.** Matches every
--   other `CDMG`-level predicate (`G.Anc v`, `G.Desc v`,
--   `G.IsAcyclic`, ...). Callers write
--   `G.IsISigmaSeparated A B C` in the same prose order as the
--   LN's "$A \isPerp_G B \given C$".
--
-- ## Downstream consequences
--
-- This is the principal graphical-separation predicate of the
-- whole LN; the shape we pick here propagates outward to every
-- chapter that reasons about CI.
--
-- * **claim_3_22** ($\sigma$-symmetry, this chapter's
--   `graphs.tex` lines 1366-1369): pivots between
--   `IsISigmaSeparated G A B C` and `IsISigmaSeparated G B A C`
--   under the side-condition $G.J = \emptyset$. Consumes the
--   three-nested-universal shape directly.
--
-- * **claim_3_23 / claim_3_24** ($\sigma$-open path
--   equivalences, `graphs.tex` lines 1382-1412): rewrite the
--   universal-over-walks here into either a universal-over-
--   paths or a negation-of-existential-of-$\sigma$-open-walk.
--   The defining-equation `isISigmaSeparated_iff` below is the
--   `rfl`-lemma those rewrites pivot through.
--
-- * **claim_3_25** ($i\sigma$-separation under marginalization,
--   `graphs.tex` lines 1414-1422): equates
--   `IsISigmaSeparated G A B C` with
--   `IsISigmaSeparated (G.marginalize D) A B C` under suitable
--   side conditions. The proof in the LN constructs walks in
--   one graph from walks in the other -- exactly the
--   three-witness slicing we chose.
--
-- * **claim_3_26 / claim_3_27** (acyclic simplification +
--   `lem:replace_walk`, `graphs.tex` lines 1581-1652): collapse
--   $i\sigma$-separation to $id$-separation when $G$ is acyclic
--   (and provide the walk-replacement lemma that powers
--   claim_3_23's path/walk equivalence). Both reason about
--   walks in `IsISigmaSeparated`'s universal, so they will
--   `unfold IsISigmaSeparated` (via the `_iff` lemma) and
--   manipulate the per-walk witness directly.
--
-- * **def_3_19 onwards (`id`-separation, this chapter's
--   subsection 3.4, `graphs.tex` lines 1680+)**: defines the
--   $d$-blocked variant parallel to `IsSigmaBlocked`, then
--   $id$-separation parallel to this predicate. The
--   parallelism is structural: `IsIDSeparated` will copy this
--   exact three-nested-universal shape with `IsDBlocked`
--   substituted for `IsSigmaBlocked`. Picking, say, an
--   `inductive` here would force `IsIDSeparated` to pick a
--   matching shape, doubling the proof-engineering effort on
--   every separoid-axiom lemma.
--
-- * **Chapter 4 (CBNs, `causal_bayesian_networks.tex`)**:
--   the Markov property for a CBN equates conditional
--   independence in the joint distribution to
--   `IsISigmaSeparated` on the underlying CDMG. Every such
--   equivalence statement consumes this predicate by name.
--
-- * **Chapter 5 (do-calculus, `do-calculus.tex` +
--   `proof-do-calculus.tex`)**: the three do-calculus rules
--   are stated *in terms of* `IsISigmaSeparated`
--   (Rule 1: insertion/deletion of observations; Rule 2:
--   action/observation exchange; Rule 3: insertion/deletion
--   of actions). The "if $A \isPerp_{G_*} B \given C$"
--   premise of every rule is a direct citation of this
--   predicate.
--
-- * **Chapter 6-7 (identification, `adjustment-criteria.tex` /
--   `id-algorithm.tex`)**: the backdoor / front-door / general
--   adjustment criteria are graphical conditions stated as
--   $i\sigma$-separation on a modified graph; the ID algorithm
--   itself dispatches on these conditions.
--
-- * **Chapter 8-10 (iSCMs, `scms.tex`-`scms4.tex`)**: iSCMs
--   inherit the CI-vs-separation equivalence through their
--   CDMG; counterfactual identification builds on top.
--
-- * **Chapters 11-16 (discovery, `causal_relations.tex` /
--   `minimal_sep_sets.tex` / `fci.tex`)**: FCI and ICDF
--   reason about *minimal separating sets* and *equivalence
--   classes of CDMGs* defined by $i\sigma$-separation.
--   `minimal_sep_sets.tex` lines 10-53 in particular cite
--   `A \isPerp_G B \given S \cup [Z]` and
--   `\forall Q \subsetneq Z: A \nisPerp_G B \given S \cup Q`
--   verbatim, both consuming this predicate.
--
-- ## Constraints / known limitations
--
-- * **$A, B, C \subseteq G.J \cup G.V$ is a caller's
--   side-condition, not a type-level guard.** The LN preamble
--   silently restricts $A, B, C$ to be subsets of the node
--   set $J \cup V$; we do not enforce this on the type.
--   Predicates downstream of `Anc^G(C)` silently ignore set
--   members outside the graph, so the LN's prose "$A, B, C
--   \ins J \cup V$" is meaningful only when the caller actively
--   uses it (e.g. for ancestor-reflexivity arguments in
--   `claim_3_25`). Callers are responsible for stating that
--   hypothesis when they need it.
--
-- * **No syntactic distinction between "marginal" and "non-
--   marginal" usage of $A$ / $B$.** The LN uses `IsISigmaSeparated`
--   with $A = \emptyset$ or $B = \emptyset$ at various places
--   (e.g. `J-Restricted Right Redundancy`: $A \iPerp \emptyset
--   \given C \cup J$); we make no distinction. The empty-set
--   special case for $C$ is exposed as `IsISigmaSeparatedEmpty`
--   (clause 3 below) but not for $A$ or $B$ -- the LN does
--   not name them, so neither do we.

/-- LN def 3.18, clause 1: *$A$ is $i\sigma$-separated from $B$
given $C$ in $G$*. Every walk from a node in `A` to a node in
`G.J ∪ B` is $C$-$\sigma$-blocked. The LN notation is
$A \isPerp_G B \given C$. Note the `G.J` summand on the target
side: it is the load-bearing footnote of the LN definition --
including `J` here makes the asymmetric separoid rules for
`id`/`i$\sigma$`-separation match the Markov-kernel CI rules in
chapters $\ge 4$. -/
def IsISigmaSeparated (G : CDMG α) (A B C : Set α) : Prop :=
  ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w), π.IsSigmaBlocked C

-- `rfl`-lemma exposing the underlying three-nested-universal
-- shape of `IsISigmaSeparated`. Pure unfolding aid for
-- `rw [isISigmaSeparated_iff]` -- consumers that need to
-- destructure the predicate's body cite this instead of
-- unfolding `IsISigmaSeparated` by name, keeping the `def`
-- opaque elsewhere. No further design rationale; the work is
-- on the underlying `def`.

/-- Defining equation for `IsISigmaSeparated`. Useful when
unfolding the definition directly. -/
theorem isISigmaSeparated_iff (G : CDMG α) (A B C : Set α) :
    G.IsISigmaSeparated A B C ↔
      ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w),
        π.IsSigmaBlocked C :=
  Iff.rfl

/-! ### Clause 2: the "not-separated" predicate -/

-- def_3_18 (clause 2)
-- title: ISigmaSeparation -- the negation of i-σ-separation
--
-- `G.IsNotISigmaSeparated A B C` says "$A$ is *not*
-- $i\sigma$-separated from $B$ given $C$ in $G$" -- the LN's
-- $A \nisPerp_G B \given C$. A one-line wrapper around
-- `¬ G.IsISigmaSeparated A B C`, matching the LN's "If that
-- property does not hold we will write $A \nisPerp_G B \given C$".
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.18,
clause 2):

  (2) If that property does not hold we will write:
        \[ A \nisPerp_G B \given C. \]
-/
--
-- ## Design choice
--
-- * **Definitional alias for `¬ IsISigmaSeparated`, not a fresh
--   primitive.** The LN treats $\nisPerp_G$ as *named notation*
--   for the negation, not a separate predicate. A one-line `def`
--   matches that exactly: downstream rows cite
--   `IsNotISigmaSeparated` by name when they want the LN's
--   symbol, or fall through to plain `¬ IsISigmaSeparated` when
--   classical reasoning is local. No new logical content -- this
--   is purely a *named negation*, mirroring the LN's clause-2
--   prose "we will *write*: $A \nisPerp_G B \given C$".
--
-- * **`def`, not `abbrev` -- the LN-textual asymmetry with
--   clause 4.** Clause 2 of the LN reads "we will *write*
--   $A \nisPerp_G B \given C$"; clause 4 reads "we *write*
--   $A \sPerp_G B \given C := A \isPerp_G B \given C$".
--   Surface-similar, but structurally different: clause 2
--   *names* a derived concept ("named notation for the
--   negation"), while clause 4 is *pure notation alias* under a
--   side-condition. Downstream chapters reason about
--   "not separated" as a first-class concept (e.g.
--   claim_3_24's Remark: "if $A \nisPerp_G B \given C$ holds
--   then there exists a $\sigma$-open path from $A$ to
--   $J \cup B$") -- statements that *introduce* the predicate
--   by name into hypotheses and conclusions. A `def` keeps
--   the symbol opaque in goals (so `A \nisPerp_G B \given C`
--   displays as `G.IsNotISigmaSeparated A B C`, not unfolded
--   to `¬ G.IsISigmaSeparated A B C` everywhere); the
--   `isNotISigmaSeparated_iff` `rfl`-lemma below unfolds it on
--   demand. An `abbrev` -- which we *do* use for clause 4 --
--   would force the negation to display everywhere, losing the
--   LN's clean $\nisPerp_G$ surface that downstream chapters
--   pattern on. The `review_design` verifier explicitly
--   validated this `def`-vs-`abbrev` asymmetry as the right
--   reading of the LN's textual distinction.
--
-- * **No mathlib re-use.** Mathlib has no analogue: the
--   negation is just `¬` on the underlying `Prop`. The wrapper
--   exists solely for the LN-faithfulness reason above.
--
-- ## Downstream consequences
--
-- * **claim_3_24** (`graphs.tex` lines 1395-1412): "if
--   $A \nisPerp_G B \given C$ holds, then there exists a
--   (shortest) $C$-$\sigma$-open path from a node in $A$ to a
--   node in $J \cup B$". This consumes
--   `IsNotISigmaSeparated` directly as a hypothesis,
--   producing an existential conclusion.
--
-- * **claim_3_25** ($i\sigma$-separation under marginalization,
--   `graphs.tex` lines 1414-1422): the LN's proof structure
--   contraposes through $A \nisPerp_G B \given C$ on each
--   direction of the `Iff` -- both forward and backward
--   directions start with "Suppose $A \nisPerp_{(\dots)} B
--   \given C$" and construct an open walk.
--
-- * **`proof-separoid-s-sep.tex`** (e.g. Left Weak Union, line
--   59 onwards): the LN proof of Left Weak Union opens with
--   "Let us assume the contrary: $A \niPerp B \given D \cup C$"
--   and derives a contradiction. The Lean transliteration
--   `intro h; by_contra hne; rw [isNotISigmaSeparated_iff] at hne`
--   pivots through this predicate.
--
-- * **`minimal_sep_sets.tex`** (chapter ~12, lines 12, 32, 46,
--   53): minimal-separating-set definitions cite
--   `\forall Q \subsetneq Z: X \nisPerp_G Y \mid S \cup Q`
--   verbatim -- a universal over `IsNotISigmaSeparated`, the
--   exact wrapper used by `def IsMinimalSeparator` in the
--   chapter-12 leanification.
--
-- * **chapter 4-10 CI-vs-separation theorems**: the
--   contrapositive direction ("if there's a CI failure, then
--   not separated") uses this predicate as the conclusion
--   shape, keeping the LN's $\nisPerp_G$ surface visible in
--   the goal.
--
-- ## Constraints / known limitations
--
-- * **Caller's side-condition $A, B, C \subseteq G.J \cup G.V$**
--   carries over verbatim from clause 1 -- this predicate
--   inherits whatever constraints
--   `IsISigmaSeparated` is meant to be applied under, and
--   states none of them at the type level.
--
-- * **No "decidability" infrastructure.** `IsNotISigmaSeparated`
--   is a classical negation of a universal-over-walks; we do
--   not provide a `Decidable` instance, even on `Finite α` /
--   finite-graph specialisations. The LN treats checking
--   $i\sigma$-separation as combinatorial-but-not-trivial
--   (claim_3_24's Remark: "in practice we usually check if
--   every *path* is $C$-$\sigma$-blocked or not"). Callers
--   that need decidability state it as an explicit hypothesis
--   on a path-existence reformulation.

/-- LN def 3.18, clause 2: *$A$ is **not** $i\sigma$-separated
from $B$ given $C$ in $G$*. Pure definitional alias for
`¬ G.IsISigmaSeparated A B C`; the LN notation is
$A \nisPerp_G B \given C$. -/
def IsNotISigmaSeparated (G : CDMG α) (A B C : Set α) : Prop :=
  ¬ G.IsISigmaSeparated A B C

-- `rfl`-lemma exposing the underlying negation. Pure unfolding
-- aid; consumers that need to push the `¬` through classically
-- (e.g. claim_3_24 extracting a $\sigma$-open path from "not
-- $i\sigma$-separated") cite this and then proceed with the
-- LN's contrapositive argument.

/-- Defining equation for `IsNotISigmaSeparated`. -/
theorem isNotISigmaSeparated_iff (G : CDMG α) (A B C : Set α) :
    G.IsNotISigmaSeparated A B C ↔ ¬ G.IsISigmaSeparated A B C :=
  Iff.rfl

/-! ### Clause 3: marginal $i\sigma$-separation ($C = \emptyset$) -/

-- def_3_18 (clause 3)
-- title: ISigmaSeparation -- marginal/unconditional special case
--
-- `G.IsISigmaSeparatedEmpty A B` says "$A$ is $i\sigma$-separated
-- from $B$ in $G$" (no conditioning set) -- the LN's
-- $A \isPerp_G B$ shorthand for $A \isPerp_G B \given \emptyset$.
-- A one-line wrapper around `G.IsISigmaSeparated A B ∅`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.18,
clause 3):

  (3) We also define the special case:
        \[ A \isPerp_G B \qquad :\iff \qquad A \isPerp_G B \given
        \emptyset.\]
-/
--
-- ## Design choice
--
-- * **`def`, not `abbrev`.** The LN says "We also *define* the
--   special case" -- explicitly a named definition, not just
--   notation. The textual cue ("define") sits between clause 2's
--   "we will *write*" and clause 4's "we *write*", so we follow
--   the LN's word-choice with a `def` (named, opaque) rather
--   than the `abbrev` (transparent alias) we use for clause 4.
--   Concretely, this means `A \isPerp_G B` displays as
--   `G.IsISigmaSeparatedEmpty A B` in goals, not unfolded to
--   `G.IsISigmaSeparated A B ∅` -- preserving the LN's marginal-
--   separation surface in proofs that reason at it directly.
--   The accompanying `isISigmaSeparatedEmpty_iff` `rfl`-lemma
--   and `isISigmaSeparatedEmpty_eq` substitution lemma let
--   callers unfold on demand.
--
-- * **Drops the `C` argument, fixes `C = ∅` at the signature.**
--   The LN's $A \isPerp_G B$ is the "no given" variant. We
--   mirror this shape: `IsISigmaSeparatedEmpty` takes only
--   `A B`, with `C = ∅` baked in. The alternative -- a single
--   `IsISigmaSeparated` predicate with a default
--   `C := ∅` argument -- was rejected because Lean has no
--   default-argument syntax for `Prop`-valued `def`s in a way
--   that preserves the `_iff`/`_eq` rewrites cleanly. A
--   `notation`-style alias (e.g. `notation A " ⊥σi[" G "] " B
--   => G.IsISigmaSeparated A B ∅`) was also considered and
--   rejected: the LN explicitly *names* it as a definition,
--   and a `notation` macro would lose the named hook that
--   downstream consumers cite.
--
-- * **Both `_iff` and `_eq` lemmas, not just `_iff`.** The
--   `_iff` form is the standard `rw`-target for proofs that
--   manipulate the `Prop`; the `_eq` form gives a propositional
--   equality at the `Prop` level, which `rw` can fire on goals
--   that have `IsISigmaSeparatedEmpty` appearing nested under a
--   higher-order constructor (e.g. `∃ G, G.IsISigmaSeparatedEmpty
--   A B`). Same precedent as the `IsSigmaOpen` /
--   `IsSigmaBlocked` `_iff`-lemmas in `SigmaBlockedWalks.lean`;
--   the `_eq` form is the additional rewrite Lean's typeclass
--   resolution sometimes needs.
--
-- * **No mathlib re-use.** Same reason as clause 1: there is no
--   mathlib graphical-separation predicate to specialise; this
--   is bespoke for the LN's paradigm.
--
-- ## Downstream consequences
--
-- * **`proof-separoid-s-sep.tex`** (e.g. `A \iPerp \emptyset
--   \given C \cup J` / "J-Restricted Right Redundancy"): a
--   couple of separoid lemmas state premises or conclusions
--   over the marginal predicate; those rows will dispatch on
--   `IsISigmaSeparatedEmpty` via `isISigmaSeparatedEmpty_iff`
--   to fall back to the three-witness universal.
--
-- * **Chapter 4 (CBNs) marginal CI**: the special-case
--   "unconditional independence $X_A \Indep X_B$" corresponds
--   to graphical $A \isPerp_G B$ in the CBN-Markov property
--   for $C = \emptyset$. CBN-Markov theorems specialise to
--   the marginal predicate at that point; having
--   `IsISigmaSeparatedEmpty` as a named hook lets those
--   theorem statements read cleanly.
--
-- * **Chapter 11-16 discovery**: marginal independence tests
--   are the base case of many discovery algorithms (FCI
--   skeleton phase tests $X \Indep Y \mid \emptyset$ for every
--   pair); the graphical counterpart is
--   `G.IsISigmaSeparatedEmpty {x} {y}`.
--
-- ## Constraints / known limitations
--
-- * **$A, B \subseteq G.J \cup G.V$** -- same caller's side-
--   condition as clauses 1 and 2; not enforced at the type
--   level.
--
-- * **No symmetry baked in.** Marginal $i\sigma$-separation
--   inherits clause 1's asymmetry (the $J$-on-the-target-side
--   footnote); $A \isPerp_G B$ is not equivalent to
--   $B \isPerp_G A$ in general -- only when $G.J = \emptyset$,
--   via claim_3_22's $\sigma$-symmetry route on
--   `IsSigmaSeparated`. Callers that conflate the two will
--   produce subtly wrong statements; the `_Empty` suffix is a
--   deliberate reminder that we are at the *marginal*, not
--   the *symmetric*, special case.

/-- LN def 3.18, clause 3: the *marginal* (unconditional)
$i\sigma$-separation $A \isPerp_G B$ -- "$A$ is $i\sigma$-separated
from $B$ in $G$", without a conditioning set. Defined as the
special case $C = \emptyset$ of `IsISigmaSeparated`. -/
def IsISigmaSeparatedEmpty (G : CDMG α) (A B : Set α) : Prop :=
  G.IsISigmaSeparated A B ∅

-- `rfl`-lemma exposing the underlying `IsISigmaSeparated A B ∅`
-- shape -- unfolds for proofs that need to manipulate the
-- empty conditioning set explicitly.

/-- Defining equation for `IsISigmaSeparatedEmpty`. -/
theorem isISigmaSeparatedEmpty_iff (G : CDMG α) (A B : Set α) :
    G.IsISigmaSeparatedEmpty A B ↔ G.IsISigmaSeparated A B ∅ :=
  Iff.rfl

-- Propositional-equality companion to `isISigmaSeparatedEmpty_iff`,
-- for `rw`-substitution at type level (e.g. when the predicate
-- appears under a higher-order constructor in the goal).

/-- Substitution form: marginal $i\sigma$-separation reduces to
`IsISigmaSeparated` with `C := ∅`. Useful for rewriting between
the two surfaces. -/
theorem isISigmaSeparatedEmpty_eq (G : CDMG α) (A B : Set α) :
    G.IsISigmaSeparatedEmpty A B = G.IsISigmaSeparated A B ∅ :=
  rfl

/-! ### Clause 4: $\sigma$-separation (rename for $J = \emptyset$) -/

-- def_3_18 (clause 4)
-- title: ISigmaSeparation -- σ-separation rename when J = ∅
--
-- `G.IsSigmaSeparated A B C` is the LN's "$\sigma$-separation"
-- shorthand, *renaming* $i\sigma$-separation for the special case
-- where $G$ has no input nodes ($J = \emptyset$). The LN says:
-- "For the special case $J = \emptyset$... $i\sigma$-separation
-- is also called $\sigma$-separation, and we write
-- $A \sPerp_G B \given C := A \isPerp_G B \given C$".
-- So this is *literally the same predicate*, just under a
-- different name when callers know $G.J = \emptyset$.
--
-- We deliberately do **not** bake `G.J = ∅` into the definition:
-- the LN treats $J = \emptyset$ as a *side-condition supplied by
-- the caller*, not a type-level guard. With the side-condition
-- reading, every theorem proved about `IsISigmaSeparated`
-- automatically lifts to `IsSigmaSeparated` without an extra
-- "if $G.J = \emptyset$ ..." translation step -- which is exactly
-- the LN's intent in choosing the same definitional content
-- under two names.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.18,
clause 4):

  (4) For the special case $J = \emptyset$---that is, if $G$ has
      no input nodes---$i\sigma$-separation is also called
      \emph{$\sigma$-separation}, and we write:
        \[A \sPerp_G B \given C := A \isPerp_G B \given C, \qquad
          A \nsPerp_G B \given C := A \nisPerp_G B \given C.\]
-/
--
-- ## Design choice (shared rationale for both `abbrev`s)
--
-- The two clause-4 `abbrev`s (`IsSigmaSeparated` for
-- $\sPerp_G$ and `IsNotSigmaSeparated` for $\nsPerp_G$) share
-- the LN-faithfulness rationale below; per-`abbrev` design
-- blocks immediately above each one then sharpen the
-- per-symbol consequences.
--
-- * **`abbrev`, not `def` -- the LN-textual asymmetry with
--   clause 2.** The LN's clause 4 reads "we *write*
--   $A \sPerp_G B \given C := A \isPerp_G B \given C$" -- a
--   `:=` *notation* assignment, not a "define" assignment.
--   Contrast clause 2's "we will *write* $A \nisPerp_G B \given
--   C$" (where the *notion* is the named negation, with $\nisPerp_G$
--   as its symbol), and clause 3's "we also *define* the special
--   case" (an explicit define). `abbrev` is Lean's notation-with-
--   identity-content: every theorem stated about
--   `IsISigmaSeparated` / `IsNotISigmaSeparated` automatically
--   applies to the `abbrev`-aliased form with no extra
--   unfolding, which is exactly the LN's intent in choosing the
--   same content under two names. The `review_design` verifier
--   explicitly validated this asymmetry: clause 2 = `def`
--   (named negation, LN says "write"), clause 4 = `abbrev`
--   (pure notation, LN says "we write ... := ...").
--
-- * **`G.J = ∅` is a caller's side-condition, not baked in.**
--   The LN says "*for the special case* $J = \emptyset$",
--   meaning callers know $G.J = \emptyset$ at the call site and
--   simply prefer the symbol $\sPerp_G$ to $\isPerp_G$. Baking
--   $G.J = \emptyset$ into the definition would (i) lose the
--   LN's "same notion, different name" reading; (ii) force
--   re-proving every $i\sigma$-separation theorem under the
--   $J = \emptyset$ guard before it could be applied via
--   $\sPerp_G$; and (iii) break the `abbrev` reduction (an
--   `abbrev` cannot carry an extra hypothesis without becoming
--   a `def`).
--
-- * **Two `abbrev`s, one for $\sPerp_G$ and one for $\nsPerp_G$.**
--   The LN gives both aliases in the same clause; we expose both
--   in the same lockstep so callers reach for either at face
--   value, paralleling the clause 1 / clause 2 pairing on the
--   $\isPerp_G$ side.
--
-- * **No mathlib re-use.** Same reason as the rest of the row:
--   mathlib has no graphical-separation API; these aliases
--   exist as a thin LN-notation layer over our own
--   `IsISigmaSeparated`.

-- ## Per-`abbrev` design block: `IsSigmaSeparated`
--
-- * **Pivot point for chapter-3 symmetry.** This abbrev is the
--   *exact* surface that claim_3_22's symmetry theorem
--   (`graphs.tex` lines 1366-1369) is stated on:
--   "$A \sPerp_G B \given C \iff B \sPerp_G A \given C$ when
--   $J = \emptyset$". Because it is `abbrev`-equal to
--   `IsISigmaSeparated`, callers in claim_3_22 can prove the
--   theorem by directly manipulating `IsISigmaSeparated`'s
--   three-witness universal under the $G.J = \emptyset$
--   hypothesis -- no extra unfold step, no translation lemma.
--
-- * **Inherits clause 1's three-nested-universal shape.** Every
--   downstream usage (claim_3_22, plus chapter 4+ CBN-Markov
--   theorems specialised to $G.J = \emptyset$) can `intro v w
--   hv hw π` against `IsSigmaSeparated G A B C` as if it were
--   `IsISigmaSeparated G A B C`, because the `abbrev` reduces
--   on contact.
--
-- ## Downstream consequences (`IsSigmaSeparated`)
--
-- * **claim_3_22** ($\sigma$-symmetry) -- the principal
--   consumer, the entire point of having the alias.
--
-- * **Chapter 4+** when CBN-Markov / do-calculus / discovery
--   results are specialised to graphs without input nodes
--   ($G.J = \emptyset$), they read in the LN as "$X_A \Indep
--   X_B \given X_C \iff A \sPerp_G B \given C$" -- the
--   `IsSigmaSeparated` surface keeps that prose readable in
--   Lean.
--
-- ## Constraints / known limitations (`IsSigmaSeparated`)
--
-- * **$G.J = \emptyset$ is a caller's side-condition, not a
--   type-level guard.** Stating
--   `G.IsSigmaSeparated A B C` when $G.J \neq \emptyset$ is
--   *not a type error* -- it just collapses to
--   `G.IsISigmaSeparated A B C` with the asymmetric $J$-
--   inclusion still active. Callers who write
--   `IsSigmaSeparated` without the $G.J = \emptyset$ hypothesis
--   will produce statements that read as "$\sigma$-separation"
--   in the LN's idiom but are not actually symmetric (since
--   $J$-inclusion makes them asymmetric). Be vigilant on the
--   distinction.
--
-- * **$A, B, C \subseteq G.J \cup G.V$** -- same caller's
--   side-condition as clause 1; inherited.

/-- LN def 3.18, clause 4: the $\sigma$-separation alias for
$i\sigma$-separation, used in the LN under the side-condition
$G.J = \emptyset$. Definitionally equal to `IsISigmaSeparated`,
exposed via `abbrev` for transparent substitution at call sites.
The LN notation is $A \sPerp_G B \given C$. -/
abbrev IsSigmaSeparated (G : CDMG α) (A B C : Set α) : Prop :=
  G.IsISigmaSeparated A B C

-- ## Per-`abbrev` design block: `IsNotSigmaSeparated`
--
-- * **Mirrors clause 2's `def` through `abbrev`.** The negation
--   surface on the $\sigma$-separation side is exposed as an
--   `abbrev` over `IsNotISigmaSeparated`, so the `def`-vs-
--   `abbrev` split at clauses 2 / 4 is preserved on the
--   negation pair: clause 2 = named negation (`def`,
--   `IsNotISigmaSeparated`), clause 4 negation = pure notation
--   over the named negation (`abbrev`, `IsNotSigmaSeparated`).
--   Reducing via `abbrev` rather than re-defining as
--   `¬ G.IsSigmaSeparated A B C` would also work, but keeping
--   it as `abbrev G.IsNotISigmaSeparated` preserves the LN's
--   $\nsPerp_G := \nisPerp_G$ chain of identities verbatim,
--   so the Lean reads structure-for-structure with the LN's
--   "$\nsPerp_G ... := ... \nisPerp_G ...$" line.
--
-- ## Downstream consequences (`IsNotSigmaSeparated`)
--
-- * **claim_3_22** (when contraposing $\sigma$-symmetry): the
--   contrapositive reading
--   "$A \nsPerp_G B \given C \iff B \nsPerp_G A \given C$"
--   under $G.J = \emptyset$ falls out of the same `abbrev`
--   reduction.
--
-- * **Chapter 4+** when CI failures need to surface in the
--   LN's $\nsPerp_G$ idiom (e.g. counter-example constructions
--   in chapter 8 iSCMs that exhibit a non-separating
--   conditioning set), `IsNotSigmaSeparated` is the
--   per-statement surface; the `abbrev` keeps the reasoning
--   identical to `IsNotISigmaSeparated`.
--
-- ## Constraints / known limitations (`IsNotSigmaSeparated`)
--
-- * **Inherits both `IsNotISigmaSeparated`'s and
--   `IsSigmaSeparated`'s side-conditions.** Caller must (i)
--   state $G.J = \emptyset$ for the LN-faithful reading and
--   (ii) carry $A, B, C \subseteq G.J \cup G.V$ when needed.
--   Neither is enforced at type level.

/-- LN def 3.18, clause 4 (negation alias): the $\nsPerp_G$
shorthand for $\nisPerp_G$, used in the LN under the
side-condition $G.J = \emptyset$. Definitionally equal to
`IsNotISigmaSeparated`. The LN notation is
$A \nsPerp_G B \given C$. -/
abbrev IsNotSigmaSeparated (G : CDMG α) (A B C : Set α) : Prop :=
  G.IsNotISigmaSeparated A B C

end CDMG

end Causality
