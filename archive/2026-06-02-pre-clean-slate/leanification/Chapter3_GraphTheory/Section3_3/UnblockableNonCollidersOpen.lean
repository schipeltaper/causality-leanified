import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

-- TeX statement: claim_3_21_statement_UnblockableNonCollidersOpen.tex
-- TeX proof: claim_3_21_proof_UnblockableNonCollidersOpen.tex

/-!
# Unblockable non-colliders are always σ-open (claim_3_21)

This file formalises *claim 3.21* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1343 -- 1346): a `\begin{claimmark}` note sitting *inside* the
def_3_17 ($\sigma$-blocked walks) defmark, immediately after
the (1)/(2) clauses listing the $\sigma$-open / $\sigma$-blocked
conditions:

> Note that unblockable non-colliders are always
> $C$-$\sigma$-open, regardless of the subset
> $C \subseteq V \cup J$.

Under our def_3_17 paradigm (`IsSigmaOpen` / `IsSigmaBlocked`
in `Section3_3/SigmaBlockedWalks.lean`), the LN's walk-level
"regardless of $C$" reading reduces to a *per-position* fact:
at an unblockable non-collider position `k` on a walk,
*neither* of the two $\sigma$-open / $\sigma$-blocking gating
predicates can fire -- neither `IsColliderAt k` nor
`IsBlockableNonColliderAt k`. Hence the universals in
`IsSigmaOpen` skip such a `k` vacuously, and the existentials
in `IsSigmaBlocked` cannot witness blocking at `k`, for any
choice of conditioning set `C ⊆ V ∪ J`.

## What this file contributes

A single `theorem`,
`Walk.not_isColliderAt_and_not_isBlockableNonColliderAt_of_isUnblockableNonColliderAt`,
with the position-level statement: an unblockable non-collider
position is *neither* a collider *nor* a blockable
non-collider:

```
(π : Walk G v w) {k : ℕ}
  (h : π.IsUnblockableNonColliderAt k) :
  ¬ π.IsColliderAt k ∧ ¬ π.IsBlockableNonColliderAt k
```

The proof is a short two-conjunct unfolding: the collider
negation comes from `IsUnblockableJoint`'s first conjunct via
the joint-case recursion, surfaced at the walk level by
`IsNonColliderAt_of_isUnblockableNonColliderAt` (whose
`IsNonColliderAt`-witness's second projection *is*
`¬ IsColliderAt k`); the blockable negation is immediate from
the *definition*
`IsBlockableNonColliderAt k := IsNonColliderAt k ∧
¬ IsUnblockableNonColliderAt k` -- its second conjunct
directly contradicts the standing
`IsUnblockableNonColliderAt k` hypothesis.

## Downstream usage

* **def_3_17** ($\sigma$-blocked walks, `graphs.tex` lines
  1326 -- 1348) -- the very definition this claim is the
  trailing note of. The design block on `IsSigmaOpen` in
  `SigmaBlockedWalks.lean` (lines 359 -- 375) explicitly
  anticipates this claim: it observes that `IsSigmaOpen`'s
  blockable-non-collider clause is vacuously satisfied at
  unblockable positions under our
  `IsBlockableNonColliderAt`-only reading, and points to
  claim_3_21 as the formal statement of that observation.
* **claim_3_22** ($\sigma$-separation symmetry, `graphs.tex`
  lines 1366 -- 1369) -- pivots between `IsSigmaOpen` and
  `IsSigmaBlocked` via the De-Morgan dual. Symmetry proofs use
  the position-wise fact that unblockable non-colliders "drop
  out" of both quantifiers, which is the conjunction this
  theorem packages.
* **claim_3_23 / claim_3_24** ($\sigma$-separation
  equivalences, `graphs.tex` lines 1383 -- 1412) -- rewrite
  $\sigma$-blocked walks in terms of $\sigma$-open paths and
  vice versa; the "unblockable non-colliders contribute
  nothing to blocking" observation is reused at every
  reduction.
* Chapters $\ge 4$ (do-calculus, identification, iSCMs) consume
  $\sigma$-separation through def_3_18 and indirectly inherit
  this observation whenever they reason about which walks
  block $A$-$B$ pairs given $C$.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.AcyclicNonCollidersBlockable`
  -- the immediately preceding claim in this subsection
  (claim_3_20). Same one-row claim file pattern: module-level
  docstring with "What this file contributes" / "Downstream
  usage" / "Style precedents" sections; per-declaration
  `-- claim_3_21 / title / ...` comment header; LN block
  reproduced verbatim in a `/- ... -/` quote; design-choice
  block. Stays in `namespace Walk` so callers reach for it via
  dot-projection on a walk.
* `Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable`
  -- source of `IsUnblockableNonColliderAt`,
  `IsBlockableNonColliderAt`, and the
  `IsNonColliderAt_of_isUnblockableNonColliderAt` /
  `not_isUnblockableNonColliderAt_zero` /
  `not_isUnblockableNonColliderAt_length` helpers the future
  proof will lean on.
* `Chapter3_GraphTheory.Section3_3.CollidersAndNon` -- source
  of `IsColliderAt` / `IsNonColliderAt`.
* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks` -- source
  of `IsSigmaOpen` / `IsSigmaBlocked`. The statement here does
  *not* literally mention them, but they are the vocabulary
  the LN's "$C$-$\sigma$-open" claim is phrased in, and every
  downstream consumer will read this theorem alongside them;
  importing `SigmaBlockedWalks` makes both the file's design
  rationale and downstream uses self-contained.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

-- claim_3_21
-- title: UnblockableNonCollidersOpen -- an unblockable non-collider
-- position is neither a collider nor a blockable non-collider,
-- hence (regardless of $C$) it can witness neither of
-- $\sigma$-blocking's two clauses
--
-- The LN's walk-level "unblockable non-colliders are always
-- $C$-$\sigma$-open, regardless of $C$" reduces, under our def_3_17
-- paradigm, to a per-position fact about the two gating predicates
-- of `IsSigmaOpen` / `IsSigmaBlocked`: at an unblockable
-- non-collider position `k`, *neither* `IsColliderAt k` *nor*
-- `IsBlockableNonColliderAt k` can hold. Consequently:
--   * `IsSigmaOpen C`'s clause (i) (`∀ k, IsColliderAt k → ...`)
--     skips `k` vacuously;
--   * `IsSigmaOpen C`'s clause (ii) (`∀ k, IsBlockableNonColliderAt
--     k → ...`) skips `k` vacuously;
--   * the dual `IsSigmaBlocked C` cannot witness blocking at `k`.
-- All three are vacuous *regardless of* the conditioning set `C`,
-- which is exactly the LN's "regardless of $C$" phrasing.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (claim_3_21,
lines 1343 -- 1346, the trailing claimmark inside the def_3_17
defmark):

  % claim_3_21
  \begin{claimmark}
  Note that unblockable non-colliders are always $C$-$\sigma$-open,
  regardless of the subset $C \ins V \cup J$.
  \end{claimmark}
-/
--
-- ## Design choice
--
-- * **Position-level conjunction, not walk-level universal over
--   $C$.** The LN says "unblockable non-colliders are always
--   $C$-$\sigma$-open, regardless of $C$". Read literally, this
--   looks like a walk-level claim ("the walk is $\sigma$-open");
--   read carefully, it is a per-position observation about what
--   an unblockable non-collider position can contribute on a walk
--   (regardless of any $C$). Our `IsSigmaOpen` (def_3_17, item 1)
--   takes the form `(∀ k, IsColliderAt k → ...) ∧ (∀ k,
--   IsBlockableNonColliderAt k → ...)`: both universal antecedents
--   are walk-level *position predicates*, not the predicate
--   "$v_k$ is unblockable". So the faithful reading of the LN is
--   per-position: *at an unblockable non-collider $k$*, the
--   $\sigma$-open / $\sigma$-blocked clauses' gating predicates
--   both fail, and so the position contributes nothing to either
--   side -- regardless of $C$. Other positions on the same walk
--   may very well witness blocking or openness; the LN's "always"
--   refers to the position, not the walk.
--
-- * **The conjunction is `C`-free: "regardless of $C$" is a
--   corollary of the statement's *shape*, not a quantifier
--   over it.** The conclusion `¬ IsColliderAt k ∧
--   ¬ IsBlockableNonColliderAt k` mentions neither `C` nor any
--   set built from it -- it is a per-position primitive whose
--   two conjuncts are *exactly the negations of* the gating
--   antecedents of `IsSigmaOpen C`'s two universals in
--   `SigmaBlockedWalks.lean`. Once discharged at a position
--   `k`, both of `IsSigmaOpen C`'s universals are vacuously
--   satisfied at the `k`-th instance *for any* $C \subseteq
--   V \cup J$, with no second proof step needed. This is the
--   structural reason the LN's universal over $C$ collapses
--   into a $C$-free statement rather than surviving as an
--   enclosing quantifier: the per-position primitive *is* the
--   thing-being-claimed, and the LN's walk-level "always" is
--   its propagation across positions. (The `review_design` /
--   `verify_equivalence` verifiers crystallised this as the
--   "$C$-free per-position primitive" framing; both passed on
--   it as the right factoring of the LN claim.)
--
-- * **Single conjunctive theorem, not two split lemmas.** The LN
--   states one observation -- "neither side of $\sigma$-blocking
--   can fire at an unblockable non-collider position" -- and
--   every downstream consumer (claim_3_22's symmetry pivot,
--   claim_3_23 / 3_24's $\sigma$-separation equivalences,
--   chapter-$\ge 4$ $\sigma$-separation reasoning) reaches for
--   the conjunction as a unit, not for one half. Mirroring the
--   LN's single sentence as a single conjunctive theorem keeps
--   the API ergonomic; consumers needing just one half extract
--   it via `(this).1` / `(this).2`. (One could *additionally*
--   expose the two conjuncts as named accessors if downstream
--   readers turn out to need them by-name; that's a follow-up
--   judgment call, not load-bearing for this row.)
--
-- * **Alternative shape considered and rejected: walk-level
--   `∀ C, π.IsSigmaOpen C`.** Quantifying over $C$ at the walk
--   level looks like a direct transcription of the LN's
--   "regardless of $C$" phrasing, but it is too strong: it
--   requires *no* colliders and *no* blockable non-colliders
--   anywhere on the walk, which the LN does *not* claim. A walk
--   with even one collider position would falsify the universal
--   for $C$ such that $v_{\text{collider}} \notin \Anc^G(C)$;
--   yet such a walk can still host unblockable non-collider
--   positions, and the LN observation is supposed to apply to
--   *each such position individually*. The per-position reading
--   is the only LN-faithful one.
--
-- * **Alternative shape considered and rejected: walk-level
--   "for any walk in which every non-collider is unblockable,
--   the walk is $C$-$\sigma$-open for all $C$".** This is also
--   strictly stronger than the LN claim and conflates the
--   per-position observation with a walk-level closure. The LN
--   is talking about what unblockable positions contribute, not
--   characterising walks built entirely from such positions.
--
-- * **Imports `SigmaBlockedWalks`, not just
--   `BlockableAndUnblockable`.** The *statement* this row
--   formalises does not literally mention `IsSigmaOpen` /
--   `IsSigmaBlocked`; the minimal import for type-checking the
--   conjunction `¬ IsColliderAt k ∧ ¬ IsBlockableNonColliderAt k`
--   is `BlockableAndUnblockable.lean` (which itself imports
--   `CollidersAndNon.lean`). We nonetheless import
--   `SigmaBlockedWalks.lean` because (a) the file's *role* --
--   and the module docstring's "Downstream usage" -- is phrased
--   in terms of `IsSigmaOpen` / `IsSigmaBlocked`; (b) every
--   downstream consumer of this theorem already lives in that
--   vocabulary, so co-locating the import keeps the dependency
--   graph aligned with the conceptual graph; (c) the design
--   block on `IsSigmaOpen` (`SigmaBlockedWalks.lean` lines
--   359 -- 375) explicitly anticipates this claim, so the
--   forward and backward cross-references are intact. The cost
--   is minimal: `SigmaBlockedWalks.lean` transitively re-exports
--   the `BlockableAndUnblockable` API anyway.
--
-- * **`namespace Walk` placement, walk explicit, position
--   implicit.** Same convention as
--   `isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`
--   in `AcyclicNonCollidersBlockable.lean`: the theorem reads
--   as a property of a walk's position predicates; callers reach
--   for it via dot-projection
--   `π.not_isColliderAt_and_not_isBlockableNonColliderAt_of_isUnblockableNonColliderAt h`.
--   The position `k` is implicit (inferable from `h`); the walk
--   `π` is explicit (passed positionally).
--
-- * **Name
--   `not_isColliderAt_and_not_isBlockableNonColliderAt_of_isUnblockableNonColliderAt`.**
--   Standard Mathlib `_of_...` convention: conclusion first
--   (the conjunction `¬ IsColliderAt ∧
--   ¬ IsBlockableNonColliderAt`), then the hypothesis
--   (`IsUnblockableNonColliderAt`). The name is verbose but
--   reads word-for-word as the theorem statement, matching the
--   `_of_..._of_..._of_...` precedent of
--   `isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`
--   in the sister file.

/-- claim_3_21 (`UnblockableNonCollidersOpen`): an *unblockable*
non-collider position on a walk `π` is *neither* a collider position
*nor* a blockable non-collider position. Consequently it is skipped
vacuously by both clauses of `IsSigmaOpen C` and cannot witness
either clause of `IsSigmaBlocked C`, *regardless of* the conditioning
set `C` -- which is the LN's "unblockable non-colliders are always
$C$-$\sigma$-open, regardless of $C \subseteq V \cup J$". -/
theorem not_isColliderAt_and_not_isBlockableNonColliderAt_of_isUnblockableNonColliderAt
    {v w : α} (π : Walk G v w) {k : ℕ}
    (h : π.IsUnblockableNonColliderAt k) :
    ¬ π.IsColliderAt k ∧ ¬ π.IsBlockableNonColliderAt k :=
  ⟨(IsNonColliderAt_of_isUnblockableNonColliderAt π k h).2, fun hb => hb.2 h⟩

end Walk

end Causality
