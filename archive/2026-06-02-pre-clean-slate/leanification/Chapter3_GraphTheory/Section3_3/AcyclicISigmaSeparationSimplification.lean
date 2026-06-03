import Chapter3_GraphTheory.Section3_3.AcyclicNonCollidersBlockable
import Chapter3_GraphTheory.Section3_3.ISigmaSeparation

/-!
# Acyclic simplification of the $i\sigma$-separation blocking condition (claim_3_26)

This file formalises *claim 3.26* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1581 -- 1597): a `\begin{claimmark}\begin{Rem}...\end{Rem}\end{claimmark}`
remark sitting just after def_3_18 ($i\sigma$-separation):

> If a CDMG $G$ is acyclic then all non-colliders are blockable.
> So, the partial condition for $i\sigma$-separation
> ``a blockable non-collider in $C$''
> can be simplified to ``(any) non-collider in $C$''.

The first sentence repeats claim_3_20 (already proven as
`Walk.isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`
in `AcyclicNonCollidersBlockable.lean`) and is *not* re-stated
here. The novel content is the *consequence*: under acyclicity,
clause (ii) of `Walk.IsSigmaBlocked` (def_3_17, the per-walk
$\sigma$-blocking predicate that def_3_18's $i\sigma$-separation
universally quantifies over) -- "$\exists$ a *blockable*
non-collider position in $C$" -- collapses to its weaker form
"$\exists$ a *non-collider* position in $C$".

## What this file contributes

Three theorems, all stated with `sorry` for the proofs (a
separate worker handles proving):

1. **Walk-level simplification** (under `Causality.Walk`,
   `exists_isBlockableNonColliderAt_and_mem_iff_exists_isNonColliderAt_and_mem_of_isAcyclic`)
   -- the direct LN restatement of "blockable non-collider in
   $C$ ↔ (any) non-collider in $C$" at the existential-witness
   level.

2. **$\sigma$-blocked-level simplification** (under
   `Causality.Walk`, `isSigmaBlocked_iff_simplified_of_isAcyclic`)
   -- the LN-prose form. An immediate corollary of theorem (1)
   lifted through `Walk.IsSigmaBlocked`'s defining `∨` of `∃`'s.

3. **$i\sigma$-separation lift** (under `Causality.CDMG`,
   `isISigmaSeparated_iff_simplified_of_isAcyclic`) -- plants
   the bridge identity that motivates the LN's later
   *$id$-separation* terminology (subsection 3.4, def_3_20): in
   the acyclic case $i\sigma$-separation is equivalent to
   *$id$-separation*, which is defined to bake the "(any)
   non-collider in $C$" reading into its statement.

## Why three theorems and not one

Each theorem serves a different downstream consumer profile:

* Theorem 1 is the *base lemma*: a walk-level existential
  rewrite. Any downstream row that reasons about
  $\sigma$-blocking-witness existentials under acyclicity --
  e.g. claim_3_28's non-collider characterisation in subsection
  3.4 -- pivots through this iff.
* Theorem 2 is the *LN-prose form*: it matches the LN's own
  surface ("the *partial condition* for $i\sigma$-separation...
  can be simplified to..."). The chapter-3 proofs in section 3.4
  that step directly between `IsSigmaBlocked` and the simplified
  blocking form (claim_3_29 / claim_3_30 in the LN's `id`-vs-
  $i\sigma$ comparison block) cite this iff verbatim.
* Theorem 3 is the *separation-level lift*: it's the form
  def_3_20 (*$id$-separation*) will mirror in shape, with the
  "non-collider" form baked into the definition rather than
  gated by an acyclicity hypothesis. Every chapter-$\ge 4$
  consumer that pivots between $i\sigma$- and $id$-separation
  on an acyclic CDMG cites this iff to switch surfaces.

A single bundled theorem would force every consumer to unfold
two or three layers of existential / universal quantifiers
before they can use the simplification at the appropriate
abstraction level. Splitting at the natural granularity (walk-
witness / $\sigma$-blocked / $i\sigma$-separated) makes each
call site a one-step rewrite. The three theorems are
inter-derivable in straight-line chains -- theorem 2 by
`Or.imp_right` on theorem 1 lifted through `isSigmaBlocked_iff`;
theorem 3 by quantifying theorem 2 over the three-witness
universal in `isISigmaSeparated_iff` -- so the layering carries
no extra mathematical content, only proof-ergonomic structure.

## Why no separate theorem for the LN's third paragraph

The LN's third paragraph onwards is *discussion* of the
acyclic-case terminology:

> So in the acyclic case we can simplify the notion of
> $i\sigma$-separation, which we will refer to as *$id$-separation*.
> However, in the non-acyclic setting $id$-separation ... and
> $i\sigma$-separation ... are clearly not equivalent.
>
> It turned out that in the non-acyclic case $i\sigma$-separation
> is the more general concept ...

This is naming and motivation, not a formal claim:

* The introduction of *$id$-separation* is formalised separately
  as def_3_20 in subsection 3.4 (`graphs.tex` lines 1680+).
* The non-equivalence in the non-acyclic case is a
  *counterexample* claim, handled (if/when needed) by a separate
  counterexample row.
* The FM citations (FM17 / FM18 / FM20 / BFPM21) are literature
  pointers, not formalisable.

So we stop at the three formal theorems and leave the discussion
paragraph to play its (entirely informal) motivational role.

## Why a new file (and not adding to `AcyclicNonCollidersBlockable.lean`)

The row's `data.json` title is `AcyclicNonCollidersBlockable` --
the *same* title as claim_3_20, because the LN re-uses the
first sentence verbatim across both. claim_3_20's existing Lean
file (`Section3_3/AcyclicNonCollidersBlockable.lean`) is
out-of-scope for this row: modifying it would conflate the two
claims' proof histories, break the row-file mapping, and
contradict the worker scope rule. The new file name
`AcyclicISigmaSeparationSimplification.lean` disambiguates at
the filename level while leaving the row's `data.json` title
intact, and -- more importantly -- reflects the *novel*
mathematical content of this row (the simplification of the
$i\sigma$-separation blocking condition, not the underlying
"all non-colliders blockable" fact that claim_3_20 already
provides).

## Downstream usage

* **def_3_20 (*$id$-separation*, `graphs.tex` lines 1680+)** --
  the LN's terminology introduction motivated by *this* claim.
  def_3_20 *defines* $id$-separation by baking the "any
  non-collider in $C$" reading into its statement; theorem 3
  here is the bridge identity equating $i\sigma$-separation
  with $id$-separation on an acyclic CDMG.
* **claim_3_28** (the non-collider characterisation in
  subsection 3.4) -- consumes theorem 1 to rewrite the
  existential disjunct.
* **Chapter 4+ CADMG-specific theorems** -- whenever a downstream
  theorem is stated on a CADMG (acyclic CDMG), and reasons
  through $i\sigma$-separation, theorem 3 lets it switch to the
  simpler $id$-separation surface without re-proving anything.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.AcyclicNonCollidersBlockable`
  (claim_3_20) -- the file whose existing theorem
  `Walk.isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`
  supplies the "non-collider ⇒ blockable under acyclicity"
  ingredient that the simplification rests on. The module
  docstring + per-declaration design-block convention also
  follows that file's pattern.
* `Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable`
  (def_3_16) -- defining `IsBlockableNonColliderAt` as
  `IsNonColliderAt ∧ ¬ IsUnblockableNonColliderAt` is what
  makes the converse direction ("blockable ⇒ non-collider")
  hold trivially (by `.1`) in any CDMG; only the forward
  direction needs acyclicity.
* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks` (def_3_17) --
  source of `IsSigmaBlocked` / `IsColliderAt` / `nodeAt` /
  `IsBlockableNonColliderAt` that the three theorems compose.
* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation` (def_3_18) --
  source of `IsISigmaSeparated` that theorem 3 lifts the
  simplification to.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### Walk-level: "blockable non-collider in $C$" simplifies to "non-collider in $C$" -/

-- claim_3_26 (theorem 1/3)
-- title: AcyclicNonCollidersBlockable -- walk-level simplification
-- of clause (ii) of `IsSigmaBlocked` under acyclicity
--
-- Direct LN restatement at the existential-witness level: on any
-- walk $\pi$ in an acyclic CDMG, the existence of a *blockable*
-- non-collider position whose vertex lies in $C$ is equivalent to
-- the existence of *any* non-collider position whose vertex lies
-- in $C$. The forward direction holds in every CDMG (blockable ⇒
-- non-collider, by definition); the backward direction is the
-- application of claim_3_20 -- under acyclicity, every non-collider
-- on every walk is blockable.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (claim_3_26,
lines 1581 -- 1597):

\begin{claimmark}
\begin{Rem}
    If a CDMG $G$ is acyclic then all non-colliders are blockable.
    So, the partial condition for $i\sigma$-separation
    ``a blockable non-collider in $C$''
    can be simplified to ``(any) non-collider in $C$''.

    So in the acyclic case we can simplify the notion of $i\sigma$-separation,
    which we will refer to as \emph{$id$-separation}.
    However, in the non-acyclic setting $id$-separation (``(any) non-collider in $C$'')
    and $i\sigma$-separation (``a blockable non-collider in $C$'') are clearly not equivalent.

    It turned out that in the non-acyclic case $i\sigma$-separation is the more general
    concept (and as said above it also captures the acyclic case equivalently well),
    see \cite{FM17,FM18,FM20,BFPM21}.
    We will first focus on CADMGs (acyclic) for which we can restrict ourselves to the
    somewhat simpler $id$-separation.
    Later, we will pick up $i\sigma$-separation again when we deal with cycles.
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Iff, not a one-way replace.** The LN's "*can be simplified
--   to*" cleanly reads in either direction: the simplified
--   non-collider form is the LN's *id*-separation-style reading;
--   the original blockable form is the LN's $i\sigma$-separation-
--   style reading. Both downstream pivot directions are needed
--   (id ⇒ $i\sigma$ to apply a claim known about
--   $i\sigma$-separation in the simpler $id$-form; $i\sigma$ ⇒ id
--   to discharge an $i\sigma$-separation goal via the simpler
--   $id$-form), so an `Iff` is the natural shape.
--
-- * **Walk-level (existential over positions), not bundled with
--   the surrounding `IsSigmaBlocked` disjunction.** Theorem 2
--   below is the bundled form. Keeping this iff at the existential-
--   witness level lets downstream proofs apply it under the
--   `IsSigmaBlocked`'s second disjunct *without* re-deriving the
--   first disjunct (which is unaffected by the simplification).
--   `Or.imp_right` (or its `Iff` companion) lifts this iff into
--   the bundled form for theorem 2.
--
-- * **`{v w : α}` implicit, `(π : Walk G v w)` explicit,
--   `(C : Set α)` explicit.** Mirrors the signature of claim_3_20
--   (which has `(π : Walk G v w)` explicit and `{v w : α}`
--   implicit, with the position `k` implicit because it is
--   inferable from the non-collider hypothesis). Here `C` is
--   explicit because it varies across consumers (we are not
--   inside a universal-over-$C$ binder), and the positional `k`
--   appears under the existential so it is not part of the
--   signature.
--
-- * **Theorem name** (long but mathlib-conventional):
--   `exists_isBlockableNonColliderAt_and_mem_iff_exists_isNonColliderAt_and_mem_of_isAcyclic`.
--   The LHS shape (`∃ k, IsBlockableNonColliderAt k ∧ ... ∈ C`)
--   is encoded by `exists_isBlockableNonColliderAt_and_mem`; the
--   RHS shape (`∃ k, IsNonColliderAt k ∧ ... ∈ C`) by
--   `exists_isNonColliderAt_and_mem`; the `iff` joins them; the
--   `_of_isAcyclic` trailing tag advertises the precondition.
--   Reads top-to-bottom as the theorem statement.
--
-- * **`namespace Walk` placement, dot-notation reach.** Matches
--   the Walk-level namespace of `IsBlockableNonColliderAt` /
--   `IsNonColliderAt` (def_3_15 / def_3_16) -- the per-position
--   predicates this iff rewrites between -- and of
--   `isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic` in
--   claim_3_20's file. Callers reach for it via dot-notation on
--   `π`, paralleling claim_3_20's dot-projection style.

/-- claim_3_26 (theorem 1/3, walk-level simplification): on a
walk $\pi$ in an acyclic CDMG, the existence of a *blockable*
non-collider position in $C$ is equivalent to the existence of
*any* non-collider position in $C$. The forward direction is
the definition `IsBlockableNonColliderAt → IsNonColliderAt` (via
`.1`); the backward direction is claim_3_20
(`isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`)
applied to the witness. -/
theorem exists_isBlockableNonColliderAt_and_mem_iff_exists_isNonColliderAt_and_mem_of_isAcyclic
    (hG : G.IsAcyclic) {v w : α} (π : Walk G v w) (C : Set α) :
    (∃ k, π.IsBlockableNonColliderAt k ∧ π.nodeAt k ∈ C) ↔
      (∃ k, π.IsNonColliderAt k ∧ π.nodeAt k ∈ C) := by
  constructor
  · rintro ⟨k, hBlock, hMem⟩
    exact ⟨k, hBlock.1, hMem⟩
  · rintro ⟨k, hNon, hMem⟩
    exact ⟨k, isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic hG π hNon, hMem⟩

/-! ### $\sigma$-blocked-level: the LN-prose form of the simplification -/

-- claim_3_26 (theorem 2/3)
-- title: AcyclicNonCollidersBlockable -- σ-blocked-level
-- simplification of the blocking condition under acyclicity
--
-- The LN-prose form: under acyclicity, $\pi$ is $C$-$\sigma$-blocked
-- iff there exists a collider on $\pi$ outside $\Anc^G(C)$, OR
-- there exists *any* non-collider on $\pi$ in $C$. The collider
-- disjunct is unchanged from def_3_17; the non-collider disjunct
-- weakens from *blockable* non-collider (def_3_17, clause (ii))
-- to any non-collider, by theorem 1 above.
--
-- ## Design choice
--
-- * **Mirrors `isSigmaBlocked_iff`'s shape, with the second
--   disjunct's `IsBlockableNonColliderAt` replaced by
--   `IsNonColliderAt`.** This is the "simplified `IsSigmaBlocked`"
--   the LN's prose names verbatim ("the partial condition for
--   $i\sigma$-separation ``a blockable non-collider in $C$'' can
--   be simplified to ``(any) non-collider in $C$''"). Keeping the
--   collider disjunct identical reflects the LN's surgical-replace
--   wording: only clause (ii) simplifies; clause (i) is unaffected.
--
-- * **Iff, not a one-way rewrite.** Same reason as theorem 1: the
--   LN's "can be simplified" reads both ways, and both directions
--   are downstream-needed (forward to discharge $i\sigma$-blocked
--   goals via the simpler form; backward to lift simpler-form
--   witnesses back into the $i\sigma$-blocked surface for theorems
--   stated in def_3_17 vocabulary).
--
-- * **Corollary of theorem 1 by `Or.imp_right` (or `Or.congr`
--   right).** The proof is straight-line: unfold `IsSigmaBlocked`'s
--   defining `Or` of `∃`'s (via `isSigmaBlocked_iff`), keep the
--   collider disjunct fixed, and apply theorem 1 to the non-
--   collider disjunct. No new mathematics; this theorem is the
--   bundled-disjunction form of the same underlying simplification.
--
-- * **Signature mirrors theorem 1; `namespace Walk` placement.**
--   Same binder shape as theorem 1 (`{v w : α}` implicit,
--   `(π : Walk G v w)` and `(C : Set α)` explicit) -- see
--   theorem 1's design block for the rationale (claim_3_20's
--   signature; `C` explicit because it varies across consumers).
--   Identical positional structure means callers can chain
--   theorem 1 / theorem 2 without re-binding. `namespace Walk`
--   matches `IsSigmaBlocked`'s own namespace (def_3_17) so
--   consumers reach for the iff via dot-notation
--   `π.isSigmaBlocked_iff_simplified_of_isAcyclic hG C`.

/-- claim_3_26 (theorem 2/3, $\sigma$-blocked-level simplification):
under acyclicity, the $C$-$\sigma$-blocked predicate of def_3_17 is
equivalent to its *simplified* form in which the second existential
disjunct weakens from "*blockable* non-collider in $C$" to "(any)
non-collider in $C$". The collider disjunct is unchanged. The LN
prose-form of the claim, the bundled corollary of theorem 1. -/
theorem isSigmaBlocked_iff_simplified_of_isAcyclic
    (hG : G.IsAcyclic) {v w : α} (π : Walk G v w) (C : Set α) :
    π.IsSigmaBlocked C ↔
      (∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C) ∨
      (∃ k, π.IsNonColliderAt k ∧ π.nodeAt k ∈ C) := by
  rw [Walk.isSigmaBlocked_iff]
  exact or_congr Iff.rfl
    (exists_isBlockableNonColliderAt_and_mem_iff_exists_isNonColliderAt_and_mem_of_isAcyclic
      hG π C)

end Walk

namespace CDMG

variable {G : CDMG α}

/-! ### $i\sigma$-separation lift: the bridge identity for *$id$-separation* -/

-- claim_3_26 (theorem 3/3)
-- title: AcyclicNonCollidersBlockable -- $i\sigma$-separation
-- lift, the bridge identity motivating *$id$-separation*
--
-- The $i\sigma$-separation-level statement of the simplification:
-- under acyclicity, $A \isPerp_G B \given C$ is equivalent to "for
-- every walk from $A$ to $J \cup B$, the simplified blocking
-- condition holds" -- where the simplified blocking condition is
-- the disjunction of theorem 2. This is the bridge identity that
-- the LN's third paragraph motivates: *$id$-separation* (def_3_20,
-- subsection 3.4) is defined to bake the simplified blocking
-- condition into its statement, and theorem 3 here is the iff that
-- equates the two surfaces on an acyclic CDMG.
--
-- ## Design choice
--
-- * **Mirrors `isISigmaSeparated_iff`'s three-nested-universal
--   shape.** def_3_18's `IsISigmaSeparated` quantifies over three
--   witnesses (`v ∈ A`, `w ∈ G.J ∪ B`, `π : Walk G v w`); we keep
--   the exact same three-witness shape on the RHS, just replacing
--   the inner `π.IsSigmaBlocked C` body with the simplified
--   disjunction. This guarantees that callers who pivot through
--   theorem 3 can `intro v w hv hw π` against the RHS exactly as
--   they would against `IsISigmaSeparated` -- no extra unfolding,
--   no re-binding of variables.
--
-- * **Strict-implicit `⦃v w : α⦄` binders, same as
--   `IsISigmaSeparated`.** See `ISigmaSeparation.lean`'s
--   design-choice block for the rationale (callers feed
--   `(h hv hw π)` and have Lean fill the endpoints from the
--   hypothesis types). We preserve the exact same binder shape on
--   the RHS so the iff reads as a literal surface substitution.
--
-- * **Iff at the separation-predicate level, not lifted into
--   *$id$-separation* directly.** *$id$-separation* (the LN's
--   def_3_20) is defined later, in subsection 3.4; this row sits
--   in subsection 3.3 and cannot reach for `IsIDSeparated` (it
--   does not yet exist). Stating the simplification in the
--   *unbundled* form ("the universal over the simplified
--   blocking disjunction") lets def_3_20 then introduce
--   *$id$-separation* with the simplified body as its definition
--   and cite this theorem to derive the
--   $i\sigma$-vs-$id$-separation equivalence on acyclic CDMGs.
--
-- * **Corollary of theorem 2 by quantifying through the three
--   `IsISigmaSeparated` witnesses.** The proof is straight-line:
--   unfold `isISigmaSeparated_iff` to expose the three-nested
--   universal, then apply theorem 2 pointwise inside the
--   universally-bound walk's `π.IsSigmaBlocked C` body.
--
-- * **`namespace CDMG` placement, dot-notation
--   `G.isISigmaSeparated_iff_simplified_of_isAcyclic`.** Matches
--   `IsISigmaSeparated`'s `CDMG`-level namespace; consumers reach
--   for it via `G.isISigmaSeparated_iff_simplified_of_isAcyclic
--   hG A B C` in prose order.

/-- claim_3_26 (theorem 3/3, $i\sigma$-separation lift): under
acyclicity, $A$ is $i\sigma$-separated from $B$ given $C$ in $G$
iff every walk from a node in $A$ to a node in $G.J ∪ B$
satisfies the *simplified* blocking condition -- a collider
outside $\Anc^G(C)$, or *any* non-collider in $C$. The bridge
identity motivating the LN's introduction of *$id$-separation*
(def_3_20, subsection 3.4) as a more economical surface on
acyclic CDMGs. -/
theorem isISigmaSeparated_iff_simplified_of_isAcyclic
    (hG : G.IsAcyclic) (A B C : Set α) :
    G.IsISigmaSeparated A B C ↔
      ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w),
        (∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C) ∨
        (∃ k, π.IsNonColliderAt k ∧ π.nodeAt k ∈ C) := by
  rw [CDMG.isISigmaSeparated_iff]
  refine forall_congr' (fun v => forall_congr' (fun w =>
    imp_congr_right (fun _ => imp_congr_right (fun _ =>
      forall_congr' (fun π => ?_)))))
  exact Walk.isSigmaBlocked_iff_simplified_of_isAcyclic hG π C

end CDMG

end Causality
