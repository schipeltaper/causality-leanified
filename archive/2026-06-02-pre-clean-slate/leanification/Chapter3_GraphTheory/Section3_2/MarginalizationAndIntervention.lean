import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.Marginalization
import Chapter3_GraphTheory.Section3_2.MarginalizationPreserves

-- TeX statement: tex/claim_3_18_statement_MarginalizationAndIntervention.tex
-- TeX proof:    tex/claim_3_18_proof_MarginalizationAndIntervention.tex

/-!
# Marginalization and intervention commute (claim_3_18)

This file formalises the lecture notes' lemma "marginalization and
intervention commute" -- `lecture-notes/lecture_notes/graphs.tex` Lem
at lines 1122 -- 1129. The LN states the equality

  `(G_{do(W₁)})^{\sm W₂} = (G^{\sm W₂})_{do(W₁)}`

under the preconditions `W₁ ⊆ J ∪ V`, `W₂ ⊆ V`, and `W₁, W₂`
disjoint. In our Lean encoding the two subset preconditions are
unnecessary: both `G.hardInterventionOn W`
(`Section3_2/HardInterventionOn.lean`) and `G.marginalize W`
(`Section3_2/Marginalization.lean`) are intentionally total
functions of `Set α` by design (each cites *composition with the
other op* as a load-bearing motivation for dropping the
precondition; this very row is that composition). The equality then
holds component-wise on `(J, V, E, L)` for arbitrary
`W₁, W₂ : Set α` once `Disjoint W₁ W₂` is in hand. The disjointness
hypothesis *is* kept -- it is load-bearing in the LN's `E` and `L`
analysis: intermediate nodes in `W₂` must avoid `W₁` for the
`hardInterventionOn` edge deletions to be transparent to the
walk-existential conditions on `marginalize`'s edge sets.

The LN's trailing prose sentence ("A similar statement holds for
marginalizations and adding intervention nodes, and also for
marginalizations and node-splitting interventions") is a forward
pointer, not a numbered claim of its own. It is not formalised at
this row; a downstream row will pick up each analogue
(marginalization vs. `addInterventionNodes`, marginalization vs.
`nodeSplittingOn`) separately if a downstream chapter cites it.

This row is the third of a small family of "two CDMG transformations
commute" theorems in Section 3.2, alongside
`HardInterventionsCommute.lean` (claim_3_4, two hard interventions)
and `MarginalizationsCommute.lean` (claim_3_17, two marginalizations).
Unlike its twins, the LN equality here is a *single* identity rather
than a chained fusion + commute pair: the two operations being
composed are different operators, so there is no analogue of
`Set.union_comm`-driven collapse, and a single theorem suffices.

## Where this gets used downstream

* **`graphs.tex` Section 3.3, $i\sigma$-separation stability
  arguments.** The lemma
  `lem:stability_separation_marginalization`
  (`graphs.tex` around line 1416) and its intervention-side
  partner need to compose the two graph-side operations freely on
  the way to the joint stability theorem; this row's equality is
  the rewrite that flattens "intervene-then-marginalize" into
  "marginalize-then-intervene" (or vice versa) so that the
  separation argument can apply the intervention last regardless
  of the order in which the user states the two operations. Both
  directions of the rewrite are used because some downstream
  consumers fix the intervention order and others fix the
  projection order.
* **claim_3_19** (`graphs.tex` Lem at line 1167, "Marginalizing
  out the output part of split nodes equals hard intervention")
  -- expresses `G_{do(W)}` as a marginalized SWIG; assembling the
  isomorphism requires composing the SWIG construction with
  marginalization and then rewriting to a single hard intervention.
  The present commutation lemma feeds into that rewrite chain in
  tandem with claim_3_17 (marginalizations commute) and the
  SWIG ↔ hard-intervention bridge.
* **Chapter 4 (CBNs) and Chapter 5 (do-calculus).** Intervention
  on a latent-projected graph and latent projection of an
  intervened graph appear interchangeably across identification
  arguments. Whenever the do-calculus rules are applied to a
  graph that already has latent variables marginalised out, the
  commutation lemma is what reconciles the
  apply-then-marginalize form with the apply-after-marginalize
  form in the chapter's lemma statements -- without it, every
  identification proof would carry an extra "swap" step.
* **Chapters 6 -- 16 (identification, the ID algorithm, FCI /
  ICDF discovery).** The latent-projection / hidden-variable
  compression machinery is fused with the do-operator pervasively
  in the identification half of the notes (ID algorithm,
  c-component machinery, adjustment criteria), and with the
  conditional-independence side of the discovery half (FCI,
  ICDF). Every identification proof that hides a latent variable
  while also intervening on a different one is one rewrite of
  this lemma away from the "marginalize first" canonical form
  that the downstream lemmas expect.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- claim_3_18
-- title: MarginalizationAndIntervention
--
-- Marginalization and hard intervention commute on disjoint subsets:
-- `(G_{do(W₁)})^{\sm W₂} = (G^{\sm W₂})_{do(W₁)}`. The two
-- transformations (`hardInterventionOn`, def_3_10; `marginalize`,
-- def_3_14) are the two foundational graph rewrites of Section 3.2;
-- this lemma says they can be applied in either order on disjoint
-- subsets without changing the resulting CDMG. The LN equality is a
-- single identity (no fusion-into-a-third-operation as in the two
-- structural twins claim_3_4 / claim_3_17), so the natural Lean
-- shape is one theorem, not a fusion-plus-commute pair.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 1122 -- 1129):

\begin{claimmark}
\begin{Lem}[Marginalization and intervention commute]
      Let $G=(J,V,E,L)$ be a CDMG and $W_1 \ins J \cup V$ and $W_2 \ins V$ two disjoint subsets of nodes from $G$.
      Then we have:
      \[ \lp G_{\doit(W_1)} \rp^{\sm W_2} = \lp G^{\sm W_2} \rp_{\doit(W_1)}. \]
      A similar statement holds for marginalizations and adding intervention nodes, and also for marginalizations and node-splitting interventions.
\end{Lem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Single equality, not a fusion + commute split.** Unlike the
--   two structural twins -- claim_3_4
--   (`hardInterventionOn_hardInterventionOn` + `hardInterventionOn_comm`
--   in `HardInterventionsCommute.lean`) and claim_3_17
--   (`marginalize_marginalize` + `marginalize_comm` in
--   `MarginalizationsCommute.lean`) -- the two ops being composed
--   here are *different* functions on `Set α`
--   (`hardInterventionOn` and `marginalize`), not the same op
--   composed with itself. There is no third operation `g` such
--   that `(G.hardInterventionOn W₁).marginalize W₂ = G.g (W₁ ⊕ W₂)`
--   for any binary `⊕` on `Set α`, so no fusion form is available.
--   The LN's own displayed equation has only two terms (a single
--   `=`, not a chain), unlike claim_3_4 / claim_3_17 whose LN
--   statements display a triple equality with a fused RHS. The
--   natural Lean shape is therefore one theorem rather than a
--   fusion-lemma + commute-corollary pair. A reader returning here
--   from the twins might be tempted to "unify" this row with them;
--   this bullet exists so that search ends quickly.
--
-- * **No `W₁ ⊆ G.J ∪ G.V` and no `W₂ ⊆ G.V` preconditions.**
--   Mirrors the no-precondition design of both component
--   operators: `hardInterventionOn` is total on `Set α` by design
--   (`Section3_2/HardInterventionOn.lean` lines 88 -- 215, see
--   payoff #1 "Iteration works unconditionally") and so is
--   `marginalize` (`Section3_2/Marginalization.lean` lines
--   258 -- 286, whose payoff #2 names *this very claim* verbatim:
--   "Composition with `hardInterventionOn` is cleaner
--   (claim_3_18)"). The four-component equality therefore holds
--   for arbitrary `W₁, W₂ : Set α`, regardless of whether
--   `W₁ ⊆ G.J ∪ G.V` or `W₂ ⊆ G.V`. The LN's prose preconditions
--   are informal scaffolding so that `G_{do(W₁)}^{\sm W₂}` reads
--   as "intervene then marginalize inside `G`" in the prose, not
--   load-bearing hypotheses in the LN proof; `verify_equivalence`
--   has confirmed this is a faithful strengthening of the LN
--   statement, not a divergence (the equation is unchanged on the
--   part of `W_i` that actually lies in `G`, and vertices in
--   `W_i \ (G.J ∪ G.V)` are silently ignored by both operators on
--   the way to the equality).
--
-- * **`Disjoint W₁ W₂` is kept as an explicit hypothesis -- it is
--   load-bearing.** The LN's own statement carries disjointness,
--   and the LN proof leans on it in the `E` and `L` analyses
--   (`graphs.tex` lines 1141 -- 1162): an "interior-in-`W₂`"
--   walk's intermediate nodes must lie outside `W₁` for the
--   `hardInterventionOn` edge deletions to be transparent to the
--   `marginalize` walk-existential predicate, which they are
--   precisely under `Disjoint W₁ W₂`; and the endpoint-exclusion
--   clause of `hardInterventionOn` (target `\notin W₁`) only lines
--   up with the shared `V \ (W₁ ∪ W₂)` of the two sides under
--   disjointness. Drop `h` and the RHS marginalizes nodes that the
--   LHS treats as interventional (and vice versa); the equation
--   outright fails. Encoded via Mathlib's `Disjoint` from
--   `Mathlib.Order.Disjoint` (transitively imported via
--   `Section3_2/Marginalization.lean`), so a downstream consumer
--   that wants the swapped form can feed `h.symm` directly --
--   same idiom as `marginalize_comm` of claim_3_17.
--
-- * **Naming `marginalize_hardInterventionOn` (outer / inner
--   convention).** Follows the Mathlib `image_image` / `map_map`
--   / `comap_comap` style for swap-of-two-named-ops lemmas: the
--   lemma name reads *outer* on the LHS first, then *inner*. The
--   LHS `(G.hardInterventionOn W₁).marginalize W₂` has
--   `marginalize` outermost (the last applied operation) and
--   `hardInterventionOn` inside, so the name is
--   `marginalize_hardInterventionOn`. Alternatives considered:
--
--     * `hardInterventionOn_marginalize` -- inverts the outer /
--       inner reading of the LHS; a reader who knows the
--       convention would expect such a lemma to have
--       `(G.marginalize _).hardInterventionOn _` as its LHS,
--       which it does not. Rejected.
--     * `marginalize_hardInterventionOn_comm` -- the Mathlib
--       `_comm` suffix is reserved for `f x y = f y x` shapes of
--       a *single* binary operator (`add_comm`, `mul_comm`,
--       `Set.union_comm`, ...), not for the swap-of-two-different
--       operators expressed here. (The twins' commute corollaries
--       `hardInterventionOn_comm` / `marginalize_comm`
--       legitimately wear `_comm` because each *is* the
--       arguments-swap of a single binary operation on `(G, W)`;
--       not the case here.) Rejected.
--     * `marginalize_hardInterventionOn_fuse` /
--       `..._fusion` -- there is no fusion here (see bullet 1),
--       so a fusion-flavoured name would mislead. Rejected.
--
-- * **`G : CDMG α` explicit, `W₁ W₂ : Set α` implicit (recovered
--   from `h`), `h : Disjoint W₁ W₂` explicit.** Matches the
--   argument-binding pattern of `marginalize_marginalize`
--   (`MarginalizationsCommute.lean` line 904) -- the close twin,
--   since both lemmas carry a load-bearing `Disjoint`
--   hypothesis. `G` is explicit per the project's CDMG
--   convention: the carrier object under study is always spelled
--   at the call site, not inferred via coercion (every other
--   CDMG-quantified lemma in this section does the same).
--   `W₁ W₂` are *implicit* because `h : Disjoint W₁ W₂` already
--   pins them down, so consumers pass only `G` and `h` and the
--   elaborator infers `W₁, W₂` from `h` -- avoids the syntactic
--   awkwardness of spelling `(W₁ W₂ : Set α) (h : Disjoint W₁ W₂)`
--   where the two sets appear three times in the binder list.
--   `h` is explicit because it is load-bearing (see bullet 3) and
--   cannot be inferred from the conclusion. The convention of
--   *which* set we call `W₁` vs `W₂` follows the LN's
--   left-to-right reading of the LHS `(G_{do(W₁)})^{\sm W₂}`:
--   `W₁` is the intervened set, `W₂` is the marginalized one.
--
-- * **The LN's motivation: making `G_{do(W₁)}^{\sm W₂}` an
--   unambiguous notation.** The LN's commented-out remark
--   immediately after the displayed equation (`graphs.tex` lines
--   1126 -- 1127:
--   "% This shows that the following notations are unambiguous:
--    % G(V \ (W₁ ∪ W₂) | \doit(W₁ ∪ J)) = G_{\doit(W₁)}^{\sm W₂}.")
--   is the *reason* this lemma is stated at all: the bare
--   notation `G_{do(W₁)}^{\sm W₂}` (no parentheses indicating
--   which transformation is applied first) is well-defined as a
--   CDMG only because the two orderings yield the same CDMG --
--   which is exactly what this theorem says. The downstream
--   `\refrow{}` chain in `graphs.tex` and the do-calculus / ID-
--   algorithm material of chapters 4 -- 5 (and the FCI / ICDF
--   identification half of chapters 11 -- 16) silently lean on
--   claim_3_18 to give the bare notation a single meaning;
--   downstream Lean code that mirrors the notation reaches for
--   this lemma whenever it needs to commit to a specific order of
--   construction. The header `/-! ... -/` block at the top of the
--   file covers the broader chapter-by-chapter consumer picture;
--   this bullet records only the local "why is this lemma stated
--   at all" point.
--
-- * **The LN's trailing prose ("similar statement holds for ...
--   adding intervention nodes, ... node-splitting interventions")
--   is *not* formalized at this row.** It is a forward-pointer to
--   two analogue commutation lemmas
--   (`marginalize` vs `addInterventionNodes`, `marginalize` vs
--   `nodeSplittingOn`), each of which deserves its own numbered
--   claim under the project's row-per-statement convention. Both
--   analogues are deferred to downstream rows
--   (claim_3_19 / claim_3_20 or follow-ups) and are out of scope
--   here; a future reader pattern-matching on this file should
--   not interpret the absence of those analogues as an incomplete
--   formalization of claim_3_18 itself.
--
-- * **Statement-only at this stage; proof is one `sorry`.** Body
--   is exactly `sorry`. The TeX proof + Lean proof are
--   Manager B's responsibility: the LN's own proof (`graphs.tex`
--   lines 1131 -- 1164) gives the four component-wise checks
--   (`J / V / E / L`); the Lean proof will discharge each via a
--   local `mk_eq_of_data` CDMG-extensionality helper (mirroring
--   the structural twins), plus `Set.diff_diff` for the `V`
--   identity, a `tauto`-after-simp combo for `J`, and walk- /
--   bifurcation-existential `iff`s for `E` and `L`.

end CDMG

/-! ## Private helpers for `marginalize_hardInterventionOn`

The proof translates walks between `G` and `G.hardInterventionOn W₁`.
Since `(G.hardInterventionOn W₁).E ⊆ G.E` and
`(G.hardInterventionOn W₁).L ⊆ G.L`, every walk in the intervention
descends to a walk in `G` (the `dropHard` direction). Conversely, a
walk in `G` whose support entirely avoids `W₁` lifts back to the
intervention (the `liftHard` direction). For the main theorem's `E`
and `L` cases we use both directions: `dropHard` for `LHS → RHS`, and
`liftHard` (with the support condition derived from `Disjoint W₁ W₂`
and endpoint hypotheses) for `RHS → LHS`.

Walk-support helpers like `marg_support_ne_nil` /
`marg_support_eq_dropLast_append_last` are reused directly from
`MarginalizationPreserves.lean` rather than re-derived locally. -/

namespace WalkStep

variable {α : Type*} {G : CDMG α}

/-- Drop the hard-intervention edge-deletion proof from a walk-step.
`(G.hardInterventionOn W).E ⊆ G.E` and the analogue for `L`, so each
step in the intervention descends to a step in `G`. -/
private def dropHard {W : Set α} :
    {v w : α} → WalkStep (G.hardInterventionOn W) v w → WalkStep G v w
  | _, _, .forward h  => .forward h.1
  | _, _, .backward h => .backward h.1
  | _, _, .bidir h    => .bidir h.1

/-- Lift a walk-step in `G` to the hard intervention, given that both
relevant endpoints avoid `W`. The `hv` hypothesis is used for
`.backward` (whose underlying directed edge has the step's source as
target) and `.bidir`; `hw` is used for `.forward` and `.bidir`. The
over-provisioned interface keeps the call site uniform regardless of
which `WalkStep` constructor is present. -/
private def liftHard (W : Set α) {v w : α} :
    (s : WalkStep G v w) → v ∉ W → w ∉ W →
    WalkStep (G.hardInterventionOn W) v w
  | .forward h,  _,  hw => .forward ⟨h, hw⟩
  | .backward h, hv, _  => .backward ⟨h, hv⟩
  | .bidir h,    hv, hw => .bidir ⟨h, fun he => he.elim hv hw⟩

private theorem dropHard_hasArrowheadAtSource_iff {W : Set α} {v w : α}
    (s : WalkStep (G.hardInterventionOn W) v w) :
    s.dropHard.HasArrowheadAtSource ↔ s.HasArrowheadAtSource := by
  cases s <;> simp [dropHard, WalkStep.HasArrowheadAtSource]

private theorem liftHard_hasArrowheadAtSource_iff {W : Set α} {v w : α}
    (s : WalkStep G v w) (hv : v ∉ W) (hw : w ∉ W) :
    (s.liftHard W hv hw).HasArrowheadAtSource ↔ s.HasArrowheadAtSource := by
  cases s <;> simp [liftHard, WalkStep.HasArrowheadAtSource]

/-- `dropHard` is a left-inverse of `liftHard` on `WalkStep`s. -/
private theorem dropHard_liftHard {W : Set α} {v w : α}
    (s : WalkStep G v w) (hv : v ∉ W) (hw : w ∉ W) :
    (s.liftHard W hv hw).dropHard = s := by
  cases s <;> rfl

end WalkStep

namespace Walk

variable {α : Type*} {G : CDMG α}

/-- Local list lemma: `tail.dropLast = dropLast.tail`. Mirrors
`MarginalizationsCommute.lean`'s private `list_tail_dropLast`. -/
private lemma list_tail_dropLast {β : Type*} (l : List β) :
    l.tail.dropLast = l.dropLast.tail := by
  cases l with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest' => rfl

/-- Drop the hard-intervention edge-deletion constraint from a walk:
the resulting walk in `G` has the same shape, support, and length. -/
private def dropHard {W : Set α} :
    {u v : α} → Walk (G.hardInterventionOn W) u v → Walk G u v
  | _, _, .nil u    => .nil u
  | _, _, .cons s p => .cons s.dropHard p.dropHard

@[simp] private theorem dropHard_nil {W : Set α} (u : α) :
    (Walk.nil u : Walk (G.hardInterventionOn W) u u).dropHard = Walk.nil u := rfl

@[simp] private theorem dropHard_cons {W : Set α} {v w u : α}
    (s : WalkStep (G.hardInterventionOn W) v w)
    (p : Walk (G.hardInterventionOn W) w u) :
    (Walk.cons s p).dropHard = Walk.cons s.dropHard p.dropHard := rfl

@[simp] private theorem dropHard_length {W : Set α} {u v : α}
    (π : Walk (G.hardInterventionOn W) u v) :
    π.dropHard.length = π.length := by
  induction π with
  | nil _ => rfl
  | cons _ _ ih => simp [Walk.dropHard_cons, Walk.length_cons, ih]

@[simp] private theorem dropHard_support {W : Set α} {u v : α}
    (π : Walk (G.hardInterventionOn W) u v) :
    π.dropHard.support = π.support := by
  induction π with
  | nil _ => rfl
  | cons _ _ ih => simp [Walk.dropHard_cons, Walk.support_cons, ih]

private theorem dropHard_isDirected_iff {W : Set α} {u v : α}
    (π : Walk (G.hardInterventionOn W) u v) :
    π.dropHard.IsDirected ↔ π.IsDirected := by
  induction π with
  | nil _ => simp
  | @cons _ _ _ s p ih =>
    cases s with
    | forward _ => simp [Walk.dropHard_cons, WalkStep.dropHard, ih]
    | backward _ => simp [Walk.dropHard_cons, WalkStep.dropHard]
    | bidir _ => simp [Walk.dropHard_cons, WalkStep.dropHard]

private theorem dropHard_isAllBackward_iff {W : Set α} {u v : α}
    (π : Walk (G.hardInterventionOn W) u v) :
    π.dropHard.IsAllBackward ↔ π.IsAllBackward := by
  induction π with
  | nil _ => simp
  | @cons _ _ _ s p ih =>
    cases s with
    | forward _ => simp [Walk.dropHard_cons, WalkStep.dropHard]
    | backward _ => simp [Walk.dropHard_cons, WalkStep.dropHard, ih]
    | bidir _ => simp [Walk.dropHard_cons, WalkStep.dropHard]

private theorem dropHard_interiorIn_iff {W W' : Set α} {u v : α}
    (π : Walk (G.hardInterventionOn W) u v) :
    π.dropHard.InteriorIn W' ↔ π.InteriorIn W' := by
  unfold Walk.InteriorIn
  rw [dropHard_support]

private theorem dropHard_append {W : Set α} {u v w : α}
    (p : Walk (G.hardInterventionOn W) u v) (q : Walk (G.hardInterventionOn W) v w) :
    (p.append q).dropHard = p.dropHard.append q.dropHard := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [Walk.cons_append, Walk.dropHard_cons, ih]

/-- Lift a walk in `G` to the hard intervention, given that every
support vertex avoids `W`. Built by structural recursion via `match`;
the per-step obligations are discharged by `WalkStep.liftHard` with
the relevant endpoint hypotheses extracted from `h_supp`. -/
private def liftHard (W : Set α) :
    {a b : α} → (π : Walk G a b) → (∀ x ∈ π.support, x ∉ W) →
    Walk (G.hardInterventionOn W) a b
  | _, _, .nil a, _ => .nil a
  | _, _, .cons step p, h_supp =>
    Walk.cons
      (step.liftHard W
        (h_supp _ (by rw [Walk.support_cons]; exact List.mem_cons_self))
        (h_supp _ (by
          rw [Walk.support_cons]
          refine List.mem_cons_of_mem _ ?_
          cases p with | nil _ => simp | cons _ _ => simp)))
      (liftHard W p (fun x hx => h_supp x (by
        rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx)))

/-- Lift `nil` is `nil`. By definition of `liftHard`. -/
private theorem liftHard_nil {W : Set α} (a : α)
    (h_supp : ∀ x ∈ (Walk.nil a : Walk G a a).support, x ∉ W) :
    liftHard W (Walk.nil a) h_supp = Walk.nil a := rfl

/-- Lift `cons` shape: peels off the head step and recurses. We package
the per-step obligations alongside the equation so callers can both
use the equation and access the extracted endpoint hypotheses. -/
private theorem liftHard_cons {W : Set α} {v w u : α}
    (step : WalkStep G v w) (p : Walk G w u)
    (h_supp : ∀ x ∈ (Walk.cons step p).support, x ∉ W) :
    ∃ (h_v : v ∉ W) (h_w : w ∉ W) (h_p : ∀ x ∈ p.support, x ∉ W),
      liftHard W (Walk.cons step p) h_supp =
        Walk.cons (step.liftHard W h_v h_w) (liftHard W p h_p) := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact h_supp v (by rw [Walk.support_cons]; exact List.mem_cons_self)
  · refine h_supp w (by
      rw [Walk.support_cons]
      refine List.mem_cons_of_mem _ ?_
      cases p with | nil _ => simp | cons _ _ => simp)
  · exact fun x hx => h_supp x (by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx)

@[simp] private theorem liftHard_length {W : Set α} {a b : α}
    (π : Walk G a b) (h_supp : ∀ x ∈ π.support, x ∉ W) :
    (π.liftHard W h_supp).length = π.length := by
  induction π with
  | nil _ => rfl
  | @cons v w u step p ih =>
    obtain ⟨_, _, h_p, hlift_eq⟩ := liftHard_cons step p h_supp
    rw [hlift_eq, Walk.length_cons, Walk.length_cons, ih h_p]

@[simp] private theorem liftHard_support {W : Set α} {a b : α}
    (π : Walk G a b) (h_supp : ∀ x ∈ π.support, x ∉ W) :
    (π.liftHard W h_supp).support = π.support := by
  induction π with
  | nil _ => rfl
  | @cons v w u step p ih =>
    obtain ⟨_, _, h_p, hlift_eq⟩ := liftHard_cons step p h_supp
    rw [hlift_eq, Walk.support_cons, Walk.support_cons, ih h_p]

private theorem liftHard_isDirected_iff {W : Set α} {a b : α}
    (π : Walk G a b) (h_supp : ∀ x ∈ π.support, x ∉ W) :
    (π.liftHard W h_supp).IsDirected ↔ π.IsDirected := by
  induction π with
  | nil _ => rfl
  | @cons v w u step p ih =>
    obtain ⟨_, _, h_p, hlift_eq⟩ := liftHard_cons step p h_supp
    rw [hlift_eq]
    cases step with
    | forward _ => simp [WalkStep.liftHard, ih h_p]
    | backward _ => simp [WalkStep.liftHard]
    | bidir _ => simp [WalkStep.liftHard]

private theorem liftHard_isAllBackward_iff {W : Set α} {a b : α}
    (π : Walk G a b) (h_supp : ∀ x ∈ π.support, x ∉ W) :
    (π.liftHard W h_supp).IsAllBackward ↔ π.IsAllBackward := by
  induction π with
  | nil _ => rfl
  | @cons v w u step p ih =>
    obtain ⟨_, _, h_p, hlift_eq⟩ := liftHard_cons step p h_supp
    rw [hlift_eq]
    cases step with
    | forward _ => simp [WalkStep.liftHard]
    | backward _ => simp [WalkStep.liftHard, ih h_p]
    | bidir _ => simp [WalkStep.liftHard]

private theorem liftHard_interiorIn_iff {W W' : Set α} {a b : α}
    (π : Walk G a b) (h_supp : ∀ x ∈ π.support, x ∉ W) :
    (π.liftHard W h_supp).InteriorIn W' ↔ π.InteriorIn W' := by
  unfold Walk.InteriorIn
  rw [liftHard_support]

/-- `dropHard` is a left-inverse of `liftHard` on `Walk`s. -/
private theorem dropHard_liftHard {W : Set α} {a b : α}
    (π : Walk G a b) (h_supp : ∀ x ∈ π.support, x ∉ W) :
    (π.liftHard W h_supp).dropHard = π := by
  induction π with
  | nil _ => rfl
  | @cons v w u step p ih =>
    obtain ⟨h_v, h_w, h_p, hlift_eq⟩ := liftHard_cons step p h_supp
    rw [hlift_eq, Walk.dropHard_cons, WalkStep.dropHard_liftHard, ih h_p]

/-- Under `Disjoint W₁ W₂`, a walk in `G` with interior in `W₂` and
endpoints outside `W₁` has every support vertex outside `W₁`. The
interior vertices lie in `W₂ ⊆ ∁W₁` by disjointness, and the two
endpoints are explicitly assumed to avoid `W₁`. -/
private lemma forall_supp_notW₁ {W₁ W₂ : Set α} (hd : Disjoint W₁ W₂)
    {u v : α} (σ : Walk G u v) (h_int : σ.InteriorIn W₂)
    (hu : u ∉ W₁) (hv : v ∉ W₁) :
    ∀ x ∈ σ.support, x ∉ W₁ := by
  intro x hx
  -- σ.support = σ.support.dropLast ++ [v] (from MarginalizationPreserves).
  rw [Walk.marg_support_eq_dropLast_append_last σ] at hx
  rcases List.mem_append.mp hx with hx_dl | hx_v
  · -- x ∈ σ.support.dropLast. Use σ.support = u :: σ.support.tail.
    rw [Walk.marg_support_cons_form σ] at hx_dl
    by_cases h_tail_nil : σ.support.tail = []
    · rw [h_tail_nil] at hx_dl; simp at hx_dl
    · rw [List.dropLast_cons_of_ne_nil h_tail_nil] at hx_dl
      rcases List.mem_cons.mp hx_dl with rfl | hx_int
      · exact hu
      · -- hx_int : x ∈ σ.support.tail.dropLast = σ's interior.
        have hx_W₂ : x ∈ W₂ := h_int x hx_int
        exact fun hx_W₁ => Set.disjoint_left.mp hd hx_W₁ hx_W₂
  · simp at hx_v; rw [hx_v]; exact hv

/-- Variant of `forall_supp_notW₁` that doesn't require the source
endpoint `u` to avoid `W₁`. The conclusion is restricted to
`σ.support.tail`, i.e., all vertices except the source. This is the
key tool for the `E`-case directed walk lift, where the RHS only
guarantees `v ∉ W₁`. Interior vertices lie in `W₂ ⊆ ∁W₁` by
disjointness; the final endpoint `v` is the only other support-tail
vertex and is also assumed `∉ W₁`. -/
private lemma forall_supp_tail_notW₁ {W₁ W₂ : Set α} (hd : Disjoint W₁ W₂)
    {u v : α} (σ : Walk G u v) (h_int : σ.InteriorIn W₂) (hv : v ∉ W₁) :
    ∀ x ∈ σ.support.tail, x ∉ W₁ := by
  intro x hx
  -- σ.support = σ.support.dropLast ++ [v] (from MarginalizationPreserves).
  -- σ.support.tail = (σ.support.dropLast ++ [v]).tail.
  -- - If σ.support.dropLast = []: σ.support = [v], σ.support.tail = []. Vacuous.
  -- - Otherwise: σ.support.tail = σ.support.dropLast.tail ++ [v]
  --   = σ.support.tail.dropLast ++ [v] (via `list_tail_dropLast`).
  have h_supp_eq : σ.support = σ.support.dropLast ++ [v] :=
    σ.marg_support_eq_dropLast_append_last
  have h_tail_eq : σ.support.tail = (σ.support.dropLast ++ [v]).tail := by
    conv_lhs => rw [h_supp_eq]
  rw [h_tail_eq] at hx
  by_cases h_dl_nil : σ.support.dropLast = []
  · rw [h_dl_nil] at hx; simp at hx
  · rw [Walk.list_tail_append_of_ne_nil _ h_dl_nil] at hx
    rcases List.mem_append.mp hx with hx_dl_tail | hx_v
    · -- x ∈ σ.support.dropLast.tail = σ.support.tail.dropLast = σ's interior.
      have h_dl_tail_eq : σ.support.dropLast.tail = σ.support.tail.dropLast :=
        (list_tail_dropLast σ.support).symm
      rw [h_dl_tail_eq] at hx_dl_tail
      have hx_W₂ : x ∈ W₂ := h_int x hx_dl_tail
      exact fun hxW1 => Set.disjoint_left.mp hd hxW1 hx_W₂
    · simp at hx_v; rw [hx_v]; exact hv

end Walk

namespace CDMG

variable {α : Type*}

/-- Local CDMG-extensionality helper for this row: two CDMGs are equal
as soon as their four data fields `J / V / E / L` agree. The six prop
fields are proof-irrelevant under Lean 4's definitional rule, so they
close by `rfl` once the data fields are pinned down. Mirrors
`mk_eq_of_data` in `HardInterventionsCommute.lean` and
`MarginalizationsCommute.lean`. -/
private theorem mk_eq_of_data {G H : CDMG α}
    (hJ : G.J = H.J) (hV : G.V = H.V) (hE : G.E = H.E) (hL : G.L = H.L) :
    G = H := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := G
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := H
  subst hJ; subst hV; subst hE; subst hL; rfl

/-- Existence-style directed-walk lift. Given a directed walk `σ` in
`G` whose support-tail (i.e. every target of every forward step)
avoids `W`, there exists a directed walk in `G.hardInterventionOn W`
with the same source, target, support, and length. The source vertex
`a` is allowed to be in `W` -- the intervention's `J` is `G.J ∪ W`,
so vertices in `W` are valid sources. This is the key lift lemma for
the `E`-component iff of the main theorem (where the RHS gives us
`b ∉ W₁` but not `a ∉ W₁`). -/
private lemma exists_directed_lift (G : CDMG α) (W : Set α) :
    ∀ {a b : α} (σ : Walk G a b), σ.IsDirected →
    (∀ x ∈ σ.support.tail, x ∉ W) →
    ∃ π : Walk (G.hardInterventionOn W) a b,
      π.IsDirected ∧ π.support = σ.support ∧ π.length = σ.length := by
  intro a b σ
  induction σ with
  | nil a => intros _ _; exact ⟨Walk.nil a, by simp, by simp, by simp⟩
  | @cons u w v step p ih =>
    intro hdir h_tail
    cases step with
    | forward h =>
      have hp_dir : p.IsDirected := by simpa using hdir
      have hw_notW : w ∉ W := h_tail w (by
        rw [Walk.support_cons, List.tail_cons]
        cases p with | nil _ => simp | cons _ _ => simp)
      have hp_tail : ∀ x ∈ p.support.tail, x ∉ W := fun x hx => h_tail x (by
        rw [Walk.support_cons, List.tail_cons]
        cases p with
        | nil _ => simp at hx
        | @cons _ _ _ _ _ =>
          rw [Walk.support_cons] at hx ⊢
          exact List.mem_cons_of_mem _ hx)
      obtain ⟨π_p, hπ_p_dir, hπ_p_supp, hπ_p_len⟩ := ih hp_dir hp_tail
      refine ⟨Walk.cons (.forward ⟨h, hw_notW⟩) π_p, ?_, ?_, ?_⟩
      · simpa using hπ_p_dir
      · rw [Walk.support_cons, Walk.support_cons, hπ_p_supp]
      · rw [Walk.length_cons, Walk.length_cons, hπ_p_len]
    | backward _ => simp at hdir
    | bidir _ => simp at hdir

/-- claim_3_18: marginalization and hard intervention commute on
disjoint subsets,
`(G.hardInterventionOn W₁).marginalize W₂
   = (G.marginalize W₂).hardInterventionOn W₁`. Mirrors the
displayed equality of the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 1122. Statement only
at this stage; the proof body is `sorry`, to be discharged by the
`prove_claim_in_lean` worker in the proof-phase manager pass
(Manager B). -/
theorem marginalize_hardInterventionOn (G : CDMG α) {W₁ W₂ : Set α}
    (h : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁).marginalize W₂
      = (G.marginalize W₂).hardInterventionOn W₁ := by
  refine mk_eq_of_data ?_ ?_ ?_ ?_
  · -- J case: both sides reduce to `G.J ∪ W₁` by definitional unfolding of
    -- `marginalize_J` (which leaves `J` unchanged) and `hardInterventionOn_J`
    -- (which adds `W₁`).
    rfl
  · -- V case: `(G.V \ W₁) \ W₂ = (G.V \ W₂) \ W₁`, both equal
    -- `G.V \ (W₁ ∪ W₂)` via `Set.diff_diff` and `Set.union_comm`.
    show (G.V \ W₁) \ W₂ = (G.V \ W₂) \ W₁
    rw [Set.diff_diff, Set.diff_diff, Set.union_comm]
  · -- E case: walk-existential `iff`. Forward direction via `dropHard`;
    -- backward via `exists_directed_lift` (target-only support condition).
    ext p
    show p ∈ ((G.hardInterventionOn W₁).marginalize W₂).E ↔
         p ∈ ((G.marginalize W₂).hardInterventionOn W₁).E
    rw [CDMG.mem_marginalize_E, CDMG.mem_hardInterventionOn_E,
        CDMG.mem_marginalize_E,
        CDMG.hardInterventionOn_J, CDMG.hardInterventionOn_V]
    constructor
    · -- LHS → RHS
      rintro ⟨h_p1, h_p2, π, hπ_dir, hπ_int, hπ_len⟩
      have hp2_V_W2 : p.2 ∈ G.V \ W₂ := ⟨h_p2.1.1, h_p2.2⟩
      have hp2_nW1 : p.2 ∉ W₁ := h_p2.1.2
      have hp1_RHS : p.1 ∈ G.J ∪ (G.V \ W₂) := by
        rcases h_p1 with (hJ | hW₁) | hV_W
        · exact Or.inl hJ
        · -- p.1 ∈ W₁. The walk's source must be in G.J ∪ G.V (since 1 ≤ length).
          -- Drop the hard-intervention constraint to apply the standard
          -- "start of a length-≥-1 directed walk is in G.J ∪ G.V" lemma.
          have hdH_dir : π.dropHard.IsDirected :=
            (Walk.dropHard_isDirected_iff π).mpr hπ_dir
          have hdH_len : 1 ≤ π.dropHard.length := by
            rw [Walk.dropHard_length]; exact hπ_len
          have h_pred : p.1 ∈ G.J ∪ G.V :=
            Walk.marg_start_in_JV_of_isDirected_pos π.dropHard hdH_dir hdH_len
          rcases h_pred with hJ | hV
          · exact Or.inl hJ
          · -- p.1 ∈ G.V ∩ W₁. By disjointness, p.1 ∉ W₂. So p.1 ∈ G.V \ W₂.
            have hp1_nW2 : p.1 ∉ W₂ := fun hW2 =>
              Set.disjoint_left.mp h hW₁ hW2
            exact Or.inr ⟨hV, hp1_nW2⟩
        · exact Or.inr ⟨hV_W.1.1, hV_W.2⟩
      refine ⟨⟨hp1_RHS, hp2_V_W2, π.dropHard, ?_, ?_, ?_⟩, hp2_nW1⟩
      · exact (Walk.dropHard_isDirected_iff π).mpr hπ_dir
      · exact (Walk.dropHard_interiorIn_iff π).mpr hπ_int
      · rw [Walk.dropHard_length]; exact hπ_len
    · -- RHS → LHS
      rintro ⟨⟨h_p1, h_p2, σ, hσ_dir, hσ_int, hσ_len⟩, hp2_nW1⟩
      have hp2_V : p.2 ∈ G.V := h_p2.1
      have hp2_nW2 : p.2 ∉ W₂ := h_p2.2
      have hp1_LHS : p.1 ∈ G.J ∪ W₁ ∪ ((G.V \ W₁) \ W₂) := by
        rcases h_p1 with hJ | hV_W2
        · exact Or.inl (Or.inl hJ)
        · by_cases h_W1 : p.1 ∈ W₁
          · exact Or.inl (Or.inr h_W1)
          · exact Or.inr ⟨⟨hV_W2.1, h_W1⟩, hV_W2.2⟩
      have hp2_LHS : p.2 ∈ (G.V \ W₁) \ W₂ := ⟨⟨hp2_V, hp2_nW1⟩, hp2_nW2⟩
      refine ⟨hp1_LHS, hp2_LHS, ?_⟩
      -- Derive the tail-only support condition on σ via the helper.
      have h_tail := Walk.forall_supp_tail_notW₁ h σ hσ_int hp2_nW1
      obtain ⟨π, hπ_dir, hπ_supp, hπ_len⟩ := exists_directed_lift G W₁ σ hσ_dir h_tail
      refine ⟨π, hπ_dir, ?_, ?_⟩
      · -- π.InteriorIn W₂ ↔ σ.InteriorIn W₂ via π.support = σ.support.
        intro x hx
        apply hσ_int
        rwa [hπ_supp] at hx
      · rw [hπ_len]; exact hσ_len
  · -- L case: bifurcation / no-directed-walk existential iffs. Both
    -- endpoints are guaranteed ∉ W₁ (from `(G.V \ W₁) \ W₂` membership),
    -- so the lift uses `liftHard` with the full-support condition derived
    -- from `forall_supp_notW₁`. The bifurcation witness is transported
    -- explicitly: each `BifurcationWitness` field (sub-walks and hinge)
    -- is mapped through `dropHard` / `liftHard`, with `decompose` closing
    -- by `dropHard_append` / `dropHard_cons` (forward direction) or by
    -- `rfl` for the construction of `π` (backward direction).
    ext p
    show p ∈ ((G.hardInterventionOn W₁).marginalize W₂).L ↔
         p ∈ ((G.marginalize W₂).hardInterventionOn W₁).L
    rw [CDMG.mem_marginalize_L, CDMG.mem_hardInterventionOn_L,
        CDMG.mem_marginalize_L, CDMG.hardInterventionOn_V]
    -- Helper: directed-walk-existential iff (under both endpoints ∉ W₁).
    have h_dwalk_iff : ∀ {a b : α}, a ∉ W₁ → b ∉ W₁ →
        ((∃ π : Walk (G.hardInterventionOn W₁) a b,
            π.IsDirected ∧ π.InteriorIn W₂) ↔
         (∃ σ : Walk G a b, σ.IsDirected ∧ σ.InteriorIn W₂)) := by
      intro a b ha hb
      constructor
      · rintro ⟨π, hdir, hint⟩
        exact ⟨π.dropHard, (Walk.dropHard_isDirected_iff π).mpr hdir,
          (Walk.dropHard_interiorIn_iff π).mpr hint⟩
      · rintro ⟨σ, hdir, hint⟩
        have h_supp := Walk.forall_supp_notW₁ h σ hint ha hb
        refine ⟨σ.liftHard W₁ h_supp, ?_, ?_⟩
        · exact (Walk.liftHard_isDirected_iff σ h_supp).mpr hdir
        · exact (Walk.liftHard_interiorIn_iff σ h_supp).mpr hint
    -- Helper: bifurcation-existential iff (under both endpoints ∉ W₁).
    have h_bif_iff : ∀ {a b : α}, a ∉ W₁ → b ∉ W₁ →
        ((∃ π : Walk (G.hardInterventionOn W₁) a b,
            π.IsBifurcation ∧ π.InteriorIn W₂) ↔
         (∃ σ : Walk G a b, σ.IsBifurcation ∧ σ.InteriorIn W₂)) := by
      intro a b ha hb
      constructor
      · -- intervention → G via dropHard
        rintro ⟨π, hπ_bif, hπ_int⟩
        refine ⟨π.dropHard, ?_, (Walk.dropHard_interiorIn_iff π).mpr hπ_int⟩
        obtain ⟨hne, hu_sp, hv_sp, ⟨bw⟩⟩ := hπ_bif
        refine ⟨hne, ?_, ?_, ⟨{
          m := bw.m
          m' := bw.m'
          leftArm := bw.leftArm.dropHard
          hinge := bw.hinge.dropHard
          rightArm := bw.rightArm.dropHard
          decompose := by
            conv_lhs => rw [bw.decompose]
            rw [Walk.dropHard_append, Walk.dropHard_cons]
          leftBackward :=
            (Walk.dropHard_isAllBackward_iff bw.leftArm).mpr bw.leftBackward
          hingeIntoSource :=
            (WalkStep.dropHard_hasArrowheadAtSource_iff bw.hinge).mpr
              bw.hingeIntoSource
          rightDirected :=
            (Walk.dropHard_isDirected_iff bw.rightArm).mpr bw.rightDirected
        }⟩⟩
        · rw [Walk.dropHard_support]; exact hu_sp
        · rw [Walk.dropHard_support]; exact hv_sp
      · -- G → intervention via liftHard
        rintro ⟨σ, hσ_bif, hσ_int⟩
        obtain ⟨hne, hu_sp_σ, hv_sp_σ, ⟨bw'⟩⟩ := hσ_bif
        -- Support of σ avoids W₁.
        have h_supp := Walk.forall_supp_notW₁ h σ hσ_int ha hb
        -- Support of each sub-walk of bw' avoids W₁ (subset of σ.support);
        -- we use the prefab inclusion lemmas from `MarginalizationPreserves`.
        have h_left_supp : ∀ x ∈ bw'.leftArm.support, x ∉ W₁ := fun x hx =>
          h_supp x (List.dropLast_subset _
            (Walk.bw_leftArm_in_π_dropLast bw' x hx))
        have h_right_supp : ∀ x ∈ bw'.rightArm.support, x ∉ W₁ := fun x hx =>
          h_supp x (List.mem_of_mem_tail (Walk.bw_rightArm_in_π_tail bw' x hx))
        have h_m_notW : bw'.m ∉ W₁ :=
          h_supp bw'.m (List.dropLast_subset _ (Walk.bw_m_in_π_dropLast bw'))
        have h_m'_notW : bw'.m' ∉ W₁ := by
          have h_m'_in_rA : bw'.m' ∈ bw'.rightArm.support := by
            rw [Walk.marg_support_cons_form bw'.rightArm]
            exact List.mem_cons_self
          exact h_supp bw'.m' (List.mem_of_mem_tail
            (Walk.bw_rightArm_in_π_tail bw' bw'.m' h_m'_in_rA))
        -- Construct the lifted bifurcation walk.
        set leftArmLift := bw'.leftArm.liftHard W₁ h_left_supp with hleftArmLift
        set hingeLift := bw'.hinge.liftHard W₁ h_m_notW h_m'_notW with hhingeLift
        set rightArmLift := bw'.rightArm.liftHard W₁ h_right_supp with hrightArmLift
        set π := leftArmLift.append (Walk.cons hingeLift rightArmLift) with hπdef
        -- π.support = σ.support via π.dropHard = σ and dropHard_support.
        -- The dropHard direction is straightforward; lift-then-drop is the
        -- identity (`dropHard_liftHard`), and that identity, together with
        -- `bw'.decompose`, gives us `π.dropHard = σ`.
        have h_π_dropHard_eq_σ : π.dropHard = σ := by
          show (leftArmLift.append (Walk.cons hingeLift rightArmLift)).dropHard = σ
          rw [Walk.dropHard_append, Walk.dropHard_cons]
          rw [Walk.dropHard_liftHard bw'.leftArm h_left_supp,
              WalkStep.dropHard_liftHard bw'.hinge h_m_notW h_m'_notW,
              Walk.dropHard_liftHard bw'.rightArm h_right_supp]
          exact bw'.decompose.symm
        have hπ_supp_eq : π.support = σ.support := by
          rw [← Walk.dropHard_support π, h_π_dropHard_eq_σ]
        refine ⟨π, ?_, ?_⟩
        · -- π.IsBifurcation
          refine ⟨hne, ?_, ?_, ⟨{
            m := bw'.m
            m' := bw'.m'
            leftArm := leftArmLift
            hinge := hingeLift
            rightArm := rightArmLift
            decompose := rfl
            leftBackward :=
              (Walk.liftHard_isAllBackward_iff bw'.leftArm h_left_supp).mpr
                bw'.leftBackward
            hingeIntoSource :=
              (WalkStep.liftHard_hasArrowheadAtSource_iff bw'.hinge
                h_m_notW h_m'_notW).mpr bw'.hingeIntoSource
            rightDirected :=
              (Walk.liftHard_isDirected_iff bw'.rightArm h_right_supp).mpr
                bw'.rightDirected
          }⟩⟩
          · -- a ∉ π.support.tail
            have : π.support.tail = σ.support.tail := by rw [hπ_supp_eq]
            rw [this]; exact hu_sp_σ
          · -- b ∉ π.support.dropLast
            have : π.support.dropLast = σ.support.dropLast := by rw [hπ_supp_eq]
            rw [this]; exact hv_sp_σ
        · -- π.InteriorIn W₂
          intro x hx
          have h_int_eq : π.support.tail.dropLast = σ.support.tail.dropLast := by
            rw [hπ_supp_eq]
          rw [h_int_eq] at hx
          exact hσ_int x hx
    -- Now prove the L-component iff.
    constructor
    · -- LHS → RHS
      rintro ⟨h_p1, h_p2, h_ne, h_nd12, h_nd21, h_bif⟩
      have hp1_V : p.1 ∈ G.V := h_p1.1.1
      have hp1_nW1 : p.1 ∉ W₁ := h_p1.1.2
      have hp1_nW2 : p.1 ∉ W₂ := h_p1.2
      have hp2_V : p.2 ∈ G.V := h_p2.1.1
      have hp2_nW1 : p.2 ∉ W₁ := h_p2.1.2
      have hp2_nW2 : p.2 ∉ W₂ := h_p2.2
      refine ⟨⟨⟨hp1_V, hp1_nW2⟩, ⟨hp2_V, hp2_nW2⟩, h_ne, ?_, ?_, ?_⟩,
        hp1_nW1, hp2_nW1⟩
      · -- ¬ ∃ σ : Walk G p.1 p.2, σ.IsDirected ∧ σ.InteriorIn W₂
        intro hex
        exact h_nd12 ((h_dwalk_iff hp1_nW1 hp2_nW1).mpr hex)
      · intro hex
        exact h_nd21 ((h_dwalk_iff hp2_nW1 hp1_nW1).mpr hex)
      · rcases h_bif with hbif | hbif
        · exact Or.inl ((h_bif_iff hp1_nW1 hp2_nW1).mp hbif)
        · exact Or.inr ((h_bif_iff hp2_nW1 hp1_nW1).mp hbif)
    · -- RHS → LHS
      rintro ⟨⟨h_p1, h_p2, h_ne, h_nd12, h_nd21, h_bif⟩, hp1_nW1, hp2_nW1⟩
      have hp1_V : p.1 ∈ G.V := h_p1.1
      have hp1_nW2 : p.1 ∉ W₂ := h_p1.2
      have hp2_V : p.2 ∈ G.V := h_p2.1
      have hp2_nW2 : p.2 ∉ W₂ := h_p2.2
      refine ⟨⟨⟨hp1_V, hp1_nW1⟩, hp1_nW2⟩,
        ⟨⟨hp2_V, hp2_nW1⟩, hp2_nW2⟩, h_ne, ?_, ?_, ?_⟩
      · intro hex
        exact h_nd12 ((h_dwalk_iff hp1_nW1 hp2_nW1).mp hex)
      · intro hex
        exact h_nd21 ((h_dwalk_iff hp2_nW1 hp1_nW1).mp hex)
      · rcases h_bif with hbif | hbif
        · exact Or.inl ((h_bif_iff hp1_nW1 hp2_nW1).mpr hbif)
        · exact Or.inr ((h_bif_iff hp2_nW1 hp1_nW1).mpr hbif)

end CDMG

end Causality
