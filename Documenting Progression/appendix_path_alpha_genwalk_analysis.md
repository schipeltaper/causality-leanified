# Appendix — Path α (GenWalk parameterisation) cost analysis

**Source:** `plan_subtasks` worker, 2026-05-31T17:30 UTC, written to
`leanification/Chapter3_GraphTheory/Section3_2/workspace_def_3_14.md`
lines 974-1344 during the discarded `refactor_def_3_14_no_L_exclusion`
attempt.

**Status:** Path α was *not* adopted. This appendix preserves the
worker's concrete cost estimate (the most thorough we have on
record) in case Cluster A is ever revisited with the
`def_3_1_no_disjoint_EL` refactor deferred.

The worker also surfaced **Path δ** — a cheap stopgap that ships
the (⇒) direction of `claim_3_25` positively while retaining the
(⇐) disproof, at ~50-100 lines. That option is recorded in
`refactor_roadmap.md` Cluster A; this appendix is the Path α
deep-dive.

---

## Question on the table

The prior plan estimated Path α (E5 WalkAug augmentation) at ~2200
lines, mostly due to duplicating `CollidersAndNon` /
`BlockableAndUnblockable` / `SigmaBlockedWalks` for the new walk
type. **Can the duplication be substantially avoided, bringing the
cost below ~1000 lines** — so the manager could commit without
re-escalating?

The audit (below) concludes: **no**. The infrastructure can be
parameterised (~410 lines via `GenWalk`), but the *proof itself*
dominates the total cost at ~3500 lines and would still need to be
written either way.

---

## Adjacent-LN-lemma search: no shortcut found

Scanned `graphs.tex:1100-1600`. Adjacent lemmas:

- **claim_3_22** (σ-sep symmetry under `J = ∅`): does not
  reformulate claim_3_25; orthogonal.
- **claim_3_23 / 3_24** (σ-open walk ↔ σ-open path ↔ σ-open
  walk with all colliders in C): rewrites the *universal over
  walks* into a *universal over paths*, but paths in
  `G.marginalize D` still use the *same step constructors* as
  walks. The cascade obstruction is at the
  `bidir h : (w, b_{j+1}) ∈ G_marg.L` *step-type-existence*
  level. Switching to paths does not help — paths use the
  same step types.
- **claim_3_26 / 3_27** (acyclic simplification; walk
  replacement): require acyclicity (`G` is a CADMG), not the
  general case.

**No adjacent LN lemma sidesteps the requirement to materialise
a `bidir` step at the collision pair `(w, b_{j+1})` in
`G.marginalize {u}`.** Path α (or equivalent encoding work)
remains the only in-scope route.

---

## Audit of the existing predicate files: proof-opacity confirmed

File sizes via `wc -l`:

| File | Lines |
|---|---:|
| `CollidersAndNon.lean` (def_3_15) | 352 |
| `BlockableAndUnblockable.lean` (def_3_16) | 569 |
| `SigmaBlockedWalks.lean` (def_3_17) | 616 |
| `ISigmaSeparation.lean` (def_3_18) | 815 |
| `ISigmaSeparationMarginalization.lean` (disproof) | 1513 |
| `SigmaOpenWalkMarginalization.lean` ((⇒)-proof) | 2246 |

The eight position-indexed predicates and four per-step
classifiers in these files are **proof-opaque**:

- They pattern-match on `WalkStep G v w`'s three constructors
  (`forward h`, `backward h`, `bidir h`) but **never destructure
  the proof `h : (v,w) ∈ G.E` or `h : (v,w) ∈ G.L`**. The proofs
  are opaque payloads.
- The per-step classifier predicates (`HasArrowheadAtTarget`,
  `HasArrowheadAtSource`, `IsForward`, `IsBackward`, `IsBidir`)
  are pure constructor matches, ~3 lines each.
- The position-indexed predicates (`IsColliderAt`,
  `IsUnblockableNonColliderAt`, `IsBlockableNonColliderAt`,
  `nodeAt`, `IsSigmaOpen`, `IsSigmaBlocked`) recurse
  structurally on `Walk G`'s `nil`/`cons` constructors plus
  the position index `k : ℕ`, calling per-step classifiers
  on the step head.
- The only out-of-step CDMG access is `G.Sc` / `G.AncSet` (in
  `IsUnblockableJoint` and `IsSigmaOpen`/`IsSigmaBlocked`); both
  go through `Anc` / `Desc` / `FamilyReachability`, which take
  the CDMG `G` as a parameter without inspecting `E` / `L`
  directly.

**This proof-opacity is the structural prerequisite for the
GenWalk approach.** A `GenWalkStep` parameterised over arbitrary
edge predicates supports the same per-step classifier API, and a
`GenWalk` over an arbitrary step type supports the same
position-indexed predicate recursion.

---

## GenWalk parameterisation — code sketch

```lean
-- In a new file Section3_3/GenericWalks.lean (in scope; no
-- existing out-of-scope file is modified).

namespace Causality.GenWalk
variable {α : Type*}

inductive GenWalkStep (P_dir : α → α → Prop) (P_bidir : α → α → Prop)
    : α → α → Type _ where
  | forward {v w : α} (h : P_dir v w) : GenWalkStep P_dir P_bidir v w
  | backward {v w : α} (h : P_dir w v) : GenWalkStep P_dir P_bidir v w
  | bidir {v w : α} (h : P_bidir v w) : GenWalkStep P_dir P_bidir v w

-- Per-step classifiers (identical bodies to existing predicates;
-- ~5 defs × 3 cases + ~15 simp lemmas = ~60 lines).
def GenWalkStep.HasArrowheadAtTarget : GenWalkStep P_dir P_bidir v w → Prop
  | .forward _ => True | .backward _ => False | .bidir _ => True
-- ... HasArrowheadAtSource, IsForward, IsBackward, IsBidir similarly

inductive GenWalk (S : α → α → Type _) : α → α → Type _ where
  | nil (v : α) : GenWalk S v v
  | cons {v w u : α} (s : S v w) (p : GenWalk S w u) : GenWalk S v u

-- length, support, append, reverse: ~40 lines (mechanical
-- transliteration of Walk's existing definitions).

-- Position-indexed predicates: identical-shape recursion as
-- existing Walk predicates, but over `GenWalk (GenWalkStep ...)`.
-- ~200 lines (defs + simp lemmas) for IsColliderAt, IsNonColliderAt,
-- IsUnblockableJoint, IsUnblockableNonColliderAt,
-- IsBlockableNonColliderAt, nodeAt, IsSigmaOpen, IsSigmaBlocked,
-- isSigmaBlocked_iff_not_isSigmaOpen.

end Causality.GenWalk

-- Specializations:
abbrev WalkStepAug (G : CDMG α) (shadow : Set (α × α)) :=
  GenWalkStep (fun v w => (v, w) ∈ G.E)
              (fun v w => (v, w) ∈ G.L ∨ (v, w) ∈ shadow)

abbrev WalkAug (G : CDMG α) (shadow : Set (α × α)) :=
  GenWalk (WalkStepAug G shadow)

-- shadow_L helper (~20 lines):
def CDMG.shadow_L (G : CDMG α) (W : Set α) : Set (α × α) :=
  { p | p.1 ∈ G.V \ W ∧ p.2 ∈ G.V \ W ∧ p.1 ≠ p.2 ∧
        ((∃ π : Walk G p.1 p.2, π.IsBifurcation ∧ π.InteriorIn W) ∨
         (∃ π : Walk G p.2 p.1, π.IsBifurcation ∧ π.InteriorIn W)) }

-- Augmented σ-separation (~10 lines):
def CDMG.IsISigmaSeparatedAug (G : CDMG α) (shadow : Set (α × α))
    (A B C : Set α) : Prop :=
  ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B →
    ∀ (π : WalkAug G shadow v w), GenWalk.IsSigmaBlocked π C

-- Bridge: Walk G ≃ GenWalk (GenWalkStep ...) (used to translate
-- existing claim_3_25 (⇒) lifts to the GenWalk world).
-- ~80 lines for the iso + predicate-iff lemmas (all `rfl` after
-- definitional unfold).
```

**Approach GenWalk infrastructure subtotal: ~410 lines.** This is
the firm savings vs. the ~1800-line "full duplication" baseline:
**~1400 lines saved.**

---

## Limit: the existing 2246-line (⇒) proof's reuse

**The dominant cost is the claim_3_25 proof itself.** The existing
`lift_sigmaOpen_walk_through_single_vertex` in
`SigmaOpenWalkMarginalization.lean` proves the (⇒) direction
**only** under priority-E, **for the standard
`Walk (G.marginalize {u})` type, no augmentation**. **It is 2246
lines, fully discharged (no `sorry`).** The `lift_aux_strong`
private induction at lines 780-2018 is the structural core (~1200
lines); the surrounding helpers (`bidir_step_to_walk_in_G_arrows`,
`u_in_Sc_via_directed_lift`, support lemmas) make up the rest.
The strengthened-IH conjunct list (`lift_aux_strong`'s five
conjuncts, including the boundary-arrowhead iff and the
`IsForward → Anc` clause) is necessitated by the σ-open boundary
verification in the cons-case — exactly the kind of book-keeping
that would have to be redone on a different walk type.

For Path α we need:

- **(⇒) direction augmented**: same lift, but now over `WalkAug`.
  Each step type now has 4 cases (forward/backward in
  `G_marg.E`, bidir in `G_marg.L`, bidir in `shadow_L`), not 3.
  The existing proof handles 3 of the 4 cases on `Walk`; we must
  either (i) port the existing proof to `WalkAug` literally
  (~2300 lines, including the new `shadow_L` case), or (ii) build
  a "wrapper" that decomposes a `WalkAug` into a series of base
  `Walk`-steps interspersed with `shadow_L` events and applies
  the existing lift segment-by-segment (~500-700 lines).

  Approach (ii) is feasible but requires careful book-keeping on
  σ-open conditions across segment boundaries. Realistic
  estimate: **~600-800 lines** for (⇒)-augmented, reusing the
  existing 2246 lines for the base cases.

- **(⇐) direction augmented**: this is the missing positive
  proof. The LN's (⇐) (`graphs.tex:1493-1577`) contracts each
  `u`-run in a G-walk into a single edge of
  `WalkAug (G.marginalize {u}) (shadow_L)`, with the LN's
  substitution argument at `graphs.tex:1546-1577` constructing
  the `b_j ⇁ w ↼ b_{j+1}` reroute via the `shadow_L` bidir step.

  This is mathematically dual to the (⇒) lift, with comparable
  combinatorial complexity. The strengthened-IH pattern from the
  existing (⇒) proof is reusable as a design template. Realistic
  estimate: **~2000-2500 lines** for (⇐)-augmented, by analogy to
  the existing (⇒)'s ~2246 lines.

---

## Other approaches rejected

**(b) Sum-type coercion to a CDMG without `disjoint_EL`.** Relabel
the augmented graph's vertices via `α ⊕ Tag` so that `shadow_L`
pairs sit in a distinct ambient type and `disjoint_EL` is vacuous.
**Two blockers:** (1) we'd still need a parallel `Walk` type over
the relabeled ambient — modifying `Walks.lean` is out of scope,
and the relabeling forces a different `WalkStep` shape that the
existing predicates don't accept. (2) the relabeling layer adds
its own ~200-300 lines of plumbing (relabel-and-unrelabel
coercions, support-list relabeling lemmas, etc.) and translates
the problem without simplifying. **No net savings vs. GenWalk.**

**(c) Direct structural induction without
`CollidersAndNon`/`BlockableAndUnblockable`/`SigmaBlockedWalks`.**
The LN proof's σ-open conditions at each walk position are *defined*
by `IsColliderAt`, `IsBlockableNonColliderAt`, `AncSet(C)` membership,
etc. To avoid the predicate infrastructure we'd have to re-derive
these conditions inline at every walk position in the proof. **This
makes the proof longer, not shorter** — the predicate API exists
precisely to avoid this kind of unrolling.

**(d) Other tricks.**
- *Restricting claim_3_25 to acyclic CDMGs* (where claim_3_26
  collapses iσ-sep to id-sep). Would shrink the proof
  substantially, but the lemma is then **strictly weaker than the
  LN's claim_3_25** — the LN explicitly handles non-acyclic
  CDMGs (the cyclic case is part of why it uses iσ-sep at all).
  Major deviation in claim statement.
- *Proving only the (⇒) direction*, leaving (⇐) as the existing
  disproof — this is **Path δ** below.

---

## Realistic Path α cost

| Component | Lines |
|---|---:|
| GenWalk infrastructure (types + per-step + per-position predicates + bridges to Walk) | ~410 |
| `shadow_L` helper + `WalkAug` abbreviations + `IsISigmaSeparatedAug` | ~50 |
| (⇒) augmented (wrapper around existing 2246-line proof) | ~700 |
| (⇐) augmented (new positive proof, analogous to existing (⇒)) | ~2200 |
| Auxiliary lemmas (claim_3_16 item 2 over WalkAug, etc.) | ~150 |
| **Total NEW Lean code for Path α** | **~3500** |

The original ~2200 estimate was optimistic by ~60% — it
under-counted the proof itself. The reduction techniques save
substantial lines on the infrastructure side (~1500-2000 lines
saved via GenWalk parameterisation), but the inherent
combinatorial complexity of the LN's claim_3_25 proof remains
around ~3000 lines of Lean regardless.

---

## Path δ — ship only the (⇒) direction positively

A path the prior plans had not separately surfaced: **state
claim_3_25 as a one-sided implication only** (the safe (⇒)
direction), and keep the disproof for (⇐).

```lean
theorem isISigmaSeparated_marginalize_forward
    (G : CDMG α) (A B C : Set α) {D : Set α} (hDV : D ⊆ G.V)
    (hDisj : Disjoint D (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C →
      (G.marginalize D).IsISigmaSeparated A B C := by
  -- Reduce to D = {u} via induction on |D| through
  -- marginalisations-commute (claim_3_17), then dispatch to the
  -- existing `lift_sigmaOpen_walk_through_single_vertex` (which
  -- proves the contrapositive of this implication, single-vertex
  -- case).
  sorry  -- ~50-100 lines, reusing existing artefacts
```

Plus retain the existing
`isISigmaSeparated_marginalize_iff_disproved` (rename:
`isISigmaSeparated_marginalize_backward_disproved`) to record that
the (⇐) direction fails. The full LN iff stays unprovable in scope.

**Path δ cost: ~50-100 lines.**

**Deviations under Path δ:**
1. (Retained) `def_3_14_marginalize_L_excludes_E`
2. (Retained) `def_3_14_l_w_membership_in_marginalization`
3. (Retained) `claim_3_16_with_source_bifurcation_deferred`
4. (CHANGED) `claim_3_25_*`: from "full iff disproved" to
   "(⇒) proven positively, (⇐) disproved". Strict improvement
   over current disproof — one direction is now usable.

**Path δ's downside vs. Path α:** the (⇐) direction is the
load-bearing direction for downstream do-calculus rule 3 use
(`if A iσ-sep B given C on G^{∖Z}, then we may delete the do(Z)
...`). The (⇒) direction alone doesn't unlock that downstream
consumer.

---

## Final ranking (worker's recommendation)

1. **Path β** (`def_3_1_no_disjoint_EL` refactor) — still the
   cleanest and lowest *new-Lean-code* total. New refactor
   surfaces a ~15-25 row table; chapter-3 transitive
   re-validation. Estimated total: ~3000 lines (mostly the
   claim_3_25 (⇐) positive proof, plus the field-discharge
   removals and mechanical updates). **No deviations remain.**

2. **Path δ** — ship the (⇒) direction only, keep the (⇐)
   disproof. **~50-100 lines, contained in this refactor.**
   Smallest in-scope progress. Trades downstream do-calculus
   rule 3 ergonomics for immediate forward progress. Could be a
   "stopgap until Path β happens".

3. **Path α** (E5 WalkAug augmentation) — in-scope but ~3500
   lines, increases deviation count by ~3, retains all current
   marginalize deviations. Net cost-benefit is noticeably worse
   than the prior plans estimated.

4. **Path γ** — accept the four deviations, no-op the refactor.

Path β remains the structural fix; this appendix documents that
Path α is *possible* under GenWalk parameterisation, but at a
cost (~3500 LoC + ~3 new deviations) that does not justify it
over Path β (~3000 LoC + zero deviations) or even Path δ
(~50-100 LoC + partial credit).
