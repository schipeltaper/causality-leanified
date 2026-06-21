# Refactor plan: collider_side_aware

**Status:** proposed (not yet executed)
**Date:** 2026-06-20
**Root ref:** def_3_15 (CollidersAndNon)
**Root chapter:** 3
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_collider_side_aware

## Why this refactor is needed

The current formalisation of `def_3_15` (`IsCollider` on a CDMG walk) tests "arrowhead at the middle vertex `v_k`" via the helper `WalkStep.IsInto vk`, applied at *both* the left walk-step (`s₀ : WalkStep G u v_k`, ending at `v_k`) and the right walk-step (`s₁ : WalkStep G v_k w`, starting at `v_k`). For non-self-loop walk-steps this is correct — the left step's *target* `v` equals `v_k` and the right step's *source* `u` equals `v_k`, so the test `IsInto vk` reads "is `v_k` the head end of this step?" on each side cleanly.

For a directed self-loop step `s : WalkStep G b b` (constructed as `.forwardE h` with `h : (b, b) ∈ G.E`), the test collapses. `WalkStep.IsInto`'s `.forwardE` branch at `Section3_3/CollidersAndNon.lean:339` reads:

```lean
| u, v, .forwardE _, w => w = v ∨ (s(u, v) ∈ G.L ∧ (w = u ∨ w = v))
```

with `u = v = b`. The first disjunct `w = v` fires for `w = b` regardless of whether the test is being applied *from the source side* of the step (we want `False` — a forward edge has tail at source) or *from the target side* (we want `True`). The `IsInto` API exposes only one vertex `w` to compare against `u` and `v`; for a self-loop `u = v`, no information about *which side* the caller cares about can survive that interface.

Consequence: `IsCollider` flags every position-1 walk of shape

```
a --(.forwardE)--> b --(.forwardE)--> b
```

as a collider at `b`, where the right step is a directed self-loop. Mathematically `b` is *not* a collider on this walk — the right step's *source* end (the side the test is asking about) is the tail of the self-loop, not the head. The current encoding sees `s₀.IsInto b = True` (correctly, the left step's target is `b`) AND `s₁.IsInto b = True` (incorrectly — the self-loop's `u = v = b` collapses both disjuncts to `True`), and concludes "collider".

The `s(u, v) ∈ G.L` L-disjunct does NOT contribute to this bug: `def_3_1`'s `hL_irrefl` axiom (no `s(v, v) ∈ G.L` — bidirected self-edges are forbidden by construction) means the L-clause's premise is identically `False` on self-loop steps. The bug is purely in the first disjunct, which doesn't pin which side of the step the test is being applied from.

### Downstream consequence: a spurious `claim_3_27` disproof

The §3.3 solver run dated 2026-06-20 produced a `mistake → disproven` outcome on `claim_3_27` (`LabelRoman`). The disproof's Lean witness — `Section3_3/LabelRomanDisproof.lean:37` — explicitly cites the `WalkStep.IsInto` self-loop firing as the load-bearing step in its counterexample. With the encoding fixed (so that self-loops don't induce spurious colliders), the disproof's counterexample no longer constructs the alleged separation/non-separation discrepancy, and the prove-side of `claim_3_27` is expected to close. The disproof artefact will be retracted at refactor finalize-time alongside the encoding fix.

`claim_3_22` (`SigmaSeparationSymmetric`, just solved as `proven` under the buggy encoding) is at risk: the buggy `IsCollider` may have admitted certain walks as colliders that distort the σ-blocking semantics, possibly closing the symmetry theorem on a degenerate case set. The refactor row should re-port `claim_3_22`'s proof against the fixed encoding and re-verify; if the existing proof still closes, fine, otherwise the row is reopened on the refactor branch and solved against the corrected predicate.

Three §3.3 claims that have not been attempted (`claim_3_23` `SigmaOpenPathsWalks`, `claim_3_24` `SigmaSeparationEquivalences`, `claim_3_25` `ISigmaSeparation`) sit on top of the same σ-blocking infrastructure; their proofs will be authored against the corrected encoding for the first time.

## Proposed new shape

Add two side-aware predicates on `WalkStep` and rewrite `IsCollider`'s `.cons _ s₀ (.cons _ s₁ _), 1` clause to consume them. `IsInto` itself stays unchanged — it expresses a different question (`is the node `w` an arrowhead-endpoint of this WalkStep`) that `claim_3_22`'s `s.reverse.IsInto w ↔ s.IsInto w` symmetry lemma and various other proofs depend on. The two new predicates are sided variants of "arrowhead at source / arrowhead at target" that take *no node argument*, since the WalkStep's own type `WalkStep G u v` already pins source vs target at the type level.

### `Section3_3/CollidersAndNon.lean`

New helpers in the `WalkStep` namespace (alongside `IsInto`, line 339):

```lean
/-- `s.HeadAtTarget` iff the walk-step `s : WalkStep G u v` has an
    arrowhead at the target end `v`. -/
def HeadAtTarget : ∀ {u v : Node}, WalkStep G u v → Prop
  | _, _, .forwardE _  => True   -- (u,v) ∈ G.E: head at v
  | _, _, .backwardE _ => False  -- (v,u) ∈ G.E: tail at v
  | _, _, .bidir _     => True   -- s(u,v) ∈ G.L: arrowheads at both

/-- `s.HeadAtSource` iff `s : WalkStep G u v` has an arrowhead at the
    source end `u`. -/
def HeadAtSource : ∀ {u v : Node}, WalkStep G u v → Prop
  | _, _, .forwardE _  => False  -- (u,v) ∈ G.E: tail at u
  | _, _, .backwardE _ => True   -- (v,u) ∈ G.E: head at u
  | _, _, .bidir _     => True   -- s(u,v) ∈ G.L: arrowheads at both
```

Both are total and case-exhaustive on the three `WalkStep` constructors. Neither consults `G.L`: the constructor identity is the witness of which channel the step uses, and the LN's collider definition reads the walk's *trajectory* (which physical edge each step takes), not the graph's edge inventory between the step's endpoints. Coexisting L-edges between the same `(u, v)` pair do not change the trajectory's arrowhead at the source/target ends — only `.bidir` carries arrowheads at both ends, and that case is handled directly.

Rewrite `IsCollider`'s clause-1 case (at `Section3_3/CollidersAndNon.lean:632-633`) to:

```lean
def IsCollider : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ (.nil _ _), _ => False
  | _, _, .cons _ _ (.cons _ _ _), 0 => False
  | _, _, .cons _ s₀ (.cons _ s₁ _), 1 =>
      s₀.HeadAtTarget ∧ s₁.HeadAtSource
  | _, _, .cons _ _ (p@(.cons _ _ _)), k + 2 => p.IsCollider (k + 1)
```

— same five clauses as currently; only clause 1's body changes. The walk's middle vertex `v_k` no longer appears in the test because the WalkStep types `s₀ : WalkStep G _ v_k` and `s₁ : WalkStep G v_k _` already pin which end of each step corresponds to `v_k` (target of `s₀`, source of `s₁`). Self-loop steps no longer collapse the side-of-step distinction: a `.forwardE` self-loop has `HeadAtTarget = True` and `HeadAtSource = False` regardless of `u = v`, so the bug disappears at the type-and-pattern-match level rather than via an additional runtime check.

### `IsInto` stays

`WalkStep.IsInto` is unchanged. It captures a coarser, non-side-aware question ("is `w` *any* arrowhead-endpoint of this step?") that has consumers outside the collider definition — most notably `SigmaSeparationSymmetric.lean:142` (`s.reverse.IsInto w ↔ s.IsInto w` reversal lemma) and the `IsCollider` *unfolding* proofs in `AcyclicNonCollidersBlockable.lean:220–272`. Those consumers either (a) only care about the non-self-loop case (where IsInto is correct), or (b) explicitly handle the per-constructor pattern. Tracking down each consumer and migrating to the sided predicates is *out of scope* for this refactor; the goal here is to make `IsCollider` itself semantically correct on self-loops, which is the bug source.

### `def_3_15`'s rewritten tex spec — `tex/def_3_15_CollidersAndNon.tex`

The tex's English description of "arrowhead at `v_k`" reads the walk graph-theoretically and is already correct (the LN explicitly considers the walk's two adjacent edges at `v_k`, with arrowheads from `e_{k-1}` ending at `v_k` and from `e_k` starting at `v_k` — i.e., side-aware in the prose). No tex changes needed; the encoding catches up to what the tex already meant.

### `def_3_15`'s `addition_to_the_LN` — `Chapter3_GraphTheory/data.json`

Append a new clarification block `[collider_side_aware_walkstep_predicates]` documenting that the Lean encoding tests `HeadAtTarget`/`HeadAtSource` on the left/right walk-steps, with rationale: a directed self-loop `(v, v) ∈ G.E` at the right slot is a tail-incident edge at `v_k = v` on the source side, NOT a head, and the LN's collider definition is correspondingly false on `a → b → b` walks. Keep the existing addition blocks as-is.

### `def_3_15`'s design-choice comment block in `CollidersAndNon.lean`

The comment block above `IsCollider` (lines 540-625 approximately) has a "Why test `IsInto vk` on both sides" section that codifies the *current* — buggy — choice. Rewrite the relevant bullets to explain the side-aware split, citing the self-loop pathology as the motivating case. The other design-choice bullets (recursion shape, position arithmetic, base cases) are unaffected.

## Downstream rows pulled into the refactor table

Expected, modulo whatever `find_dependents.py` discovers (the discovery runs `lake build` against the renamed root and observes every transitive consumer):

- **def_3_16** `BlockableAndUnblockable.lean` — defines `IsBlockableNonCollider` / `IsUnblockableNonCollider` over `IsNonCollider` (= `¬ IsCollider`). The Lean signatures are unchanged; bodies recompile as-is. The `HasBlockingLeftSlot` / `HasBlockingRightSlot` helpers are already side-aware via their own constructor-pattern matches — no edit needed.
- **def_3_17** `SigmaBlockedWalks.lean` (`IsSigmaBlockedGiven`, `IsSigmaOpenGiven`) — consumes `IsCollider` / `IsBlockableNonCollider` only via the predicates' public Prop signature, which is unchanged.
- **def_3_18** `ISigmaSeparation.lean` — consumes `IsSigmaBlockedGiven` indirectly through the walk-quantifier shape. Untouched at the source-text level; the *content* of σ-separation tightens (fewer walks are colliders ⇒ more walks are unblocked ⇒ fewer pairs are σ-separated). This shifts the truth-set of `IsISigmaSeparated` on graphs that contain directed self-loops on their walks. Verify nothing builds on a stale-superset assumption.
- **claim_3_20** `AcyclicNonCollidersBlockable.lean` — proof uses an explicit `(s₀.IsInto vMid ∧ s₁.IsInto vMid)` unfolding (line 220). The unfolding must change to `s₀.HeadAtTarget ∧ s₁.HeadAtSource` in lock-step with `IsCollider`'s clause-1 body. The proof's overall structure (acyclic ⇒ every non-collider position is blockable) is unaffected.
- **claim_3_21** `UnblockableNonCollidersOpen.lean` — re-port, audit for `IsInto`-style assumptions.
- **claim_3_22** `SigmaSeparationSymmetric.lean` — re-port. The `s.reverse.IsInto w ↔ s.IsInto w` reversal lemma stays (`IsInto` unchanged), but the proof's use of the lemma to lift to collider symmetry must thread through the new `HeadAtTarget`/`HeadAtSource` predicates. May require a small lemma `s.reverse.HeadAtTarget ↔ s.HeadAtSource` (and the symmetric one), provable by case-on-the-three-constructors.
- **claim_3_23**, **claim_3_24**, **claim_3_25** — not yet attempted. The refactor table picks them up and they're solved for the first time against the corrected encoding.
- **claim_3_26** `IdSeparationAlt.lean` (already proven; trivial under any IsCollider semantics) — re-verify; no changes expected.
- **claim_3_27** `LabelRomanDisproof.lean` — **retract**. The refactor row sets `proven` back to `"no"` (rolling the `mistake` flow forward via the orchestrator's `unmistake` action on entry), re-uses the prove-side `Section3_3/LabelRoman.lean` file, and the row is solved on the prove side against the fixed encoding. The disproof-side tex and Lean files are deleted at finalize-time (Phase 7's solved-state cleanup handles the disprove-side artefact removal automatically once `proven = "yes"`).

## Why not the alternatives

- **Adding `w` as a second argument to `HeadAtTarget`/`HeadAtSource` (mirroring `IsInto`).** Defeats the type-safety: the WalkStep's `u` and `v` already encode the two ends, so a second `w` re-introduces the same equality-collapse ambiguity that broke `IsInto` on self-loops. The whole point of the side-aware split is to *not* compare against a `w`.
- **Defining `IsCollider` directly via a 3 × 3 truth table over `WalkStep` constructor pairs.** Equivalent in semantics; harder to read; encodes the same side-aware logic less compositionally. The two-helper factoring exposes "head at source / head at target" as separately-reusable concepts and lets future definitions (e.g. a `IsForkSource` predicate on a walk-step, if the chapter ever needs one) reuse the same vocabulary.
- **Fixing `IsInto` to take a side-tag instead of a `w`.** Breaks every consumer that pattern-matches the current shape `IsInto vk`. The dedicated helpers don't disturb existing call sites.
- **Patching `IsCollider` to short-circuit on self-loops by detecting `u = v`.** Hacky and only addresses the symptom on the exact `.forwardE` self-loop shape; doesn't address `.backwardE` self-loops (also possible — `(b, b) ∈ G.E` is a self-loop in `G.E` regardless of which constructor wraps it).

## Lifecycle commands

```
git checkout server_setting_up_scaffold        # must be on this branch
python extras/do_refactor.py init \
    --chapter 3 \
    --root-ref def_3_15 \
    --name collider_side_aware
```

`do_refactor.py init` will: create the `refactor_collider_side_aware` branch, run `find_dependents.py` (bullet-proof transitive scan; the rename + lake build pass over `Section3_3/CollidersAndNon.lean:IsCollider` is expected to surface `def_3_16`, `def_3_17`, `def_3_18`, `claim_3_20`, `claim_3_21`, `claim_3_22`, `claim_3_23`, `claim_3_24`, `claim_3_25`, `claim_3_26`, `claim_3_27` plus whatever §3.4+ rows already build on σ-separation if any are in `lean_files`), run `initialize_refactor.py` to build `Refactor_collider_side_aware/refactor_data.json`, commit, push the new branch. Then the human drives the refactor table with the canonical wrapper:

```
scaffold/scripts/run_refactor_pipeline.sh \
    leanification/Chapter3_GraphTheory/Refactor_collider_side_aware/refactor_data.json
```

which chains solve → finalize → merge with the post-`cdmg_typed_edges` workflow improvements active (DELETE marker form, Pass 1.7 duplicate-decl prediction, solve-time marker-hygiene gate, Pass 4 empty-namespace pruning, `time_committed` post-commit clean-tree guard).

```
REFACTOR_PLAN_FILE: leanification/refactors/refactor_collider_side_aware.md
ROOT_REF: def_3_15
ROOT_CHAPTER: 3
NAME: collider_side_aware
RECOMMENDED_INVOCATION: python extras/do_refactor.py init --chapter 3 --root-ref def_3_15 --name collider_side_aware
```
