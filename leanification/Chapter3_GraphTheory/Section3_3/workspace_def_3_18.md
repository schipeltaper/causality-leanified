# Workspace for def_3_18 — ISigmaSeparation (refactor: sigma_separation_J_empty_premise)

## Refactor goal (from `leanification/refactors/refactor_sigma_separation_J_empty_premise.md`)

Three deficiencies in the current Lean shape of `def_3_18`:

1. **All 5 sub-defs are LN-mandated parts of the def's statement** but only `IsISigmaSeparated` is marker-wrapped as a main statement (two-dash); the other four ride along as helpers (three-dash). Website builder under-renders.
2. **`IsSigmaSeparated` / `IsNotSigmaSeparated` silently drop the LN's `J = ∅` premise.** They're `abbrev`s with body `G.IsISigmaSeparated …` and no `hJ` constraint, so a CDMG with `G.J ≠ ∅` can be passed and the σ-typed concept gets the iσ semantics under a misleading name.
3. **All 5 silently drop the LN's `A, B, C ⊆ J ∪ V` premise.** Out-of-graph nodes are admissible at the type level; the LN's domain of definition is lost.

## Decisions

| Concern | Choice | Rationale |
|---|---|---|
| `J = ∅` premise encoding | **Option A: explicit `(hJ : G.J = ∅)`** | Word-for-word LN reading ("$J = \emptyset$"); `IsDMG` exists at `Section3_1/CDMGTypes.lean:196` but the literal form keeps def_3_18 self-contained and matches how `claim_3_22` will hand it in. |
| Subset hyps form | **Three separate `(hA …) (hB …) (hC …)`** | Matches chapter convention (Section 3.2 — `HardInterventionsCommute`, `DisjointHardInterventionsSwig`, `AddingInterventionNodes`, …); matches LN's per-set discussion. |
| Subset RHS Lean phrasing | **`↑G.J ∪ ↑G.V` (Set-level union of coerced Finsets)** | Matches the existing `(G.J : Set Node) ∪ B` pattern in the same file (body of `IsISigmaSeparated`); both sides are `Set Node`. Alternative `↑(G.J ∪ G.V)` (Finset union then coerce) is equally well-typed; pick whichever the formalizer finds cleaner. |
| `abbrev` vs `def` | `IsISigmaSeparated`, `IsNotISigmaSeparated`: stay `def`. `IsISigmaSeparatedEmpty`: stay `abbrev` (still pure notation — no `hJ`). `IsSigmaSeparated`, `IsNotSigmaSeparated`: **promote `abbrev` → `def`** because `hJ` is a non-trivial dependent argument. | Per refactor plan. |
| All 5 markers | **`-- def_3_18 -- start statement` / `… end statement` (two dashes)** on every replacement | Refactor plan §"Promote all 5 sub-defs to main-statement markers" — all 5 are LN-anchored named sub-concepts. |
| `variable {Node : Type*} [DecidableEq Node]` line | **Stays as-is**, three-dash helper markers preserved. Not inside any ORIGINAL/REPLACEMENT pair. | Its shape isn't changing; cleanup leaves it untouched. |

## New replacement signatures

```lean
-- def_3_18 -- start statement
def refactor_IsISigmaSeparated (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ∀ {u v : Node} (π : Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C
-- def_3_18 -- end statement

-- def_3_18 -- start statement
def refactor_IsNotISigmaSeparated (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ¬ G.refactor_IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement

-- def_3_18 -- start statement
abbrev refactor_IsISigmaSeparatedEmpty (G : CDMG Node) (A B : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.refactor_IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)
-- def_3_18 -- end statement

-- def_3_18 -- start statement
def refactor_IsSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.refactor_IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement

-- def_3_18 -- start statement
def refactor_IsNotSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.refactor_IsNotISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
```

## File-level structure (post-edit)

```
imports, namespace, /-! file doc -/

-- def_3_18 --- start helper       (unchanged variable block)
variable {Node : Type*} [DecidableEq Node]
-- def_3_18 --- end helper

-- (interleaved 5 × pair):
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsISigmaSeparated
… existing def with three-dash helper markers around it INTACT …
-- REFACTOR-BLOCK-ORIGINAL-END: IsISigmaSeparated

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsISigmaSeparated (was: refactor_IsISigmaSeparated)
… new def with two-dash statement markers …
-- REFACTOR-BLOCK-REPLACEMENT-END: IsISigmaSeparated

(repeat for IsNotISigmaSeparated, IsISigmaSeparatedEmpty, IsSigmaSeparated, IsNotSigmaSeparated)
```

## Plan

1. **Dispatch formalize-refactor worker.** Add 5 `REFACTOR-BLOCK-ORIGINAL` wraps and 5 `REFACTOR-BLOCK-REPLACEMENT` decls with the new shape. `lake build` clean.
2. `review_design` — natural shape check, full LN context.
3. `verify_equivalence` — focused match against LN + addition.
4. `verify_equivalence_strict` — recommended (new operator surface: `hA hB hC` and `hJ` hypotheses on existing predicates).
5. `add_design_choice_comments` — *why* the subset hyps, *why* `hJ`, *why* `abbrev` for item 3 only, *why* Option A over Option B. **Mandatory.**
6. `solved` → final gate.

## addition_to_the_LN review

The row's addition is `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]` (walk-reversal involution as background for the embedded `claim_3_22` symmetry remark). The refactor does not contradict this — the σ-typing premise (`J = ∅`) actually sharpens the symmetry-claim's domain. No revision needed.

## Notes / risks

- The body of `refactor_IsISigmaSeparated` is **byte-identical** to the original — only the signature gains hypotheses. The mathematical content of the predicate is unchanged; only its domain of definition is restricted.
- `Set.empty_subset _` is the canonical proof that `∅ ⊆ anything`. Lean elaborates the `_` to `↑G.J ∪ ↑G.V` from `refactor_IsISigmaSeparated`'s `hC` slot.
- The website builder won't run on this refactor row's solved (per manager.md "On `solved`, the orchestrator … does not … run the for-website worker"); the two simultaneous `-- def_3_18 -- start statement` blocks (original + replacement) coexist safely until Phase 7 cleanup deletes the originals.
