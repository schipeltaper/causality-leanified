# Refactor plan: sigma_separation_J_empty_premise

**Status:** proposed (not yet executed)
**Date:** 2026-06-15
**Root ref:** def_3_18 (`ISigmaSeparation`)
**Root chapter:** 3
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_sigma_separation_J_empty_premise

## Why this refactor is needed

`def_3_18` currently formalises the LN's four-item iσ-separation / σ-separation block as:

| Item | LN concept | Current Lean shape | Marker |
|------|------------|--------------------|--------|
| 1 | `A ⫫ᵢ B \| C` (iσ-separation) | `def IsISigmaSeparated` | **main statement** (`--` markers) |
| 2 | `A ⪥ᵢ B \| C` (not iσ-separated) | `def IsNotISigmaSeparated` | helper (`---` markers) |
| 3 | `A ⫫ᵢ B` (iσ-separation, `C = ∅` case) | `abbrev IsISigmaSeparatedEmpty` | helper (`---` markers) |
| 4 | `A ⫫ B \| C` (σ-separation, `J = ∅` case) | `abbrev IsSigmaSeparated` | helper (`---` markers) |
| 4 | `A ⪥ B \| C` (not σ-separated, `J = ∅` case) | `abbrev IsNotSigmaSeparated` | helper (`---` markers) |

Two problems with the current shape:

1. **All four items are LN-mandated parts of the definition's statement, not statement-supporting infrastructure.** The current helper-marker assignment for items 2-4 misrepresents their status: the website builder renders only the `IsISigmaSeparated` block as "the statement of def_3_18", obscuring that the full LN definition includes the negation, the `C = ∅` alias, and the `J = ∅` aliases as named LN-anchored concepts. Per the marker convention's litmus test, a declaration that names an LN-mandated sub-concept of the row's statement should ride along as a main-statement marker.

2. **The `J = ∅` aliases silently drop the LN's `J = ∅` premise.** The LN's σ-separation notation `A ⫫_G B \| C` is defined only when `G` is a DMG (i.e. when `G.J = ∅`). The current `abbrev IsSigmaSeparated` body is just `G.IsISigmaSeparated A B C` with **no premise on `G.J`** — so a consumer can write `G.IsSigmaSeparated A B C` for a CDMG with non-empty `J` and get back the iσ-separated relation under a misleading name. The LN's typed-concept distinction (σ vs iσ) is lost. The fix: add a `J = ∅` premise (via an explicit `(hJ : G.J = ∅)` hypothesis, or by routing through the `IsDMG` typeclass / predicate if one exists).

3. **All five predicates silently drop the LN's `A, B, C ⊆ J ∪ V` premise.** The LN's σ- and iσ-separation are defined for `A, B, C` that are subsets of the graph's node carrier `J ∪ V`. The current Lean shape types `A B C : Set Node` without any subset constraint — a consumer can pass arbitrary `Set Node` (including nodes that don't exist in the graph) and get back a definitionally well-formed predicate that the LN never assigned a meaning to. The fix: add `(hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V)` premises to **every** predicate (or a more compact `(hABC : A ⊆ ↑G.J ∪ ↑G.V ∧ B ⊆ ↑G.J ∪ ↑G.V ∧ C ⊆ ↑G.J ∪ ↑G.V)` bundle). For `IsISigmaSeparatedEmpty` (items 3), there is no `C` — only `hA` and `hB`. The σ-aliases (items 4a, 4b) get this on top of the `J = ∅` premise.

## Proposed new shape

### Promote all 5 sub-defs to main-statement markers

Each of the 5 declarations (`IsISigmaSeparated`, `IsNotISigmaSeparated`, `IsISigmaSeparatedEmpty`, `IsSigmaSeparated`, `IsNotSigmaSeparated`) gets `-- def_3_18 -- start statement` / `-- def_3_18 -- end statement` wrap (two dashes), matching their LN-anchored status as named parts of the def_3_18 statement block. The website builder will then render all five.

The current single-statement-marker pattern was an underestimate of the LN's intent — the four-item block of def_3_18 is a single LN definition with multiple named sub-concepts, all of which are part of "the statement".

### Add `J = ∅` premise to `IsSigmaSeparated` / `IsNotSigmaSeparated`

The two `J = ∅` aliases (current `abbrev`s) become predicates with an explicit `J = ∅` premise. Two encoding choices, equally LN-faithful:

**Option A: explicit hypothesis.**
```lean
def IsSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node) : Prop :=
  G.IsISigmaSeparated A B C
```

**Option B: route through `IsDMG`** (if a `def IsDMG (G : CDMG Node) : Prop := G.J = ∅` predicate exists or is worth introducing).
```lean
def IsSigmaSeparated (G : CDMG Node) (hDMG : G.IsDMG) (A B C : Set Node) : Prop :=
  G.IsISigmaSeparated A B C
```

Either way the body stays the same (transparent forwarding to `IsISigmaSeparated`); only the type signature gains the premise. Same treatment for `IsNotSigmaSeparated`.

The `abbrev` form is replaced by `def` since the premise turns the declaration from a pure notational alias into a property-bearing definition.

### Add `A, B, C ⊆ G.J ∪ G.V` premises to all five predicates

Every predicate gains explicit subset hypotheses on its `Set Node` arguments. Concretely:

- `IsISigmaSeparated` and `IsNotISigmaSeparated` (items 1, 2): three subset hypotheses `(hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V)`.
- `IsISigmaSeparatedEmpty` (item 3): two subset hypotheses `(hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V)` — there is no `C`.
- `IsSigmaSeparated` and `IsNotSigmaSeparated` (items 4a, 4b): three subset hypotheses, in addition to the `J = ∅` premise above.

```lean
def IsISigmaSeparated (G : CDMG Node)
    (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    Prop :=
  ∀ {u v : Node} (π : Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C
```

Alternative bundling: a single `(hABC : A ⊆ ↑G.J ∪ ↑G.V ∧ B ⊆ ↑G.J ∪ ↑G.V ∧ C ⊆ ↑G.J ∪ ↑G.V)` hypothesis. The refactor row's manager picks whichever shape best matches the chapter convention (likely three separate hypotheses, matching the LN's per-set discussion).

## Affected rows

Per the grep scan: no chapter-3 Lean file outside `Section3_3/ISigmaSeparation.lean` itself references any of these five predicates (`IsISigmaSeparated`, `IsNotISigmaSeparated`, `IsISigmaSeparatedEmpty`, `IsSigmaSeparated`, `IsNotSigmaSeparated`). The refactor table is **single-row**:

| Ref | File | What changes |
|-----|------|--------------|
| `def_3_18` | `Section3_3/ISigmaSeparation.lean` | (a) Promote 4 of the 5 sub-defs to main-statement markers. (b) Add `J = ∅` premise to the two `J = ∅` aliases. (c) Add `A, B, C ⊆ ↑G.J ∪ ↑G.V` subset premises to all five predicates (where `A, B, C` are present — `IsISigmaSeparatedEmpty` only has `A, B`). |

`claim_3_22+` are not yet started (consumed σ-separation reasoning conceptually but haven't compiled against these names yet); they pick up the new shape directly when they are next attempted.

## Risks

- Choice between Option A (explicit `J = ∅`) vs Option B (`IsDMG` predicate) is a style call. Option B is cleaner if `IsDMG` already exists; Option A is local and doesn't introduce a new concept. The refactor row's manager makes the call based on what's already in scope.
- The website builder rendering of def_3_18 will look different (5 statement blocks instead of 1). This is the explicit goal.
- No downstream Lean file needs source changes (verified by grep). Phase 7b will confirm.
