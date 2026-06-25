# Refactor plan: eqViaNodeMap_injective

**Status:** proposed (not yet executed)
**Date:** 2026-06-25
**Root ref:** claim_3_7 (TwoDisjointNode)
**Root chapter:** 3
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_eqViaNodeMap_injective

## Why this refactor is needed

The current formalisation of `eqViaNodeMap` at `Section3_2/TwoDisjointNode.lean:143` reads:

```lean
def eqViaNodeMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : CDMG α) (G' : CDMG β) (f : α → β) : Prop :=
  G.J.image f = G'.J
    ∧ G.V.image f = G'.V
    ∧ G.E.image (Prod.map f f) = G'.E
    ∧ G.L.image (Sym2.map f) = G'.L
```

The design comment block above the def claims this realises "the LN's *equality up to the canonical bijection of carriers*". But `f : α → β` is unconstrained — no injectivity, no surjectivity, no bijectivity. `Finset.image` has set-semantics: duplicates are dropped. So a many-to-one `f` that collapses distinct G-nodes to the same G'-node can satisfy all four conjuncts while G and G' are not isomorphic as CDMGs.

### Concrete counter-witness to the predicate's intended semantics

- `G : CDMG (Fin 3)` with `J = {0, 1}`, `V = {2}`, `E = {(0, 2), (1, 2)}`, `L = ∅` (3 underlying nodes).
- `G' : CDMG (Fin 2)` with `J = {0}`, `V = {1}`, `E = {(0, 1)}`, `L = ∅` (2 underlying nodes).
- `f : Fin 3 → Fin 2`: `0 ↦ 0`, `1 ↦ 0`, `2 ↦ 1`.

Then `G.J.image f = {0} = G'.J`, `G.V.image f = {1} = G'.V`, `G.E.image (Prod.map f f) = {(0, 1)} = G'.E` (both `(0,2)` and `(1,2)` collapse to `(0,1)`), `G.L.image (Sym2.map f) = ∅ = G'.L`. So `eqViaNodeMap G G' f` is `True` even though G has 3 nodes and G' has 2 — they are not isomorphic CDMGs.

### The bug is currently latent but real

Every consumer call site (`claim_3_7`, `claim_3_8`, `claim_3_10`, `claim_3_11`, `claim_3_14`, `claim_3_15`, `claim_3_18`, `claim_3_19`) passes a specific structural flatten map (`flattenSplit`, `flattenIntExt`, `flattenSwigDoit`, etc.). The claim is that the iterated operation's CDMG is `eqViaNodeMap`-equivalent to a single-operation CDMG via the flatten map.

But: at least one of these flatten maps — `flattenSplit` at `Section3_2/TwoDisjointNode.lean:113` — is **not injective globally**:

```
flattenSplit (.copy0 (.unsplit w)) = .copy0 w
flattenSplit (.copy0 (.copy0 w))   = .copy0 w     ← same output, different input
flattenSplit (.copy0 (.copy1 w))   = .copy1 w
flattenSplit (.copy1 (.unsplit w)) = .copy1 w     ← same output, different input
```

The map `flattenSplit : SplitNode (SplitNode Node) → SplitNode Node` has `3 × 3 = 9` possible constructor patterns on the domain side and only `3` on the codomain side. It is necessarily many-to-one on its full domain.

What *does* hold for `flattenSplit` is **injectivity on the actual node set of the doubly-iterated graph** `(G_split W₁)_split W₂` when `W₁` and `W₂` are appropriately disjoint — the collapsed pairs above never both appear in that node set simultaneously. So the claim's truth value is fine; what's flawed is that the *predicate* doesn't carry the constraint that makes the truth value meaningful. The predicate is satisfied by any flatten map that *happens* to image-collapse the right way, regardless of whether the underlying carrier-level injection is sound.

This is the "encoding too weak; relies on use-site discipline" pattern. The predicate `eqViaNodeMap G G' f` should commit to "G and G' are isomorphic via the carrier map f" — which requires f to be injective on the source carrier (or at least on G.J ∪ G.V). Without that commitment, downstream consumers can't reason about node-count preservation, fibre-of-projection structure, or any other carrier-level fact from `eqViaNodeMap` alone — they'd have to re-prove injectivity at every use site, defeating the purpose of having a reusable equivalence predicate.

## Proposed new shape

Strengthen `eqViaNodeMap` by adding an injectivity conjunct on the source carrier set. The natural minimum is **injectivity on `↑G.J ∪ ↑G.V` as a `Set Node`** — the nodes that appear in any of G's four data fields (E and L's endpoints are constrained to `J ∪ V` by G's `hE_subset` and `hL_subset` axioms, so injectivity on `J ∪ V` is sufficient).

### `Section3_2/TwoDisjointNode.lean`

`eqViaNodeMap` becomes:

```lean
def eqViaNodeMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : CDMG α) (G' : CDMG β) (f : α → β) : Prop :=
  Set.InjOn f (↑G.J ∪ ↑G.V)
    ∧ G.J.image f = G'.J
    ∧ G.V.image f = G'.V
    ∧ G.E.image (Prod.map f f) = G'.E
    ∧ G.L.image (Sym2.map f) = G'.L
```

The first conjunct says `f` is injective on the union of G's input and output node sets (coerced from `Finset Node` to `Set Node`). The remaining four conjuncts are unchanged.

Why `Set.InjOn`, not `Function.Injective`:
- `Function.Injective f` would require f to be injective on the *entire* carrier type `α`. That's stronger than necessary — only G's actual nodes need to be discriminated. For carrier types like `SplitNode (SplitNode Node)`, where many "off-graph" elements exist that don't appear in any real iterated split, the global-injectivity reading is over-tight and would force consumer rows to prove global injectivity of their flatten maps (often false, e.g. `flattenSplit`).
- `Set.InjOn f (↑G.J ∪ ↑G.V)` is exactly the minimum semantic content needed: distinct G-nodes (in J or V) map to distinct G'-nodes. Edges and L-elements are automatically discriminated because their endpoints are constrained to `J ∪ V` by `def_3_1`'s subset axioms.

### Downstream consumer rows pulled into the refactor table

Each consumer of `eqViaNodeMap` now has to discharge the new `Set.InjOn` conjunct in its `eqViaNodeMap` proof obligation. This is a per-row new sub-proof, typically 10-30 lines, structured as a case-analysis on the doubly-iterated `SplitNode` (or `IntExtNode`) constructors with `Finset.mem_union` + `Finset.mem_image` destructuring on each branch.

Expected rows surfaced by `find_dependents.py` (transitive scan):

- **claim_3_7** (`TwoDisjointNode.lean`) — `flattenSplit`'s `Set.InjOn` on `(G_split W₁)_split W₂`'s J ∪ V. Two iteration orders, two `eqViaNodeMap` calls; both need the new InjOn proof.
- **claim_3_8** (`DisjointHardInterventions.lean`) — same shape, hard-intervention variant.
- **claim_3_10** (`TwoDisjointNodeSwig.lean`) — SWIG variant.
- **claim_3_11** (`DisjointHardInterventionsSwig.lean`) — SWIG-hard-intervention variant.
- **claim_3_14** (`AddingInterventionNodes.lean`) — `flattenIntExt`'s `Set.InjOn` on `(G_doit(W₁))_doit(W₂)`'s J ∪ V.
- **claim_3_15** (`AddingInterventionNodesSwig.lean`) — SWIG variant.
- **claim_3_18** (`MarginalizationAndIntervention.lean`) — composite marginalization + intervention.
- **claim_3_19** (`MarginalizingOutThe.lean`) — composite.

Each row's flatten map needs an `_InjOn` lemma proved once and threaded through every `eqViaNodeMap` call in that file. The proofs are mechanical — case-analysis on the constructor pairs (3×3 = 9 cases for `SplitNode`, 2×2 = 4 cases for `IntExtNode`) showing that within the actual node set of the iterated graph, the constructor pattern that would collapse two distinct inputs never co-occurs (i.e., for `flattenSplit`, the `.copy0 (.unsplit w)` form is in the doubly-iterated J ∪ V only when `w ∈ W₁ ∩ W₂ᶜ`, while `.copy0 (.copy0 w)` is in there only when `w ∈ W₂`, and the W₁/W₂-disjointness hypothesis on the claim ensures these two cases never share a `w`).

## Why not the alternatives

- **`Function.Bijective f`** — overshoots. Injectivity is what's needed for the predicate to faithfully encode "equal up to carrier renaming"; surjectivity onto the entire codomain type `β` is already implied by the four image-equality conjuncts (G'.J ∪ G'.V is the image of G's nodes, so the predicate already commits to G' having no nodes outside f's image). Adding `Surjective f` would force every consumer to prove the surjectivity onto a possibly-larger carrier type, which is again over-tight.
- **`Function.Injective f` (global)** — over-tight (see "Why `Set.InjOn`" above). `flattenSplit` and `flattenIntExt` are *not* globally injective; only injective when restricted to the actual iterated-graph node set. Forcing global injectivity would break the rows.
- **Leave `eqViaNodeMap` as-is and add a separate `eqViaNodeMap_with_injOn` predicate** — bifurcates the API. The whole reason `eqViaNodeMap` exists is to be the canonical "equal-up-to-renaming" predicate; having two flavors means every theorem statement has to pick one, and consumers downstream of the predicate's truth value can't know which guarantee they're getting. Cleaner to fix the predicate in place.
- **Add `Set.InjOn` as a side hypothesis on each consumer theorem rather than as a conjunct of `eqViaNodeMap`** — re-introduces the use-site-discipline pattern this refactor is designed to eliminate. The predicate should be self-contained; if it says "G and G' are equivalent via f", it should carry the full content of that claim.

## Lifecycle commands

```
git checkout server_setting_up_scaffold
python extras/do_refactor.py init \
    --chapter 3 \
    --root-ref claim_3_7 \
    --name eqViaNodeMap_injective \
    --decl-name eqViaNodeMap
```

The `--decl-name eqViaNodeMap` override is needed because `find_dependents.py` defaults to the row's title (`TwoDisjointNode`) but the rename target is the helper `eqViaNodeMap` defined inside that row's file.

Then drive end-to-end:

```
scaffold/scripts/run_refactor_pipeline.sh \
    leanification/Chapter3_GraphTheory/Refactor_eqViaNodeMap_injective/refactor_data.json
```

```
REFACTOR_PLAN_FILE: leanification/refactors/refactor_eqViaNodeMap_injective.md
ROOT_REF: claim_3_7
ROOT_CHAPTER: 3
NAME: eqViaNodeMap_injective
RECOMMENDED_INVOCATION: python extras/do_refactor.py init --chapter 3 --root-ref claim_3_7 --name eqViaNodeMap_injective --decl-name eqViaNodeMap
```
