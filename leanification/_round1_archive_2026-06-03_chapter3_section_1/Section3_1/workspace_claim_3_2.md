# Workspace for claim_3_2 — AcyclicIffTopologicalOrder

## LN tex block

```
\begin{Lem}
        A CDMG  $G=(J,V,E,L)$ is acyclic if and only if it has a topological order.
\end{Lem}
```

## LN proof (lifted from graphs.tex L227-245)

```
(⇐)  Suppose < is a topological order of G, i.e. v ∈ Pa^G(w) ⟹ v < w.
     If there were a non-trivial directed walk v = v_0 → v_1 → … → v_n = v
     (n ≥ 1), then v_0 < v_1 < … < v_n = v_0, a contradiction.

(⇒)  Suppose G is acyclic. We construct a topological order by repeatedly
     selecting a node with no parents in the remaining graph.
     Define v_1, …, v_K (K = |J ∪ V|) inductively: given v_1, …, v_{i-1},
     let R_i := (J ∪ V) \ {v_1, …, v_{i-1}} and G_i the subgraph of G induced
     on R_i. Since G_i is acyclic (as an induced subgraph of an acyclic
     graph) and finite, it has a node v_i with Pa^{G_i}(v_i) = ∅ (otherwise
     following parent edges would produce a directed cycle). Choose any
     such v_i.

     This gives a total order v_1 < v_2 < ⋯ < v_K. If v = v_j ∈ Pa^G(w = v_i),
     then when w was selected, v was still in R_i, so v would have been a
     parent of w in G_i, contradicting Pa^{G_i}(v_i) = ∅ — unless v was
     already selected, i.e. j < i. Hence v < w.
```

## Wording-check subtleties — not registering

1. **`claim_finiteness_not_stated_but_required_by_def_3_8`** — already
   resolved upstream: def_3_1's `addition_to_the_LN` includes
   `[manual_1] Node sets J and V are both finite.`, and `CDMG.J / V :
   Finset Node` enforces it at the Lean level. The TopologicalOrder.lean
   design block already cites this. No global note needed.

2. **`has_a_topological_order_existence_vs_equipment`** — already
   resolved by the predicate-form encoding chosen for def_3_8. The
   TopologicalOrder.lean design block explicitly anticipates this row:
   "the form `claim_3_2` will use: `G.IsAcyclic ↔ ∃ lt,
   G.IsTopologicalOrder lt`". No global note needed.

## Plan

Manager A (this manager) — statement only:

1. ✅ Read claude.md, LN proof, predecessor Lean files (IsAcyclic, IsTopologicalOrder).
2. `spawn_agent_sub_task` → `formalize_claim_in_lean.md`. Target shape:
   `theorem isAcyclic_iff_exists_topologicalOrder (G : CDMG Node) :
      G.IsAcyclic ↔ ∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt := by sorry`
   New file `AcyclicIffTopologicalOrder.lean` (claims get their own file
   per the section's convention — cf. `CDMGRestrictions.lean` for claim_3_1).
3. `review_design`.
4. `verify_equivalence` (and `verify_equivalence_strict` recommended given
   this is a foundational equivalence).
5. `add_design_choice_comments`.
6. `new_manager` handoff to Manager B for the proof.

Manager B (next):

7. `spawn_agent_sub_task` → `write_tex_proof.md` (LN proof already exists,
   verbatim above; worker should adapt minimally).
8. `verify_tex_statement_plus_proof` + `verify_tex_proof`.
9. `spawn_agent_sub_task` → `prove_claim_in_lean.md`.
10. `simplify_proof`.
11. `solved`.

## Running log

- 2026-06-03: started. Plan written. Dispatching formalize_claim_in_lean.
- 2026-06-03: statement shipped. `AcyclicIffTopologicalOrder.lean` created;
  imports both `Acyclicity` and `TopologicalOrder` (siblings — both depend on
  `Walks`, neither on the other, so explicit dual import is required).
  Theorem `isAcyclic_iff_exists_topologicalOrder` carries the
  `∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt` shape pinned by the
  predecessor design blocks. File added to `Chapter3_GraphTheory.lean`
  aggregator. `lake build` clean with only the expected `sorry` warning on
  line 78. Brief shape note in place above the start marker; deep design
  block deferred to `add_design_choice_comments`. Ready for `review_design`
  / `verify_equivalence` next.
