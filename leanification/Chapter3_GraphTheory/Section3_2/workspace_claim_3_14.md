# Workspace for claim_3_14 — AddingInterventionNodes

## Refactor port plan (refactor `eqViaNodeMap_injective`, dependent on `claim_3_7`)

### What changes

Root refactor strengthens `eqViaNodeMap` → `refactor_eqViaNodeMap` by adding a
1st conjunct `Set.InjOn f (↑G.J ∪ ↑G.V)`. The four image-equality conjuncts
(J, V, E, L) are unchanged.

### What needs porting in `AddingInterventionNodes.lean`

Two theorems live in this file:

* `addInterventionNodes_comm_disjoint` — uses `eqViaNodeMap` (lines 150, 158).
  **NEEDS PORTING** to `refactor_eqViaNodeMap`. Two `eqViaNodeMap` conjuncts
  (one per iteration order), so two new `Set.InjOn` sub-proofs.

* `addInterventionNodes_comm_hardIntervention` — uses literal `=` of CDMGs,
  NOT `eqViaNodeMap`. **NO PORT NEEDED.** Both CDMGs live in
  `CDMG (IntExtNode Node)`; the equality is direct. (Confirmed by inspection
  of file lines 359-369: signature is `... = ... ∧ ... = ...`.)

### Carrier map: `flattenIntExt` injectivity story

```
def flattenIntExt : IntExtNode (IntExtNode Node) → IntExtNode Node
  | .unsplit (.unsplit v) => IntExtNode.unsplit v
  | .unsplit (.intCopy w) => IntExtNode.intCopy w
  | .intCopy (.unsplit v) => IntExtNode.intCopy v
  | .intCopy (.intCopy w) => IntExtNode.intCopy w
```

Globally NOT injective: `.unsplit (.intCopy w)`, `.intCopy (.unsplit w)`,
and `.intCopy (.intCopy w)` all collapse to `.intCopy w`. But on the iterated
extended graph's J ∪ V (under `Disjoint W₁ W₂`) the patterns that appear are:

* `.unsplit (.unsplit j)` for `j ∈ G.J` → `.unsplit j`
* `.unsplit (.unsplit v)` for `v ∈ G.V` → `.unsplit v`
* `.unsplit (.intCopy w₁)` for `w₁ ∈ W₁ \ G.J` → `.intCopy w₁`
* `.intCopy (.unsplit w₂)` for `w₂ ∈ W₂ \ G.J` → `.intCopy w₂`

(Note: `.intCopy (.intCopy w)` does NOT appear on the iterated graph's J ∪ V
because the outer extension is indexed by `W₂.image .unsplit`, so the
outer-`intCopy` always wraps an inner `.unsplit`.)

Injective because:
- `.unsplit · → .unsplit ·` injectivity holds since G.J ∩ G.V = ∅ (def_3_1 axiom).
- `.unsplit (.intCopy w₁) ↦ .intCopy w₁` vs `.intCopy (.unsplit w₂) ↦ .intCopy w₂`
  collide iff `w₁ = w₂`. But `w₁ ∈ W₁`, `w₂ ∈ W₂`, and `Disjoint W₁ W₂` → no collision.
- Cross-tag (`.unsplit ·` vs `.intCopy ·`) cases close by constructor mismatch.

Disjointness `Disjoint W₁ W₂` is consumed in exactly the `intCopy`-vs-`intCopy`
(after-flatten) cross-cell case. The same `Disjoint W₁ W₂` (or `.symm`) works
for the other iteration order via W₁ ↔ W₂ swap.

### Plan steps

1. Write tex twin at `tex/refactor_claim_3_14_proof_AddingInterventionNodes.tex`.
   * Statement: restate via `refactor_eqViaNodeMap` reading (componentwise + carrier bijection injective on J ∪ V).
   * Proof: keep the original's componentwise (J, V, E, L) verification verbatim;
     add a new "Injectivity of `flattenIntExt` on iterated extended J ∪ V" paragraph
     handling the 4×4 case analysis with the disjointness use call-out.
2. `verify_tex_statement_plus_proof` (structural).
3. `verify_tex_proof` (mathematical).
4. Leanify: add a private helper `refactor_flattenIntExt_injOn_of_disjoint`
   and a `refactor_addInterventionNodes_comm_disjoint` theorem.
   * Wrap original `addInterventionNodes_comm_disjoint` (lines 145-356) with
     `REFACTOR-BLOCK-ORIGINAL-BEGIN/END` markers.
   * Add a `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END` block containing the
     `refactor_flattenIntExt_injOn_of_disjoint` helper AND the
     `refactor_addInterventionNodes_comm_disjoint` theorem.
   * Reuse the J/V/E/L image-equality conjuncts via `obtain` on the original
     theorem (same destructure trick that `refactor_twoDisjointNodeSplittingsCommute`
     uses — see TwoDisjointNode.lean lines 308-356).
5. `solved` → final-gate.

### Key references for workers

* Original: `AddingInterventionNodes.lean` (lines 145-356 = the theorem to port).
* Root refactor proof pattern: `TwoDisjointNode.lean`'s
  `refactor_flattenSplit_injOn_of_disjoint` and `refactor_twoDisjointNodeSplittingsCommute`
  (the "reuse the original for the 4 image-equality conjuncts, just add the InjOn discharge" trick).
* Root refactor tex twin: `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex`
  shows the "Injectivity" paragraph pattern.
