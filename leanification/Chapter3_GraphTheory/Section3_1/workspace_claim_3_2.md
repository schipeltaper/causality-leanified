# Workspace for claim_3_2 — AcyclicIffTopologicalOrder

## State at run start
- formalized=no, proven=not proven, solved=no
- agent_registry is empty (no prior attempts on this row)
- statement stub: `claim_3_2_statement_AcyclicIffTopologicalOrder.tex` (filled with LN's `\begin{Lem}` block verbatim)
- proof stub: `claim_3_2_proof_AcyclicIffTopologicalOrder.tex` (only `\begin{proof} TODO \end{proof}`)
- target Lean file: `AcyclicIffTopologicalOrder.lean` (does **not** exist yet)

## What the LN says
`graphs.tex:222–245`:

> **Lem.** A CDMG `G=(J,V,E,L)` is acyclic if and only if it has a topological order.

The LN **already includes its own proof** wrapped in a `\Claude{ ... }` block
(lines 227–245). Both directions are spelled out:

- **(⇐)** Topological order ⇒ acyclic. If a non-trivial directed walk
  `v = v_0 ⟶ v_1 ⟶ … ⟶ v_n = v` (with `n ≥ 1`) existed, transitivity of
  the order would give `v_0 < v_1 < … < v_n = v_0`, contradicting irreflexivity.
- **(⇒)** Acyclic ⇒ topological order. Repeatedly pick a parent-free node in
  the induced subgraph `G_i` on the still-unselected nodes `R_i = (J∪V) ∖
  {v_1,…,v_{i-1}}`. Such a node exists because `G_i` is finite + acyclic.
  This yields the order `v_1 < v_2 < … < v_K`. Verify the parent constraint:
  if `v_j = v ∈ Pa^G(v_i = w)`, then `v` was still in `R_i` when `v_i` was
  selected, so `v ∈ Pa^{G_i}(v_i)`, contradicting parent-freeness — unless
  `j < i`, i.e. `v < w`.

The (⇒) direction requires **finiteness** of `J ∪ V` to terminate.

## Lean shape
The infrastructure is already in place:

- `Causality.CDMG.IsAcyclic G : Prop` — `Acyclicity.lean`
  (def `∀ v ∈ G, ¬ ∃ π : Walk G v v, π.IsDirected ∧ 1 ≤ π.length`)
- `Causality.CDMG.HasTopologicalOrder G : Prop` — `TopologicalOrder.lean`
  (def `∃ r, IsTopologicalOrder G r`)

The natural statement is:

```lean
theorem isAcyclic_iff_hasTopologicalOrder (G : CDMG α) :
    G.IsAcyclic ↔ G.HasTopologicalOrder
```

Both `Acyclicity.lean` (lines 28–33) and `TopologicalOrder.lean` (lines 21–27, 204–209)
already cross-reference this row by this exact shape — so the design is
already in agreement across the section.

## Open question for proof phase (NOT statement phase)
The (⇒) direction needs finiteness of `J ∪ V`. The LN's def_3_1 CDMG does
*not* bake `Fintype` into the structure (the vertex type `α` is fully
polymorphic). Three plausible options for the proof phase:

1. Add a `[Fintype α]` hypothesis to the iff (or just to the `→` direction).
2. Add a hypothesis `(J ∪ V).Finite`.
3. Phrase the iff conditionally on finiteness, or split into two lemmas.

The LN's own proof says "since `G_i` is acyclic and **finite**", so finiteness
is *used*, not derived. The statement Lem 224 itself does not mention
finiteness — that may be an oversight in the LN, or the LN implicitly
assumes finite vertex sets globally. **The next manager (proof phase) should
revisit this.** For now (statement phase) we will go with option 1 — a
`[Fintype α]` hypothesis on the iff — because:

- it matches the LN's implicit "finite CDMG" reading,
- `Fintype α` is the most common Lean idiom for "the underlying set is
  finite", and
- the LN's def_3_1 does not constrain `α` further, so we cannot derive
  finiteness; it has to be an extra hypothesis somewhere.

If the proof-phase manager finds option 2 or 3 better, the statement can be
adjusted (with a re-run of `review_design` / `verify_equivalence`).

## Plan (this is Manager A — statement only)
1. ✅ Context gathered (this file).
2. ▶ Dispatch `formalize_claim_in_lean.md` to create
   `AcyclicIffTopologicalOrder.lean` with theorem statement and `sorry` body.
3. `review_design` — full-LN check of the statement.
4. `verify_equivalence` — focused statement-vs-LN check.
5. `new_manager` — handoff dossier to Manager B (proof phase).

## Agent registry
- `spawn_agent_sub_task` (formalize_claim_in_lean) — id `deef23de-40b0-4fab-98d4-bbac1c649b02`
  - **Result**: created `AcyclicIffTopologicalOrder.lean` with theorem
    `Causality.CDMG.isAcyclic_iff_hasTopologicalOrder [Finite α] (G : CDMG α) : G.IsAcyclic ↔ G.HasTopologicalOrder := by sorry`.
  - **Deviation from plan**: chose `[Finite α]` (Prop-valued) over `[Fintype α]`
    (data-valued). Worker's rationale: Mathlib's `linter.unusedFintypeInType`
    flags `[Fintype α]` for `Prop`-valued statements where the concrete
    enumeration is only needed in the proof; `[Finite α]` is the weakest
    finiteness hypothesis the proof needs, derivable from `[Fintype α]`
    automatically, and `Fintype α` is recoverable inside the proof via
    `Fintype.ofFinite α`. Documented at length in the file's design-choice
    block. **Reviewer should weigh in — this is the main design call.**

## Turn 2 — dispatching `review_design`
Goal: confirm the statement shape is natural given the whole LN. Reviewer
focuses on:
  (a) existential RHS (`HasTopologicalOrder`) vs relation-level
      (`IsTopologicalOrder G r`),
  (b) `[Finite α]` vs `[Fintype α]` vs `(G.J ∪ G.V).Finite`,
  (c) name / namespacing / argument order.

- `review_design` (id `773f8b2f-4290-4497-94a7-4670aa7a5674`) — **PASS**.
  Reviewer endorsed: (a) bundled-iff over split lemmas, (b) existential RHS,
  (c) `[Finite α]` over `[Fintype α]` (Mathlib linter alignment), (d) name
  + namespace + argument order. No design changes needed.

## Turn 3 — dispatching `verify_equivalence`
Goal: focused statement-level check that the Lean theorem is exactly
equivalent to the LN block (independent from the design review).

- `verify_equivalence` (id `5c285337-f19a-4dbe-8c46-2c5575a1deb9`) — **PASS**.
  Verifier confirmed: every LN hypothesis is a Lean hypothesis, the
  `[Finite α]` instance is strictly stronger than the LN reading in
  isolation but explicitly documented and motivated by the LN's own proof.
  No equivalence gap.

## Turn 4 — handoff to Manager B

Both statement-level verifiers have PASSed. Per the manager workflow
(claim row → Manager A statement-only → handoff → Manager B for whole
proof), this is the natural handoff point. Statement-phase commit:
`scaffold/build_and_commit.sh "claim_3_2: statement (AcyclicIffTopologicalOrder)"`.

The next manager picks up with:
  - target Lean file already in place (`AcyclicIffTopologicalOrder.lean`,
    theorem body = `sorry`),
  - empty proof tex stub
    (`claim_3_2_proof_AcyclicIffTopologicalOrder.tex` —
    only `\begin{proof} TODO \end{proof}`),
  - LN proof already drafted *in `graphs.tex` lines 227 -- 245* inside a
    `\Claude{...}` block (write_tex_proof.md's first step is to find this
    and copy it).

## Open issues flagged for Manager B
1. **Finiteness phrasing** — Manager A chose `[Finite α]`; both verifiers
   endorsed. If the proof worker finds `(G.J ∪ G.V).Finite` (Set.Finite)
   materially cleaner, the statement *can* be revisited (with a re-run of
   `review_design` / `verify_equivalence`). Current expectation: stick
   with `[Finite α]`.
2. **`Fintype` recovery inside (⇒)** — the proof worker may need
   `Fintype.ofFinite α` from `Mathlib.Data.Fintype.EquivFin` to enumerate
   the node set; this is already noted in the Lean docstring.
3. **Splitting the iff in the Lean proof** — although the *statement* is
   one iff, the proof worker may choose to split internally:
   ```
   refine ⟨?mp, ?mpr⟩
   · -- (⇒) acyclic ⇒ has topological order  [uses [Finite α]]
   · -- (⇐) topological order ⇒ acyclic       [no finiteness needed]
   ```
   This is purely a Lean-proof-style choice and does not affect the
   statement.
