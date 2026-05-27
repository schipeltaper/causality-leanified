# Workspace for claim_3_22 — SigmaSeparationSymmetric

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

---

## Source (LN graphs.tex lines 1366–1369, trailing claimmark inside def_3_18)

```latex
% claim_3_22
\begin{claimmark}
Note that $\sigma$-separation is symmetric: $A \sPerp_G B \given C \iff B \sPerp_G A \given C$,
since when $J = \emptyset$ the set of walks between $A$ and $B$ is the same regardless of direction,
and the $\sigma$-blocking conditions are invariant under walk reversal.
\end{claimmark}
```

## What this claim is (one paragraph)

A trailing-claimmark *note* inside the def_3_18 defmark. The LN's $\sigma$-separation
$\sPerp_G$ is the special-case rename of $i\sigma$-separation $\isPerp_G$ when $G$ has
no input nodes (`G.J = ∅`). The claim observes that *under that side-condition*, the
asymmetric "every walk from $A$ to $J\cup B$" universal collapses to the symmetric
"every walk from $A$ to $B$" universal — `J = ∅` removes the $J$-summand on the target.
Combined with the fact that the $\sigma$-blocking predicate is invariant under walk
reversal (every walk $\pi : A \to B$ has a reverse $\pi' : B \to A$, and the two are
$\sigma$-blocked together because colliders/non-colliders and ancestor membership are
all walk-reversal-symmetric), the result follows.

## Lean shape (statement only — Manager A's job)

File: `leanification/Chapter3_GraphTheory/Section3_3/SigmaSeparationSymmetric.lean`
Imports: `Chapter3_GraphTheory.Section3_3.ISigmaSeparation` (which transitively imports
`SigmaBlockedWalks`, `Walks`, etc.).

Target statement (with `sorry`):

```lean
theorem isSigmaSeparated_symm {α : Type*} (G : CDMG α) (hJ : G.J = ∅)
    (A B C : Set α) :
    G.IsSigmaSeparated A B C ↔ G.IsSigmaSeparated B A C := sorry
```

Side-condition `hJ : G.J = ∅` is explicit — it is the LN's "for the special case
$J = \emptyset$" hypothesis, which `IsSigmaSeparated` (an `abbrev` of
`IsISigmaSeparated`) does *not* bake in (see def_3_18 clause-4 design block in
`ISigmaSeparation.lean`).

The $\nsPerp_G$ contrapositive form
(`G.IsNotSigmaSeparated A B C ↔ G.IsNotSigmaSeparated B A C`) is **not** a separate
statement: `IsNotSigmaSeparated` is `abbrev`-equal to `IsNotISigmaSeparated`, which is
`¬ IsISigmaSeparated`; the negation form follows by `Iff.not` from the main symmetry
theorem, no extra theorem needed.

## Plan (manager-level, two-phase per claim row)

**Manager A (this manager) — statement only:**
1. (this step) Write the workspace plan. Done.
2. `spawn_agent_sub_task` → `formalize_claim_in_lean.md` to produce the Lean statement
   with `sorry` in `SigmaSeparationSymmetric.lean`.
3. `review_design` — full-LN-context check the Lean shape is natural (J = ∅ as
   side-condition, abbrev surface, etc.).
4. `verify_equivalence` — focused check the Lean statement matches the LN block.
5. `add_design_choice_comments` — write the *why* into the comment block above the
   declaration.
6. `new_manager` — handoff to Manager B with the dossier (Lean file, stub paths, LN
   block, verifiers passed).

**Manager B — the proof (TeX + Lean):**
7. `write_tex_proof` — first search LN for `\begin{proof}` after the claim (the LN
   text *is* the proof: "since when $J = \emptyset$ the set of walks between $A$ and
   $B$ is the same regardless of direction, and the $\sigma$-blocking conditions are
   invariant under walk reversal" — so it is a short justification, no separate
   `\begin{proof}` block). The tex proof will need to:
   - Pivot to `IsISigmaSeparated` (since `IsSigmaSeparated` is `abbrev`).
   - Use `hJ : G.J = ∅` to simplify `G.J ∪ B = B` and `G.J ∪ A = A` on both sides.
   - Apply walk reversal: for any walk $\pi : v → w$ there is $\pi^{-1} : w → v$ with
     the same $\sigma$-blocking status.
   - **Walk-reversal-preserves-σ-blocking is the key lemma.** It may not yet exist;
     the prover may need to introduce it. Position-level: collider/non-collider/
     blockable-non-collider are reversal-invariant, and `nodeAt k` on `π` corresponds
     to `nodeAt (π.length - k)` on `π.reverse`. The set $\Anc^G(C)$ is unchanged.
8. `verify_tex_proof`.
9. `prove_claim_in_lean` — translate to Lean. May need to introduce a helper lemma
   `Walk.isSigmaBlocked_reverse_iff : π.IsSigmaBlocked C ↔ π.reverse.IsSigmaBlocked C`.
   This helper might naturally live in `SigmaBlockedWalks.lean` (an `add_to`
   refactor decision) or in this file as a local helper.
10. `simplify_proof`.
11. `solved` → final-gate verifier.

## Notes & risks

- **The "walk-reversal-preserves-σ-blocking" infrastructure may not exist yet.** Search
  `Section3_3/*.lean` for any `_reverse_` lemmas about colliders or non-colliders. If
  absent, the prover must introduce them. The natural home for such lemmas is
  `Section3_3/SigmaBlockedWalks.lean` (or a co-located helper); the prover (Manager B)
  decides.
- **`IsSigmaSeparated` is `abbrev` for `IsISigmaSeparated`** — proofs are stated on
  $i\sigma$, with `hJ` simplifying `G.J ∪ B` to `B`. `simp only [hJ, Set.empty_union]`
  should do the bridging.
- **No mathlib reuse** — the entire CDMG/Walk/σ-blocking stack is bespoke; mathlib's
  `SimpleGraph` has no σ-blocking API.

---

## Manager A — DONE (statement phase)

All four statement-phase steps passed:

1. `spawn_agent_sub_task` → `formalize_claim_in_lean.md` — produced
   `SigmaSeparationSymmetric.lean` with the target statement and `sorry`.
2. `review_design` — **PASS**. Reviewer confirmed `IsSigmaSeparated` is the
   LN-faithful surface (asymmetric `IsISigmaSeparated` would be literally false
   without `hJ`), the `abbrev` introduction was *deliberately anticipating*
   this row (see `ISigmaSeparation.lean:710–757` design block), and the
   `theorem` + `Iff` shape matches the LN's `\iff` verbatim.
3. `verify_equivalence` — **PASS**. Lean conclusion =
   `G.IsSigmaSeparated A B C ↔ G.IsSigmaSeparated B A C`, side-condition
   `hJ : G.J = ∅` correctly encodes the LN's "$\sigma$-separation" qualifier
   (def_3_18 clause 4). Side-condition is documented in the design-choice
   block above the declaration.
4. `add_design_choice_comments` — **DONE**. The pre-existing design block
   (already written by the formalizer) was sharpened in three places:
   - "Stated on `IsSigmaSeparated`, not `IsISigmaSeparated`" — quoted the
     anticipating design block at `ISigmaSeparation.lean:710–757`.
   - Made the "literally false" sub-clause point at the $J$-on-target
     footnote of def_3_18 clause 1.
   - (Other tightenings; see Turn 4 report in history.)

State of files now:

- `SigmaSeparationSymmetric.lean`: statement complete (with `sorry`),
  rich module docstring, full design-choice comment block, "Constraints /
  known limitations" subsection, and "Infrastructure note for the future
  prover" enumerating what walk-reversal data already exists vs. what
  doesn't.
- `tex/claim_3_22_statement_SigmaSeparationSymmetric.tex`: populated by
  orchestrator (the LN block verbatim).
- `tex/claim_3_22_proof_SigmaSeparationSymmetric.tex`: orchestrator stub,
  `% TODO: write the proof body.` placeholder — **Manager B's first task**.

`lake build` is clean (the formalizer worker confirmed).

## Handoff → Manager B (the proof, TeX + Lean)

Next steps (per the claim-row workflow):

7. `spawn_agent_sub_task` → `write_tex_proof.md`. The LN block *includes a
   short proof sketch* ("since when $J = \emptyset$ ... walk reversal") —
   the writer should expand that sketch into a real `\begin{proof}` block.
   Search the LN around line 1366 (`graphs.tex`) for any standalone
   `\begin{proof}` block; the claimmark itself is self-contained (no
   separate proof block in the LN), so the sketch is all there is to work
   with — the writer constructs the proof from it.

   **Structure the proof will need:**
   - Pivot to `IsISigmaSeparated` (via `abbrev` reduction).
   - Use `hJ : G.J = ∅` to collapse `G.J ∪ B = B` and `G.J ∪ A = A` on both
     sides (`Set.empty_union`).
   - Apply walk reversal: for any walk $\pi : v \to w$ between $A$ and $B$,
     there is $\pi^{-1} : w \to v$ between $B$ and $A$, and the two are
     $\sigma$-blocked together.
   - **Key sub-lemma the proof will need:**
     "$\sigma$-blocking is walk-reversal-invariant". This decomposes into
     position-level invariances: `IsColliderAt`, `IsBlockableNonColliderAt`,
     `IsUnblockableNonColliderAt` are all unchanged under reversal modulo
     the `nodeAt k ↔ nodeAt (length - k)` re-indexing. The set
     $\Anc^G(C)$ is unchanged.

8. `verify_tex_proof` — independent check.
9. `spawn_agent_sub_task` → `prove_claim_in_lean.md`. The prover will
   almost certainly need to introduce
   `Walk.isSigmaBlocked_reverse_iff : π.IsSigmaBlocked C ↔ π.reverse.IsSigmaBlocked C`
   and its position-level primitives. The natural home is
   `Section3_3/SigmaBlockedWalks.lean` (or a new
   `SigmaBlockedReversal.lean`); the prover decides. **Walk-reversal data
   is already in place** in `Section3_1/Walks.lean`:
   `Walk.reverse`, `WalkStep.reverse`, `length_reverse`, and three
   `reverse_forward` / `reverse_backward` / `reverse_bidir` `@[simp]`
   lemmas. The σ-blocking-level invariance is what doesn't exist yet.
10. `simplify_proof`.
11. `solved` → `verify_row_solved`.

## Manager A → B notes & risks

- **The negation form is not a separate theorem.** `IsNotSigmaSeparated`
  is `abbrev` for `IsNotISigmaSeparated` = `¬ IsISigmaSeparated`, so the
  contrapositive `A \nsPerp_G B ↔ B \nsPerp_G A` follows by
  `not_congr isSigmaSeparated_symm`. Don't introduce a second theorem.
- **`hJ : G.J = ∅` is an explicit hypothesis, not a typeclass.** Design
  block lines 230–249 of the Lean file documents why.
- **The walk-reversal-preserves-σ-blocking infrastructure may be the
  bulk of the work.** Forewarn the prover: this is not a one-line proof.
  Position-level reversal invariance for each of
  `IsColliderAt` / `IsBlockableNonColliderAt` / `IsUnblockableNonColliderAt`
  has to be proved separately, and combined.

