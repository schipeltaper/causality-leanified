# Workspace for claim_3_16 — MarginalizationPreserves

This file is the manager's scratchpad for this row. The plan below was
produced by the `plan_subtasks` worker on 2026-05-21. Subsequent
managers may freely extend it with notes-from-the-trenches.

---

## 1. Theorem decomposition

The LN remark has three sub-items. They are logically independent
(item-3a does *not* go through claim_3_2; see §3 below), but they all
share the same walk-shrinkage / walk-expansion paradigm. We split into
**five Lean theorems**, one per LN sub-item with item 2 split into
no-source and with-source variants:

| # | Lean name                              | LN content                                                                  |
|---|----------------------------------------|-----------------------------------------------------------------------------|
| 1 | `marginalize_anc_iff`                  | item 1 — `v_1 ∈ Anc^G(v_2) ↔ v_1 ∈ Anc^{G^{\sm W}}(v_2)`                    |
| 2 | `marginalize_bifurcation_iff`          | item 2 (no source) — symmetric `∃ bifurcation between v_1, v_2` ↔ idem      |
| 3 | `marginalize_bifurcation_source_iff`   | item 2 parenthetical — same with source `v_3` (see risks below)             |
| 4 | `marginalize_isAcyclic`                | item 3a — `G.IsAcyclic → (G.marginalize W).IsAcyclic`                       |
| 5 | `marginalize_isTopologicalOrder`       | item 3b — `G.IsTopologicalOrder r → (G.marginalize W).IsTopologicalOrder r` |

### Proposed signatures (illustrative — formalizer worker will finalise)

```lean
-- item 1
theorem marginalize_anc_iff (G : CDMG α) (W : Set α) {v₁ v₂ : α}
    (h₁ : v₁ ∉ W) (h₂ : v₂ ∉ W) :
    v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W).Anc v₂

-- item 2 (no source) — symmetric reading of LN "between"
theorem marginalize_bifurcation_iff (G : CDMG α) (W : Set α)
    {v₁ v₂ : α} (h₁ : v₁ ∈ G ∧ v₁ ∉ W) (h₂ : v₂ ∈ G ∧ v₂ ∉ W) :
    ((∃ π : Walk G v₁ v₂, π.IsBifurcation) ∨
     (∃ π : Walk G v₂ v₁, π.IsBifurcation)) ↔
    ((∃ π : Walk (G.marginalize W) v₁ v₂, π.IsBifurcation) ∨
     (∃ π : Walk (G.marginalize W) v₂ v₁, π.IsBifurcation))

-- item 2 (with source v_3) — refines hinge to .backward at v_3.
-- Define a helper predicate first:
--   def Walk.IsBifurcationWithSource (π : Walk G v w) (c : α) : Prop :=
--     ∃ bw : BifurcationWitness π, bw.m' = c ∧
--       (∃ h : bw.m ⟵[G] bw.m', bw.hinge = WalkStep.backward h)
theorem marginalize_bifurcation_source_iff (G : CDMG α) (W : Set α)
    {v₁ v₂ v₃ : α}
    (h₁ : v₁ ∈ G ∧ v₁ ∉ W) (h₂ : v₂ ∈ G ∧ v₂ ∉ W) (h₃ : v₃ ∈ G ∧ v₃ ∉ W) :
    ((∃ π : Walk G v₁ v₂, π.IsBifurcation ∧ π.IsBifurcationWithSource v₃) ∨
     (∃ π : Walk G v₂ v₁, π.IsBifurcation ∧ π.IsBifurcationWithSource v₃)) ↔
    ((∃ π : Walk (G.marginalize W) v₁ v₂,
        π.IsBifurcation ∧ π.IsBifurcationWithSource v₃) ∨
     (∃ π : Walk (G.marginalize W) v₂ v₁,
        π.IsBifurcation ∧ π.IsBifurcationWithSource v₃))

-- item 3a
theorem marginalize_isAcyclic (G : CDMG α) (W : Set α)
    (h : G.IsAcyclic) : (G.marginalize W).IsAcyclic

-- item 3b
theorem marginalize_isTopologicalOrder (G : CDMG α) (W : Set α)
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    (G.marginalize W).IsTopologicalOrder r
```

### Rationale & trade-offs for the split

- **Five theorems instead of one big remark-shaped Prop.** Each
  sub-item has a clean, citable signature that downstream rows can
  invoke directly. Claim_3_17's proof will call
  `marginalize_anc_iff` and `marginalize_bifurcation_iff` separately;
  claim_3_18 / claim_3_19 will additionally invoke
  `marginalize_isAcyclic`. A monolithic conjunction would force every
  caller to destructure.
- **Item 2 split into no-source + with-source.** The LN's
  "(with source v_3)" parenthetical is a refinement: in our Lean
  encoding, the with-source version is strictly more constrained than
  the no-source version *and* it is the one that interacts with the
  `L^{\sm W}` exclusion clause non-trivially (see risks §5.2 below).
  Splitting keeps the no-source signature usable on its own and lets
  the with-source theorem reuse the no-source proof's machinery
  rather than re-deriving it inline.
- **Item 3 split into acyclicity + topological order.** Logically
  independent — `marginalize_isAcyclic` is provable directly by
  walk-concatenation without going through claim_3_2. Splitting
  avoids a circular feeling (claim_3_2 ↔ item 3) and makes each
  theorem invokable separately. Downstream uses do call them
  separately (claim_3_17 / chapter 4 want acyclicity preservation
  even when no order is named; chapter 5's do-calculus wants the
  order itself).
- **Why a `Walk.IsBifurcationWithSource` helper predicate?** Direct
  reading `π.bifurcationSource hb = some v₃` is fragile because
  `bifurcationSource` is `noncomputable` (uses `Classical.choice`);
  two distinct bifurcation witnesses for the *same* walk could yield
  different sources, and the choice axiom doesn't let us reason about
  which witness gets picked. The witness-level predicate
  `IsBifurcationWithSource` quantifies over witnesses directly. The
  formalizer should add this helper to `Section3_1/Bifurcation.lean`
  if it isn't there (it isn't, as of 2026-05-21) — or, if scope rule
  4 prevents touching Section3_1, define it locally in
  `MarginalizationPreserves.lean` (and document the cross-section
  scope decision in design comments).

### Could the split go differently?

- **Merge item-2 no-source and with-source via `Option α` source
  parameter.** Considered; rejected. "No source" doesn't cleanly
  map to "source = none" because the latter means "bidir hinge"
  (one specific witness shape), while "no source" means "any
  witness shape". Two distinct predicates ⇒ two distinct theorems.
- **Drop item-3b entirely (subsume into item-3a + claim_3_2).** Yes,
  3b *follows* from 3a + claim_3_2 (acyclic ⇒ has topological order)
  + the converse, but the LN says "a topological order of G induces
  a topological order on G^{\sm W}", which is a constructive
  statement on the same relation. We mirror the LN — same relation
  `r` carries through — rather than rebuilding the order via a
  classical extraction.
- **Drop item-2 with-source for an MVP.** Tempting; the LN's
  parenthetical "(with source v_3)" is a refinement that doesn't
  appear in claim_3_17's proof and may not be cited by claim_3_18 /
  3_19 either. If it turns out to be unused, the manager can defer
  it. *Recommendation:* attempt it; if the exclusion-clause friction
  (risk §5.2) is too costly, defer and add a design comment
  documenting the deviation.

---

## 2. File placement & size estimate

- **Target file:** `leanification/Chapter3_GraphTheory/Section3_2/MarginalizationPreserves.lean`.
- **Imports:** `Chapter3_GraphTheory.Section3_2.Marginalization` (gives
  the four `@[simp]` lemmas + `Walk.InteriorIn`); transitively pulls in
  `Section3_1.Bifurcation`, which transitively gives `Walks`,
  `WalkPredicates`, `EdgeRelations`, `CDMG`. Additionally need:
    - `Chapter3_GraphTheory.Section3_1.FamilyReachability` (for `Anc`).
    - `Chapter3_GraphTheory.Section3_1.Acyclicity` (for `IsAcyclic`).
    - `Chapter3_GraphTheory.Section3_1.TopologicalOrder` (for
      `IsTopologicalOrder`).
    - `Chapter3_GraphTheory.Section3_1.FamilyDirect` (transitively;
      `TopologicalOrder` already pulls it).
- **Size estimate:** ~600 – 800 lines.
    - Theorem 1 (`marginalize_anc_iff`): ~120 lines including a
      `Walk.toMarginalize` / `Walk.fromMarginalize` shortcut translator
      helper (~50 lines).
    - Theorems 2 + 3 (bifurcation): ~250 lines combined — bifurcation
      witness manipulation is the heavy lifter, mostly shared
      between the two.
    - Theorem 4 (acyclicity): ~80 lines, mostly reusing the walk
      translator from theorem 1.
    - Theorem 5 (topological order): ~80 lines, four conditions to
      check.
    - Module docstring + design-choice blocks: ~150 lines.
- **If size blows past ~800 lines:** split along the LN's three
  sub-items:
    - `MarginalizationPreservesAncestors.lean` (theorem 1)
    - `MarginalizationPreservesBifurcations.lean` (theorems 2, 3)
    - `MarginalizationPreservesAcyclicity.lean` (theorems 4, 5)
  Keep the walk-translator helpers in the ancestors file (or factor
  them into a fourth `MarginalizationWalks.lean`); both downstream
  files import the ancestors one.
- **Update `Section3_2/main.tex`** to `\subfile`-include the new
  `claim_3_16_proof_MarginalizationPreserves.tex` (the proof file,
  per the convention in `claude.md` §"Repo structure").

---

## 3. Proof strategy sketches (no Lean code)

The unifying machinery is a pair of **walk translators** between `G`
and `G.marginalize W` exploiting `mem_marginalize_E` /
`mem_marginalize_L`. Sketch them once, reuse across all five
theorems.

### Walk-translator helpers (private to the file)

- **`Walk.fromMarginalize`** (informal): given a walk
  `π' : Walk (G.marginalize W) u v` whose every step is `.forward`
  (i.e. directed), expand each step (`u_i, u_{i+1}) ∈ E^{\sm W}` via
  `mem_marginalize_E` to a directed walk in `G` of length ≥ 1 with
  interior in `W`, then concatenate. Result: a directed walk in `G`
  from `u` to `v` whose interior includes all the in-`W` shortcuts.
- **`Walk.toMarginalize`** (informal, harder): given a directed walk
  `π : Walk G u v` with `u, v ∉ W`, partition `π.support` into
  maximal contiguous "in-`W`" stretches separated by "not-in-`W`"
  pivots `u = w_0, w_1, …, w_r = v` (where each `w_i ∉ W`). Each
  pivot-to-pivot stretch `w_i → ⋯ → w_{i+1}` is a directed walk in
  `G` of length ≥ 1 with interior in `W`, so by `mem_marginalize_E`
  there is an edge `(w_i, w_{i+1}) ∈ E^{\sm W}`. Cons these edges
  into a directed walk in `G.marginalize W`. *Length-≥-1 check:* each
  pivot-to-pivot stretch crosses at least one edge of `π`, so the
  shortcut edge satisfies the `1 ≤ π.length` clause of
  `mem_marginalize_E`.
- These translators are also needed for the directed *arms* of a
  bifurcation (left arm read in reverse is directed; right arm is
  directed), so write them once and reuse.

### Theorem 1 — `marginalize_anc_iff`

- (→) Use `Walk.toMarginalize` on the directed walk witnessing
  `v_1 ∈ Anc^G(v_2)`.
- (←) Use `Walk.fromMarginalize` on the directed walk witnessing
  `v_1 ∈ Anc^{G^{\sm W}}(v_2)`.
- The `v_1 ∈ G` ↔ `v_1 ∈ G.marginalize W` swap is automatic given
  `v_1 ∉ W` (and walks of length ≥ 1 force their endpoints into
  `G.V`; length-0 case is `v_1 = v_2`, both in `G.J ∪ (G.V \ W)`
  iff in `G.J ∪ G.V` and `∉ W`).
- *Rationale:* LN's item 1 has no explicit proof; this is the
  "obvious" claim and the translators do all the work.

### Theorem 2 — `marginalize_bifurcation_iff` (no source)

- (→) Given a bifurcation witness `bw` for `π : Walk G v₁ v₂`:
    - Apply `Walk.toMarginalize` to *the reverse of the left arm*
      (which is a directed walk in `G` from `bw.m` to `v_1`); reverse
      back to get the left arm in `G.marginalize W` (all backward).
    - Apply `Walk.toMarginalize` to the right arm directly.
    - Translate the hinge: case-split on whether
      `bw.m, bw.m' ∈ W`. The hardest case is when *both* hinge
      endpoints are interior to a maximal in-`W` stretch; then the
      hinge gets *absorbed* into the surrounding shortcut edge, and
      the surrounding shortcut is a bifurcation pattern in `G` →
      lands as an `L^{\sm W}`-edge (or `E^{\sm W}` if the exclusion
      fires, see risk §5.2).
    - Re-assemble into a witness for `Walk.IsBifurcation` in
      `G.marginalize W`. If the hinge ended up landing in
      `E^{\sm W}` (exclusion case), the resulting witness lives on
      `Walk (G.marginalize W) v₂ v₁` (the second disjunct of the
      symmetric ∨); read the original walk in reverse, with the
      directed shortcut serving as a `.backward` hinge.
- (←) Given a bifurcation witness `bw'` for
  `π' : Walk (G.marginalize W) v₁ v₂`:
    - Use `Walk.fromMarginalize` on (the reverse of) the left arm
      and on the right arm to expand the all-`forward` shortcut
      edges back into directed walks in `G`.
    - The hinge step `bw'.hinge` is either `.backward` (giving
      `(bw'.m', bw'.m) ∈ E^{\sm W}`, i.e. a directed walk in `G`
      from `bw'.m'` to `bw'.m` with interior in `W` — read in
      reverse as a backward arm in `G`) or `.bidir` (giving
      `(bw'.m, bw'.m') ∈ L^{\sm W}`, i.e. a bifurcation in `G` from
      `bw'.m` to `bw'.m'` with interior in `W` — splice the LN's
      `\hut ⋯ \hus \tuh ⋯` shape into the surrounding arms).
    - Concatenate everything: result is a bifurcation in `G`.
- *Reuses the LN's item-2 proof paradigm:* walk-shrinkage / expansion
  through `mem_marginalize_E` and `mem_marginalize_L`. The LN's actual
  proof inducts on `|W|` via claim_3_17 (`marginalizations-commute`);
  we avoid that forward reference by doing the multi-vertex shrinkage
  directly, which the `mem_marginalize_E` / `mem_marginalize_L`
  simp lemmas were *specifically designed* to support (see the long
  design-choice block in `Marginalization.lean`, especially the note
  about downstream callers using the symmetric `∨`-of-two-directions
  reading — claim_3_16 is the first such caller).
- *Symmetric reading is load-bearing:* the second disjunct of the ∨
  is what makes the exclusion case (risk §5.2) work — without the
  reverse-direction bifurcation, the (→) direction would fail when
  the bidir hinge lands in `E^{\sm W}` via the exclusion clause.

### Theorem 3 — `marginalize_bifurcation_source_iff` (with source)

- Same structure as theorem 2, with extra bookkeeping for the hinge:
  the hinge of the constructed witness must be `.backward h` with
  `h : bw.m ⟵ bw.m'` and `bw.m' = v₃`.
- Critical extra wrinkle: when the `L^{\sm W}`-exclusion fires
  (risk §5.2), a bidir hinge in `G` may *force* the hinge in
  `G^{\sm W}` to be backward, *introducing a source where the LN
  bifurcation had none*. This could break the LN's "source v₃"
  preservation in subtle cases. *Investigate before stating the
  theorem.* Possible mitigations:
    - Strengthen hypotheses: require `v_3` such that the hinge in
      G is `.backward` with target `v_3` and the exclusion doesn't
      fire on its endpoints.
    - State the theorem only for hinge endpoints not in `W` (forcing
      a clean correspondence).
    - Accept that the exclusion case is a Lean-encoding artefact
      and state the LN-faithful theorem with the artefact
      documented in a design-choice block.
- *Recommendation:* dispatch the formalizer worker for theorems 1, 2,
  4, 5 first; punt theorem 3 to a follow-up turn after we see how
  the exclusion-clause interaction plays out in the no-source proof.

### Theorem 4 — `marginalize_isAcyclic`

- Contrapositive: suppose `(G.marginalize W).IsAcyclic` fails. Then
  there is `v ∈ G.marginalize W` and a non-trivial directed walk
  `π' : Walk (G.marginalize W) v v` with `1 ≤ π'.length`.
- Apply `Walk.fromMarginalize` to `π'` to get a directed walk
  `π : Walk G v v` with `π.length ≥ π'.length ≥ 1` (each shortcut
  expands to a walk of length ≥ 1; their lengths add).
- `v ∈ G.marginalize W` ⇒ `v ∈ G.J ∪ (G.V \ W) ⊆ G.J ∪ G.V = G`.
- This contradicts `G.IsAcyclic`. ∎
- *No claim_3_2 dependency.* Direct walk-concatenation argument.

### Theorem 5 — `marginalize_isTopologicalOrder`

- Restated hypotheses with `r : α → α → Prop` and
  `hr : G.IsTopologicalOrder r`. Goal:
  `(G.marginalize W).IsTopologicalOrder r` (same relation, restricted
  to the smaller vertex set).
- Discharge the four fields:
    1. **`irrefl`:** `∀ v ∈ G.marginalize W, ¬ r v v`. Every
       `v ∈ G.marginalize W` is in `G` (as in theorem 4), so
       `hr.irrefl v hv_in_G` gives `¬ r v v`.
    2. **`trans`:** analogous — every `v, w, x ∈ G.marginalize W`
       is in `G`, so `hr.trans` discharges it.
    3. **`trichotomous`:** analogous.
    4. **`parent_lt`:** given `v ∈ Pa^{G.marginalize W}(w)`, show
       `r v w`. Unfold `mem_Pa`: `v ∈ G.marginalize W` (⇒ `v ∈ G`)
       and `v ⟶[G.marginalize W] w` (i.e. `(v, w) ∈ E^{\sm W}`).
       Apply `mem_marginalize_E`: there exists a directed walk
       `π : Walk G v w` with `1 ≤ π.length` and interior in `W`.
       Chain the LN's `parent_lt` along each step of `π`: each step
       `u_i → u_{i+1}` gives `u_i ⟶[G] u_{i+1}`, so
       `u_i ∈ Pa^G(u_{i+1})`, so `r u_i u_{i+1}`. Apply `hr.trans`
       repeatedly (with intermediate vertices in `G.V ⊆ G` via
       `G.E_subset`).
       *Care:* the `trans` field requires `v, w, x ∈ G` for each
       composition; the intermediate vertices `u_i ∈ G.V ⊆ G` are
       fine.
- LN's "by just ignoring the nodes from W" is exactly the "same `r`,
  smaller domain" reading.

---

## 4. Subtask ordering for the manager

This is the suggested action sequence for the manager-loop on
claim_3_16. Each line maps to a single worker dispatch unless
noted otherwise.

### Phase A — formalization

1. **`formalize_claim_in_lean`** — single dispatch covering theorems
   1, 2, 4, 5 (and the `Walk.IsBifurcationWithSource` helper) with
   bodies = `sorry`. Punt theorem 3 to a separate sub-step (see
   risk §5.2). Worker input:
   - LN block: `graphs.tex` lines 962 – 974 (the `claimmark`).
   - File to create: `Section3_2/MarginalizationPreserves.lean`.
   - Use the proposed signatures from §1 above as a starting point;
     allow the worker to refine.
2. **`review_design`** — full-LN-context verifier. Question to
   answer: is the five-theorem split natural? does the symmetric ∨
   reading match the LN's "between" semantics? does the
   `IsBifurcationWithSource` helper belong here or in Section3_1?
3. **`verify_equivalence`** — does the Lean statement (cumulatively
   across the five theorems) capture the LN block exactly? In
   particular: are the preconditions `v_i ∈ G ∧ v_i ∉ W` faithful
   to "v_i ∈ G\W"? Does the bifurcation-existential symmetric ∨
   match "between"?
4. **`add_design_choice_comments`** — write design-choice blocks
   above each of the five theorems, citing this workspace where
   relevant.
5. **Commit** the formalized statements (with sorry). Run
   `scaffold/build_and_commit.sh` per `claude.md` workflow.
6. **`new_manager`** handoff to the proof phase. Reason: prove-phase
   prompts and verifier loops are a distinct mental mode; clean
   context.

### Phase B — proof (post-handoff)

7. **`formalize_claim_in_lean`** (or a follow-up) — add theorem 3
   (`marginalize_bifurcation_source_iff`) once the no-source proof
   has surfaced the exclusion-clause issue concretely. Possibly
   reshape its signature if risk §5.2 forces deviation.
8. **`write_tex_proof`** — fill in
   `tex/claim_3_16_proof_MarginalizationPreserves.tex`. The LN
   proof at `graphs.tex:976–993` only covers item 2; the worker
   must construct proofs for items 1 and 3 from scratch following
   the same walk-shrinkage paradigm. *Style guide:* one
   `subsubsection` per LN sub-item; reuse the LN's notation where
   possible.
9. **`verify_tex_proof`** — completeness verifier on the TeX proof.
10. **`prove_claim_in_lean`** — multiple dispatches, one per
    theorem in order (1 → 4 → 5 → 2 → 3). Rationale for ordering:
    - Theorem 1 (`marginalize_anc_iff`) introduces the walk
      translator helpers; do it first so they exist.
    - Theorem 4 (`marginalize_isAcyclic`) reuses the translators
      directly; cheap to do next.
    - Theorem 5 (`marginalize_isTopologicalOrder`) is structurally
      independent of the translators but pattern-matches the
      walk-step-by-step `parent_lt` chaining used elsewhere.
    - Theorem 2 (`marginalize_bifurcation_iff`) is the heaviest
      (bifurcation witness shuffling); do it after the helpers are
      battle-tested.
    - Theorem 3 (`marginalize_bifurcation_source_iff`) reuses
      theorem 2's machinery with extra hinge-bookkeeping.
11. **`simplify_proof`** — full-LN-context simplifier pass on the
    finished Lean proofs. Bifurcation witness manipulation is a
    likely culprit for accidental complexity; look for unused
    case-splits in particular.
12. **`verify_row_solved`** — final gate.
13. **`mark_solved`** in `data.json`.
14. **Subsection cleanup / presentation** — if claim_3_16 is the
    last row of subsection 3.2, the manager should also trigger
    the subsection-presentation step (per `claude.md` §"Tip" —
    currently TODO in the scaffold, so flag for human).

---

## 5. Risks & open questions

These should be resolved (or explicitly punted with documented
rationale) **before** the proof phase commits Lean code.

### 5.1 — `IsBifurcationWithSource` placement

The helper predicate makes most sense in `Section3_1/Bifurcation.lean`
(it's a property of walks-in-`G`, not specific to marginalization).
But scope rule 4 in `claude.md` says workers should not edit other
subsections without manager approval. *Resolution:* manager
explicitly approves adding the helper to `Section3_1/Bifurcation.lean`
*OR* defines it locally in `MarginalizationPreserves.lean` (and
documents the cross-section scope decision in design comments). The
former is cleaner long-term — claim_3_17 / 3_18 / 3_19 will likely
want the same predicate.

### 5.2 — The `L^{\sm W}` exclusion clause and item 2 with source

The exclusion clause in `mem_marginalize_L` removes pairs that are
*also* in `E^{\sm W}` (in either direction). This is the
Lean-encoding deviation from the LN's literal `L^{\sm W}` (see the
~80-line design-choice block in `Marginalization.lean`).

For item 2 *no source*, the symmetric ∨ reading absorbs the
exclusion: a bidir hinge in `G` that gets absorbed by `E^{\sm W}`
in the marginalize encoding still gives a `.backward`-hinge
bifurcation in `G^{\sm W}` *in the opposite walk direction*, which
the ∨ admits.

For item 2 *with source*, the picture is murkier: the original LN
bifurcation in `G` may have *no source* (bidir hinge), but the
exclusion-case `G^{\sm W}` bifurcation has a `.backward` hinge,
i.e. has a source. The biconditional "with source `v_3`" then
relates a no-source bifurcation in `G` to a with-source-`v_3`
bifurcation in `G^{\sm W}`, which is **not** what
`IsBifurcationWithSource v_3` reads as on both sides.

*Resolution candidates:*
- **(R1)** State theorem 3 with stronger hypotheses on `v_1, v_2,
  v_3` that rule out the exclusion case (e.g. require no directed
  walk through `W` between any pair).
- **(R2)** Drop theorem 3 from the row's scope and document the
  deviation in `Marginalization.lean`'s design block (the
  bifurcation symmetric-reading note already gestures at this).
- **(R3)** Replace "source v_3" with a weaker `Set α`-valued
  "source-or-hinge-endpoint" reading.
- **Recommendation:** attempt theorem 3 in the proof phase with
  (R1); if the strengthened hypothesis turns out to be vacuous
  for downstream calls, fall back to (R2) and document.

### 5.3 — Direction of the `Walk.toMarginalize` translator

Theorem 2's `(→)` direction needs to translate *backward* arms of a
bifurcation, not just *forward* directed walks. The LN's symmetry
"a reversed `\hut ⋯ \hut` chain is a `\tuh ⋯ \tuh` chain" suggests
proving a single forward-direction translator and applying it to
arm-reversals via `Walk.reverse`. *Resolution:* the formalizer
should write `Walk.toMarginalize` for forward-directed walks, and
phrase the backward-arm uses via `Walk.reverse` + `IsDirected ↔
IsAllBackward.reverse` (the latter equivalence is *not* proven in
`Bifurcation.lean` — see that file's design block — so the proof
phase may need to add it). Document this dependency early.

### 5.4 — Vertex membership precondition shapes

The LN writes `v_1, v_2 ∈ G` with `v_1, v_2 ∉ W`. This is
*subtly different* from `v_1, v_2 ∈ G.marginalize W` (the latter is
`G.J ∪ (G.V \ W)`, which can include `v ∈ G.J ∩ W`; the former
excludes such `v`). With our no-precondition design on
`G.marginalize`, the user *can* pass a `W` that overlaps `G.J`. The
formalizer should follow the LN literally: precondition is
`v_i ∈ G ∧ v_i ∉ W`. (For item 1, the implicit `v_1 ∈ G` is already
in the `Anc` definition's `w ∈ G` clause and need not be repeated.)

### 5.5 — Scope of `Walk.toMarginalize` and `Walk.fromMarginalize`

These translators are the workhorse of the row. They should be
defined **inside** `MarginalizationPreserves.lean` (private to the
file) unless a downstream row (claim_3_17 / 3_18 / 3_19) clearly
needs them — in which case they can be promoted to `public` or
moved to `Marginalization.lean`. *Recommendation:* keep them
private to start; promote later if needed. Mirrors the pattern in
`BifurcationAlternative.lean` (which has `private` walk helpers
`support_ne_nil`, `support_append`, `support_head`,
`support_getLast`, `append_assoc`, etc.).

### 5.6 — `lake build` discipline

Per `claude.md`, run `scaffold/build_and_commit.sh` from the repo
root after each meaningful step. The proof phase will likely have
3 – 5 commits (one per theorem proven, plus one for the
TeX proof). Keep them small and focused.

---

## 6. Quick reference — relevant existing decls

For the formalizer / prover workers, here are the chief APIs they
will call:

- `Walk.InteriorIn W` (in `Section3_2/Marginalization.lean:159`):
  `∀ x ∈ π.support.tail.dropLast, x ∈ W`. The "all intermediate
  vertices in W" predicate.
- `CDMG.marginalize` (`Marginalization.lean:517`): the
  marginalization itself; pulled in by `@[simp]` lemmas below.
- `CDMG.marginalize_J`, `CDMG.marginalize_V` (`Marginalization.lean:556,
  562`): `Iff.rfl`-equational projections.
- `CDMG.mem_marginalize_E` (`Marginalization.lean:575`): the
  directed-edge characterisation — `(u, v) ∈ E^{\sm W}` iff source
  in `G.J ∪ (G.V \ W)`, target in `G.V \ W`, and ∃ directed walk
  `u → v` in `G` of length ≥ 1 with interior in `W`.
- `CDMG.mem_marginalize_L` (`Marginalization.lean:597`): the
  bidirected-edge characterisation, with the exclusion clause and
  the symmetric ∨ on bifurcation existence.
- `CDMG.Anc` (`Section3_1/FamilyReachability.lean:119`):
  `{w | w ∈ G ∧ ∃ π : Walk G w v, π.IsDirected}`.
- `CDMG.IsAcyclic` (`Section3_1/Acyclicity.lean:182`):
  `∀ v ∈ G, ¬ ∃ π : Walk G v v, π.IsDirected ∧ 1 ≤ π.length`.
- `CDMG.IsTopologicalOrder` (`Section3_1/TopologicalOrder.lean:178`):
  4-field structure (`irrefl`, `trans`, `trichotomous`, `parent_lt`).
- `Walk.IsBifurcation` (`Section3_1/Bifurcation.lean:309`):
  `v ≠ w ∧ v ∉ π.support.tail ∧ w ∉ π.support.dropLast ∧
   Nonempty (BifurcationWitness π)`.
- `Walk.BifurcationWitness` (`Section3_1/Bifurcation.lean:246`):
  fields `m, m'`, `leftArm` (all-backward), `hinge` (with
  arrowhead-at-source), `rightArm` (all-forward), plus
  `decompose` / `leftBackward` / `hingeIntoSource` / `rightDirected`.
- `Walk.bifurcationSource` (`Section3_1/Bifurcation.lean:362`):
  `noncomputable`; returns `some bw.m'` if backward hinge, `none`
  if bidir hinge. *Not directly usable* for theorem 3's
  source-equality reasoning (Classical.choice issue) — go via
  the witness predicate.
- `BifurcationAlternative.lean` (`Section3_2/`): contains private
  walk helpers (`support_append`, `append_assoc`, `support_head`,
  `support_getLast`, `support_ne_nil`) that the proof phase will
  almost certainly need; copy / adapt them.

---

## 7. Log of decisions & punts (running notes)

*(Future managers: append your decisions / punts here as the row
progresses, so a third manager picking this up can reconstruct the
chain of reasoning.)*

- 2026-05-21: plan_subtasks worker drafted §§ 1 – 6 of this file.
  Theorem 3 (with-source) flagged as deferrable per risk §5.2.
  `Walk.IsBifurcationWithSource` helper placement deferred to the
  formalizer / manager (risk §5.1).
