# Workspace for claim_3_25 — ISigmaSeparation

The LN row is **Lem ($i\sigma$-separation under marginalization)**,
`graphs.tex` lines 1414 -- 1577. Statement:

> Let $G=(J,V,E,L)$ be a CDMG, $A,B,C \subseteq J \cup V$ and
> $D \subseteq V$ with $D \cap (A \cup B \cup C) = \emptyset$. Then
> $A \isPerp_G B \given C \iff A \isPerp_{G^{\sm D}} B \given C$.

Title clash note: `ISigmaSeparation.lean` is already occupied by def_3_18.
The Lean file for this claim should be **`ISigmaSeparationMarginalization.lean`**.

## Existing dependencies (already in repo)
- `CDMG.IsISigmaSeparated` -- `Section3_3/ISigmaSeparation.lean` (def_3_18, clause 1)
- `CDMG.marginalize` -- `Section3_2/Marginalization.lean` (def_3_14)
- `CDMG.marginalize_marginalize` / `marginalize_comm` -- `Section3_2/MarginalizationsCommute.lean` (claim_3_17, the lemma the LN proof inducts through)
- `CDMG.marginalize_anc_iff` / `marginalize_bifurcation_iff` -- `Section3_2/MarginalizationPreserves.lean` (claim_3_16, used as `eq:anc_preserved` / `eq:sc_preserved`)
- `sigmaOpens_TFAE` -- `Section3_3/SigmaOpenPathWalk.lean` (claim_3_23, the LN proof's "Proposition 3.23(3)" appeal)
- `isISigmaSeparated_TFAE` / `isNotISigmaSeparated_TFAE` -- `Section3_3/SigmaSeparationEquivalences.lean` (claim_3_24, the σ-open walk rewriting of `¬IsISigmaSeparated`)

## Plan

### Manager A (this manager) -- statement
1. **Formalize the Lean statement** with `sorry` in `ISigmaSeparationMarginalization.lean`.
   Target shape:
   ```lean
   theorem isISigmaSeparated_marginalize_iff (G : CDMG α)
       {A B C D : Set α} (hDV : D ⊆ G.V)
       (hDdisj : Disjoint D (A ∪ B ∪ C)) :
       G.IsISigmaSeparated A B C ↔ (G.marginalize D).IsISigmaSeparated A B C
   ```
2. `review_design` -- full-LN-context check that the shape is natural for chapters $\ge 4$.
3. `verify_equivalence` -- focused check against the LN block.
4. `add_design_choice_comments` -- write the *why* into the comment above the declaration.
5. `new_manager` -- handoff to Manager B for the proof.

### Manager B -- TeX + Lean proof
6. `write_tex_proof` -- copy the LN's `\Claude{...}` proof (lines 1424--1579 already wrap a complete proof) verbatim into the proof subfile.
7. `verify_tex_proof`.
8. `prove_claim_in_lean` -- heavy. Strategy follows the LN:
   * Reduce to `|D| = 1` by `marginalize_comm` + induction on a `Finset` enumeration of `D`.
   * Each direction proven contrapositively via `isNotISigmaSeparated_TFAE` (extract a $\sigma$-open walk, then construct one on the other side).
   * (⇒): lift an open walk in $G^{\sm u}$ to an open walk in $G$ by expanding edges through $u$.
   * (⇐): contract a run of $u$'s in an open walk in $G$ to a single edge in $G^{\sm u}$; possibly modify when an unblockable non-collider's outgoing edge was via $u$.
   * Uses `marginalize_anc_iff`, the SCC characterisation `Sc = Anc ∩ Desc`, and case-split on collider type.
9. `simplify_proof`.
10. `solved`.

## Running log
- Manager A turn 1 (2026-05-27): plan written; dispatching formalizer for the statement.
- Manager A turn 2 (2026-05-27): formalizer wrote `isISigmaSeparated_marginalize_iff` in `ISigmaSeparationMarginalization.lean` with `sorry`. Signature `(G : CDMG α) (A B C D : Set α) (hDV : D ⊆ G.V) (hDdisj : Disjoint D (A ∪ B ∪ C)) : G.IsISigmaSeparated A B C ↔ (G.marginalize D).IsISigmaSeparated A B C`. `lake build` clean modulo the expected `sorry`. Dispatching `review_design`.
- Manager A turn 3 (2026-05-27): `review_design` **PASS** — predicate-level `Iff` is the right surface for downstream chapter-5+ consumers; explicit `(A B C D)` binders, `Disjoint`, `hDV : D ⊆ G.V` and the deliberate omission of `A ∪ B ∪ C ⊆ G.J ∪ G.V` all match section-3.3 precedent. Dispatching `verify_equivalence`.
- Manager A turn 4 (2026-05-27): `verify_equivalence` **PASS** — every LN clause matched to the Lean signature; the `A,B,C ⊆ J ∪ V` LN preamble is convention (mirrors `IsISigmaSeparated`'s own definition), not type-level. Dispatching `add_design_choice_comments`.
- Manager A turn 5 (2026-05-27): `add_design_choice_comments` complete — rich `## Design choice` block now sits above the theorem, covering predicate-level statement choice, explicit binders, `Disjoint` vs `∩ = ∅`, the `hDV` / `A,B,C` hypothesis decisions, `Iff` vs two `→`s, naming, `G`-first signature, minimal imports, mathlib re-use, and `## Constraints / known limitations` block. Time to hand off to Manager B for TeX + Lean proof.

## Handoff to Manager B (2026-05-27)
Statement phase is **complete** — all five required steps (formalize, review_design, verify_equivalence, add_design_choice_comments) passed. The handoff payload is below in the `new_manager` action body.

## Manager B running log
- **Manager B turn 1 (2026-05-27):** picked up the row. Re-read `claude.md`, the LN's full `\Claude{...}` proof at `graphs.tex` lines 1424--1579, the workspace, the Lean statement file, and Manager A's design block. Dispatching `write_tex_proof` worker with the explicit instruction to lift the LN's `\Claude{...}` proof body verbatim into the stub (it is a complete, mathematician-grade proof — no construction from scratch needed).
- **Manager B turn 2 (2026-05-27):** `write_tex_proof` complete — lifted verbatim from `graphs.tex:1425--1578`; only the `% TODO: write the proof body.` line was replaced. Braces / dollars balanced; lineage comment prepended; inline `\ref{...}` → row-ref mappings noted (`marginalizations-commute` → claim_3_17, `rem:marg_preserves_ancestors_bifurcations_acyclicity` → claim_3_16, `prp:sigma_opens(3)` → claim_3_23). Dispatching `verify_tex_proof`.
- **Manager B turn 3 (2026-05-27):** `verify_tex_proof` **PASS** — verifier confirmed statement match, provenance lineage, and all three external citations resolve correctly to the existing Lean lemmas in Section 3.2 and Section 3.3 (`MarginalizationsCommute.marginalize_marginalize` / `marginalize_comm`; `MarginalizationPreserves.marginalize_anc_iff` / `marginalize_bifurcation_iff`; `SigmaOpenPathWalk.sigmaOpens_TFAE`). All `\Sc`, `\Anc`, `\Desc` notation usages are LN-standard. Proceeding to `prove_claim_in_lean` (the heavy step). Note for future runs: the LN proof has two "longer runs through self-loops are handled analogously" hand-waves (one in the ⇒ footnote on bifurcations through `u` self-loops, one in the ⇐ direction's contraction case-split). The leanifier should flag if either of these blocks the Lean proof — at which point we `expand_proof` on the offending step.

## Leanification diagnostic — 2026-05-27

Authored by leanification session 8886611a after `prove_claim_in_lean` stalled
on the `sorry` body of `isISigmaSeparated_marginalize_iff` (lines 442--447 of
`ISigmaSeparationMarginalization.lean`). The Lean file is untouched (single
`by sorry`, `lake build` clean modulo the expected `sorry` warning).

### A. Summary

The proof stalls on the **systematic absence of public Lean primitives for per-edge expansion and per-vertex contraction of σ-open walks across a marginalization**: the LN's two-and-a-half-page proof reads as a walk-rewriting calculus, but the Lean walk API (in `Section3_1/Walks.lean` and the σ-open layer in `Section3_3/SigmaBlockedWalks.lean`) only supports prepend / append / reverse, with no contract / interior-splice combinators, and the relevant interior-tracking translators between `G` and `G.marginalize W` exist as `private` lemmas in `Section3_2/MarginalizationsCommute.lean` rather than as a publicly callable layer. Two LN hand-waves on `u`-self-loops are load-bearing because `CDMG` admits directed self-loops on `V`-nodes (only `L_irrefl` blocks them, on `L`). Headline recommendation: **(a) Infrastructure-first** — build a new `Section3_3/SigmaOpenWalkMarginalization.lean` plus three trivial additions to `Section3_2/MarginalizationPreserves.lean` plus a `private`-to-public promotion of six existing lemmas in `Section3_2/MarginalizationsCommute.lean`, then re-dispatch leanification of the main proof.

### B. Blockers, precisely

#### B.1 Blocker A — per-edge expansion / contraction in (⇒) and (⇐) has no public Lean primitive

**TeX citation**: `claim_3_25_proof_ISigmaSeparation.tex` lines 57--70 (the lift table) and 121--138 (the contraction case-table).

The lift table (proof.tex:57--70):

```
Third, every edge in G^{∖u} lifts to a short walk through u in G:
  - A directed edge v → w in G^{∖u} comes from
    v → w or v → u → w in G.
  - A bidirected edge v ↔ w in G^{∖u} comes from
    a bifurcation through u in G, i.e.:
    v ↔ w, or
    v ← u → w (fork), or
    v ↔ u → w (left hinge), or
    v ← u ↔ w (right hinge).
In all bifurcation cases, u appears as a non-collider
(at most one arrowhead towards u).
```

The contraction case-table (proof.tex:131--138):

```
b_j → u → b_{j+1}     ─→  b_j → b_{j+1}  ∈ E^{∖u}    (directed walk)
b_j ← u → b_{j+1}     ─→  b_j ↔ b_{j+1}  ∈ L^{∖u}    (fork bifurcation)
b_j ↔ u → b_{j+1}     ─→  b_j ↔ b_{j+1}  ∈ L^{∖u}    (hinge bifurcation)
```

**Lean subgoal**: structural recursion on `π' : Walk (G.marginalize {u}) v w`. For each `WalkStep`, case on the constructor:

```lean
-- WalkStep.forward case yields, after unfolding mem_marginalize_E
-- (Section3_2/Marginalization.lean:575):
have h_E : ∃ π : Walk G a b, π.IsDirected ∧ π.InteriorIn {u} ∧ 1 ≤ π.length

-- WalkStep.bidir case yields, after unfolding mem_marginalize_L
-- (Section3_2/Marginalization.lean:597):
have h_L : (∃ π : Walk G a b, π.IsBifurcation ∧ π.InteriorIn {u}) ∨
           (∃ π : Walk G b a, π.IsBifurcation ∧ π.InteriorIn {u})
```

The LN's bullet table promises a decomposition of these existentials into four enumerated walk shapes (`v ↔ w`, fork, left hinge, right hinge for the bidir case; length-1 vs length-2 for the forward case). The decomposition is what would let the proof produce a *new* walk in `G` from the existential witness. **No public Lean lemma performs this decomposition.** The structural-recursive walk-translation that would do it exists inside the private `marginalize_bif_backward` proof (`Section3_2/MarginalizationPreserves.lean:948`, ~1500 lines) as embedded reasoning rather than a separately-named lemma callers can pattern-match on.

**Classification**: (i) **missing upstream API lemma** + (iii) **structural mismatch** (the LN argues over walks as if they were lists with a primitive splice / contract operation; the Lean `Walk` type is an inductive whose constructors only prepend a step or concatenate at endpoints).

**Concreteness check**: I read the TeX, looked at the API (Tier-1 and Tier-2 of §C below), and decided the per-step expansion lemma was the load-bearing missing piece. I did not write Lean tactics into the file; I traced through the case-analysis on paper and confirmed that without the missing lemma, even the simplest `WalkStep.forward` case requires re-deriving by-hand what `marginalize_bif_forward`'s private proof already does.

#### B.2 Blocker B — two "handled analogously" LN hand-waves on self-loops are load-bearing because `CDMG` admits directed self-loops on `V`-nodes

**TeX citations**: `claim_3_25_proof_ISigmaSeparation.tex:66` and `claim_3_25_proof_ISigmaSeparation.tex:129--130`.

Hand-wave 1 (footnote in (⇒), proof.tex:66):

```
We exclude longer bifurcations through repeated self-loop
traversals of u for simplicity; they can be handled analogously.
```

Hand-wave 2 (parenthetical in (⇐), proof.tex:129--130):

```
Otherwise, the possible local patterns (for a single intermediate u;
longer runs through self-loops are handled analogously) are, ...
```

**Why this is load-bearing in Lean**: the `CDMG` structure (`Section3_1/CDMG.lean:119--141`) has

```lean
E_subset : E ⊆ (J ∪ V) ×ˢ V                                   -- line 129
L_irrefl : ∀ ⦃v₁ v₂ : α⦄, (v₁, v₂) ∈ L → v₁ ≠ v₂                -- line 137
```

There is **no `E_irrefl` field**. So `(u, u) ∈ G.E` is permitted for any `u ∈ G.V`. The walks

```
b_j → u → u → … → u → b_{j+1}      (n interior u's, all forward via the self-loop)
```

are legitimate `Walk G b_j b_{j+1}` values with interior in `{u}`. They witness `(b_j, b_{j+1}) ∈ (G.marginalize {u}).E` exactly the way the length-2 case does, but the LN's contraction case-table only treats `n = 1`. The LN's "handled analogously" provides no Lean-level recipe for which contracted edge type to emit when `n ≥ 2`, nor for which σ-open conditions to verify on the interior `u`-tower.

**Lean subgoal that's hand-waved** (in the (⇐) contraction direction): given `π : Walk G v w` σ-open with colliders in `C`, and a sub-walk `b_j ─[u-tower of length n+1]─ b_{j+1}` with all internal vertices = `u`, construct the contracted edge in `(G.marginalize {u}).E ∪ (G.marginalize {u}).L`. For `n ≥ 1` (i.e., towers of length ≥ 2), no recipe is provided. The internal `u`-positions in such a tower can also have collider patterns (e.g., `... → u ← u → u → ...` if both `(prev, u) ∈ G.E` and `(u_left, u_right) ∈ G.E` arrange the arrowheads adversarially) — these are σ-open only if the colliding `u`-positions land in `Anc^G(C)`, which doesn't transfer automatically to `(G.marginalize {u}).AncSet C`.

**Classification**: (ii) **TeX hand-wave that needs `expand_proof`** — but only after the rest of the infrastructure is in place, otherwise an `expand_proof` worker has nowhere to land its Lean tactics.

**Concreteness check**: I traced the contraction proof by hand on a `b_j → u → u → b_{j+1}` example (all forward arrows, the simplest self-loop tower). The contracted edge should be `(b_j, b_{j+1}) ∈ E^{\sm u}` via the length-3 directed-walk witness; this part works. The σ-openness verification at the *internal* `u`-position with two forward arrows on either side gives a non-collider, fine. But if instead the tower is `b_j ↔ u → u → b_{j+1}` (left hinge with a self-loop interior), the LN's table has no case — the interior `u → u` arrow is forward, but the contracted edge in `L^{\sm u}` (hinge bifurcation) needs an arrowhead pattern at `b_j` and `b_{j+1}` that's not obviously consistent with the LN's "hinge" pattern when the run length increases. **I could not satisfy myself that "handled analogously" is true** without spelling out the case-by-case for `n = 2, 3` explicitly.

#### B.3 Blocker C — outer reduction over `D : Set α` is non-obvious because `D` may be infinite

**TeX citation**: `claim_3_25_proof_ISigmaSeparation.tex:38--39`:

```
By Lemma \ref{marginalizations-commute} and induction on #D, it
suffices to prove the case D = {u} for a single node u ∈ V ∖ (A ∪ B ∪ C).
```

**Why this isn't a one-liner**: the Lean statement (`ISigmaSeparationMarginalization.lean:442--447`) takes `D : Set α` with no finiteness hypothesis:

```lean
theorem isISigmaSeparated_marginalize_iff (G : CDMG α)
    (A B C D : Set α) (hDV : D ⊆ G.V)
    (hDdisj : Disjoint D (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C ↔
      (G.marginalize D).IsISigmaSeparated A B C := by
  sorry
```

The LN's "induction on `#D`" requires `D` finite. For the iff to hold for arbitrary `D` (which it should — `G.V` itself is `Set α`-not-`Finset`, and `G.marginalize` is defined for all `W : Set α` per the `Marginalization.lean:258--286` design block), we need one of:

- **(C.i)** Add `(hDfin : D.Finite)` to the statement signature. **Cheap, but conflicts with the already-`PASS`'d `verify_equivalence` round** which endorsed the no-finiteness signature.
- **(C.ii)** Prove an auxiliary "iff transports from every finite subset of `D` to `D` itself" lemma, then apply (C.i)-style induction inside it. Needs the observation that every `Walk` is finite and hence uses only finitely many `D`-nodes locally.
- **(C.iii)** Skip outer reduction; absorb general `D` into the inner helpers. **Multiplies the inner-case work** — instead of `D = {u}`, we work with "any single edge of `G.marginalize D` is witnessed by an interior-in-`D` walk in `G` of arbitrary length and arbitrary structure", which makes Blocker B fundamentally worse.

The workspace plan (lines 42--46 of this file) explicitly settled on the LN's (C.i)-style reduction, but the Lean statement doesn't include the finiteness hypothesis, so the chosen plan doesn't actually apply.

**Classification**: (iv) **strategy / statement mismatch** — the statement and the chosen proof skeleton are inconsistent on whether `D` is finite.

**Concreteness check**: I drafted the outer skeleton on paper:

```
induction (D.toFinset) using Finset.induction with
  | empty => -- need G.marginalize ∅ = G or equivalent iff
  | insert u F hu_notin ih =>
      rw [show (insert u F : Set α) = F ∪ {u} from ...]
      rw [marginalize_marginalize G h_disj_F_u]
      rw [ih]  -- reduce to G.marginalize F problem
      apply isISigmaSeparated_marginalize_singleton_iff
```

— but the `D.toFinset` only exists if `D.Finite`. Without finiteness, this skeleton doesn't compile.

### C. API survey — what already exists upstream

#### C.1 Public marginalize / σ-open / TFAE surface

```
Section3_1/CDMG.lean
  :119  structure CDMG (α : Type*) where ...
        -- E_subset, L_subset, L_irrefl, L_symm, disjoint_JV, disjoint_EL
        -- NB: no E_irrefl → directed self-loops on V-nodes ARE permitted

Section3_1/Walks.lean
  :134  inductive WalkStep (G : CDMG α) : α → α → Type _ where
          | forward  {v w} (h : v ⟶[G] w)
          | backward {v w} (h : v ⟵[G] w)
          | bidir    {v w} (h : v ⟷[G] w)
  :213  inductive Walk (G : CDMG α) : α → α → Type _ where
          | nil (v : α) : Walk G v v
          | cons {v w u} (s : WalkStep G v w) (p : Walk G w u) : Walk G v u
  :259  def WalkStep.reverse  -- forward ↔ backward, bidir conjugates
  :299  def length            -- recursive
  :323  def support           -- recursive, List α
  :452  def append            -- concatenate at shared vertex
  :508  def reverse           -- reverse a walk
  -- NO contract / interior-splice / insert-at-position combinators

Section3_2/Marginalization.lean
  :167  def Walk.InteriorIn {v w : α} (π : Walk G v w) (W : Set α) : Prop :=
          ∀ x ∈ π.support.tail.dropLast, x ∈ W
  :517  def CDMG.marginalize (G : CDMG α) (W : Set α) : CDMG α  -- def_3_14
  :556  @[simp] theorem marginalize_J : (G.marginalize W).J = G.J
  :562  @[simp] theorem marginalize_V : (G.marginalize W).V = G.V \ W
  :575  @[simp] theorem mem_marginalize_E ...
          -- (u, v) ∈ (G.marginalize W).E ↔
          --   u ∈ G.J ∪ (G.V\W) ∧ v ∈ G.V\W ∧
          --   ∃ π : Walk G u v, π.IsDirected ∧ π.InteriorIn W ∧ 1 ≤ π.length
  :597  @[simp] theorem mem_marginalize_L ...
          -- (u, v) ∈ (G.marginalize W).L ↔
          --   u ∈ G.V\W ∧ v ∈ G.V\W ∧ u ≠ v ∧
          --   (¬ ∃ directed walk u → v with interior in W) ∧
          --   (¬ ∃ directed walk v → u with interior in W) ∧
          --   ((∃ π : Walk G u v, π.IsBifurcation ∧ π.InteriorIn W) ∨
          --    (∃ π : Walk G v u, π.IsBifurcation ∧ π.InteriorIn W))

Section3_2/MarginalizationsCommute.lean
  :904  theorem marginalize_marginalize (h : Disjoint W₁ W₂) :
          (G.marginalize W₁).marginalize W₂ = G.marginalize (W₁ ∪ W₂)
  :1034 theorem marginalize_comm (h : Disjoint W₁ W₂) :
          (G.marginalize W₁).marginalize W₂ = (G.marginalize W₂).marginalize W₁

Section3_2/MarginalizationPreserves.lean
  :409  lemma exists_marg_directed_of_directed (W : Set α) :
          ∀ {u v} (π : Walk G u v), π.IsDirected → u ∉ W → v ∉ W →
          ∃ π' : Walk (G.marginalize W) u v, π'.IsDirected ∧ <support tracking>
  :569  lemma exists_directed_of_marg_directed (W : Set α) :
          ∀ {u v} (π' : Walk (G.marginalize W) u v), π'.IsDirected →
          ∃ ρ : Walk G u v, ρ.IsDirected ∧ <length + support tracking>
  :948  lemma marginalize_bif_backward (hu : u ∉ W) (hv : v ∉ W)
          (π' : Walk (G.marginalize W) u v) (hb' : π'.IsBifurcation) :
          (∃ π : Walk G u v, π.IsBifurcation ∧ <support tracking>) ∨
          (∃ π : Walk G v u, π.IsBifurcation ∧ <support tracking>)
  :2515 lemma marginalize_bif_forward  -- dual of marginalize_bif_backward
  :3550 theorem marginalize_anc_iff (h₁ : v₁ ∉ W) (h₂ : v₂ ∉ W) :
          v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W).Anc v₂
  :3694 theorem marginalize_bifurcation_iff (h₁v : v₁ ∈ G) (h₂v : v₂ ∈ G)
          (h₁W : v₁ ∉ W) (h₂W : v₂ ∉ W) :
          ((∃ π : Walk G v₁ v₂, π.IsBifurcation) ∨
           (∃ π : Walk G v₂ v₁, π.IsBifurcation)) ↔
          ((∃ π : Walk (G.marginalize W) v₁ v₂, π.IsBifurcation) ∨
           (∃ π : Walk (G.marginalize W) v₂ v₁, π.IsBifurcation))
  :3817 theorem marginalize_isAcyclic
  :3917 theorem marginalize_isTopologicalOrder

Section3_3/SigmaBlockedWalks.lean
  :258  def Walk.nodeAt (π : Walk G v w) (k : ℕ) : α  -- vertex at position k
  :277  theorem nodeAt_zero : π.nodeAt 0 = v
  :285  theorem nodeAt_length : π.nodeAt π.length = w
  :426  def Walk.IsSigmaOpen (π : Walk G v w) (C : Set α) : Prop :=
          (∀ k, π.IsColliderAt k → π.nodeAt k ∈ G.AncSet C) ∧
          (∀ k, π.IsBlockableNonColliderAt k → π.nodeAt k ∉ C)
  :534  def Walk.IsSigmaBlocked : ...   -- existential dual
  :597  theorem isSigmaBlocked_iff_not_isSigmaOpen : ...   -- classical De-Morgan

Section3_3/ISigmaSeparation.lean
  :351  def CDMG.IsISigmaSeparated (G : CDMG α) (A B C : Set α) : Prop :=
          ∀ ⦃v w : α⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w), π.IsSigmaBlocked C
  :486  def CDMG.IsNotISigmaSeparated G A B C : Prop := ¬ G.IsISigmaSeparated A B C

Section3_3/SigmaSeparationEquivalences.lean
  :371  theorem isISigmaSeparated_TFAE :
          List.TFAE [predicate, walk-universal, path-universal]
  :606  theorem isNotISigmaSeparated_TFAE :
          List.TFAE
            [ IsNotISigmaSeparated
            , ∃ v w π, v ∈ A ∧ w ∈ G.J ∪ B ∧ π.IsPath ∧ π.IsSigmaOpen C
            , ∃ v w π, v ∈ A ∧ w ∈ G.J ∪ B ∧ π.IsSigmaOpen C ∧
                        ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C ]

Section3_3/SigmaOpenPathWalk.lean
  :1453 theorem sigmaOpens_TFAE (G C w₁ w₂) :
          List.TFAE
            [ ∃ π : Walk G w₁ w₂, π.IsPath ∧ π.IsSigmaOpen C
            , ∃ π : Walk G w₁ w₂, π.IsSigmaOpen C
            , ∃ π : Walk G w₁ w₂, π.IsSigmaOpen C ∧
                ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C ]
```

#### C.2 Private interior-tracking walk translators

These are the load-bearing helpers I'd need for the inner case-split and they are all `private` to `Section3_2/MarginalizationsCommute.lean`:

```
:121  private lemma lift_directed_walk (W₁ W₂ : Set α) :
        Walk (G.marginalize W₁) a b → IsDirected → InteriorIn W₂ →
        ∃ ρ : Walk G a b, IsDirected ∧ InteriorIn (W₁ ∪ W₂) ∧ length-bound
:278  private lemma shrink_directed_walk (W₁ : Set α) : <dual of lift_directed_walk>
:479  private lemma directed_walk_iff
:519  private lemma directed_walk_iff_no_length
:586  private lemma lift_bifurcation_walk (W₁ W₂ hd) :
        Walk (G.marginalize W₁) a b → IsBifurcation → InteriorIn W₂ →
        (∃ σ : Walk G a b, IsBifurcation ∧ InteriorIn (W₁ ∪ W₂)) ∨
        (∃ σ : Walk G b a, IsBifurcation ∧ InteriorIn (W₁ ∪ W₂))
:686  private lemma shrink_bifurcation_walk  -- dual of lift_bifurcation_walk
:784  private lemma bifurcation_walk_iff_no_length
```

The naming convention `lift_*` / `shrink_*` is the project's existing prefix
for marg ↔ G walk translation with interior tracking. **This is exactly the
tier we need for claim_3_25, but it is closed off from `Section3_3`.**

#### C.3 What's NOT in the API

| Concept | Status |
|---|---|
| `Walk.contract_at` (drop interior vertex) | Missing |
| `Walk.insert_at` (insert vertex with two edges) | Missing |
| σ-open walk preservation across walk transformation | Missing entirely |
| `marginalize_Sc_iff` (LN's `eq:sc_preserved`) | Missing (derivable from `marginalize_anc_iff` + `Sc = Anc ∩ Desc`) |
| `marginalize_AncSet_iff` (LN's `eq:anc_preserved` lifted to sets) | Missing |
| `marginalize_desc_iff` (`Desc`-symmetric of `marginalize_anc_iff`) | Missing |
| Public per-step decomposition of single-vertex marg edges | Missing |
| Tier-2 (interior-tracking) walk translators visibility | Private (Blocker A) |

### D. Proposed new helpers (precise statements)

Listed in dependency order, smallest-first.

#### D.1 Cheap upstream additions in `Section3_2/MarginalizationPreserves.lean`

Discharges LN steps in proof.tex:43--56 (`eq:anc_preserved`, `eq:sc_preserved`) at the *set-level* (which the LN actually uses) rather than the singleton level.

```lean
theorem marginalize_desc_iff (G : CDMG α) (W : Set α) {v₁ v₂ : α}
    (h₁ : v₁ ∉ W) (h₂ : v₂ ∉ W) :
    v₁ ∈ G.Desc v₂ ↔ v₁ ∈ (G.marginalize W).Desc v₂

theorem marginalize_Sc_iff (G : CDMG α) (W : Set α) {v : α}
    (hv : v ∈ G) (hvW : v ∉ W) :
    (G.marginalize W).Sc v = G.Sc v \ W

theorem marginalize_AncSet_subset (G : CDMG α) (W : Set α) (C : Set α) :
    (G.marginalize W).AncSet C ⊆ G.AncSet C

theorem marginalize_AncSet_eq_on_complement (G : CDMG α) (W : Set α) (C : Set α)
    (hCW : Disjoint C W) :
    (G.marginalize W).AncSet C = G.AncSet C \ W
```

Proof obligations: each is a one-step composition of `marginalize_anc_iff` (already proven, `MarginalizationPreserves.lean:3550`) with the symmetric / set-level wrapper. Total estimated size: **~150 lines**.

#### D.2 Visibility promotion in `Section3_2/MarginalizationsCommute.lean`

Discharges Blocker A's underlying ingredients. Zero new Lean code; remove the `private` keyword on the six declarations at lines 121, 278, 479, 519, 586, 686, 784:

```lean
-- Was: private lemma lift_directed_walk ...
   lemma lift_directed_walk (G : CDMG α) (W₁ W₂ : Set α) :
     ∀ {a b : α} (π : Walk (G.marginalize W₁) a b),
       π.IsDirected → π.InteriorIn W₂ →
       ∃ ρ : Walk G a b, ρ.IsDirected ∧ ρ.InteriorIn (W₁ ∪ W₂) ∧
         π.length ≤ ρ.length

   lemma shrink_directed_walk (G : CDMG α) (W₁ : Set α) :
     ∀ (n : ℕ) {a b : α} (σ : Walk G a b), σ.length ≤ n →
       σ.IsDirected → a ∈ G.J ∪ (G.V \ W₁) → b ∉ W₁ →
       ∃ π : Walk (G.marginalize W₁) a b, π.IsDirected ∧
         (∀ x ∈ π.support.tail.dropLast, x ∈ σ.support.tail.dropLast) ∧
         π.length ≤ σ.length ∧
         (1 ≤ σ.length → 1 ≤ π.length)

   lemma directed_walk_iff_no_length (G : CDMG α) (W₁ W₂ : Set α)
       {a b : α} (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
       (hab : a ≠ b) :
     (∃ π : Walk (G.marginalize W₁) a b, π.IsDirected ∧ π.InteriorIn W₂)
     ↔ (∃ σ : Walk G a b, σ.IsDirected ∧ σ.InteriorIn (W₁ ∪ W₂))

   lemma lift_bifurcation_walk (G : CDMG α) (W₁ W₂ : Set α)
       (_hd : Disjoint W₁ W₂)
       {a b : α} (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
       (π : Walk (G.marginalize W₁) a b)
       (hb_π : π.IsBifurcation) (hint_π : π.InteriorIn W₂) :
     (∃ σ : Walk G a b, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂)) ∨
     (∃ σ : Walk G b a, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂))

   lemma shrink_bifurcation_walk (G : CDMG α) (W₁ W₂ : Set α)
       (_hd : Disjoint W₁ W₂)
       {a b : α} (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
       (σ : Walk G a b)
       (hb_σ : σ.IsBifurcation) (hint_σ : σ.InteriorIn (W₁ ∪ W₂)) :
     (∃ π : Walk (G.marginalize W₁) a b,
        π.IsBifurcation ∧ π.InteriorIn W₂) ∨
     (∃ π : Walk (G.marginalize W₁) b a,
        π.IsBifurcation ∧ π.InteriorIn W₂)

   lemma bifurcation_walk_iff_no_length (G : CDMG α)
       (W₁ W₂ : Set α) (hd : Disjoint W₁ W₂) {a b : α}
       (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
       (hab : a ≠ b) :
     ((∃ π : Walk (G.marginalize W₁) a b, π.IsBifurcation ∧ π.InteriorIn W₂) ∨
      (∃ π : Walk (G.marginalize W₁) b a, π.IsBifurcation ∧ π.InteriorIn W₂))
     ↔
     ((∃ σ : Walk G a b, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂)) ∨
      (∃ σ : Walk G b a, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂)))
```

Proof obligations: none — proofs already exist. Estimated size: **0 lines of new Lean**, plus a module-docstring entry (~20 lines) calling out the public surface. The promotion needs manager sign-off because it crosses subsection scope.

#### D.3 New helper file `Section3_3/SigmaOpenWalkMarginalization.lean`

Discharges Blocker A (per-edge expansion / contraction) and Blocker B's mathematical content (modulo the self-loop hand-wave being resolved via `expand_proof` or vacuously closed by a separate side-argument). Sits between `Section3_3/SigmaSeparationEquivalences.lean` and `Section3_3/ISigmaSeparationMarginalization.lean` in the dependency order.

```lean
-- The single-vertex case of the lift direction (LN proof.tex:71--105):

theorem lift_sigmaOpen_walk_through_single_vertex
    (G : CDMG α) {u : α} (huV : u ∈ G.V) (C : Set α) (huC : u ∉ C)
    {v w : α} (hvu : v ≠ u) (hwu : w ≠ u)
    (π' : Walk (G.marginalize {u}) v w)
    (hOpen' : π'.IsSigmaOpen C)
    (hCol' : ∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C) :
    ∃ ρ : Walk G v w, ρ.IsSigmaOpen C ∧
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ C)

-- The single-vertex case of the contract direction (LN proof.tex:106--190):

theorem contract_sigmaOpen_walk_at_single_vertex
    (G : CDMG α) {u : α} (huV : u ∈ G.V) (C : Set α) (huC : u ∉ C)
    {v w : α} (hvu : v ≠ u) (hwu : w ≠ u)
    (huA : u ∉ A) (huB : u ∉ B)
    (π : Walk G v w)
    (hOpen : π.IsSigmaOpen C)
    (hCol : ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) :
    ∃ π' : Walk (G.marginalize {u}) v w, π'.IsSigmaOpen C ∧
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C)

-- Direct single-vertex iff (combines the two above):

theorem isISigmaSeparated_marginalize_singleton_iff
    (G : CDMG α) {u : α} (huV : u ∈ G.V) (A B C : Set α)
    (huA : u ∉ A) (huB : u ∉ B) (huC : u ∉ C) :
    G.IsISigmaSeparated A B C ↔
      (G.marginalize {u}).IsISigmaSeparated A B C
```

Proof obligations: structural recursion on the input walk. For each step / for each maximal `u`-run, use the (now-public) `lift_bifurcation_walk` / `shrink_bifurcation_walk` to translate the underlying walk-segment, plus `marginalize_anc_iff` and `marginalize_Sc_iff` (from D.1) to verify the σ-open clauses. The self-loop hand-wave (Blocker B) bites inside `contract_sigmaOpen_walk_at_single_vertex` specifically; the worker building this file should either prove a "no σ-open walk with colliders in `C` admits a `u`-self-loop tower of length ≥ 2" side-lemma OR escalate via `expand_proof` on proof.tex:129--130.

Estimated size: **~1500--2500 lines** (comparable to claim_3_27 `LabelRoman`).

#### D.4 Outer-reduction wrapper in `Section3_3/ISigmaSeparationMarginalization.lean`

Discharges Blocker C. Two viable shapes; **(D.4.ii) recommended**.

(D.4.ii) Auxiliary lemma:

```lean
theorem isISigmaSeparated_marginalize_iff_of_finite_iff
    (G : CDMG α) (A B C : Set α)
    (h : ∀ (F : Finset α), ↑F ⊆ G.V → Disjoint (↑F : Set α) (A ∪ B ∪ C) →
         G.IsISigmaSeparated A B C ↔ (G.marginalize ↑F).IsISigmaSeparated A B C)
    (D : Set α) (hDV : D ⊆ G.V) (hDdisj : Disjoint D (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C ↔ (G.marginalize D).IsISigmaSeparated A B C
```

Proof obligation: walk-by-walk reduction — every `Walk` is finite, so any
counter-example to either direction uses only finitely many `D`-nodes, and
the iff for that finite subset is enough. Estimated size: **~200--400 lines**.

Plus the actual proof body of `isISigmaSeparated_marginalize_iff` becomes:

```lean
theorem isISigmaSeparated_marginalize_iff ... := by
  apply isISigmaSeparated_marginalize_iff_of_finite_iff
  · intro F hFV hFdisj
    induction F using Finset.induction with
    | empty => simp [marginalize_empty]  -- needs G.marginalize ∅ = G (probably exists)
    | @insert u F' hu_notin ih =>
        have h_disj : Disjoint (↑F' : Set α) ({u} : Set α) := by ...
        rw [show ((insert u F' : Finset α) : Set α) = ↑F' ∪ {u} from ...]
        rw [← marginalize_marginalize G h_disj]
        rw [ih ...]
        exact isISigmaSeparated_marginalize_singleton_iff G ...
  · exact hDV
  · exact hDdisj
```

Estimated size: **~50--80 lines**.

### E. Strategic recommendation

**(a) Infrastructure-first.** Spawn the sub-task workers in this order, each as
a separate `spawn_agent_sub_task` invocation:

1. **Sub-task 1** — small upstream API additions per D.1, in
   `Section3_2/MarginalizationPreserves.lean`. **~150 lines, low risk.**
2. **Sub-task 2** — visibility promotion per D.2, in
   `Section3_2/MarginalizationsCommute.lean`. **~20 lines of docstring
   only, trivial.**
3. **Sub-task 3** — new helper file per D.3,
   `Section3_3/SigmaOpenWalkMarginalization.lean`. **~1500--2500 lines,
   high risk; this is where the self-loop hand-wave (Blocker B) bites and
   may require an embedded `expand_proof` invocation.**
4. **Sub-task 4** — outer-reduction wrapper per D.4 + the original proof body,
   in `Section3_3/ISigmaSeparationMarginalization.lean`. **~300 lines, medium
   risk.**

Sub-task 3 is the bulk of the work and is the one that should be most
carefully scoped. Suggested brief for that worker:

> Build `Section3_3/SigmaOpenWalkMarginalization.lean` with the three theorems
> in D.3 above. Use the now-public `lift_directed_walk`, `shrink_directed_walk`,
> `lift_bifurcation_walk`, `shrink_bifurcation_walk`,
> `directed_walk_iff_no_length`, `bifurcation_walk_iff_no_length` from
> `Section3_2/MarginalizationsCommute.lean` as the walk-translation
> primitives. For the σ-openness preservation in
> `contract_sigmaOpen_walk_at_single_vertex`: if the LN hand-wave on
> "longer runs through self-loops are handled analogously" blocks the
> proof, **stop and escalate via `expand_proof` on
> `claim_3_25_proof_ISigmaSeparation.tex:129--130`** rather than guessing.

Justification for (a) over (b)/(c)/(d):
- (b) `expand_proof` alone is *necessary but not sufficient*: even if the LN
  hand-wave is expanded, the worker has nowhere to land its tactics without
  the infrastructure of D.1--D.3.
- (c) An alternative proof strategy (e.g., bypassing walks by working purely
  in terms of `marginalize_anc_iff` and `marginalize_bifurcation_iff`) does
  not exist because the σ-open condition is intrinsically about walks, not
  about ancestor/bifurcation existence alone.
- (d) The underlying Lean shapes (`Walk`, `IsSigmaOpen`, `CDMG.marginalize`,
  `IsISigmaSeparated`) are endorsed by prior `verify_*` rounds and used
  downstream by `claim_3_22`, `claim_3_23`, `claim_3_24`, `claim_3_27`. The
  shapes are correct; only the σ-open marginalization API layer **on top of
  them** is missing. No refactor warranted.

### F. Confidence + open questions

**Confidence**: **medium-high** in the recommendation. I have not actually written the
new helper file myself, so I cannot fully rule out that Sub-task 3 turns out
to be much heavier than estimated (the LN's "delicate sub-case" at
proof.tex:159--189 — the unblockable-non-collider rerouting through `w` —
has its own ~30 lines of dense prose that I think can be discharged with the
infrastructure of D.1--D.2, but I haven't carried it through). I am
**high** confidence that the infrastructure gaps in D.1--D.2 are real and
necessary, and **high** confidence on the Blocker A and Blocker B
diagnoses. Confidence on Blocker C (outer reduction) is **medium** — I
believe (D.4.ii) works but haven't tried it.

**Open questions for the manager**:

1. Should I attempt Sub-task 3 directly (with all the size risk), or split it
   further into a "lift-only" sub-task and a "contract-only" sub-task? The
   contract direction is much harder (it owns Blocker B); a "lift-only"
   worker would land cleanly and de-risk the harder follow-up.

2. The visibility promotion in D.2 touches `Section3_2/`. Is that within
   the scope of a *Section 3.3-row* sub-task, or does it need a separate
   `refactor_lean_code` invocation? The current `prove_claim_in_lean` worker
   scope explicitly forbids editing files outside the subsection folder, but
   the promotion is a one-line change per declaration and arguably "API
   exposure for an already-proven private lemma" rather than refactoring.

3. If Blocker B is escalated via `expand_proof` on
   proof.tex:129--130 mid-Sub-task-3, do you want the same worker to absorb
   the `expand_proof` output and continue, or pause for a separate
   `verify_tex_proof` round before resuming?

4. For (D.4.ii), is there an existing `marginalize_empty` or
   `marginalize_emptySet_eq_self` lemma I missed? If not, this would be a
   trivial one-line addition either in `Section3_2/Marginalization.lean` or
   inline in `Section3_3/ISigmaSeparationMarginalization.lean`. (Likely
   needed for the `Finset.induction` base case.)

End of leanification diagnostic.

## Manager B running log (continued)

- **Manager B turn 4 (2026-05-27):** read the full diagnostic. Adopted strategy
  **(a) infrastructure-first**, in the leanifier's 4-sub-task ordering. Bundled
  **D.1 (cheap upstream additions)** and **D.2 (private→public promotion)** into
  a single Sub-task 1 brief — both live in `Section3_2/`, both are small and
  low-risk, and one worker can verify them together with a single `lake build`.
  Open question (1): I am holding the split decision until after Sub-task 3
  begins — if the lift-only half lands cleanly inside one worker session,
  splitting buys nothing. Open question (2): manager sign-off given here for
  the cross-subsection Sub-task 1 (justification: `claude.md:175` allows
  cross-subsection edits with manager approval; D.1 adds new public lemmas
  (no breakage), D.2 only changes visibility (no signature changes, no
  breakage to existing callers). Open question (3): on Blocker B
  escalation, the worker should **pause and report** so I can dispatch a
  separate `expand_proof` + `verify_tex_proof` round before resuming.
  Open question (4): `marginalize_empty` does not currently exist (grep
  confirmed); deferring to the D.4 worker since none of D.1's signatures
  depend on it. Dispatching the Sub-task 1 worker.

### Sub-task 1 completion — 2026-05-27

Sub-task 1 (D.1 + D.2) **complete**. Two files touched, no commit, full
`lake build` clean modulo the one expected `sorry` at
`Section3_3/ISigmaSeparationMarginalization.lean:442:8` (the row's main
body, untouched).

**D.1 (`Section3_2/MarginalizationPreserves.lean`)** — four new
public theorems added inside `namespace CDMG`, after
`marginalize_isTopologicalOrder` (claim_3_16 part 4) and before
`end CDMG`, under a new `## Downstream support layer (claim_3_25 helpers)`
sub-section header. Line numbers (after the additions):

  | name | line |
  |---|---|
  | `marginalize_desc_iff`              | 3986 |
  | `marginalize_Sc_iff`                | 4040 |
  | `marginalize_AncSet_subset`         | 4093 |
  | `marginalize_AncSet_eq_on_complement` | 4142 |

**D.2 (`Section3_2/MarginalizationsCommute.lean`)** — `private`
keyword removed on **seven** declarations (the diagnostic counted
"six" but flagged the unified-length `directed_walk_iff` as an
optional addition; reading the file confirmed both length-bound and
no-length variants exist and both are useful for downstream, so all
seven were promoted). Signatures and proofs are **unchanged**. Updated
the surrounding section docstring at the top of the helpers block to
reflect the mixed private / public visibility and to document the
manager sign-off + downstream rationale.

Line numbers (after the docstring update):

  | name | new line | (was) |
  |---|---|---|
  | `lift_directed_walk`            | 145 | 121 |
  | `shrink_directed_walk`          | 302 | 278 |
  | `directed_walk_iff`             | 503 | 479 |
  | `directed_walk_iff_no_length`   | 543 | 519 |
  | `lift_bifurcation_walk`         | 610 | 586 |
  | `shrink_bifurcation_walk`       | 710 | 686 |
  | `bifurcation_walk_iff_no_length` | 808 | 784 |

The other five `private` declarations in
`MarginalizationsCommute.lean` (`mk_eq_of_data`, `list_tail_dropLast`,
`start_in_support_dropLast`, `support_append_dropLast`,
`support_tail_in_V_of_isDirected`) were intentionally left `private`
— they're CDMG-extensionality / list-massaging glue specific to the
`marginalize_marginalize` proof body, not part of the walk-translation
API that claim_3_25 consumes. If Sub-task 3 turns out to need any of
them, that's the moment to revisit; the diagnostic did not flag them.

**Signature deviations from the diagnostic.**

(a) **`marginalize_Sc_iff` precondition dropped from
`(hv : v ∈ G) (hvW : v ∉ W)` to `(hvW : v ∉ W)`.** The diagnostic
wrote `(hv : v ∈ G) (hvW : v ∉ W)` mirroring an LN-style preamble,
but the proof never references `v ∈ G`: when `v ∉ G` both sides are
empty (`Sc v` is empty off `G`, and the only `(G.marginalize W).Sc v`
member would have to share a directed walk to / from `v` in
`G.marginalize W`, which lands `w` outside `W` via the same
end-of-walk-in-`V` argument). Matching `marginalize_anc_iff`'s
single-precondition shape (only `_ ∉ W`) makes the two theorems pair
cleanly at call sites — the SCC-rewriting step of Sub-task 3
would otherwise need a useless `v ∈ G` extraction.

(b) **`marginalize_AncSet_eq_on_complement` gained an extra
`(hW : W ⊆ G.V)` precondition** the diagnostic omitted. Reason: the
equality `(G.marginalize W).AncSet C = G.AncSet C \ W` *fails*
without `W ⊆ G.V` — a witness `a ∈ G.J ∩ W` can be in
`(G.marginalize W).AncSet C` (via a `G.J`-source directed edge to
some `v ∈ C`) while being excluded from `G.AncSet C \ W` (since
`a ∈ W`). The LN's source block carries `D ⊆ V` (`graphs.tex` 1414),
and the proof.tex's set-rewrite at line 48
(`Anc^{G^{\sm u}}(C) = Anc^G(C) \cap (J \cup V \sm \{u\})`) uses
`{u} ⊆ V` implicitly. Adding the precondition makes the equality
truthful and is satisfied at the only downstream call site (claim_3_25
passes `hDV : D ⊆ G.V` directly).

(c) **All other signatures match the diagnostic exactly** — the
remaining three D.1 theorems and the seven D.2 promotions
(signatures unchanged on promotion, by design).

**Surprises / coupling.**

None blocking. Two observations for the Sub-task 3 worker:

* The directed-walk iff in `MarginalizationsCommute.lean` exists in
  *two* variants — `directed_walk_iff` (with `1 ≤ length` baked in
  on both sides, signature on line 503) and
  `directed_walk_iff_no_length` (with `hab : a ≠ b` instead, line
  543). Both are promoted; pick whichever fits the recursion pattern
  at each call site.
* The seven promoted lemmas internally call private helpers
  (`list_tail_dropLast`, `start_in_support_dropLast`,
  `support_append_dropLast`, `support_tail_in_V_of_isDirected`) in
  their proof bodies. Since `private` only restricts cross-file
  visibility, this is fine — the public API exposes only signatures,
  not proof bodies, so no further promotion is induced.

**`lake build` result.** Clean. `687/687 jobs`. Only warning:

```
warning: leanification/Chapter3_GraphTheory/Section3_3/ISigmaSeparationMarginalization.lean:442:8: declaration uses `sorry`
```

(the expected one; line is 442 in the actual file, the diagnostic
referred to it as :447 in §A — minor positional drift, same
declaration). Plus the pre-existing style / deprecation warnings on
`push_neg` and `simp` flexibility in several files (all pre-existing,
not introduced by this sub-task).

### Sub-task 2 completion — 2026-05-28

Sub-task 2 (D.3 helper file `Section3_3/SigmaOpenWalkMarginalization.lean`)
**partially complete with ESCALATION on the lift theorem**.

**File created**: `leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean`

**Three new declarations** (all in `namespace Causality.CDMG`):

  | name | line | status |
  |---|---|---|
  | `lift_sigmaOpen_walk_through_single_vertex` | 272 | **ESCALATED** (`by sorry` with detailed TODO) |
  | `contract_sigmaOpen_walk_at_single_vertex`  | 386 | stub (`by sorry`, sub-task 3) |
  | `isISigmaSeparated_marginalize_singleton_iff` | 434 | stub (`by sorry`, sub-task 4) |

**Signature deviations from the diagnostic.** None. All three
signatures match diagnostic §D.3 exactly (with the explicit
`huA : u ∉ A`, `huB : u ∉ B` carried in `contract_*` for the
sub-task-3 worker's convenience; the lift theorem deliberately
omits them per the diagnostic's note that they are not needed
for the lift direction).

**Imports added** beyond the diagnostic's minimum:
* `Section3_3.SigmaBlockedReversal` -- for the
  `nodeAt_append_le` / `nodeAt_append_add_left` /
  `isColliderAt_append_lt_length` /
  `isColliderAt_append_cons_cons_one` /
  `isUnblockableNonColliderAt_append_*` walk-position-transport
  lemmas the lift proof would consume.
* `Section3_3.LabelRomanHelpers` -- for the
  `isDirected_append` / `isColliderAt_append_shift_pos` /
  `directed_walk_in_Sc` / `anc_trans` lemmas the lift proof
  would consume for the unblockability-preservation SCC argument.

**ESCALATION on the lift theorem** (`lift_sigmaOpen_walk_through_single_vertex`):

The escalation policy in the sub-task brief
("I would rather have a clean partial result than a guessed
proof") is invoked. The proof body is `by sorry` with a
detailed TODO block citing:

* The structural-recursion skeleton (induct on `π'`,
  case-split on the head `WalkStep`, lift via
  `mem_marginalize_E` / `mem_marginalize_L`, concatenate via
  `Walk.append`).
* The σ-openness verification at each position type
  (interior `u` / boundary `b_j`).
* The **named obstruction**: the LN's "unblockable non-collider
  remains unblockable" SCC argument at proof.tex lines 94 -- 100.
  This is the LN's deepest mathematical content in the lift
  direction and requires inspecting the *specific shape* of each
  lift segment to determine the outgoing-edge structure at
  boundary positions, then chaining ancestry / descendant facts
  through `marginalize_anc_iff` / `marginalize_desc_iff` /
  `marginalize_Sc_iff`.
* Estimated remaining effort: ~500 -- 1000 lines, comparable to
  the bifurcation translator proofs in
  `Section3_2/MarginalizationsCommute.lean:610 -- 825`.
* The infrastructure (per-step lift primitives, AncSet/Sc
  preservation, append-position transport) is all in place.

**Surprises / coupling notes for the Sub-task 3 worker.**

(a) **The boundary unblockability preservation argument is the
load-bearing piece of *both* directions.** The lift's
"unblockable in `π'` (marg) → unblockable in `ρ` (G)" is
mirrored by the contract direction's
"unblockable in `π` (G) → either unblockable in `π'` (marg)
or the LN's edge-rerouting fires (proof.tex:159 -- 189)".
Sub-task 3 may want to factor a *joint* SCC-argument lemma
that both directions consume; if so, please coordinate with
sub-task 2's follow-up.

(b) **No new `Walk.append`-related lemmas were added.** All the
walk-position transport needed for boundary analysis is
already in `Section3_3/SigmaBlockedReversal.lean` and
`Section3_3/LabelRomanHelpers.lean`. If sub-task 3 (or the
lift-completion worker) needs a new append lemma, it should
go in one of those two files, *not* in
`SigmaOpenWalkMarginalization.lean` (which is row-3-25-specific).

(c) **The `IsBlockableNonColliderAt` predicate at endpoint
positions (`k = 0` and `k = π.length`) is unconditionally
True** (via `isBlockableNonColliderAt_zero` /
`isBlockableNonColliderAt_length` in
`Section3_3/BlockableAndUnblockable.lean`). So the nil case
of the lift induction needs `hOpen'.2 0` to discharge
`v ∉ C`; similarly for the cons case at the right endpoint.

**`lake build` result.** Clean. `688/688 jobs`. Four `sorry`
warnings — one **more** than the expected three:

```
warning: leanification/Chapter3_GraphTheory/Section3_3/ISigmaSeparationMarginalization.lean:442:8: declaration uses `sorry`
warning: leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean:272:8: declaration uses `sorry`
warning: leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean:386:8: declaration uses `sorry`
warning: leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean:434:8: declaration uses `sorry`
```

The `:272` `sorry` is the escalated lift theorem. The other two
(`:386, :434`) are the sub-task-3 / sub-task-4 stubs per the
plan. The `:442` is pre-existing in
`ISigmaSeparationMarginalization.lean` (untouched).

**Open question for the manager.** The lift escalation means
sub-task 3 cannot proceed as planned (the singleton iff
combines lift + contract, both of which would be unproven).
Two options:
1. **Re-dispatch a sub-task-2-completion worker** with a longer
   budget specifically for the lift proof. The escalation TODO
   in `SigmaOpenWalkMarginalization.lean:280 -- 339` is detailed
   enough that a fresh worker can pick up directly.
2. **Re-bundle**: dispatch a single worker for lift + contract
   together (sub-tasks 2 + 3 fused). The joint SCC-argument
   factoring noted in (a) above may make this more efficient
   than two separate workers.

The manager's call.

### Manager B turn 5 (2026-05-28) — decision on the escalation

Choosing **option 1** (re-dispatch a fresh sub-task-2-completion worker
specifically for the lift theorem). Reasons:

1. **Smaller blast radius.** Lift alone is a focused, well-scoped
   deliverable; bundling with contract drags Blocker B (self-loop
   hand-wave) into the same worker session, where mid-proof escalation
   would interrupt the structural-recursion bookkeeping. Lock lift in
   first.
2. **The TODO is actionable.** `SigmaOpenWalkMarginalization.lean`
   lines 280 -- 337 spell out the structural-recursion skeleton, the
   case-split on `WalkStep`, the case-by-case σ-openness verification,
   and the SCC argument at the boundary positions. A fresh worker can
   pick this up directly.
3. **Fresh-perspective lift over `continue_agent`.** The original
   sub-task 2 worker (session `bf95b774`) explicitly invoked the
   escalation policy ("clean partial result over guessed proof") —
   that's a cognitive commitment to stopping. A new agent has no such
   prior decision and is more likely to push through.
4. **The "joint SCC argument" can be factored *after* both directions
   exist.** Sub-task 2's completion note (a) suggests factoring a
   joint lemma. That's a `simplify_proof` opportunity later, not a
   pre-condition for getting either direction proven.

Sub-task brief: fresh `spawn_agent_sub_task` worker, edits exactly the
single `lift_sigmaOpen_walk_through_single_vertex` theorem at
`SigmaOpenWalkMarginalization.lean:272`. Other two stubs at `:386`
(contract) and `:434` (singleton iff) remain untouched — they belong
to sub-task 3 / sub-task 4.

### Manager B turn 6 (2026-05-28) — second escalation; decompose further

The fresh worker (session `11d69522`) **also escalated** rather than
attempt the proof. They produced a much more detailed TODO (now at
`SigmaOpenWalkMarginalization.lean` lines 280 -- 592) including a
strengthened-IH design, a 6-helper decomposition, and a vacuous-
implication observation for the bidir case. But still `by sorry`.

Pattern recognized: **workers see a 500--1000 LoC structural recursion
and bail.** The "clean partial result over guessed proof" escalation
policy is too permissive for a proof of this size. Two consecutive
workers have made the same call.

**New strategy: decompose past the lift theorem itself.** The second
worker's refined TODO at `SigmaOpenWalkMarginalization.lean:534--561`
identifies 6 private helpers to add *before* attempting `lift_aux`:

| # | Helper | Estimated LoC | Status |
|---|---|---|---|
| 1 | `not_isColliderAt_interior_of_isBifurcation` | ~80 | most novel content; standalone |
| 2 | `isBlockableNonColliderAt_append_shift_pos` | ~15 | mechanical |
| 3 | `isAllBackward_reverse_of_isDirected` (local copy) | ~15 | direct re-derivation |
| 4 | `forward_step_to_walk_in_G` | ~15 | unfold `mem_marginalize_E` |
| 5 | `backward_step_to_walk_in_G` | ~25 | unfold + reverse |
| 6 | `bidir_step_to_walk_in_G` | ~30 | unfold `mem_marginalize_L` |

Total: ~180 LoC across 6 standalone helpers. Each is independently
provable and small enough that no worker should escalate.

Sub-strategy:
- **Sub-task 2a**: dispatch a worker for just helper (1),
  `not_isColliderAt_interior_of_isBifurcation`. Standalone, ~80 LoC.
  This is the most mathematically interesting helper (the only one
  the diagnostic explicitly flagged as "genuinely new content").
  Successful completion gives us momentum + a foundational reusable
  bifurcation lemma.
- **Sub-task 2b**: dispatch a worker for helpers (2)--(6). ~100 LoC
  total of mechanical infrastructure.
- **Sub-task 2c**: dispatch a worker for `lift_aux` + the main lift
  theorem body. ~200--400 LoC, but with all prerequisites in place
  so "stop and report" is a much higher bar.

Reasons for this finer decomposition:
1. **No bail-out room.** Helper (1) is one lemma. The worker either
   proves it or declares it false. Escalation is not on the menu.
2. **Foundational reuse.** Helper (1) is a clean, general fact about
   bifurcations and may be hoisted to `Section3_1/Bifurcation.lean`
   later. Worth getting right.
3. **Momentum building.** Two consecutive escalations have cost
   significant compute without producing any Lean code beyond
   refined TODOs. Need a concrete win.

Dispatching sub-task 2a (helper 1) as the next action.

### Manager B turn 7 (2026-05-28) — sub-task 2a complete; dispatch 2b

**Sub-task 2a (helper 1) — DONE.** Session `a6510b28` returned with
`not_isColliderAt_of_isBifurcation` proven at
`SigmaOpenWalkMarginalization.lean:214 -- 295` (~80 LoC). The lemma is
a `private`, sits inside `namespace Causality.CDMG`, and consumes only
`leftBackward` / `rightDirected` from the bifurcation witness as
expected. `lake build` clean, 688/688 jobs. Five `sorry` warnings as
expected (`:442` in `ISigmaSeparationMarginalization.lean` for the
row body; `:443`, `:763`, `:823`, `:869` in
`SigmaOpenWalkMarginalization.lean` for the lift theorem header,
its TODO body, the contract stub, and the singleton-iff stub).

**Decision: dispatch sub-task 2b — helpers (2) through (6) bundled.**
Reasons:

1. **No risk of escalation reframing.** Each of (2) -- (6) is small
   (~15 -- 30 LoC) and mechanical. Bundling them in one worker session
   does NOT recreate the "500--1000 LoC bail-out" pattern that bit
   sub-tasks 2 and 2-completion: every individual helper is a
   self-contained unfold + dispatch to existing API.
2. **Shared idiom.** Helpers (4) -- (6) all unfold the same shape
   `mem_marginalize_E` / `mem_marginalize_L` and extract a lift
   segment; bundling avoids re-explaining the unfold idiom three
   times.
3. **All upstream API verified to exist.** Manager B turn 7 confirmed:
   * `isColliderAt_append_shift_pos` -- `LabelRomanHelpers.lean:728`.
   * `isUnblockableNonColliderAt_append_shift_pos` --
     `LabelRomanHelpers.lean:785`.
   * `IsBlockableNonColliderAt` def -- `BlockableAndUnblockable.lean:545`,
     defining equation at `:549`. `IsBlockableNonColliderAt k :=
     IsNonColliderAt k ∧ ¬ IsUnblockableNonColliderAt k`.
   * `IsNonColliderAt` def -- `CollidersAndNon.lean:309`.
   * `isAllBackward_reverse_of_isDirected` (private) --
     `BifurcationAlternative.lean:136 -- 149` (10 lines, ready for
     local copy).
   * `lift_directed_walk` -- `MarginalizationsCommute.lean:145` (public
     post-Sub-task 1).
   * `lift_bifurcation_walk` -- `MarginalizationsCommute.lean:610`
     (public post-Sub-task 1).

**Sub-task 2b helper signatures (the worker's contract):**

```lean
-- (2) Append-shift transport for IsBlockableNonColliderAt.
private theorem isBlockableNonColliderAt_append_shift_pos
    {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w) (k' : ℕ)
    (hk : 0 < k') :
    (p₁.append p₂).IsBlockableNonColliderAt (p₁.length + k') ↔
      p₂.IsBlockableNonColliderAt k'

-- (3) Local re-derivation of the private lemma at
-- BifurcationAlternative.lean:136 (direct copy of body).
private lemma isAllBackward_reverse_of_isDirected_local {v w : α}
    {p : Walk G v w} (hp : p.IsDirected) : p.reverse.IsAllBackward

-- (4) Per-step lift wrapper for `forward` steps.
private lemma forward_step_to_walk_in_G {G : CDMG α} {u v m : α}
    (h_E : (v, m) ∈ (G.marginalize {u}).E)
    (hvu : v ≠ u) (hmu : m ≠ u) :
    ∃ σ : Walk G v m, σ.IsDirected ∧ σ.InteriorIn {u} ∧ 1 ≤ σ.length

-- (5) Per-step lift wrapper for `backward` steps.
private lemma backward_step_to_walk_in_G {G : CDMG α} {u v m : α}
    (h_E : (m, v) ∈ (G.marginalize {u}).E)
    (hvu : v ≠ u) (hmu : m ≠ u) :
    ∃ σ : Walk G v m, σ.IsAllBackward ∧ σ.InteriorIn {u} ∧ 1 ≤ σ.length

-- (6) Per-step lift wrapper for `bidir` steps.
private lemma bidir_step_to_walk_in_G {G : CDMG α} {u v m : α}
    (h_L : (v, m) ∈ (G.marginalize {u}).L)
    (hvu : v ≠ u) (hmu : m ≠ u) (huV : u ∈ G.V) :
    ∃ σ : Walk G v m, σ.IsBifurcation ∧ σ.InteriorIn {u} ∧ 1 ≤ σ.length
```

Two judgment calls baked into these signatures:

* **Signature of `(6)`.** `mem_marginalize_L` exposes the bifurcation
  in either direction (v → m OR m → v); the worker must pick one and
  may need to reverse the m → v case via
  `Walk.reverse`. The codebase warning at
  `Marginalization.lean:369--371` (`IsBifurcation` does NOT transport
  through reverse for single-step backward bifurcations) is sidestepped
  because *for the (6) case we only need the existence of a walk in `G`
  with the right interior + length* — not strictly a bifurcation. The
  caller (lift_aux) consumes the conclusion via the vacuous-implication
  observation in the second-pass TODO (`SigmaOpenWalkMarginalization.lean:494 -- 501`).
  Therefore: **soften the `(6)` conclusion** to drop the `IsBifurcation`
  conjunct, OR insist on `IsBifurcation` and let the worker prove it by
  case-analysis on which direction `mem_marginalize_L` produces. The
  manager defers this judgment call to the worker; they should pick
  whichever is easier and document the choice.

* **Signature of `(3)`.** Suffixed `_local` to avoid clashing with the
  private one in `BifurcationAlternative.lean` (same namespace). The
  worker may drop the suffix if Lean's privacy semantics make it OK
  (private declarations are file-local, so name clash should not occur,
  but suffixing is a safety net).

**Dispatching sub-task 2b worker.**

### Manager B turn 8 (2026-05-28) — sub-task 2b complete; dispatch 2c (the lift theorem itself)

**Sub-task 2b — DONE.** Session `97daa3b3` returned with all six helpers
(plus one aux `interiorIn_reverse_iff`) at `SigmaOpenWalkMarginalization.lean`
lines 214 -- 485 (helper 1 at 214 -- 295, aux at 324 -- 332, helpers 2 -- 6
at 348 -- 485). `lake build` clean, 688/688 jobs, four expected `sorry`
warnings (`:442` row body, `:633` lift, `:1002` contract stub, `:1050`
singleton-iff stub) and five unused-variable warnings on `hvu` / `hmu` /
`huV` in helpers 4 -- 6 (documentary preconditions, kept per the manager's
spec; will be revisited at `simplify_proof` time after the lift theorem
is proved).

Helper signature notes baked into the file (the lift theorem worker's
contract):

* **Helper (6) softened.** The worker (and the manager) dropped the
  `IsBifurcation` conjunct from `bidir_step_to_walk_in_G`'s conclusion.
  Conclusion is now just `∃ σ : Walk G v m, σ.InteriorIn {u} ∧ 1 ≤ σ.length`.
  Rationale (per the inline design block at lines 440 -- 463): the bidir
  consumer in the lift theorem only needs a walk in `G` with the right
  interior + length, because the boundary joint-condition implication
  `σ.last.HasArrowheadAtTarget → step.HasArrowheadAtTarget` collapses to
  `True → True` when `step = bidir` (target-arrowhead trivially True).
* **Helper (5) reverse pattern**: backward step uses
  `π.reverse` via `interiorIn_reverse_iff` (the auxiliary) and
  `isAllBackward_reverse_of_isDirected_local` (helper 3).

**Decision: dispatch sub-task 2c — the lift theorem proof itself.**

Reasons to dispatch now (rather than dispatch sub-task 3 first or try a
joint lift+contract worker):

1. **All infrastructure is in place.** Sub-task 1 (`Section3_2/Marginalization*`
   public API expansions) + Sub-task 2a (helper 1, the only "novel content"
   lemma) + Sub-task 2b (helpers 2 -- 6, mechanical step lifters) cover every
   piece the lift theorem's refined TODO (`SigmaOpenWalkMarginalization.lean:641 -- 953`)
   calls out as needed. There is nothing more to set up upstream.
2. **Escalation policy is tightened.** Two consecutive workers escalated
   on the lift theorem when it was framed as "prove the whole 500 -- 1000
   LoC structural recursion from scratch". The new framing is concrete:
   *(a)* Write a `private lemma lift_aux` with the strengthened IH whose
   signature is already typed out in the file. *(b)* Discharge it by
   structural recursion on `π'` with four sub-cases (nil + forward / backward
   / bidir step) each of which has a step-to-walk helper ready to consume.
   *(c)* Use `lift_aux` to derive the public theorem in 5 -- 10 lines. This
   is a chain of mechanical compositions, not a creative leap.
3. **Lift is independent of contract.** The (⇒) and (⇐) directions of
   `isISigmaSeparated_marginalize_iff` use disjoint infrastructure: lift
   consumes `lift_directed_walk` / `lift_bifurcation_walk` (now public after
   Sub-task 1), contract consumes `shrink_directed_walk` /
   `shrink_bifurcation_walk` (already public). Proving lift first locks in
   roughly half of the (⇒)/(⇐) symmetric pair, then contract can be done
   in a follow-up sub-task with the lift proof as a template.

**Sub-task 2c contract for the worker:**

* **File**: `leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean`,
  edit exactly the theorem `lift_sigmaOpen_walk_through_single_vertex` at
  line 633 -- replace the multi-page TODO comment block (lines 641 -- 952)
  and the `sorry` at line 953 with a real proof. May freely add new
  `private` declarations *above* line 633 (e.g., the `lift_aux` strengthened
  IH); MUST NOT touch the two stubbed declarations at `:1002` and `:1050`,
  the comment blocks around them, or the theorem signature at line 633 -- 640
  itself.
* **Sorry budget after this task**: three (`:442` row body, `:1002` contract
  stub, `:1050` singleton iff stub). The current `:633` warning must
  disappear.
* **Suggested skeleton** (already typed out in the existing TODO at
  lines 656 -- 953):

```lean
-- Strengthened IH: tracks first-step arrowhead invariant for boundary matching.
private lemma lift_aux (G : CDMG α) {u : α} (huV : u ∈ G.V)
    (C : Set α) (huC : u ∉ C) :
    ∀ {a b : α} (π' : Walk (G.marginalize {u}) a b),
      a ≠ u → b ≠ u →
      π'.IsSigmaOpen C →
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C) →
    ∃ ρ : Walk G a b,
      ρ.IsSigmaOpen C ∧
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ C) ∧
      -- The strengthened invariant: "if ρ has a first step, its source-arrowhead
      -- implies π''s first step has a source-arrowhead". Vacuous when π' is nil.
      (... see lines 656 -- 700 for the precise binder shape ...)
```

  Worker should treat the refined TODO at lines 656 -- 953 as the design
  spec: don't reinvent it, follow it.
* **Three things the worker should NOT change**:
  - The helper signatures at lines 214 -- 485 (sub-task 2a + 2b output;
    used by the lift proof). If the worker finds a needed tweak (e.g.,
    strengthening helper (6) back to include `IsBifurcation`), they
    should `request_from_human` or escalate cleanly rather than silently
    re-spec.
  - The two stubs at `:1002` (contract) and `:1050` (singleton iff) and
    their docstrings.
  - The row main body at `ISigmaSeparationMarginalization.lean:442` --
    that's sub-task 4 + the final `D`-induction wrapper.
* **Escalation rules tightened from prior dispatches**:
  - If a specific structural-recursion sub-case bogs down past 200 LoC,
    extract a fresh `private lemma` *for that sub-case* and prove the
    extracted lemma instead -- exactly the pattern Sub-tasks 2a/2b
    already validated. Do NOT escalate the whole theorem.
  - The escalation policy ("stop and report") is OK ONLY if the worker
    encounters a *genuinely new* obstruction not foreseen in the refined
    TODO (e.g., an `IsBifurcation` reversal issue that helper (6)'s
    soften does not actually sidestep). Reporting "this is large" is
    NOT a sufficient reason to escalate this time.
  - If the worker finds a missing API lemma in upstream files
    (e.g., a new `Walk.*` lemma in `Section3_1/Walks.lean`), they should
    add it as a `private` in this file, *not* go cross-subsection again.
    Cross-subsection additions (sub-task 1's scope) are now closed.

**Dispatching sub-task 2c worker.**

---

## Manager B turn 9 — 2026-05-28: Sub-task 2c partial + dispatching Sub-task 2d (`lift_aux` body)

### State after Sub-task 2c worker (turn 16's `spawn_agent_sub_task`)

Worker session `ea3a8761-...` delivered:

* **`bidir_step_to_walk_in_G_arrows`** (lines 530 -- 665, ~135 LoC) — fully proven.
  Strengthened bidir step lift: σ has no collider at any position, σ's
  first step has `HasArrowheadAtSource`, σ's last step has `HasArrowheadAtTarget`.
  Case analyses on `(v → m)` vs `(m → v reversed)` bifurcation directions,
  with the impossible-sub-cases (rightArm = nil + hinge = backward and dual)
  ruled out via `mem_marginalize_L`'s no-directed-walk conjuncts.
* **`u_in_Sc_via_directed_lift`** (lines 697 -- 737, ~40 LoC) — fully proven.
  LN's SCC argument (proof.tex 94 -- 100): from a directed `τ : Walk G m anchor`
  of length ≥ 2 with interior `{u}` and `anchor ∈ G.Anc m`, deduces `u ∈ G.Sc m`.
  Decomposes τ as `cons τ_first τ_tail`, forces the intermediate vertex to `u`
  via the interior constraint, then uses transitivity.
* **`lift_aux`** (lines 791 -- 839) — signature + docstring + detailed TODO + `sorry`.
  **Body NOT done — escalated by Sub-task 2c.** TODO at lines 808 -- 838 outlines
  the structural recursion on `π'` (nil + forward/backward/bidir cons cases),
  each case using the appropriate step lift helper and verifying σ-open clauses
  by case-analyzing position regions (inside σ, boundary `k = σ.length`, after σ).
  Estimated 500 -- 700 LoC.
* **`lift_sigmaOpen_walk_through_single_vertex`** (lines 985 -- 1010) — **proven
  modulo `lift_aux`.** Derives the public theorem from `lift_aux` via the
  `k = 0` repair using `h_c2_full 0`. So once `lift_aux` is filled in, the
  public theorem is automatically discharged.

`lake build` clean (688/688). Sorry warnings: 3 (the `lift_aux` at :791,
the contract stub at :1076, and the singleton-iff stub at :1124).

### Decision: Sub-task 2d — fill in `lift_aux`'s body

I'm dispatching one focused worker to prove just `lift_aux`. Rationale:

1. The infrastructure stack is now complete — all per-step lift helpers
   (forward / backward / strong bidir), the SCC helper, the bifurcation-non-collider
   helper, and the upstream `marginalize_*` API are in place.
2. The TODO at lines 808 -- 838 is a precise roadmap. The worker's job is
   composition, not invention.
3. The 500 -- 700 LoC estimate is large but tractable when (a) the worker
   is allowed to add private sub-helpers per-step-case (just as Sub-tasks 2a/2b
   added per-step helpers for the lift segment construction), and (b) the
   escalation policy is tightened: only escalate on *new* obstructions, not
   on "this is large".
4. Three prior escalations on the lift theorem were structural (the IH wasn't
   strong enough, the per-step lifts didn't have arrowhead witnesses, the SCC
   argument needed its own helper). All three structural issues are now
   resolved by the helpers above. The remaining work is genuinely just
   case-analysis assembly.

The worker gets the same "decompose internally if a case grows past 200 LoC"
escalation policy that Sub-task 2c had, with the additional tightening that
"this is large" is not a valid escalation reason.

---

## Sub-task 2d worker turn — 2026-05-28: ESCALATION with precise IH-design obstruction

**Worker outcome**: ESCALATION (file unchanged from manager turn-9 state — `lake build` clean,
3 expected sorrys: `:442`, `:791`, `:1076`, `:1124`).

**Reason for escalation**: a *genuinely new structural obstruction* in the IH C4 design,
discovered via careful case analysis of the boundary unblockable verification. The
manager's brief explicitly allows this escalation form: "a genuinely-new structural
obstruction that requires a NEW upstream API change". The fix is NOT in upstream files
but in the lift_aux signature itself, which the worker is not permitted to change.

### The obstruction in precise form

The `lift_aux` signature at lines 791 -- 807 specifies C4 as:

```lean
(∀ {mπ : α} (sπ : WalkStep (G.marginalize {u}) a mπ)
   (pπ : Walk (G.marginalize {u}) mπ b),
   π' = Walk.cons sπ pπ →
   ∃ (mρ : α) (sρ : WalkStep G a mρ) (pρ : Walk G mρ b),
     ρ = Walk.cons sρ pρ ∧
     (sρ.HasArrowheadAtSource ↔ sπ.HasArrowheadAtSource))
```

This gives only **source-arrowhead-iff** between `ρ`'s first step and `π'`'s first step.

**Claim**: this is mathematically insufficient for the recursive cons-case's
**boundary unblockable verification**.

**Concrete subgoal where it fails**: in the forward outer case (π' = cons (forward h_E) p'
with p' = cons step' p'' for some step' : WalkStep _ m m'), the boundary check at
position σ.length on ρ requires showing

> `ρ.IsBlockableNonColliderAt σ.length → ρ.nodeAt σ.length = m ∉ C`.

Tracing this through:

1. ρ blockable at σ.length means ρ is non-collider AND NOT unblockable.
2. Non-collider (forward outer case): σ.last is forward (HasArrowheadAtTarget = True),
   so collider iff ρ_p'.first.HasArrowheadAtSource = True. Non-collider means
   ρ_p'.first.HasArrowheadAtSource = False, i.e., ρ_p'.first is forward.
3. NOT unblockable (forward outer case, σ.last.IsBackward vacuously False):
   means ρ_p'.first.IsForward AND ρ_p'.first.target = mρ ∉ G.Sc m.
4. We need to conclude m ∉ C. Path: π'.IsBlockableNonColliderAt 1 + h_c2 1 gives m ∉ C.
5. π' blockable at 1 (forward outer case): step is forward (target-arrow True), so
   collider iff step'.HasArrowheadAtSource = True. By IH C4 arrowhead iff,
   step'.HasArrowheadAtSource = ρ_p'.first.HasArrowheadAtSource = False. So
   step'.IsForward, non-collider. ✓
6. π' NOT unblockable at 1: step.IsBackward (False, vacuous) + step'.IsForward →
   step'.target ∉ (G.marg {u}).Sc m.
7. So we need: **step'.target ∉ (G.marg {u}).Sc m**, given that ρ_p'.first.target = mρ ∉ G.Sc m.
8. The LN's lift table (`claim_3_25_proof_ISigmaSeparation.tex` lines 57 -- 70) says
   the lift of step' is either a length-1 walk (m → m' directly) giving mρ = step'.target,
   OR a length-≥2 walk (m → u → ... → m') giving mρ = u.

The case analysis on whether mρ = step'.target or mρ = u is the LN's split between
"outgoing edge was not expanded through $u$" vs "outgoing edge was expanded through $u$"
(proof.tex lines 95 -- 100):

* **mρ = step'.target case**: mρ ∉ G.Sc m, so step'.target ∉ G.Sc m, so
  step'.target ∉ G.Sc m \ {u} = (G.marg {u}).Sc m. ✓
* **mρ = u case**: u ∉ G.Sc m. Need step'.target ∉ (G.marg {u}).Sc m. Assume otherwise
  for contradiction: step'.target ∈ (G.marg {u}).Sc m ⊆ G.Sc m, so step'.target ∈ G.Anc m.
  We have u ∈ G.Anc step'.target (the suffix u → ... → step'.target of the length-≥2 lift
  segment of step'). By Anc-trans (`CDMG.anc_trans`): u ∈ G.Anc m.
  Also u ∈ G.Desc m (from sρ being the forward step m → u in G, since sρ.IsForward holds
  by source-arrowhead iff with step' forward). So u ∈ G.Sc m = G.Anc m ∩ G.Desc m.
  Contradicts u ∉ G.Sc m. ✓

**The problem**: the IH C4 as specified gives us only the source-arrowhead iff.
It does NOT expose:

* whether mρ = step'.target or mρ = u (i.e., the binary dispatch), OR
* the SCC info `u ∈ G.Anc step'.target` (needed for the mρ = u case via Anc-trans), OR
* the lift segment's structure that would let us derive these.

### Proposed fix: strengthen C4

The minimal strengthening that closes the gap:

```lean
(∀ {mπ : α} (sπ : WalkStep (G.marginalize {u}) a mπ)
   (pπ : Walk (G.marginalize {u}) mπ b),
   π' = Walk.cons sπ pπ →
   ∃ (mρ : α) (sρ : WalkStep G a mρ) (pρ : Walk G mρ b),
     ρ = Walk.cons sρ pρ ∧
     (sρ.HasArrowheadAtSource ↔ sπ.HasArrowheadAtSource) ∧
     (sρ.IsForward → mρ ∈ G.Anc mπ))   -- NEW conjunct
```

The new conjunct `sρ.IsForward → mρ ∈ G.Anc mπ` captures the SCC-suffix invariant uniformly:

* mρ = mπ (length-1 lift): reflexive Anc inclusion via `CDMG.self_mem_Anc`.
* mρ = u (length-≥2 lift): the suffix of the lift gives u ∈ G.Anc mπ.

With this, the boundary contradiction argument goes through:

```
mρ ∉ G.Sc m + sρ.IsForward → mρ ∈ G.Anc mπ + step'.target ∈ G.Anc m
  → mρ ∈ G.Anc m (Anc-trans)
  → mρ ∈ G.Desc m (sρ forward gives single-edge m → mρ)
  → mρ ∈ G.Sc m
  → contradicts mρ ∉ G.Sc m.
```

### Second obstruction: p' = nil sub-case at boundary

Even with the strengthened C4, there is a SECOND obstruction in the cons-case's
**p' = nil sub-case**:

* When p' = nil m, applying IH on p' = nil m gives some ρ_p' : Walk G m m. The IH's
  C4 strong is vacuous (no cons decomposition of p'). So abstractly ρ_p' could be
  EITHER nil m or cons s_first ρ_rest. The proof of `lift_aux_strong`'s nil case
  produces ρ_p' = nil m, but as a consumer of the IH, we lose this information.
* If ρ_p' is cons (abstractly possible), the boundary at σ.length on ρ has joint
  structure (σ.last + ρ_p'.first) and we cannot verify ρ.nodeAt σ.length = m ∈ AncSet C
  for the collider clause, nor m ∉ C for the blockable clause — because h_c1 1 gives
  vacuously nothing (π'.IsColliderAt 1 = False on cons_nil) and h_c2 1 gives m ∉ C
  unconditionally (since π'.IsBlockableNonColliderAt 1 = True at length-1 endpoint).

The fix is straightforward: **C5 invariant on length-preservation at nil**:

```lean
(π'.length = 0 → ρ.length = 0)
```

This says: if π' is the trivial walk, so is ρ. Combined with `source_eq_target_of_length_zero`
(LabelRomanHelpers.lean line 1054), this forces ρ_p' = nil m when p' = nil m, eliminating
the awkward sub-case.

For the recursion, C5 is verified easily: in the nil case ρ = nil v has length 0 ✓; in the
cons case σ.length ≥ 1 forces ρ.length ≥ 1, so the implication is vacuous ✓.

### Recommended action: strengthened auxiliary lemma

Add a private auxiliary `lift_aux_strong` BEFORE `lift_aux` (between line 738 and the
docstring at line 739), with the strengthened signature (C4 strong + C5). Then:

```lean
private lemma lift_aux ... := by
  intro a b π' ha hb h1 h2 h3
  obtain ⟨ρ, hc1, hc2, hc3, _h_len, h_c4_strong⟩ :=
    lift_aux_strong huV huC π' ha hb h1 h2 h3
  refine ⟨ρ, hc1, hc2, hc3, ?_⟩
  intros mπ sπ pπ h_eq
  obtain ⟨mρ, sρ, pρ, hρ_eq, hρ_arrow, _h_anc⟩ := h_c4_strong sπ pπ h_eq
  exact ⟨mρ, sρ, pρ, hρ_eq, hρ_arrow⟩
```

This keeps `lift_aux`'s public signature (lines 791 -- 807) **unchanged**, satisfying the
manager's no-touch constraint, while exposing the strengthened C4 + C5 internally for the
inductive recursion.

### Work attempted in this session

The worker:

1. Read all 8 required documents (claude.md, prove_claim_in_lean.md, workspace, graphs.tex
   1414 -- 1579, claim_3_25_proof_ISigmaSeparation.tex, the lean file end-to-end, Sub-task 1
   additions, Walks/SigmaBlockedWalks/Marginalization/etc. API surface).
2. Identified the source-arrowhead-iff insufficiency through careful case analysis of the
   boundary unblockable check.
3. Identified the p' = nil + ρ_p' = cons abstract-IH gap.
4. Designed the strengthened C4 + C5 invariants.
5. Drafted a partial `lift_aux_strong` (nil case + partial forward case, ~350 LoC of dense
   Lean code) before recognizing the scope.
6. Reverted to leave the file UNCHANGED from manager turn-9 state.
7. Wrote this escalation document.

The drafted partial proof confirmed:

* The nil case is ~12 lines.
* The forward cons case (without p' = nil sub-case issue, with strengthened IH) is
  estimated at ~150 -- 200 LoC.
* Backward and bidir follow analogous patterns with ~150 -- 200 LoC each.
* Total `lift_aux_strong` proof: estimated ~500 -- 700 LoC.
* `lift_aux` derivation: ~7 LoC.

### Estimated remaining effort

A focused worker with the strengthened signature in hand should be able to complete this
in one session. Recommend:

1. Dispatch a worker with the explicit instruction to add `lift_aux_strong` as a private
   helper above lift_aux (in the same `namespace Causality.CDMG` block) with the
   strengthened C4 + C5 signature shown above, and derive lift_aux from it (~7 lines).
2. The worker should write the proof of `lift_aux_strong` as a structural recursion on π'
   with:
   * nil case (trivial, ~12 lines)
   * cons case dispatching on step (forward / backward / bidir)
   * Each step case **case-splits on p' FIRST** (avoiding the p' = nil + ρ_p' = cons
     abstract-IH gap by NOT applying IH when p' = nil)
   * For p' = nil: build ρ := σ directly (using `Walk.append_nil` to make types match).
   * For p' = cons step' p'': apply IH on p', use C4 strong + C5 to extract ρ_p''s
     structure, do position-region case analysis on ρ.

This pattern is concrete enough that the worker should not escalate. The "decompose into
per-step-case private helpers" option from sub-task 2b's pattern remains available for
sub-cases that exceed ~200 LoC.

### Acknowledged failure modes the next worker should anticipate

1. **`induction π'` may not generalize the implicit `a b` indices**. The pattern used in
   `not_isColliderAt_of_isBifurcation` (this file, lines 222 -- 295) is the canonical
   workaround: `intro a m m' b la; induction la with | nil _ => ... | @cons _ _ _ s p ih => ...`.
   Lean 4's `induction` tactic does generalize indices that the goal depends on, but the
   worker should validate this on a small smoke test (e.g., the nil case + one cons case
   compiling) before sinking time into the full proof.
2. **`Walk.length_zero_iff` may not exist**; the worker may need to inline the argument
   "ρ_p'.length = 0 → ρ_p' = nil m" via `cases ρ_p' with | nil _ => rfl | cons _ _ => omega`.
3. **`source_eq_target_of_length_zero` is at `LabelRomanHelpers.lean:1054`** if needed for
   forcing m = b in the p' = nil sub-case.
4. **The boundary unblockable contradiction argument requires `CDMG.anc_trans`**, which
   has signature `Anc x → Anc y → Anc z` (transitive — check the exact form at
   `Section3_1/FamilyReachability.lean`).
5. The IH for p' has `m` (intermediate vertex) and `b` (outer endpoint) as endpoints.
   Lean's induction-tactic IH automatically handles index generalization, so applying
   `ih hm_ne_u hb_ne_u hp_c1 hp_c2 hp_col_in_C` should work.

### Sorry budget unchanged

`lake build` ran clean at `688/688 jobs` with the exact same 3 sorrys as before the
worker's session: `:442` row body, `:791` lift_aux, `:1076` contract stub, `:1124`
singleton iff stub. (4 sorrys total, matching the manager turn-9 file state. The "3 sorrys
before, 2 after" from the worker brief counts only the SigmaOpenWalkMarginalization.lean
sorrys; the `:442` ISigmaSeparationMarginalization.lean sorry is pre-existing across all
sub-tasks.)

### Why this is NOT a "this is large" escalation

The manager's policy explicitly tightens against "this is large". This escalation is on
two **specific structural insufficiencies** in the IH design:

1. The C4 conjunct as currently specified gives only source-arrowhead-iff, but the
   boundary unblockable verification requires also `sρ.IsForward → mρ ∈ G.Anc mπ`.
2. The C4 conjunct's vacuous-on-nil-π' clause does not constrain ρ when π' is nil, but
   the boundary verification (when called recursively with p' = nil) cannot distinguish
   ρ_p' = nil from ρ_p' = cons abstractly.

Both fixes change the lift_aux conclusion, which the worker is not permitted to do. The
clean workaround is the private `lift_aux_strong` auxiliary with the strengthened
conclusion, derived as shown.

The worker did NOT escalate on size alone; the partial draft (forward case ~70 LoC of
nil sub-case + ~80 LoC of cons sub-case before hitting the IH-vacuity gap) confirmed
that the per-case work is mechanically tractable once the IH is right. The blocker is
the IH design, not the size.

## Manager B turn 10 — 2026-05-28: dispatching Sub-task 2e (`lift_aux_strong` + `lift_aux`)

### Decision

Sub-task 2d's escalation is **well-grounded structural feedback**, not a "this is large"
escalation. I accept the diagnosis:

* The current C4 (source-arrowhead-iff only) cannot discharge the boundary unblockable
  verification in the forward outer cons-case with the length-≥2 lift sub-case.
* Without C5 (length-zero preservation), the IH on `p' = nil` does not constrain `ρ_p'`,
  forcing an awkward abstract sub-case.

### Plan: add `lift_aux_strong` private helper

Strategy from the diagnostic (lines 1342 -- 1360, paraphrased):

1. Add `private lemma lift_aux_strong` BEFORE `lift_aux` (line 791) with the strengthened
   conclusion: append `∧ (sρ.IsForward → mρ ∈ G.Anc mπ)` to the C4 existential, and
   append `∧ (π'.length = 0 → ρ.length = 0)` to the conjunction list.
2. Prove `lift_aux_strong` by structural recursion on `π'`. Each per-step-case
   case-splits on `p'` FIRST (to handle `p' = nil` via direct construction `ρ := σ`
   without applying the IH), and on `p' = cons` applies the IH.
3. Derive `lift_aux`'s body (lines 808 -- 839) from `lift_aux_strong` in ~7 lines by
   discarding the new conjuncts.

This preserves `lift_aux`'s public signature (consumed by `lift_sigmaOpen_walk_through_single_vertex`
at line 985), so that derivation remains unchanged.

### Verification of the new conjuncts in each step-lift case

For C4-strong's new conjunct `sρ.IsForward → mρ ∈ G.Anc mπ`:

* **forward step lift** (`forward_step_to_walk_in_G` at :410):
  * length-1 sub-case: `mρ = mπ`, use `CDMG.self_mem_Anc (mπ ∈ G.V)`.
  * length-≥2 sub-case: `mρ = u`, suffix `u → ... → mπ` directed, gives `u ∈ G.Anc mπ`.
* **backward step lift** (`backward_step_to_walk_in_G` at :430): `sρ` is backward,
  so `sρ.IsForward = False`, conjunct vacuous.
* **bidir step lift** (`bidir_step_to_walk_in_G_arrows` at :530): `sρ` is bidir or
  backward (per bifurcation pattern), never forward. Conjunct vacuous.

For C5 `π'.length = 0 → ρ.length = 0`:

* **nil case**: `π' = nil v`, `ρ := nil v`, both length 0. ✓
* **cons cases**: `π'.length ≥ 1`, hypothesis `π'.length = 0` is False, vacuous. ✓

### Worker's escalation contract

The worker is **not permitted to escalate on size**. They may escalate ONLY on:

* A genuinely NEW structural obstruction (not the C4-strong / C5 gap, which is closed),
* A specific API gap requiring an upstream addition (treat that as "report and request
  manager guidance", do NOT add upstream files).

If a per-case body grows past ~200 LoC, the worker should add a private sub-helper
WITHIN the same file (following the Sub-task 2b pattern), not escalate.

### Anticipated failure modes (from Sub-task 2d's report)

1. `induction π'` may not generalize implicit `a b` indices — fallback to the
   `intro a; intro b; intro π'; induction π'` pattern, or `Walk.cases` if needed.
2. `Walk.length_zero_iff` may not exist — inline `cases ρ_p' with | nil _ => rfl | cons _ _ => omega`.
3. `CDMG.self_mem_Anc` is at `Section3_1/FamilyReachability.lean:141` (`{v : α} (hv : v ∈ G) : v ∈ G.Anc v`).
4. `CDMG.anc_trans` is at `Section3_3/LabelRomanHelpers.lean:250` (`(h₁ : u ∈ G.Anc v) (h₂ : v ∈ G.Anc w) : u ∈ G.Anc w`).
5. `source_eq_target_of_length_zero` is at `Section3_3/LabelRomanHelpers.lean:1054`.

### Sorry budget (before / after)

Before Sub-task 2e: 4 sorrys (`:442` row body, `:791` lift_aux body, `:1076` contract stub, `:1124` singleton-iff stub).

After Sub-task 2e (target): 3 sorrys (`:442`, `:1076`, `:1124`) — only `lift_aux` body discharged.
The contract direction (`:1076`) and singleton-iff (`:1124`) are explicitly Sub-task 3 / 4 work.

---

## Manager B turn 11 — 2026-05-28: Sub-task 2e complete; dispatching Sub-task 3 (contract direction)

### Sub-task 2e completion confirmed

Session `013e1090-5817-...` returned with the lift direction **fully proven**:

* **`nodeAt_mem_interior_support`** (new private helper, ~43 lines): lines 747 -- 787 (worker's
  report listed 739 -- 787; the actual file places the docstring at 738 and the lemma
  signature at 747). Extracts "`σ.nodeAt k ∈ σ.support.tail.dropLast` for interior `k`" — a
  position-tracking helper used three times in `lift_aux_strong`.
* **`lift_aux_strong`** (new private auxiliary, ~1195 lines): lines 798 -- 2030 (signature
  798 -- 818, body 819 -- 2030). Structural recursion on `π'` with the C4-strong / C5-strong
  invariants accepted in turn 10's design. No sub-helpers added inside; one large `induction π'`
  proof with detailed per-step case analysis.
* **`lift_aux`** (line 2037): now derives from `lift_aux_strong` in ~7 lines by discarding the
  new conjuncts. Public signature unchanged.
* **`lift_sigmaOpen_walk_through_single_vertex`** (line 2211): unchanged from manager turn 9 —
  it already derived from `lift_aux`, so closing `lift_aux` automatically closes it.

`lake build` ran clean (688/688 jobs). Three expected `sorry` warnings remain:

* `ISigmaSeparationMarginalization.lean:442` — row body, sub-task 5 target.
* `SigmaOpenWalkMarginalization.lean:2302` — `contract_sigmaOpen_walk_at_single_vertex`, sub-task 3 target.
* `SigmaOpenWalkMarginalization.lean:2350` — `isISigmaSeparated_marginalize_singleton_iff`, sub-task 4 target.

(The line numbers `:1076` / `:1124` in the turn-10 sorry-budget were the pre-2e file; after 2e
inserted ~1238 lines of new code, they drifted to `:2302` / `:2350`. Substantively unchanged.)

The lift direction is the harder of the two infrastructure halves measured by *time invested*
(5 sub-tasks, ~3 manager turns of decomposition pressure, several worker escalations). For the
contract direction, we now have:

* All upstream `marginalize_*` API additions from Sub-task 1 (`Section3_2/MarginalizationPreserves.lean`).
* All public `shrink_directed_walk` / `shrink_bifurcation_walk` / `bifurcation_walk_iff_no_length`
  / `directed_walk_iff_no_length` from Sub-task 1's promotion in `Section3_2/MarginalizationsCommute.lean`.
* Several private helpers in `SigmaOpenWalkMarginalization.lean` (lines 214 -- 787) that **may
  generalize / re-apply for contract** — particularly `not_isColliderAt_of_isBifurcation`
  (collider/bifurcation interaction, dual-direction applicable) and
  `nodeAt_mem_interior_support` (position tracking, fully generic).

### Decision: dispatch Sub-task 3 — a single worker for the contract direction

Strategy choice. **Single worker, comprehensive brief** (no pre-emptive helper decomposition).
Rationale:

1. **Sub-task 2's decomposition was reactive, not proactive.** The 2a/2b helper extraction was
   forced *after* two consecutive workers escalated on size. A single worker briefed with
   the strengthened-IH design and the helper API succeeded (sub-task 2e, ~1195 LoC in one
   session). Sub-task 3 should start from that baseline — extract sub-helpers internally if
   a sub-case grows past ~200 LoC, but don't pre-decompose.

2. **Contract is structurally dual to lift, with one extra hard sub-case.** The basic
   case-table (proof.tex:131--138) is mechanical given the shrink helpers; the unblockable
   rerouting (proof.tex:159--189) is the genuinely tricky piece. The worker can implement the
   straightforward case-table first and then attack the rerouting as a self-contained sub-task.

3. **Blocker B is less severe than initially feared.** The diagnostic's §B.2 worried that
   "longer runs through self-loops" required ad-hoc treatment. But `shrink_directed_walk` /
   `shrink_bifurcation_walk` accept *any-length* walks with interior in `W` and produce a
   single edge in `G.marginalize W` — they handle u-runs of arbitrary length uniformly. The
   LN's "single intermediate u" case-table specializes to length-2; the shrink helpers
   generalize it for free.

4. **Helper re-use from sub-task 2's helpers.**
   * Helper (1) `not_isColliderAt_of_isBifurcation` (line 214) gives "bifurcation walks have
     no interior colliders" — directly applicable to the contract direction's σ-openness
     verification of the lifted-from-bifurcation interior u-positions in π.
   * `nodeAt_mem_interior_support` (line 747) is fully reusable.
   * Helpers 2 -- 6 (lines 348 -- 485) are *forward* step-lift wrappers (`forward_step_to_walk_in_G`,
     etc.) -- they go from a single marg-edge to a G-walk. The contract direction needs the
     *backward* analogs: given a G-walk segment, produce a marg-edge. This dual is provided
     by `shrink_directed_walk` / `shrink_bifurcation_walk` themselves (no need to re-wrap).

### IH design for the contract direction

The natural IH parallels lift's strengthened IH:

```lean
private lemma contract_aux (G : CDMG α) {u : α} (huV : u ∈ G.V)
    (A B C : Set α) (huA : u ∉ A) (huB : u ∉ B) (huC : u ∉ C) :
    ∀ {a b : α} (π : Walk G a b),
      a ≠ u → b ≠ u →
      π.IsSigmaOpen C →
      (∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) →
    ∃ π' : Walk (G.marginalize {u}) a b,
      π'.IsSigmaOpen C ∧
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C)
```

(Optionally, with C4'-style strong conjuncts if the recursive case requires more.)

### Anticipated structural recursion shape

For the contract direction, the natural recursion is **not** simple structural recursion on `π`,
because contracting a u-run requires *looking ahead* past consecutive u-positions until the
next non-u position. Two viable strategies:

**(Strategy A) "Find the next non-u position" recursion.** Auxiliary recursion: given
`π : Walk G a b` with `a ≠ u`, return `(m, sπ', ρ)` where `m` is the first non-u position
after `a`, `sπ'` is the contracted edge from `a` to `m` in `G.marginalize {u}`, and `ρ` is the
remaining sub-walk from `m` to `b`. Then the outer recursion concatenates: `π' = cons sπ' (contract ρ)`.

* **Pro**: clean separation between "find the next non-u stretch" and "process the contracted walk".
* **Con**: needs a well-founded recursion (decreasing on `π.length`), not a simple structural one.

**(Strategy B) "Eager state-machine" recursion on `π` with an accumulator** tracking whether
we're currently mid-u-run. When we see a step that ends at non-u, emit the contracted edge from
the previous non-u position to this one (consuming the buffered u-run).

* **Pro**: closer to a simple structural recursion on `π`.
* **Con**: the accumulator type is non-trivial (`Walk G start_of_u_run a` where `a` is the
  current position).

Recommend **Strategy A** as it more closely mirrors the LN's proof structure ("for each pair
b_j, b_{j+1}, ..."). The worker can pick whichever feels more tractable.

### Unblockable rerouting (proof.tex:159 -- 189)

The hardest sub-case. Brief sketch for the worker:

When an unblockable non-collider b_j on π has an outgoing edge that goes to u (so to Sc^G(b_j)),
and we contract u away, the outgoing edge in π' goes to b_{j+1}. If b_{j+1} ∉ Sc^{G^{∖u}}(b_j),
then b_j may not be unblockable in π'. The LN's fix: insert a fresh hinge vertex w (successor of
u on the directed path back to b_j), and replace `b_j → b_{j+1}` by `b_j → w ↔ b_{j+1}`. This
makes w a collider with w ∈ Sc^{G^{∖u}}(b_j), and b_j has an outgoing edge to w ∈ Sc, so b_j is
unblockable.

This rerouting modifies the walk π' AFTER the initial contraction. So the contract proof has
two phases:

1. **Phase 1**: contract π to π'_0 using the shrink helpers and the basic case-table.
2. **Phase 2**: for each unblockable non-collider b_j on π'_0 whose outgoing edge violates the
   Sc-condition, apply the rerouting transform. This yields the final π'.

A clean way to organize this is: prove Phase 1 first as a "rough contraction" lemma, then prove
Phase 2 as a separate "rerouting" lemma, and compose.

### Brief for the Sub-task 3 worker

Single `spawn_agent_sub_task` dispatch, with these specifics:

* **File**: `leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean`,
  edit only the theorem `contract_sigmaOpen_walk_at_single_vertex` at line 2302 (and any new
  private helpers placed in the same file, between the lift theorem at line 2211 and the
  contract theorem at line 2302, or above line 798 in the "private helpers" zone).
* **Sorry budget after this task**: 2 (the row body at `:442` and the singleton-iff stub at
  `:2350`). The `:2302` warning must disappear.
* **Escalation rules tightened**: only escalate on genuinely new structural obstructions
  (analogous to sub-task 2d's "IH C4 insufficiency"). "This is large" is NOT a valid reason
  to escalate. Decompose into private sub-helpers within the file if a sub-case grows past
  ~200 LoC.

Dispatching the worker.

---

## Sub-task 3 worker turn 1 — 2026-05-28: structural escalation report

### Status: ESCALATING with a structural diagnostic

I am the Sub-task 3 worker dispatched by Manager B turn 11. After thorough analysis
of the LN's contract proof and the available Lean infrastructure, I have identified
a **genuinely new structural obstruction** in the LN's rerouting argument (proof.tex
lines 159 -- 189). This obstruction is **distinct from "size"** — it concerns the
formal correctness of the LN's hinge construction in a specific corner case.

### Work completed

**Helpers added to `SigmaOpenWalkMarginalization.lean`** (between lines 2255 and 2335,
~60 LoC, no new sorry's):

1. **`split_until_next_non_u`** (~30 LoC): strong-induction-on-length helper that takes
   a walk `p : Walk G u b` (starting at u, b ≠ u) and decomposes
   `p = τ.append ρ` where `τ : Walk G u m` is the maximal u-prefix (`τ.support.dropLast`
   all = u), `m ≠ u`, `τ.length ≥ 1`, and `ρ : Walk G m b` is the remainder. Used by
   the recursive `contract_aux` to peel off one u-segment at a time.

2. **`single_forward_to_marg_E`** (~15 LoC): given a single edge `(v, m) ∈ G.E` with
   `v, m ≠ u`, exhibits `(v, m) ∈ (G.marginalize {u}).E` via the single-step directed
   walk witness. Used by the non-u step contraction.

Both compile cleanly; `lake build` still has only 2 sorrys (`:442` and `:2350`), plus
the `:2302` we're trying to close. The helpers are positioned to be consumed by the
main `contract_aux` lemma.

### Structural obstruction: the LN's hinge L^{∖u} claim has a corner-case gap

#### The setup

In Phase 2 (rerouting), the LN considers an unblockable non-collider `b_j ∈ C` on `π`
whose contracted outgoing edge on `π'_0` no longer lands in `Sc^{G^{\sm u}}(b_j)`.
The LN's fix (proof.tex:159 -- 189) is to insert a hinge vertex `w` (the successor of
`u` on a directed path from `u` to `b_j` in `G`), replacing the contracted edge
`b_j → b_{j+1}` by **`b_j → w ↔ b_{j+1}`**.

The LN claims (proof.tex:172):

> The fork bifurcation `w ← u → b_{j+1}` yields `w ↔ b_{j+1} ∈ L^{∖u}`.

This requires `(w, b_{j+1}) ∈ (G.marginalize {u}).L`. By `mem_marginalize_L`
(`Section3_2/Marginalization.lean:597`), this is equivalent to four conjuncts:

* `w ∈ G.V \ {u}` ✓ (w is on a directed path through G, w ≠ u).
* `b_{j+1} ∈ G.V \ {u}` ✓ (`b_{j+1}` is a non-u vertex on π).
* `w ≠ b_{j+1}` ✓ (LN's "note w ≠ b_{j+1} since b_{j+1} ∉ Sc^G(b_j)").
* `¬ (∃ directed walk w → b_{j+1} with interior in {u})` — **may fail**.
* `¬ (∃ directed walk b_{j+1} → w with interior in {u})` — likely holds.
* `∃ bifurcation between w and b_{j+1} (in either direction) with interior in {u}` ✓
  (the fork `w ← u → b_{j+1}` is exactly this).

#### The corner case

The fourth conjunct **fails** when `(w, u) ∈ G.E`. In that case, the directed walk
`w → u → b_{j+1}` exists (using `(w, u) ∈ G.E` for the first step and `(u, b_{j+1}) ∈ G.E`
for the second), so `(w, b_{j+1}) ∉ L^{∖u}`, contradicting the LN's claim.

#### Concreteness of the corner case

The case `(w, u) ∈ G.E` is achievable: it occurs precisely when `u ↔ w` form a directed
2-cycle in `G`. Since both `(u, w) ∈ G.E` (the LN's definition of w) and (in the corner
case) `(w, u) ∈ G.E` are present, `u` and `w` are mutually directly reachable.

This 2-cycle scenario is **consistent with all of the LN's preconditions**:

* `u ∈ Sc^G(b_j)` ✓ (the 2-cycle, plus the path `w → ... → b_j`, gives `u → b_j` directed
  walks and `b_j → u` from τ_j's first step).
* `b_j → u ∈ E` ✓ (from τ_j's first step in the contraction case).
* `u → b_{j+1} ∈ E` ✓ (from τ_j's second step in the contraction case).
* `b_{j+1} ∉ Sc^G(b_j)` ✓ (the rerouting precondition — `b_{j+1}` is the
  problematic-contraction target).

Nothing in the LN's setup excludes `(w, u) ∈ G.E`.

#### Why the alternative ("use `(w, b_{j+1}) ∈ E^{∖u}` instead") doesn't trivially work

In the corner case, although `(w, b_{j+1}) ∉ L^{∖u}`, we still have
`(w, b_{j+1}) ∈ E^{∖u}` (via the very directed walk `w → u → b_{j+1}` that breaks the
`L^{∖u}` clauses). So we can use a **forward step `w → b_{j+1}`** instead of the LN's
bidir step.

But this creates a new issue: the contracted walk becomes `b_j → w (forward) → b_{j+1}
(forward)`, making `w` a **non-collider** (instead of a collider, as in the LN's
bidir construction).

For `w` to be σ-open on the new walk:

* If `w ∉ C`: blockable non-collider σ-open ✓ (vacuous since `w ∉ C`).
* If `w ∈ C`: must be **unblockable**, which requires
  `b_{j+1} ∈ Sc^{G^{\sm u}}(w) = Sc^G(w) \ {u}`.

But `b_{j+1} ∈ Sc^G(w)` is **not guaranteed by the LN's setup**:

* `b_{j+1} ∈ Desc^G(w)` ✓ (via `w → u → b_{j+1}`).
* `b_{j+1} ∈ Anc^G(w)`: requires a directed walk `b_{j+1} → ... → w` in G. **Not
  guaranteed**. In particular, `b_{j+1} ∉ Sc^G(b_j)` (the rerouting hypothesis)
  combined with `w ∈ Sc^G(b_j)` gives `Sc^G(w) ⊆ Sc^G(b_j)` (same SCC), and
  `b_{j+1} ∉ Sc^G(b_j)` forces `b_{j+1} ∉ Sc^G(w)`. So `b_{j+1} ∉ Sc^G(w)` in the
  corner case where `b_{j+1} ∉ Sc^G(b_j)`.

So the forward-step alternative also fails to give σ-open when `w ∈ C`.

#### Cannot route around by picking a different w

The LN's `w` is the successor of `u` on a directed path `u → ... → b_j`. We could in
principle pick a different path or a different `w` (e.g., a successor of `u` that is
not in the 2-cycle with `u`). But:

* If `u` has only one outgoing edge in `G.E` (to `w`), there's no choice — all
  paths from `u` start with `w`.
* If `u` has multiple outgoing edges but only one of them lies on an `Anc^G(b_j)`
  path (i.e., the other outgoing edges don't lead back to `b_j`), same issue.
* The LN doesn't argue that "good" choices of `w` always exist.

#### Severity classification

This is analogous to **Sub-task 2d's "IH C4 insufficiency"** in the sense that it
identifies a specific structural gap that the original LN argument does not address.
Unlike "this is large" (which the brief explicitly rules out as an escalation reason),
this is a **genuine new structural obstruction** that requires manager guidance:

* Either: confirm the LN's hinge argument is incomplete and provide a strengthened
  construction (e.g., a different choice of `w`, or a different rerouting pattern).
* Or: confirm that the `(w, u) ∈ G.E` corner case is somehow excluded by other
  invariants that I'm missing.

### Proposed paths forward

**(P1) Strengthen the rerouting construction.** Possibly: in the corner case
`(w, u) ∈ G.E`, instead of routing through `w`, route through a different vertex
or use a different combination of edges. E.g., if `u` and `w` are in a 2-cycle,
consider using `b_j ↔ w'` (via fork) where `w'` is some other ancestor of `b_j`
in `G.V \ {u, b_j}`. Whether such a `w'` always exists needs analysis.

**(P2) Strengthen the IH and bake rerouting into the recursion.** Instead of a
Phase 1 + Phase 2 split, do the rerouting upfront during the recursion. The IH
would carry, for each step, the SCC info needed to decide which construction to use.

**(P3) Weaken the contract direction's conclusion.** Currently the theorem requires
"all colliders in C". If we drop this and just produce a σ-open walk, then use
`sigmaOpens_TFAE` (`Section3_3/SigmaOpenPathWalk.lean:1453`) to upgrade — does this
sidestep the issue? Doesn't seem to: the rerouting issue is at the σ-open clause 2
(non-collider in C must be unblockable), not at the colliders-in-C clause.

**(P4) Use the path version of the input.** Extract a σ-open *path* (not just walk)
from π via `sigmaOpens_TFAE`. Paths have distinct vertices, so u appears at most
once. This simplifies the analysis to at most one u-segment, but doesn't eliminate
the rerouting corner case.

**(P5) Manager-designed strengthened IH for `contract_aux`** (analogous to
Sub-task 2d → 2e). The corner-case analysis above could be encoded into the IH
itself, so that the boundary verification can pick the right construction.

### Recommendation for next dispatch

A manager analysis of the (w, u) ∈ G.E corner case is needed. Specifically:

1. Confirm whether the corner case is genuinely problematic, or whether some
   other invariant excludes it.
2. If problematic, design either:
   * A modified rerouting strategy (potentially picking a different w), or
   * A strengthened IH that exposes enough info to handle this case during the
     recursion, analogous to `lift_aux_strong`'s C4-strong / C5.
3. Specify the LN extension needed (a careful analog of `lift_aux_strong`'s C4
   conjunct adapted for the contract direction).

I will not attempt the proof until this design is settled, to avoid producing
a faulty proof or hitting the same structural wall mid-way.

### Sorry budget after this turn

Same as before sub-task 3 dispatch: 3 sorrys (`:442`, `:2392` = the renumbered
`:2302` due to my added 60 lines of helpers, `:2438` = the renumbered `:2350`).

The two helpers (`split_until_next_non_u`, `single_forward_to_marg_E`) are
positioned at lines ~2257 -- ~2335 and will be consumed by the next worker's
`contract_aux` implementation.

---

## Sub-task 3 worker turn 1 — 2026-05-28: CRITICAL UPDATE — concrete counterexample found

### THE LN's LEMMA IS FALSE — concrete counterexample

While analyzing the rerouting obstruction, I constructed and verified a concrete
counterexample to `claim 3.25` itself. The LN's lemma
`lem:stability_separation_marginalization` does NOT hold for the case stated. The
mistake is in the (⇐) contract direction, specifically the rerouting argument.

`CLAUDE.md` explicitly notes: "If certain claims in the lecture notes do not hold,
we prove the negation of the claim. This could for example be a counter-example.
There does exist at least one claim in the lecture notes that is false, so don't
disregard this possibility entirely." Sub-task 3 may have hit this case.

### The counterexample

**Graph `G`**: `α = Fin 6` (or any 6-element type), labelled
`{v_0, b_j, u, w, b_{j+1}, v_n}`:
* `G.J = ∅`
* `G.V = {v_0, b_j, u, w, b_{j+1}, v_n}`
* `G.E = {(v_0, b_j), (b_j, u), (u, b_{j+1}), (b_{j+1}, v_n), (u, w), (w, u), (w, b_j)}`
* `G.L = ∅`

(All CDMG fields verified: `E ⊆ (J ∪ V) ×ˢ V` ✓, `L_irrefl` vacuous, `L_symm`
vacuous, `disjoint_JV` vacuous, `disjoint_EL` vacuous.)

**Parameters**: `A = {v_0}, B = {v_n}, C = {b_j, w}, D = {u}`.

Preconditions:
* `D ⊆ V` (`u ∈ V`) ✓
* `Disjoint D (A ∪ B ∪ C)` (`u ∉ {v_0, v_n, b_j, w}`) ✓

### The counterexample WITNESS

**Side 1: `¬ G.IsISigmaSeparated A B C`** — exhibit a σ-open walk.

Take `π = v_0 → b_j → u → b_{j+1} → v_n` (length 4, all forward steps).

Computation of relevant `Sc^G` sets:
* `Anc^G(b_j) = {v_0, b_j, u, w}` (`v_0 → b_j` direct; `u → w → b_j`; `w → b_j` direct).
* `Desc^G(b_j) = {b_j, u, w, b_{j+1}, v_n}` (via `b_j → u → ...`).
* `Sc^G(b_j) = {b_j, u, w}`.

σ-open verification on `π`:
* Position 0 (`v_0`): blockable endpoint. `v_0 ∉ C`. ✓
* Position 1 (`b_j`): forward in + forward out → non-collider. Unblockability check:
  step-out forward to `u`, target `u ∈ Sc^G(b_j)` ✓ — so unblockable, clause 2
  vacuous. (b_j ∈ C is OK because it's not blockable.)
* Position 2 (`u`): non-collider, blockable (target `b_{j+1} ∉ Sc^G(u)`). `u ∉ C`. ✓
* Position 3 (`b_{j+1}`): non-collider, blockable (`v_n ∉ Sc^G(b_{j+1})`). `b_{j+1} ∉ C`. ✓
* Position 4 (`v_n`): blockable endpoint. `v_n ∉ C`. ✓
* Colliders on `π`: none. "All colliders in `C`" vacuous. ✓

So `π` is `C`-σ-open in `G` with all colliders in `C`. Hence
`¬ G.IsISigmaSeparated A B C`.

**Side 2: `(G.marginalize {u}).IsISigmaSeparated A B C`** — show every walk in
marg from `v_0` to `v_n` is σ-blocked.

Computation: `E^{\sm u} = {(v_0, b_j), (b_j, b_{j+1}) [via b_j → u → b_{j+1}],
(b_j, w) [via b_j → u → w], (b_{j+1}, v_n), (w, b_j), (w, b_{j+1})
[via w → u → b_{j+1}], (w, w) [via w → u → w]}`. `L^{\sm u} = ∅` (`L = ∅` in G).

`Sc^{G^{\sm u}}(b_j) = Sc^G(b_j) \ {u} = {b_j, w}`.
`Sc^{G^{\sm u}}(w) = ... = {b_j, w}` (analogous).

For ANY walk `π'` from `v_0` to `v_n` in marg:
* The walk must end with a step into `v_n`. Only predecessor of `v_n` in `E^{\sm u}`
  is `b_{j+1}` (since `v_n` has no `E^{\sm u}`-or-`L^{\sm u}`-incoming edges from
  any other vertex). So the LAST step is forward `b_{j+1} → v_n`.
* The walk must reach `b_{j+1}` immediately before. Predecessors of `b_{j+1}` in
  `E^{\sm u}` are `b_j` and `w`. No `L`-edges, so no bidir reach. So the second-
  to-last vertex is `b_j` or `w`, with step type forward (`E^{\sm u}` from `b_j`
  or `w` to `b_{j+1}`).

In either case (penultimate vertex `b_j` or `w`), that vertex has an outgoing
forward step to `b_{j+1}`. For σ-open at that vertex:
* `b_j ∈ C` and `w ∈ C` (`C = {b_j, w}`), so neither is "blockable non-collider
  with `∉ C`"-σ-open.
* For collider: forward-out has `atSource = False`, so the step can't form a
  collider at this position (collider requires `atTarget ∧ atSource = True`).
* For unblockable: forward-out requires target `b_{j+1} ∈ Sc^{G^{\sm u}}(_)`,
  which fails for both `b_j` (`b_{j+1} ∉ {b_j, w}`) and `w` (same).

So at this penultimate position, σ-open clause 2 fails (blockable non-collider
in `C`). Hence EVERY walk from `v_0` to `v_n` in marg is σ-blocked.

So `(G.marginalize {u}).IsISigmaSeparated A B C`.

**Combined**: `¬ G.IsISigmaSeparated A B C` AND `(G.marg{u}).IsISigmaSeparated A B C`.
The iff `G.IsISigmaSeparated A B C ↔ (G.marg{u}).IsISigmaSeparated A B C`
**fails**.

### Why the LN's argument breaks

The LN's contract direction (proof.tex:106 -- 190) constructs `π'` by contracting
each maximal `u`-run, with Phase 2 rerouting via a hinge vertex `w` to repair
broken unblockable non-colliders. In my counterexample:

* Phase 1 produces `π'_0 = v_0 → b_j → b_{j+1} → v_n` (forward direct contraction
  of the `b_j → u → b_{j+1}` segment). `b_j` is blockable on `π'_0` with `b_j ∈ C`
  — broken.
* Phase 2 rerouting: take hinge `w` = successor of `u` on a directed path
  `u → ... → b_j`. In my graph, `u`'s only outgoing edge to `Anc^G(b_j)`-vertices
  is `u → w` (the `(w, b_j)` direct edge gives the path `u → w → b_j`). So `w`
  is forced. We have `w ∈ Sc^G(b_j) \ {u} = {b_j, w}` (✓ the LN's claim).
* LN's hinge construction: replace `b_j → b_{j+1}` (forward) by
  `b_j → w → ↔ b_{j+1}` (forward then bidir). The bidir `w ↔ b_{j+1}` requires
  `(w, b_{j+1}) ∈ L^{\sm u}`, which requires "no directed walk `w → b_{j+1}`
  through `u`". But `(w, u) ∈ G.E` AND `(u, b_{j+1}) ∈ G.E`, so the directed walk
  `w → u → b_{j+1}` exists, breaking the `L^{\sm u}` clause.
* Alternative: use `(w, b_{j+1}) ∈ E^{\sm u}` via the directed walk
  `w → u → b_{j+1}`, giving forward step `w → b_{j+1}`. New `π' = v_0 → b_j → w
  → b_{j+1} → v_n`. But now `w` is a non-collider in the walk with outgoing
  forward to `b_{j+1}`, requiring `b_{j+1} ∈ Sc^{G^{\sm u}}(w) = {b_j, w}` —
  again fails. And `w ∈ C`, so `w` is blockable non-collider in `C` — σ-blocked.

I have verified (above) that NO walk from `v_0` to `v_n` in marg is σ-open.

### Recommendation

The LN's lemma `lem:stability_separation_marginalization` is **wrong** (it doesn't
hold under the stated preconditions). The CLAUDE.md anticipates this possibility
and instructs: "we prove the negation of the claim".

**Recommended action for the manager**:

1. **Confirm the counterexample** by:
   * Manually re-checking the σ-open verification on `π` in `G` (done above).
   * Manually re-checking the σ-blocked status of every walk in marg from `v_0`
     to `v_n` (done above).
   * Building the same graph in Lean and running it through the formal
     `IsISigmaSeparated` definition.

2. **Replan the row**:
   * `claim_3_25` should be **disproven**, not proven.
   * The Lean statement at `ISigmaSeparationMarginalization.lean:442` needs to
     be changed from `iff` to `¬ iff` (or restructured to capture the
     counterexample).
   * Sub-task 3 (this task: prove contract direction) is no longer applicable
     as currently scoped.
   * Sub-task 4 (singleton iff) is similarly affected.
   * Sub-task 5 (outer reduction over `D`) is also affected.

3. **Alternative**: identify additional preconditions that would make the lemma
   true (e.g., acyclicity, or restricting `D` to vertices that aren't in any
   2-cycle with their parents). The LN as stated doesn't include any such
   additional preconditions, so this would diverge from the LN.

### Two helpers retained in the file

The two helpers I wrote (`split_until_next_non_u`,
`single_forward_to_marg_E`) are correct lemmas about CDMG walks regardless of
whether the contract direction is true. They're at lines ~2257 -- ~2335 and
compile cleanly. They may be useful for other claims or as documentation. They
add no new `sorry`s.

### Sorry count

Unchanged from before sub-task 3: 3 `sorry`s total
(`ISigmaSeparationMarginalization.lean:442`,
`SigmaOpenWalkMarginalization.lean:2381` (= old `:2302`),
`SigmaOpenWalkMarginalization.lean:2429` (= old `:2350`)).

`lake build` passes (688/688 jobs). No new `sorry`s introduced.

## Independent verifier turn — 2026-05-28

### Verdict
**[COUNTEREXAMPLE VALID]** — the Lean theorem
`Causality.CDMG.isISigmaSeparated_marginalize_iff` at
`ISigmaSeparationMarginalization.lean:442` is **false** under the
current Lean encoding of `CDMG.marginalize`.

The LN's lemma `lem:stability_separation_marginalization` may be true
in the LN's own framework (where directed and bidirected edges are
disjoint *types* of objects), but our Lean encoding's `disjoint_EL`
constraint forces `(u, v) ∈ E^{\sm W}` and `(u, v) ∈ L^{\sm W}` to be
mutually exclusive — and the LN's proof of claim_3_25 silently relies
on a bidirected edge surviving alongside a directed walk on the same
pair, which our encoding strips out.

### Method used
**Option II (exhaustive pen-and-paper)**. I did *not* attempt Option I
because `IsISigmaSeparated` is a universal quantifier over `Walk
(G.marginalize {u}) v_0 v_n`, which admits arbitrarily-long walks
revisiting the `(w, w)` self-loop; no `Decidable` instance exists and
synthesising one is out-of-scope. I redid the case analysis
independently from the worker, then confirmed convergence on the same
verdict.

### Predicate semantics confirmed from the source

I read the following Lean files to anchor every claim:

* `Section3_1/CDMG.lean:119-141` -- `E` carries **no irreflexivity
  field**; only `L_irrefl` rules out bidirected self-loops. So `(w, w)
  ∈ G.E` is permissible. ✓
* `Section3_3/BlockableAndUnblockable.lean:265-269` --
  `IsUnblockableJoint (s : WalkStep G a b) (s' : WalkStep G b c)` is
  ```
  (¬ (s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource)) ∧
  (s.IsBackward → a ∈ G.Sc b) ∧
  (s'.IsForward → c ∈ G.Sc b)
  ```
  i.e. *for a forward-in, forward-out non-collider, only the forward-out
  target matters for unblockability* (the backward-clause is vacuous on
  a forward step). ✓
* `Section3_3/BlockableAndUnblockable.lean:545-546` --
  `IsBlockableNonColliderAt k := IsNonColliderAt k ∧ ¬
  IsUnblockableNonColliderAt k`. End-positions ($k = 0$, $k = \pi.\text{length}$)
  are always blockable non-colliders (`isBlockableNonColliderAt_zero`,
  `isBlockableNonColliderAt_length`).
* `Section3_3/CollidersAndNon.lean:189-195` -- `IsColliderAt`, at the
  joint, is `s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource`. Forward
  has arrowhead-at-target only; backward has arrowhead-at-source only;
  bidir has both.
* `Section3_3/SigmaBlockedWalks.lean:426-428` -- `IsSigmaOpen π C` is
  the conjunction `(∀ k, IsColliderAt → nodeAt ∈ AncSet C) ∧ (∀ k,
  IsBlockableNonColliderAt → nodeAt ∉ C)`. ✓
* `Section3_3/ISigmaSeparation.lean:351-352` -- `IsISigmaSeparated G A
  B C := ∀ ⦃v w⦄, v ∈ A → w ∈ G.J ∪ B → ∀ (π : Walk G v w),
  π.IsSigmaBlocked C`. ✓
* `Section3_2/Marginalization.lean:517-551`, esp. `L^{\sm W}`'s two
  *exclusion clauses* `¬ ∃ π : Walk G p.1 p.2, π.IsDirected ∧
  π.InteriorIn W` and the analogous `Walk G p.2 p.1` clause. **This is
  the load-bearing deviation from the LN.** ✓

The Lean marginalize design block at
`Section3_2/Marginalization.lean:373-425` openly acknowledges this
deviation but claims it is benign at the "bifurcation existence"
level. The deviation is **not** benign at the σ-separation level: the
σ-open analysis needs the *arrowhead structure* of the bidirected
hinge edge, not just the existence of a bifurcation walk.

### Side 1 verification (¬ G.IsISigmaSeparated A B C)

The walk `π = v_0 → b_j → u → b_{j+1} → v_n` in `G` (all forward,
length 4).

`v_0 ∈ A = {v_0}` ✓. `v_n ∈ G.J ∪ B = ∅ ∪ {v_n} = {v_n}` ✓. So `π`
witnesses the universal in `IsISigmaSeparated` iff `π.IsSigmaBlocked
C`. Equivalent (via `isSigmaBlocked_iff_not_isSigmaOpen`) to showing
`π.IsSigmaOpen C`.

**Sc computations in `G`** (verified from scratch):
* `Anc^G(b_j)`: predecessors `v_0` (direct), `w` (direct), `u`
  (via `u → w → b_j`). Plus `b_j` (reflexive). $= \{v_0, b_j, u,
  w\}$.
* `Desc^G(b_j)`: `b_j → u → \{w, b_{j+1}\}`; `b_{j+1} → v_n`; `w → \{u,
  b_j\}` (cycle into existing). $= \{b_j, u, w, b_{j+1}, v_n\}$.
* `Sc^G(b_j) = Anc \cap Desc = \{b_j, u, w\}`.
* `Anc^G(u) = \{v_0, b_j, w, u\}`; `Desc^G(u) = \{u, b_{j+1}, v_n, w,
  b_j\}`; `Sc^G(u) = \{b_j, w, u\}`.
* `Anc^G(b_{j+1}) = \{v_0, b_j, u, w, b_{j+1}\}`;
  `Desc^G(b_{j+1}) = \{b_{j+1}, v_n\}`; `Sc^G(b_{j+1}) = \{b_{j+1}\}`.

**Per-position σ-open verification on `π`:**

| Position | Vertex     | Step-in / out                        | Status                                          | σ-open at this position? |
|----------|------------|---------------------------------------|--------------------------------------------------|--------------------------|
| 0        | `v_0`      | (endpoint)                            | blockable non-collider (auto)                    | `v_0 ∉ C` ✓             |
| 1        | `b_j`      | forward in (from `v_0`); forward out to `u` | non-collider; `u ∈ Sc^G(b_j) = {b_j, u, w}` → **unblockable** | trivially ✓ (blockable-conjunct vacuous) |
| 2        | `u`        | forward in; forward out to `b_{j+1}`  | non-collider; `b_{j+1} ∉ Sc^G(u) = {b_j, w, u}` → blockable | `u ∉ C = {b_j, w}` ✓   |
| 3        | `b_{j+1}`  | forward in; forward out to `v_n`      | non-collider; `v_n ∉ Sc^G(b_{j+1}) = {b_{j+1}}` → blockable | `b_{j+1} ∉ C` ✓        |
| 4        | `v_n`      | (endpoint)                            | blockable non-collider (auto)                    | `v_n ∉ C` ✓             |

**No colliders:** all 4 steps are forward, so for every interior
position the `step_in.HasArrowheadAtTarget ∧
step_out.HasArrowheadAtSource` is `True ∧ False = False`. The
"colliders are in `Anc^G(C)`" universal is vacuous.

So `π.IsSigmaOpen C` holds, hence `π.IsSigmaBlocked C` is **false**
(by `isSigmaBlocked_iff_not_isSigmaOpen`), hence `¬
G.IsISigmaSeparated A B C`. ✓ Side 1 confirmed.

### Side 2 verification ((G.marg{u}).IsISigmaSeparated A B C)

#### 2a. Compute `E^{\sm u}` and `L^{\sm u}` carefully

By `mem_marginalize_E`, `(p.1, p.2) ∈ E^{\sm u}` iff `p.1 ∈ G.J ∪
(G.V \ {u})`, `p.2 ∈ G.V \ {u}`, and there's a directed `Walk G p.1
p.2` with interior in `{u}` and length ≥ 1.

Enumerating directed walks in `G` with interior in `{u}`:

* Length 1 (no interior): the original `G.E` edges whose endpoints
  are both in `V \ {u}`: `(v_0, b_j)`, `(b_{j+1}, v_n)`, `(w, b_j)`.
* Length 2 (`x → u → y` with `(x, u), (u, y) ∈ G.E`):
  - `(x, u)` candidates: `(b_j, u)`, `(w, u)`. So `x ∈ {b_j, w}`.
  - `(u, y)` candidates: `(u, b_{j+1})`, `(u, w)`. So `y ∈ {b_{j+1},
    w}`.
  - Cartesian pairs `(x, y)` with `x, y ∈ V \ {u}`: `(b_j,
    b_{j+1})`, `(b_j, w)`, `(w, b_{j+1})`, `(w, w)`. All ✓.
* Length 3+ through `u` repeated: interior would need to contain
  vertices `u, ?, u, ...`, and the `?` must be in `{u}`. But `(u, u)
  ∉ G.E`, so a 3-step walk `x → u → ? → y` through `u` has `? ∈
  {b_{j+1}, w}` (successors of `u`), neither of which is in `{u}`.
  So no length ≥ 3 walks add new entries.

So `E^{\sm u} = \{(v_0, b_j), (b_{j+1}, v_n), (w, b_j), (b_j,
b_{j+1}), (b_j, w), (w, b_{j+1}), (w, w)\}`. ✓ (Worker's claim
verified.)

For `L^{\sm u}`: by `mem_marginalize_L`, need `(p.1, p.2)` with both
endpoints in `V \ {u}`, `p.1 ≠ p.2`, NO directed walk with interior
in `{u}` in either direction, AND ∃ bifurcation walk with interior
in `{u}` in either direction.

`G.L = ∅`. Bifurcation walks in `G` with interior in `{u}`:
* Length 1 (single backward step from `(a, b) ∈ G.E` read as
  backward `b → a`): a single backward step is a bifurcation
  (witness with `leftArm = nil`, `hinge = backward`, `rightArm =
  nil`, `v ≠ w`). Bifurcations of pairs in `V \ {u}`: from `(v_0,
  b_j)` → bifurc Walk G b_j v_0; from `(b_{j+1}, v_n)` → bifurc Walk
  G v_n b_{j+1}; from `(w, b_j)` → bifurc Walk G b_j w. *But* these
  pairs all have a directed walk in *one* direction with empty
  interior in `{u}` (the original `G.E` edge), so the corresponding
  `L^{\sm u}` exclusion fires and these pairs are excluded from
  `L^{\sm u}`.
* Length 2 with middle vertex `u`:
  - `a ← u ← b` (both backward): bifurc with `leftArm = first
    backward`, `hinge = second backward`. Requires `(u, a), (b, u)
    ∈ G.E`. Pairs: `(b_{j+1}, b_j)`, `(b_{j+1}, w)`, `(w, b_j)`
    (after excluding `(w, w)` by `v ≠ w`).
  - `a ← u → b` (fork, "backward then forward"): bifurc with
    `leftArm = nil`, `hinge = first backward`, `rightArm = second
    forward`. Requires `(u, a), (u, b) ∈ G.E`. Pairs: `(b_{j+1},
    w)`, `(w, b_{j+1})`.
  - `a → u → b` (both forward): NOT a bifurcation -- no hinge step
    has `HasArrowheadAtSource = True` (forward has
    `HasArrowheadAtSource = False`).
  - `a → u ← b` (collider at `u`): NOT a bifurcation -- the hinge
    would need to be one of the two steps, but a forward step has
    no arrowhead-at-source.

Now check the exclusion clause for each candidate pair:

* `(b_{j+1}, b_j)`: bifurc exists. But directed walk `b_j → u →
  b_{j+1}` with interior `{u}` exists, so the exclusion clause for
  `Walk G p.2 p.1` (i.e. `Walk G b_j b_{j+1}`) fires. Excluded.
* `(b_{j+1}, w)` and `(w, b_{j+1})`: bifurc exists in both walk
  directions. But directed walk `w → u → b_{j+1}` with interior
  `{u}` exists, so the exclusion clause fires. Excluded.
* `(w, b_j)` / `(b_j, w)`: bifurc exists. But directed walk `b_j →
  u → w` (and `w → b_j` direct, and `b_j → u → b_j`... wait,
  actually `w → b_j` direct from `G.E`) exist. Exclusion fires.
  Excluded.

So `L^{\sm u} = ∅`. ✓ (Worker's claim verified.)

#### 2b. `Sc^{G^{\sm u}}` and `Anc^{G^{\sm u}}(C)` computations

* `Anc^{G^{\sm u}}(b_j)`: predecessors in `E^{\sm u}` are `(v_0,
  b_j)`, `(w, b_j)` → `v_0`, `w`. Plus `b_j` reflexive. Predecessors
  of `w` in `E^{\sm u}`: `(b_j, w)`, `(w, w)` → `b_j`, `w`. So
  `Anc^{G^{\sm u}}(b_j) = \{v_0, w, b_j\}`.
* `Desc^{G^{\sm u}}(b_j)`: `b_j` (reflexive); `(b_j, b_{j+1})` →
  `b_{j+1}`; `(b_j, w)` → `w`; from `b_{j+1}`: `(b_{j+1}, v_n)` →
  `v_n`; from `w`: `(w, b_j), (w, b_{j+1}), (w, w)` → all already
  in. `Desc^{G^{\sm u}}(b_j) = \{b_j, b_{j+1}, w, v_n\}`.
* `Sc^{G^{\sm u}}(b_j) = \{v_0, w, b_j\} \cap \{b_j, b_{j+1}, w,
  v_n\} = \{b_j, w\}`. ✓
* By symmetry of the SCC argument:
  - `Anc^{G^{\sm u}}(w) = \{v_0, w, b_j\}`.
  - `Desc^{G^{\sm u}}(w) = \{w, b_j, b_{j+1}, v_n\}`.
  - `Sc^{G^{\sm u}}(w) = \{w, b_j\}`. ✓
* `Sc^{G^{\sm u}}(b_{j+1})`: outgoing edges from `b_{j+1}`:
  `(b_{j+1}, v_n)` only. `Desc(b_{j+1}) = \{b_{j+1}, v_n\}`.
  `Anc(b_{j+1})`: predecessors `(b_j, b_{j+1}), (w, b_{j+1})` →
  `b_j, w`, etc., yielding `\{v_0, b_j, w, b_{j+1}\}`. `Sc^{G^{\sm
  u}}(b_{j+1}) = \{b_{j+1}\}`. ✓
* `AncSet^{G^{\sm u}}(C) = Anc(b_j) \cup Anc(w) = \{v_0, w, b_j\}`.

Crucially:
* `b_{j+1} ∉ Sc^{G^{\sm u}}(b_j) = \{b_j, w\}`.
* `b_{j+1} ∉ Sc^{G^{\sm u}}(w) = \{w, b_j\}`.
* `v_n ∉ AncSet^{G^{\sm u}}(C) = \{v_0, w, b_j\}`.

#### 2c. Case analysis for any walk from `v_0` to `v_n` in `G^{\sm u}`

**The walk must start `v_0 → b_j` (forward).** Outgoing from `v_0` in
`marg`-steps:
* forward: `(v_0, b_j) ∈ E^{\sm u}` → to `b_j`.
* backward: requires `(_, v_0) ∈ E^{\sm u}`. None.
* bidir: `L^{\sm u} = ∅`.

So position 1 = `b_j`, with `step_0 = forward`.

**The walk must end `b_{j+1} → v_n` (forward).** Incoming to `v_n`:
* forward: `(_, v_n) ∈ E^{\sm u}` → only `(b_{j+1}, v_n)`. So from
  `b_{j+1}` forward.
* backward: requires `(v_n, _) ∈ E^{\sm u}`. None.
* bidir: `L^{\sm u} = ∅`.

So position `n-1 = b_{j+1}`, with `step_{n-1} = forward`.

**Step into position `n-1 = b_{j+1}`** (i.e., `step_{n-2}`):
* forward from `(_, b_{j+1}) ∈ E^{\sm u}` → from `b_j` or `w`.
* backward from `(b_{j+1}, _) ∈ E^{\sm u}` → only `(b_{j+1}, v_n)`,
  so backward from `v_n`.
* bidir: none.

So `v_{n-2} ∈ \{b_j, w, v_n\}`. Three subcases.

**Subcase A (v_{n-2} = b_j):** `step_{n-2}` is `forward b_j →
b_{j+1}` (no backward to `b_{j+1}` since `(b_{j+1}, b_j) ∉ E^{\sm
u}`; no bidir).

At position `n-2 = b_j`: step-out is forward (`HasArrowheadAtSource
= False`). Collider check: `step_{in}.HasArrowheadAtTarget ∧ False =
False`. So **non-collider** regardless of step-in. Unblockable joint
check: `s'.IsForward → b_{j+1} ∈ Sc^{G^{\sm u}}(b_j) = \{b_j, w\}`?
**NO**. So **blockable non-collider**. `b_j ∈ C = \{b_j, w\}`. So
position `n-2` is a blockable non-collider in `C` → **σ-blocked**.

**Subcase B (v_{n-2} = w):** `step_{n-2}` is `forward w → b_{j+1}`
(symmetric to A; backward and bidir to `b_{j+1}` from `w` are not in
`E^{\sm u} \cup L^{\sm u}`).

At position `n-2 = w`: same argument as A. `b_{j+1} ∉ Sc^{G^{\sm
u}}(w) = \{w, b_j\}`, so blockable non-collider. `w ∈ C`. **σ-blocked**.

**Subcase C (v_{n-2} = v_n):** `step_{n-2}` is `backward v_n →
b_{j+1}` (the only step from `v_n` to `b_{j+1}` is backward via
`(b_{j+1}, v_n)`).

The step *into* `v_n` (i.e., `step_{n-3}`) must come from somewhere.
Predecessors of `v_n` in marg-edges: forward from `b_{j+1}` only;
no backward; no bidir. So `step_{n-3}` is forward from `b_{j+1}`.

At position `n-2 = v_n`: step-in forward
(`HasArrowheadAtTarget = True`), step-out backward
(`HasArrowheadAtSource = True`). **Collider**. σ-open as collider
requires `v_n ∈ AncSet^{G^{\sm u}}(C) = \{v_0, w, b_j\}`. **NO**.
**σ-blocked**.

**Conclusion: in all three subcases, the walk is σ-blocked at some
position `n-2`.**

#### 2d. Why no clever revisiting saves the day

The above argument is *local* to the final two steps of the walk,
independent of the walk's earlier structure. The blocking happens at
the step-out from the third-from-last vertex (Subcase A or B) or at
the second-from-last vertex's collider status (Subcase C). The
walk's history before that does not matter — the trap closes on the
final approach.

In particular, the `(w, w)` self-loop, repeated visits to `b_j` or
`w`, detours through `v_n` and back, etc., do not produce a σ-open
walk. The combinatorial obstruction is exactly:

> *The only "useful" edges out of `\{b_j, w\}` toward `b_{j+1}` are
> forward, and `b_{j+1} \notin Sc^{G^{\sm u}}(\{b_j, w\}) = \{b_j,
> w\}` is the load-bearing fact. The vertex `b_{j+1}` lies in its
> own SCC singleton because `(b_{j+1}, w), (b_{j+1}, b_j) \notin
> E^{\sm u}` (there's no walk `b_{j+1} → ⋯ → \{b_j, w\}` through
> `\{u\}`; the only walk from `b_{j+1}` is `(b_{j+1}, v_n)`).*

So `(G.marginalize \{u\}).IsISigmaSeparated A B C` holds. ✓ Side 2
confirmed.

### LN proof analysis — where the argument breaks

**The LN's proof of (⇐) at line 172 of
`claim_3_25_proof_ISigmaSeparation.tex` (= `graphs.tex:1559`)
claims:**

> *The fork bifurcation `w ← u → b_{j+1}` yields `w ↔ b_{j+1} ∈
> L^{\sm u}`.*

**This step is incorrect under the Lean encoding of marginalize.**

In our Lean `CDMG.marginalize`, the `L^{\sm W}` set has *two
exclusion clauses* (`Section3_2/Marginalization.lean:532-533`):

```lean
(¬ ∃ π : Walk G p.1 p.2, π.IsDirected ∧ π.InteriorIn W) ∧
(¬ ∃ π : Walk G p.2 p.1, π.IsDirected ∧ π.InteriorIn W) ∧
```

A pair `(p.1, p.2)` enters `L^{\sm W}` only if *no* directed walk
exists in either direction through `W`. For our counterexample with
`p.1 = w`, `p.2 = b_{j+1}`, `W = \{u\}`:

* The directed walk `w → u → b_{j+1}` (forward forward, interior
  `\{u\}`, length 2) exists.

This walk witnesses `(w, b_{j+1}) ∈ E^{\sm u}`, and *also* — by the
exclusion clause — kicks `(w, b_{j+1})` out of `L^{\sm u}`. So the
LN-asserted `w ↔ b_{j+1} ∈ L^{\sm u}` is **false in our Lean
encoding**.

**The LN's proof in the LN's framework is correct,** because the LN
treats `E` and `L` as *different types of objects* (LN def 3.1
writes `E ⊆ (J ∪ V) × V` and `L ⊆ V × V / ((v_1, v_2) ∼ (v_2,
v_1))` — *different ambient types*), so a pair `(w, b_{j+1})` *can*
be both a directed `E^{\sm u}`-edge and a bidirected `L^{\sm
u}`-edge in the LN's `G^{\sm u}`.

The deviation is openly documented in the Lean marginalize design
block (`Section3_2/Marginalization.lean:373-425`), which claims the
deviation is "purely syntactic at the `L^{\sm W}` membership level"
and that bifurcation existence is preserved via reading directed
walks reversed as all-backward bifurcation walks. **That claim is
correct at the *existence* level but wrong at the *arrowhead
structure* level.**

The LN's rerouted walk
`b_j → w ↔ b_{j+1} → v_n` (with hinge step `w ↔ b_{j+1}` bidirected)
makes `w` a **collider** (because the bidirected step has
`HasArrowheadAtSource = True`), and `w ∈ Sc^{G^{\sm u}}(b_j) ⊆
Anc^{G^{\sm u}}(C)` (since `b_j ∈ C`), so `w` is σ-open as a
collider in `Anc(C)`.

In our Lean encoding, the rerouted walk must use the forward step
`w → b_{j+1}` (from `(w, b_{j+1}) ∈ E^{\sm u}`) instead. This makes
`w` a **non-collider** (forward step out has `HasArrowheadAtSource =
False`), and the unblockable joint check `b_{j+1} ∈ Sc(w) = \{w,
b_j\}` **fails**. So `w` becomes a *blockable* non-collider, and `w
∈ C` makes the rerouted walk **σ-blocked at `w`**.

The same obstruction kills every other rerouting attempt — see
Side 2's case analysis.

### Worker error analysis

The worker's argument is **correct**. The only nit is at the
end-of-the-walk case analysis ("Side 2" in the worker's
write-up). The worker's "Case A: third-to-last ∈ {b_j, w}, forward
to b_{j+1}, blockable non-collider in C → σ-blocked" and "Case B:
position n-2 = v_n with forward-in (from b_{j+1}) and backward-out
(to b_{j+1}) = collider, v_n ∉ C → σ-blocked" exactly match my own
recomputation. The worker correctly identified `Sc^{G^{\sm u}}(b_j)
= Sc^{G^{\sm u}}(w) = \{b_j, w\}` and `Sc^{G^{\sm u}}(b_{j+1}) =
\{b_{j+1}\}` as the load-bearing facts. The worker also correctly
identified the LN's line 172 ("The fork bifurcation `w ← u →
b_{j+1}` yields `w ↔ b_{j+1} ∈ L^{\sm u}`") as the breaking step.

I have no corrections to the worker's analysis.

### A subtle point: is this a "LN mistake" or a "Lean encoding mistake"?

This is **not** a mistake in the LN itself — the LN's proof works in
the LN's own framework (where `E` and `L` are disjoint *types*, so a
pair can be both a directed and a bidirected edge). The mistake is
in our **Lean encoding's `disjoint_EL` design choice** plus the
**`L^{\sm W}` exclusion clauses in `CDMG.marginalize`**.

The `Marginalization.lean` design block at lines 373-425 explicitly
flags this deviation but errs in claiming it's benign: the deviation
*is* observable in σ-separation proofs, because σ-separation tracks
the *arrowhead structure* of walk steps, not just bifurcation
existence.

**Implications for the manager.** Two paths forward:

1. **Path A (proceed with `mistake` action):** prove the Lean
   statement is false (via the counterexample). The Lean theorem
   statement becomes its negation. Downstream consumers (chapters
   5-16) that need the LN's true result will not be able to use
   this row; they will need an analog that either uses a corrected
   `CDMG.marginalize` or carries extra hypotheses (e.g.
   `Acyclic G`).

2. **Path B (refactor `CDMG.marginalize`):** change the `L^{\sm W}`
   definition to drop the exclusion clauses, accepting that
   `disjoint_EL` must then be dropped from `def_3_1.CDMG` itself.
   This is a **deep refactor** affecting `CDMG`, every claim in
   Section 3.2 that consumes the current `marginalize`, the
   `mem_marginalize_L` simp lemma, and so on. The cost is high; the
   payoff is the LN's lemma becomes true.

My recommendation, as verifier, is **Path A is correct given the
"prove the negation of false claims" rule in `claude.md`** — but the
manager should pause to consider whether the encoding is what we
intended in the first place. The author of the marginalize design
block argued for the exclusion clauses on the grounds of "preserves
bifurcation existence"; that grounds is correct but doesn't extend
to σ-separation proofs. The deeper LN-faithfulness question is:
should `def_3_1.CDMG` carry `disjoint_EL` at all? The LN's def 3.1
does say "two (disjoint) sets of edges", so yes; but then the LN's
def 3.14 (marginalize) silently violates the disjointness when both
existentials happen to fire on the same pair, which the LN
sidesteps by treating `E` and `L` as different sorts. The Lean
encoding's `Set (α × α)` form for both forces the disjointness
explicitly. That's the root cause.

**This is a `mistake` row given Path A, but it is a row whose
mistake-status is a *Lean-encoding* artifact, not a *content*
mistake of the LN.** Future manager turns should weigh whether the
high-cost Path B refactor of `CDMG.marginalize` is worth it before
locking in Path A.

### Confidence

**High** on the verdict (`COUNTEREXAMPLE VALID`).

* The Side 1 σ-open verification is a finite checklist of 5
  positions and a Sc computation; I cross-checked the worker's Sc
  computation independently and they match.
* The Side 2 case analysis exhausts the three cases for `v_{n-2}`
  determined by edge structure of `marg` plus `L^{\sm u} = ∅`. Each
  case is σ-blocked. The "no clever revisiting saves the day"
  argument is *local* to the final two steps, so walk-length /
  walk-revisits cannot matter.
* The LN-breaks-at-line-172 conclusion is straightforward once the
  `L^{\sm u}` exclusion clauses are understood. The deviation is
  pre-documented in the Lean marginalize file's design block — so
  no surprise that the LN's bidir-driven rerouting argument fails.
* I did not attempt Option I (Lean `decide`) because
  `IsISigmaSeparated` has no `Decidable` instance and the task
  forbids adding one. This is the only "softness" in the verdict.
  But the analysis is finite-checkable by hand and I am confident.

**Medium** on the *broader interpretation* (whether the row should
proceed via `mistake` or via a marginalize refactor): see the
"subtle point" section above. The manager should weigh both paths;
my verifier role is only to confirm the false-ness of the Lean
statement.

### Caveats

* I have not verified that the Lean `CDMG.marginalize_marginalize`
  (claim_3_17), `marginalize_anc_iff`, `marginalize_bifurcation_iff`
  (claim_3_16) are themselves correctly stated/proven under the
  current marginalize encoding. If the marginalize encoding is
  flawed, these prior rows may also need revisiting; that's
  out-of-scope for this verification turn.
* The exclusion-clause issue may also affect *upstream* rows
  (claim_3_17, claim_3_18, claim_3_19) silently; the verifier did
  not check.
* If the manager decides on Path B (refactor marginalize), this
  verification's verdict becomes moot — under a fixed marginalize,
  the LN's proof goes through and the lemma is true.

### Sub-task 5: tex proof of negation -- 2026-05-28

- **Proof file**: `leanification/Chapter3_GraphTheory/Section3_3/tex/claim_3_25_proof_ISigmaSeparation.tex` (459 lines total; framing + restated `\begin{Lem}` block at lines 1--33 untouched, new `\begin{proof}` body at lines 36--457).
- **What the negation proves**: there exists a CDMG `G` on six vertices `{v_0, b_j, u, w, b_{j+1}, v_n}` with `E = {(v_0,b_j),(b_j,u),(u,b_{j+1}),(b_{j+1},v_n),(u,w),(w,u),(w,b_j)}` and `L = ∅` such that with `A = {v_0}`, `B = {v_n}`, `C = {b_j, w}`, `D = {u}` (disjointness `D ∩ (A ∪ B ∪ C) = ∅` holds): `¬ (A ⊥_G B | C)` (witnessed by the σ-open walk `v_0 → b_j → u → b_{j+1} → v_n`, with `b_j` unblockable via `u ∈ Sc^G(b_j)`) AND `(A ⊥_{G^{∖u}} B | C)` (every walk from `v_0` to `v_n` is σ-blocked at the penultimate vertex, by exhaustive case analysis).
- **LN error cited**: the LN's proof at `graphs.tex:1559` (= line 172 of the prior version of the proof file) asserts that the fork bifurcation `w ← u → b_{j+1}` yields `w ↔ b_{j+1} ∈ L^{∖u}`. Under the Lean encoding of marginalization (`Section3_2/Marginalization.lean:530--535`), `L^{∖u}` excludes pairs already supplied by a directed walk through `u`; the directed walk `w → u → b_{j+1}` (length 2, interior `{u}`) forces `(w, b_{j+1}) ∈ E^{∖u}`, hence `(w, b_{j+1}) ∉ L^{∖u}`, and the LN's rerouting step is unavailable.
- **Structure of the proof file** (subparagraph offsets relative to start-of-`\begin{proof}` at line 36):
  - Counter-example setup: lines 76--103 (define `G`, verify CDMG axioms, define `A, B, C, D`, verify disjointness).
  - LHS `¬ A ⊥_G B | C`: lines 105--174 (define the walk `π`, compute `Anc^G`, `Desc^G`, `Sc^G` at the relevant vertices, verify σ-open position-by-position, observe no colliders).
  - RHS `A ⊥_{G^{∖u}} B | C`: lines 176--410 (compute `E^{∖u}`, `L^{∖u} = ∅` via candidate-by-candidate exclusion, `Sc^{G^{∖u}}`, `Anc^{G^{∖u}}(C)`, exhaustive case analysis on the final two steps of any walk).
  - Conclusion: lines 412--418.
  - Where the LN proof fails (audit trail): lines 420--456.
- Ready for `verify_tex_proof` dispatch.

---
## Run summary -- 2026-05-28T05:26:54+00:00
**Reason for stop:** 8-hour budget exhausted after 22 turns
**Turns this run:** 18
**Elapsed:** 480.7 min
**Row state at exit:** formalized=no proven=not proven solved=no

### Action sequence
    5. new_manager               fresh manager taking over.
    6. spawn_agent_sub_task      Lift complete. Braces balanced (0), dollars balanced (0); one real `\begin{proof}` / `\end{proof}` pair (the other `begin{proof}` count comes from the literal mention in the stub's header comment, ...
    7. verify_tex_proof          I have all the pieces I need. Let me compose the verdict.

## Verification summary

**Statement match.** The proof file's restated `\begin{Lem}` matches `claim_3_25_statement_ISigmaSeparation.tex` ...
    8. spawn_agent_sub_task      ## Report back to manager

**File state**: `ISigmaSeparationMarginalization.lean` is **unchanged** — the original `by sorry` body remains. I did not modify any other files either. `lake build` is c...
    9. continue_agent            Resumed session 8886611a…; reply: ## Full diagnostic — `claim_3_25` (`isISigmaSeparated_marginalize_iff`)

**Note on file state**: `ISigmaSeparationMarginalization.lean` is untouched (single `by so...
   10. continue_agent            Resumed session 8886611a…; reply: Done — appended **597 - 62 = 535 lines** of structured diagnostic to `workspace_claim_3_25.md` without touching any of the prior content. The new `## Leanification...
   11. spawn_agent_sub_task      Sub-task 1 complete. Here's the structured report back to the manager:

## Sub-task 1 completion report

### (a) Files touched

**`leanification/Chapter3_GraphTheory/Section3_2/MarginalizationPrese...
   12. spawn_agent_sub_task      Here is my structured report:

## Report — Sub-task 2 Completion (with Escalation)

### 1. File path created

`leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean`

### ...
   13. spawn_agent_sub_task      Now let me write my report back to the manager.

## Report

### 1. File state
- **File touched**: `leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean` (only). No other ...
   14. spawn_agent_sub_task      Sub-task 2a complete. Here is the report.

## Report back

**1. Exact line of the new lemma**

`leanification/Chapter3_GraphTheory/Section3_3/SigmaOpenWalkMarginalization.lean:214` (the `private le...
   15. spawn_agent_sub_task      All 5 helpers (plus one auxiliary) built clean. Here is the report for the manager.

## Report to manager: sub-task 2b complete

### 1. Line range of each new helper (sorted in helper order 2 → 6)
...
   16. spawn_agent_sub_task      ## Report to Manager

**Status: PARTIAL — escalation on `lift_aux` body.** The strong bidir helper and SCC helper are fully proven; the public theorem now derives from `lift_aux`; `lift_aux`'s stru...
   17. spawn_agent_sub_task      ## Report to Manager

**Outcome**: ESCALATION with precise structural obstruction documented at `workspace_claim_3_25.md` (new "Sub-task 2d worker turn" section, ~190 lines).

**File state**: `Sigm...
   18. spawn_agent_sub_task      Build is clean with exactly 3 sorrys as expected. Let me now report back to the manager.

## Sub-task 2e Complete — `lift_aux_strong` proved, `lift_aux` derived

### Line ranges

**`SigmaOpenWalkMa...
   19. spawn_agent_sub_task      ## Summary

I escalate with a **critical structural finding**: the LN's lemma `lem:stability_separation_marginalization` (claim_3_25) appears to be **FALSE** under the stated preconditions, with a ...
   20. spawn_agent_sub_task      ## Verdict: COUNTEREXAMPLE VALID

The worker's counterexample is sound. The Lean theorem `isISigmaSeparated_marginalize_iff` at `ISigmaSeparationMarginalization.lean:442` is **false** as currently ...
   21. mistake                   (disprove flow engaged)
   22. spawn_agent_sub_task      Done. The proof of negation is written. Here is the structured report.

## 1. File written

- **Path**: `/home/11716061/repo_scaffold2/leanification/Chapter3_GraphTheory/Section3_3/tex/claim_3_25_p...

### Latest verifier verdicts
  (none captured)

### Resumable past agents (most recent 10)
  - spawn_agent_sub_task      id=8b5f1dab-1a27-4146-b1de-11d7b0f54978  last=2026-05-28T02:50:06+00:00
  - manager                   id=80ff6824-2dae-4842-9fc1-5665ea9e082e  last=2026-05-28T02:54:31+00:00
  - spawn_agent_sub_task      id=013e1090-5817-4a6c-9bd5-161da62a0349  last=2026-05-28T03:50:05+00:00
  - manager                   id=c69877a2-b1b2-43cf-a146-4b670a310c7e  last=2026-05-28T03:56:28+00:00
  - spawn_agent_sub_task      id=c257e278-272a-4446-99b5-18f24c9f84e7  last=2026-05-28T04:46:20+00:00
  - manager                   id=b55a8304-cd71-411e-818a-613ff1b76f41  last=2026-05-28T04:56:02+00:00
  - spawn_agent_sub_task      id=9cc69ee7-e3b6-406c-93e0-e3139974483c  last=2026-05-28T05:10:53+00:00
  - manager                   id=56ba17e9-219a-4633-9de7-b528af49018c  last=2026-05-28T05:12:54+00:00
  - manager                   id=17af29a1-6a47-4efe-85e6-699bc8ba19c5  last=2026-05-28T05:15:16+00:00
  - spawn_agent_sub_task      id=9642572c-2cfe-4b6f-b0b2-759599d0e972  last=2026-05-28T05:26:54+00:00

### What the next manager should NOT repeat
_(Auto-recorded section. The next manager may overwrite this with a
sharper diagnosis once it has read above. The bullets below are a
heuristic from the action sequence -- treat them as hypotheses, not facts.)_
- Actions emitted this run, in order, are listed above. Re-running the
  same sequence is unlikely to help -- pick a different angle.
- If a verifier last reported FAIL, the feedback was inside its
  `BEGIN[feedback]…END[feedback]` block; read your history before
  dispatching the same verifier again.
- If you want to talk to a specific past agent, use `continue_agent`
  with one of the session ids above instead of spawning fresh.
