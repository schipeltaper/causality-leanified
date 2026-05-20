import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

-- TeX statement: tex/claim_3_8_statement_DisjointHardInterventions.tex
-- TeX proof: tex/claim_3_8_proof_DisjointHardInterventions.tex (Manager B)

/-!
# Disjoint hard interventions and node-splittings commute (claim_3_8)

This file formalises the lecture notes' lemma "disjoint hard
interventions and node-splittings commute" --
`lecture-notes/lecture_notes/graphs.tex` Lem at lines 497 -- 503. The
LN states the equality

  `(G_{do(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{do(W₁)}`

under the prose preconditions `W₁ ⊆ J ∪ V`, `W₂ ⊆ V`, and
`Disjoint W₁ W₂` (LN proof at lines 505 -- 533).

## Why literal `Eq` (and not `CDMGEquiv`)

Unlike `TwoDisjointNodeSplittingsCommute.lean` (claim_3_7), where two
*iterated* node-splittings produce carriers
`(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` vs `α ⊕ ↑(W₁ ∪ W₂)` that differ
def-equally and force a `CDMGEquiv`-valued framing, in claim_3_8 the
node-splitting operator is applied **only once on each side** and on
the **same set `W₂`**, while the hard-intervention operator is
**carrier-preserving** (`hardInterventionOn : CDMG α → Set α → CDMG α`;
see `HardInterventionOn.lean` line 232). Therefore:

* LHS `(G.hardInterventionOn W₁).nodeSplittingOn W₂ _` has carrier
  `α ⊕ ↑W₂` -- HI takes `α → α`, then NS takes `α → α ⊕ ↑W₂`.
* RHS `(G.nodeSplittingOn W₂ hW₂).hardInterventionOn (Sum.inl '' W₁)`
  has carrier `α ⊕ ↑W₂` -- NS takes `α → α ⊕ ↑W₂`, then HI takes
  `α ⊕ ↑W₂ → α ⊕ ↑W₂`.

Both carriers are *definitionally* equal, so the statement is a
literal `Eq` of CDMGs over the same carrier. This puts claim_3_8 in
the same regime as `HardInterventionsCommute.lean` (claim_3_4) and is
precisely why `TwoDisjointNodeSplittingsCommute.lean` (claim_3_7)
lines 49 -- 71 single out *this* row as the literal-`Eq` case: HI's
carrier-preservation absorbs the `Sum.inl`-lift of `W₁` into the
target-set argument on the RHS without forcing a re-labeling
bijection.

We reuse `HardInterventionsCommute.lean`'s `private mk_eq_of_data`
ext-style helper verbatim (renamed `private` per the same one-shot
rationale; see the design block on `HardInterventionsCommute.lean`
lines 81 -- 92 -- the helper is generic over the carrier `α`, so the
copy is literal).

## Where this gets used downstream

* **claim_3_11** (`graphs.tex` Lem at lines 666 -- 671) -- the SWIG
  mirror of this lemma: identical shape with `\swig` in place of
  `\spl` and dependence on `def_3_12` instead of `def_3_11`. The LN
  proofs of claim_3_8 (lines 505 -- 533) and claim_3_11 (lines
  672 -- 700) are structurally identical case-by-case, and the Lean
  formalisation of claim_3_11 will re-use this file's
  `mk_eq_of_data` and `subset_hardInterventionOn_V_of_disjoint`
  patterns once `def_3_12` is in place. claim_3_11 is the most
  direct and most certain downstream consumer.

* **chapter 4 (CBNs)** -- `causal_bayesian_networks.tex` defines
  CBN-level analogues of `\spl` (Def at line 298) and `\doit`; the
  CBN-level Markov-kernel bookkeeping for a hard intervention
  composed with a node-splitting (under disjointness) is the
  measure-theoretic lift of the graph-side identity proven here.
  No CBN-level *lemma* in chapter 4 currently quotes claim_3_8
  directly by name, but the graph-side bookkeeping behind those
  CBN-level constructions is exactly what this row delivers.

* **chapters 5 / 8 -- 10 (do-calculus, iSCMs, counterfactuals)** --
  Survey of `do-calculus.tex`, `scms.tex`, `scms2.tex`,
  `scms3.tex`, `scms4.tex`, and `counterfactuals.tex` shows
  iSCM-level node-splitting (`counterfactuals.tex` line 45,
  `\spl(v)` on an iSCM) and hard interventions (`\doit` throughout)
  appearing pervasively, but no displayed-equation lemma directly
  iterates `\doit` with `\spl` on disjoint sets at the iSCM /
  counterfactual layer. The graph-side commute identity proven
  here is therefore a foundational building block: when chapter
  5 / 8 -- 10 manipulate iSCM-or-counterfactual carriers, the
  *graph-side* projection of those manipulations reduces to
  claim_3_8 (or its SWIG mirror claim_3_11). No specific
  call-site beyond claim_3_11 is currently visible in the LN by
  name, so we do not fabricate citations here -- only claim_3_11
  is a load-bearing direct consumer.

If a third call site emerges outside chapter 3 that wants the
same-carrier `Eq`, we reconsider promoting `mk_eq_of_data` to a
shared chapter-3 helper. Until then, keeping it `private` per-row
mirrors the `HardInterventionsCommute.lean` precedent and avoids
leaking a chapter-wide ext-lemma from a localised row.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ## Local CDMG-extensionality helper -/

/-- Local CDMG-extensionality helper for this row: two CDMGs over the
same carrier `α` are equal as soon as their four data fields
`J / V / E / L` agree. The six prop fields (`disjoint_JV`, `E_subset`,
`L_subset`, `L_irrefl`, `L_symm`, `disjoint_EL`) are propositions,
hence proof-irrelevant under Lean 4's definitional rule, so they
close by `rfl` once the data fields are pinned down.

Kept `private` because it is a one-shot shortcut used only by
`hardInterventionOn_nodeSplittingOn_comm` below -- `CDMG` is
intentionally not `@[ext]`-tagged at its definition site
(`Section3_1/CDMG.lean`), and we do not want a chapter-wide ext lemma
leaking out from this row. The component-wise discipline of the LN
proof (`tex/claim_3_8_proof_DisjointHardInterventions.tex`) is exactly
what this helper packages.

Identical to the private `mk_eq_of_data` in
`HardInterventionsCommute.lean` lines 93 -- 105 (carrier-generic, so
the body is literal). We deliberately re-declare it here rather than
import `HardInterventionsCommute.lean` because claim_3_8 is
independent of claim_3_4 at the *content* level -- the only shared
dependency is the carrier-generic CDMG ext lemma itself, and
duplicating a 10-line proof-irrelevance helper is the right
trade-off against pulling in claim_3_4's iteration / commute API as a
build-graph dependency. -/
private theorem mk_eq_of_data {G H : CDMG α}
    (hJ : G.J = H.J) (hV : G.V = H.V) (hE : G.E = H.E) (hL : G.L = H.L) :
    G = H := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := G
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := H
  -- After `obtain` on both sides, the dot-projections in the four
  -- hypotheses def-reduce to free variables; `subst` then rewrites
  -- the data fields, and the prop fields agree by proof irrelevance.
  subst hJ
  subst hV
  subst hE
  subst hL
  rfl

/-! ## Bridging helper: inner-NS precondition discharge -/

/-- If `W₂ ⊆ G.V` and `W₁` is disjoint from `W₂`, then `W₂` is
contained in the output set of the hard-intervened graph:
`W₂ ⊆ (G.hardInterventionOn W₁).V = G.V \ W₁`. Used to discharge the
precondition of the inner `nodeSplittingOn W₂` call on the LHS of the
commute identity below.

## Design choice

* **Standalone, not inlined.** Inlining the proof in the LHS's
  `nodeSplittingOn` precondition slot would make the main theorem's
  signature unreadable and force every (Manager B) proof step to
  re-derive the inclusion under any goal-state perturbation.
  Factoring it lets the `@[simp]` lemma `hardInterventionOn_V` from
  `HardInterventionOn.lean` line 275 discharge the rewrite in one
  step. Mirrors the analogous helper
  `subset_nodeSplittingOn_V_of_subset_V` in
  `TwoDisjointNodeSplittingsCommute.lean` lines 242 -- 247.

* **Not `private`.** The SWIG analogue (claim_3_11) will re-use this
  same helper unchanged -- node-splitting and node-splitting hard
  intervention both promote a subset of `V` away from the output
  layer in the same way with respect to a *prior* hard intervention
  on `W₁` -- so we keep it public per the
  `subset_nodeSplittingOn_V_of_subset_V` precedent.

* **`hW₂` and `hdisj` order matches the main theorem.** Both are
  needed; ordering them `hW₂ : W₂ ⊆ G.V` first then
  `hdisj : Disjoint W₁ W₂` mirrors the order they appear in the
  main theorem's signature below, so a call-site reads the helper's
  argument list left-to-right in the same way as the main theorem's
  hypothesis list. -/
theorem subset_hardInterventionOn_V_of_disjoint
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    W₂ ⊆ (G.hardInterventionOn W₁).V := by
  -- `hardInterventionOn_V`: `(G.hardInterventionOn W₁).V = G.V \ W₁`.
  rw [hardInterventionOn_V]
  intro x hx
  exact ⟨hW₂ hx, fun hx₁ => Set.disjoint_left.mp hdisj hx₁ hx⟩

/-! ## The commute identity -/

-- claim_3_8
-- title: DisjointHardInterventions
--
-- Hard intervention on a set `W₁` and node-splitting on a set
-- `W₂ ⊆ G.V` commute when `W₁` and `W₂` are disjoint:
-- `(G_{do(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{do(W₁)}`. On the RHS the
-- hard intervention's target set is the canonical `Sum.inl`-lift of
-- `W₁` (since the post-split graph lives over the carrier `α ⊕ ↑W₂`);
-- under our convention `Sum.inl = 0-copy = canonical observation
-- copy` (see `NodeSplittingOn.lean` lines 244 -- 269), this matches
-- the LN's implicit identification `α ≅ inl '' α` exactly.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 497 -- 503)
-- the prose paragraph and displayed equation are reflowed for the
-- 100-character line limit (linewrap only; LaTeX whitespace collapses
-- between tokens, so this is verbatim under \LaTeX semantics):

\begin{claimmark}
\begin{Lem}[Disjoint hard interventions and node-splittings commute]
   Let $G=(J,V,E,L)$ be a CDMG and $W_1 \ins J \cup V$ and $W_2 \ins V$
   two disjoint subsets of nodes of $G$.
   Then the CDMG obtained from first hard intervening on $W_1$ and then
   node-splitting $W_2$ is the same CDMG that arises from first
   node-splitting $W_2$ and then hard intervening on $W_1$.
      \[ \lp G_{\doit(W_1)} \rp_{\spl(W_2)} =  \lp G_{\spl(W_2)} \rp_{\doit(W_1)}.   \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_8 (`DisjointHardInterventions`): for a CDMG `G : CDMG α` and
disjoint subsets `W₁ W₂ : Set α` with `W₂ ⊆ G.V`, hard intervention
on `W₁` and node-splitting on `W₂` commute. Mirrors the displayed
equation in the `\Lem` at `lecture-notes/lecture_notes/graphs.tex`
line 501.

## Design choice

* **Literal `Eq`, not `CDMGEquiv`.** Both sides have carrier
  `α ⊕ ↑W₂`. On the LHS, `G.hardInterventionOn W₁` is
  carrier-preserving (`α → α`) and then `nodeSplittingOn W₂`
  extends to `α ⊕ ↑W₂`. On the RHS, `G.nodeSplittingOn W₂ hW₂`
  extends to `α ⊕ ↑W₂` and then `hardInterventionOn` is
  carrier-preserving (`α ⊕ ↑W₂ → α ⊕ ↑W₂`). The two carriers are
  *definitionally* equal, so literal `Eq` is type-correct -- no
  bijection / re-labeling helper structure is needed. This puts
  this row in the same regime as `HardInterventionsCommute.lean`
  (claim_3_4) and is precisely why
  `TwoDisjointNodeSplittingsCommute.lean` (claim_3_7) lines
  49 -- 71 single out this row as *not* needing the `CDMGEquiv`
  machinery. See the file docstring for the longer comparison.

* **No `W₁ ⊆ G.J ∪ G.V` precondition.** The LN writes
  `W₁ ⊆ J ∪ V`, but `G.hardInterventionOn W₁` is well-defined for
  every `W₁ : Set α` -- see the design notes at
  `HardInterventionOn.lean` lines 88 -- 215 and the same drop in
  `HardInterventionsCommute.lean` lines 138 -- 161 (which cites
  claim_3_8 / claim_3_11 as one of the consumers that benefit from
  the no-precondition encoding). The LN's `W₁ ⊆ J ∪ V` is informal
  scaffolding ("`W₁ ⊆ G`" so that `do(W₁)` is mathematically
  meaningful in prose), not a load-bearing hypothesis. Vertices in
  `W₁ \ (G.J ∪ G.V)` are inert under `hardInterventionOn` (no edge
  has an endpoint there, by `G.E_subset` / `G.L_subset`), so they
  ride along the LHS / RHS equality without contributing anything,
  and the commute identity holds for arbitrary `W₁`.

* **`hW₂ : W₂ ⊆ G.V` is structurally required.** Unlike
  `W₁ ⊆ J ∪ V` (which is droppable), `W₂ ⊆ G.V` is load-bearing
  on **both** sides:
    * RHS: `G.nodeSplittingOn W₂ hW₂` directly requires `hW₂` (see
      `NodeSplittingOn.lean` lines 271 -- 281, which records the
      structural reason -- the split edge `w^0 → w^1` needs its
      source `Sum.inl w` in the split graph's vertex set, which
      contains only the `inl`-labels of vertices in `G.V`).
    * LHS: the inner `nodeSplittingOn W₂` is on
      `G.hardInterventionOn W₁`, whose vertex set is `G.V \ W₁`.
      We need `W₂ ⊆ G.V \ W₁`, discharged by the helper
      `subset_hardInterventionOn_V_of_disjoint hW₂ hdisj` above.
      The bare `hW₂` plus `hdisj` is exactly what makes that
      inclusion hold (the LN's parenthetical "with
      `W₂ ⊆ V \ W₁`" at `graphs.tex` line 510 is the same
      observation).

* **`Disjoint W₁ W₂` is load-bearing on both sides.** The
  hypothesis is not a convenience but a structural requirement,
  for *different* reasons on each side:
    * LHS: the inner `nodeSplittingOn W₂` operates on
      `G.hardInterventionOn W₁`, whose vertex set is `G.V \ W₁`,
      so its precondition demands `W₂ ⊆ G.V \ W₁`. This is
      precisely the conclusion of the helper
      `subset_hardInterventionOn_V_of_disjoint hW₂ hdisj`,
      which *consumes* `hdisj`: without disjointness, the bare
      `hW₂ : W₂ ⊆ G.V` does **not** imply the post-HI
      inclusion, and the inner NS call fails to elaborate.
    * RHS: the outer `hardInterventionOn (Sum.inl '' W₁)` acts
      on the post-split graph over `α ⊕ ↑W₂`. The lifted target
      set `Sum.inl '' W₁` lives entirely in the `inl`-half of
      that carrier, which is correct *only* because
      `W₁ ∩ W₂ = ∅`: otherwise, a vertex `w ∈ W₁ ∩ W₂` would
      get duplicated into a pair `(Sum.inl w, Sum.inr ⟨w, _⟩)`
      by the inner NS, and `Sum.inl '' W₁` would silently miss
      the `Sum.inr`-copy -- the post-split HI would then strip
      only one of the two split copies of `w`, which is not
      what the LHS does (the LHS HI on the base graph cleanly
      removes `w` before NS ever sees it).
  Dropping `hdisj` therefore breaks the LHS's typechecking
  *and* the RHS's semantics; the two sides demonstrably differ
  on the duplicated-`W₂` half. This matches the LN's explicit
  "two disjoint subsets" precondition at `graphs.tex` line 499.

* **Lift `W₁ ↦ Sum.inl '' W₁` on the RHS's HI argument.** The
  outer operation on the RHS is hard intervention on the
  *post-split* graph, which lives over the carrier `α ⊕ ↑W₂`. Its
  target set must therefore be a `Set (α ⊕ ↑W₂)`, not a
  `Set α`. The natural lift is `Sum.inl '' W₁`: under our
  convention `Sum.inl = 0-copy = canonical observation copy` (see
  `NodeSplittingOn.lean` lines 244 -- 269), the LN's "the same
  `W₁`" *is* the `inl`-image of `W₁` in the split carrier. The LN
  writes `W₁` on both sides because it identifies `α ≅ inl '' α`
  implicitly throughout def_3_11 / def_3_12 (LN hint at
  `graphs.tex` line 197 "we ... make the identification
  `W = W^0`"). Lean's stricter type discipline forces us to spell
  the lift out. Note this is faithful to LN intent: vertices of
  `W₁ ∩ G.J` survive into the post-split graph as
  `Sum.inl '' (G.J ∩ W₁) ⊆ (G.nodeSplittingOn W₂ hW₂).J` and
  vertices of `W₁ ∩ G.V` survive as
  `Sum.inl '' (G.V ∩ W₁) ⊆ Sum.inl '' G.V ⊆ (G.nodeSplittingOn W₂
  hW₂).V`, so removing `Sum.inl '' W₁` from the post-split graph
  exactly mirrors the LN's "then `doit(W₁)`" on the right-hand
  side. (Vertices of `W₁ \ (G.J ∪ G.V)`, which are inert anyway by
  the previous bullet, ride along under `Sum.inl` too.)

  We also considered narrowing the lift to
  `Sum.inl '' (W₁ ∩ (G.J ∪ G.V))` -- which tracks only the
  LN-relevant vertices and drops the inert ones up-front -- and
  rejected it. Two reasons. First, by the inertness argument of
  the no-`W₁ ⊆ G.J ∪ G.V` bullet above, the two lifts produce
  the *same* RHS CDMG: inert vertices contribute nothing to
  `hardInterventionOn` (they appear in no edge endpoint by
  `G.E_subset` / `G.L_subset` and lie outside both `J` and `V`),
  so removing or not removing them under HI is an identity on
  the four CDMG data fields. The narrower lift therefore gives
  no provable strengthening of the theorem. Second, it would
  force every call site to wrap the `W₁` argument in
  `· ∩ (G.J ∪ G.V)` -- chapters 5 and 8 -- 10 typically already
  know `W₁ ⊆ J ∪ V` (the LN-level convention) and would have to
  thread that fact through *just* to discharge the `∩`. The
  wider lift `Sum.inl '' W₁` is the cleaner shape on both
  counts.

* **`G : CDMG α` implicit; `W₁ W₂ : Set α` implicit; `hW₂` /
  `hdisj` explicit.** Both sets appear in the hypotheses (`hW₂`,
  `hdisj`) and in the conclusion, so the elaborator can recover
  them from either side; making them implicit lines up with
  `TwoDisjointNodeSplittingsCommute.lean`'s
  `nodeSplittingOn_nodeSplittingOn_equiv` (lines 386 -- 387),
  which uses the same convention for the same reason
  (sets-pinned-by-hypotheses pattern). Note that
  `HardInterventionsCommute.lean` (claim_3_4) uses *explicit*
  `W₁ W₂` because it has *no* constraining hypotheses on them --
  the sets there are arbitrary and must be supplied at call sites
  for the rewrite to fire. Here, the sets are pinned down by the
  hypotheses, so call-site ergonomics is preserved via
  unification.

* **Naming `hardInterventionOn_nodeSplittingOn_comm`.** Follows
  the Mathlib `_comm` convention for commutativity of two
  operators (`add_comm`, `mul_comm`, `Set.union_comm`), with both
  operators in the name (left to right matching the LHS of the
  conclusion). The order matches the LN's prose ("first hard
  intervening on `W₁` and then node-splitting `W₂`") and the LHS
  of the displayed equation. Pairing with
  `hardInterventionOn_comm` (claim_3_4) and
  `nodeSplittingOn_comm_equiv` (claim_3_7) makes the subsection's
  three commute lemmas form a uniform `_comm` family. The mirror
  `nodeSplittingOn_hardInterventionOn_comm` (operators reversed) is
  technically equivalent but not exposed -- consumers can use
  `.symm` if they want the swap; we follow the LN's LHS-then-RHS
  reading order.

* **Bridging helper `subset_hardInterventionOn_V_of_disjoint`
  factored out.** See the design block on that helper above; this
  keeps the main theorem's signature readable.

* **Proof strategy: componentwise via `mk_eq_of_data`.** The body is
  `refine mk_eq_of_data ?_ ?_ ?_ ?_` plus four component-wise checks
  mirroring `tex/claim_3_8_proof_DisjointHardInterventions.tex`: `J`
  is a one-liner `Set.image_union Sum.inl G.J W₁`; `V` is `ext x` +
  forward/backward `rintro` on `Sum.inl '' (G.V \ W₁)` vs
  `Set.range Sum.inr`, with the `Sum.inl`/`Sum.inr` cross-carrier
  mismatch closed by `Sum.inl_injective`; `E` and `L` share the shape
  `ext p` + `simp only [mem_..._E/L]` + two-piece `rintro` (relabeled
  original edges vs split edges for `E`; the two-endpoint exclusion
  handled on each side for `L`), again with `Sum.inl_injective`
  carrying the case-split. See the in-body comments (lines
  ~387 -- 397) for why `Sum.inl` injectivity replaces the LN's
  `W₁ ∩ W₂ = ∅` case-split at this layer. -/
theorem hardInterventionOn_nodeSplittingOn_comm
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁).nodeSplittingOn W₂
        (subset_hardInterventionOn_V_of_disjoint hW₂ hdisj)
      = (G.nodeSplittingOn W₂ hW₂).hardInterventionOn (Sum.inl '' W₁) := by
  -- Mirrors `tex/claim_3_8_proof_DisjointHardInterventions.tex`: four
  -- component-wise checks J / V / E / L, via `mk_eq_of_data`. The LN
  -- proof appeals to `W₁ ∩ W₂ = ∅` inside its case-splits (e.g.
  -- "`v_2^0 ∈ W_1 ↔ v_2 ∈ W_1`"); in our Lean encoding the LN's
  -- `^0 := id` identification on `V ∖ W₂` is replaced by the *uniform*
  -- `Sum.inl` embedding for *all* of `α` (the canonical-observation
  -- convention from `def_3_11`), so `Sum.inl v ∈ Sum.inl '' W₁ ↔ v ∈ W₁`
  -- is just `Sum.inl` injectivity -- no case-split on `v ∈ W₂` and no
  -- disjointness needed at this layer. Disjointness remains load-bearing
  -- at the typing level via `subset_hardInterventionOn_V_of_disjoint`,
  -- which discharges the LHS's inner-NS precondition.
  refine mk_eq_of_data ?_ ?_ ?_ ?_
  · -- Node sets, `J` half (TeX "Node sets" section).
    -- Goal: `Sum.inl '' (G.J ∪ W₁) = Sum.inl '' G.J ∪ Sum.inl '' W₁`.
    exact Set.image_union Sum.inl G.J W₁
  · -- Node sets, `V` half (TeX "Node sets" section).
    -- Goal: `Sum.inl '' (G.V \ W₁) ∪ Set.range Sum.inr
    --        = (Sum.inl '' G.V ∪ Set.range Sum.inr) \ Sum.inl '' W₁`.
    -- Pointwise on `Sum.inl a`: both sides ↔ `a ∈ G.V ∧ a ∉ W₁`.
    -- Pointwise on `Sum.inr w`: both sides true (LHS via the
    -- `range Sum.inr` summand; RHS via the constructor-mismatch
    -- `Sum.inr w ∉ Sum.inl '' W₁`).
    ext x
    constructor
    · rintro (⟨y, ⟨hyV, hyW⟩, rfl⟩ | ⟨w, rfl⟩)
      · refine ⟨Or.inl ⟨y, hyV, rfl⟩, ?_⟩
        rintro ⟨z, hzW, hzeq⟩
        exact hyW (Sum.inl_injective hzeq ▸ hzW)
      · refine ⟨Or.inr ⟨w, rfl⟩, ?_⟩
        rintro ⟨_, _, hzeq⟩
        cases hzeq
    · rintro ⟨h, hno⟩
      rcases h with ⟨y, hyV, rfl⟩ | ⟨w, rfl⟩
      · exact Or.inl ⟨y, ⟨hyV, fun hyW => hno ⟨y, hyW, rfl⟩⟩, rfl⟩
      · exact Or.inr ⟨w, rfl⟩
  · -- Directed edges (TeX "Directed edges" section).
    -- LHS = NS-piece-1 on edges of `G ∖ {head ∈ W₁}` ∪ NS-piece-2 (split edges).
    -- RHS = (NS-piece-1 on edges of `G` ∪ NS-piece-2) ∖ {target ∈ Sum.inl '' W₁}.
    -- Piece 1 (`(split1 W₂ v₁, Sum.inl v₂)`): target = `Sum.inl v₂`, so
    -- `target ∈ Sum.inl '' W₁ ↔ v₂ ∈ W₁` by injectivity; both sides
    -- exclude exactly `v₂ ∈ W₁`.
    -- Piece 2 (`(Sum.inl w.val, Sum.inr w)`): target = `Sum.inr w`,
    -- never in `Sum.inl '' W₁` (constructor mismatch); both sides keep
    -- all split edges.
    ext p
    simp only [mem_nodeSplittingOn_E, mem_hardInterventionOn_E, Set.mem_image]
    constructor
    · rintro (⟨v₁, v₂, ⟨hE, hv₂⟩, rfl⟩ | ⟨w, rfl⟩)
      · refine ⟨Or.inl ⟨v₁, v₂, hE, rfl⟩, ?_⟩
        rintro ⟨z, hzW, hzeq⟩
        exact hv₂ (Sum.inl_injective hzeq ▸ hzW)
      · refine ⟨Or.inr ⟨w, rfl⟩, ?_⟩
        rintro ⟨_, _, hzeq⟩
        cases hzeq
    · rintro ⟨h, hno⟩
      rcases h with ⟨v₁, v₂, hE, rfl⟩ | ⟨w, rfl⟩
      · exact Or.inl ⟨v₁, v₂, ⟨hE, fun hv₂W => hno ⟨v₂, hv₂W, rfl⟩⟩, rfl⟩
      · exact Or.inr ⟨w, rfl⟩
  · -- Bidirected edges (TeX "Bidirected edges" section).
    -- LHS = `(Sum.inl × Sum.inl) '' (G.L ∖ {p | p.1 ∈ W₁ ∨ p.2 ∈ W₁})`.
    -- RHS = `((Sum.inl × Sum.inl) '' G.L) ∖
    --        {p | p.1 ∈ Sum.inl '' W₁ ∨ p.2 ∈ Sum.inl '' W₁}`.
    -- Both endpoints become `Sum.inl vₖ`, so
    -- `Sum.inl vₖ ∈ Sum.inl '' W₁ ↔ vₖ ∈ W₁` by injectivity. Both
    -- sides exclude exactly the same pairs.
    ext p
    simp only [mem_nodeSplittingOn_L, mem_hardInterventionOn_L, Set.mem_image]
    constructor
    · rintro ⟨v₁, v₂, ⟨hL, hv₁, hv₂⟩, rfl⟩
      refine ⟨⟨v₁, v₂, hL, rfl⟩, ?_, ?_⟩
      · rintro ⟨z, hzW, hzeq⟩
        exact hv₁ (Sum.inl_injective hzeq ▸ hzW)
      · rintro ⟨z, hzW, hzeq⟩
        exact hv₂ (Sum.inl_injective hzeq ▸ hzW)
    · rintro ⟨⟨v₁, v₂, hL, rfl⟩, hno₁, hno₂⟩
      refine ⟨v₁, v₂, ⟨hL, ?_, ?_⟩, rfl⟩
      · intro h₁W
        exact hno₁ ⟨v₁, h₁W, rfl⟩
      · intro h₂W
        exact hno₂ ⟨v₂, h₂W, rfl⟩

end CDMG

end Causality
