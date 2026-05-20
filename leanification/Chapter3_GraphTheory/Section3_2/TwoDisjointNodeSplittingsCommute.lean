import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Set
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

-- TeX statement: tex/claim_3_7_statement_TwoDisjointNode.tex
-- TeX proof: tex/claim_3_7_proof_TwoDisjointNode.tex (Manager B)

/-!
# Two disjoint node-splittings commute (claim_3_7)

This file formalises the lecture notes' lemma "two disjoint node-splittings
commute" -- `lecture-notes/lecture_notes/graphs.tex` Lem at lines 459 -- 463
with proof at lines 466 -- 493. The LN states the chained equality

  `(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ⊔ W₂)}`

under the precondition `W₁, W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`.

Unlike `HardInterventionsCommute.lean` -- where both sides of the chained
equality live over the same carrier `α`, allowing literal `Eq` -- iterated
node-splitting is *type-changing*: the iterated splitting lives over
`(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` while the merged splitting lives over
`α ⊕ ↑(W₁ ∪ W₂)`. The two carriers are canonically *isomorphic* via a
re-labeling bijection, but not definitionally equal. This is precisely the
"modulo a re-labeling equivalence" telegraphed by `NodeSplittingOn.lean`
lines 43 -- 48.

The file therefore introduces a small bundled equivalence between CDMGs
over potentially different carriers (`CDMGEquiv`) and states the fusion
lemma + the commute corollary as `CDMGEquiv`-valued definitions.

This file delivers:

* `CDMGEquiv` -- 4-data-field equivalence between two CDMGs.
* `CDMGEquiv.refl`, `.symm`, `.trans` -- the groupoid laws; Manager B
  uses `.symm.trans` to derive the commute corollary from the fusion
  lemma.
* `subset_nodeSplittingOn_V_of_subset_V` -- bridging lemma so the inner
  `nodeSplittingOn` call's precondition discharges cleanly.
* `fusionEquiv` -- the canonical re-labeling bijection
  `α ⊕ ↑(W₁ ∪ W₂) ≃ (α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)`. Body is fully
  defined (no `sorry`).
* `nodeSplittingOn_nodeSplittingOn_equiv` -- fusion lemma statement
  (body = `sorry`, Manager B fills it).
* `nodeSplittingOn_comm_equiv` -- commute corollary statement (body =
  `sorry`, Manager B fills it via `.symm.trans` of the fusion lemma).

## Foundation placement (local Section 3.2, not Section 3.1)

`CDMGEquiv` is intentionally introduced in this row's own file rather
than promoted to `Section3_1/`. Survey of current and forthcoming
consumers (Plan §1 in `workspace_claim_3_7.md` reaches this same
conclusion):

* **claim_3_8** has both sides over the *same* carrier `α ⊕ ↑W₂`
  (hard intervention preserves the carrier; node-splitting on `W₂`
  produces the same `α ⊕ ↑W₂` on either ordering), so it states
  literal `Eq` and does *not* need `CDMGEquiv`.
* **claim_3_12** is a `\Rem` (prose, no displayed equation); no
  `CDMGEquiv` need.
* **claim_3_10** (SWIG mirror of claim_3_7) is the most likely future
  consumer but is not yet solved; the precise `CDMGEquiv` shape it
  wants depends on `def_3_12`'s Lean encoding, which has not yet been
  fixed. Promoting `CDMGEquiv` now risks locking in a shape that
  claim_3_10 then has to refactor chapter-wide.

Decision: keep local. If claim_3_10's prover needs the same shape
they can `import` from here; only a *third* consumer should trigger
`reorder` to promote to Section 3.1. Mirrors
`HardInterventionsCommute.lean`'s `private mk_eq_of_data`, which kept
CDMG extensionality per-row rather than promoting it.
-/

namespace Causality

namespace CDMG

universe u

variable {α β γ : Type u}

/-! ## CDMGEquiv: re-labeling equivalence between CDMGs -/

/-- An equivalence between CDMGs `G : CDMG α` and `H : CDMG β` over
potentially distinct carrier types: a bijection `toEquiv : α ≃ β` whose
images on the four data fields `J`, `V`, `E`, `L` of `G` recover the
corresponding fields of `H`. The six prop fields (`disjoint_JV`,
`E_subset`, `L_subset`, `L_irrefl`, `L_symm`, `disjoint_EL`) are
proof-irrelevant once the four data fields are pinned down.

## Design choice

* **Why a 4-field `structure` (Option A) rather than literal `Eq`
  through a pushforward.** `CDMGEquiv` is a *relation* between two
  CDMGs over potentially different carriers; it commits to no
  canonical pushforward direction. The runner-up shape (Option B)
  would have defined a `CDMG.relabel : CDMG α → (α ≃ β) → CDMG β` and
  written `H = G.relabel e` as a literal `Eq` -- more `rw`-friendly,
  but it bakes one direction of the bijection into the result and
  gives `relabel` chapter-wide blast radius (every later
  iSCM / SWIG / counterfactual carrier-shift would reach for it)
  before we have evidence of what those consumers actually want. The
  conservative direction-symmetric encoding is Option A; we can
  promote to Option B later by defining `relabel` once the call-site
  pattern is visible, but the reverse move is much costlier.

* **Four `image`-equalities is exactly the data `fusionEquiv`
  transports.** Option C (four separate top-level
  `_J_eq` / `_V_eq` / `_E_eq` / `_L_eq` lemmas, no bundling) is not
  LN-faithful: the LN states *one* displayed chained equation and
  downstream consumers want "the two CDMGs are equivalent", not four
  disconnected component equalities (re-stated in pairs for each
  direction of the commute). Option D (`∃ e, ...` existential) hides
  the canonical witness `fusionEquiv` that the commute corollary
  needs to name when composing two equivalences.

* **The six prop fields are deliberately omitted.** Once the four
  data fields are pinned down via the `image`-equalities, the
  prop-field obligations on `H` (`disjoint_JV`, `E_subset`,
  `L_subset`, `L_irrefl`, `L_symm`, `disjoint_EL`) are completely
  determined by `G`'s prop fields plus the bijection -- there is no
  *information* in carrying them inside the bundle, just opportunity
  for spurious unification mismatches. This is the same
  proof-irrelevance principle that `HardInterventionsCommute.lean`
  packaged in its `private mk_eq_of_data` helper for the same-carrier
  case. -/
structure CDMGEquiv (G : CDMG α) (H : CDMG β) where
  /-- The underlying bijection on the carrier types. -/
  toEquiv : α ≃ β
  /-- The bijection sends `G.J` to `H.J`. -/
  J_eq : H.J = toEquiv '' G.J
  /-- The bijection sends `G.V` to `H.V`. -/
  V_eq : H.V = toEquiv '' G.V
  /-- The bijection sends `G.E` to `H.E` (applied to each endpoint). -/
  E_eq : H.E = (Prod.map toEquiv toEquiv) '' G.E
  /-- The bijection sends `G.L` to `H.L` (applied to each endpoint). -/
  L_eq : H.L = (Prod.map toEquiv toEquiv) '' G.L

namespace CDMGEquiv

/-- Reflexivity: `G` is `CDMGEquiv`-equivalent to itself via `Equiv.refl`.

## Design choice (`CDMGEquiv` groupoid laws)

* **Why ship `refl`, `symm`, `trans` together with the structure.**
  The commute corollary `nodeSplittingOn_comm_equiv` is derived from
  two `fusionEquiv` instances composed via `.symm.trans` (Manager
  B's one-line proof). Without the groupoid laws Manager B would
  hand-build each composition from `toEquiv.symm` / `.trans` and the
  four `image`-equalities -- six lines per direction, repeated. This
  is exactly the mitigation for Risk R5 in
  `workspace_claim_3_7.md` Plan §4: the LN's "follows by symmetry"
  sentence has to *land* somewhere on the Lean side, and these laws
  are where.

* **Three short `def`s rather than a `CategoryTheory.Groupoid`
  instance.** A full groupoid instance would force `CDMGEquiv` to
  live inside a `Sigma`-bundled morphism type over the proper class
  of all CDMGs (across all carrier types), introducing universe /
  size-issue overhead disproportionate to a one-row corollary. Three
  hand-written `def`s in this namespace expose precisely the API the
  commute corollary needs; a heavier categorical wrapper can be
  layered on later if a downstream consumer wants
  `Iso`/`Equiv`-style rewriting. -/
def refl (G : CDMG α) : CDMGEquiv G G where
  toEquiv := Equiv.refl α
  J_eq := by simp [Equiv.refl]
  V_eq := by simp [Equiv.refl]
  E_eq := by simp [Equiv.refl, Prod.map]
  L_eq := by simp [Equiv.refl, Prod.map]

/-- Symmetry: from `G ≃ H` build `H ≃ G` by inverting the bijection.
Used by Manager B's `nodeSplittingOn_comm_equiv` proof to flip one of
the two fusion equivalences before composing them. -/
def symm {G : CDMG α} {H : CDMG β} (e : CDMGEquiv G H) : CDMGEquiv H G where
  toEquiv := e.toEquiv.symm
  J_eq := by
    rw [e.J_eq, ← Set.image_comp]
    simp
  V_eq := by
    rw [e.V_eq, ← Set.image_comp]
    simp
  E_eq := by
    rw [e.E_eq, ← Set.image_comp]
    ext ⟨a, b⟩
    simp [Prod.map]
  L_eq := by
    rw [e.L_eq, ← Set.image_comp]
    ext ⟨a, b⟩
    simp [Prod.map]

/-- Transitivity: compose `G ≃ H` and `H ≃ K` to obtain `G ≃ K`. Used by
Manager B's `nodeSplittingOn_comm_equiv` proof to chain the two fusion
equivalences after flipping one via `.symm`. -/
def trans {G : CDMG α} {H : CDMG β} {K : CDMG γ}
    (e₁ : CDMGEquiv G H) (e₂ : CDMGEquiv H K) : CDMGEquiv G K where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  J_eq := by
    rw [e₂.J_eq, e₁.J_eq, ← Set.image_comp]
    rfl
  V_eq := by
    rw [e₂.V_eq, e₁.V_eq, ← Set.image_comp]
    rfl
  E_eq := by
    rw [e₂.E_eq, e₁.E_eq, ← Set.image_comp]
    ext ⟨a, b⟩
    simp [Prod.map, Equiv.trans]
  L_eq := by
    rw [e₂.L_eq, e₁.L_eq, ← Set.image_comp]
    ext ⟨a, b⟩
    simp [Prod.map, Equiv.trans]

end CDMGEquiv

/-! ## Helper: `W₂ ⊆ V` lifts to `Sum.inl '' W₂ ⊆ V_split` -/

/-- If `W₂ ⊆ G.V`, then `Sum.inl '' W₂` is contained in the vertex set of
the node-split graph `G.nodeSplittingOn W₁ hW₁`. Used to discharge the
inner precondition of the iterated splitting in the fusion lemma below.

## Design choice

* **No `Disjoint W₁ W₂` hypothesis.** Splitting preserves the
  output-nodes layer *monotonically*: `(G.nodeSplittingOn W₁ hW₁).V`
  contains all of `Sum.inl '' G.V` (every original output vertex
  appears via its 0-copy embedding, including those in `W₁`), so any
  `W₂ ⊆ G.V` lifts under `Sum.inl` into the split carrier regardless
  of how `W₁` and `W₂` overlap. Disjointness is only load-bearing for
  the *fusion* itself (the bijection on `↑(W₁ ∪ W₂)` needs an
  unambiguous `W₁` vs `W₂` dispatch); the *embedding* layer does not
  care. Plan §4 Risk R6 in `workspace_claim_3_7.md` records the
  verification; the practical consequence is one fewer hypothesis to
  thread through every use of the fusion lemma.

* **Standalone, not inlined into the fusion lemma signature.**
  Inlining the proof in the fusion lemma's type as a `by simp; ...`
  block would make the signature unreadable and force every call
  site to re-prove the same fact under any goal-state perturbation.
  Factoring it lets the `@[simp]` lemma `nodeSplittingOn_V` from
  `NodeSplittingOn.lean` (line 527) discharge the precondition in
  one step. -/
theorem subset_nodeSplittingOn_V_of_subset_V
    {G : CDMG α} {W₁ W₂ : Set α} (hW₂ : W₂ ⊆ G.V) (hW₁ : W₁ ⊆ G.V) :
    Sum.inl '' W₂ ⊆ (G.nodeSplittingOn W₁ hW₁).V := by
  rw [nodeSplittingOn_V]
  rintro x ⟨w, hw, rfl⟩
  exact Or.inl ⟨w, hW₂ hw, rfl⟩

/-! ## The canonical fusion equivalence -/

/-- The canonical re-labeling bijection
`α ⊕ ↑(W₁ ∪ W₂) ≃ (α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` between the
merged-splitting and iterated-splitting carriers. Built by composing
the Mathlib equivalences `Equiv.Set.union` (disjoint-union of sets),
`Equiv.sumAssoc` (sum reassociation), and `Equiv.Set.image` (transport
along an injective embedding). The disjointness hypothesis
`hdisj : Disjoint W₁ W₂` is consumed by `Equiv.Set.union`; injectivity
of `Sum.inl` is consumed by `Equiv.Set.image`.

## Design choice

* **Why `noncomputable`.** `Equiv.Set.union` reduces a union of sets
  to a `Sum`, which under the hood requires
  `[DecidablePred (· ∈ W₁)]` to dispatch each `w ∈ W₁ ∪ W₂` to its
  `W₁`-or-`W₂` summand. We supply that instance via
  `Classical.decPred`, but the result inherits `noncomputable`. The
  declaration appears `Prop`-relevantly only (in the type of
  `CDMGEquiv`-valued witnesses for the fusion lemma), so classical
  choice has no observable cost. This matches `NodeSplittingOn.lean`
  lines 84 -- 104 where the same trade-off was already made for
  `split1`; consistency across the section means no
  `noncomputable`-vs-computable boundary is introduced here. Plan §4
  Risk R3 records the concern that some computable chapter-8-onwards
  iSCM chain might hit a wall; the mitigation is that the iSCM
  chapters are already deep in `Prop`-valued (measure-theoretic)
  territory.

* **Built from Mathlib combinators, not hand-rolled.** Rolling the
  four constructor cases (`Sum.inl a` / `Sum.inr w` with `w ∈ W₁` /
  `w ∈ W₂`) and the two round-trip proofs `left_inv` / `right_inv`
  by hand would be ~30 lines of `dite`-laden case analysis (Plan
  §2.2 in `workspace_claim_3_7.md` walks through the cases). The
  Mathlib triple `Equiv.Set.union` + `Equiv.sumAssoc` +
  `Equiv.Set.image` packages the same content with the round-trip
  proofs already discharged, and its `_apply`-shaped `simp` lemmas
  (`Equiv.Set.union_apply_left` / `_right`, `Equiv.sumAssoc_apply`,
  `Equiv.Set.image_apply`) let Manager B's fusion-lemma proof
  discharge the four `image`-equality goals via `simp` rather than
  by unfolding hand-rolled match arms.

* **Codomain ends in `↑(Sum.inl '' W₂)`, not the cleaner `↑W₂`.**
  The iterated splitting
  `(G.nodeSplittingOn W₁ _).nodeSplittingOn (Sum.inl '' W₂) _` has
  carrier `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` directly from the
  signature of `nodeSplittingOn` -- its second argument is the
  `Set` `Sum.inl '' W₂`, not `W₂` itself. We accept this asymmetric
  wrapping (Plan §4 Risk R2); `Equiv.Set.image` transports the
  `↑W₂`-side internally, and consumers of the *fusion lemma* never
  see the extra subtype-of-image layer. Avoiding the wrapping would
  require touching `NodeSplittingOn.lean` to factor out a
  `nodeSplittingOn_carrier_lift` helper, which is out of scope for
  this row and would invalidate the prior row's design choices. -/
noncomputable def fusionEquiv (W₁ W₂ : Set α) (hdisj : Disjoint W₁ W₂) :
    α ⊕ ↑(W₁ ∪ W₂) ≃
      (α ⊕ ↑W₁) ⊕ ↑((Sum.inl : α → α ⊕ ↑W₁) '' W₂) :=
  letI : DecidablePred (· ∈ W₁) := Classical.decPred _
  (Equiv.sumCongr (Equiv.refl α) (Equiv.Set.union hdisj)).trans <|
    (Equiv.sumAssoc α ↑W₁ ↑W₂).symm.trans <|
      Equiv.sumCongr (Equiv.refl (α ⊕ ↑W₁))
        (Equiv.Set.image (Sum.inl : α → α ⊕ ↑W₁) W₂ Sum.inl_injective)

/-! ## The fusion lemma and the commute corollary -/

-- claim_3_7 (part 1/2)
-- title: TwoDisjointNode -- fusion lemma
--
-- Iterating two disjoint node-splittings is equivalent (modulo the
-- canonical re-labeling `fusionEquiv`) to a single node-splitting on
-- the union. The LN proves this as the first `=` of the chained
-- equality `(G_{spl(W₁)})_{spl(W₂)} = G_{spl(W₁ ⊔ W₂)}` -- the second
-- `=` (commute) follows by symmetry, formalised as
-- `nodeSplittingOn_comm_equiv` below.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 459 -- 463)
-- linewrapped within the prose paragraph and within the displayed
-- equation; LaTeX whitespace collapses, so this is verbatim under
-- \LaTeX semantics:

\begin{claimmark}
\begin{Lem}[Two disjoint node-splittings commute]
   Let $G=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins V$ two disjoint
   subsets of the output nodes of $G$.
   Then the CDMG obtained from first node-splitting $W_1$ and then
   node-splitting $W_2$ is the same CADMG that arises from first
   node-splitting $W_2$ and then node-splitting $W_1$:
   \[ \lp G_{\spl(W_1)} \rp_{\spl(W_2)} = \lp G_{\spl(W_2)} \rp_{\spl(W_1)}
      = G_{\spl(W_1 \dcup W_2)}. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_7 part 1/2 (fusion lemma): iterated node-splitting is
`CDMGEquiv`-equivalent to a single node-splitting on the union. Mirrors
the first half (`(G_{spl(W₁)})_{spl(W₂)} = G_{spl(W₁ ⊔ W₂)}`) of the
chained equality in the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 462. Body = `sorry`; the
Lean proof is Manager B's job (the LN's own proof at lines 466 -- 493
gives the four field-equality arguments).

## Design choice

* **`CDMGEquiv` rather than literal `Eq`.** The LN's `=` reads as
  set-equality after a re-labeling, but the two CDMGs in this
  statement live over *different* carrier types
  `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` (iterated) and `α ⊕ ↑(W₁ ∪ W₂)`
  (merged), so literal `Eq` is not even type-correct. `CDMGEquiv`
  is the categorified version: a bijection on carriers plus the
  four `image`-equalities on `J / V / E / L`. This realises the
  "modulo a re-labeling equivalence" telegraph in
  `NodeSplittingOn.lean` lines 43 -- 48 and is what claim_3_8's
  same-carrier literal `Eq` would *not* generalise to.

* **Fusion + commute split mirrors the LN's own proof structure.**
  The LN states a chained equality
  `(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ⊔ W₂)}`
  and only proves the fusion direction; the commute is "by
  symmetry" (LN line 493). We follow that factoring: fusion is the
  load-bearing lemma stated here, commute is the corollary
  `nodeSplittingOn_comm_equiv` below. This mirrors
  `HardInterventionsCommute.lean`'s claim_3_4 split for the
  same-shape claim, and matches Mathlib's `image_image` /
  `filter_filter` convention of naming the fusion lemma by
  doubling the construction name.

* **Explicit `hdisj : Disjoint W₁ W₂` on the fusion lemma, absent
  on the helper.** Disjointness is structurally required for
  `fusionEquiv` to be a bijection (the dispatch `w ∈ W₁` vs
  `w ∈ W₂` on the `↑(W₁ ∪ W₂)` carrier must not overlap), so it
  appears as an explicit hypothesis here and on
  `nodeSplittingOn_comm_equiv` -- matching the LN's "*two
  disjoint* subsets" phrasing. By contrast, the bridging helper
  `subset_nodeSplittingOn_V_of_subset_V` is independently
  free of `hdisj` (Plan §4 Risk R6); the hypothesis appears
  exactly where it is load-bearing, not threaded through the whole
  call chain. -/
noncomputable def nodeSplittingOn_nodeSplittingOn_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
          (Sum.inl '' W₂)
          (subset_nodeSplittingOn_V_of_subset_V hW₂ hW₁))
      (G.nodeSplittingOn (W₁ ∪ W₂) (Set.union_subset hW₁ hW₂)) := by
  letI : DecidablePred (· ∈ W₁) := Classical.decPred _
  -- `fusionEquiv` (forward direction) on each constructor case.
  have apply_inl : ∀ (a : α),
      fusionEquiv W₁ W₂ hdisj (Sum.inl a) = Sum.inl (Sum.inl a) := fun a => by
    simp [fusionEquiv]
  have apply_inr_left : ∀ (w : α) (hw₁ : w ∈ W₁) (hw : w ∈ W₁ ∪ W₂),
      fusionEquiv W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inl (Sum.inr ⟨w, hw₁⟩) := by
    intros w hw₁ hw
    have h_union : (Equiv.Set.union hdisj) ⟨w, hw⟩ = Sum.inl ⟨w, hw₁⟩ :=
      Equiv.Set.union_apply_left (a := ⟨w, hw⟩) hdisj hw₁
    simp [fusionEquiv, h_union]
  have apply_inr_right : ∀ (w : α) (hw₂ : w ∈ W₂) (hw : w ∈ W₁ ∪ W₂),
      fusionEquiv W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩ := by
    intros w hw₂ hw
    have h_union : (Equiv.Set.union hdisj) ⟨w, hw⟩ = Sum.inr ⟨w, hw₂⟩ :=
      Equiv.Set.union_apply_right (a := ⟨w, hw⟩) hdisj hw₂
    simp [fusionEquiv, h_union]
  -- Derive the symm-direction by `e.symm (e x) = x`.
  have symm_inl_inl : ∀ (a : α),
      (fusionEquiv W₁ W₂ hdisj).symm (Sum.inl (Sum.inl a)) = Sum.inl a := fun a => by
    rw [← apply_inl a]; exact Equiv.symm_apply_apply _ _
  have symm_inl_inr : ∀ (w : α) (hw₁ : w ∈ W₁) (hw : w ∈ W₁ ∪ W₂),
      (fusionEquiv W₁ W₂ hdisj).symm (Sum.inl (Sum.inr ⟨w, hw₁⟩)) =
        Sum.inr ⟨w, hw⟩ := fun w hw₁ hw => by
    rw [← apply_inr_left w hw₁ hw]; exact Equiv.symm_apply_apply _ _
  have symm_inr : ∀ (w : α) (hw₂ : w ∈ W₂) (hw : w ∈ W₁ ∪ W₂),
      (fusionEquiv W₁ W₂ hdisj).symm (Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩) =
        Sum.inr ⟨w, hw⟩ := fun w hw₂ hw => by
    rw [← apply_inr_right w hw₂ hw]; exact Equiv.symm_apply_apply _ _
  -- Key lemma for the E-field: `fusionEquiv` transports the source-side
  -- relabel of the merged splitting to the iterated source-side relabel.
  have key_e_source : ∀ (v : α),
      fusionEquiv W₁ W₂ hdisj (split1 (W₁ ∪ W₂) v) =
        split1 (Sum.inl '' W₂) (split1 W₁ v) := by
    intro v
    by_cases hv₁ : v ∈ W₁
    · -- v ∈ W₁: both sides land at `Sum.inl (Sum.inr ⟨v, hv₁⟩)`.
      have hv : v ∈ W₁ ∪ W₂ := Or.inl hv₁
      have hv_notin : (Sum.inr ⟨v, hv₁⟩ : α ⊕ ↑W₁) ∉ (Sum.inl '' W₂ : Set _) := by
        rintro ⟨_, _, h⟩; exact nomatch h
      rw [split1_of_mem hv, split1_of_mem hv₁, split1_of_not_mem hv_notin]
      exact apply_inr_left v hv₁ hv
    · by_cases hv₂ : v ∈ W₂
      · -- v ∈ W₂ (and v ∉ W₁): both sides land at `Sum.inr ⟨Sum.inl v, _⟩`.
        have hv : v ∈ W₁ ∪ W₂ := Or.inr hv₂
        have hv_mem : (Sum.inl v : α ⊕ ↑W₁) ∈ Sum.inl '' W₂ := ⟨v, hv₂, rfl⟩
        rw [split1_of_mem hv, split1_of_not_mem hv₁, split1_of_mem hv_mem]
        exact apply_inr_right v hv₂ hv
      · -- v ∉ W₁ ∪ W₂: both sides land at `Sum.inl (Sum.inl v)`.
        have hv : v ∉ W₁ ∪ W₂ := fun h => h.elim hv₁ hv₂
        have hv_notin : (Sum.inl v : α ⊕ ↑W₁) ∉ Sum.inl '' W₂ := by
          rintro ⟨w, hw, h⟩; exact hv₂ (Sum.inl_injective h ▸ hw)
        rw [split1_of_not_mem hv, split1_of_not_mem hv₁, split1_of_not_mem hv_notin]
        exact apply_inl v
  refine
    { toEquiv := (fusionEquiv W₁ W₂ hdisj).symm
      J_eq := ?_
      V_eq := ?_
      E_eq := ?_
      L_eq := ?_ }
  -- J_eq: H.J = (fusionEquiv).symm '' (iterated).J
  · simp only [nodeSplittingOn_J, Set.image_image]
    refine Set.image_congr (fun j _ => ?_)
    exact (symm_inl_inl j).symm
  -- V_eq: case-split on whether y is in the `Sum.inl '' V` piece or the
  -- `Set.range Sum.inr` piece.
  · simp only [nodeSplittingOn_V]
    ext y
    simp only [Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
      · -- y = Sum.inl v, v ∈ G.V
        refine ⟨Sum.inl (Sum.inl v),
          Or.inl ⟨Sum.inl v, Or.inl ⟨v, hv, rfl⟩, rfl⟩, ?_⟩
        exact symm_inl_inl v
      · rcases hw with hw₁ | hw₂
        · -- w ∈ W₁: lift via the outer Sum.inl in the iterated splitting.
          refine ⟨Sum.inl (Sum.inr ⟨w, hw₁⟩),
            Or.inl ⟨Sum.inr ⟨w, hw₁⟩, Or.inr ⟨⟨w, hw₁⟩, rfl⟩, rfl⟩, ?_⟩
          exact symm_inl_inr w hw₁ (Or.inl hw₁)
        · -- w ∈ W₂: in the outer splitting's range piece.
          refine ⟨Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩,
            Or.inr ⟨⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩, rfl⟩, ?_⟩
          exact symm_inr w hw₂ (Or.inr hw₂)
    · rintro ⟨x, hx, rfl⟩
      rcases hx with (⟨z, hz, rfl⟩ | ⟨⟨w_val, hw_val⟩, rfl⟩)
      · rcases hz with (⟨v, hv, rfl⟩ | ⟨⟨w₁, hw₁⟩, rfl⟩)
        · -- x = Sum.inl (Sum.inl v) for v ∈ G.V
          refine Or.inl ⟨v, hv, ?_⟩
          exact (symm_inl_inl v).symm
        · -- x = Sum.inl (Sum.inr ⟨w₁, hw₁⟩) for hw₁ : w₁ ∈ W₁
          refine Or.inr ⟨⟨w₁, Or.inl hw₁⟩, ?_⟩
          exact (symm_inl_inr w₁ hw₁ (Or.inl hw₁)).symm
      · -- x = Sum.inr ⟨w_val, hw_val⟩ for hw_val : w_val ∈ Sum.inl '' W₂
        obtain ⟨w', hw'₂, rfl⟩ := hw_val
        refine Or.inr ⟨⟨w', Or.inr hw'₂⟩, ?_⟩
        exact (symm_inr w' hw'₂ (Or.inr hw'₂)).symm
  -- E_eq: three sub-pieces matched via `mem_nodeSplittingOn_E` + the
  -- key `split1`-transport lemma above.
  · ext y
    rw [Set.mem_image, mem_nodeSplittingOn_E]
    constructor
    · rintro (⟨v₁, v₂, hE, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
      · -- y comes from the original-edge relabel piece on the merged side.
        refine ⟨(split1 (Sum.inl '' W₂) (split1 W₁ v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
        · rw [mem_nodeSplittingOn_E]
          refine Or.inl ⟨split1 W₁ v₁, Sum.inl v₂, ?_, rfl⟩
          rw [mem_nodeSplittingOn_E]
          exact Or.inl ⟨v₁, v₂, hE, rfl⟩
        · refine Prod.ext ?_ ?_
          · change (fusionEquiv W₁ W₂ hdisj).symm (split1 (Sum.inl '' W₂) (split1 W₁ v₁))
              = split1 (W₁ ∪ W₂) v₁
            rw [← key_e_source]
            exact Equiv.symm_apply_apply _ _
          · exact symm_inl_inl v₂
      · rcases hw with hw₁ | hw₂
        · -- w ∈ W₁: matched by the W₁-split edge lifted via the outer Sum.inl.
          have h_notmem : (Sum.inl w : α ⊕ ↑W₁) ∉ Sum.inl '' W₂ := by
            rintro ⟨w'', hw'', h⟩
            exact (Set.disjoint_left.mp hdisj hw₁) (Sum.inl_injective h ▸ hw'')
          refine ⟨(Sum.inl (Sum.inl w), Sum.inl (Sum.inr ⟨w, hw₁⟩)), ?_, ?_⟩
          · rw [mem_nodeSplittingOn_E]
            refine Or.inl ⟨Sum.inl w, Sum.inr ⟨w, hw₁⟩, ?_, ?_⟩
            · rw [mem_nodeSplittingOn_E]
              exact Or.inr ⟨⟨w, hw₁⟩, rfl⟩
            · rw [split1_of_not_mem h_notmem]
          · refine Prod.ext ?_ ?_
            · exact symm_inl_inl w
            · exact symm_inl_inr w hw₁ (Or.inl hw₁)
        · -- w ∈ W₂: matched by the W₂-split edge in the outer splitting.
          refine ⟨(Sum.inl (Sum.inl w),
                    Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩), ?_, ?_⟩
          · rw [mem_nodeSplittingOn_E]
            exact Or.inr ⟨⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩, rfl⟩
          · refine Prod.ext ?_ ?_
            · exact symm_inl_inl w
            · exact symm_inr w hw₂ (Or.inr hw₂)
    · rintro ⟨p, hp, rfl⟩
      rw [mem_nodeSplittingOn_E] at hp
      rcases hp with (⟨a₁, a₂, ha, rfl⟩ | ⟨⟨w_val, hw_val⟩, rfl⟩)
      · rw [mem_nodeSplittingOn_E] at ha
        rcases ha with (⟨v₁, v₂, hE, h_eq⟩ | ⟨⟨w₁, hw₁⟩, h_eq⟩)
        · -- Original edge double-relabeled.
          injection h_eq with h_eq1 h_eq2
          subst h_eq1; subst h_eq2
          refine Or.inl ⟨v₁, v₂, hE, ?_⟩
          refine Prod.ext ?_ ?_
          · change (fusionEquiv W₁ W₂ hdisj).symm (split1 (Sum.inl '' W₂) (split1 W₁ v₁))
              = split1 (W₁ ∪ W₂) v₁
            rw [← key_e_source]
            exact Equiv.symm_apply_apply _ _
          · exact symm_inl_inl v₂
        · -- Inner W₁-split edge lifted via outer Sum.inl.
          injection h_eq with h_eq1 h_eq2
          subst h_eq1; subst h_eq2
          have h_notmem : (Sum.inl w₁ : α ⊕ ↑W₁) ∉ Sum.inl '' W₂ := by
            rintro ⟨w'', hw'', h⟩
            exact (Set.disjoint_left.mp hdisj hw₁) (Sum.inl_injective h ▸ hw'')
          refine Or.inr ⟨⟨w₁, Or.inl hw₁⟩, ?_⟩
          rw [split1_of_not_mem h_notmem]
          refine Prod.ext ?_ ?_
          · exact symm_inl_inl w₁
          · exact symm_inl_inr w₁ hw₁ (Or.inl hw₁)
      · -- Outer (Sum.inl '' W₂)-split edge.
        obtain ⟨w', hw'₂, rfl⟩ := hw_val
        refine Or.inr ⟨⟨w', Or.inr hw'₂⟩, ?_⟩
        refine Prod.ext ?_ ?_
        · exact symm_inl_inl w'
        · exact symm_inr w' hw'₂ (Or.inr hw'₂)
  -- L_eq: bidirected edges, both sides reduce to double-Sum.inl on G.L.
  · ext y
    rw [Set.mem_image, mem_nodeSplittingOn_L]
    constructor
    · rintro ⟨v₁, v₂, hL, rfl⟩
      refine ⟨(Sum.inl (Sum.inl v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
      · rw [mem_nodeSplittingOn_L]
        refine ⟨Sum.inl v₁, Sum.inl v₂, ?_, rfl⟩
        rw [mem_nodeSplittingOn_L]
        exact ⟨v₁, v₂, hL, rfl⟩
      · refine Prod.ext ?_ ?_
        · exact symm_inl_inl v₁
        · exact symm_inl_inl v₂
    · rintro ⟨p, hp, rfl⟩
      rw [mem_nodeSplittingOn_L] at hp
      obtain ⟨a, b, hab, rfl⟩ := hp
      rw [mem_nodeSplittingOn_L] at hab
      obtain ⟨v₁, v₂, hL, h_eq⟩ := hab
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      refine ⟨v₁, v₂, hL, ?_⟩
      refine Prod.ext ?_ ?_
      · exact symm_inl_inl v₁
      · exact symm_inl_inl v₂

-- claim_3_7 (part 2/2)
-- title: TwoDisjointNode -- commute corollary
--
-- The two iterations agree (modulo re-labeling): swapping `W₁` and
-- `W₂` in the iteration gives a `CDMGEquiv`-equivalent CDMG. Manager B
-- derives this by `(fusion W₁ W₂ hdisj).trans (fusion W₂ W₁ hdisj.symm).symm`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 459 -- 463)
-- linewrapped within the prose paragraph and within the displayed
-- equation; LaTeX whitespace collapses, so this is verbatim under
-- \LaTeX semantics:

\begin{claimmark}
\begin{Lem}[Two disjoint node-splittings commute]
   Let $G=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins V$ two disjoint
   subsets of the output nodes of $G$.
   Then the CDMG obtained from first node-splitting $W_1$ and then
   node-splitting $W_2$ is the same CADMG that arises from first
   node-splitting $W_2$ and then node-splitting $W_1$:
   \[ \lp G_{\spl(W_1)} \rp_{\spl(W_2)} = \lp G_{\spl(W_2)} \rp_{\spl(W_1)}
      = G_{\spl(W_1 \dcup W_2)}. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_7 part 2/2 (commute corollary): swapping `W₁` and `W₂` in
the iterated node-splitting yields a `CDMGEquiv`-equivalent CDMG.
Mirrors the second half
(`(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)}`) of the chained
equality in the `\Lem` at `lecture-notes/lecture_notes/graphs.tex`
line 462. Body = `sorry`; Manager B derives this by composing the
fusion lemma with its `Disjoint.symm`-variant via `CDMGEquiv.trans` /
`.symm`.

## Design choice

* **Derived from the fusion lemma, not re-proven from scratch.**
  Once `nodeSplittingOn_nodeSplittingOn_equiv` is in hand for both
  `(W₁, W₂, hdisj)` and `(W₂, W₁, hdisj.symm)`, Manager B's proof
  is a one-line composition
  `(fusion W₁ W₂ hdisj).trans (fusion W₂ W₁ hdisj.symm).symm`.
  This is the entire payoff of shipping `CDMGEquiv.refl / symm /
  trans` with the structure, and is the Lean transcription of the
  LN's "the other follows by symmetry" close at `graphs.tex` line
  493. Both invocations of `fusion` land in `G_{spl(W₁ ∪ W₂)}` (set
  equality `W₁ ∪ W₂ = W₂ ∪ W₁` is absorbed into the `image`-equality
  fields of `CDMGEquiv`), so no separate `Set.union_comm` rewrite is
  required.

* **Standalone declaration, not folded into the fusion lemma's
  conclusion.** Downstream consumers that want to *swap* two
  node-splittings (without collapsing them) reach for this form
  directly; folding it inside the fusion lemma would force every
  such consumer to chain two fusion calls themselves, an extra step
  every time. Same reasoning as `hardInterventionOn_comm` vs
  `hardInterventionOn_hardInterventionOn` in
  `HardInterventionsCommute.lean`, and exposes the LN's chained
  equality as two named Lean facts a consumer can pick between by
  the `rw`-shape they need. -/
noncomputable def nodeSplittingOn_comm_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
          (Sum.inl '' W₂)
          (subset_nodeSplittingOn_V_of_subset_V hW₂ hW₁))
      ((G.nodeSplittingOn W₂ hW₂).nodeSplittingOn
          (Sum.inl '' W₁)
          (subset_nodeSplittingOn_V_of_subset_V hW₁ hW₂)) := by
  -- Build the small bridge CDMGEquiv between the two merged CDMGs
  -- (over `W₁ ∪ W₂` and over `W₂ ∪ W₁` respectively). The two CDMGs are
  -- equal as Set α-valued data, but their carrier types differ since
  -- `↑(W₁ ∪ W₂) ≠ ↑(W₂ ∪ W₁)` def-equally. The bridge absorbs the
  -- `Set.union_comm` discrepancy via the subtype-relabel Equiv
  -- `Equiv.subtypeEquivRight (fun _ => Or.comm)`.
  let σ : ↑(W₁ ∪ W₂) ≃ ↑(W₂ ∪ W₁) := Equiv.subtypeEquivRight (fun _ => Or.comm)
  let toEq : (α ⊕ ↑(W₁ ∪ W₂)) ≃ (α ⊕ ↑(W₂ ∪ W₁)) :=
    Equiv.sumCongr (Equiv.refl α) σ
  have toEq_inl : ∀ (a : α),
      toEq (Sum.inl a) = Sum.inl a := fun a => rfl
  have toEq_inr : ∀ (a : α) (h : a ∈ W₁ ∪ W₂) (h' : a ∈ W₂ ∪ W₁),
      toEq (Sum.inr ⟨a, h⟩) = Sum.inr ⟨a, h'⟩ := fun _ _ _ => rfl
  have toEq_split1 : ∀ (v : α),
      toEq (split1 (W₁ ∪ W₂) v) = split1 (W₂ ∪ W₁) v := by
    intro v
    by_cases hv : v ∈ W₁ ∪ W₂
    · have hv' : v ∈ W₂ ∪ W₁ := hv.symm
      rw [split1_of_mem hv, split1_of_mem hv']
      exact toEq_inr v hv hv'
    · have hv' : v ∉ W₂ ∪ W₁ := fun h => hv h.symm
      rw [split1_of_not_mem hv, split1_of_not_mem hv']
      exact toEq_inl v
  let bridge : CDMGEquiv
      (G.nodeSplittingOn (W₁ ∪ W₂) (Set.union_subset hW₁ hW₂))
      (G.nodeSplittingOn (W₂ ∪ W₁) (Set.union_subset hW₂ hW₁)) :=
  { toEquiv := toEq
    J_eq := by
      simp only [nodeSplittingOn_J, Set.image_image]
      refine Set.image_congr (fun j _ => ?_)
      exact (toEq_inl j).symm
    V_eq := by
      simp only [nodeSplittingOn_V, Set.image_union]
      congr 1
      · rw [Set.image_image]
        refine Set.image_congr (fun v _ => ?_)
        exact (toEq_inl v).symm
      · ext y
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨w', rfl⟩
          refine ⟨Sum.inr (σ.symm w'), ⟨σ.symm w', rfl⟩, ?_⟩
          show toEq (Sum.inr (σ.symm w')) = Sum.inr w'
          simp [toEq, Equiv.sumCongr_apply, Equiv.apply_symm_apply]
        · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
          exact ⟨σ w, rfl⟩
    E_eq := by
      ext y
      rw [Set.mem_image, mem_nodeSplittingOn_E]
      constructor
      · rintro (⟨v₁, v₂, hE, rfl⟩ | ⟨⟨w, hw'⟩, rfl⟩)
        · refine ⟨(split1 (W₁ ∪ W₂) v₁, Sum.inl v₂), ?_, ?_⟩
          · rw [mem_nodeSplittingOn_E]
            exact Or.inl ⟨v₁, v₂, hE, rfl⟩
          · refine Prod.ext ?_ ?_
            · exact toEq_split1 v₁
            · exact toEq_inl v₂
        · have hw : w ∈ W₁ ∪ W₂ := hw'.symm
          refine ⟨(Sum.inl w, Sum.inr ⟨w, hw⟩), ?_, ?_⟩
          · rw [mem_nodeSplittingOn_E]
            exact Or.inr ⟨⟨w, hw⟩, rfl⟩
          · refine Prod.ext ?_ ?_
            · exact toEq_inl w
            · exact toEq_inr w hw hw'
      · rintro ⟨p, hp, rfl⟩
        rw [mem_nodeSplittingOn_E] at hp
        rcases hp with (⟨v₁, v₂, hE, h_eq⟩ | ⟨⟨w, hw⟩, h_eq⟩)
        · subst h_eq
          refine Or.inl ⟨v₁, v₂, hE, ?_⟩
          refine Prod.ext ?_ ?_
          · exact toEq_split1 v₁
          · exact toEq_inl v₂
        · subst h_eq
          have hw' : w ∈ W₂ ∪ W₁ := hw.symm
          refine Or.inr ⟨⟨w, hw'⟩, ?_⟩
          refine Prod.ext ?_ ?_
          · exact toEq_inl w
          · exact toEq_inr w hw hw'
    L_eq := by
      ext y
      rw [Set.mem_image, mem_nodeSplittingOn_L]
      constructor
      · rintro ⟨v₁, v₂, hL, rfl⟩
        refine ⟨(Sum.inl v₁, Sum.inl v₂), ?_, ?_⟩
        · rw [mem_nodeSplittingOn_L]; exact ⟨v₁, v₂, hL, rfl⟩
        · refine Prod.ext ?_ ?_
          · exact toEq_inl v₁
          · exact toEq_inl v₂
      · rintro ⟨p, hp, rfl⟩
        rw [mem_nodeSplittingOn_L] at hp
        obtain ⟨v₁, v₂, hL, h_eq⟩ := hp
        subst h_eq
        refine ⟨v₁, v₂, hL, ?_⟩
        refine Prod.ext ?_ ?_
        · exact toEq_inl v₁
        · exact toEq_inl v₂ }
  exact (nodeSplittingOn_nodeSplittingOn_equiv hW₁ hW₂ hdisj).trans
    (bridge.trans (nodeSplittingOn_nodeSplittingOn_equiv hW₂ hW₁ hdisj.symm).symm)

end CDMG

end Causality
