import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Extension.Linear

-- TeX proof: claim_3_2_proof_AcyclicIffTopologicalOrder.tex

/-!
# Acyclicity iff existence of a topological order (claim_3_2)

This file formalises the lecture notes' Lemma immediately following
the definition of a topological order (def_3_8): a Conditional
Directed Mixed Graph `G = (J, V, E, L)` is *acyclic* (def_3_6) iff
it *has* a topological order (def_3_8). In Lean:

```
G.IsAcyclic ↔ G.HasTopologicalOrder
```

with `IsAcyclic` from `Acyclicity.lean` and `HasTopologicalOrder`
from `TopologicalOrder.lean`. The statement is the existential
reading of the LN's "has a topological order" — the relation-level
variant `IsTopologicalOrder G r` is *not* the right-hand side here,
because the LN's prose existentially quantifies the order (see the
design-choice block below).

The LN includes its own proof in a `\Claude{...}` block at
`graphs.tex:227--245`: the (⇐) direction contradicts a
hypothetical non-trivial directed cycle
`v_0 < v_1 < ... < v_n = v_0` against the topological order's
`irrefl` + `trans`; the (⇒) direction iteratively selects a
parent-free node from the induced subgraph on the still-unselected
nodes and uses *finiteness* of `J ∪ V` to terminate. The use of
finiteness in the LN proof drives the `[Finite α]` hypothesis on
the iff (see the design-choice block).

## Where this gets used downstream

The iff is one of the load-bearing equivalences of the whole
project: it lets every later chapter freely translate between the
graph-theoretic "$G$ is acyclic" precondition and the constructive
"let `<` be a topological order of $G$" hypothesis. Concretely:

* **claim_3_3** (`graphs.tex` Rem 311) — "if $G$ is acyclic then
  also $G_{\doit(W)}$ is acyclic, and a topological order for $G$ is
  also one for $G_{\doit(W)}$". Hard-intervention preservation of
  both sides of the iff is its own row but quotes claim_3_2 to
  bounce between the two predicates.
* **def_3_7** (graph-shape names CADMG / ADMG / DAG / …) — the iff
  lets these names be characterised either via "no directed cycle"
  or via "admits a topological order"; downstream rows that
  pattern-match on `G.IsCADMG` reach for whichever side is more
  convenient.
* **chapter 4 (CBNs, `causal_bayesian_networks.tex`)** — Causal
  Bayesian Networks factorise `P(V | J)` as a product indexed by
  parents *along a chosen topological order*. The iff is what
  guarantees the order exists from the CBN's acyclicity hypothesis,
  enabling the recursive factorisation.
* **chapter 5 (do-calculus, `do-calculus.tex`,
  `proof-do-calculus.tex`)** — the soundness proofs of the three
  do-calculus rules induct *along* a topological order of the CADMG.
  The iff is the bridge from "the underlying graph is acyclic" to
  "we have an order to induct on".
* **chapter 6 (ID-algorithm, `id-algorithm.tex`)** — the
  ID-algorithm takes "a CADMG `G` with a fixed topological order `<`"
  as input. Concrete examples in the chapter (lines 698, 786, 942)
  use prose like "we have the topological order `v_1 < v_2 < v_3`",
  derived from claim_3_2 applied to the CADMG.
* **chapters 8 -- 10 (SCMs / iSCMs, `scms.tex` -- `scms4.tex`)** —
  the unique-solution theory of acyclic iSCMs proceeds by recursion
  along a topological order of the underlying graph `G^+`. The
  recursion is *only* well-founded because `G^+` is acyclic, and the
  topological order is exactly what packages that well-foundedness
  (cf. `scms3.tex:296`: "its graph $G^+$ is acyclic, and hence has a
  topological order $<$. Consider $f_v$, the causal mechanism for
  $v \in V$. The parents $\Pa^{G^+}(v)$ precede $v$ in the
  topological order.").
* **chapters 11 -- 16 (causal discovery, `fci.tex`, `icdf.tex`,
  `proof-icdf.tex`)** — FCI / IC discovery algorithms assume an
  acyclic ground-truth graph and reason about it via topological
  orders of the candidate output graphs.

## References

  * `lecture-notes/lecture_notes/graphs.tex`, Lem at lines 222 -- 226
    (the `\begin{claimmark}\begin{Lem}...\end{Lem}\end{claimmark}`
    block immediately after `def_3_8` `TopologicalOrder`).
  * `def_3_6` — `Chapter3_GraphTheory.Section3_1.Acyclicity`:
    `CDMG.IsAcyclic`.
  * `def_3_8` — `Chapter3_GraphTheory.Section3_1.TopologicalOrder`:
    `CDMG.IsTopologicalOrder` (relation-level) and
    `CDMG.HasTopologicalOrder` (existential closure).
  * `def_3_1` — `Chapter3_GraphTheory.Section3_1.CDMG`: the `CDMG`
    structure with its polymorphic vertex type `α`; in particular,
    no built-in finiteness is supplied by `def_3_1`, motivating the
    extra `[Finite α]` instance hypothesis on this iff.

The theorem below is fully proved. The Lean proof diverges from
the LN's iterative parent-free-node-pick route in favour of
Mathlib's `extend_partialOrder` (Szpilrajn) applied to the
"reachable by a directed walk" preorder on `α`; see the
per-declaration comment block above the `theorem` declaration
for the design rationale.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

/-- Helper (private to this file): appending two directed walks gives
a directed walk. Used to chain directed walks through transitivity of
the "reachable by a directed walk" preorder in the (⇒) direction
below. Kept private; we do not allocate a row ref for it. -/
private lemma directedWalk_append {G : CDMG α} :
    ∀ {v w u : α} (π₁ : Walk G v w) (π₂ : Walk G w u),
      π₁.IsDirected → π₂.IsDirected → (π₁.append π₂).IsDirected := by
  intro v w u π₁
  induction π₁ with
  | nil _ => intro π₂ _ h₂; simpa using h₂
  | @cons _ _ _ s p ih =>
    intro π₂ h_dir h₂
    cases s with
    | forward _ =>
      simp only [Walk.cons_append, Walk.isDirected_cons_forward] at h_dir ⊢
      exact ih π₂ h_dir h₂
    | backward _ => simp at h_dir
    | bidir _ => simp at h_dir

/-- Helper (private to this file): in a topological order `r`, every
directed walk of positive length `π : Walk G v w` satisfies `r v w`
(and `v, w ∈ G`). This is the inductive heart of the (⇐) direction:
chains `parent_lt` along each `forward` step and uses `trans` between
them. Kept private; we do not allocate a row ref for it. -/
private lemma topo_lt_of_directed_walk_pos
    {G : CDMG α} {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    ∀ {v w : α} (π : Walk G v w), π.IsDirected → 1 ≤ π.length →
      v ∈ G ∧ w ∈ G ∧ r v w := by
  intro v w π
  induction π with
  | nil _ => intro _ h; simp at h
  | @cons a b c s p ih =>
    intro h_dir h_pos
    cases s with
    | forward h =>
      have habE := G.E_subset h
      have ha_jv : a ∈ G.J ∪ G.V := (Set.mem_prod.mp habE).1
      have hb_v : b ∈ G.V := (Set.mem_prod.mp habE).2
      have ha : a ∈ G := CDMG.mem_iff.mpr ha_jv
      have hb : b ∈ G := CDMG.mem_iff.mpr (Or.inr hb_v)
      have h_pa : a ∈ Pa G b := ⟨ha, h⟩
      have h_ab : r a b := hr.parent_lt h_pa
      have h_p_dir : p.IsDirected := by
        simp only [Walk.isDirected_cons_forward] at h_dir; exact h_dir
      by_cases hp_pos : 1 ≤ p.length
      · obtain ⟨_, hc, h_bc⟩ := ih h_p_dir hp_pos
        exact ⟨ha, hc, hr.trans a ha b hb c hc h_ab h_bc⟩
      · have hp_zero : p.length = 0 := by omega
        cases p with
        | nil _ => exact ⟨ha, hb, h_ab⟩
        | cons _ _ => simp [Walk.length_cons] at hp_zero
    | backward _ => simp at h_dir
    | bidir _ => simp at h_dir


-- claim_3_2 (refactored: no-finiteness variant)
-- title: AcyclicIffTopologicalOrder
--
-- A CDMG `G = (J, V, E, L)` is *acyclic* iff it *has* a topological
-- order. The LN states this without any finiteness hypothesis on the
-- vertex set, and (as our proof witnesses) the equivalence holds for
-- arbitrary `α` --- no `[Finite α]` instance is required. See the
-- design block below for the discussion of why the LN's prose
-- mentions finiteness only inside its *proof* (its iterative parent-
-- free-node construction needs it) but the statement itself is
-- finiteness-free, and how the Lean proof discharges the (⇒)
-- direction via Mathlib's `extend_partialOrder` (Szpilrajn) on the
-- "reachable by a directed walk" preorder rather than the LN's
-- iterative construction.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem after
def 3.8, lines 222 -- 226):

\begin{claimmark}
\begin{Lem}
        A CDMG  $G=(J,V,E,L)$ is acyclic if and only if it has a topological order.
\end{Lem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **No `[Finite α]` hypothesis.** The LN states the lemma without
--   any finiteness assumption on the vertex set, and our Lean proof
--   honours that --- the equivalence holds for arbitrary `α` via the
--   Szpilrajn route discussed below (which does not enumerate
--   vertices). Removing `[Finite α]` makes the lemma applicable
--   downstream to iSCMs (chapters 8 -- 10) and other settings where
--   the vertex type is not assumed finite at the statement level.
--   Concrete beneficiaries already foreshadowed in the codebase:
--   `claim_3_6` part B (`isAcyclic_nodeSplittingOn` in
--   `Section3_2/SplitTopologicalOrder.lean`) explicitly kept its own
--   `[Finite α]` off and noted that route (i) of its proof would have
--   needed it via this very iff --- once this refactor lands, that
--   route becomes finiteness-free too. Similar wins propagate
--   through claim_3_12 / _16 / _17 / _18 / _19 / _23 / _27, all
--   listed as dependents in the refactor table.
--
-- * **Existential right-hand side `G.HasTopologicalOrder`, not the
--   relation-level `IsTopologicalOrder G r`.** The LN's Lem reads
--   "G ... has a topological order" --- the order is existentially
--   quantified. `HasTopologicalOrder` (def in
--   `TopologicalOrder.lean`) is exactly the unwrap
--   `∃ r, IsTopologicalOrder G r`, so it lines up verbatim with the
--   LN's "has". An alternative iff `G.IsAcyclic ↔ ∀ r,
--   IsTopologicalOrder G r` would be false (the trivial relation is
--   never a topological order of a non-empty graph), and
--   `G.IsAcyclic ↔ IsTopologicalOrder G r` for a *fixed* `r` would
--   be a strictly stronger statement that the LN does not make.
--   Both `Acyclicity.lean` (its `Where this gets used downstream`
--   block) and `TopologicalOrder.lean` (its `HasTopologicalOrder`
--   docstring) already commit the project to this exact shape, so
--   choosing the existential reading also keeps cross-file
--   references consistent.
--
-- * **Why Szpilrajn rather than the LN's iterative parent-free-node
--   construction (in the (⇒) direction).** The LN's construction
--   needs `|J ∪ V|` to be finite to terminate --- `graphs.tex` line
--   238 explicitly invokes "since `G_i` is acyclic ... and finite,
--   it has a node `v_i` with `\Pa^{G_i}(v_i) = ∅`" --- and would
--   force a `[Finite α]` hypothesis back onto the statement. The
--   Szpilrajn route (`extend_partialOrder` applied to the "reachable
--   by a directed walk" preorder `r₀`) is *strictly more general*: it
--   does not enumerate vertices, so it works for arbitrary `α` while
--   establishing the same equivalence the LN claims. Antisymmetry of
--   `r₀` under acyclicity is the load-bearing observation --- a
--   two-way directed walk between distinct nodes appends into a
--   non-trivial directed cycle, which `IsAcyclic` forbids.
--
--   The walk-based preorder `r₀` is chosen over the semantically
--   equivalent "ancestor of" relation because walk concatenation
--   discharges transitivity and antisymmetry directly: the appended
--   walk *is* the cycle witness under acyclicity, and the `Walk`
--   inductive already carries the structural recursion needed for
--   the `directedWalk_append` helper above. An ancestor-defined
--   preorder would have to first reify the reflexive-transitive
--   closure of `Pa^G`, then re-derive the same chaining.
--
--   The LN's iterative construction itself stays preserved verbatim
--   in the *original* proof tex
--   `tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex` (which
--   stays on disk untouched until Phase 7 cleanup), so the finite-
--   context reasoning is not lost. The refactor twin
--   `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex`
--   will carry the Szpilrajn route that this Lean theorem follows
--   and is what the cleanup script promotes over the original at
--   Phase 7.
--
-- * **Namespacing
--   `Causality.CDMG.isAcyclic_iff_hasTopologicalOrder`,
--   dot-projection intended.** Downstream callers write
--   `G.isAcyclic_iff_hasTopologicalOrder.mp ha` (acyclic ⇒ has topo
--   order) and similarly `.mpr` for the reverse direction. The name
--   reads as the LN's prose "G is acyclic iff G has a topological
--   order" and parallels every other claim-of-`CDMG` theorem in this
--   section (`no_arrowhead_into_input`, `input_edge_target_mem_V`,
--   `input_nodes_not_adjacent` in `JNodeProperties.lean`). Splitting
--   into two separate lemmas (`isAcyclic_of_hasTopologicalOrder` and
--   `hasTopologicalOrder_of_isAcyclic`) was considered, but the LN
--   states the equivalence as a single Lem; bundling them as one iff
--   matches that prose and lets `simp` / `rw` rewrite freely between
--   the two predicates.
--
-- * **`α` implicit, `G` explicit.** Standard for "fix a graph, then
--   state a property of it" theorems; matches every other theorem in
--   the section (`Acyclicity`, `TopologicalOrder`,
--   `JNodeProperties`, the `Family*` files).
/-- claim_3_2 (`AcyclicIffTopologicalOrder`, refactored: no
finiteness): a CDMG `G` is acyclic iff it has a topological order.
Mirrors `lecture-notes/lecture_notes/graphs.tex` Lem at line 224
verbatim, using `CDMG.IsAcyclic` (def_3_6) on the left and the
existential `CDMG.HasTopologicalOrder` (def_3_8) on the right. **No
`[Finite α]` hypothesis** --- the LN states the lemma without
finiteness, and the Lean proof uses `extend_partialOrder`
(Szpilrajn) on the "reachable by a directed walk" preorder for the
(⇒) direction, which does not require finiteness. See the design
block above for the trade-off vs. the LN's iterative construction
and the list of downstream rows whose `[Finite α]` baggage this
refactor lifts. -/
theorem isAcyclic_iff_hasTopologicalOrder
    (G : CDMG α) :
    G.IsAcyclic ↔ G.HasTopologicalOrder := by
  refine ⟨?_, ?_⟩
  · -- (⇒) acyclic ⇒ has topological order, via Szpilrajn on the
    -- "reachable by a directed walk" preorder. No finiteness needed.
    intro hac
    -- The "reachable by a directed walk" preorder.
    let r₀ : α → α → Prop := fun v w => ∃ π : Walk G v w, π.IsDirected
    -- Refl: take the trivial walk.
    have hr₀_refl : ∀ v, r₀ v v := fun v => ⟨Walk.nil v, by simp⟩
    -- Trans: concat directed walks.
    have hr₀_trans : ∀ x y z, r₀ x y → r₀ y z → r₀ x z := by
      rintro x y z ⟨π₁, h₁⟩ ⟨π₂, h₂⟩
      exact ⟨π₁.append π₂, directedWalk_append π₁ π₂ h₁ h₂⟩
    -- Antisymm: under acyclicity, any two-way directed walk closes
    -- into a cycle through `x`.
    have hr₀_antisymm : ∀ x y, r₀ x y → r₀ y x → x = y := by
      rintro x y ⟨π₁, h₁⟩ ⟨π₂, h₂⟩
      by_contra h_neq
      cases π₁ with
      | nil _ => exact h_neq rfl
      | cons s p =>
        cases s with
        | forward h_e =>
          have hx : x ∈ G :=
            CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset h_e)).1
          have h_cycle_dir : ((Walk.cons (.forward h_e) p).append π₂).IsDirected :=
            directedWalk_append _ _ h₁ h₂
          have h_cycle_pos :
              1 ≤ ((Walk.cons (.forward h_e) p).append π₂).length := by
            rw [Walk.length_append, Walk.length_cons]; omega
          exact hac x hx ⟨_, h_cycle_dir, h_cycle_pos⟩
        | backward _ => simp at h₁
        | bidir _ => simp at h₁
    -- Register `r₀` as a partial order; apply Mathlib's Szpilrajn.
    haveI : IsPartialOrder α r₀ :=
      { refl := hr₀_refl, trans := hr₀_trans, antisymm := hr₀_antisymm }
    obtain ⟨s, hs_lin, hrs⟩ := extend_partialOrder r₀
    haveI : IsLinearOrder α s := hs_lin
    -- The strict part of `s` is the topological order.
    refine ⟨fun v w => s v w ∧ v ≠ w, ?_, ?_, ?_, ?_⟩
    · intro v _ ⟨_, hne⟩; exact hne rfl
    · intro v _ w hw u _ ⟨hsvw, hne_vw⟩ ⟨hswu, _⟩
      refine ⟨_root_.trans hsvw hswu, ?_⟩
      intro h_eq
      subst h_eq
      exact hne_vw (_root_.antisymm hsvw hswu)
    · intro v _ w _
      rcases eq_or_ne v w with rfl | hne
      · exact Or.inr (Or.inl rfl)
      · rcases total_of s v w with h | h
        · exact Or.inl ⟨h, hne⟩
        · exact Or.inr (Or.inr ⟨h, hne.symm⟩)
    · intro v w h_pa
      obtain ⟨hv, h_edge⟩ := h_pa
      have hr0 : r₀ v w :=
        ⟨Walk.cons (.forward h_edge) (Walk.nil w), by simp⟩
      have hsvw : s v w := hrs v w hr0
      have hne : v ≠ w := by
        intro h_eq; subst h_eq
        exact hac v hv
          ⟨Walk.cons (.forward h_edge) (Walk.nil v), by simp, by simp⟩
      exact ⟨hsvw, hne⟩
  · -- (⇐) has topological order ⇒ acyclic. No finiteness used.
    rintro ⟨r, hr⟩ v hv ⟨π, h_dir, h_pos⟩
    obtain ⟨_, _, h_rvv⟩ :=
      topo_lt_of_directed_walk_pos hr π h_dir h_pos
    exact hr.irrefl v hv h_rvv

end CDMG

end Causality
