import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable

-- TeX proof: claim_3_20_proof_AcyclicNonCollidersBlockable.tex

/-!
# Acyclic CDMGs make all non-colliders blockable (claim_3_20)

This file formalises *claim 3.20* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`, lines
1256 -- 1261): a `\begin{claimmark}\begin{Rem}...\end{Rem}\end{claimmark}`
remark sitting between def_3_16 (blockable / unblockable
non-colliders) and def_3_17 ($\sigma$-blocked walks):

> If $G$ is acyclic then all non-colliders are blockable.

Under the def_3_16 paradigm, "all non-colliders are blockable"
reads pointwise: for every walk $\pi$ in $G$ and every position
$k$ on $\pi$, the implication
`IsNonColliderAt k → IsBlockableNonColliderAt k` holds whenever
`G` is acyclic.

## What this file contributes

A single `theorem`,
`Walk.isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`,
with the pointwise universal closure described above as its
signature:

```
(hG : G.IsAcyclic) (π : Walk G v w) {k : ℕ}
  (hk : π.IsNonColliderAt k) → π.IsBlockableNonColliderAt k
```

The proof goes via a private helper
`not_isUnblockableNonColliderAt_of_isAcyclic` that derives `False`
from any `IsUnblockableNonColliderAt` witness: every
`IsUnblockableJoint` produces a directed walk into the joint vertex
(via the SCC ⊆ Anc inclusion supplied by the joint condition)
which, combined with the strict outgoing edge underlying the
unblockable step, closes a directed cycle through the joint —
contradicting `IsAcyclic`. The TeX proof's three patterns (left
chain, right chain, fork) line up with the head-step case analysis
in the helper.

## Downstream usage

* **def_3_17** ($\sigma$-blocked walks, `graphs.tex` lines
  1326 -- 1348) -- the LN's $C$-$\sigma$-open / $\sigma$-blocked
  conditions reference *blockable* non-colliders specifically; in
  the acyclic case this claim collapses "blockable non-collider
  in $C$" to "any non-collider in $C$".
* **claim_3_21** (`graphs.tex` lines 1344 -- 1346) --
  "unblockable non-colliders are always $C$-$\sigma$-open". The
  dual fact to claim_3_20: claim_3_20 says acyclicity rules out
  *unblockable* non-colliders altogether; claim_3_21 says (in any
  graph, acyclic or not) unblockable non-colliders are $\sigma$-open.
* **claim_3_24** ($\sigma$-separation equivalences) -- uses
  claim_3_20 to swap "blockable non-collider" for "non-collider"
  in the acyclic case.
* **claim_3_26** (`graphs.tex` lines 1581 -- 1597) -- the
  *non-remark* twin of this claim in the $i\sigma$-separation
  section: "If a CDMG $G$ is acyclic then all non-colliders are
  blockable. So, the partial condition for $i\sigma$-separation
  ``a blockable non-collider in $C$'' can be simplified to
  ``(any) non-collider in $C$''." The claim_3_26 row will consume
  this theorem directly.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable` --
  source of `IsNonColliderAt`, `IsUnblockableNonColliderAt`,
  `IsBlockableNonColliderAt`. The theorem here sits one floor
  above and stays in `namespace Walk` so that callers reach for
  it via dot-projection on a walk.
* `Chapter3_GraphTheory.Section3_1.AcyclicIffTopologicalOrder` --
  the precedent "one-row claim file": a single `theorem`,
  module-level docstring summarising the claim and its downstream
  consumers, LN block reproduced verbatim in a `/- ... -/` quote
  above the declaration, and a design-choice block.
* `Chapter3_GraphTheory.Section3_1.Acyclicity` -- source of
  `CDMG.IsAcyclic`, the precondition.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

-- claim_3_20
-- title: AcyclicNonCollidersBlockable -- in an acyclic CDMG, every
-- non-collider position on every walk is a blockable non-collider
--
-- Pointwise reading of the LN's "all non-colliders are blockable":
-- for every walk `π : Walk G v w` in `G` and every position
-- `k : ℕ` on `π`, if `k` is a non-collider on `π` then `k` is a
-- blockable non-collider on `π`, provided `G.IsAcyclic`.
--
-- The two ingredients on the right-hand side
-- (`IsNonColliderAt`, `IsBlockableNonColliderAt`) come from
-- def_3_15 / def_3_16 (`Section3_3/CollidersAndNon.lean` and
-- `Section3_3/BlockableAndUnblockable.lean`); the precondition
-- `IsAcyclic` comes from def_3_6 (`Section3_1/Acyclicity.lean`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (claim_3_20,
lines 1256 -- 1261):

\begin{claimmark}
\begin{Rem}
If $G$ is acyclic then all non-colliders are blockable.
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Pointwise universal closure, walk explicit and position
--   implicit.** The LN's "all non-colliders are blockable" reads
--   naturally under the def_3_16 paradigm (which talks about a
--   single walk $\pi$ and a single position $k$) as: for every
--   walk $\pi$ in $G$ and every position $k$ on $\pi$,
--   `IsNonColliderAt k → IsBlockableNonColliderAt k`. We quantify
--   `π` explicitly (callers pass it positionally) and `k`
--   implicitly (inferable from `hk`); the `hk` hypothesis is the
--   LN's "non-collider" antecedent and is not dropped, since the
--   conclusion is genuinely conditional on `k` being a non-collider
--   position.
--
-- * **Alternative shape considered and rejected: drop the `hk`
--   antecedent, conclude `¬ π.IsUnblockableNonColliderAt k`
--   directly.** An equivalent-content version of the same claim
--   would be `(hG : G.IsAcyclic) (π : Walk G v w) {k : ℕ} :
--   ¬ π.IsUnblockableNonColliderAt k`. The two shapes are
--   inter-derivable via
--   `IsNonColliderAt_of_isUnblockableNonColliderAt` in
--   `BlockableAndUnblockable.lean` (its contrapositive supplies
--   `¬ IsUnblockableNonColliderAt` at every non-non-collider
--   position for free, so dropping `hk` does not actually weaken
--   the statement). We reject the negated-unblockable shape for
--   two reasons. **(i) LN-lexical fidelity.** The LN states the
--   conclusion as "blockable" -- the *positive* predicate
--   `IsBlockableNonColliderAt` -- not as "not unblockable" (the
--   negated `IsUnblockableNonColliderAt`); mirroring the LN's
--   vocabulary keeps the Lean conclusion lined up with the prose
--   word-for-word. **(ii) Consumer ergonomics.** The downstream
--   rows that consume this implication -- claim_3_24 and
--   claim_3_26 most directly -- apply it *under def_3_17's
--   universal quantifier over blockable non-collider positions
--   in $C$*, to substitute "blockable non-collider in $C$" by
--   "any non-collider in $C$" once acyclicity is known. Those
--   call sites want a conclusion that already says
--   `IsBlockableNonColliderAt`, so they can dispatch it under the
--   def_3_17 binder directly; the negated-unblockable shape would
--   force an extra `IsBlockableNonColliderAt.intro` (i.e.
--   explicit pairing with the local `hk` via the defining
--   equation in `BlockableAndUnblockable.lean`) at every call
--   site.
--
-- * **`namespace Walk` placement.** The theorem reads as a
--   property of a walk's position predicates, mirroring
--   `isBlockableNonColliderAt_zero` and `isBlockableNonColliderAt_length`
--   in `BlockableAndUnblockable.lean`. Callers reach for it via
--   dot-projection `π.isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic
--   hG hk`.
--
-- * **Name `isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`.**
--   Standard Mathlib `_of_..._of_...` convention: conclusion first,
--   then each hypothesis in argument order (`hG` for acyclicity,
--   `hk` for non-collider). Reads as "blockable non-collider at
--   $k$, from non-collider at $k$, from acyclicity". The walk `π`
--   and position `k` are bound but unnamed in the theorem name,
--   matching the convention used for `isBlockableNonColliderAt_zero`
--   (the position `0` is in the name; the walk is not).
--
-- * **One-way implication only, mirroring the LN's prose.** The LN
--   claims acyclic ⇒ all non-colliders blockable, and that is the
--   direction we formalise. The converse also holds -- any
--   directed cycle $v_0 \tuh v_1 \tuh \cdots \tuh v_n = v_0$ in
--   $G$ yields, on the length-2 walk $\pi = (v_0 \tuh v_1 \tuh
--   v_2)$ (taking $v_2$ around the cycle back to $v_1$), an
--   unblockable non-collider at position $1$: the joint is a
--   right-chain (`forward, forward`), so the collider conjunct of
--   `IsUnblockableJoint` holds; the backward-SCC clause is
--   vacuous; and the forward-SCC clause $v_2 \in \Sc^G(v_1)$
--   holds because the cycle witnesses $v_1 \to v_2$ and $v_2 \to
--   \cdots \to v_1$. So `∃ π k, π.IsUnblockableNonColliderAt k`
--   contradicts blockability and witnesses `¬ G.IsAcyclic`. We do
--   *not* bundle the iff here because no downstream row needs the
--   converse (claim_3_26 and the other consumers only use the
--   forward direction); a future row can introduce the converse
--   as a separate lemma if a proof requires it.
--
-- * **Mathlib re-use: convention, not content.** The theorem's
--   content -- `CDMG.IsAcyclic`, `IsNonColliderAt`,
--   `IsBlockableNonColliderAt` -- is entirely project-local
--   (defined in `Section3_1/Acyclicity.lean`,
--   `Section3_3/CollidersAndNon.lean`, and
--   `Section3_3/BlockableAndUnblockable.lean`); mathlib has no
--   CDMG / walk-positional / collider-blockability infrastructure
--   to reuse, since these predicates are paradigm-specific to the
--   LN's conditional-directed-mixed-graph setup. What we *do*
--   borrow from mathlib is *naming and placement convention*: the
--   `_of_..._of_...` theorem name (conclusion first, then each
--   hypothesis in argument order) and the `namespace Walk`
--   dot-projection idiom both mirror mathlib's `SimpleGraph.Walk`
--   namespace style. This keeps the theorem feeling at home with
--   mathlib API even though its content is wholly project-local.
--
-- * **Downstream consequences -- see the module-level
--   "Downstream usage" block.** The module docstring above
--   already enumerates the four consumers (def_3_17, claim_3_21,
--   claim_3_24, claim_3_26) and what each does with this
--   theorem; we keep the design rationale and the consumer list
--   *co-located* via this cross-reference rather than duplicating
--   the consumer list here. The takeaway for the design choice
--   is that the chosen shape --
--   `IsNonColliderAt k → IsBlockableNonColliderAt k`, walk `π`
--   and position `k` universally bound -- is exactly the form in
--   which those consumers will dispatch the implication: they sit
--   inside def_3_17's universal "for every blockable non-collider
--   position $k$ in $C$ ..." quantifier and apply this theorem
--   modus-ponens-style to turn the binder's
--   `IsBlockableNonColliderAt` hypothesis into a plain
--   `IsNonColliderAt` one.
--
-- * **Constraint / known limitation: per-walk, not per-vertex.**
--   The theorem fixes a single walk `π` and a single position
--   `k` on it; it does *not* directly assert "for every walk
--   that visits `v` as a non-collider, the visit is blockable"
--   (a universal over walks containing `v` as a vertex). The two
--   statements are inter-derivable -- every downstream consumer
--   quantifies over walks anyway, so the per-walk shape composes
--   cleanly -- but a reader expecting a vertex-indexed flavor
--   should know we keep `π` on the *outside* of the implication.
--   This mirrors def_3_15 / def_3_16's own paradigm (predicates
--   *on* a walk + position, not on a vertex), so the choice is
--   forced by paradigm consistency rather than a fresh design
--   call here.

/-- Helper for `not_isUnblockableNonColliderAt_of_isAcyclic`: a
directed edge `(b, x) ∈ G.E` together with `x ∈ Sc^G(b)` closes a
directed cycle through `b`, contradicting `G.IsAcyclic`. This is the
common core of claim_3_20's three TeX patterns (left chain / right
chain / fork): each pattern instantiates `(b, x)` with the underlying
strict outgoing edge from the joint and `x ∈ Sc^G(b)` with the LN's
"$v_{k\pm 1} \in \Sc^G(v_k)$" SCC clause of `IsUnblockableJoint`. -/
private lemma absurd_isAcyclic_of_directedEdge_Sc
    (hG : G.IsAcyclic) {b x : α}
    (h_e : (b, x) ∈ G.E) (h_x : x ∈ G.Sc b) : False := by
  obtain ⟨⟨_, π, π_dir⟩, _⟩ := h_x
  exact hG _ (CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset h_e)).1)
    ⟨Walk.cons (WalkStep.forward h_e) π,
      by simpa using π_dir,
      by simp [Walk.length_cons]⟩

/-- Helper for `isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`:
under acyclicity, no walk has an *unblockable* non-collider at any
position. This is the heart of claim_3_20: the TeX proof's three
patterns (left chain, right chain, fork) collapse into the
`cons s (cons s' _), 1` case of the recursion below, where each
`IsUnblockableJoint` SCC clause produces a directed walk back to the
joint vertex; prepending the strict outgoing edge closes a directed
cycle through the joint, contradicting `IsAcyclic`. -/
private lemma not_isUnblockableNonColliderAt_of_isAcyclic
    (hG : G.IsAcyclic) :
    ∀ {v w : α} (π : Walk G v w) (k : ℕ),
      ¬ π.IsUnblockableNonColliderAt k
  | _, _, .nil _, _, h => h.elim
  | _, _, .cons _ (.nil _), _, h => h.elim
  | _, _, .cons _ (.cons _ _), 0, h => h.elim
  | _, _, .cons s (.cons s' _), 1, hUnblock => by
      -- `IsUnblockableNonColliderAt` at position 1 of `cons s (cons s' _)`
      -- unfolds (via the `isUnblockableNonColliderAt_cons_cons_one`
      -- `Iff.rfl` simp lemma) to `s.IsUnblockableJoint s'`, which is
      -- `(¬ collider) ∧ (s.IsBackward → a ∈ Sc b) ∧ (s'.IsForward → c ∈ Sc b)`.
      obtain ⟨hNotColl, hBack, hFwd⟩ := hUnblock
      -- Case-split on the head step `s`, then on `s'` where needed.
      -- The four collider configurations of `(s, s')` are discharged via
      -- `hNotColl`; the three non-collider strict-arrow configurations
      -- (right chain via `hFwd`, left chain via `hBack`, fork via either)
      -- dispatch to `absurd_isAcyclic_of_directedEdge_Sc`.
      cases s with
      | forward _ =>
        -- s.HasArrowheadAtTarget = True ⇒ non-collider forces s' = forward.
        cases s' with
        | forward h_e =>
          -- Right-chain pattern: cycle via the strict outgoing arrow `s'`.
          exact absurd_isAcyclic_of_directedEdge_Sc hG h_e (hFwd (by simp))
        | backward _ => exact hNotColl ⟨by simp, by simp⟩
        | bidir _ => exact hNotColl ⟨by simp, by simp⟩
      | backward h_e =>
        -- Left-chain / fork pattern: cycle via the strict outgoing arrow `s`.
        exact absurd_isAcyclic_of_directedEdge_Sc hG h_e (hBack (by simp))
      | bidir _ =>
        -- Same as the `forward _` case: s.HasArrowheadAtTarget = True ⇒ s' = forward.
        cases s' with
        | forward h_e =>
          -- Right-chain pattern (bidir variant on left): cycle via `s'`.
          exact absurd_isAcyclic_of_directedEdge_Sc hG h_e (hFwd (by simp))
        | backward _ => exact hNotColl ⟨by simp, by simp⟩
        | bidir _ => exact hNotColl ⟨by simp, by simp⟩
  | _, _, .cons _ (.cons s' p), k + 2, hUnblock => by
      -- Recurse: at position `k + 2` of `cons _ (cons s' p)`, the
      -- definition of `IsUnblockableNonColliderAt` is by `Iff.rfl`
      -- equal to its value at position `k + 1` of the tail `cons s' p`.
      exact not_isUnblockableNonColliderAt_of_isAcyclic hG
        (.cons s' p) (k + 1) hUnblock

/-- claim_3_20 (`AcyclicNonCollidersBlockable`): if `G` is acyclic
then every non-collider position on every walk in `G` is a
*blockable* non-collider. Mirrors
`lecture-notes/lecture_notes/graphs.tex` claim_3_20 (the
`\begin{claimmark}\begin{Rem}...\end{Rem}\end{claimmark}` block at
lines 1256 -- 1261) verbatim, with the LN's "all non-colliders"
unrolled under the def_3_16 paradigm to a universal quantifier over
walks `π` and positions `k`, and the non-collider antecedent kept as
the hypothesis `hk : π.IsNonColliderAt k`. -/
theorem isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic
    (hG : G.IsAcyclic) {v w : α} (π : Walk G v w) {k : ℕ}
    (hk : π.IsNonColliderAt k) :
    π.IsBlockableNonColliderAt k :=
  ⟨hk, not_isUnblockableNonColliderAt_of_isAcyclic hG π k⟩

end Walk

end Causality
