import Chapter3_GraphTheory.Section3_2.HardInterventionOn

-- TeX statement: tex/claim_3_4_statement_HardInterventionsCommute.tex
-- TeX proof: tex/claim_3_4_proof_HardInterventionsCommute.tex

/-!
# Hard interventions commute (claim_3_4)

This file formalises the lecture notes' lemma "hard interventions
commute" -- `lecture-notes/lecture_notes/graphs.tex` Lem at lines
314 -- 325. The LN states the chained equality

  `(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`

under the precondition `W₁, W₂ ⊆ J ∪ V`. In our Lean encoding the
precondition is unnecessary: `G.hardInterventionOn W` is well-defined
for every `W : Set α`, and the equality of CDMGs holds for arbitrary
`W₁, W₂` (see the design notes in `HardInterventionOn.lean` lines
88 -- 215, which cite *this* row as the load-bearing iteration test
that justified dropping the precondition).

The LN bundles the chained equality into one statement, but its own
proof structure already factors it the same way we do: at
`graphs.tex` line 328 -- 329 the LN writes "We show
`(G_{do(W₁)})_{do(W₂)} = G_{do(W₁ ∪ W₂)}`; the equality
`(G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}` then follows by symmetry."
Our two-theorem split mirrors this exactly, and also mirrors
`AcyclicUnderIntervention.lean`'s split-`\Rem` pattern for claim_3_3:

* `hardInterventionOn_hardInterventionOn` -- the **fusion** lemma,
  the fundamental fact:
  `(G.hardInterventionOn W₁).hardInterventionOn W₂ = G.hardInterventionOn (W₁ ∪ W₂)`.
  Established by component-wise set-theoretic identities on the
  four CDMG fields `J / V / E / L` (see the LN proof in lines
  326 -- 356; the Lean proof is Manager B's job).

* `hardInterventionOn_comm` -- the **commute** corollary:
  `(G.hardInterventionOn W₁).hardInterventionOn W₂ =
   (G.hardInterventionOn W₂).hardInterventionOn W₁`. Once the
  fusion lemma is in hand, this is a one-liner: rewrite both sides
  via the fusion lemma, then `Set.union_comm`.

## Where this gets used downstream

* **claim_3_8 / claim_3_11** (`graphs.tex`) -- disjoint hard
  interventions. Iteration `(G_{do(W₁)})_{do(W₂)}` reduces to a
  single hard intervention `G_{do(W₁ ∪ W₂)}` via the fusion
  lemma; the commute form is occasionally needed when the
  downstream argument has fixed which `W_i` comes "first".
* **claim_3_14** (`graphs.tex` Lem at line 831, "Adding
  intervention nodes commutes with disjoint hard interventions")
  -- the proof iterates `\doit(I_{W_1})` and `\doit(W_2)` and
  collapses the chain via this fusion lemma (graph-side); without
  fusion the inner / outer intervention bookkeeping has nowhere
  to land.
* **Chapter 5 (do-calculus)** -- iteration of do-operators inside
  identification proofs collapses via the fusion lemma; the LN
  freely rewrites `do(W₁); do(W₂) = do(W₁ ∪ W₂)` as a one-step
  algebraic move.
* **Chapters 8 -- 10 (iSCMs)** -- intervention iteration on the
  graph side of the iSCM unique-solution / Markov-property theory
  collapses chains of hard interventions to a single hard
  intervention via this fusion lemma. Specific call sites:
  `scms.tex` Prp at line 1493 (`prp:interventions_commute`, iSCM
  intervention commutativity, whose graph-side specialisation is
  exactly this lemma) and `scms3.tex` Prp at line 157
  (`prp:compatibility_graph`, hard-intervention / graph-functor
  compatibility, whose iteration argument reduces nested
  interventions via fusion). Without it, every iterated
  intervention statement would have to carry a nested
  `hardInterventionOn` expression that the Lean elaborator has no
  general definitional unfolding for.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-- Local CDMG-extensionality helper for this row: two CDMGs are equal as
soon as their four data fields `J / V / E / L` agree. The six prop
fields (`disjoint_JV`, `E_subset`, `L_subset`, `L_irrefl`, `L_symm`,
`disjoint_EL`) are propositions, hence proof-irrelevant under Lean 4's
definitional rule, so they close by `rfl` once the data fields are
pinned down. Kept `private` because it is a one-shot shortcut used only
by `hardInterventionOn_hardInterventionOn` below -- `CDMG` is
intentionally not `@[ext]`-tagged at its definition site
(`Section3_1/CDMG.lean`), and we do not want a chapter-wide ext lemma
leaking out from this row. The component-wise discipline of the LN
proof (`tex/claim_3_4_proof_HardInterventionsCommute.tex`) is exactly
what this helper packages. -/
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

-- claim_3_4 (part 1/2)
-- title: HardInterventionsCommute -- fusion lemma
--
-- Iterating two hard interventions collapses to a single hard
-- intervention on the union: `(G_{do(W₁)})_{do(W₂)} = G_{do(W₁ ∪ W₂)}`.
-- This is the fundamental fact behind the LN's chained equality; the
-- commute form (part 2/2 below) is an immediate corollary by
-- `Set.union_comm`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 314 -- 325)
-- the displayed equation is reflowed (linewrap only; math-mode
-- whitespace collapses, so this is verbatim under \LaTeX semantics):

\begin{claimmark}
\begin{Lem}[Hard interventions commute]\label{hard-interventions-commute}
    Let $G:=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins J \cup V$ two  subsets of nodes from $G$.
      Then we have:
      \[ \lp G_{\doit(W_1)} \rp_{\doit(W_2)} = \lp G_{\doit(W_2)} \rp_{\doit(W_1)}
         =  G_{\doit(W_1 \cup W_2)}. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_4 part 1/2 (fusion lemma): iterating two hard
interventions equals a single hard intervention on the union,
`(G.hardInterventionOn W₁).hardInterventionOn W₂
   = G.hardInterventionOn (W₁ ∪ W₂)`. Mirrors the first half of
the chained equality in the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 317.

## Design choice

* **No `W₁, W₂ ⊆ G.J ∪ G.V` precondition.** The LN states
  `W₁, W₂ ⊆ J ∪ V`, but the CDMG `G.hardInterventionOn W` is
  well-defined for every `W : Set α` (see the design note at
  `Section3_2/HardInterventionOn.lean` lines 88 -- 215, which
  cites *this very claim* as the load-bearing iteration test
  that justified dropping the precondition). The fusion equality
  holds component-wise as a set-theoretic identity on
  `J / V / E / L` for arbitrary `W₁, W₂` -- the LN's
  precondition is informal scaffolding ("`W ⊆ G`" so that
  `do(W)` is mathematically meaningful in prose), not a
  load-bearing hypothesis in the proof.

  This matters: the *outer* call in
  `(G.hardInterventionOn W₁).hardInterventionOn W₂` would
  otherwise need a hypothesis
  `W₂ ⊆ (G.hardInterventionOn W₁).J ∪ (G.hardInterventionOn W₁).V`
  =  `(G.J ∪ W₁) ∪ (G.V \ W₁)`, which is not the same set as
  `G.J ∪ G.V` (`W₁` got promoted into the inputs). The LN's
  proof prose tacitly assumes `W₂ ⊆ J ∪ V` -- the *base* graph's
  node set -- without re-justifying it for the inner intervention,
  which is exactly the informal usage our no-precondition encoding
  captures faithfully. (See `HardInterventionOn.lean` lines
  102 -- 110 for the explicit citation.)

* **Splitting the LN's chained equality into two theorems.** The
  LN bundles `(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁ )} =
  G_{do(W₁ ∪ W₂)}` into one displayed equation, but its own proof
  (`graphs.tex` lines 326 -- 356) already does the split: line
  328 -- 329 says "We show
  `(G_{do(W₁)})_{do(W₂)} = G_{do(W₁ ∪ W₂)}`; the equality
  `(G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}` then follows by
  symmetry." We split this into a *fusion* lemma (this
  declaration) and a *commute* corollary (`hardInterventionOn_comm`
  below), mirroring both the LN's proof structure and
  claim_3_3's split-`\Rem` pattern in
  `AcyclicUnderIntervention.lean`. The fusion form is the
  fundamental fact -- it is what every downstream consumer
  actually rewrites with. claim_3_8 / claim_3_11 (disjoint hard
  interventions), claim_3_14 (`graphs.tex` line 831, adding
  intervention nodes commutes with disjoint hard interventions),
  the do-calculus iteration arguments of chapter 5, and the iSCM
  intervention iteration of chapters 8 -- 10 (`scms.tex` line
  1493, `scms3.tex` line 157) all need to collapse a chained hard
  intervention to a single one, *not* to swap the order of two
  hard interventions. The commute form is the rare-use corollary;
  given the fusion lemma it is a one-liner (`Set.union_comm`), so
  we expose both shapes explicitly.

* **Naming `hardInterventionOn_hardInterventionOn`.** Follows
  Mathlib's `image_image` / `filter_filter` /
  `comap_comap` convention: when applying a construction to its
  own output collapses (or "fuses") into a single application on
  a combined argument, the convention is to name the lemma by
  doubling the construction name. The RHS combines the two
  arguments by `∪`, exactly as `image_image` combines by `∘`.
  Picking this name over alternatives (`hardInterventionOn_union`
  on the wrong side, `hardInterventionOn_fuse`, ...) makes the
  rewrite direction unambiguous and lines up with simp's
  preference for collapsing nested applications.

* **`W₁, W₂` explicit, `G` implicit.** The lemma is intended to
  fire as a `rw` / `simp`-style rewrite rule keyed on the **target
  sets** `W₁, W₂` -- which are precisely the part of the LHS that
  the consumer wants to control at the call site. Both are
  therefore explicit. Consumers (claim_3_8 / claim_3_11, claim_3_14,
  do-calculus proofs in chapter 5, iSCM proofs in chapters 8 -- 10)
  typically have specific `W₁, W₂ : Set α` in mind when they invoke
  the fusion lemma. Forcing them to be passed (a) makes call sites
  read as plainly as the LN prose `(G_{do(W₁)})_{do(W₂)}`, and
  (b) sidesteps the unification fragility of a fully-implicit
  rewrite: the two `W`-arguments are *not* unifiable from a single
  `(_).hardInterventionOn _` subterm without pinning down which
  outer / inner role they play. `G`, by contrast, is implicit
  because the LHS `(G.hardInterventionOn W₁).hardInterventionOn W₂`
  pins it down uniquely -- this is the standard Mathlib pattern for
  binary fusion / commute / associativity rewrites.

* **Statement-only at this stage; proof is one `sorry`.** The
  body is exactly one `sorry`. The TeX proof + Lean proof are
  Manager B's job (the LN's own proof, lines 326 -- 356, gives
  the four component-wise set-theoretic identities; the Lean
  proof will discharge each via `Set.ext` plus standard
  set-difference / union manipulations, finishing with a
  `congr`-style argument or by explicitly invoking a CDMG
  ext-lemma). -/
theorem hardInterventionOn_hardInterventionOn
    {G : CDMG α} (W₁ W₂ : Set α) :
    (G.hardInterventionOn W₁).hardInterventionOn W₂
      = G.hardInterventionOn (W₁ ∪ W₂) := by
  -- Mirrors `tex/claim_3_4_proof_HardInterventionsCommute.tex`. The TeX
  -- proof verifies the chained equality componentwise on the CDMG
  -- 4-tuple `(J, V, E, L)`; we do the same via the local `mk_eq_of_data`
  -- helper (which packages the proof-irrelevance argument for the six
  -- prop fields). Each of the four data-field goals is a standard set
  -- identity from the LN's four checks.
  refine mk_eq_of_data ?_ ?_ ?_ ?_
  · -- J: `(G.J ∪ W₁) ∪ W₂ = G.J ∪ (W₁ ∪ W₂)` (associativity of `∪`).
    exact Set.union_assoc _ _ _
  · -- V: `(G.V \ W₁) \ W₂ = G.V \ (W₁ ∪ W₂)` (`Set.diff_diff`).
    exact Set.diff_diff
  · -- E: membership-wise via `mem_hardInterventionOn_E`; `tauto` closes
    -- the resulting boolean tautology after unfolding `Set.mem_union`.
    ext p
    simp only [mem_hardInterventionOn_E, Set.mem_union]
    tauto
  · -- L: same shape as E, with the both-endpoints exclusion of
    -- `mem_hardInterventionOn_L`.
    ext p
    simp only [mem_hardInterventionOn_L, Set.mem_union]
    tauto

-- claim_3_4 (part 2/2)
-- title: HardInterventionsCommute -- commute corollary
--
-- Hard interventions commute: `(G_{do(W₁)})_{do(W₂)} =
-- (G_{do(W₂)})_{do(W₁)}`. This is the LN's headline statement; in our
-- Lean architecture it is a one-line corollary of the fusion lemma
-- (part 1/2) combined with `Set.union_comm`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 314 -- 325)
-- the displayed equation is reflowed (linewrap only; math-mode
-- whitespace collapses, so this is verbatim under \LaTeX semantics):

\begin{claimmark}
\begin{Lem}[Hard interventions commute]\label{hard-interventions-commute}
    Let $G:=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins J \cup V$ two  subsets of nodes from $G$.
      Then we have:
      \[ \lp G_{\doit(W_1)} \rp_{\doit(W_2)} = \lp G_{\doit(W_2)} \rp_{\doit(W_1)}
         =  G_{\doit(W_1 \cup W_2)}. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_4 part 2/2 (commute corollary): the order of two hard
interventions does not matter,
`(G.hardInterventionOn W₁).hardInterventionOn W₂
   = (G.hardInterventionOn W₂).hardInterventionOn W₁`. Mirrors the
second half (`= (G_{do(W₂)})_{do(W₁)}`) of the chained equality in
the `\Lem` at `lecture-notes/lecture_notes/graphs.tex` line 317.

## Design choice

* **No `W₁, W₂ ⊆ G.J ∪ G.V` precondition** -- same reasoning as
  `hardInterventionOn_hardInterventionOn` above (the
  no-precondition design of `G.hardInterventionOn` is precisely
  what makes both this and the fusion lemma hold for arbitrary
  `W₁, W₂`; see `Section3_2/HardInterventionOn.lean` lines
  88 -- 215).

* **Why split this off from the fusion lemma rather than expose
  only the chained equality?** Both shapes occur naturally in
  practice. Downstream consumers that need to *collapse* a
  chained intervention to a single one (claim_3_8 / claim_3_11
  disjoint hard interventions, claim_3_14 / `graphs.tex` line
  831, chapter 5 do-calculus iteration, chapter 8 -- 10 iSCM
  intervention iteration via `scms.tex` line 1493 /
  `scms3.tex` line 157) reach for the fusion lemma. Consumers
  that need to *reorder* two interventions without collapsing
  them (e.g. matching the order of some other operation that is
  order-sensitive) reach for this commute form. A single
  chained-equality theorem would force one of the two patterns
  to project, an extra step every time. The split also mirrors
  the LN's *own* proof structure (`graphs.tex` lines 326 -- 356,
  which proves the fusion direction in full and then derives the
  swap by symmetry), and matches
  `AcyclicUnderIntervention.lean`'s split-`\Rem` precedent for
  this subsection.

* **One-line proof from the fusion lemma.** Once
  `hardInterventionOn_hardInterventionOn` is proven, this is a
  rewrite: both sides equal `G.hardInterventionOn (W₁ ∪ W₂)` and
  `G.hardInterventionOn (W₂ ∪ W₁)` respectively, and
  `Set.union_comm` identifies the union arguments. The Manager B
  Lean proof will be essentially
  `rw [hardInterventionOn_hardInterventionOn,
       hardInterventionOn_hardInterventionOn, Set.union_comm]`.

* **Naming `hardInterventionOn_comm`.** Follows the standard
  Mathlib `_comm` suffix for commutativity-of-an-operator-style
  lemmas (`add_comm`, `mul_comm`, `union_comm`, `Function.comm`,
  ...). Pairs naturally with the `_hardInterventionOn` fusion
  name above; a reader scanning the file will see "fusion lemma
  + commute corollary" rather than two disconnected facts.

* **`W₁, W₂` explicit, `G` implicit** -- same reasoning as the
  fusion lemma. The lemma fires as a rewrite rule keyed on the
  target sets `W₁, W₂` (the part the consumer needs to spell at
  the call site); `G` is recovered from the LHS of the conclusion.
  Standard Mathlib convention for binary commute rewrites
  (`mul_comm`, `add_comm`, `Set.union_comm`).

* **Statement-only at this stage; proof is one `sorry`.** Body
  is exactly one `sorry`; the proof is deferred to Manager B
  (one-line rewrite via the fusion lemma plus `Set.union_comm`,
  as noted above). -/
theorem hardInterventionOn_comm
    {G : CDMG α} (W₁ W₂ : Set α) :
    (G.hardInterventionOn W₁).hardInterventionOn W₂
      = (G.hardInterventionOn W₂).hardInterventionOn W₁ := by
  -- Mirrors the symmetry sentence at the close of
  -- `tex/claim_3_4_proof_HardInterventionsCommute.tex`. With the fusion
  -- lemma in hand, both sides collapse to a single hard intervention on
  -- the union (`G.hardInterventionOn (W₁ ∪ W₂)` and
  -- `G.hardInterventionOn (W₂ ∪ W₁)` respectively); `Set.union_comm`
  -- identifies the arguments.
  rw [hardInterventionOn_hardInterventionOn,
      hardInterventionOn_hardInterventionOn, Set.union_comm]

end CDMG

end Causality
