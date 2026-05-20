import Chapter3_GraphTheory.Section3_1.Bifurcation
import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_2.HardInterventionOn

-- TeX statement: tex/claim_3_5_statement_BifurcationAlternative.tex
-- TeX proof: tex/claim_3_5_proof_BifurcationAlternative.tex

/-!
# Bifurcation source ↔ ancestral conditions in singleton hard interventions (claim_3_5)

This file formalises *proposition 3.5* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex` lines
358 -- 371, label `prp:bifurcations_alternative`): for vertices
`v`, `w`, `c` of a CDMG `G`, there exists a bifurcation between
`v` and `w` in `G` with source `c` if and only if `v ≠ w` and both
ancestor-set conditions
`c ∈ Anc^{G_{do(w)}}(v) ∖ {v}` and `c ∈ Anc^{G_{do(v)}}(w) ∖ {w}`
hold.

The Lean LHS carries an extra `c ≠ w` conjunct beyond the literal
LN reading; see the design-choice note above the theorem (and the
manager decision recorded in
`Section3_2/workspace_claim_3_5.md`) for the rationale. -/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

-- claim_3_5
-- title: BifurcationAlternative
--
-- LN claim 3.5: there is a bifurcation between `v` and `w` with
-- source `c` iff `v ≠ w` and `c` is a non-trivial ancestor of `v`
-- in the single-vertex hard intervention `G_{do(w)}` and of `w` in
-- `G_{do(v)}`. The LN's prose is at `graphs.tex` 358 -- 371.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Prp 360 -- 364)
-- the iff sentence is reflowed (linewrap only; text-mode whitespace
-- collapses, so this is verbatim under \LaTeX semantics):

\begin{claimmark}
\begin{Prp}\label{prp:bifurcations_alternative}
  Let $G = \lt J, V, E, L \rt$ be a CDMG. For $v, w, c \in V \cup J$:
  there exists a bifurcation between $v$ and $w$ in $G$ with source $c$
  if and only if $v \ne w$ and $c \in \Anc^{G_{\doit(w)}}(v) \sm \{v\}$
  and $c \in \Anc^{G_{\doit(v)}}(w) \sm \{w\}$.
\end{Prp}
\end{claimmark}
-/
/-- LN claim 3.5 (`prp:bifurcations_alternative`): for vertices
`v`, `w`, `c` of a CDMG `G`, there exists a bifurcation between
`v` and `w` in `G` with source `c` iff `v ≠ w` and both
ancestor-set conditions
`c ∈ Anc^{G_{do(w)}}(v) ∖ {v}` and `c ∈ Anc^{G_{do(v)}}(w) ∖ {w}`
hold. The LHS quantifies existentially over a walk
`π : Walk G v w` and a witness `hb : π.IsBifurcation`, with the
source extracted via `π.bifurcationSource hb = some c`; an extra
`c ≠ w` conjunct on the LHS captures the LN's *implicit*
"non-trivial directed path from `c` to `w`" requirement at the
claim level (see `## Design choice` below).

## Design choice

* **The `c ≠ w` LHS conjunct is the load-bearing decision for
  this row.** Without it, the iff is *literally false*. The
  current `Walk.bifurcationSource`
  (`Section3_1/Bifurcation.lean` lines 362 -- 367) returns
  `some bw.m'` whenever the chosen witness's hinge is
  `.backward _`, regardless of whether the witness's `rightArm`
  is the trivial `.nil` walk. Consequently, an all-backward walk
  `v ⊣ ⋯ ⊣ w` (length ≥ 1) is an `IsBifurcation` whose source is
  `w` (the witness picks the last backward step as the hinge,
  `rightArm = .nil w`, so `bw.m' = w`): the LHS with `c = w`
  holds, but the RHS forbids `c = w` via the `\ {w}` exclusion.
  Two repair routes were considered.
  - **Path 1** -- tighten `bifurcationSource` itself to require
    a non-trivial `rightArm` in addition to the backward hinge.
    **Rejected.** That extractor is owned by **def_3_4**
    (`Section3_1/Bifurcation.lean`, a previously-solved row in
    a different subsection); editing it from a Section_3_2 row
    breaks the manager-side scope rule, and the heavy-redesign
    machinery would have to be invoked to retract def_3_4 and
    its dependents. Disproportionate surgery to make one iff
    hold.
  - **Path 2** (chosen) -- add `c ≠ w` to the LHS so it mirrors
    the RHS's `\ {w}` exclusion clause-for-clause. Local,
    surgical, LN-faithful: the LN's own proof prose at
    `graphs.tex` lines 366 -- 371 calls the right half a
    *"non-trivial directed path from `c` to `w`"*, and `c ≠ w`
    is exactly the Lean transcription of "non-trivial". The LN's
    def_3_4 item 6 leaves this implicit -- claim_3_5 is where
    the LN first relies on it -- so encoding it on the claim's
    LHS rather than retroactively tightening def_3_4 stays
    closer to the LN's own factoring.

  See the *Manager decision (2026-05-20)* section at the top of
  `Section3_2/workspace_claim_3_5.md` for the full decision
  record (counterexample, scope-rule discussion, forward-tax
  estimate).

* **No symmetric `c ≠ v` conjunct on the LHS -- deliberate
  asymmetry.** `IsBifurcation` already enforces
  `v ∉ π.support.tail` (`Section3_1/Bifurcation.lean` line 311).
  For any witness `bw` of `π : Walk G v w`, the source vertex
  `c = bw.m'` sits at position `1 + bw.leftArm.length ≥ 1` of
  `π.support`, i.e. inside `π.support.tail`; combined with
  `v ∉ π.support.tail` this forces `c ≠ v` automatically. The
  asymmetry between the two endpoints mirrors how
  `bifurcationSource` *extracts* the source -- it names `m'`,
  the right side of the hinge -- so it is the *right arm* whose
  non-triviality has to be enforced separately on the LHS. The
  left arm's non-triviality is irrelevant to the source
  extractor: even a degenerate `k = 1` (empty `leftArm`) witness
  does not threaten the iff.

* **Two-argument `Anc` and singleton hard interventions.** `Anc`
  is the two-argument form `Anc : CDMG α → α → Set α`
  (`Section3_1/FamilyReachability.lean` lines 115 -- 125), not a
  one-argument predicate bundled over an implicit subgraph. The
  LN's `\Anc^{G_{\doit(w)}}(v)` therefore transcribes as
  `Anc (G.hardInterventionOn ({w} : Set α)) v`: the intervened
  graph is supplied as the first positional argument, and the
  singleton `{w}` is a literal `Set α`. We reuse the existing
  `hardInterventionOn : CDMG α → Set α → CDMG α` API of
  `Section3_2/HardInterventionOn.lean` directly rather than
  introducing a vertex-flavoured `hardInterventionOnVertex`
  wrapper -- the LN's notation is set-flavoured (the more
  general `G_{\doit(W)}` is the actual definitional unit), and
  the single-vertex case is just a one-element instantiation.
  Note also that `G.hardInterventionOn ({w} : Set α)` is
  well-defined for any `w : α` (no `w ∈ G` precondition),
  matching `HardInterventionOn`'s no-precondition design -- a
  design choice that was explicitly justified, in part, by this
  claim's need to write `G.hardInterventionOn {w}` without
  having to discharge `w ∈ G` at every call site.

* **No explicit `v, w, c ∈ G` precondition.** The LN's preamble
  "For `v, w, c ∈ V ∪ J`" is *not* hoisted into a hypothesis on
  the Lean statement. Both sides of the iff already force the
  relevant memberships where they are load-bearing:
  - LHS: a `π : Walk G v w` with `IsBifurcation` has length ≥ 1
    (`length_pos_of_isBifurcation`,
    `Section3_1/Bifurcation.lean` lines 395 -- 399), and its
    first/last/hinge edges place `v`, `w`, `c` in `G` via
    `G.E_subset` / `CDMG.mem_iff`.
  - RHS: each `c ∈ Anc G' v` membership carries a built-in
    `c ∈ G'` clause (`mem_Anc`,
    `Section3_1/FamilyReachability.lean` lines 122 -- 125),
    and the `\ {v}` / `\ {w}` exclusions give the remaining
    `c ≠ v` / `c ≠ w` constraints.
  An explicit precondition would therefore be redundant on both
  sides and would mildly clutter the consumer surface at every
  call site that does not already have the memberships in hand.
  Same no-precondition pattern as `isAcyclic_hardInterventionOn`
  (`Section3_2/AcyclicUnderIntervention.lean` line 191) and the
  `hardInterventionOn_hardInterventionOn` / `_comm` pair in
  `Section3_2/HardInterventionsCommute.lean`.

* **Walk direction: `Walk G v w`, not `Walk G w v`.** Matches
  the LN's def 3.4 ordering `v = v_0 \hus \cdots \hus v_n = w`
  -- the start vertex of the walk is the LN's `v`, the end
  vertex is the LN's `w`. This lets the `BifurcationWitness`'s
  `leftArm` / `rightArm` decomposition line up with the LN's
  left-of-hinge / right-of-hinge arms without any direction
  inversion, and lets `bw.m'` (the source) read off as the
  LN's `v_k` on the right of the hinge. The arrow direction on
  individual edges is independent of the walk direction --
  steps can be `.forward`, `.backward`, or `.bidir` either way
  -- so this choice is purely about index orientation, not
  about which arrows the walk is allowed to contain.

* **Known limitation / future redesign trigger.** The `c ≠ w`
  conjunct on the LHS is a *local* compensation for the
  looseness of `bifurcationSource` in the
  all-backward-walk corner case. Any future downstream claim
  that re-phrases "bifurcation with source `c`" in an
  *asymmetric* shape -- relating the source to ancestral /
  acyclicity / topological-order properties of one specific
  endpoint -- will need to repeat the same `c ≠ w` conjunct (or
  its symmetric `c ≠ v` variant) on its own LHS. Symmetric
  claims (e.g. the marginalisation-preserves-bifurcations
  reading of claim_3_6, which only quantifies source *existence*
  rather than identifying the source with a specific endpoint)
  are corner-case-stable and need no extra bookkeeping. If
  enough downstream rows end up paying this asymmetry tax, the
  **Path 1** refactor (tighten `bifurcationSource` once at the
  source, propagate via the heavy-redesign machinery) should be
  re-considered. -/
theorem bifurcation_alternative {G : CDMG α} {v w c : α} :
    (∃ π : Walk G v w, ∃ hb : π.IsBifurcation,
       π.bifurcationSource hb = some c ∧ c ≠ w)
    ↔ v ≠ w
      ∧ c ∈ Anc (G.hardInterventionOn ({w} : Set α)) v \ {v}
      ∧ c ∈ Anc (G.hardInterventionOn ({v} : Set α)) w \ {w} := by
  sorry

end CDMG

end Causality
