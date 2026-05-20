import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.AcyclicUnderIntervention
import Chapter3_GraphTheory.Section3_2.SplitTopologicalOrder

-- TeX proof: tex/claim_3_9_proof_SwigAcyclicTopologicalOrder.tex

/-!
# Acyclicity and topological orders survive the SWIG (claim_3_9)

This file formalises the lecture notes' remark immediately following
the definition of the SWIG `G_{\swig(W)}` (def_3_12): if `G` is a
CADMG (i.e. acyclic) and `W ⊆ G.V`, then `G.nodeSplittingHardInterven
tionOn W hW` is also acyclic; furthermore, given a topological order
`<` of `G`, an *explicit* topological order on the SWIG can be built
by interleaving each `v_j ∈ W` with two new index slots `j - 1/3` and
`j + 1/3` for `v_j^o` and `v_j^i` respectively, then re-sorting. See
`lecture-notes/lecture_notes/graphs.tex` Rem at line 612.

This row is the **corollary chain of claim_3_3 + claim_3_6**: the LN's
own def_3_12 spells `G_{\swig(W)}` as a node-splitting followed by a
hard intervention on the fresh `W^i` copies, and in Lean
`nodeSplittingHardInterventionOn = (· .nodeSplittingOn _ _).hardInter
ventionOn (Set.range Sum.inr)`. The two halves of the SWIG remark are
therefore the **literal composites** of the two halves of claim_3_6
with the two halves of claim_3_3:

* **Part A (topological order, constructive content)** -- apply
  `isTopologicalOrder_nodeSplittingOn` to `hr` to lift the topological
  order `r` of `G` to `splitOrder W r` on the split graph, then apply
  `isTopologicalOrder_hardInterventionOn` to that result with the
  precondition `Set.range Sum.inr ⊆ (G.nodeSplittingOn W hW).J ∪
  (G.nodeSplittingOn W hW).V` (which holds because every `Sum.inr w`
  is an input of the post-NS graph by `nodeSplittingOn_J`). The
  topological order on the SWIG is **literally `splitOrder W r`**, the
  same relation produced by claim_3_6 -- the LN's `±1/3` index recipe
  for `v_j^o`, `v_j^i` (claim_3_9) is identical to the recipe for
  `v_j^0`, `v_j^1` (claim_3_6) under our `^o = ^0 = Sum.inl`, `^i = ^1
  = Sum.inr` convention (set in `NodeSplittingOn.lean`).
* **Part B (acyclicity, side-condition content)** -- apply
  `isAcyclic_nodeSplittingOn` to `h` to get acyclicity of the split
  graph, then apply `isAcyclic_hardInterventionOn` (no precondition
  required at the HI step) to obtain acyclicity of the SWIG.

The two halves split into two theorems exactly the way claim_3_6
splits, and exactly the way claim_3_3 splits for the HI-only analogue:
the topological-order half is the **named-construction** result
(downstream callers want `splitOrder W r` by name to plug into their
own constructions); the acyclicity half is the **side-condition**
result (downstream callers want `(G.swig W hW).IsAcyclic` as a
hypothesis without committing to a specific topological order).
Bundling them would force one class of callers to project or to drag
in data they do not need. This mirrors `SplitTopologicalOrder.lean`'s
and `AcyclicUnderIntervention.lean`'s precedents exactly.

## Where this gets used downstream

* **Chapters 4 -- 6 (CBNs, do-calculus, ID-algorithm)** -- soundness
  arguments that intervene by SWIG (rather than the simpler `do(W)`
  hard intervention) read the topological order on `G_{\swig(W)}` off
  as `splitOrder W <` for the original `<`, and the SWIG's acyclicity
  is a standing precondition for talking about Markov blankets and
  ID-algorithm subroutines that pattern-match on parent / descendant
  relations.
* **Chapters 8 -- 10 (iSCMs, SWIGs and counterfactuals)** -- the
  Richardson--Robins SWIG machinery and the iSCM counterfactual
  uniqueness theory both quote the SWIG's topological order along
  which counterfactual mechanisms are evaluated. The order is
  *exactly* `splitOrder W <` produced here.
* **Chapters 11 -- 16 (causal discovery)** -- FCI and related
  algorithms over latent confounding pass through SWIG-style derived
  graphs at intermediate steps; acyclicity of the SWIG is the
  (sometimes implicit) sanity check.

Foundational: every chapter past chapter 7 leans on the SWIG. The
proof-phase will likely be short -- both halves are one-line
composites of the existing claim_3_3 + claim_3_6 theorems, modulo a
short subset-of-node-set argument for the HI precondition in Part A.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- claim_3_9 (part A)
-- title: SwigAcyclicTopologicalOrder -- topological order preserved
--
-- The LN's "for a CADMG `G = (J, V, E, L)`, also `G_{\swig(W)}` is
-- acyclic; if `<` is any topological order of `G` ... then ... a
-- topological order for `G_{\swig(W)}` can be achieved by assigning
-- `v_j^o` the index `j - 1/3` and `v_j^i` the index `j + 1/3` and
-- ordering by index value" splits into two formal statements (see
-- the file-level docstring for the rationale). This is the
-- *constructive* half: from a topological order `r` of `G` and the
-- precondition `hW : W ⊆ G.V` (required by
-- `nodeSplittingHardInterventionOn` def_3_12 itself, inherited from
-- `nodeSplittingOn` def_3_11), produce a topological order
-- `splitOrder W r` of `G.nodeSplittingHardInterventionOn W hW`. The
-- construction follows the LN's `± 1/3` interleaving recipe for
-- `v_j^o` / `v_j^i` verbatim -- which, under our `^o = Sum.inl`,
-- `^i = Sum.inr` convention, is *exactly* the same relation
-- `splitOrder W r` produced by claim_3_6 (where the recipe was
-- written `v_j^0` / `v_j^1`). The reuse-by-name is intentional --
-- see the design block below.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Rem 612):

\begin{claimmark}
\begin{Rem}
    For a CADMG $G=(J,V,E,L)$, also $G_{\swig(W)}$ is acyclic.
    If $<$ is any topological order of $G$ given by enumerating all
    nodes $v \in J \cup V$ via:
    \[ v_1 < v_2 < \cdots < v_n,\]
    then, for instance,
    a topological order for $G_{\swig(W)}$ can be achieved by
    assigning for a node $v_j \in W$ with index $j$ the node
    $v_j^o$ the index $j-\frac{1}{3}$
    and $v_j^i$ the index $j+\frac{1}{3}$, and then ordering all
    nodes according to their index value.
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Two theorems rather than one bundled conjunction.** The LN's
--   single `\Rem` mixes a *named-construction* statement (the
--   topological order is `splitOrder W r`, plug it in by name) with
--   a *side-condition* statement (the SWIG is acyclic, use as a
--   precondition). Bundling them as `... .IsAcyclic ∧ ... .IsTopo
--   logicalOrder (splitOrder W r)` would force every consumer that
--   only wants one side to either project (`.1` / `.2`) or to drag
--   in data they do not need. This split follows the precedent in
--   `SplitTopologicalOrder.lean` (claim_3_6) -- the SWIG analogue
--   here -- and `AcyclicUnderIntervention.lean` (claim_3_3) -- the
--   HI-only analogue -- both of which split their LN `\Rem` block
--   into two theorems for the same reason.
-- * **`splitOrder W r` is reused by name, not redefined.** The
--   carrier of `G.nodeSplittingHardInterventionOn W hW` is the same
--   `α ⊕ ↑W` as the carrier of `G.nodeSplittingOn W hW` (the HI
--   step preserves the carrier; see `HardInterventionOn.lean`), so
--   the `splitOrder` relation -- which is purely typed on the
--   carrier and parameterised by `W : Set α` and `r : α → α →
--   Prop` -- has the right type to live on the SWIG directly. The
--   LN's `±1/3` recipe for `v_j^o` / `v_j^i` is identical to its
--   recipe for `v_j^0` / `v_j^1` (modulo notation), under our
--   `^o = ^0 = Sum.inl`, `^i = ^1 = Sum.inr` convention (fixed in
--   `NodeSplittingOn.lean`); redefining the relation would be a
--   syntactic alias of the existing one. Reusing it by name also
--   means downstream callers (counterfactual chapters quoting
--   "the topological order on the SWIG inherited from `<`") talk
--   about a *single* named relation regardless of whether they
--   first chain through `nodeSplittingOn` or jump directly to the
--   SWIG.
-- * **J / V partition is preserved through NS + HI, exactly the way
--   the LN's `\Rem` reads.** By `nodeSplittingHardInterventionOn_J`
--   and `_V` (in `NodeSplittingHard.lean`), the SWIG splits the
--   carrier `α ⊕ ↑W` as
--   `J_{SWIG} = Sum.inl '' G.J ∪ Set.range Sum.inr` and
--   `V_{SWIG} = Sum.inl '' G.V`, so the fresh `v_j^o = Sum.inl w`
--   live in the SWIG's *output* set `V_{SWIG}` (because `w ∈ W ⊆
--   G.V` lifts under `Sum.inl`) and the fresh `v_j^i = Sum.inr
--   ⟨w, _⟩` live in the SWIG's *input* set `J_{SWIG}` (because the
--   HI step promotes them to inputs). The `splitOrder W r`
--   construction then quantifies its `IsTopologicalOrder` fields
--   over `J_{SWIG} ∪ V_{SWIG}` -- exactly the LN's "enumerate all
--   nodes $v \in J \cup V$" -- with each `v_j^o` getting index
--   `j - 1/3` and each `v_j^i` getting index `j + 1/3`. The
--   def_3_12 file already explains the four-bullet construction;
--   this bullet just flags the *partition* point so the reader of
--   this row does not have to re-derive which split-vertex lives
--   on which side of the J / V cut.
-- * **`{G}, {W}, hW, {r}, hr` binder choice.** Same rationale as
--   `isTopologicalOrder_nodeSplittingOn` (claim_3_6 part A) --
--   `G`, `W`, `r` are implicit because they are unifiable from the
--   conclusion `(G.nodeSplittingHardInterventionOn W hW).IsTopologi
--   calOrder (splitOrder W r)` and from `hW` / `hr`. `hW` is
--   explicit because `nodeSplittingHardInterventionOn` (def_3_12)
--   demands it as a structural precondition.
-- * **No `[Finite α]` instance hypothesis.** Inherits from the
--   claim_3_6 part A and claim_3_3 part B precedents: the
--   constructive content is purely relational, and the composite
--   proof route (Part A of this row chains through the same two
--   theorems) does not introduce finiteness anywhere.
-- * **Naming `isTopologicalOrder_nodeSplittingHardInterventionOn`.**
--   Mirrors `isTopologicalOrder_nodeSplittingOn` (claim_3_6 part A)
--   and `isTopologicalOrder_hardInterventionOn` (claim_3_3 part B)
--   and follows Mathlib's `<conclusion>_<construction>` convention.
--   The long-form name (rather than the `swig` alias) is used so
--   the lemma matches the underlying `def` name; downstream callers
--   can still invoke it through the `swig` alias by reducibility
--   (cf. the `noncomputable abbrev swig` in `NodeSplittingHard.lean`).
-- * **Downstream impact.** Counterfactual / iSCM chapters (8 -- 16)
--   quote the SWIG's topological order pervasively; this theorem is
--   the *foundational* result they rely on. Choosing the same named
--   relation `splitOrder W r` as claim_3_6 means the chapters can
--   stay agnostic about whether the user reached the SWIG via the
--   composition or directly.

/-- claim_3_9 part A: if `W ⊆ G.V` and `r` is a topological order of
`G`, then `splitOrder W r` is a topological order of
`G.nodeSplittingHardInterventionOn W hW` (the SWIG). Mirrors the
constructive half of the `\Rem` immediately after def_3_12 in
`lecture-notes/lecture_notes/graphs.tex` (line 612), with the LN's
`± 1/3` interleaving recipe for `v_j^o` / `v_j^i` encoded as the
four-case `splitOrder` pattern match -- the *same* `splitOrder W r`
relation produced by claim_3_6 (whose recipe for `v_j^0` / `v_j^1`
agrees with the SWIG's `v_j^o` / `v_j^i` under our
`^o = ^0 = Sum.inl`, `^i = ^1 = Sum.inr` convention).

The `W ⊆ G.V` precondition is structurally required by
`nodeSplittingHardInterventionOn` itself (def_3_12), inherited from
`nodeSplittingOn` def_3_11; it is *not* a topological-order
condition.

See `isAcyclic_nodeSplittingHardInterventionOn` below for the
acyclicity half of the LN remark and the file-level docstring for
the rationale behind splitting the LN's single `\Rem` into two
theorems. This row is the corollary chain of claim_3_3 + claim_3_6;
both halves are short composites of the existing theorems. -/
theorem isTopologicalOrder_nodeSplittingHardInterventionOn
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V)
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    (G.nodeSplittingHardInterventionOn W hW).IsTopologicalOrder
      (splitOrder W r) := sorry

-- claim_3_9 (part B)
-- title: SwigAcyclicTopologicalOrder -- acyclicity preserved
--
-- The acyclicity half of the LN remark: if `G` is acyclic and
-- `W ⊆ G.V`, then `G.nodeSplittingHardInterventionOn W hW` is
-- acyclic. By def_3_12 the SWIG is the composition
-- `(G.nodeSplittingOn W hW).hardInterventionOn (Set.range Sum.inr)`,
-- so this is `isAcyclic_hardInterventionOn` applied to the result
-- of `isAcyclic_nodeSplittingOn h` -- a literal one-line composite
-- of the existing claim_3_6 part B and claim_3_3 part A.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Rem 612; same block as part A):

\begin{claimmark}
\begin{Rem}
    For a CADMG $G=(J,V,E,L)$, also $G_{\swig(W)}$ is acyclic.
    ...
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Why a separate theorem from the topological-order half.**
--   Same rationale as Part A: the topological-order half is the
--   *named-construction* result while the acyclicity half is the
--   *side-condition* result, and the two classes of downstream
--   callers want different shapes. Mirrors claim_3_6's and
--   claim_3_3's two-theorem decompositions.
-- * **`{G}, {W}, hW, h` binder choice.** Same rationale as Part A
--   and as `isAcyclic_nodeSplittingOn` (claim_3_6 part B): `G`,
--   `W` are implicit (recovered from the conclusion / `hW`); `hW`
--   is explicit because `nodeSplittingHardInterventionOn` (def_3_12)
--   demands it as a structural precondition; `h : G.IsAcyclic` is
--   explicit because it is the hypothesis being transported, with
--   no opportunity for unification.
-- * **`G.IsAcyclic` as a separate hypothesis, not bundled into the
--   carrier.** `CDMG α` is the LN's *unconditional* DMG carrier
--   (def_3_1); it does *not* bundle acyclicity. The LN reserves
--   the *A* in CADMG for the conditional+acyclic refinement, and
--   in this formalisation we model that distinction by leaving
--   `IsAcyclic` as a `Prop`-valued predicate (in
--   `Section3_1/Acyclicity.lean`) rather than as a `CADMG`
--   structure or typeclass. Taking `h : G.IsAcyclic` as an
--   explicit hypothesis here is the consequence: every claim about
--   "for a CADMG `G = (J, V, E, L)`, also $G_{\swig(W)}$ is
--   acyclic" has to pass that hypothesis explicitly. Bundling it
--   into a `CADMG` typeclass would force every chapter-3 lemma to
--   either restate the typeclass instance (boilerplate) or to
--   commit early to a refinement that some downstream rows (e.g.
--   the not-yet-acyclic precursors in chapter 4 -- 6) need to
--   relax again. Note also that Part A's
--   `IsTopologicalOrder` hypothesis `hr` already *implies* the
--   SWIG's acyclicity for the same reason `IsTopologicalOrder`
--   implies acyclicity in the original graph (claim_3_2's `←`
--   direction); duplicating `h : G.IsAcyclic` in Part A would be
--   redundant. Part B is the dual: callers who have `G.IsAcyclic`
--   without a named topological order to hand should not be forced
--   to invent one just to reach the conclusion.
-- * **No `[Finite α]` instance hypothesis at statement phase.** The
--   composite proof route inherits the choice from claim_3_6 part
--   B: if the prover routes through claim_3_6 part B's preferred
--   walk-lifting (route ii in `SplitTopologicalOrder.lean`'s design
--   block), no finiteness enters; if the prover routes through
--   claim_3_2's iff (route i), `[Finite α]` is introduced as needed
--   via a `correct_tex_proof` request. Statement-phase keeps both
--   routes open. The HI step does not introduce finiteness in
--   either case (claim_3_3 part A is direct and finiteness-free).
-- * **Naming `isAcyclic_nodeSplittingHardInterventionOn`.** Mirrors
--   `isAcyclic_nodeSplittingOn` (claim_3_6 part B) and
--   `isAcyclic_hardInterventionOn` (claim_3_3 part A) -- the
--   `IsAcyclic` part comes first because it is the result, the
--   `nodeSplittingHardInterventionOn` part second because it is the
--   construction we are showing preserves acyclicity. Long-form
--   name (rather than `swig` alias) for the same reason as Part A.
-- * **Downstream impact.** Acyclicity of the SWIG is a standing
--   precondition for talking about parents / descendants / Markov
--   blankets / districts on the SWIG; counterfactual chapters
--   (8 -- 16) use this preservation result silently whenever they
--   form `G_{\swig(W)}` from an acyclic input CADMG.

/-- claim_3_9 part B: if `W ⊆ G.V` and `G` is acyclic, then
`G.nodeSplittingHardInterventionOn W hW` (the SWIG) is acyclic.
Mirrors the acyclicity half of the `\Rem` immediately after def_3_12
in `lecture-notes/lecture_notes/graphs.tex` (line 612); see
`isTopologicalOrder_nodeSplittingHardInterventionOn` above for the
constructive half and the file-level docstring for the rationale
behind splitting the LN's single `\Rem` into two theorems.

The `W ⊆ G.V` precondition is structurally required by
`nodeSplittingHardInterventionOn` itself (def_3_12); see
`isTopologicalOrder_nodeSplittingHardInterventionOn`. No `[Finite α]`
hypothesis is added at the statement phase, keeping both proof routes
open (composite via claim_3_6 part B + claim_3_3 part A, or direct
walk-lifting on the SWIG). -/
theorem isAcyclic_nodeSplittingHardInterventionOn
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V)
    (h : G.IsAcyclic) :
    (G.nodeSplittingHardInterventionOn W hW).IsAcyclic := sorry

end CDMG

end Causality
