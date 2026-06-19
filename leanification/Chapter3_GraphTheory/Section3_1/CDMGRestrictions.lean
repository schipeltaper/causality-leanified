import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations

namespace Causality

/-!
# CDMG restrictions — consequences of the typing constraints (`claim_3_1`)

This file formalises the three consequences of the CDMG typing
constraints stated in the LN remark `claim_3_1`
(`\label{CDMGRestrictions}` in `graphs.tex`, the `\begin{Rem}` block
immediately following `\label{not-cdmg}`).  The remark is an LN
"remark" (`\begin{Rem}`) — i.e. a statement of consequences of
`def_3_1`'s typing constraints, *not* a new definition.  Each
consequence is therefore formalised here as a `theorem` (statement
only, body `sorry` for now; proofs come in `prove_claim_in_lean`).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/claim_3_1_statement_CDMGRestrictions.tex`,
verified equivalent to the LN block plus one operator clarification:

* `[implicit_universal_quantifier_in_hus_clause]` — the LN's
  "$j \hus v \notin G$" and "edges $j \tuh v$ are allowed" carry
  implicit universal quantification over the second-position variable
  `v`.  The rewritten tex surfaces these quantifiers explicitly: in
  clause (i) `v` ranges over `J ∪ V` (every "node in the graph", per
  def_3_2 item 1), while in clause (ii) `v` ranges over `V` only.

## Why three separate theorems, not one with a conjunction?

The canonical tex enumerates three distinct consequences in a numbered
list:

* (i)   No arrowhead points at a `J`-node.
* (ii)  The typing constraint does not forbid a directed `J`→`V` edge.
* (iii) No two `J`-nodes are adjacent.

Each is conceptually independent and downstream consumers will invoke
them individually — walks (`def_3_4`) need (i) to rule out walks
*ending* at a `J`-node by a head, family relationships (`def_3_5`) use
(i) and (iii) to make `Pa^G(j) = ∅` for `j ∈ J`, hard intervention
(`def_3_10`) leverages (ii) when it converts `V`-nodes into `J`-nodes.
A single conjunction `∀ j v, P₁ ∧ P₂ ∧ P₃` would force every consumer
to destructure even when only one consequence is wanted, and the three
clauses *have different quantifier ranges* (clauses (i), (iii) bind
two variables; clause (ii) is a non-existence-style permission claim
with a different quantification range over `v`).  Three theorems also
mirrors the upstream style: `CDMGNotation.lean` has seven separate
`def`s (one per LN-numbered item), `EdgeRelations.lean` has three.

## Use of upstream named relations

* (i) uses `G.hus j v` (def_3_2 item 6) directly — the LN writes this
  clause as `$j \hus v \notin G$` verbatim, and `CDMGNotation.lean`
  provides `hus` precisely so the LN macro has a 1:1 Lean form.
  Unfolding to `(v, j) ∈ E ∨ (j, v) ∈ L` is a single `unfold` step for
  any consumer that wants the set-theoretic form.
* (iii) uses `G.adjacent j₁ j₂` (def_3_3 item i) directly — the
  canonical tex pins it to that definition: "the nodes `j_1` and
  `j_2` are *not* adjacent in `G` in the sense of def
  `\ref{def-edge-relations}` item~i.".
* (ii) is a *permission* statement (the rewrite flags this explicitly:
  not an existence claim).  We render it as the literal typing-
  constraint precondition `j ∈ J ∪ V ∧ v ∈ V` — exactly the shape of
  `hE_subset`'s conclusion in `CDMG.lean`.  Alternative: an
  extensibility statement `∃ G', G'.E = G.E ∪ {(j, v)} ∧ <still valid>`
  reads closer to the natural-language "permitted" but is heavier and
  the canonical tex picked the lighter form.

The substantive per-theorem design rationale lives in the comment
block immediately above each `-- claim_3_1 -- start statement` marker;
read those before modifying the file.
-/

namespace CDMG

-- ## Design choice — section-wide statement context (refactor)
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`, mirror of the
--   pre-refactor `namespace CDMG` helper.*  Inherits unchanged from
--   the original section header: `CDMG` is parameterised by
--   the same arbitrary node type as the original `CDMG`, and the
--   downstream chapter-3 / chapter-4+ consumers continue to
--   instantiate `Node` at their ambient (random-)variable type.  The
--   refactor's only structural change is to `L`'s carrier
--   (`Finset (Node × Node) → Finset (Sym2 Node)`) and the associated
--   `hL_subset` / `hL_irrefl` / `hL_symm` fields; the
--   `[DecidableEq Node]` requirement is unchanged (and is needed by
--   Mathlib's derived `DecidableEq (Sym2 Node)` instance so the new
--   `L` carrier stays computable).
--
-- *Three-dash `--- start helper` / `--- end helper` markers, matching
--   the convention used in `CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean` for their `CDMG`-namespace helper
--   `variable` lines.*  Auto-binding into every theorem below makes
--   this line *load-bearing* (each theorem implicitly carries
--   `{Node : Type*} [DecidableEq Node]`); the three-dash flavour tags
--   it as infrastructure distinct from the per-theorem `start statement`
--   markers, exactly as in the original `CDMG`-namespace block above.
-- claim_3_1 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_1 --- end helper

-- ref: claim_3_1 (part i/iii) — refactor
--
-- For every `j ∈ G.J` and every `v ∈ G.J ∪ G.V`, there is no
-- "head-star" edge `j \hus v` in `G`.  Body identical in structure to
-- the original proof; only the L-disjunct's typing argument adapts —
-- under the refactor `G.L : Finset (Sym2 Node)`, the L-branch of
-- `hus` is `s(j, v) ∈ G.L` (not the ordered pair
-- `(j, v) ∈ G.L`), and `G.hL_subset h (Sym2.mem_mk_left j v)` extracts
-- the LN's "j is mentioned by an L-edge, hence j ∈ V" step in one
-- `Sym2.Mem` invocation rather than via ordered-pair component
-- projection.  The E-branch is structurally unchanged.
/-
LN tex (item i of `refactor_claim_3_1_proof_CDMGRestrictions`):

  For every $j \in J$ and every $v \in J \cup V$,
    $j \hus v \notin G$.
  Unfolding the shorthand $\hus$ via def \ref{not-cdmg} item~6
  (so $j \hus v \in G$ abbreviates $(v, j) \in E \lor s(j, v) \in L$,
  with the L-disjunct expressed via the unordered pair
  $s(j, v) = s(v, j)$ in place of the ordered pair $(j, v)$ used
  pre-refactor), this is equivalent to the set-theoretic conjunction
    $(v, j) \notin E \land s(j, v) \notin L$.
-/
-- ## Design choice
--
-- *Why `¬ G.hus j v`, not the unfolded
--   `(v, j) ∉ G.E ∧ s(j, v) ∉ G.L`.*  Same rationale as the original
--   `no_arrowhead_into_J`: `CDMGNotation.lean`'s `hus` is the
--   LN macro's 1:1 Lean form (the LN's verbatim
--   `$j \hus v \notin G$`), and downstream consumers should reach for
--   `unfold CDMG.hus` once rather than re-derive the
--   disjunction-to-conjunction step at every use site.
--
-- *Why `v ∈ G.J ∪ G.V` rather than `v ∈ G.V` or no constraint at all.*
--   Mirror of the original.  Addition
--   `[implicit_universal_quantifier_in_hus_clause]` puts `v` in the
--   wider set `J ∪ V` for this clause; under the refactor the L-side
--   of the disjunction (`s(j, v) ∈ G.L`) is also vacuously false for
--   `v ∉ G.V` (by `CDMG.hL_subset`'s "every node of an L-edge
--   lies in `V`"), but the LN's quantifier range stays the wider one.
--
-- *L-branch port: from `obtain ⟨hjV, _⟩ := G.hL_subset h` to
--   `Sym2.mem_mk_left j v` + a single `hL_subset` application.*  This
--   is the *only* substantive shape change versus the original proof.
--   Pre-refactor, `h : (j, v) ∈ G.L` plus `hL_subset h` gave
--   `(j, v).1 ∈ G.V ∧ (j, v).2 ∈ G.V` — the first component projection
--   was `j ∈ G.V`.  Post-refactor, `h : s(j, v) ∈ G.L` plus
--   `hL_subset h` gives `∀ ⦃w⦄, w ∈ s(j, v) → w ∈ G.V` (the new
--   "every node mentioned by `s` lies in `V`" form, see the refactored
--   `def_3_1` design block).  To extract `j ∈ G.V` we supply the
--   membership witness `j ∈ s(j, v)` directly — Mathlib's
--   `Sym2.mem_mk_left j v` provides this in one step (`s(j, v)` is
--   `Sym2.mk (j, v)`, and the left endpoint of the underlying ordered
--   pair is always a member of the quotient class).  No `Sym2.lift`
--   destructuring, no representative choice.  This is the canonical
--   `Sym2.Mem` idiom matching `CDMG.hL_subset`'s own
--   `Sym2.Mem` quantifier.
--
-- *E-branch unchanged.*  `G.hut j v` still unfolds to
--   `(v, j) ∈ G.E`, and `CDMG.hE_subset` is unchanged
--   (`E : Finset (Node × Node)` was *not* retyped).  The E-side of the
--   original proof — destructure `G.hE_subset h` to get the head
--   component `j ∈ G.V`, contradict against `hj` ∈ `G.J` via
--   `Finset.disjoint_left.mp G.hJV_disj` — ports mechanically.
-- claim_3_1 -- start statement
theorem no_arrowhead_into_J (G : CDMG Node) {j : Node}
    (hj : j ∈ G.J) {v : Node} (hv : v ∈ G.J ∪ G.V) :
    ¬ G.hus j v
-- claim_3_1 -- end statement
  := by
    -- `hv` is part of the statement for LN-faithful quantifier range
    -- (`v ∈ J ∪ V`), but the contradiction below uses only `hj` and the
    -- typing constraints — the proof faithfully mirrors the tex proof,
    -- which also "fixes $v$" without consuming it.
    let _ := hv
    intro h
    unfold CDMG.hus CDMG.hut
      CDMG.huh at h
    rcases h with h | h
    · obtain ⟨_, hjV⟩ := G.hE_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj hjV
    · have hjV : j ∈ G.V := G.hL_subset h (Sym2.mem_mk_left j v)
      exact Finset.disjoint_left.mp G.hJV_disj hj hjV

-- ref: claim_3_1 (part ii/iii) — refactor
--
-- For every `j ∈ G.J` and every `v ∈ G.V`, the typing constraint
-- `E ⊆ (J ∪ V) × V` of def_3_1 does not forbid the inclusion of the
-- pair `(j, v)` in `G.E`: concretely, `j ∈ G.J ∪ G.V` and `v ∈ G.V`.
-- This is the LN's "edges `j \tuh v` are allowed" clause.
-- *Permission*, not existence — the pair may or may not actually be
-- in `G.E`.  Port is fully mechanical: the refactor only changed `L`'s
-- carrier, not `E`'s, and this clause is *entirely* about `E`'s typing
-- precondition.  Body unchanged; only `G`'s type is retargeted from
-- `CDMG` to `CDMG`.
/-
LN tex (item ii of `refactor_claim_3_1_proof_CDMGRestrictions`):

  For every $j \in J$ and every $v \in V$, the ordered pair $(j, v)$
  satisfies $j \in J \cup V$ and $v \in V$, so the typing constraint
  $E \subseteq (J \cup V) \times V$ of def \ref{def-cdmg} is compatible
  with $(j, v) \in E$; equivalently, no restriction in def
  \ref{def-cdmg} forbids the inclusion of $(j, v)$ in $E$.  This is a
  \emph{permission} statement, not an existence statement.
-/
-- ## Design choice
--
-- *Body unchanged from the original `J_to_V_edge_admissible`; only the
--   `G`'s structure type is retargeted.*  The refactor's L-carrier
--   reshape (`Finset (Node × Node) → Finset (Sym2 Node)`) does not
--   surface at any site in this theorem: the conclusion talks only
--   about `G.J ∪ G.V` and `G.V` (vertex-set membership, unchanged),
--   and the conclusion's *proof* uses only `Finset.mem_union_left`
--   on `hj`.  No `L`-fact, no `hL_subset`, no `hL_irrefl`, no
--   `hL_symm` — this clause is structurally invisible to the
--   refactor.  Archetypal mechanical-port case (cf. `outOf`
--   in `EdgeRelations.lean` for the parallel reasoning).
--
-- *Why the theorem is "trivial" but worth formalising.*  Mirror of
--   the original `J_to_V_edge_admissible`'s rationale: the LN remark
--   *names* this consequence and pairs it with a specific
--   quantification range (`j ∈ J`, `v ∈ V`), so the formalization
--   preserves both as a named theorem.  The "claim" content is the
--   explicit statement of what's permitted, not a proof obligation.
--
-- *Implicit binders for `j` and `v`.*  Same rationale as parts (i)
--   and (iii).
-- claim_3_1 -- start statement
theorem J_to_V_edge_admissible (G : CDMG Node) {j : Node}
    (hj : j ∈ G.J) {v : Node} (hv : v ∈ G.V) :
    j ∈ G.J ∪ G.V ∧ v ∈ G.V
-- claim_3_1 -- end statement
  := by exact ⟨Finset.mem_union_left _ hj, hv⟩

-- ref: claim_3_1 (part iii/iii) — refactor
--
-- For every `j₁ ∈ G.J` and every `j₂ ∈ G.J`, the nodes `j₁` and `j₂`
-- are *not* adjacent in `G` (def_3_3 item i): no directed edge in
-- either direction and no bidirected edge connects them.  Body
-- structurally identical to the original; only the L-branch's typing
-- argument adapts to the `Sym2`-membership form of
-- `CDMG.hL_subset`, exactly as in `no_arrowhead_into_J`.
/-
LN tex (item iii of `refactor_claim_3_1_proof_CDMGRestrictions`):

  For every $j_1 \in J$ and every $j_2 \in J$, the nodes $j_1$ and
  $j_2$ are \emph{not} adjacent in $G$ in the sense of def
  \ref{def-edge-relations} item~i.; equivalently,
    $(j_1, j_2) \notin E \land (j_2, j_1) \notin E \land s(j_1, j_2)
    \notin L$.
-/
-- ## Design choice
--
-- *Why `¬ G.adjacent j₁ j₂`, not the unfolded three-way
--   conjunction.*  Mirror of the original.  `adjacent` is
--   precisely def_3_3 item i (over `CDMG`), and the canonical
--   tex makes the connection explicit ("not adjacent in `G` in the
--   sense of def `\ref{def-edge-relations}` item~i.").  Using the
--   named predicate keeps the statement aligned with that sentence
--   and lets downstream proofs unfold to the three-disjunct
--   `tuh ∨ hut ∨ huh` on demand.
--
-- *No `j₁ ≠ j₂` precondition.*  Mirror of the original.  The LN says
--   "no two nodes in `J` are adjacent" without restricting to distinct
--   nodes; the case `j₁ = j₂` is also covered.  Under the refactor,
--   the `huh` self-loop case `huh j j` (i.e.
--   `s(j, j) ∈ G.L`) is ruled out by `CDMG.hL_irrefl` (no
--   bidirected self-loop — phrased now as `¬ s.IsDiag`, with
--   `s(j, j).IsDiag` immediate via `Sym2.isDiag_iff_proj_eq` or the
--   constructor `Sym2.IsDiag.mk`).  The directed self-loop case
--   `(j, j) ∈ G.E` is not ruled out by `def_3_1` in general, but for
--   `j ∈ G.J` it *is* ruled out: `hE_subset` would force `j ∈ G.V`,
--   contradicting `j ∈ G.J ∧ Disjoint G.J G.V` — same as the
--   pre-refactor case.  So the statement holds also for `j₁ = j₂`,
--   and we omit the distinctness hypothesis.
--
-- *L-branch port (same as for `no_arrowhead_into_J`).*  The
--   pre-refactor L-branch destructured `G.hL_subset h` to get
--   `(j₁, j₂).1 ∈ G.V ∧ (j₁, j₂).2 ∈ G.V` — the first component was
--   `j₁ ∈ G.V`.  Post-refactor `h : s(j₁, j₂) ∈ G.L`, and
--   `G.hL_subset h (Sym2.mem_mk_left j₁ j₂)` gives `j₁ ∈ G.V`
--   directly.  Symmetric extraction `j₂ ∈ G.V` is available via
--   `Sym2.mem_mk_right j₁ j₂` but we pick `j₁` to match the structure
--   of the original proof.
--
-- *Two E-branches unchanged in structure: head-component of `E`'s
--   ordered pair forces the relevant `j_i` into `G.V`.*  The
--   `CDMG.E` carrier is unchanged (still
--   `Finset (Node × Node)`), and `hE_subset`'s signature is unchanged
--   too.  Both branches port mechanically — first branch reads `j₂`
--   off `e.2`, second branch reads `j₁` off `e.2` (note: `hut
--   j₁ j₂` unfolds to `(j₂, j₁) ∈ G.E`, so the head is `j₁`).
--
-- *Implicit binders for `j₁`, `j₂`.*  Same rationale as parts (i) and
--   (ii).
--
-- *Symmetry, not stated explicitly.*  `adjacent` is symmetric
--   in its two arguments (inherits from `sus`'s `tuh ∨ hut`
--   flip combined with the *definitional* swap symmetry of
--   `huh` under the `Sym2` quotient — no `hL_symm` invocation
--   needed, contrast with the pre-refactor encoding).  Stating the
--   theorem in one direction suffices.
-- claim_3_1 -- start statement
theorem J_nodes_not_adjacent (G : CDMG Node) {j₁ : Node}
    (hj₁ : j₁ ∈ G.J) {j₂ : Node} (hj₂ : j₂ ∈ G.J) :
    ¬ G.adjacent j₁ j₂
-- claim_3_1 -- end statement
  := by
    intro h
    unfold CDMG.adjacent CDMG.sus
      CDMG.tuh CDMG.hut
      CDMG.huh at h
    rcases h with h | h | h
    · obtain ⟨_, hj₂V⟩ := G.hE_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj₂ hj₂V
    · obtain ⟨_, hj₁V⟩ := G.hE_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj₁ hj₁V
    · have hj₁V : j₁ ∈ G.V := G.hL_subset h (Sym2.mem_mk_left j₁ j₂)
      exact Finset.disjoint_left.mp G.hJV_disj hj₁ hj₁V

end CDMG

end Causality
