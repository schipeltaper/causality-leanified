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

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches
--   the chapter convention (`CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean`): a CDMG is parameterised by an arbitrary
--   node type so downstream chapters (CBNs in ch. 4, do-calculus in
--   ch. 5, iSCMs in ch. 8–10, discovery in ch. 11+) can instantiate
--   `Node` at the ambient type their (random) variables live on.
--   Fixing `Node` to a concrete carrier here would force every
--   downstream caller of these theorems to renumber.
--   `[DecidableEq Node]` is the minimal typeclass inherited from
--   `def_3_1`: `J, V : Finset Node` and `E, L : Finset (Node × Node)`
--   need decidable equality for `Disjoint J V` (a `CDMG` field),
--   membership tests on `G.J ∪ G.V`, and the unfolding of `G.hus`
--   (`∨` over `Finset` membership) inside each theorem statement.
--
-- *Three-dash `--- start helper` / `--- end helper` markers, not
--   the two-dash `-- start statement` form used by the theorems
--   below.*  Lean 4's `variable` auto-binding means each theorem's
--   signature implicitly carries `{Node : Type*} [DecidableEq Node]`,
--   so this line *is* part of every theorem's statement context — not
--   throwaway local sugar.  The three-dash `helper` flavour tags it
--   as load-bearing infrastructure (distinct from the per-theorem
--   `-- start statement` markers) for the tex/Lean reconciliation
--   tooling.  Matches the wrapping used by
--   `CDMGNotation.lean` (line 90) and `EdgeRelations.lean` (line 91)
--   on the identical `variable` line.
--
-- *`namespace CDMG` (under `Causality`).*  Mirrors `CDMG.lean`,
--   `CDMGNotation.lean`, `EdgeRelations.lean`.  Sharing the namespace
--   gives every theorem below access to field-projection notation
--   `G.hus`, `G.adjacent`, `G.J ∪ G.V`, … without qualification —
--   exactly the left-to-right reading the LN macros (`$j \hus v$`,
--   `$j_1, j_2$ adjacent in $G$`) suggest.
-- claim_3_1 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_1 --- end helper

-- ref: claim_3_1 (part i/iii)
--
-- For every `j ∈ G.J` and every `v ∈ G.J ∪ G.V`, there is no
-- "head-star" edge `j \hus v` in `G`.  Unfolding `hus` via def_3_2
-- item 6, this means `(v, j) ∉ G.E ∧ (j, v) ∉ G.L`, i.e. no directed
-- edge has `j` at the head and no bidirected edge involves `j`.
-- This is the LN's "the nodes `j ∈ J` will not have any arrowheads
-- pointing towards them" clause.
/-
LN tex (item i of `claim_3_1_statement_CDMGRestrictions`, after rewrite):

  For every $j \in J$ and every $v \in J \cup V$,
    $j \hus v \notin G$.
  Unfolding the shorthand $\hus$ via def \ref{not-cdmg} item~6
  (so $j \hus v \in G$ abbreviates $(v, j) \in E \lor (j, v) \in L$),
  this is equivalent to the set-theoretic conjunction
    $(v, j) \notin E \land (j, v) \notin L$.

LN block (verbatim, for backup):

  With the notations \ref{not-cdmg} the restrictions in definition
  \ref{def-cdmg} mean that the nodes $j \in J$ will not have any
  arrowheads pointing towards them: $j \hus v \notin G$.
-/
-- ## Design choice
--
-- *Why `¬ G.hus j v`, not the unfolded `(v, j) ∉ G.E ∧ (j, v) ∉ G.L`.*
--   The LN's verbatim text is `$j \hus v \notin G$`, and
--   `CDMGNotation.lean` exists precisely so that LN macro has a 1:1
--   Lean form.  Stating the conclusion as the unfolded conjunction
--   would mirror the canonical tex's expansion sentence but duplicate
--   `hus`'s body in the statement — every downstream consumer would
--   re-derive the disjunction-to-conjunction step instead of
--   `unfold CDMG.hus` once.  Faithfulness to the LN macro wins.
--
-- *Why `v ∈ G.J ∪ G.V` rather than `v ∈ G.V` or no constraint at all.*
--   Addition `[implicit_universal_quantifier_in_hus_clause]` is
--   explicit: in clause (i), `v` ranges over `J ∪ V` (every "node in
--   the graph").  Dropping the constraint would *technically* yield a
--   stronger statement (vacuously true for `v ∉ G.J ∪ G.V` because
--   `hE_subset` / `hL_subset` exclude such pairs from `G.E ∪ G.L`),
--   but it would no longer match the LN's quantification.
--   Restricting to `G.V` would be wrong — the addition explicitly
--   puts `v` in the wider set `J ∪ V` for this clause.
--
-- *Implicit binders `{j}`, `{v}`, explicit `(hj)`, `(hv)`.*  Standard
--   mathlib style: variables appearing in subsequent argument types
--   are made implicit so callers supply `hj` / `hv` and let Lean
--   infer the witnesses.
--
-- *`G : CDMG Node` first and explicit.*  Enables dot-notation:
--   `G.no_arrowhead_into_J hj hv`.  Matches `G.adjacent`, `G.hus`,
--   `G.hE_subset` style throughout the section.
-- claim_3_1 -- start statement
theorem no_arrowhead_into_J (G : CDMG Node) {j : Node} (hj : j ∈ G.J)
    {v : Node} (hv : v ∈ G.J ∪ G.V) :
    ¬ G.hus j v
-- claim_3_1 -- end statement
  := by
    -- `hv` is part of the statement for LN-faithful quantifier range
    -- (`v ∈ J ∪ V`), but the contradiction below uses only `hj` and the
    -- typing constraints — the proof faithfully mirrors the tex proof,
    -- which also "fixes $v$" without consuming it.
    let _ := hv
    intro h
    unfold CDMG.hus CDMG.hut CDMG.huh at h
    rcases h with h | h
    · obtain ⟨_, hjV⟩ := G.hE_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj hjV
    · obtain ⟨hjV, _⟩ := G.hL_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj hjV

-- ref: claim_3_1 (part ii/iii)
--
-- For every `j ∈ G.J` and every `v ∈ G.V`, the typing constraint
-- `E ⊆ (J ∪ V) × V` of def_3_1 does not forbid the inclusion of the
-- pair `(j, v)` in `G.E`: concretely, `j ∈ G.J ∪ G.V` and `v ∈ G.V`.
-- This is the LN's "edges `j \tuh v` are allowed" clause.
-- *Permission*, not existence — the pair may or may not actually be
-- in `G.E`.
/-
LN tex (item ii of `claim_3_1_statement_CDMGRestrictions`, after rewrite):

  For every $j \in J$ and every $v \in V$, the ordered pair $(j, v)$
  satisfies $j \in J \cup V$ and $v \in V$, so the typing constraint
  $E \subseteq (J \cup V) \times V$ of def \ref{def-cdmg} is compatible
  with $(j, v) \in E$; equivalently, no restriction in def
  \ref{def-cdmg} forbids the inclusion of $(j, v)$ in $E$ (in the
  notation of \ref{not-cdmg}: no restriction forbids $j \tuh v \in G$).
  This is a \emph{permission} statement, not an existence statement:
  $(j, v) \in E$ is admissible by the definition for every
  $(j, v) \in J \times V$, but is not asserted to hold.

LN block (verbatim, for backup):

  Nodes $j \in J$ can only point towards nodes $v \in V$: edges
  $j \tuh v$ are allowed.
-/
-- ## Design choice
--
-- *Permission, not existence — encoded as the typing-constraint
--   precondition.*  The rewrite is explicit: this clause asserts only
--   that the pair `(j, v)` *could* be in `E` without violating the
--   typing constraint, not that it actually is.  The natural Lean
--   rendering is the conjunction `j ∈ G.J ∪ G.V ∧ v ∈ G.V` — exactly
--   the RHS of `hE_subset`'s implication
--   `∀ ⦃e⦄, e ∈ E → e.1 ∈ J ∪ V ∧ e.2 ∈ V`, instantiated at
--   `e = (j, v)`.  We are claiming `(j, v)` *satisfies* that RHS for
--   the relevant range of `j` and `v`.
--
-- *Alternative rejected — extensibility form.*  A closer reading of
--   "permitted" would be `∃ G' : CDMG Node, G'.J = G.J ∧ G'.V = G.V
--   ∧ G'.L = G.L ∧ G'.E = G.E ∪ {(j, v)}` (i.e. the edge can be
--   appended while preserving CDMG-validity).  That form is heavier
--   (needs witness construction + re-proof of every typing field),
--   and the canonical tex chose the lighter typing-precondition
--   form.  Downstream consumers that need the extensibility version
--   can derive it from this theorem.
--
-- *Why this statement is "trivial" but worth formalising.*  The
--   conclusion follows from `hj` and `hv` via `Finset.mem_union_left`
--   alone — no graph-theoretic depth.  But the LN remark *names*
--   this consequence and pairs it with a specific quantification
--   range, so the formalization preserves both as a named theorem.
--   The "claim" content is the explicit statement of what's
--   permitted, not a proof obligation.
--
-- *No `tuh` notation in the conclusion.*  The canonical tex's
--   parenthetic says "in the notation of `\ref{not-cdmg}`: no
--   restriction forbids `j \tuh v \in G`".  Encoding *that* would
--   require an extensibility `∃ G' …` claim (see above).  We use the
--   set-theoretic precondition form (the rewrite's primary phrasing)
--   and treat the `\tuh` reading as commentary.
--
-- *Implicit binders for `j` and `v`.*  Same rationale as part (i).
-- claim_3_1 -- start statement
theorem J_to_V_edge_admissible (G : CDMG Node) {j : Node} (hj : j ∈ G.J)
    {v : Node} (hv : v ∈ G.V) :
    j ∈ G.J ∪ G.V ∧ v ∈ G.V
-- claim_3_1 -- end statement
  := by exact ⟨Finset.mem_union_left _ hj, hv⟩

-- ref: claim_3_1 (part iii/iii)
--
-- For every `j₁ ∈ G.J` and every `j₂ ∈ G.J`, the nodes `j₁` and `j₂`
-- are *not* adjacent in `G` (def_3_3 item i): no directed edge in
-- either direction and no bidirected edge connects them.
/-
LN tex (item iii of `claim_3_1_statement_CDMGRestrictions`, after rewrite):

  For every $j_1 \in J$ and every $j_2 \in J$, the nodes $j_1$ and
  $j_2$ are \emph{not} adjacent in $G$ in the sense of def
  \ref{def-edge-relations} item~i.; equivalently,
    $(j_1, j_2) \notin E \land (j_2, j_1) \notin E \land (j_1, j_2)
    \notin L$.

LN block (verbatim, for backup):

  Furthermore, no two nodes in $J$ are adjacent.
-/
-- ## Design choice
--
-- *Why `¬ G.adjacent j₁ j₂`, not the unfolded three-way conjunction.*
--   `CDMG.adjacent` is precisely def_3_3 item i, and the canonical
--   tex makes the connection explicit ("not adjacent in `G` in the
--   sense of def `\ref{def-edge-relations}` item~i.").  Using the
--   named predicate keeps the statement aligned with that sentence
--   and lets downstream proofs unfold to the three-disjunct
--   `tuh ∨ hut ∨ huh` (or the set-theoretic conjunction) on demand.
--
-- *No `j₁ ≠ j₂` precondition.*  The LN says "no two nodes in `J` are
--   adjacent" without restricting to distinct nodes.  Strictly, the
--   case `j₁ = j₂` is covered too: "`j` is not adjacent to itself".
--   The `huh` self-loop case is ruled out by `hL_irrefl` (no
--   bidirected self-loop).  The directed self-loop case
--   `G.tuh j j ≡ (j, j) ∈ G.E` is *not* ruled out by `def_3_1` in
--   general (see CDMG.lean's "directed self-loops admitted by the
--   type"), but for `j ∈ G.J` it *is* ruled out: `hE_subset` would
--   force `j ∈ G.V`, contradicting `j ∈ G.J ∧ Disjoint G.J G.V`.
--   So the statement holds also for `j₁ = j₂`, and we omit the
--   distinctness hypothesis — staying close to the LN.
--
-- *Implicit binders for `j₁`, `j₂`.*  Same rationale as parts (i)
--   and (ii).
--
-- *Symmetry, not stated explicitly.*  `adjacent` is symmetric in its
--   two arguments (consequence of `sus`'s `tuh ∨ hut` flip combined
--   with `huh` symmetry via `hL_symm`), so
--   `¬ G.adjacent j₁ j₂ ↔ ¬ G.adjacent j₂ j₁`.  Stating the theorem
--   in one direction suffices; the symmetric reading is a one-line
--   corollary.
-- claim_3_1 -- start statement
theorem J_nodes_not_adjacent (G : CDMG Node) {j₁ : Node} (hj₁ : j₁ ∈ G.J)
    {j₂ : Node} (hj₂ : j₂ ∈ G.J) :
    ¬ G.adjacent j₁ j₂
-- claim_3_1 -- end statement
  := by
    intro h
    unfold CDMG.adjacent CDMG.sus CDMG.tuh CDMG.hut CDMG.huh at h
    rcases h with h | h | h
    · obtain ⟨_, hj₂V⟩ := G.hE_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj₂ hj₂V
    · obtain ⟨_, hj₁V⟩ := G.hE_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj₁ hj₁V
    · obtain ⟨hj₁V, _⟩ := G.hL_subset h
      exact Finset.disjoint_left.mp G.hJV_disj hj₁ hj₁V

end CDMG

end Causality
