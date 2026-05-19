# Workspace for claim_3_1 — JNodeProperties

## What this claim is

LN block (graphs.tex, line 84-89, after def_3_2 `not-cdmg`):

> With the notations \ref{not-cdmg} the restrictions in definition
> \ref{def-cdmg} mean that the nodes $j \in J$ will not have any
> arrowheads pointing towards them: $ j \hus v \notin G$. Nodes
> $j \in J$ can only point towards nodes $v \in V$: edges
> $j \tuh v$ are allowed. Furthermore, no two nodes in $J$ are
> adjacent.

It is a remark, no `\begin{proof}` in the LN. The claim is a
collection of **three** independent sub-statements about input nodes;
each one is a direct unfolding of CDMG's structural fields.

## Mapping to existing def_3_1 fields

- `disjoint_JV : Disjoint J V`
- `E_subset   : E ⊆ (J ∪ V) ×ˢ V`  (directed edges target ∈ V)
- `L_subset   : L ⊆ V ×ˢ V`        (bidirected edges live in V × V)

All three sub-statements follow by combining these with disjointness
of `J` and `V`.

## Three sub-statements in Lean (formalization plan)

Using the def_3_2 / def_3_3 names already in the subsection:

1. **No arrowheads into a J-node.**
   `∀ {G : CDMG α} {j : α}, j ∈ G.J → ∀ v : α, ¬ CDMG.hus G j v`
   Equivalent prose: `¬ (j ⇷[G] v)` for any `v`.

2. **Directed edges out of J must target V.**
   `∀ {G : CDMG α} {j : α}, j ∈ G.J → ∀ {w : α},
     CDMG.tuh G j w → w ∈ G.V`
   This is the "j can only point to V" half. The complementary half
   — that no `hut`/`huh` edges leave J — is item (1) above (it's
   the same condition, just stated as "no arrowhead at j").

3. **No two J-nodes are adjacent.**
   `∀ {G : CDMG α} {j₁ j₂ : α}, j₁ ∈ G.J → j₂ ∈ G.J →
     ¬ CDMG.Adjacent G j₁ j₂`

These three should live in a new file
`leanification/Chapter3_GraphTheory/Section3_1/JNodeProperties.lean`
as three separate `theorem`s, each with `sorry`.

## Manager-A vs Manager-B split

I am **Manager A**. My deliverables this run:

1. ✅ Read claude.md + LN main + chapter context + existing
   def_3_1/3_2/3_3 Lean files.
2. ⬜ `spawn_agent_sub_task` → `formalize_claim_in_lean.md` to write
   the three statements in JNodeProperties.lean with `sorry`.
3. ⬜ `review_design` — full-LN-context check of the Lean shape.
4. ⬜ `verify_equivalence` — focused statement-vs-LN check.
5. ⬜ `new_manager` handoff to Manager B (for the tex proof + Lean
   proof phase). The proof for each of the three statements is a
   one-liner unfolding `hus`/`hut`/`huh`/`sus` and combining
   `E_subset` / `L_subset` with `disjoint_JV`.

## Tried so far

- **Turn 1** — `spawn_agent_sub_task` → `formalize_claim_in_lean.md`.
  Worker (session `c62b6b4d-919b-4930-9908-1d34af258ff1`) produced
  `Section3_1/JNodeProperties.lean` with three `sorry`-stubbed
  theorems under `namespace Causality.CDMG`:
    1. `no_arrowhead_into_input (hj : j ∈ G.J) (v : α) : ¬ hus G j v`
    2. `input_edge_target_mem_V (hj : j ∈ G.J) {w : α}
         (h : tuh G j w) : w ∈ G.V`
    3. `input_nodes_not_adjacent (h₁ : j₁ ∈ G.J) (h₂ : j₂ ∈ G.J) :
         ¬ Adjacent G j₁ j₂`
  Also wired into `Chapter3_GraphTheory.lean`. `lake build` clean.
  File has rich design-choice comments per theorem (three-vs-one
  split, explicit/implicit argument choices, why `Adjacent` not
  `sus`, why no `j₁ ≠ j₂` hypothesis).

- **Turn 2** — `review_design` → PASS.
- **Turn 3** — `verify_equivalence` → PASS.
- **Turn 4** — `new_manager` handoff to Manager B (proof phase).

## Manager B notes

I am **Manager B**. Statement phase finished; both verifiers PASSed. My
deliverables this run:

1. ✅ Read claude.md + LN block + Section3_1 state. Confirmed:
   - Statement Lean file `JNodeProperties.lean` has three theorems
     with `sorry`, full design-choice comments per theorem.
   - LN has **no** `\begin{proof}` block after the `\begin{Rem}` — it
     is a remark, not a labelled proposition. The proof must be
     constructed from scratch in the LN paradigm.
   - The proof subfile
     `claim_3_1_proof_JNodeProperties.tex` is the auto-stub with
     `% TODO: write the proof body.`.
2. ✅ `spawn_agent_sub_task` → `write_tex_proof.md`. Worker
   (session `e93cf15c-1f0c-4049-81c5-d6d82682575c`) confirmed there
   is no `\begin{proof}` in the LN (def_3_4 starts at line 91, right
   after `\end{claimmark}` at line 89) and constructed a three-part
   proof from scratch:
     - **(1)** assume `j ∈ J` and `j \hus v ∈ G`; by `not-cdmg`
       split into `\hut`/`\huh`; both branches give `j ∈ V` via
       `E_subset` / `L_subset`; contradicts disjointness.
     - **(2)** `j \tuh w ∈ G ⇒ (j, w) ∈ E ⇒ w ∈ V` by `E_subset`.
     - **(3)** for `j₁, j₂ ∈ J` and `j₁ \sus j₂`, split into the
       three `\sus` disjuncts; each disjunct yields some `j_k \hus
       j_{3-k} ∈ G`, contradicting part (1).
   File written cleanly; renders standalone via `subfiles`.
3. ✅ `verify_tex_proof` (session `444a8ea0-4fe4-4d74-9de3-09b36f23f727`) → **PASS**.
   All checklist items passed; every citation resolves; per-part case-analysis
   is airtight. Proof is ready for leanification.
4. ⬜ `spawn_agent_sub_task` → `prove_claim_in_lean.md` — about to dispatch.
5. ⬜ `simplify_proof`.
6. ⬜ `solved` (`verify_row_solved`).

## Notes for the Lean prover

- Three independent theorems in `JNodeProperties.lean`, each `sorry`-stubbed.
  Goal: replace each `sorry` with a tactic proof mirroring the corresponding
  part of the TeX proof.
- Per-part strategy after unfolding:
  - **(1) `no_arrowhead_into_input`.** `intro v hhus`; unfold `hus` to
    `hut ∨ huh`; in either branch, unfold to membership in `E`/`L`; apply
    `G.E_subset`/`G.L_subset`; obtain `j ∈ V`; close with
    `G.disjoint_JV` (rcases on `Disjoint` or use `Finset.disjoint_left`).
  - **(2) `input_edge_target_mem_V`.** Unfold `tuh` to `(j, w) ∈ E`; apply
    `G.E_subset`; project second coordinate.
  - **(3) `input_nodes_not_adjacent`.** `intro hAdj`; unfold `Adjacent`
    to `sus`; rcases the three disjuncts; each yields a `hus` violating
    part (1) on `j₁` or `j₂`. Be careful with the `tuh` case: the TeX
    proof argues `(j₁, j₂) ∈ E ⇔ j₂ ⇷ j₁` (i.e.\ `j₂ \hut j₁`, hence
    `j₂ \hus j₁`), so the contradiction is via part (1) on `j₂`, not `j₁`.
- Existing helpers to look for in `EdgeRelations.lean` and `CDMGNotation.lean`:
  any `hus_iff_hut_or_huh`, `hut_iff_mem_E`, `huh_iff_mem_L`, `Adjacent_iff`,
  `sus_iff_…` etc. The prover should grep first to avoid reinventing.

## Proof strategy (for the tex worker)

Three sub-claims; each one is a short structural argument from
def_3_1's fields. The tex proof should explicitly cite
\ref{def-cdmg} for `E_subset`, `L_subset`, and `disjoint_JV`.

- **(1) No arrowhead at $j$.** Suppose $j \hus v \in G$. By
  def_3_2 either $j \hut v \in G$ (i.e.\ $(v,j) \in E$) or
  $j \huh v \in G$ (i.e.\ $(j,v) \in L$). In the first case
  `E_subset` gives $j \in V$, contradicting $j \in J$ (disjoint).
  In the second case `L_subset` gives $j \in V$, same contradiction.
- **(2) Directed edges out of $J$ target $V$.** If $j \tuh w$ then
  $(j,w) \in E$ so by `E_subset` $w \in V$.
- **(3) No two $J$-nodes adjacent.** If $j_1, j_2 \in J$ and
  $\Adjacent(j_1,j_2)$, expand to $j_1 \sus j_2$. The three
  disjuncts each contradict step (1) or `L_irrefl` (for $j_1 = j_2$
  with a `huh` self-loop).
