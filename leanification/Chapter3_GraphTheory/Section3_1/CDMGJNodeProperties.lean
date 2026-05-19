import Chapter3_GraphTheory.Section3_1.EdgeRelations

-- The verbatim TeX source of the LN claim is reproduced below; its rendered
-- prose runs past 100 characters. Disable the style linter for this file so
-- the TeX is kept byte-for-byte identical to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# claim_3_1 — `J`-node properties of a CDMG

This file formalises the LN `\begin{Rem}` block tagged `claim_3_1` in
`Section3_1/main.tex`. The remark spells out three immediate consequences
of the typing baked into `def_3_1` (`E ⊆ (J ∪ V) × V`, `L ⊆ V × V`) and the
notation introduced in `def_3_2`:

1. No arrowhead points into a `J`-node — `¬ G.hus (Sum.inl j) v`.
2. Out-edges from a `J`-node land in `V` — a **type-level** fact, see the
   comment block in the middle of this file; not a separate Lean theorem.
3. No two `J`-nodes are adjacent — `¬ G.Adjacent (Sum.inl j₁) (Sum.inl j₂)`.

We state (1) and (3) as `theorem`s with `sorry` bodies; their proofs are
produced by the next worker (`prove_claim_in_lean`) once the tex proof has
been written and verified.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% claim_3_1`):

\begin{claimmark}
\begin{Rem}
With the notations \ref{not-cdmg} the restrictions in definition \ref{def-cdmg} mean that the nodes $j \in J$ will not have any arrowheads pointing towards them: $ j \hus v \notin G$. Nodes $j \in J$ can only point towards nodes $v \in V$: edges $j \tuh v$ are allowed. Furthermore, no two nodes in $J$ are adjacent.
\end{Rem}
\end{claimmark}
-/

-- claim_3_1 (part 1/2) — No arrowhead points into a `J`-node.
--
-- LN fragment:
-- /- the nodes `j ∈ J` will not have any arrowheads pointing towards
--    them: `j \hus v ∉ G`. -/
--
-- In `def_3_2` (`CDMGNotation.lean`), `CDMG.hus` is the "arrowhead on the
-- first endpoint" composite: it is the disjunction of `hut` (i.e. a
-- directed edge into `v₁`) and `huh` (a bidirected edge incident to `v₁`).
-- Both disjuncts require `v₁` to be of the form `Sum.inr _` — that is, to
-- live in `V` — because `E`'s codomain and `L`'s domain are both `V`. So
-- whenever `v₁ = Sum.inl j` with `j : J`, neither disjunct can fire, and
-- `G.hus (Sum.inl j) v` is identically `False`.
--
-- Design choice:
-- * Universally quantify the *target* `v : J ⊕ V` (rather than restricting
--   to `V`): the LN writes `j \hus v ∉ G` with `v` unrestricted, and the
--   stronger statement (no arrowhead, regardless of where the other
--   endpoint sits) is exactly what is true.
-- * `j` is taken as a `J`-node and lifted via `Sum.inl` at the call site,
--   which mirrors the LN's "`j ∈ J`" phrasing one-for-one against our
--   `Sum`-based encoding of `J ∪ V` (`def_3_1`).
-- * Stated about `G.hus` (not unfolded into `hut`/`huh`) so the statement
--   reads at the same level of abstraction as the LN.
theorem CDMG.no_arrowhead_into_J (G : CDMG J V) (j : J) (v : J ⊕ V) :
    ¬ G.hus (Sum.inl j) v := by
  intro h
  unfold CDMG.hus at h
  rcases h with ⟨_, hj, _⟩ | ⟨_, _, hj, _, _⟩
  · cases hj
  · cases hj

-- Note on the middle sentence of the remark — "Nodes `j ∈ J` can only point
-- towards nodes `v ∈ V`: edges `j \tuh v` are allowed."
--
-- This is a *type-level* fact baked into `def_3_2`: `CDMG.tuh` has signature
-- `(v₁ : J ⊕ V) (v₂ : V) → Prop`, so the target of any `tuh`-edge already
-- lives in `V` by construction — independently of whether the source `v₁`
-- is in `J` or in `V`. There is therefore no honest proposition to prove
-- here: any attempt to phrase it as a Lean `theorem` would either be
-- definitionally `True` (e.g. "the target type is `V`") or would have to
-- contort the statement around the existing typing. We deliberately keep
-- this sentence as a comment rather than a `theorem` with a `sorry` /
-- `True` body, in keeping with the project rule against trivial
-- substitutes for statements.

-- claim_3_1 (part 2/2) — No two `J`-nodes are adjacent.
--
-- LN fragment:
-- /- Furthermore, no two nodes in `J` are adjacent. -/
--
-- `CDMG.Adjacent` (from `def_3_3`) unfolds to `CDMG.sus`, the three-way
-- disjunction `tuh ∨ hut ∨ huh`. Each disjunct, after the `Sum.inr`
-- existentials introduced in `def_3_2`, forces at least one of the two
-- endpoints to live in `V`. When both endpoints are `Sum.inl _` (i.e. in
-- `J`), none of the three disjuncts can fire, so adjacency is identically
-- `False`.
--
-- Design choice:
-- * Phrased about `CDMG.Adjacent` (not directly `CDMG.sus`), to match the
--   LN's noun-level wording "no two nodes in `J` are adjacent". This keeps
--   the statement at the abstraction level the LN works at.
-- * Both `j₁` and `j₂` are universally quantified (no `j₁ ≠ j₂`
--   precondition): the LN says "no two nodes in `J` are adjacent",
--   which in our setting is the stronger statement that the relation is
--   identically `False` on `J × J` — there is not even a self-loop in `J`,
--   because edges out of a `J`-node land in `V`.
theorem CDMG.no_J_J_adjacency (G : CDMG J V) (j₁ j₂ : J) :
    ¬ G.Adjacent (Sum.inl j₁) (Sum.inl j₂) := by
  intro h
  unfold CDMG.Adjacent CDMG.sus at h
  rcases h with ⟨_, hj, _⟩ | ⟨_, hj, _⟩ | ⟨_, _, hj, _, _⟩
  · cases hj
  · cases hj
  · cases hj

end Chapter3
end Causality
