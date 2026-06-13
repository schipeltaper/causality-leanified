# Workspace for claim_3_16 — MargPreservesAncestors (refactor `marginalize_loose_self_cycle`)

## Refactor context (recap)

`def_3_14` swapped `MarginalizationΦE` (5 conjuncts, last one = `u = v → length ≥ 2`)
for `refactor_MarginalizationΦE` (4 conjuncts, self-cycle restriction dropped).
Knock-on twins also wrapped in `MarginalizationAK.lean`:

| Original                          | Replacement                                |
|-----------------------------------|--------------------------------------------|
| `MarginalizationΦE`               | `refactor_MarginalizationΦE`               |
| `instDecidableMarginalizationΦE`  | `refactor_instDecidableMarginalizationΦE`  |
| `marginalize_hE_subset`           | `refactor_marginalize_hE_subset`           |
| `marginalize`                     | `refactor_marginalize`                     |

`MarginalizationΦL`, `instDecidableMarginalizationΦL`, `marginalize_hJV_disj`,
`marginalize_hL_*` are unchanged. Semantically:
`(G.refactor_marginalize W hW).E ⊇ (G.marginalize W hW).E` (refactor adds length-1
`G.E`-self-edges `(v, v)` for `v ∈ V ∖ W`). The `L` field, `J`, `V`, all proof
obligation discharges, are bit-for-bit identical between the two.

For `claim_3_16` (this row, DEPENDENT) the LN sub-claims are unchanged; only the
Lean encoding (which now quantifies over `refactor_marginalize`) needs replacement
twins. The proof strategy of the tex twin is the same — only the Φ_E description
loses one clause.

---

## File / line inventory (read-first map)

### `MarginalizationAK.lean` — refactor markers already in place
Confirmed read; no changes needed in this file.
- L198–207 ORIGINAL `MarginalizationΦE`, L327–335 REPLACEMENT `refactor_MarginalizationΦE`.
- L510–515 ORIGINAL `instDecidableMarginalizationΦE`, L535–540 REPLACEMENT twin.
- L570–578 ORIGINAL `marginalize_hE_subset`, L595–603 REPLACEMENT twin.
- L859–876 ORIGINAL `marginalize`, L1126–1143 REPLACEMENT `refactor_marginalize`.

### `MargPreservesAncestors.lean` — the work surface (3845 lines)

#### Helpers that quantify over `G.marginalize` and therefore need refactor twins

| Helper                                          | Line | Touch Φ_E? | Notes                                       |
|-------------------------------------------------|------|-----------|---------------------------------------------|
| `mem_of_mem_marginalize`                        | 238  | no        | trivial; `change v ∈ G.J ∪ (G.V \ W)` works the same on the new marg (same `J`/`V`). |
| `notW_of_mem_marginalize`                       | 248  | no        | trivial; same. |
| `expand_directed_walk_marginalize`              | 312  | **YES**   | destructures Φ_E **5-tuple at L342**: `⟨q_edge, hq_edge_dir, hq_edge_pos, hq_edge_inter, _⟩`. Under refactor → **drop trailing `_`**: `⟨q_edge, hq_edge_dir, hq_edge_pos, hq_edge_inter⟩`. The `ha_filter` line at L337–339 also references `MarginalizationΦE` — switch to `refactor_MarginalizationΦE` and `G.refactor_marginalize` for the marg-edge unfold. |
| `project_directed_walk_aux`                     | 477  | **YES**   | constructs Φ_E **5-args at L530**: `refine ⟨head, h_head_dir, h_head_pos, h_head_inter, ?_⟩; intro heq; exact absurd heq hv₁_eq_m`. Under refactor → **drop the 5th-arg goal + the `intro heq; exact absurd heq hv₁_eq_m` cleanup**: `exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩`. The L523–525 `change` references `MarginalizationΦE` → `refactor_MarginalizationΦE`. The `v₁ = m` self-loop branch (L512–520) becomes structurally redundant under refactor (the refactor admits self-edges of the form `(v₁, v₁) ∈ marg.E` via *any* witnessing walk of length ≥ 1, including the head); **keep the by_cases split for proof-structural parity with the original** and just drop the 5th-arg in the non-self-loop branch. |
| `project_directed_walk_marginalize` (wrapper)   | 540  | no        | one-liner wrapper; just renames `G.marginalize` → `G.refactor_marginalize` and calls `refactor_project_directed_walk_aux`. |
| `project_directed_walk_with_vertex_subset_aux`  | 556  | **YES**   | constructs Φ_E **5-args at L663**, same pattern as `project_directed_walk_aux`. Switch L658–659 `change` reference and drop the 5th arg. |
| `project_directed_walk_strong` (wrapper)        | 702  | no        | wrapper of the previous; rename `G.marginalize` → `G.refactor_marginalize`. |

#### Bifurcation helpers that quantify over `G.marginalize` — refactor twins, **mechanical**
These all need refactor twins, but their proof bodies change only by:
- Signature substitution `G.marginalize` → `G.refactor_marginalize` (in `hu`, `hw`, return type, and any local `Walk (G.marginalize …)` annotations).
- Helper call substitution `expand_directed_walk_marginalize` →
  `refactor_expand_directed_walk_marginalize`,
  `project_directed_walk_strong` → `refactor_project_directed_walk_strong`,
  `project_directed_walk_marginalize` → `refactor_project_directed_walk_marginalize`,
  `mem_of_mem_marginalize` → `refactor_mem_of_mem_marginalize`,
  `notW_of_mem_marginalize` → `refactor_notW_of_mem_marginalize`.
- The marg-`L` filter unfolds (e.g. L1995, L2368, L2421) continue to use
  `G.MarginalizationΦL` verbatim because `refactor_marginalize.L` is bit-identical
  to `marginalize.L`. Just update the `change` LHS `(G.marginalize W hW).L` →
  `(G.refactor_marginalize W hW).L`.

| Helper                                       | Line | Calls Φ_E-helper twins? |
|----------------------------------------------|------|-------------------------|
| `marg_preserves_bifSource_forward`           | 1706 | yes (`project_directed_walk_strong`) |
| `marg_preserves_bifSource_backward`          | 1773 | yes (`expand_directed_walk_marginalize`) |
| `marg_bif_forward_dir_hinge_src_marg`        | 1861 | yes (calls `marg_preserves_bifSource_forward`) |
| `marg_bif_backward_dir_hinge`                | 1882 | yes (calls `marg_preserves_bifSource_backward`) |
| `marg_bif_backward_bidir_hinge`              | 1983 | yes (`expand_directed_walk_marginalize`) |
| `marg_bif_forward_bidir_both_notW`           | 2325 | yes (`project_directed_walk_strong`) |
| `marg_bif_forward_assemble_bidirected`       | 2400 | yes (`project_directed_walk_strong`) |
| `marg_bif_forward_dir_hinge_src_W`           | 2445 | uses `find_first_non_W_directed` (unchanged) + `marg_bif_forward_assemble_bidirected` (twin) |
| `marg_bif_forward_bidir_finish`              | 2745 | uses `marg_bif_forward_assemble_bidirected` (twin) |
| `marg_bif_forward_bidir_with_W`              | 2973 | uses `find_first_non_W_directed` (unchanged) + `marg_bif_forward_bidir_finish` (twin) |
| `marg_preserves_bif_forward`                 | 3114 | dispatcher: calls forward leaf helpers (all twinned) |
| `marg_preserves_bif_backward`                | 3141 | dispatcher: calls backward leaf helpers (all twinned) |

#### 5 main theorems — refactor twins, the user-visible API

| Theorem (actual Lean name)                            | Line | Body sketch                                            |
|-------------------------------------------------------|------|--------------------------------------------------------|
| `marginalize_preserves_ancestors`                     | 3244 | direct rewrite: replace `marginalize` → `refactor_marginalize`, swap `project_directed_walk_marginalize` and `expand_directed_walk_marginalize` for their twins. |
| `marginalize_preserves_bifurcation`                   | 3385 | direct rewrite: replace `marginalize` → `refactor_marginalize`, swap `marg_preserves_bif_forward` / `_backward` for their twins. |
| `marginalize_preserves_bifurcation_with_source`       | 3552 | direct rewrite: replace `marginalize` → `refactor_marginalize`, swap `marg_preserves_bifSource_forward` / `_backward` for their twins. |
| `marginalize_preserves_acyclic`                       | 3644 | direct rewrite: replace `marginalize` → `refactor_marginalize`, swap `mem_of_mem_marginalize` and `expand_directed_walk_marginalize` for their twins. |
| `marginalize_restricts_topological_order`             | 3805 | direct rewrite: replace `marginalize` → `refactor_marginalize`. **Φ_E destructure at L3840**: `⟨p, hp_dir, hp_pos, _, _⟩` → `⟨p, hp_dir, hp_pos, _⟩` (one fewer underscore). The `change` at L3836–3837 references `MarginalizationΦE` → `refactor_MarginalizationΦE`. Swap `mem_of_mem_marginalize` → twin. |

#### Helpers that do NOT need a refactor twin (operate on `G` alone, or are pure
walk algebra over `Walk G _ _`)
- `Walk.comp`, `Walk.length_comp`, `Walk.isDirectedWalk_comp` (L130–149)
- `Walk.vertices_ne_nil`, `Walk.head_mem_vertices`, `Walk.vertices_comp` (L151–171)
- `WalkStep.source_mem`, `Walk.mem_of_mem_vertices` (L173–200)
- `Walk.source_in_G_of_directedWalk_pos`, `Walk.target_in_GV_of_directedWalk_pos`,
  `Walk.target_in_G_of_directedWalk_pos` (L202–235)
- `Walk.lt_of_directedWalk_pos` (L261)
- `Walk.vertices_eq_head_cons_tail`, `Walk.tail_vertices_ne_nil_of_pos` (L293–304)
- `find_first_non_W_directed` (L404) — pure G-walk surgery, NO `G.marginalize` quantifier
- All `Walk.reverseDirected`, `Walk.mkBifurcation*`, `Walk.exists_arms_of_*`,
  `Walk.singleEdge_*`, `Walk.length_pos_of_*`, `Walk.arm_dropLast_in_W`,
  `Walk.isBifurcation*` (L714–1697) — pure walk algebra on `Walk G`

These ~25 helpers stay unchanged and are referenced by both original and refactor
twins.

### `tex/claim_3_16_proof_MargPreservesAncestors.tex` (549 lines)
**Twin file to create**: `tex/refactor_claim_3_16_proof_MargPreservesAncestors.tex`.
The proof strategy is unchanged. Only the **setup paragraph's Φ_E description**
(around L150) needs surgery; the rest can be copied verbatim.

Concretely, the line
> "$\Phi_E^{\sm W}(\ul{v}, \ol{v})$ asserts the existence of a directed walk in $G$
> (in the sense of def \ref{def:walks}, item~ii.) from $\ul{v}$ to $\ol{v}$ of
> length $n \ge 1$ whose intermediate vertices $w_1, \dots, w_{n-1}$ (if any) all
> lie in $W$, **subject to the self-cycle restriction that $\ul{v} = \ol{v}
> \Rightarrow n \ge 2$**. (The restriction is automatic in the witnessing argument
> because no walk of length~$1$ with $\ul{v} = \ol{v}$ has any intermediate vertex
> through which the path could pass; an honest witness for a $G^{\sm W}$-self-cycle
> $(\ul{v}, \ul{v}) \in E^{\sm W}$ requires a $G$-walk that traverses at least one
> $W$-vertex on its way back to $\ul{v}$, and is of length $\ge 2$ by construction.)"

should become

> "$\Phi_E^{\sm W}(\ul{v}, \ol{v})$ asserts the existence of a directed walk in $G$
> (in the sense of def \ref{def:walks}, item~ii.) from $\ul{v}$ to $\ol{v}$ of
> length $n \ge 1$ whose intermediate vertices $w_1, \dots, w_{n-1}$ (if any) all
> lie in $W$. (Note: per the LN footnote at item~iii.\ of def
> \ref{def:G_marginalization}, self-cycles $\ul{v} = \ol{v}$ are admitted, in
> particular by length-$1$ direct edges $(\ul{v}, \ul{v}) \in E$ with
> $\ul{v} \in V \sm W$, and equally by longer $W$-traversing walks
> $\ul{v} \to w_1 \to \dots \to \ul{v}$.)"

All five sub-claim proofs (i, ii(a), ii(b), iii(a), iii(b)) work verbatim with the
loosened $\Phi_E^{\sm W}$: the projection arguments still find a witness, the
expansion arguments still get a `length ≥ 1` walk back, and the cycle-excision
pre-processing in sub-claim ii(a)'s `(⟹)` Region~H (L264–332) addresses a
*separate* soundness issue (deletion would leave non-$W$ vertices in the interior)
unrelated to the self-cycle restriction. **Keep the cycle-excision section as-is.**

A side note worth a tiny tweak: sub-claim i's `(⟹)` Region-H paragraph at L184
contains the parenthetical
> "and the self-cycle restriction $u_{c_j} = u_{c_{j+1}} \Rightarrow$ length $\ge 2$ is moot whenever ... and is satisfied otherwise because $\tilde{p}_j$ passes through at least one $W$-vertex in any nontrivial self-return..."

Under the refactor, the self-cycle restriction no longer exists. Replace this
parenthetical with
> "the length-$\ge 1$ requirement is met directly by $c_{j+1} - c_j \ge 1$."

(This is cosmetic — the proof is still correct as-is — but the twin file should
read cleanly.)

**No other tex changes are needed.** Copy the rest of the 549 lines verbatim.

---

## Ordered subtask plan

All `prove_claim_in_lean` workers work in
`/home/11716061/repo_scaffold2/leanification/Chapter3_GraphTheory/Section3_2/MargPreservesAncestors.lean`,
respect the manager.md REFACTOR convention (wrap originals + add refactor_ twin),
and `lake build` from the repo root after each subtask completes.

### Marker convention used throughout
For each helper `X` that we refactor-twin, the original block becomes
```
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: X
<the existing helper, verbatim>
-- REFACTOR-BLOCK-ORIGINAL-END: X
```
and the new block (placed immediately after, with intervening blank line)
```
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: X (was: refactor_X)
<the refactor_ twin>
-- REFACTOR-BLOCK-REPLACEMENT-END: X
```
For the 5 **theorems**, each refactor twin's signature must additionally be
sandwiched by
```
-- claim_3_16 -- start statement
theorem refactor_<name> ... :
    <signature>
-- claim_3_16 -- end statement
  := by
    <proof body>
```
between the `BEGIN`/`END` markers (mirrors the original-block style). The
original's `-- claim_3_16 -- start statement` / `-- claim_3_16 -- end statement`
markers stay where they are inside the ORIGINAL block.

---

### Subtask 1 — wrap originals + refactor_twin foundation helpers
**Worker:** `prove_claim_in_lean.md`
**Inputs:** the file at line ranges
- L238–244 (`mem_of_mem_marginalize`)
- L246–255 (`notW_of_mem_marginalize`)

**Job:**
1. Wrap each of the two helpers with REFACTOR-BLOCK-ORIGINAL markers (use the
   actual Lean names: `mem_of_mem_marginalize`, `notW_of_mem_marginalize`).
2. Immediately after each ORIGINAL block, add a REPLACEMENT block with the
   refactor_ twin. The twin bodies are verbatim copies with the single
   substitution `G.marginalize` → `G.refactor_marginalize` in the
   `(h : v ∈ ...)` argument type. The proof bodies are unchanged (both helpers
   `change` to `G.J ∪ (G.V \ W)`, which is the same for both marginalize
   variants — `J` and `V` fields are unchanged in the refactor).
3. `lake build` from repo root.

**Rationale:** these are pre-requisites for every downstream refactor twin (the
projection/expansion + bifurcation helpers all call them). Tiny, low-risk; gets
the file into "refactor markers present" state.

**Risk:** none. ~10 lines of edits, build should pass first try.

---

### Subtask 2 — refactor_twin the walk-expansion helper
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L286–389 of `MargPreservesAncestors.lean`
(`expand_directed_walk_marginalize` plus its docstring at L286–305).

**Job:**
1. Wrap `expand_directed_walk_marginalize` (the `private lemma` at L312–389) with
   ORIGINAL markers (Lean name: `expand_directed_walk_marginalize`).
2. Add a REPLACEMENT block with `refactor_expand_directed_walk_marginalize`. The
   twin body is the **same proof structure**, modulo these substitutions:
   - Signature: `Walk (G.marginalize W hW) u v` → `Walk (G.refactor_marginalize W hW) u v`.
   - L336: `(u, vMid) ∈ (G.marginalize W hW).E` → `(u, vMid) ∈ (G.refactor_marginalize W hW).E`.
   - L337–339 `ha_filter`: change RHS of the `change` to use
     `(fun e => G.refactor_MarginalizationΦE W e.1 e.2)` (the refactor's filter
     predicate).
   - L340: `G.MarginalizationΦE W u vMid` → `G.refactor_MarginalizationΦE W u vMid`.
   - **L342 destructure**: `⟨q_edge, hq_edge_dir, hq_edge_pos, hq_edge_inter, _⟩`
     → `⟨q_edge, hq_edge_dir, hq_edge_pos, hq_edge_inter⟩` (drop trailing `_`).
   - L324: `mem_of_mem_marginalize hv` → `refactor_mem_of_mem_marginalize hv`.
3. `lake build` from repo root.

**Rationale:** this is the main destructure-site change for the expansion
direction. Every downstream theorem (i `(⟸)`, iii(a), and bifurcation backward)
calls this helper. Self-contained — only depends on Subtask 1 (for
`refactor_mem_of_mem_marginalize`).

**Risk:** the proof body is intricate (induction on `p`, with two complex
`vertices.dropLast` cases). Mechanical fixes only; build catches errors fast.

---

### Subtask 3 — refactor_twin the walk-projection auxiliary
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L470–545 of `MargPreservesAncestors.lean`
(`project_directed_walk_aux` and its wrapper `project_directed_walk_marginalize`).

**Job:**
1. Wrap `project_directed_walk_aux` (the `private lemma` at L477–536) with
   ORIGINAL markers.
2. Wrap `project_directed_walk_marginalize` (L540–545) with ORIGINAL markers.
3. Add REPLACEMENT blocks for both:
   - `refactor_project_directed_walk_aux`: same proof structure. Substitutions:
     - All `v₁, v₂ ∈ G.marginalize W hW` (signature, L482–483) →
       `... ∈ G.refactor_marginalize W hW`.
     - L484 return type `Walk (G.marginalize W hW) v₁ v₂` →
       `Walk (G.refactor_marginalize W hW) v₁ v₂`.
     - L491, L496 `Walk.nil v hv₁` lives in the new marg type — works as-is
       because `hv₁` is in the refactor's carrier `J ∪ (V ∖ W)`, definitionally
       same set.
     - L498 `notW_of_mem_marginalize` → `refactor_notW_of_mem_marginalize`.
     - L505 `m ∈ G.marginalize W hW` → `... ∈ G.refactor_marginalize W hW` (the
       `change m ∈ G.J ∪ (G.V \ W)` works because the V/J fields are unchanged).
     - L523 `(v₁, m) ∈ (G.marginalize W hW).E` →
       `(v₁, m) ∈ (G.refactor_marginalize W hW).E`.
     - L524–525 `change` RHS filter predicate: `MarginalizationΦE` →
       `refactor_MarginalizationΦE`.
     - **L530 construct**: replace
       `refine ⟨head, h_head_dir, h_head_pos, h_head_inter, ?_⟩`
       `intro heq`
       `exact absurd heq hv₁_eq_m`
       with the **single line**
       `exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩`.
     - L533 `(G.marginalize W hW).WalkStep` → `(G.refactor_marginalize W hW).WalkStep`.
     - **Optional simplification (do NOT take):** the `by_cases hv₁_eq_m`
       split at L512 is no longer logically necessary under refactor (the
       self-loop branch L513–520 was a workaround for the old Φ_E's
       `u = v → length ≥ 2` clause). **Keep the case split as-is**; the
       self-loop branch's `subst hv₁_eq_m; exact ⟨q_tail, hq_tail_dir⟩`
       still type-checks under refactor (a marg-walk from `m` to `v₂` is
       trivially a marg-walk from `v₁ = m` to `v₂`), so collapsing the
       case-split is a separate cleanup that's out of refactor scope.
   - `refactor_project_directed_walk_marginalize`: one-line wrapper.
     Substitutions: signature `... ∈ G.marginalize ...` →
     `... ∈ G.refactor_marginalize ...`, body calls
     `refactor_project_directed_walk_aux`.
4. `lake build` from repo root.

**Risk:** medium — the induction proof body is ~60 lines with intricate
case-splits. Build catches most mistakes; if the construct site (L530) is
hand-edited incorrectly, the new Φ_E shape will fail unification quickly.

---

### Subtask 4 — refactor_twin the strong walk-projection helpers
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L547–712 of `MargPreservesAncestors.lean`
(`project_directed_walk_with_vertex_subset_aux` and its wrapper
`project_directed_walk_strong`).

**Job:**
1. Wrap `project_directed_walk_with_vertex_subset_aux` (L556–697) with ORIGINAL
   markers (use Lean name: `project_directed_walk_with_vertex_subset_aux`).
2. Wrap `project_directed_walk_strong` (L702–712) with ORIGINAL markers.
3. Add REPLACEMENT blocks:
   - `refactor_project_directed_walk_with_vertex_subset_aux`: same proof
     structure. Substitutions:
     - Signature `v₁, v₂ ∈ G.marginalize W hW` →
       `v₁, v₂ ∈ G.refactor_marginalize W hW`.
     - Return type `Walk (G.marginalize W hW) v₁ v₂` →
       `Walk (G.refactor_marginalize W hW) v₁ v₂`.
     - L603 `notW_of_mem_marginalize` → `refactor_notW_of_mem_marginalize`.
     - L609 `m ∈ G.marginalize W hW` → `... ∈ G.refactor_marginalize W hW`.
     - L657 `(v₁, m) ∈ (G.marginalize W hW).E` → `... refactor_marginalize ...`.
     - L658–659 `change` RHS filter `MarginalizationΦE` → `refactor_MarginalizationΦE`.
     - **L663–665 construct**: replace
       `refine ⟨head, h_head_dir, h_head_pos, h_head_inter, ?_⟩`
       `intro heq`
       `exact absurd heq hv₁_eq_m`
       with
       `exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩`.
     - L666 `(G.marginalize W hW).WalkStep` → `(G.refactor_marginalize W hW).WalkStep`.
     - **Keep the by_cases hv₁_eq_m split** for the same reason as Subtask 3.
   - `refactor_project_directed_walk_strong`: one-line wrapper.
4. `lake build` from repo root.

**Risk:** the strong-projection proof is ~140 lines with three extra `dropLast` /
`tail` subset conjuncts to preserve through the induction. Same mechanical
substitutions; build will catch issues fast.

---

### Subtask 5 — refactor_twin the directed-bifurcation backward / forward
"thin" helpers (`marg_preserves_bifSource_*`)
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L1704–1854 of `MargPreservesAncestors.lean` (the two
`marg_preserves_bifSource_*` helpers).

**Job:**
1. Wrap each with ORIGINAL markers.
2. Add REPLACEMENT twins:
   - `refactor_marg_preserves_bifSource_forward`: signature substitution
     `G.marginalize` → `G.refactor_marginalize`. Body: replace
     `project_directed_walk_strong` (L1749, L1751) →
     `refactor_project_directed_walk_strong`. Everything else verbatim.
   - `refactor_marg_preserves_bifSource_backward`: signature substitution.
     Body: replace `expand_directed_walk_marginalize` (L1816, L1818) →
     `refactor_expand_directed_walk_marginalize`,
     `notW_of_mem_marginalize` (L1824, L1825, L1826) →
     `refactor_notW_of_mem_marginalize`.
3. `lake build` from repo root.

**Risk:** low. These are dispatchers / arm-extractors over `Walk.mkBifurcation` —
the `Walk.exists_arms_of_bifurcation_directed_hinge_strong` helper they call
operates on `Walk G` and is unchanged.

---

### Subtask 6 — refactor_twin the directed-hinge dispatchers (`marg_bif_*_dir_hinge_*`)
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L1856–1897 of `MargPreservesAncestors.lean`.

**Job:** wrap and refactor-twin `marg_bif_forward_dir_hinge_src_marg` (L1861)
and `marg_bif_backward_dir_hinge` (L1882). Substitutions: `G.marginalize` →
`G.refactor_marginalize` in signatures; internal calls to
`marg_preserves_bifSource_forward` / `_backward` → refactor twins from
Subtask 5; `Walk.mem_of_mem_vertices` is unchanged (operates on the marg-walk's
own carrier, which is the same `Node`). `lake build`.

**Risk:** low (~15-line helpers each).

---

### Subtask 7 — refactor_twin the bidirected-hinge backward helper
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L1899–2321 of `MargPreservesAncestors.lean` (which includes some
pre-requisite walk-algebra lemmas at L1899–1980 that do NOT need twinning, then
the heavy `marg_bif_backward_bidir_hinge` lemma at L1983–2318).

**Job:**
1. Confirm L1899–1980 helpers (`Walk.vertices_getLast`,
   `Walk.tail_getLast_of_pos`, `Walk.length_pos_of_isBifurcation`,
   `Walk.arm_dropLast_in_W`) operate on `Walk G _ _` (NOT on marg-walks) and
   therefore need no twin — leave them unchanged.
2. Wrap `marg_bif_backward_bidir_hinge` (L1983–2318) with ORIGINAL markers.
3. Add REPLACEMENT `refactor_marg_bif_backward_bidir_hinge` with
   substitutions:
   - Signature `G.marginalize` → `G.refactor_marginalize`.
   - L1995–1996: `change` RHS for the L-filter unfold —
     `((G.V \ W) ×ˢ (G.V \ W)).filter (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)`
     — **stays verbatim**, because `refactor_marginalize.L` is bit-identical to
     `marginalize.L`.
   - L2018, L2020: `expand_directed_walk_marginalize` →
     `refactor_expand_directed_walk_marginalize`.
   - L2002, L2003: `notW_of_mem_marginalize` → `refactor_notW_of_mem_marginalize`.
   - Everything else verbatim (the body is ~330 lines of bifurcation arm
     splicing, all on `Walk G`).
4. `lake build`.

**Risk:** highest single-file change in the row. The proof body is large; one
substitution miss in a deep nested term will surface as a `marginalize` /
`refactor_marginalize` mismatch in the build. Run `Grep` for
`G\.marginalize` and `MarginalizationΦL` in the replacement block after
edits to double-check substitutions before building.

---

### Subtask 8 — refactor_twin the bidirected-forward "both not-W" helper
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L2319–2391 (`marg_bif_forward_bidir_both_notW`).

**Job:** wrap + twin. Substitutions:
- Signature `G.marginalize` → `G.refactor_marginalize`.
- L2350, L2352 `hvL_marg`, `hvR_marg` `change` LHS — works without change.
- L2366: `(vL, vR) ∈ (G.marginalize W hW).L` → `... refactor_marginalize ...`,
  the inner `change` filter expression stays verbatim.
- L2373, L2375: `project_directed_walk_strong` →
  `refactor_project_directed_walk_strong`.
- Everything else verbatim.

`lake build`.

**Risk:** low.

---

### Subtask 9 — refactor_twin the bidirected-forward assembler
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L2392–2442 (`marg_bif_forward_assemble_bidirected`).

**Job:** wrap + twin. Substitutions:
- Signature `G.marginalize` → `G.refactor_marginalize`.
- L2415, L2417: `change ... ∈ G.J ∪ (G.V \ W)` — works without change.
- L2419: `(vL_exit, vR_exit) ∈ (G.marginalize W hW).L` → `... refactor_marginalize ...`,
  L-filter `change` RHS unchanged.
- L2426, L2429: `project_directed_walk_strong` →
  `refactor_project_directed_walk_strong`.
- Everything else verbatim.

`lake build`.

**Risk:** low.

---

### Subtask 10 — refactor_twin the forward Case 2 helper
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L2443–2744 (`marg_bif_forward_dir_hinge_src_W`).

**Job:** wrap + twin. Substitutions:
- Signature `G.marginalize` → `G.refactor_marginalize`.
- L2451 `c ∉ G.marginalize W hW` → `c ∉ G.refactor_marginalize W hW`.
- L2460, L2461: `notW_of_mem_marginalize` → `refactor_notW_of_mem_marginalize`.
- Internal `find_first_non_W_directed` calls — operates on `G`, unchanged.
- Internal `marg_bif_forward_assemble_bidirected` call → twin.
- Search for any other `marg_bif_*` calls in the body and switch to twins.
- Search for any remaining `G.marginalize` → `G.refactor_marginalize`.

`lake build`.

**Risk:** medium-high — ~300 lines. Use `Grep` over the new block before
building.

---

### Subtask 11 — refactor_twin the bidirected-forward "finish" helper
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L2745–2970 (`marg_bif_forward_bidir_finish`).

**Job:** wrap + twin. Same recipe: substitute `marginalize` → `refactor_marginalize`
in signatures, `marg_bif_forward_assemble_bidirected` → twin, any other helpers
to their twins. `lake build`.

**Risk:** medium — ~225 lines.

---

### Subtask 12 — refactor_twin the bidirected-forward "with W" helper
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L2971–3113 (`marg_bif_forward_bidir_with_W`).

**Job:** wrap + twin. Internal calls: `find_first_non_W_directed` (unchanged),
`notW_of_mem_marginalize` → twin, `marg_bif_forward_bidir_finish` → twin.
`lake build`.

**Risk:** medium — ~140 lines, three sub-case branches.

---

### Subtask 13 — refactor_twin the two forward / backward dispatchers
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L3114–3150 (`marg_preserves_bif_forward` and
`marg_preserves_bif_backward`).

**Job:** wrap + twin both. Substitutions: `G.marginalize` → `G.refactor_marginalize`
in signatures; internal calls to per-case forward helpers (Case 1 / 2 / 3.A /
3.B leaf helpers) and backward helpers all switch to twins. `lake build`.

**Risk:** low — dispatchers are short.

---

### Subtask 14 — refactor_twin the 5 main theorems
**Worker:** `prove_claim_in_lean.md`
**Inputs:** L3152–3845 (the 5 user-facing theorems).

**Job:**
1. Wrap each of the 5 theorems with ORIGINAL markers (use **actual Lean
   names**, NOT row title):
   - `marginalize_preserves_ancestors` (L3244)
   - `marginalize_preserves_bifurcation` (L3385)
   - `marginalize_preserves_bifurcation_with_source` (L3552)
   - `marginalize_preserves_acyclic` (L3644)
   - `marginalize_restricts_topological_order` (L3805)
2. For each, add a REPLACEMENT block containing the `refactor_<name>` twin.
   Each twin's signature has the `-- claim_3_16 -- start statement` /
   `-- claim_3_16 -- end statement` markers around the signature (above the
   `:= by` body).
3. Substitutions:
   - All `G.marginalize W hW` → `G.refactor_marginalize W hW` in signature
     (membership hypotheses, return-type `.Anc`, `.IsAcyclic`,
     `.IsTopologicalOrder`, `Walk (...)` annotations).
   - In bodies:
     - `marginalize_preserves_ancestors`: `project_directed_walk_marginalize` →
       `refactor_project_directed_walk_marginalize`,
       `expand_directed_walk_marginalize` →
       `refactor_expand_directed_walk_marginalize`,
       `mem_of_mem_marginalize` → `refactor_mem_of_mem_marginalize`.
     - `marginalize_preserves_bifurcation`: `marg_preserves_bif_forward` →
       `refactor_marg_preserves_bif_forward`, `marg_preserves_bif_backward` →
       `refactor_marg_preserves_bif_backward`.
     - `marginalize_preserves_bifurcation_with_source`:
       `marg_preserves_bifSource_forward` → `refactor_*`,
       `marg_preserves_bifSource_backward` → `refactor_*`.
     - `marginalize_preserves_acyclic`: `mem_of_mem_marginalize` → twin,
       `expand_directed_walk_marginalize` → twin.
     - `marginalize_restricts_topological_order`:
       `mem_of_mem_marginalize` → twin (×4 sites).
       **L3836–3837 `change` RHS:** `(fun e => G.MarginalizationΦE W e.1 e.2)` →
       `(fun e => G.refactor_MarginalizationΦE W e.1 e.2)`.
       **L3838 hvw_phi:** `G.MarginalizationΦE W v w` →
       `G.refactor_MarginalizationΦE W v w`.
       **L3840 destructure**: `⟨p, hp_dir, hp_pos, _, _⟩` →
       `⟨p, hp_dir, hp_pos, _⟩` (one fewer underscore).
4. `lake build` from repo root.

**Risk:** the theorem proof bodies are short (mostly dispatchers calling the
already-twinned helpers); the main risk is missing one `marginalize` →
`refactor_marginalize` substitution in a `change` or a `Walk` type annotation.
After edits, `Grep` for `G\.marginalize` (without `refactor_`) inside each
REPLACEMENT block as a sanity check.

---

### Subtask 15 — write the tex twin
**Worker:** `write_tex_proof.md` (or `correct_tex_proof.md`).
**Inputs:**
- Original tex: `tex/claim_3_16_proof_MargPreservesAncestors.tex` (549 lines).
- LN block: claim_3_16 tex block in `refactor_data.json` (or in `graphs.tex`).
- Refactored Lean: the 5 refactor_ twin theorems from Subtask 14.

**Job:**
1. Create `tex/refactor_claim_3_16_proof_MargPreservesAncestors.tex` as a copy
   of the original.
2. Apply the **two targeted edits** described in the "File / line inventory"
   section above:
   - L150 `Φ_E^{∖W}` description: drop the self-cycle restriction clause +
     replace with the LN-footnote-grounded "self-cycles are admitted" sentence.
   - L184 sub-claim i `(⟹)` Region-H parenthetical: replace the self-cycle
     restriction phrasing with the simpler "length-$\ge 1$ requirement is met
     directly" phrasing.
3. Leave every other line untouched (the projection / expansion arguments work
   verbatim under the looser Φ_E^{∖W}).
4. Verify the twin compiles with `pdflatex` if the section's `main.tex` is set up
   (likely a Phase 7 concern; do not block here).

**Risk:** very low — tex edits are surgical.

---

### Subtask 16 — refactor-twin coverage check (final-gate)
**Worker:** `verify_row_solved.md` (or a manual sanity Grep pass).
**Inputs:** post-Subtask-15 state of
`leanification/Chapter3_GraphTheory/Section3_2/MargPreservesAncestors.lean`.

**Job:**
1. `Grep` for `G\.marginalize` (no `refactor_` prefix) across the file: every
   match should be inside a REFACTOR-BLOCK-ORIGINAL block (the originals are
   intentionally preserved until Phase 7 cleanup).
2. `Grep` for `refactor_` over the file: every match should be inside a
   REPLACEMENT block OR a call site inside another REPLACEMENT block. (No stray
   top-level `refactor_*` declarations outside a REPLACEMENT marker pair —
   the cleanup script refuses on those.)
3. `lake build` once more from the repo root.
4. Report file size, count of REPLACEMENT blocks added (~7 helpers + ~12
   bifurcation helpers + 5 theorems = ~24), and any leftover
   `MarginalizationΦE` references that didn't get a `refactor_` prefix.

**Risk:** trivial. Catches any silent omissions.

---

## Risk callouts (consolidated)

1. **Foundational helpers used everywhere.** The 7 projection/expansion helpers
   (Subtasks 1–4) are called by ALL the bifurcation helpers (Subtasks 5–13)
   and by 4 of the 5 main theorems (Subtask 14). A single typo at this layer
   cascades. Mitigation: do Subtasks 1–4 sequentially with `lake build` between
   each — a build error stays local.
2. **The bifurcation backward / forward bidir helpers are large (Subtasks 7,
   10, 11) — 150–330 lines each.** Mitigation: split each into its own subtask
   (already done in this plan); use Grep-over-the-new-block to spot stray
   `G.marginalize` references before building.
3. **L-channel unchanged but L-filter expressions are textually verbatim.**
   The bifurcation helpers' `change` RHS for the `L`-membership unfolds spell
   out `((G.V \ W) ×ˢ (G.V \ W)).filter (fun e => e.1 ≠ e.2 ∧
   G.MarginalizationΦL W e.1 e.2)`. Under refactor, the LHS still says
   `(G.refactor_marginalize W hW).L`, and `refactor_marginalize.L` is bit-for-bit
   identical to `marginalize.L` — so the `change` lands the same as before. Do
   NOT replace `MarginalizationΦL` with `refactor_MarginalizationΦL` (no such
   thing exists; `Φ_L` was not refactored).
4. **The `by_cases hv₁_eq_m` self-loop branches in
   `project_directed_walk_aux` and `project_directed_walk_with_vertex_subset_aux`
   become logically redundant.** Do NOT collapse them in the refactor twin;
   keeping the split makes the diff minimal and the proof structure parallel.
   Cleanup is a follow-up concern out of scope for `marginalize_loose_self_cycle`.
5. **The tex twin's cycle-excision section (Region H pre-processing,
   L264–332) stays.** It addresses a separate soundness issue and is still
   needed under refactor.

## Net-new declarations
None expected. Every refactor twin in this row replaces an existing helper
or theorem. The plan does not introduce any `refactor_*` declaration without
an ORIGINAL counterpart, so the manager.md "REPLACEMENT-only marker" guidance
(net-new helpers) does not apply here.

## Build-check cadence
After every subtask, run from repo root:
```
lake build 2>&1 | tail -50
```
A failing `lake build` after a subtask means **stop and inspect** before moving
on; the next subtask's twin will depend on the previous one's symbols.

## Suggested dispatch order
1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 — strictly sequential.
Subtasks 5–13 (bifurcation helpers) could in principle be parallelised after
Subtasks 1–4 finish, since they are independent leaves of the dependency tree,
but parallelising adds merge-conflict risk on the same file and is **not
recommended** here. One worker, one subtask, one `lake build`, repeat.
