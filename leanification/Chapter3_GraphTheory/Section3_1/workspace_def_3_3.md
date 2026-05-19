# Workspace for def_3_3 — EdgeRelations

## What this row is

A **pure terminology** definition (`\begin{Def}` block, no `[Title]`) following
def_3_2 (CDMGNotation). It does *not* introduce new graph structure — it just
gives semantic names to combinations of the primitive `\tuh`/`\hut`/`\huh`
edge notations:

| LN concept                            | LN expansion                              | Already-defined in def_3_2     |
|---------------------------------------|-------------------------------------------|---------------------------------|
| $v_1$ and $v_2$ *adjacent*            | $v_1 \sus v_2 \in G$                      | `sus G v₁ v₂` / `v₁ ↮[G] v₂`   |
| edge *into $v_1$* (between $v_1,v_2$) | $v_1 \hut v_2$ or $v_1 \huh v_2$          | `hus G v₁ v₂` / `v₁ ⇷[G] v₂`   |
| edge *into $v_2$* (between $v_1,v_2$) | $v_1 \tuh v_2$ or $v_1 \huh v_2$          | `suh G v₁ v₂` / `v₁ ⇸[G] v₂`   |
| edge *out of $v_1$* (between $v_1,v_2$) | $v_1 \tuh v_2$ or $v_2 \hut v_1$        | `tuh G v₁ v₂` / `v₁ ⟶[G] v₂`   |

So item 3 ("out of $v_1$") presents the *same* condition twice in two
equivalent notations — $v_1 \tuh v_2$ and $v_2 \hut v_1$ both unfold to
$(v_1, v_2) \in E$. The LN is teaching the reader that the same edge can be
spelled either way. In Lean this collapses to `tuh G v₁ v₂` (which equals
`hut G v₂ v₁` by definition).

Notably, "out of $v_1$" excludes the bidirected case $v_1 \huh v_2$ — a
bidirected edge has arrowheads at *both* endpoints, so it's "into" both
endpoints but "out of" neither. That asymmetry between items 2 and 3 is
intentional and load-bearing for downstream chapters (causal directionality).

## Plan

1. `formalize_definition_in_lean` → write `Section3_1/EdgeRelations.lean`.
   - Three new named predicates: `Adjacent`, `EdgeInto`, `EdgeOutOf`.
   - Each defined as a literal re-spelling of the def_3_2 underlying form,
     so they're definitionally equal — the role of the new names is to
     match LN prose phrasing ("$v$ is adjacent to $w$", "an edge into $v$",
     "the edge out of $v$").
   - Tag with `@[simp]` characterisation lemmas so users can rewrite freely
     between the semantic name and the underlying `sus` / `hus` / `suh` /
     `tuh`.
   - No new notation tokens — the def_3_2 arrow notations already cover the
     formal phrasings the LN uses. The new names are for prose only.
2. `review_design` — full-LN-context check (does the shape compose with
   def_3_4 Walks "into/out of $v_0$", def_3_5 family relationships, etc.).
3. `verify_equivalence` — focused LN-block-vs-Lean check.
4. `solved` → `verify_row_solved`.

## Notes for downstream rows

- def_3_4 (Walks) uses *exactly the same phrases* "into $v_0$" / "out of
  $v_0$" but lifted to walks (via the first/last edge). The names chosen
  here should compose: `WalkInto G w v` ↔ "first edge of `w` is `EdgeInto`
  the start vertex `v`". So picking `EdgeInto`/`EdgeOutOf` as the *predicate
  on a pair of vertices* (not on an `Edge` object — we don't have one)
  is the shape that lets def_3_4 read cleanly.
- claim_3_1 (JNodeProperties) uses `hus` directly (`j \hus v \notin G`) and
  the word "adjacent" in prose ("no two nodes in $J$ are adjacent"). So
  `Adjacent` will be cited there.
- The convention this row sets: **in Lean, semantic names like `Adjacent`,
  `EdgeInto`, `EdgeOutOf` are introduced for prose-readability; the
  underlying machine-level reasoning uses the def_3_2 notations directly.**

## Delivered (2026-05-19)

`Section3_1/EdgeRelations.lean` — all in `namespace Causality.CDMG`:

| Declaration                                       | Kind       | Unfolds to            |
|---------------------------------------------------|------------|-----------------------|
| `Adjacent (G : CDMG α) (v₁ v₂ : α) : Prop`        | `def`      | `sus G v₁ v₂`         |
| `EdgeInto (G : CDMG α) (v₁ v₂ : α) : Prop`        | `def`      | `hus G v₁ v₂`         |
| `EdgeOutOf (G : CDMG α) (v₁ v₂ : α) : Prop`       | `def`      | `tuh G v₁ v₂`         |
| `adjacent_iff`                                    | `@[simp]`  | `Iff.rfl`             |
| `edgeInto_iff`                                    | `@[simp]`  | `Iff.rfl`             |
| `edgeOutOf_iff`                                   | `@[simp]`  | `Iff.rfl`             |
| `edgeOutOf_iff_hut : EdgeOutOf G v₁ v₂ ↔ hut G v₂ v₁` | `theorem`  | `Iff.rfl` (LN's alternative spelling) |
| `Adjacent.symm`                                   | `theorem`  | proved by 3-case `rcases`; bidirected case uses `G.L_symm` |

Notes for downstream callers:
- `Adjacent.symm` is the *only* non-trivial proof in this file; cite it (or
  `h.symm`) instead of unfolding to `sus` and re-doing the case split.
- The three `_iff` simp lemmas are *upward* unfoldings (prose → underlying).
  If you want to push the other way, `rw [← adjacent_iff]` etc. or just
  `unfold Adjacent`.
- `EdgeOutOf` does **not** include the bidirected case (`huh`). If a
  downstream row needs "any edge with `v₁` as tail OR a bidirected edge",
  build a new disjunction — don't try to redefine `EdgeOutOf`.
