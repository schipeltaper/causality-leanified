import Chapter3_GraphTheory.Section3_1.CDMG

namespace Causality

/-!
# Node-splitting on CDMGs (`def_3_11`)

This file formalises the LN definition `def_3_11`
(`\label{def:G_node-splitting}` in `graphs.tex`) — the *node-splitting*
operation `G ↦ G_{\spl(W)}` on a CDMG.  Given a CDMG
`G = (J, V, E, L)` and a subset `W ⊆ V` of output nodes, the
node-split graph has

* `J_{\spl(W)} := J` (input nodes unchanged);
* `V_{\spl(W)} := (V ∖ W) ⊍ W^0 ⊍ W^1` (each `w ∈ W` replaced by
  two tagged copies `w^0`, `w^1`);
* `E_{\spl(W)} := { (v_1^1, v_2^0) | (v_1, v_2) ∈ E } ∪
                   { (w^0, w^1) | w ∈ W }`
  (every directed edge of `G` is lifted to point from the `^1`-copy
  of its source to the `^0`-copy of its target, plus a *transfer
  edge* `w^0 → w^1` for every `w ∈ W`);
* `L_{\spl(W)} := { (v_1^0, v_2^0) | (v_1, v_2) ∈ L }` (every
  bidirected edge of `G` is lifted with **both** endpoints carrying
  the `^0` superscript — no element of `W^1` appears as the endpoint
  of any bidirected edge).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_11_NodeSplittingOn.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_node-splitting}`) augmented with the operator
clarification
`[disjointness_of_new_copies_only_partially_stipulated]`:
the disjointness assertions
`W^0 ∩ V = W^1 ∩ V = W^0 ∩ J = W^1 ∩ J = W^0 ∩ W^1 = ∅`
are realised **at the type level** — `W^0` and `W^1` are constructed
as *tagged copies* (here via an `inductive` `SplitNode Node` with
distinct constructors), so disjointness is a *typing* fact rather
than a side condition.

The substantive design rationale — the choice of an `inductive`
`SplitNode` over a `Sum`-based encoding, the encoding of the
`v^0 := v^1 := v` notational shorthand as helper functions
`toCopy0` / `toCopy1`, the literal `Finset.image`-based set-builders
for `E_{\spl(W)}` and `L_{\spl(W)}`, and how each CDMG axiom of
`def_3_1` is discharged on the tagged-sum carrier — lives in the
`--` comment block immediately above the `def` declaration.  Read
that block before changing a field; it is the load-bearing contract
for downstream chapter-3 rows that compose node-splitting with hard
intervention (`def_3_12` SWIG) or that reason about topological
orders on the split graph (`claim_3_6` SplitTopologicalOrder).
-/

namespace CDMG


end CDMG

namespace CDMG

-- def_3_11 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_11 --- end helper

-- ## Helper: the tagged-sum node universe of the split graph
--
-- *One-sentence summary.*  The carrier of the node-split graph:
-- a tagged-sum `Type*` whose three constructors `.unsplit`,
-- `.copy0`, `.copy1` realise the LN's three node-kinds
-- (`J ∪ (V \ W)`, `W^0`, `W^1`) as type-level disjoint inhabitants
-- of a single Lean type.
--
-- This is the post-refactor port of `SplitNode` for the
-- `cdmg_typed_edges` design (`def_3_1` shape:
-- `L : Finset (Sym2 Node)`, no `hL_symm` axiom).  The inductive
-- carrier itself is *structurally unchanged* from the pre-refactor
-- encoding: `SplitNode Node` references neither `L`'s typing nor any
-- field of `CDMG` / `CDMG` — it is a pure construction on
-- the ambient `Node` type — so the three named constructors and the
-- `deriving DecidableEq` carry over verbatim, only the namespace
-- changes.
--
-- *Driver from `addition_to_the_LN`.*  Addition
-- `[disjointness_of_new_copies_only_partially_stipulated]` is the
-- load-bearing spec for this carrier: it requires that the LN's
-- five disjointness assertions
-- `W^0 ∩ V = W^1 ∩ V = W^0 ∩ J = W^1 ∩ J = W^0 ∩ W^1 = ∅` be
-- realised *at the type level* — via a `Σ`-type or tagged sum —
-- rather than as side conditions on a single-sort encoding.
-- `SplitNode` discharges this by being a fresh
-- `inductive` whose three constructors are tag-distinct by
-- construction, making each of the five LN intersections vacuous
-- (`unsplit v = copy0 w` is structurally impossible, etc.).  The
-- addition also clarifies that the LN's `v^0 := v^1 := v` for
-- `v ∈ J ∪ (V \ W)` is *purely notational shorthand* that does
-- *not* reassign such `v` to either tagged-copy carrier; the
-- third constructor `.unsplit` realises this by keeping
-- untagged nodes in their *own* lane of the same Lean type
-- (rather than embedding them via `.copy0` or `.copy1`).  This is
-- the addition-driven design choice that fixes the three-
-- constructor shape over a two-constructor `Sum`-of-tagged-copies
-- alternative.
--
-- *`inductive` with three named constructors, not `Sum Node (Node ×
--   Bool)` or `Σ b : Fin 2, Node` or `Sum (V \ W) (W × Fin 2)`.*
--   The LN's "two tagged copies `W^0`, `W^1` plus the unsplit
--   nodes" reads as three distinguishable kinds of element; the
--   named constructors `unsplit`, `copy0`, `copy1` mirror the LN
--   symbols `v`, `w^0`, `w^1` one-for-one and let downstream
--   pattern matches read `| .unsplit v => …` / `| .copy0 w => …` /
--   `| .copy1 w => …` instead of nested `Sum.inl` / `Sum.inr`
--   destructuring.  Three alternatives considered:
--
--   - **`Sum Node (Node × Bool)`** (`Sum.inl v` for unsplit,
--     `Sum.inr (w, false)` for `w^0`, `Sum.inr (w, true)` for
--     `w^1`) was the workspace's expected fallback; we picked the
--     named-constructor form because it is identical in
--     expressive power, shorter at every use site, and matches
--     the LN notation without a translation table.
--   - **`Σ b : Fin 2, Node`** (a dependent pair indexing the
--     "copy bit" by `Fin 2`) was rejected because it cannot
--     express the *third* kind (the unsplit nodes) without a
--     coproduct wrapper — yielding `Sum Node (Σ b : Fin 2, Node)`,
--     which is even less direct than `Sum Node (Node × Bool)`.
--   - **`Sum (V \ W) (W × Fin 2)`** (encoding membership in `W`
--     in the type itself) was rejected because (i) it makes the
--     carrier depend on `G.V` and `W`, so a single
--     `SplitNode Node` cannot be re-used across different
--     graphs / different `W`-subsets, and (ii) `DecidableEq` on a
--     subtype requires decidability of the underlying predicate,
--     adding instance bookkeeping at every use site.
--
-- *`deriving DecidableEq`.*  `def_3_1`'s post-refactor
--   `CDMG` carrier requires `[DecidableEq Node]`; the split
--   graph lives over `SplitNode Node`, so we need
--   `[DecidableEq (SplitNode Node)]` to satisfy
--   `CDMG (SplitNode Node)`.  This is also what
--   makes `Sym2 (SplitNode Node)` decidably-comparable
--   (Mathlib's derived instance lifts `DecidableEq` through `Sym2`),
--   which the `L`-side `Finset.image (Sym2.map …)` construction
--   below relies on.  The `deriving` handler generates the instance
--   `[DecidableEq Node] → DecidableEq (SplitNode Node)` for
--   free.
--
-- *No membership predicates on `W` or proofs `hv : v ∉ W` /
--   `hw : w ∈ W` baked into the constructors.*  A richer
--   `inductive SplitNode (Node : Type*) (W : Set Node)`
--   carrying per-constructor membership proofs would force every
--   consumer to manipulate those proofs through every pattern match
--   (and would make `DecidableEq` non-trivial because the proof
--   argument has `Prop` type with `Eq` undecidable in general).
--   Disjointness of the three constructors is structural; whether a
--   `copy0 w` is "valid" (i.e.\ `w ∈ W`) is then enforced by the
--   *`Finset`* level of `J_{\spl(W)}` / `V_{\spl(W)}` membership
--   rather than by the *type* itself.  This matches the LN reading:
--   `W^0` is a `Finset` inside the carrier `SplitNode
--   Node`, not a separate type.
-- def_3_11 --- start helper
inductive SplitNode (Node : Type*) where
  | unsplit (v : Node) : SplitNode Node
  | copy0 (w : Node) : SplitNode Node
  | copy1 (w : Node) : SplitNode Node
  deriving DecidableEq
-- def_3_11 --- end helper

-- ## Helper: the `v^0` notational shorthand
--
-- *One-sentence summary.*  The Lean rendering of the LN's `v^0`
-- shorthand: a function `Node → SplitNode Node` that
-- branches on `v ∈ W` and returns either the `.copy0` tagged
-- copy or the `.unsplit` lift, used to lift directed-edge targets
-- and *both* endpoints of bidirected edges into the split graph.
--
-- *Driver from `addition_to_the_LN`.*  Addition
-- `[disjointness_of_new_copies_only_partially_stipulated]`
-- explicitly clarifies the LN's convention `v^0 := v^1 := v` for
-- `v ∈ J ∪ (V \ W)` as *purely notational shorthand* used inside
-- the `E_{\spl(W)}` / `L_{\spl(W)}` set-builders; it "does not
-- reassign these elements to the tagged copy types".  The Lean
-- function `toCopy0 W` realises this reading literally:
-- on the `W`-branch it returns the *tagged* `.copy0 v`, on the
-- complement (`v ∈ J ∪ (V \ W)`) it returns the *untagged*
-- `.unsplit v` — keeping `v` in the ambient lane of
-- `SplitNode Node`, not re-routing it through a `.copy0`
-- tag.  This is the addition-driven design choice that fixes the
-- `.unsplit`-on-the-complement branch over a hypothetical
-- `.copy0`-on-the-complement variant.
--
-- *Function `Node → SplitNode Node`, parameterised by
--   `W : Finset Node`.*  The LN convention is `v^0 := v` if
--   `v ∈ J ∪ (V ∖ W)` and `v^0 := (the tagged copy of v in W^0)` if
--   `v ∈ W`.  In Lean this is a single function: branch on `v ∈ W`
--   (decidable from `[DecidableEq Node]` on `Finset Node`), return
--   the tagged constructor on the `W`-branch and the unsplit
--   injection on the complement.  Encoding this as a *function*
--   (rather than as two separate cases inside every set-builder)
--   directly mirrors the LN's "notational shorthand" framing and
--   keeps the `E_{\spl(W)}` / `L_{\spl(W)}` definitions terse and
--   uniform.  Unchanged from the pre-refactor encoding, only the
--   namespace prefix changes.
--
-- *Why no `v ∈ W`-precondition subtype argument.*  An alternative
--   `toCopy0 (v : Node) (hv : v ∈ W) : SplitNode
--   Node := .copy0 v` would have made the function partial — only
--   defined on `W`-elements — and would have forced every caller
--   (the `E'` / `L'` set-builders) to first prove membership
--   `e.2 ∈ W` before lifting.  We picked the total, branching form
--   because (i) the LN treats the shorthand `v^0` as defined on
--   *all* of `J ∪ V` (not just `W`), and (ii) keeping the function
--   total makes `Sym2.map (toCopy0 W)` (the `L`-side lift)
--   type-check without an outer `Sym2.attach`-style subtype dance.
--
-- *Total on all of `Node`, not partial.*  The function is defined on
--   *every* `v : Node`, including `v ∈ G.J` and `v ∈ G.V ∖ W`.  At
--   those `v`-values the function returns `.unsplit v`, exactly the
--   LN's "`v^0 := v`" convention — extended literally to the entire
--   ambient `Node` type so the function has a single uniform
--   signature.  Restricting to a subtype was rejected as gratuitous
--   typing noise: every set-builder in `E_{\spl(W)}` / `L_{\spl(W)}`
--   ranges over pairs coming from `G.E` / `G.L`, whose endpoints
--   already satisfy the subtype condition by `def_3_1`'s typing
--   axioms.  In the `L`-side construction below this matters: we
--   lift via `Sym2.map (toCopy0 W)`, and `Sym2.map`
--   requires a *total* function on the underlying carrier.
-- def_3_11 --- start helper
def toCopy0 (W : Finset Node) (v : Node) : SplitNode Node :=
  if v ∈ W then SplitNode.copy0 v else SplitNode.unsplit v
-- def_3_11 --- end helper

-- ## Helper: the `v^1` notational shorthand
--
-- Same shape as `toCopy0` above, returning
-- `SplitNode.copy1 v` on the `W`-branch instead of
-- `SplitNode.copy0 v`.  See the design block above
-- `toCopy0` for the rationale; the two helpers differ only
-- in which tagged copy they pick on the `W`-branch.  Unchanged from
-- the pre-refactor encoding except for the namespace prefix.
-- def_3_11 --- start helper
def toCopy1 (W : Finset Node) (v : Node) : SplitNode Node :=
  if v ∈ W then SplitNode.copy1 v else SplitNode.unsplit v
-- def_3_11 --- end helper

-- ## Helper: injectivity of `toCopy0 W` on `Node`
--
-- *One-sentence summary.*  A private structural lemma: the
-- `toCopy0 W` function is injective on `Node`, used by
-- `nodeSplittingOn_hL_irrefl` to lift `G.hL_irrefl`'s
-- conclusion through `Sym2.isDiag_map` in the post-refactor
-- `cdmg_typed_edges` setting.
--
-- *Why a standalone private helper, not inlined into
-- `hL_irrefl`?*  Mathlib's `Sym2.isDiag_map` has the form
-- `Function.Injective f → ((Sym2.map f s).IsDiag ↔ s.IsDiag)` —
-- it requires its function argument to come paired with a bare
-- injectivity premise.  Extracting `toCopy0_inj` as a
-- standalone lemma (i) lets it be cited once via the thunk
-- `(fun _ _ => toCopy0_inj)` at the `hL_irrefl` call
-- site without a four-case `by_cases` inline, and (ii) keeps it
-- available for any future row that lifts via
-- `Sym2.map (toCopy0 W)` (anticipated in
-- `claim_3_22`-style σ-separation-symmetry arguments downstream).
--
-- *Proof strategy.*  Case-analysis on `a ∈ W`, `b ∈ W`: the two
-- cross-cases (`a ∈ W, b ∉ W` and `a ∉ W, b ∈ W`) close
-- structurally by constructor mismatch (`.copy0` vs `.unsplit`
-- are distinct inductive constructors); the two matched cases
-- close by constructor injectivity (`.copy0 a = .copy0 b →
-- a = b` and `.unsplit a = .unsplit b → a = b`).  Unchanged from
-- the pre-refactor `toCopy0_inj`; only the namespace prefix
-- changes.
--
-- *No analogous `refactor_toCopy1_inj` is defined.*  The `L`-side
-- (the only consumer of `Sym2.isDiag_map`-style reasoning in
-- this row) only lifts via `toCopy0` — by the LN's
-- one-sided convention `L_{\spl(W)} := \{(v_1^0, v_2^0) \st …\}`
-- (cf. wording-check subtlety `spl_L_attached_to_W0_only_silently`
-- and the rewritten tex's "Asymmetry between directed and
-- bidirected edges at `W^0` vs. `W^1`" paragraph), so no
-- `toCopy1`-injectivity result is needed here.  The
-- `E`-side uses `toCopy1` on the source of every lifted
-- directed edge, but `hE_subset`'s typing-only obligation never
-- requires injectivity of the source lift — only membership of
-- the produced node in the right Finset image, which routes
-- through `Finset.mem_image` rather than through `Sym2.isDiag_map`.
private lemma toCopy0_inj {W : Finset Node} {a b : Node}
    (h : toCopy0 W a = toCopy0 W b) : a = b := by
  unfold toCopy0 at h
  by_cases hWa : a ∈ W
  · by_cases hWb : b ∈ W
    · rw [if_pos hWa, if_pos hWb] at h
      injection h
    · rw [if_pos hWa, if_neg hWb] at h
      cases h
  · by_cases hWb : b ∈ W
    · rw [if_neg hWa, if_pos hWb] at h
      cases h
    · rw [if_neg hWa, if_neg hWb] at h
      injection h

-- ref: def_3_11
--
-- The *node-splitting on `G` with respect to `W`* is the
-- `CDMG` `G.nodeSplittingOn W hW` over the carrier
-- `SplitNode Node` whose four components are
--
--   * `J' := G.J.image .unsplit`                       — input nodes
--     unchanged, lifted into `SplitNode Node` via the
--     `unsplit` constructor;
--   * `V' := (G.V \ W).image .unsplit ∪
--             W.image .copy0 ∪ W.image .copy1`         — output
--     nodes partition into the unsplit part `V \ W` (still injected
--     via `unsplit`) and the two tagged copies `W^0`, `W^1`;
--   * `E' := G.E.image (fun e => (toCopy1 W e.1,
--             toCopy0 W e.2)) ∪
--             W.image (fun w => (.copy0 w, .copy1 w))` — every
--     directed edge `v_1 → v_2 ∈ G.E` is lifted with `v_1^1` on the
--     source and `v_2^0` on the target; the transfer edges
--     `w^0 → w^1` for `w ∈ W` are added in a separate clause;
--   * `L' := G.L.image (Sym2.map (toCopy0 W))` — every
--     bidirected (unordered) edge `s(v_1, v_2) ∈ G.L` is lifted
--     pointwise on both endpoints via `toCopy0 W`, so both
--     endpoints carry the `^0` superscript.  No element of `W^1`
--     ever appears in `L'`.
--
-- The hypothesis `hW : W ⊆ G.V` is the LN's "$W \subseteq V$"
-- precondition.
--
-- This declaration is the post-refactor port of `def_3_11` against
-- the `cdmg_typed_edges` design (`def_3_1` shape:
-- `L : Finset (Sym2 Node)`, no `hL_symm` axiom).  The `L`-side
-- construction now lifts each *unordered* edge `s ∈ G.L` via
-- `Sym2.map (toCopy0 W)`; under the `Sym2` typing this is
-- the literal, structural reading of the LN's item iv set-builder
-- (no two-endpoints destructure, no `hL_symm`-driven sym-axiom
-- preservation, no need to manually commute over the swap), and it
-- preserves the LN-faithful asymmetric `^0`-only convention by
-- construction.
/-
LN tex (rewritten `def_3_11_NodeSplittingOn`, items i–iv):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq V$ a subset of
    output nodes.  The node-split graph w.r.t. $W$ is the CDMG
    $G_{\spl(W)} := (J_{\spl(W)}, V_{\spl(W)}, E_{\spl(W)},
                      L_{\spl(W)})$,
    where (using the tagged copies $W^0 := \{w^0 \mid w \in W\}$,
    $W^1 := \{w^1 \mid w \in W\}$ realised at the type level, and the
    convention $v^0 := v^1 := v$ for $v \in J \cup (V \setminus W)$
    as notational shorthand inside the set-builders below):
      i.   $J_{\spl(W)} := J$;
      ii.  $V_{\spl(W)} := (V \setminus W) \dcup W^0 \dcup W^1$;
      iii. $E_{\spl(W)} := \{ (v_1^1, v_2^0) \mid (v_1, v_2) \in E \}
                         \cup \{ (w^0, w^1) \mid w \in W \}$;
      iv.  $L_{\spl(W)} := \{ (v_1^0, v_2^0) \mid (v_1, v_2) \in L \}$.

LN block (verbatim, for backup):

    Let $G=(J,V,E,L)$ be a CDMG and $W \subseteq V$ a subset of the
    output nodes.  The node-split graph w.r.t. $W$ of $G$ is the
    CDMG $G_{\spl(W)} := (J_{\spl(W)}, V_{\spl(W)}, E_{\spl(W)},
    L_{\spl(W)})$, constructed as follows.  We first make two
    disjoint copies of the nodes in $W$: $W^0 := \{w^0 \mid w \in W\}$,
    $W^1 := \{w^1 \mid w \in W\}$.  Note that we consider
    $w^0 \neq w^1$ for $w \in W$.  Additionally (for convenience), for
    $v \in J \cup V \setminus W$ we put $v^0 := v^1 := v$.  We then
    define:
      i.   $J_{\spl(W)} := J$,
      ii.  $V_{\spl(W)} := (V \setminus W) \dcup W^0 \dcup W^1$,
      iii. $E_{\spl(W)} := \{ v_1^1 \to v_2^0 \mid v_1 \to v_2 \in E \}
                         \cup \{ w^0 \to w^1 \mid w \in W \}$,
      iv.  $L_{\spl(W)} := \{ v_1^0 \leftrightarrow v_2^0
                              \mid v_1 \leftrightarrow v_2 \in L \}$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **Post-refactor port — `L : Finset (Sym2 (SplitNode
--   Node))`.**  The only field whose Lean *shape* changes versus the
--   pre-refactor encoding is `L_{\spl(W)}`.  Pre-refactor:
--     `L := G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))`
--   over `Finset (Node × Node)`, requiring a separate `hL_symm`
--   proof obligation that explicitly swaps the underlying pair and
--   re-routes it through `G.hL_symm`.  Post-refactor:
--     `L := G.L.image (Sym2.map (toCopy0 W))`
--   over `Finset (Sym2 (SplitNode Node))`.  Under the
--   `Sym2` typing the obligation reduces by *three* structural
--   simplifications:
--
--   - **No two-endpoints destructure.**  `Sym2.map` lifts the
--     unordered-pair structure pointwise.  The pre-refactor
--     `fun e => (toCopy0 W e.1, toCopy0 W e.2)` had to project to
--     each ordered component separately; `Sym2.map (toCopy0
--     W)` does the same job in a single closed form.  Membership
--     reasoning at L-manipulation sites uses `Sym2.mem_map`
--     (`v ∈ Sym2.map f s ↔ ∃ w ∈ s, f w = v`), so every endpoint of
--     every lifted edge is reached via a single bounded existential.
--
--   - **No `hL_symm` obligation.**  The pre-refactor encoding had to
--     prove `(v_2, v_1) ∈ L'` whenever `(v_1, v_2) ∈ L'` (a fifth
--     proof obligation on the structure literal), routing through
--     `G.hL_symm`.  Under `Sym2`, `s(v_1, v_2) = s(v_2, v_1)` is
--     *definitional*, so the entire obligation goes away
--     structurally — exactly the same simplification `def_3_10`
--     (HardInterventionOn) sees, paying off the
--     `cdmg_typed_edges` refactor's central design commitment.
--
--   - **The `^0`-only-on-`L` convention is preserved structurally.**
--     `Sym2.map (toCopy0 W)` of an edge `s(w_1, w_2) ∈ G.L`
--     with `w_1, w_2 ∈ W` lands on `s(.copy0 w_1, .copy0 w_2)` —
--     never on `.copy1 w_1` or `.copy1 w_2`, nor on a mixed
--     `s(.copy0 w_1, .copy1 w_2)`.  This is the load-bearing LN-
--     faithful asymmetric convention flagged by wording-check
--     subtlety `spl_L_attached_to_W0_only_silently`: bidirected
--     edges live on `W^0` only, and the structural construction
--     enforces it without any side-condition.  Downstream SWIG
--     semantics (`def_3_12`, etc.) rests on exactly this: each
--     `w^0`-copy represents the *natural* / observational side of
--     `w` (on which latent confounding is inherited from `G`), while
--     each `w^1`-copy represents the *intervened* / `do`-side
--     (causally isolated from latent confounding by design).
--
--   This is the *primary* downstream payoff of the
--   `cdmg_typed_edges` refactor at the `def_3_11` row.  Compare with
--   `def_3_10`'s REPLACEMENT block above (the load-bearing
--   "structurally resolved deviation" reasoning is identical in
--   spirit, though the pre-refactor `def_3_10` had a *registered
--   content deviation* `hard_intervention_l_symmetrized_removal`
--   in `deviations.json` while `def_3_11`'s pre-refactor `^0`-only
--   convention was already structurally LN-faithful — the
--   `Sym2.image (Sym2.map …)` lift now expresses that convention in
--   a single closed-form clause without manual pair-destructuring).
--
-- * **`def`, not `structure` / `inductive` / `class`.**  Node
--   splitting is a *function* `CDMG Node → Finset Node →
--   … → CDMG (SplitNode Node)`, not new data and
--   not a typeclass-resolvable property.  The CDMG already has its
--   `structure` (`def_3_1`); this row produces a new CDMG over the
--   tagged-sum carrier `SplitNode Node` from an existing
--   one.  Wrapping the result in a fresh structure (e.g. a
--   `NodeSplittingOn` record carrying the split graph as a field)
--   was rejected because every downstream consumer (SWIG `def_3_12`,
--   `claim_3_6` SplitTopologicalOrder, `claim_3_12`
--   HardInterventionNodeSplit) destructures the split graph the same
--   way any other CDMG is destructured — via
--   `(G.nodeSplittingOn W hW).J`, `…V`, `…E`, `…L` — and an
--   extra wrapping layer would force a re-destructuring step at
--   every such call site.  Mirrors the sibling `def_3_10`
--   (`hardInterventionOn`).
--
-- * **Carrier of the result is `SplitNode Node`, NOT
--   `Node`.**  This is the load-bearing departure from `def_3_10`:
--   hard intervention keeps the same node universe (`Finset Node`
--   operations on `J ∪ W` / `V \ W`), whereas node splitting
--   *creates new nodes* (`w^0`, `w^1`) that must be type-level
--   distinct from the original `Node` and from each other.  The
--   `addition_to_the_LN`
--   `[disjointness_of_new_copies_only_partially_stipulated]` fixes
--   the semantics: disjointness is at the *type level*, encoded via
--   an `inductive` `SplitNode` with three named
--   constructors so the LN's
--   `W^0 ∩ V = W^1 ∩ V = W^0 ∩ J = W^1 ∩ J = W^0 ∩ W^1 = ∅`
--   becomes a typing fact, not a `Disjoint` proof obligation.
--   Downstream consumers see the carrier change in the return type
--   `CDMG (SplitNode Node)` and pattern-match on
--   `.unsplit` / `.copy0` / `.copy1` as needed (or, when the
--   unsplit-only branch suffices, project through the `unsplit`
--   constructor).
--
-- * **`hW : W ⊆ G.V` is an explicit argument, not a sub-condition
--   threaded through the body.**  The LN's "Let $W \subseteq V$" is
--   part of the *signature* of node splitting.  In contrast with
--   `def_3_10`'s `W ⊆ G.J ∪ G.V` (which permits `W ∩ G.J ≠ ∅`),
--   node splitting requires `W ⊆ G.V` strictly: the construction
--   *removes* members of `W` from `V` and creates tagged copies, so
--   it only makes sense on output nodes.  `hW` is part of the
--   signature but is not consumed in every proof obligation (the
--   type-level disjointness of the three `SplitNode`
--   constructors already discharges most of the work); the few
--   obligations that do consume it are the `hJV_disj` and
--   `hE_subset` / `hL_subset` set-membership cases that route the
--   unsplit `G.V \ W` branch through the `unsplit` constructor.
--
-- * **`Finset.image` for every set-builder, not `Finset.filter` /
--   recursion / a quotient.**  The LN writes the four components as
--   set-builders ranging over `G.E` / `G.L` / `W`.  Lean's
--   `Finset.image` is the closest primitive (`Finset.mem_image` gives
--   exactly `b ∈ s.image f ↔ ∃ a ∈ s, f a = b`), shares the
--   `Finset (SplitNode Node × SplitNode Node)`
--   carrier between the directed image clauses and the
--   `Finset (Sym2 (SplitNode Node))` carrier for the `L`-
--   side image, and decidability of `Finset.image` construction
--   follows from the `DecidableEq` instances on `Node` and
--   `SplitNode Node` (and from Mathlib's derived
--   `DecidableEq (Sym2 _)` instance for the `L`-side).  `Finset.
--   filter` was rejected because the construction *creates* new
--   elements via `toCopy0` / `toCopy1`, not selects
--   a subset of existing ones; recursion is overkill for a single
--   set-comprehension.  The `Sym2` quotient encoding is precisely
--   what the post-refactor `L` carrier needs — `Finset.image` over
--   `Sym2.map (toCopy0 W)` reads the LN's
--   "$L_{\spl(W)} := \{ s(v_1^0, v_2^0) \mid s(v_1, v_2) \in L \}$"
--   literally on the unordered-pair carrier.
--
-- * **Notational shorthand `v^0 := v^1 := v` as helper *functions*
--   `toCopy0` / `toCopy1`, not as a coercion.**
--   The LN's "$v^0 := v^1 := v$ for $v \in J \cup (V \setminus W)$"
--   is *meta-notation* used inside the set-builders for items iii
--   and iv; it is NOT a coercion that re-assigns the meaning of `v`
--   in the ambient carrier (per the operator clarification,
--   "untagged nodes $v \in J \cup (V \sm W)$ remain of their
--   original kind in the ambient carrier").  The Lean rendering as
--   a function `toCopy0 W : Node → SplitNode Node`
--   (branching on `v ∈ W` to pick either `SplitNode.copy0
--   v` or `SplitNode.unsplit v`) captures exactly this
--   reading: the *original* `v : Node` continues to inhabit `Node`,
--   and the function is just the per-set-builder lift into
--   `SplitNode Node`.  A `Coe Node (SplitNode
--   Node)` instance was rejected because (i) `Node` is polymorphic
--   and a global coercion would fire across the chapter, and
--   (ii) there are *two* such lifts (`toCopy0` and
--   `toCopy1`) differing only on `W` — neither is canonical.
--
-- * **Items i, ii: literal `Finset.image` translations.**  Item i
--   (`J' := G.J.image .unsplit`) injects every input node through
--   the `unsplit` constructor; item ii's three-piece union
--   `(G.V \ W).image .unsplit ∪ W.image .copy0 ∪ W.image .copy1`
--   spells out the LN's `(V \ W) \dcup W^0 \dcup W^1` literally,
--   with the LN's three pieces in left-to-right order.  Unchanged
--   from the pre-refactor encoding (`J`, `V`, `hJV_disj` are
--   untouched by the refactor — only `L`-side typing changed).
--
-- * **Item iii: two-clause union, lifted edges plus transfer edges.**
--   The first clause
--   `G.E.image (fun e => (toCopy1 W e.1,
--                         toCopy0 W e.2))`
--   lifts every directed edge `v_1 → v_2 ∈ G.E` to the LN's
--   `(v_1^1, v_2^0)`.  The second clause
--   `W.image (fun w => (.copy0 w, .copy1 w))` adds the *transfer
--   edges* `w^0 → w^1` for every `w ∈ W`.  These two clauses are
--   semantically disjoint (the transfer edges have `.copy0` on the
--   source side, which the first clause's `toCopy1` cannot
--   produce on `v_1 ∈ G.J ∪ G.V`); the union is taken literally for
--   LN-faithfulness, not because the disjointness is content-
--   bearing.  Unchanged from the pre-refactor encoding (`E`'s
--   ordered-pair typing is untouched by the refactor).
--
-- * **Item iv: single-clause `Finset.image (Sym2.map …)`, both
--   endpoints via `toCopy0`.**  The LN's *asymmetric*
--   choice of `^0` on both endpoints of every lifted bidirected edge
--   (per the wording-check subtlety
--   `spl_L_attached_to_W0_only_silently`) is the load-bearing
--   convention.  No bidirected edge in `L_{\spl(W)}` has `.copy1 w`
--   as an endpoint.  Downstream rows that reason about the
--   bidirected/latent structure (c-components, m-separation,
--   confounding ancestry) build on this one-sided convention, and
--   swapping `^0` for `^1` would change the chapter's semantics.
--   The semantic motivation is the SWIG-style reading composed
--   downstream in `def_3_12` (NodeSplittingHard): each `w^0`-copy
--   represents the *natural* / observational side of `w` (its pre-
--   intervention identity, on which latent confounding and ancestry
--   are inherited from `G`), while each `w^1`-copy represents the
--   *intervened* / `do`-side, which is causally isolated from its
--   observational counterpart.  Bidirected edges encode latent
--   confounding, which by SWIG semantics lives entirely on the
--   natural (`W^0`) side; the intervened `W^1`-copies have no latent
--   structure by design.  This is what makes the one-sided lift the
--   unique LN-faithful reading and not a typo — `review_design`
--   PASS surfaced exactly this point pre-refactor, and the
--   `Sym2.map` lift now expresses it in a single closed form rather
--   than as two coordinated pair-projection clauses.
--
-- * **Self-loops `(v, v) ∈ E` for `v ∈ W` produce 2-cycles
--   `v^0 → v^1 → v^0` in `E_{\spl(W)}`; the result is still a CDMG.**
--   Per the wording-check subtlety
--   `spl_self_loop_creates_two_cycle_in_split` and the rewritten
--   tex's "Self-loops on $W$ produce $2$-cycles" paragraph: the
--   first clause of item iii produces the lifted edge `(v^1, v^0)`
--   and the second clause adds the transfer edge `(v^0, v^1)`,
--   yielding a directed 2-cycle.  This does NOT invalidate the
--   `CDMG` axioms (`def_3_1` does not require acyclicity);
--   it only means downstream claims about node-splitting preserving
--   acyclicity (cf. `claim_3_6` SplitTopologicalOrder) must add a
--   self-loop-free precondition on `G`.  Unchanged from the pre-
--   refactor encoding (this subtlety lives entirely on the `E`-side,
--   which the refactor does not touch).
--
-- * **Type-level disjointness collapses the `hJV_disj` /
--   `hE_subset` / `hL_subset` proof obligations.**  Because
--   `SplitNode.unsplit`, `SplitNode.copy0`,
--   `SplitNode.copy1` are distinct constructors of an
--   `inductive` type, any `Disjoint`-style obligation between two
--   of the three `Finset` images reduces to a per-element
--   `Finset.mem_image` check and a constructor-mismatch `cases` or
--   `noConfusion`.  The only non-trivial case in `hJV_disj` is the
--   `J vs (V \ W)` branch where both Finsets route through
--   `unsplit`; there the injectivity of `unsplit` reduces the
--   obligation to `G.hJV_disj`.  On the `L`-side, `hL_subset` reads
--   each endpoint of a lifted `Sym2` edge via `Sym2.mem_map` and
--   case-splits `w ∈ W`: the `.copy0`-branch lands in
--   `W.image .copy0`; the `.unsplit`-branch combines `w ∈ G.V`
--   (from `G.hL_subset`) and `w ∉ W` to land in
--   `(G.V \ W).image .unsplit`.
--
-- * **`hL_irrefl` transports pointwise from `G.hL_irrefl` via
--   `toCopy0`-injectivity.**  Each `s ∈ L'` factors as
--   `s = Sym2.map (toCopy0 W) s₀` for some `s₀ ∈ G.L`.
--   `Sym2.IsDiag (Sym2.map f s₀)` is equivalent to `s₀.IsDiag`
--   *when `f` is injective* (Mathlib's `Sym2.isDiag_map`); we have
--   `toCopy0_inj` precisely for this, so `s.IsDiag` would
--   contradict `G.hL_irrefl s₀ hs₀L`.  This is the post-refactor
--   replacement for the pre-refactor obligation "`v_1 ≠ v_2`": the
--   `Sym2`-level irreflexivity predicate combines naturally with
--   `Sym2.map` and lifts cleanly through any injective node-map.
--   No `hL_symm` obligation to discharge — swap-symmetry is
--   definitional on `Sym2`, structurally collapsing the pre-
--   refactor fifth obligation.
--
-- * **Argument order `(G : CDMG Node) (W : Finset Node)
--   (hW : …)`.**  Matches the convention of every chapter-3
--   predicate (`G.tuh`, `G.huh`, `G.adjacent`,
--   `G.hardInterventionOn`), enabling dot-notation
--   `G.nodeSplittingOn W hW`.  `W` precedes `hW` so the
--   call site reads left-to-right like the LN's "Let `W ⊆ V` be a
--   subset".  Mirrors `hardInterventionOn`'s argument
--   order verbatim.
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The `CDMG` `structure` has eight fields —
--   one fewer than the pre-refactor nine, because `hL_symm` is gone
--   (swap-symmetry is definitional on `Sym2`).  An anonymous-
--   constructor form would interleave data and proof obligations in
--   a positional list, making the correspondence with `def_3_1`'s
--   `structure` opaque at a glance.  `where … J := … V := …` keeps
--   every field labelled and lets the proof obligations sit next to
--   the data they refer to.  Mirrors `hardInterventionOn`'s
--   choice.
--
-- * **No local `Decidable` instance for the L-side filter.**
--   `def_3_10`'s `hardInterventionOn` needs a private
--   `DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W)` instance
--   because it uses `Finset.filter` on a `Sym2`-bounded-universal
--   predicate.  This row uses `Finset.image (Sym2.map …)` instead,
--   which only requires `DecidableEq` of the image-carrier type
--   (`Sym2 (SplitNode Node)`); Mathlib's derived
--   `DecidableEq (Sym2 _)` instance handles that from
--   `[DecidableEq Node]` plus `deriving DecidableEq` on
--   `SplitNode`.  No `Sym2.Mem`-bounded-universal predicate
--   appears in any of the four CDMG-axiom proof obligations, so no
--   local `DecidablePred` instance is needed.  The L-side
--   construction is therefore strictly simpler than `def_3_10`'s,
--   not more complex — the refactor's structural benefit lands at
--   this row without any boilerplate price.
--
-- * **`def`, not `noncomputable def`.**  Both the `E`-side and `L`-
--   side images are kernel-computable: `Finset.image` is computable
--   whenever the target carrier has `DecidableEq`, and `Sym2.map` is
--   a `Quot.map` of a function (kernel-computable) on the underlying
--   pair.  The resulting `CDMG` is therefore a *computable*
--   construction, matching the pre-refactor design and keeping
--   `#eval (G.nodeSplittingOn W hW).L` available for
--   inspecting the split graph on small concrete examples.  No
--   `Classical.dec`-style shortcut was needed.
--
-- * **Downstream consumers.**  SWIG `def_3_12` (the composition of
--   node splitting with hard intervention on the `W^1`-copies),
--   `claim_3_6` SplitTopologicalOrder (a topological order on the
--   acyclic, self-loop-free `G` induces one on `G_{\spl(W)}`),
--   `claim_3_12` HardInterventionNodeSplit (the interaction between
--   node splitting and disjoint hard intervention).  Each of these
--   rests on the four field assignments above; the tagged-sum
--   carrier `SplitNode Node` is the contract those rows
--   rely on.  Post-refactor, these consumers see the `Sym2`-native
--   `L` image — no manual `(toCopy0, toCopy0)` pair-construction is
--   needed in any of them, and the membership rule on
--   `(G.nodeSplittingOn W hW).L` reduces to a single
--   `Finset.mem_image.mp` + `Sym2.mem_map.mp` chain without case-
--   splitting on which endpoint was the LN's "$v_1$" vs "$v_2$".
--
-- * **Working-phase wording-check subtleties are non-issues for the
--   `Sym2` port.**  Two subtleties were surfaced at this row's
--   working-phase check (`Section3_2/workspace_def_3_11.md`):
--   (a) `spl_self_loop_creates_two_cycle_in_split` — admitted as
--   above (the construction does produce 2-cycles on `E`-self-loops
--   into `W`; this is unchanged from pre-refactor because the
--   refactor touches only the `L`-side); (b)
--   `spl_L_attached_to_W0_only_silently` — preserved *structurally*
--   by `Sym2.map (toCopy0 W)`, which never produces a
--   `.copy1 w` endpoint in `L_{\spl(W)}` by construction.  Both are
--   non-issues for this port; the manager will decide whether to
--   `register_ln_subtlety` after review.
-- ## Proof helpers for the four CDMG axioms under node splitting
--
-- The four private lemmas below discharge the four proof obligations
-- of `def_3_1`'s post-refactor `CDMG` structure
-- (`hJV_disj`, `hE_subset`, `hL_subset`, `hL_irrefl`) for the
-- node-splitting construction.  One fewer than the pre-refactor five
-- (`nodeSplittingOn_hL_symm` is gone — swap-symmetry is definitional
-- on `Sym2`).  They are factored out of the structure-literal body
-- of `nodeSplittingOn` so the def body is pure data + lemma
-- references — the website builder renders the def's signature, and
-- a reader sees the data assignments without proof clutter.  Per
-- the `hW`-unused design-choice bullet above, none of the
-- obligations consume `hW`; `hW` is carried on the def's signature
-- purely for LN-faithfulness (the LN's "Let `W ⊆ V`").

-- ### Proof helper 1 / 4 — `J' ∩ V' = ∅` after the split lift
--
-- *What this discharges.*  The `hJV_disj` field of `CDMG`
-- for the node-split graph: the lifted input set
-- `G.J.image .unsplit` is disjoint from the three-piece union
-- forming the lifted output set
-- `(G.V \ W).image .unsplit ∪ W.image .copy0 ∪ W.image .copy1`.
--
-- *Refactor port note.*  The post-refactor `def_3_1.hJV_disj`
-- field is *unchanged* from the pre-refactor encoding — the
-- `cdmg_typed_edges` refactor only touched `L`-side fields.  So
-- this obligation is a mechanical port of the pre-refactor
-- `nodeSplittingOn_hJV_disj`; only the namespace prefix and
-- constructor names change.
--
-- *Design choice — `private lemma` factored out of the structure
-- literal.*  Per the convention in `claude.md` (formalize-def
-- pattern) and the "where syntax with named fields" design-choice
-- bullet above the main `def`, constructor-proof obligations live
-- *outside* the structure literal so the def body stays pure
-- data + lemma references.  This lemma is purely proof-side
-- scaffolding for the constructor: it is NOT part of the row's
-- statement (no `-- def_3_11 --- start helper` markers wrap it),
-- and the `private` modifier keeps it scoped to this file.
--
-- *Design choice — proof strategy leverages type-level
-- disjointness.*  Three of the four image-vs-image overlap cases
-- close *structurally* by constructor mismatch on
-- `SplitNode` (`.unsplit ≠ .copy0`, `.unsplit ≠ .copy1`):
-- `cases hweq` immediately discharges them because there is no
-- equation between distinct inductive constructors.  The single
-- non-trivial case (`.unsplit j` for `j ∈ G.J` versus
-- `.unsplit v` for `v ∈ G.V \ W`) reduces by injectivity of the
-- `.unsplit` constructor to `j = v`, which contradicts
-- `G.hJV_disj` on the original CDMG.  This is the load-bearing
-- payoff of encoding the three node-kinds as distinct constructors
-- of a single `inductive` (cf. the "type-level disjointness
-- collapses obligations" design-choice bullet above): a
-- `Sum`-based or `Finset.disjUnion`-based encoding would have
-- moved this structural part of the proof into explicit
-- `Sum.inl`/`Sum.inr` case-splits or
-- `Finset.disjoint_disjUnion_left` lemma invocations.
--
-- *`hW` not on the signature.*  The W-in-V hypothesis is not
-- consumed: constructor mismatch and `G.hJV_disj` together
-- discharge every case without needing `W ⊆ G.V`.
private lemma nodeSplittingOn_hJV_disj
    (G : CDMG Node) (W : Finset Node) :
    Disjoint (G.J.image SplitNode.unsplit)
        ((G.V \ W).image SplitNode.unsplit
          ∪ W.image SplitNode.copy0
          ∪ W.image SplitNode.copy1) := by
  rw [Finset.disjoint_left]
  rintro x hxJ hxV
  obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hxJ
  rcases Finset.mem_union.mp hxV with hxV12 | hxC1
  · rcases Finset.mem_union.mp hxV12 with hxVuns | hxC0
    · obtain ⟨v, hvVW, hveq⟩ := Finset.mem_image.mp hxVuns
      cases hveq
      exact Finset.disjoint_left.mp G.hJV_disj hjJ
        (Finset.mem_sdiff.mp hvVW).1
    · obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hxC0
      cases hweq
  · obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hxC1
    cases hweq

-- ### Proof helper 2 / 4 — typing of `E'` after the split lift
--
-- *What this discharges.*  The `hE_subset` field of
-- `CDMG` for the node-split graph: every ordered pair in
-- the two-clause union forming `E'` satisfies the LN typing
-- `E' ⊆ (J' ∪ V') × V'` (item iii of `def_3_11`).
--
-- *Refactor port note.*  The post-refactor `def_3_1.hE_subset`
-- field is *unchanged* from the pre-refactor encoding — the
-- `cdmg_typed_edges` refactor leaves `E`'s ordered-pair typing
-- alone (only `L`'s carrier moved to `Sym2`).  So this obligation
-- is a mechanical port of the pre-refactor
-- `nodeSplittingOn_hE_subset`; only the namespace prefix and
-- constructor names change.
--
-- *Design choice — `private lemma` factored out.*  Same rationale
-- as `nodeSplittingOn_hJV_disj` above: keeps the def body
-- pure data + lemma references; not part of the row's statement;
-- `private`-scoped to this file.
--
-- *Proof strategy.*  Case-split on the union clause forming
-- `e ∈ E'`:
--
--   * **Lifted edges (clause 1):** `e = (toCopy1 W e'.1,
--     toCopy0 W e'.2)` for some `e' ∈ G.E`.  Case-split
--     on `e'.1 ∈ W`: on the `W`-branch the source unfolds to
--     `.copy1 e'.1 ∈ W.image .copy1 ⊆ V' ⊆ J' ∪ V'`; on the
--     complement, the source unfolds to `.unsplit e'.1`, and a
--     further case-split on whether `e'.1 ∈ G.J` or `e'.1 ∈ G.V`
--     (from `G.hE_subset`) lands it in `J'` or
--     `(G.V \ W).image .unsplit ⊆ V'` respectively.  The target
--     unfolds analogously with `toCopy0`, two branches.
--
--   * **Transfer edges (clause 2):** `e = (.copy0 w, .copy1 w)`
--     for some `w ∈ W`.  Both endpoints land directly in
--     `W.image .copy0 ⊆ V'` and `W.image .copy1 ⊆ V'` by
--     construction.
--
-- *Design choice — `simp only [toCopy0/1, …, if_true /
-- if_false]` to unfold the helper.*  The `if`-branches of
-- `toCopy0` / `toCopy1` are dispatched
-- explicitly via `simp only` with `if_true` / `if_false`
-- lemmas, rather than via `unfold` or by-cases on the underlying
-- decidability.  This keeps each branch's residual goal in the
-- shape of a literal `.copy0 _` / `.copy1 _` / `.unsplit _`
-- constructor application, which then matches the right
-- `Finset.mem_image` shape.  An alternative `unfold` approach
-- would have left the `if` unevaluated in the goal, forcing
-- explicit `rfl`-rewrites; the explicit `simp only` is one step
-- shorter and locally clearer.
--
-- *`hW` not on the signature.*  The W-in-V hypothesis is not
-- consumed: `G.hE_subset` already gives `e'.1 ∈ J ∪ V` (so the
-- non-W case-split lands in `J' ∪ (G.V \ W).image .unsplit` via
-- the LN-given typing), and the lifted-edge case never needs
-- `W ⊆ G.V` to position the target either.
private lemma nodeSplittingOn_hE_subset
    (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : SplitNode Node × SplitNode Node⦄,
      e ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))
          ∪ W.image (fun w =>
              (SplitNode.copy0 w, SplitNode.copy1 w)) →
      e.1 ∈ G.J.image SplitNode.unsplit ∪
              ((G.V \ W).image SplitNode.unsplit
                ∪ W.image SplitNode.copy0
                ∪ W.image SplitNode.copy1) ∧
        e.2 ∈ (G.V \ W).image SplitNode.unsplit
                ∪ W.image SplitNode.copy0
                ∪ W.image SplitNode.copy1 := by
  intro e he
  rcases Finset.mem_union.mp he with hImg | hTrans
  · obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp hImg
    obtain ⟨he'1, he'2⟩ := G.hE_subset he'E
    refine ⟨?_, ?_⟩
    · by_cases hW1 : e'.1 ∈ W
      · simp only [toCopy1, hW1, if_true]
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hW1, rfl⟩
      · simp only [toCopy1, hW1, if_false]
        rcases Finset.mem_union.mp he'1 with hJ | hV
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e'.1, hJ, rfl⟩)
        · refine Finset.mem_union_right _ ?_
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr
            ⟨e'.1, Finset.mem_sdiff.mpr ⟨hV, hW1⟩, rfl⟩
    · by_cases hW2 : e'.2 ∈ W
      · simp only [toCopy0, hW2, if_true]
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨e'.2, hW2, rfl⟩
      · simp only [toCopy0, hW2, if_false]
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr
          ⟨e'.2, Finset.mem_sdiff.mpr ⟨he'2, hW2⟩, rfl⟩
  · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hTrans
    refine ⟨?_, ?_⟩
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨w, hwW, rfl⟩
    · refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨w, hwW, rfl⟩

-- ### Proof helper 3 / 4 — typing of `L'` after the split lift
--
-- *What this discharges.*  The `hL_subset` field of
-- `CDMG` for the node-split graph: every endpoint of
-- every bidirected edge in `L'` lies in the lifted output set
-- `V' = (G.V \ W).image .unsplit ∪ W.image .copy0 ∪ W.image .copy1`.
--
-- *Refactor port note — load-bearing signature change.*  The
-- post-refactor `def_3_1.hL_subset` signature *changed* under
-- `cdmg_typed_edges`: it is now universally quantified via
-- `Sym2.Mem` (`∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V`) on the
-- `Sym2 Node` carrier, NOT the pre-refactor
-- `e.1 ∈ V ∧ e.2 ∈ V` on ordered pairs.  This obligation is the
-- load-bearing *consumer* of the post-refactor shape at this row;
-- the proof exercises both (i) `Sym2.mem_map` to extract the
-- underlying ordered-pair witness from a `Sym2.map`-image, and
-- (ii) the `Sym2.Mem`-style quantification at the call site.
--
-- *Design choice — `private lemma` factored out.*  Same rationale
-- as the previous two helpers: keeps the def body pure data +
-- lemma references; not part of the row's statement;
-- `private`-scoped to this file.
--
-- *Proof strategy.*  Each `s ∈ L'` factors as
-- `s = Sym2.map (toCopy0 W) s₀` for some `s₀ ∈ G.L` (via
-- `Finset.mem_image`).  Each endpoint `v ∈ s` factors as
-- `v = toCopy0 W w` for some `w ∈ s₀` (via
-- `Sym2.mem_map`).  From `G.hL_subset` we obtain `w ∈ G.V`.
-- Then case-split `w ∈ W`:
--
--   * on the `W`-branch, `v = .copy0 w` lands in
--     `W.image .copy0 ⊆ V'`;
--   * on the complement, `v = .unsplit w` with `w ∈ G.V \ W`
--     lands in `(G.V \ W).image .unsplit ⊆ V'`.
--
-- *Design choice — dispatch via `Sym2.mem_map`, not `Sym2.ind` to
-- destructure through `Sym2.mk`.*  `Sym2.mem_map` is the
-- canonical Mathlib idiom for "what does a `Sym2.map f s` edge
-- contain"; it returns `∃ w ∈ s, f w = v` directly, bypassing the
-- need to pick a representative of the quotient.  The alternative
-- (`Sym2.ind` to lift `s₀` to an ordered pair `(a, b)` and then
-- case-split on which coordinate `v` matches) would force a
-- representative choice that the swap quotient makes arbitrary —
-- exactly what the `cdmg_typed_edges` refactor exists to avoid
-- (`Sym2.map` lifts pointwise, and `Sym2.mem_map` reads off the
-- pre-image pointwise without quotient bookkeeping).
--
-- *`hW` not on the signature.*  The W-in-V hypothesis is not
-- consumed: the case-split on `w ∈ W` versus `w ∈ G.V \ W` is
-- decidable from `[DecidableEq Node]` on `Finset Node` without
-- needing `W ⊆ G.V`.
private lemma nodeSplittingOn_hL_subset
    (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃s : Sym2 (SplitNode Node)⦄,
      s ∈ G.L.image (Sym2.map (toCopy0 W)) →
      ∀ ⦃v : SplitNode Node⦄, v ∈ s →
        v ∈ (G.V \ W).image SplitNode.unsplit
            ∪ W.image SplitNode.copy0
            ∪ W.image SplitNode.copy1 := by
  intro s hs v hv
  obtain ⟨s₀, hs₀L, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨w, hwS, rfl⟩ := Sym2.mem_map.mp hv
  have hwV : w ∈ G.V := G.hL_subset hs₀L hwS
  by_cases hwW : w ∈ W
  · simp only [toCopy0, hwW, if_true]
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨w, hwW, rfl⟩
  · simp only [toCopy0, hwW, if_false]
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr
      ⟨w, Finset.mem_sdiff.mpr ⟨hwV, hwW⟩, rfl⟩

-- ### Proof helper 4 / 4 — irreflexivity of `L'` after the split lift
--
-- *What this discharges.*  The `hL_irrefl` field of
-- `CDMG` for the node-split graph: no bidirected edge of
-- `L'` is a self-pair (`¬ s.IsDiag`).
--
-- *Refactor port note — load-bearing signature change.*  The
-- post-refactor `def_3_1.hL_irrefl` signature *changed* under
-- `cdmg_typed_edges`: it is now `¬ s.IsDiag` (Mathlib's canonical
-- "this unordered pair is a self-pair" predicate on `Sym2 _`),
-- NOT the pre-refactor `v₁ ≠ v₂` on ordered pairs.  The two are
-- mathematically equivalent (`Sym2.IsDiag s(x, y) ↔ x = y`), but
-- the `Sym2`-level idiom composes cleanly with `Sym2.map` via
-- Mathlib's `Sym2.isDiag_map`, which is the central lift used by
-- this proof.  This is the single largest proof simplification of
-- the `cdmg_typed_edges` refactor at this row: pre-refactor, the
-- analogous `nodeSplittingOn_hL_irrefl` had to destructure
-- `s = s(a, b)` via `Sym2.ind`, manipulate ordered-pair-with-
-- symmetry through `G.hL_symm`, and re-route through the
-- `≠`-flavored conclusion of `G.hL_irrefl`.  Post-refactor the
-- entire pipeline collapses to a single `Sym2.isDiag_map` lift.
--
-- *Design choice — `private lemma` factored out.*  Same rationale
-- as the previous three helpers: keeps the def body pure data +
-- lemma references; not part of the row's statement;
-- `private`-scoped to this file.
--
-- *Proof strategy.*  Each `s ∈ L'` factors as
-- `s = Sym2.map (toCopy0 W) s₀` for some `s₀ ∈ G.L`
-- (via `Finset.mem_image`).  Suppose `s.IsDiag`.  By
-- `Sym2.isDiag_map` (Mathlib's "diag-preservation under
-- injective lift") and `toCopy0_inj` (the
-- private-helper injectivity result proved above the main
-- block), we conclude `s₀.IsDiag`.  This contradicts
-- `G.hL_irrefl s₀ hs₀L`, completing the proof.
--
-- *Design choice — `Sym2.isDiag_map` over manual destructuring.*
-- Mathlib's `Sym2.isDiag_map : Function.Injective f →
-- (Sym2.map f s).IsDiag ↔ s.IsDiag` is the right idiom because
-- (i) it accepts a *bare* injectivity premise (no `Sym2`-quotient
-- bookkeeping required at the call site), and (ii) it discharges
-- in *one rewrite step* what would otherwise be a four-case
-- destructure (`Sym2.ind` on `s₀`, then a case-split on whether
-- each endpoint is in `W`, then constructor-mismatch reasoning
-- on the four `.copy0 _ = .copy0 _` / `.copy0 _ = .unsplit _` /
-- `.unsplit _ = .copy0 _` / `.unsplit _ = .unsplit _` cases).
-- The pre-refactor proof had to do (variants of) this manual
-- destructure because pre-refactor `hL_irrefl` was phrased on
-- ordered pairs.
--
-- *Design choice — why `toCopy0_inj` is a separate
-- helper.*  `Sym2.isDiag_map` requires the function argument to
-- satisfy `Function.Injective f` in the precise Mathlib sense
-- `∀ a b, f a = f b → a = b`.  Factoring `toCopy0_inj`
-- as a standalone private lemma lets it be referenced here with
-- a single `(fun _ _ => toCopy0_inj)` thunk and avoids
-- inlining the four-case `by_cases` proof at every potential
-- `Sym2.isDiag_map` call site.  This is the only call site at
-- present; if any downstream row lifts via
-- `Sym2.map (toCopy0 W)` (anticipated for
-- `claim_3_22`-style σ-separation-symmetry arguments), the
-- helper is already available.
--
-- *`hW` not on the signature.*  The W-in-V hypothesis is not
-- consumed: `Sym2.isDiag_map` and
-- `G.hL_irrefl` together discharge the goal without needing
-- `W ⊆ G.V`.
private lemma nodeSplittingOn_hL_irrefl
    (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃s : Sym2 (SplitNode Node)⦄,
      s ∈ G.L.image (Sym2.map (toCopy0 W)) →
      ¬ s.IsDiag := by
  intro s hs hDiag
  obtain ⟨s₀, hs₀L, rfl⟩ := Finset.mem_image.mp hs
  have hs₀Diag : s₀.IsDiag :=
    (Sym2.isDiag_map (fun _ _ => toCopy0_inj)).mp hDiag
  exact G.hL_irrefl hs₀L hs₀Diag

-- `hW` is bound on the signature for LN-faithfulness ("Let
-- `W ⊆ V`") but is not consumed by any of the four obligations — the
-- type-level distinction of `SplitNode`'s three
-- constructors and `G`'s own axioms discharge them.  The
-- `set_option` keeps the linter quiet without dropping the binder
-- from the signature (which is part of the LN-faithful encoding and
-- the call-site contract `G.nodeSplittingOn W hW`).
set_option linter.unusedVariables false in
-- def_3_11 -- start statement
def nodeSplittingOn (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) : CDMG (SplitNode Node) where
  J := G.J.image SplitNode.unsplit
  V := (G.V \ W).image SplitNode.unsplit
        ∪ W.image SplitNode.copy0
        ∪ W.image SplitNode.copy1
  hJV_disj := nodeSplittingOn_hJV_disj G W
  E := G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))
        ∪ W.image (fun w =>
            (SplitNode.copy0 w, SplitNode.copy1 w))
  hE_subset := by exact nodeSplittingOn_hE_subset G W
  L := G.L.image (Sym2.map (toCopy0 W))
  hL_subset := by exact nodeSplittingOn_hL_subset G W
  hL_irrefl := by exact nodeSplittingOn_hL_irrefl G W
-- def_3_11 -- end statement

end CDMG

end Causality
