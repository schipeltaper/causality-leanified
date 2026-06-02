import Chapter3_GraphTheory.Section3_1.CDMGNotation

/-!
# Node-splitting on a CDMG (def 3.11)

This file formalises *definition 3.11* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): given a
CDMG `G = (J, V, E, L)` and a subset `W ⊆ V` of output nodes, the
*node-split graph* `G_{spl(W)}` duplicates every `w ∈ W` into a
"0-copy" `w^0` (the new sink for all edges incoming to `w`) and a
"1-copy" `w^1` (the new source of all edges outgoing from `w`),
with a fresh directed edge `w^0 → w^1` for every `w ∈ W`.
Bidirected edges between output nodes attach to the 0-copies of
their endpoints (using the convention `v^0 := v` for `v ∉ W`).

Concretely, the resulting CDMG lives over a *new* ambient type
`α ⊕ ↑W` with the convention

* `w^0 := Sum.inl w` for `w ∈ W` (the 0-copies, *the canonical
  observation copy*, are identified with the originals via the
  `inl` embedding -- this is the LN's hint
  "%which could be identified with $V$ again if we want to make
  the identification $W = W^0$" in def_3_11 and the analogous
  hint at def_3_12 "$W = W^o$", which matches the
  Richardson--Robins SWIG convention `X = X^o`);
* `w^1 := Sum.inr ⟨w, hw⟩` for `w ∈ W` (the 1-copies, the fresh
  intervention-input labels, are indexed by `W`);
* `v^0 := v^1 := Sum.inl v` for `v ∉ W` (matching the LN's
  identity convention on the unsplit nodes).

This is the second of the two "intervention-style" operations of
Section 3.2 (the first being `hardInterventionOn` of def 3.10);
nearly every later split-related statement in the chapter and the
SWIG / counterfactual machinery of chapters 8 -- 16 quotes it.

## Where this gets used downstream

* **claim_3_6** (`graphs.tex` Rem 446, "split topological order")
  -- if `G` is acyclic with topological order `<`, then
  `G_{spl(W)}` is also acyclic; an explicit topological order on
  the split graph is built from `<` by interleaving each
  `w^0, w^1` immediately around `w`.
* **claim_3_7** (`graphs.tex` Lem 458, "two disjoint
  node-splittings commute") --
  `(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)} =
  G_{spl(W₁ ⊔ W₂)}`. Iteration here is type-changing
  (the carrier nests as `(α ⊕ ↑W₁) ⊕ ↑W₂` etc.), so the equality
  is stated modulo a re-labeling equivalence.
* **claim_3_8** (`graphs.tex` Lem 497) -- disjoint hard
  interventions and node-splittings commute; combines the present
  `@[simp]` membership lemmas with their `HardInterventionOn`
  counterparts.
* **claim_3_12** (`graphs.tex` Lem) -- composition of
  `HardInterventionOn` with `NodeSplittingOn`.
* **def_3_12** (`graphs.tex` Def 580, `G_{swig(W)}`,
  single-world intervention graph) -- a SWIG is a node-splitting
  followed by a hard intervention on the `W^1` copies; the
  building blocks for the SWIG definition are the
  `@[simp]` membership lemmas below.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ## 1-copy encoding helper -/

-- ## Design choice (`split1`)
--
-- * **Standalone helper rather than an inlined `dite`.** The
--   1-copy operation `v ↦ v^1` shows up at *the source endpoint*
--   of every original directed edge (LN item iii) and at every
--   later split-related lemma (claim_3_6 builds a topological
--   order by interleaving `w^0, w^1`; claim_3_7 / claim_3_8
--   pattern-match on `split1` membership; def_3_12 composes a
--   `split1`-source with a hard intervention). Factoring it out
--   under a single name -- with the two `@[simp]` reduction
--   lemmas `split1_of_mem` / `split1_of_not_mem` -- lets `simp`
--   discharge the case-split once per call site, instead of
--   forcing every downstream proof to re-derive the same `dite`.
-- * **`noncomputable` + global `open Classical` over a
--   `[Decidable (v ∈ W)]` parameter.** The LN takes `W : Set V`
--   with no decidability hypothesis; matching that, our signature
--   is `W : Set α` and `v ∈ W` is a `Prop`, not a `Bool`.
--   Threading a `[Decidable (v ∈ W)]` instance through `split1`,
--   every membership lemma, and every downstream `simp` call
--   would be intrusive for zero computational payoff:
--   `nodeSplittingOn` is `Prop`-valued (sets of vertices and
--   edges) -- no caller ever *evaluates* `split1` at runtime, so
--   classical choice in the construction has no observable cost.
--   We mark the helper `noncomputable` to make the choice loud
--   rather than implicit; this is consistent with how the rest of
--   Section 3.2 (and `hardInterventionOn` downstream) is written.
-- * **No companion `split0` helper.** Under our identification
--   convention `Sum.inl = 0-copy` (canonical observation copy;
--   see the design block on `nodeSplittingOn` below), the LN's
--   0-copy operation `v ↦ v^0` is the canonical `Sum.inl`
--   embedding with *no* case-split on `v ∈ W`. So a hypothetical
--   `split0 W v` would be a no-op alias for `Sum.inl v`; we use
--   `Sum.inl` directly. This asymmetry is the entire payoff of
--   fixing the identification direction `inl = 0`: only the
--   1-copy needs a `dite`-style helper.
-- * **`α ⊕ ↑W` codomain rather than a parameter.** The
--   codomain `α ⊕ ↑W` is the carrier of the about-to-be-built
--   `nodeSplittingOn G W hW`. Making it a separate type
--   parameter (or a `[Decidable]`-style universe shuffle) would
--   force every caller to instantiate the carrier explicitly;
--   inlining it keeps the helper a one-call away from the main
--   construction.

/-- The "1-copy" encoding of a vertex `v : α` in the carrier
`α ⊕ ↑W` of a node-split graph:

* if `v ∈ W`: returns `Sum.inr ⟨v, hv⟩`, the fresh `W^1`
  intervention-input label for `v`;
* if `v ∉ W`: returns `Sum.inl v`, matching the LN's convention
  `v^1 := v` for vertices outside `W`.

The complementary "0-copy" encoding `v^0 := Sum.inl v` is plain
`Sum.inl` -- the *canonical observation copy*, identified with the
original vertex (cf. the LN comment "we ... make the
identification $W = W^0$" in def_3_11). No wrapper needed (see the
design notes above for the asymmetry).

Noncomputable because membership in a general `Set α` need not be
decidable: we use `Classical.propDecidable` via `open Classical`.
Used Prop-valued only, so the classical choice has no observable
cost downstream. -/
noncomputable def split1 (W : Set α) (v : α) : α ⊕ ↑W :=
  open Classical in
  if h : v ∈ W then Sum.inr ⟨v, h⟩ else Sum.inl v

/-- `split1 W v = Sum.inl v` when `v ∉ W`, matching the LN's
convention `v^1 := v` on the unsplit vertices. -/
@[simp] theorem split1_of_not_mem {W : Set α} {v : α} (hv : v ∉ W) :
    split1 W v = Sum.inl v := by
  unfold split1
  exact dif_neg hv

/-- `split1 W v = Sum.inr ⟨v, hv⟩` when `v ∈ W`, the fresh
`W^1` intervention-input label. -/
@[simp] theorem split1_of_mem {W : Set α} {v : α} (hv : v ∈ W) :
    split1 W v = Sum.inr ⟨v, hv⟩ := by
  unfold split1
  exact dif_pos hv

/-- A `Sum.inl x` value equals `split1 W u` precisely when
`u ∉ W` and `x = u` -- the 0-copy / unsplit form of `split1`. -/
private theorem inl_eq_split1_iff {W : Set α} {u x : α} :
    (Sum.inl x : α ⊕ ↑W) = split1 W u ↔ u ∉ W ∧ x = u := by
  constructor
  · intro h
    by_cases hu : u ∈ W
    · rw [split1_of_mem hu] at h
      exact nomatch h
    · rw [split1_of_not_mem hu] at h
      exact ⟨hu, (Sum.inl_injective h)⟩
  · rintro ⟨hu, rfl⟩
    rw [split1_of_not_mem hu]

/-! ## The node-splitting CDMG construction -/

-- def_3_11
-- title: NodeSplittingOn
--
-- The *node-splitting* of a CDMG `G = (J, V, E, L)` with respect
-- to a subset `W ⊆ V` of output nodes is the CDMG `G_{spl(W)}`
-- over the carrier type `α ⊕ ↑W` obtained by duplicating every
-- `w ∈ W` into two copies: a 0-copy `w^0 := Sum.inl w` (the
-- *canonical observation copy*, identified with the original
-- vertex via `inl`) that receives the incoming edges of `w`, and
-- a 1-copy `w^1 := Sum.inr ⟨w, hw⟩` (fresh `inr`-label, the
-- intervention-input copy) that sends out the outgoing edges of
-- `w`. Between the two copies we add a fresh directed edge
-- `w^0 → w^1`. Bidirected edges relabel both endpoints to the
-- corresponding 0-copies (which here means: just `Sum.inl`).
-- The LN's `\spl(W)` subscript is the same operator written
-- infix.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.11):

\begin{defmark}
\begin{Def}[Node-splitting on CDMGs]
  \label{def:G_node-splitting}
    Let $G=(J,V,E,L)$ be a CDMG and $W \ins V$ a subset of the output nodes.
    The \emph{node-split graph} w.r.t.\ $W$ of $G$ is the CDMG:
    \[ G_{\spl(W)} :=\lp J_{\spl(W)}, V_{\spl(W)}, E_{\spl(W)},L_{\spl(W)} \rp,\]
    constructed as follows.
    We first make two disjont copies of the nodes in $W$:
    \[ W^0:=\lC w^0\st w \in W \rC, \qquad W^1:=\lC w^1 \st w \in W \rC.  \]
    Note that we consider $w^0 \neq w^1$ for $w \in W$.
    Additionally (for convenience), for $v \in J \cup V \sm W$ we put:
  \[ v^0:=v^1:=v.  \]
  We then define:
  \begin{enumerate}[label=\roman*.)]
      \item $J_{\spl(W)} := J$,
      \item $V_{\spl(W)} := (V \sm W) \dcup W^0 \dcup W^1$,
      \item $E_{\spl(W)} := \lC v^1_1 \tuh v_2^0 \st v_1 \tuh v_2 \in E \rC
                              \cup \lC w^0 \tuh w^1 \st w \in W \rC$,
      \item $L_{\spl(W)} :=\lC v_1^0 \huh v_2^0 \st v_1 \huh v_2 \in L \rC$.
  \end{enumerate}
  So all incoming edges onto nodes in $W$ become incoming edges into the
  corresponding nodes in $W^0$, all outgoing edges out of nodes in $W$ become
  outgoing edges out of the corresponding nodes in $W^1$, and edges
  $w^0 \tuh w^1$ are added for all nodes in $W$.
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Carrier type `α ⊕ ↑W`.** Unlike `hardInterventionOn` --
--   which is a `CDMG α → Set α → CDMG α` because hard
--   intervention never introduces new labels -- node-splitting
--   *does* introduce new labels (the 1-copies `W^1`), so the
--   result must live over a strictly larger type. We weigh three
--   shapes:
--
--     1. **`α ⊕ ↑W`** (this choice) -- one fresh copy of `W`
--        (the 1-copies, via `Sum.inr`); the original `α`
--        continues to host `J`, `V ∖ W`, and the 0-copies (via
--        `Sum.inl`). Effectively identifies `w^0 := w` for
--        `w ∈ W`. Smallest carrier, no quotient, and the LN's
--        identity convention `v^0 := v^1 := v` for `v ∉ W`
--        becomes the *canonical* `inl` embedding rather than a
--        case-split rule.
--     2. **`α ⊕ ↑W ⊕ ↑W`** -- two fresh copies of `W`; the
--        original `W` is "ghosted" out of the result. The most
--        literal reading of "two disjoint copies", but doubles
--        the carrier-shifting work in every downstream proof and
--        loses the natural `inl`-as-identity correspondence.
--     3. **`α ⊕ α`** -- doubles everything; forces an explicit
--        identification on `J ∪ V ∖ W` (collapse `inl = inr`
--        there) to recover LN semantics. Awkward and wasteful.
--
--   We choose option 1. The LN's "we consider `w^0 ≠ w^1`" is
--   captured exactly by `inl w ≠ inr ⟨w, _⟩` (distinct `Sum`
--   constructors). Downstream rows (claim_3_6
--   `SplitTopologicalOrder`, def_3_12 `NodeSplittingHard`,
--   claim_3_7, claim_3_12) pattern-match on this shape; the
--   `inl` embedding gives a clean way to recover the original
--   CDMG's structure under the split.
--
-- * **Direction of the identification: `Sum.inl = 0-copy`
--   (canonical observation copy), `Sum.inr = 1-copy` (fresh
--   intervention-input label).** The LN gives two explicit
--   hints that the 0-copy is the canonical one:
--
--     * def_3_11 itself, the commented-out line right next to
--       the `V_{spl(W)}` definition: "%which could be identified
--       with $V$ again if we want to make the identification
--       $W = W^0$";
--     * def_3_12 (`G_{swig(W)}`), the analogous hint: "...if we
--       want to make the identification $W = W^o$" (the LN uses
--       superscript `o` for observation = 0).
--
--   This is also the Richardson--Robins SWIG convention used
--   throughout the counterfactuals literature: `X = X^o = W^0`.
--   The original variable corresponds to the *observation*, with
--   the 1-copy / `^i` being the fresh intervention-input label.
--   Going the other way -- identifying the 1-copy with `α` --
--   would force every downstream SWIG / iSCM / counterfactual
--   mechanism statement to mentally invert the convention; see
--   in particular def_3_12 where post-SWIG output set becomes
--   `Sum.inl '' G.V` (exactly `X = X^o`) under our direction,
--   versus needing an extra `Sum.inl ''` re-lift if we went the
--   other way.
--
-- * **Precondition `W ⊆ G.V` is structurally required.**
--   `hardInterventionOn` opted to drop the LN's `W ⊆ J ∪ V`
--   precondition because the construction remained well-defined
--   for any `W`. Here, the precondition is *load-bearing*: the
--   split edge `w^0 → w^1 = (Sum.inl w, Sum.inr ⟨w, _⟩)` needs
--   its source `inl w` to live in `V_split`, and `V_split` only
--   contains `inl`-labels that lie in `G.V`. Without `W ⊆ G.V`,
--   for `w ∈ W ∖ G.V` the split edge would violate `E_subset`.
--   Adding `hW : W ⊆ G.V` to the signature is therefore the
--   cleanest fix and matches the LN ("`W ⊆ V` a subset of the
--   output nodes") exactly.
--
-- * **`J_split := Sum.inl '' G.J`.** Lifting `G.J` along `inl`.
--   Equivalent to "treat the inputs as unchanged"; the carrier
--   is now `α ⊕ ↑W` but no input is split (the LN restricts
--   `W ⊆ V`), so we copy `G.J` verbatim under `inl`. The LN's
--   `J_{spl(W)} := J` reads as the same set after identifying
--   `α` with its `inl`-image in `α ⊕ ↑W`.
--
-- * **`V_split := Sum.inl '' G.V ∪ Set.range Sum.inr`.** The
--   LN's `(V ∖ W) ⊔ W^0 ⊔ W^1` simplifies, under `W ⊆ V` and
--   our identification `w^0 := w` (0 = canonical), to
--   `V ∪ W^1` (since `(V ∖ W) ∪ W = V` when `W ⊆ V`, and
--   `W^0 = W` under the identification). Encoded:
--   `inl '' V ∪ inr '' univ`. The `inl '' V` piece carries the
--   0-copies (i.e. all of `V`, since `w^0 = w` for `w ∈ W`); the
--   `Set.range Sum.inr` piece carries the 1-copies (fresh
--   labels indexed by `↑W`).
--
-- * **`split1` helper.** The LN's "1-copy" operation `v ↦ v^1`
--   is defined by cases on `v ∈ W`. Lean expresses this
--   naturally as a `dite` (`if h : v ∈ W then Sum.inr ⟨v, h⟩
--   else Sum.inl v`), but `v ∈ W` is not in general decidable,
--   so we lift the case-split to `Classical.propDecidable`,
--   making `split1` noncomputable. This is fine because every
--   downstream use of `split1` is in a `Prop`-valued context
--   (membership of edges in the split graph). The two `@[simp]`
--   lemmas `split1_of_mem` / `split1_of_not_mem` discharge the
--   case-split at use-sites; the private `inl_eq_split1_iff`
--   characterises *when* a given `Sum.inl x` equals `split1 W u`,
--   and is the workhorse lemma of the `disjoint_EL` proof.
--   We do *not* need a `split0` helper because `v^0 := Sum.inl v`
--   has no case-split (it is the canonical embedding).
--
-- * **`E_split` as a binary union of images.**
--
--     * Piece 1: `(fun (v₁, v₂) => (split1 W v₁, Sum.inl v₂))
--       '' G.E`. Each original directed edge `(v₁, v₂) ∈ G.E`
--       relabels its source `v₁ ↦ v₁^1 = split1 W v₁` (outgoing
--       edges out of `w ∈ W` become outgoing out of `w^1`) and
--       its target `v₂ ↦ v₂^0 = Sum.inl v₂` (incoming edges into
--       `w ∈ W` become incoming into `w^0`, which is just
--       `inl w`). The `split1` dispatch lives on the source
--       only; the target needs no dispatch because the 0-copy
--       is the canonical `inl` embedding.
--     * Piece 2: `Set.range (fun w : ↑W => (Sum.inl w,
--       Sum.inr w))`. The fresh split edges `w^0 → w^1` for
--       `w ∈ W`, i.e. `(Sum.inl w, Sum.inr ⟨w, hw⟩)`.
--
--   The two pieces map one-to-one to the two `\cup`-clauses of
--   the LN's `E_{spl(W)}`.
--
-- * **`L_split` as a plain `Sum.inl × Sum.inl` image.**
--   `(fun (v₁, v₂) => (Sum.inl v₁, Sum.inl v₂)) '' G.L`. Each
--   bidirected edge `(v₁, v₂) ∈ G.L` relabels *both* endpoints to
--   their 0-copies, matching the LN's
--   `\lC v_1^0 \huh v_2^0 \st v_1 \huh v_2 \in L \rC`. Under our
--   convention (0 = `inl`), no case-split is needed -- the entire
--   relabeling is just `Sum.inl` applied to both endpoints. This
--   is the key downstream payoff of choosing the LN-aligned
--   direction: `L_subset`, `L_irrefl`, `L_symm` all collapse to
--   short two-line proofs, and the piece-2-vs-L case in
--   `disjoint_EL` is immediate (constructor mismatch).
--
-- * **Structural fields discharged in-place.** As in
--   `hardInterventionOn`, the seven CDMG obligations are short
--   consequences of the corresponding `G.*` field:
--
--     * `disjoint_JV` -- `inl '' G.J` and `inl '' G.V ∪ range inr`
--       are disjoint because `inl '' G.J ∩ inl '' G.V = ∅` (by
--       `G.disjoint_JV` + injectivity of `inl`) and
--       `inl '' G.J ∩ range inr = ∅` (different constructors).
--     * `E_subset` -- piece 1 splits source on `split1`, target
--       lands in `inl '' G.V` via `G.E_subset`; piece 2 needs the
--       precondition `hW : W ⊆ G.V` precisely to put the source
--       `Sum.inl w` into `V_split = inl '' G.V ∪ range inr`.
--     * `L_subset` -- both endpoints of a relabeled bidirected
--       edge are `Sum.inl v_i` with `v_i ∈ G.V` (by
--       `G.L_subset`), so directly in `inl '' G.V ⊆ V_split`.
--     * `L_irrefl` -- `(Sum.inl v₁, Sum.inl v₂) ∈ L_split` with
--       `Sum.inl v₁ = Sum.inl v₂` forces `v₁ = v₂` via
--       `Sum.inl_injective`; `G.L_irrefl` finishes.
--     * `L_symm` -- direct from `G.L_symm` since the relabeling
--       is symmetric in the two endpoints.
--     * `disjoint_EL` -- the two pieces of `E_split` are
--       inspected separately; piece 1 (source-dispatch image)
--       intersected with `L_split` (`Sum.inl × Sum.inl` image)
--       forces `split1 W v_1 = Sum.inl u_1` (so `v_1 ∉ W` and
--       `v_1 = u_1` via `inl_eq_split1_iff`) and
--       `Sum.inl v_2 = Sum.inl u_2`, whereupon `(v_1, v_2) ∈
--       G.E ∩ G.L` contradicts `G.disjoint_EL`; piece 2
--       (split edges, target `Sum.inr`) is *immediate* by
--       constructor mismatch -- `Sum.inr` cannot equal
--       `Sum.inl u_2` from any `L_split` membership.

/-- The *node-splitting* of the CDMG `G` with respect to a set
`W ⊆ G.V` of output nodes: the new CDMG `G_{spl(W)}` over the
carrier `α ⊕ ↑W` obtained by duplicating each `w ∈ W` into a
0-copy `Sum.inl w` (receiving incoming edges; identified with the
original `w` via the canonical `inl` embedding) and a 1-copy
`Sum.inr ⟨w, hw⟩` (fresh intervention-input label; sends outgoing
edges), with a fresh directed edge `w^0 → w^1` for each
`w ∈ W`. See `lecture-notes/lecture_notes/graphs.tex` definition
`def:G_node-splitting` (def 3.11 of the LN).

The identification direction `Sum.inl = 0-copy` (canonical) follows
the LN's own hints in def_3_11 and def_3_12 (and matches the
Richardson--Robins SWIG convention `X = X^o`); see the design
notes above.

The four `@[simp]` projection / membership lemmas
`nodeSplittingOn_J`, `nodeSplittingOn_V`, `mem_nodeSplittingOn_E`,
`mem_nodeSplittingOn_L` below characterise the four components of
the result and are the gateway for every downstream rewrite. -/
noncomputable def nodeSplittingOn (G : CDMG α) (W : Set α)
    (hW : W ⊆ G.V) : CDMG (α ⊕ ↑W) where
  J := Sum.inl '' G.J
  V := Sum.inl '' G.V ∪ Set.range (Sum.inr : ↑W → α ⊕ ↑W)
  disjoint_JV := by
    rw [Set.disjoint_left]
    rintro x ⟨j, hj, rfl⟩ hxV
    rcases hxV with ⟨v, hv, hjv⟩ | ⟨w, hjw⟩
    · cases Sum.inl_injective hjv
      exact Set.disjoint_left.mp G.disjoint_JV hj hv
    · exact nomatch hjw
  E := (fun p : α × α => (split1 W p.1, Sum.inl p.2)) '' G.E
     ∪ Set.range (fun w : ↑W => ((Sum.inl (w : α) : α ⊕ ↑W), Sum.inr w))
  E_subset := by
    rintro ⟨a, b⟩ h
    rcases h with ⟨⟨v₁, v₂⟩, hE, hab⟩ | ⟨w, hab⟩
    · -- piece 1: original edge (v₁, v₂) ∈ G.E, relabeled.
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨?_, ?_⟩
      · -- a = split1 W v₁ in J_split ∪ V_split
        by_cases hv₁ : v₁ ∈ W
        · rw [split1_of_mem hv₁]
          exact Or.inr (Or.inr ⟨⟨v₁, hv₁⟩, rfl⟩)
        · rw [split1_of_not_mem hv₁]
          rcases (G.E_subset hE).1 with hJ | hV
          · exact Or.inl ⟨v₁, hJ, rfl⟩
          · exact Or.inr (Or.inl ⟨v₁, hV, rfl⟩)
      · -- b = Sum.inl v₂ in V_split
        exact Or.inl ⟨v₂, (G.E_subset hE).2, rfl⟩
    · -- piece 2: split edge (Sum.inl w, Sum.inr w) for w ∈ ↑W.
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨?_, ?_⟩
      · -- a = Sum.inl w.val in V_split (uses hW : W ⊆ G.V)
        exact Or.inr (Or.inl ⟨(w : α), hW w.property, rfl⟩)
      · -- b = Sum.inr w in V_split
        exact Or.inr ⟨w, rfl⟩
  L := (fun p : α × α => ((Sum.inl p.1 : α ⊕ ↑W), Sum.inl p.2)) '' G.L
  L_subset := by
    rintro ⟨a, b⟩ ⟨⟨v₁, v₂⟩, hL, hab⟩
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨hv₁V, hv₂V⟩ := G.L_subset hL
    exact ⟨Or.inl ⟨v₁, hv₁V, rfl⟩, Or.inl ⟨v₂, hv₂V, rfl⟩⟩
  L_irrefl := by
    rintro a₁ a₂ ⟨⟨v₁, v₂⟩, hL, hab⟩
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    intro heq
    exact G.L_irrefl hL (Sum.inl_injective heq)
  L_symm := by
    rintro a₁ a₂ ⟨⟨v₁, v₂⟩, hL, hab⟩
    refine ⟨(v₂, v₁), G.L_symm hL, ?_⟩
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨hab.2, hab.1⟩
  disjoint_EL := by
    rw [Set.disjoint_left]
    rintro p hE ⟨⟨u₁, u₂⟩, huL, rfl⟩
    -- p has been substituted by (Sum.inl u₁, Sum.inl u₂).
    rcases hE with ⟨⟨v₁, v₂⟩, hvE, hvb⟩ | ⟨w, hvb⟩
    · -- piece 1: (split1 W v₁, Sum.inl v₂) = (Sum.inl u₁, Sum.inl u₂).
      simp only [Prod.mk.injEq] at hvb
      obtain ⟨h1, h2⟩ := hvb
      -- h1 : split1 W v₁ = Sum.inl u₁ ; h2 : Sum.inl v₂ = Sum.inl u₂.
      obtain ⟨_, hv₁u₁⟩ := inl_eq_split1_iff.mp h1.symm
      have hv₂u₂ : v₂ = u₂ := Sum.inl_injective h2
      subst hv₁u₁
      subst hv₂u₂
      exact Set.disjoint_left.mp G.disjoint_EL hvE huL
    · -- piece 2: (Sum.inl w.val, Sum.inr w) = (Sum.inl u₁, Sum.inl u₂).
      -- Target Sum.inr cannot equal Sum.inl -- immediate contradiction.
      simp only [Prod.mk.injEq] at hvb
      exact nomatch hvb.2

/-! ## `@[simp]` projection / membership lemmas

These four lemmas are the workhorses for downstream proofs that
manipulate node-split graphs. They mirror the four `@[simp]`
lemmas attached to `hardInterventionOn`. Together with the
`split1_of_mem` / `split1_of_not_mem` helpers above, they let
`simp` rewrite any membership / projection statement on
`G.nodeSplittingOn W hW` into terms of `G.J`, `G.V`, `G.E`,
`G.L` and `W` -- *without* unfolding the underlying `where`-block
of `nodeSplittingOn`. Downstream rows (claim_3_6 / claim_3_7 /
claim_3_8 / claim_3_12 and def_3_12) pattern-match against these
lemmas; rewriting them is the entry point for every later
node-splitting proof. Two design notes that apply to all four:

* **Projection form rather than `Sum.inl v ∈ ... ↔ v ∈ G.V`
  rewrites.** We expose the *whole* `J` / `V` / `E` / `L`
  components rather than a constructor-indexed family of
  membership rewrites (e.g. `Sum.inl v ∈ V_split ↔ v ∈ G.V` and
  `Sum.inr w ∈ V_split ↔ True`). The projection form is what
  `dsimp` / `Iff.rfl` can deliver from the `where`-block
  directly, and the constructor-indexed form is a one-line
  derivative of it. Downstream proofs that *do* want the
  constructor-indexed form (e.g. claim_3_7 splitting cases on
  `Sum.inl` vs. `Sum.inr`) compose this lemma with
  `Set.mem_union`, `Set.mem_image`, and `Sum.inl_injective` --
  a `simp`-trivial step.
* **Why `@[simp]`.** Marking them `@[simp]` means a single `simp`
  call inside a downstream proof unfolds `(G.nodeSplittingOn W
  hW).{J,V,E,L}` into the LN's set-builder form without
  exposing the internals of the construction. This is essential
  for the iterated-splitting proofs in claim_3_7 / claim_3_8,
  where the inner `nodeSplittingOn` should never need to be
  unfolded by hand. -/

/-- The *input* nodes of `G.nodeSplittingOn W hW` are `Sum.inl ''
G.J` -- the original input nodes embedded under `inl`. The LN's
`J_{spl(W)} := J` reads as the same set under the identification
`α ≅ inl '' α`. Used by claim_3_8 (disjoint hard interventions
and node-splittings commute) and def_3_12 (SWIG = node-split +
hard intervention) -- both quote `J_{spl(W)}` to compute the
input set of the composite. By definition. -/
@[simp] theorem nodeSplittingOn_J (G : CDMG α) (W : Set α)
    (hW : W ⊆ G.V) :
    (G.nodeSplittingOn W hW).J = Sum.inl '' G.J := rfl

/-- The *output* nodes of `G.nodeSplittingOn W hW` are
`Sum.inl '' G.V ∪ Set.range Sum.inr` -- the original output nodes
embedded under `inl` (which carries the canonical 0-copies of all
of `V`, including `W^0 = inl '' W`), plus the fresh 1-copies
`Set.range Sum.inr` (i.e. `W^1`). The LN's
`(V ∖ W) ⊔ W^0 ⊔ W^1` simplifies to this form via
`(V ∖ W) ∪ W^0 = V` (using `W^0 = W` under our identification, and
`W ⊆ V` from the precondition). Used by claim_3_6 (acyclicity of
the split graph, where the topological order ranges over
`V_{spl(W)}`), claim_3_7 (the node-set equality for the
disjoint-splittings commutation), and def_3_12 (the SWIG retains
`Sum.inl '' G.V` as its observation outputs). By definition. -/
@[simp] theorem nodeSplittingOn_V (G : CDMG α) (W : Set α)
    (hW : W ⊆ G.V) :
    (G.nodeSplittingOn W hW).V =
      Sum.inl '' G.V ∪ Set.range (Sum.inr : ↑W → α ⊕ ↑W) := rfl

/-- *Directed-edge* membership in `G.nodeSplittingOn W hW`: a pair
`p` is a directed edge of the split graph iff *either* it is the
relabeling `(split1 W v₁, Sum.inl v₂)` of some `(v₁, v₂) ∈ G.E`
(this captures the LN's first set-builder
`{v_1^1 → v_2^0 | v_1 → v_2 ∈ E}` -- the source dispatches on
`v_1 ∈ W` via `split1`, the target is always the canonical
`Sum.inl`), *or* it is a fresh split edge `(Sum.inl w.val,
Sum.inr w)` for some `w : ↑W` (this captures the LN's second
set-builder `{w^0 → w^1 | w ∈ W}`). The asymmetry source vs.
target (split1 vs. plain inl) is intentional and LN-faithful --
see the `E_split` bullet in the design block. Used by claim_3_6
(edge preservation under split), claim_3_7 / claim_3_8
(case-splitting on the two pieces of `E_split` during the
commutation proofs), and claim_3_12 / def_3_12 (the SWIG / HI
composition rewrites this membership). -/
@[simp] theorem mem_nodeSplittingOn_E (G : CDMG α) (W : Set α)
    (hW : W ⊆ G.V) {p : (α ⊕ ↑W) × (α ⊕ ↑W)} :
    p ∈ (G.nodeSplittingOn W hW).E ↔
      (∃ v₁ v₂, (v₁, v₂) ∈ G.E ∧ p = (split1 W v₁, Sum.inl v₂)) ∨
      (∃ w : ↑W, p = (Sum.inl (w : α), Sum.inr w)) := by
  change p ∈ (fun q : α × α => (split1 W q.1, Sum.inl q.2)) '' G.E
           ∪ Set.range (fun w : ↑W => ((Sum.inl (w : α) : α ⊕ ↑W), Sum.inr w)) ↔ _
  simp only [Set.mem_union, Set.mem_image, Set.mem_range, Prod.exists]
  refine or_congr ?_ ?_
  · constructor
    · rintro ⟨v₁, v₂, hE, h⟩
      exact ⟨v₁, v₂, hE, h.symm⟩
    · rintro ⟨v₁, v₂, hE, rfl⟩
      exact ⟨v₁, v₂, hE, rfl⟩
  · constructor
    · rintro ⟨w, h⟩
      exact ⟨w, h.symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩

/-- *Bidirected-edge* membership in `G.nodeSplittingOn W hW`: a
pair `p` is a bidirected edge of the split graph iff it is the
double-`inl` relabeling `(Sum.inl v₁, Sum.inl v₂)` of some
`(v₁, v₂) ∈ G.L`. This matches the LN's
`L_{spl(W)} = {v_1^0 ↔ v_2^0 | v_1 ↔ v_2 ∈ L}`. Under our
direction (0 = canonical `inl`), no case-split is needed: both
endpoints just get `inl`-lifted -- the latent confounder never
points at the 1-copy, which is the LN's deliberate choice (not an
oversight; see the `L_split` bullet in the design block). Used
by claim_3_7 (the bidirected-edge equality reduces to a
`Sum.inl × Sum.inl` image equality) and claim_3_8 (the
disjoint-HI/NS commutation needs `L_split` to compose cleanly
with the LN's `\doit(W_1)` deletion). -/
@[simp] theorem mem_nodeSplittingOn_L (G : CDMG α) (W : Set α)
    (hW : W ⊆ G.V) {p : (α ⊕ ↑W) × (α ⊕ ↑W)} :
    p ∈ (G.nodeSplittingOn W hW).L ↔
      ∃ v₁ v₂, (v₁, v₂) ∈ G.L ∧ p = (Sum.inl v₁, Sum.inl v₂) := by
  change p ∈ (fun q : α × α => ((Sum.inl q.1 : α ⊕ ↑W), Sum.inl q.2)) '' G.L ↔ _
  simp only [Set.mem_image, Prod.exists]
  constructor
  · rintro ⟨v₁, v₂, hL, h⟩
    exact ⟨v₁, v₂, hL, h.symm⟩
  · rintro ⟨v₁, v₂, hL, rfl⟩
    exact ⟨v₁, v₂, hL, rfl⟩

end CDMG

end Causality
