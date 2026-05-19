import Chapter3_GraphTheory.Section3_1.CDMG

-- The verbatim TeX source of the LN notation block is reproduced below; some
-- of its lines exceed 100 characters. Disable the style linter for this file
-- so the TeX is kept byte-for-byte identical to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_2 — Notation for CDMGs

The lecture notes introduce seven shorthand notations for talking about a CDMG
`G = (J, V, E, L)` (see `def_3_1` / `Section3_1/CDMG.lean`):

1. `v ∈ G`     — node membership;
2. `v₁ ⟶ v₂` (`tuh`)  — directed edge in `E`;
3. `v₁ ⟵ v₂` (`hut`)  — reversed directed edge in `E`;
4. `v₁ ↔ v₂` (`huh`)  — bidirected edge in `L`;
5. `v₁ \suh v₂` — `tuh` or `huh`;
6. `v₁ \hus v₂` — `hut` or `huh`;
7. `v₁ \sus v₂` — `tuh` or `hut` or `huh`.

The star in `\suh`, `\hus`, `\sus` stands for "arrowhead or tail".

This file is `def_3_2` of the data file (part 2/2 of `Section3_1` so far).
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_2`):

\begin{defmark}
\begin{Not}
    \label{not-cdmg}
    Let $G=(J,V,E,L)$ be a CDMG.
    We will write:
    \begin{enumerate}
        %\item $G(V|\doit(J))$ to represent the graph $(J,V,E,L)$, where $E$ and $L$ are kept implicit in this notation.
        \item $v \in G$ to mean $v \in J \cup V$,
        \item $v_1 \tuh v_2 \in G$ to mean $(v_1,v_2) \in E$,
        \item $v_1 \hut v_2 \in G$ to mean $(v_2,v_1) \in E$,
        \item $v_1 \huh v_2 \in G$ to mean $(v_1,v_2) \in L$,
        \item $v_1 \suh v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$ or $v_1 \huh v_2 \in G$,
        \item $v_1 \hus v_2 \in G$ to mean that either $v_1 \hut v_2 \in G$ or $v_1 \huh v_2 \in G$,
        \item $v_1 \sus v_2 \in G$ to mean that either $v_1 \tuh v_2 \in G$ or $v_1 \hut v_2 \in G$ or $v_1 \huh v_2 \in G$.
    \end{enumerate}
    The star stands for a placeholder to mean: ``arrowhead or tail''.
\end{Not}
\end{defmark}
-/

/-!
## Design choice — typing of the composite arrows `suh`, `hus`, `sus`

`tuh` and `hut` allow one endpoint in `J ∪ V` (because `E ⊆ (J ∪ V) × V`), but
`huh` requires both endpoints in `V` (because `L ⊆ V × V`). The composites of
the LN take "either of those" as their meaning, so we have to pick a uniform
Lean type for each composite.

We give all three composites the type `(J ⊕ V) → (J ⊕ V) → Prop`, i.e. uniform
endpoints in `J ⊕ V` (Lean's encoding of `J ∪ V`, per `def_3_1`). For each
composite, the `huh` disjunct fires only when both endpoints happen to be in
`V` (`Sum.inr`), and the `tuh` / `hut` disjuncts fire only when the appropriate
endpoint is in `V` (since `E` has codomain in `V`). We encode that with
`Sum.inr` existentials; LN-illegal arrows (e.g. `j ↔ v` with `j ∈ J`) end up
identically `False`, which is exactly the property `claim_3_1` will use.

Why uniform `J ⊕ V` and not uniform `V`:

* `claim_3_1` writes `j \hus v ∉ G` with `j ∈ J` — so the *type* of `\hus`
  must accept a `J`-endpoint, otherwise the LN statement does not even type-
  check in Lean.
* `def_3_3` calls two nodes `v₁`, `v₂` of `G` *adjacent in `G`* iff
  `v₁ \sus v₂`; nodes of `G` live in `J ⊕ V`, so adjacency must accept any
  pair in `J ⊕ V`.
* `def_3_4` defines walks whose vertices live in `J ⊕ V`, with `\sus`-style
  adjacency between consecutive nodes — a uniform `J ⊕ V` composite is exactly
  the per-step predicate we need.

We keep `tuh`, `hut`, `huh` with their *strict* types (the codomain of `E`
and `L` constrains the second / first / both endpoints to `V`). This way each
of the three "primitive" arrows is a direct membership test in the underlying
set, which is the lightest weight for proofs; the composites do the lifting to
`J ⊕ V` once and for all.

We do **not** introduce Lean `notation` for the arrows: the unicode arrows
`→`, `↔`, `←` would clash with core / mathlib symbols, and bracketed forms
like `v₁ ⟶[G] v₂` add parser surface without buying much over plain function
calls `G.tuh v₁ v₂`. Downstream code can still read close to the LN.
-/

-- def_3_2 (part 1/7) — `v ∈ G` for `v : J ⊕ V`.
--
-- LN item: "`v ∈ G` to mean `v ∈ J ∪ V`".
--
-- Since `def_3_1` encodes `J ∪ V` as `J ⊕ V` *at the type level*, every term
-- of type `J ⊕ V` is "in `G`" by construction — there is no propositional
-- content. We register a `Membership` instance whose body is `True` so that
-- `v ∈ G` parses and the downstream LN statements (`def_3_3` adjacency,
-- `def_3_4` walks, …) can be written as in the lecture notes.
--
-- Design choice: returning `True` here is *not* a placeholder. The honest
-- alternative — refusing to introduce a `Membership` instance and forcing
-- every LN occurrence of `v ∈ G` to be rephrased — would make the Lean text
-- drift away from the lecture notes without adding any information.
instance : Membership (J ⊕ V) (CDMG J V) where
  mem _ _ := True

-- def_3_2 (part 2/7) — directed edge `v₁ ⟶ v₂` ("tail-to-head", `\tuh`).
--
-- LN item: "`v₁ \tuh v₂ ∈ G` to mean `(v₁, v₂) ∈ E`".
--
-- Source `v₁` is in `J ⊕ V`, target `v₂` is in `V` — exactly the domain of
-- `G.E`, so this is definitionally an `E`-membership.
def CDMG.tuh (G : CDMG J V) (v₁ : J ⊕ V) (v₂ : V) : Prop :=
  (v₁, v₂) ∈ G.E

-- def_3_2 (part 3/7) — reversed directed edge `v₁ ⟵ v₂` ("head-to-tail",
-- `\hut`).
--
-- LN item: "`v₁ \hut v₂ ∈ G` to mean `(v₂, v₁) ∈ E`".
--
-- Same underlying data as `tuh`; the LN convention is that arrowheads in the
-- macro name sit on `v₁`. So here `v₂` is the source (in `J ⊕ V`) and `v₁`
-- is the target (in `V`).
def CDMG.hut (G : CDMG J V) (v₁ : V) (v₂ : J ⊕ V) : Prop :=
  (v₂, v₁) ∈ G.E

-- def_3_2 (part 4/7) — bidirected edge `v₁ ↔ v₂` ("head-to-head", `\huh`).
--
-- LN item: "`v₁ \huh v₂ ∈ G` to mean `(v₁, v₂) ∈ L`".
--
-- Both endpoints lie in `V`, matching `G.L : Set (V × V)`. Symmetry of the
-- relation is *not* baked into the definition (we mirror the LN's chosen
-- ordered-pair representative); it is delivered separately by `G.L_symm`
-- of `def_3_1`.
def CDMG.huh (G : CDMG J V) (v₁ v₂ : V) : Prop :=
  (v₁, v₂) ∈ G.L

-- def_3_2 (part 5/7) — composite arrow `\suh` ("tuh or huh", arrowhead on
-- `v₂`).
--
-- LN item: "`v₁ \suh v₂ ∈ G` to mean that either `v₁ \tuh v₂ ∈ G` or
-- `v₁ \huh v₂ ∈ G`".
--
-- Typing: `(J ⊕ V) → (J ⊕ V) → Prop` (see the design-choice block above).
-- The `tuh` disjunct fires only when `v₂` is in `V`; the `huh` disjunct fires
-- only when both are in `V`. Both restrictions are enforced via `Sum.inr`
-- existentials.
def CDMG.suh (G : CDMG J V) (v₁ v₂ : J ⊕ V) : Prop :=
  (∃ w₂ : V, v₂ = Sum.inr w₂ ∧ G.tuh v₁ w₂) ∨
  (∃ w₁ w₂ : V, v₁ = Sum.inr w₁ ∧ v₂ = Sum.inr w₂ ∧ G.huh w₁ w₂)

-- def_3_2 (part 6/7) — composite arrow `\hus` ("hut or huh", arrowhead on
-- `v₁`).
--
-- LN item: "`v₁ \hus v₂ ∈ G` to mean that either `v₁ \hut v₂ ∈ G` or
-- `v₁ \huh v₂ ∈ G`".
--
-- Symmetric to `suh` (arrowhead-on-`v₁` instead of arrowhead-on-`v₂`).
-- This is the predicate that `claim_3_1` will show is `False` whenever
-- `v₁ ∈ J` (no arrowheads can point into a `J`-node).
def CDMG.hus (G : CDMG J V) (v₁ v₂ : J ⊕ V) : Prop :=
  (∃ w₁ : V, v₁ = Sum.inr w₁ ∧ G.hut w₁ v₂) ∨
  (∃ w₁ w₂ : V, v₁ = Sum.inr w₁ ∧ v₂ = Sum.inr w₂ ∧ G.huh w₁ w₂)

-- def_3_2 (part 7/7) — composite arrow `\sus` ("tuh or hut or huh",
-- arrowheads on *either* side).
--
-- LN item: "`v₁ \sus v₂ ∈ G` to mean that either `v₁ \tuh v₂ ∈ G` or
-- `v₁ \hut v₂ ∈ G` or `v₁ \huh v₂ ∈ G`".
--
-- This is the adjacency predicate `def_3_3` will name. Per the design-choice
-- block, downstream definitions (`def_3_3` adjacency, `def_3_4` walks)
-- consume `sus` on `J ⊕ V` directly.
def CDMG.sus (G : CDMG J V) (v₁ v₂ : J ⊕ V) : Prop :=
  (∃ w₂ : V, v₂ = Sum.inr w₂ ∧ G.tuh v₁ w₂) ∨
  (∃ w₁ : V, v₁ = Sum.inr w₁ ∧ G.hut w₁ v₂) ∨
  (∃ w₁ w₂ : V, v₁ = Sum.inr w₁ ∧ v₂ = Sum.inr w₂ ∧ G.huh w₁ w₂)

end Chapter3
end Causality
