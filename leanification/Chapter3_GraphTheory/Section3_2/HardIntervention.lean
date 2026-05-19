import Chapter3_GraphTheory.Section3_1.CDMG

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_2/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_10 — Hard intervention on CDMGs

The first definition of subsection 3.2 introduces the *hard intervention*
operator `G ↦ G_{do(W)}`: given a CDMG `G = (J, V, E, L)` and a subset
`W ⊆ J ∪ V` of nodes, build a new CDMG by

* turning every `W`-node into an input node (so `J_{do(W)} = J ∪ W`,
  `V_{do(W)} = V ∖ W`); and
* deleting every directed edge whose head lies in `W` and every
  bidirected edge with an endpoint in `W` (so
  `E_{do(W)} = E ∖ {v ⟶ w | w ∈ W}` and
  `L_{do(W)} = L ∖ {v ↔ w | w ∈ W}`).

In our typed encoding from `def_3_1` (`Section3_1/CDMG.lean`), `J` and
`V` are separate Lean types and `W` is a `Set (J ⊕ V)`. The output of
`do(W)` therefore has a **different node-type pair** to the input — this
is the main design challenge of this row, and the encoding chosen here
is what every subsequent row of Section 3.2 (`claim_3_3`, `claim_3_4`,
`def_3_11`, …) will inherit.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_2/main.tex`, under `% def_3_10`):

\begin{defmark}
\begin{Def}[Hard intervention on CDMGs]\label{def:G_hard_intervention}
    Let $G=(J,V,E,L)$ be a CDMG and $W \ins J \cup V$ a subset of nodes.
  The \emph{intervened CDMG} w.r.t.\ $W$ of $G$ is the CDMG:
  \[ G_{\doit(W)}:=(J_{\doit(W)},V_{\doit(W)},E_{\doit(W)},L_{\doit(W)}),\]
  %\[G(V\sm W|\doit(W \cup J)):=G_{\doit(W)}:=(J_{\doit(W)},V_{\doit(W)},E_{\doit(W)},L_{\doit(W)}),\]
  where:
  \begin{enumerate}[label=\roman*.)]
      \item $J_{\doit(W)}:= J \cup W$,
      \item $V_{\doit(W)}:= V \sm W$,
      \item $E_{\doit(W)}:= E \sm \lC v \tuh w \,|\, v \in G, w  \in W  \rC$,
      \item $L_{\doit(W)}:= L \sm \lC v \huh w\,|\, v \in G, w \in W \rC$,
  \end{enumerate}
  where we turn all nodes from $W$ into input nodes and remove all edges into nodes from $W$.
\end{Def}
\end{defmark}
-/

/-!
## Design choices — common to every component of `do(W)`

* **`J_doit` is `J ⊕ {v : V // Sum.inr v ∈ W}`, not a flat subtype of
  `J ⊕ V`.** The LN equation `J_{do(W)} = J ∪ W` would in principle map
  to either of two Lean encodings:

  1. `J_doit := J ⊕ {v : V // Sum.inr v ∈ W}` — the disjoint union of
     the original `J` with the `V`-part of `W`. (`W` may also intersect
     `J`, but `J ⊆ J ∪ W` already, so the `J`-part of `W` contributes
     nothing new.)
  2. `J_doit := {w : J ⊕ V // w ∈ W ∨ ∃ j, w = Sum.inl j}` — a flat
     subtype of the original node universe.

  Encoding (1) preserves the natural embedding `J ↪ J_doit = Sum.inl`,
  so the "original input nodes are still input nodes" property is
  definitional. Encoding (2) instead drags a disjunction proof around
  every original `J`-node. Since downstream rows (`claim_3_3`,
  `claim_3_4`, `def_3_13`) need to **compare** `G` and `G_{do(W)}` and
  manipulate `J`-nodes on both sides, encoding (1) is by far the
  lighter weight. The cost is one extra layer of `Sum` when mapping
  back to the original `J ⊕ V` universe (`doIt_toOld` below).

* **`V_doit` is a subtype `{v : V // Sum.inr v ∉ W}`.** The LN equation
  `V_{do(W)} = V ∖ W` is faithfully a subtype of `V`; no flexibility
  needed here.

* **Both `J_doit` and `V_doit` are `abbrev`, not `def`.** They are pure
  type aliases — every property we want about them (membership tests,
  subtype-`.val` projection, `Sum`-constructor pattern matching)
  unfolds through the alias on the nose. `abbrev` makes the unfolding
  reducible, so downstream `simp` / `rfl` / pattern matching just
  works; `def` would force every consumer to insert `unfold` calls.

* **Edges and bidirected edges are defined by *pullback along
  `doIt_toOld`*, not by set-difference.** The LN writes
  `E_doit = E ∖ {v ⟶ w | w ∈ W}` — a set-difference on `(J ⊕ V) × V`.
  In our encoding, the typing itself does the set-difference: an edge
  of `E_doit` has its target in `V_doit = V ∖ W`, so the "edges into
  `W`" cannot even be typed. We therefore take `E_doit` to be **the
  preimage of `G.E` under the coercion `doIt_toOld`** (extended to
  pairs). This is equivalent to the LN's set-difference on the nose
  and avoids threading the "target not in `W`" hypothesis through
  every edge. The same trick handles `L_doit`: bidirected edges in
  our encoding have both endpoints in `V_doit`, so any `L`-edge with
  an endpoint in `W` is untyped, matching `L_doit = L ∖ {v ↔ w |
  w ∈ W}`. (Symmetry of `G.L` upgrades the LN's one-sided filter
  "`w ∈ W`" to the symmetric "either endpoint in `W`"; the typed
  encoding mirrors that by construction.)

* **`doIt_toOld : (J_doit ⊕ V_doit) → J ⊕ V` is the one coercion every
  downstream row will use.** It sends `Sum.inl (Sum.inl j) ↦ Sum.inl
  j`, `Sum.inl (Sum.inr ⟨v, _⟩) ↦ Sum.inr v`, and `Sum.inr ⟨v, _⟩ ↦
  Sum.inr v`. The two cases that produce `Sum.inr v` are precisely
  the LN's "`v ∈ W ∩ V` is now an input" and "`v ∈ V ∖ W` is still
  an output"; both map back to the same `V`-node, which is what makes
  the LN's identification `J ∪ V = J_{do(W)} ∪ V_{do(W)}` hold
  *definitionally* in our encoding.

* **`L_symm` and `L_irrefl` are inherited verbatim from `G`.** The new
  `L_doit` is just the preimage of `G.L`, so symmetry transports
  through directly (`G.L_symm h`) and irreflexivity transports through
  the underlying-value congruence (`G.L_irrefl h ∘ congrArg
  Subtype.val`).

* **No notation `G_{do(W)}` is introduced.** Lean's parser does not
  natively support subscript-of-application notation, and the call
  site `G.doIt W` reads close enough to the LN. A future macro could
  add `G_{do(W)}` if it becomes ergonomically important.

* **The `_G : CDMG J V` parameter on `J_doit` / `V_doit` is unused
  in the body** — both type aliases only mention `J`, `V`, and `W`.
  We keep `G` as the first explicit parameter so that dot-notation
  `G.J_doit W` works for callers, matching the LN's `J_{do(W)}` which
  names `G` implicitly via the subscript. The underscore prefix
  silences the unused-variable linter.
-/

-- def_3_10 (part 1/4) — the new input-node type `J_{do(W)}`.
--
-- LN fragment: `J_{do(W)} := J ∪ W`.
--
-- See the design-choice block above for why we encode `J ∪ W` as
-- `J ⊕ (W ∩ V)` rather than as a flat subtype of `J ⊕ V`. The
-- `W ∩ V` factor is the subtype of `V` consisting of `V`-nodes that
-- got moved to input by the intervention.
abbrev CDMG.J_doit (_G : CDMG J V) (W : Set (J ⊕ V)) : Type _ :=
  J ⊕ {v : V // (Sum.inr v : J ⊕ V) ∈ W}

-- def_3_10 (part 2/4) — the new output-node type `V_{do(W)}`.
--
-- LN fragment: `V_{do(W)} := V ∖ W`.
--
-- A subtype of `V`: those `V`-nodes that the intervention does *not*
-- move to input.
abbrev CDMG.V_doit (_G : CDMG J V) (W : Set (J ⊕ V)) : Type _ :=
  {v : V // (Sum.inr v : J ⊕ V) ∉ W}

-- def_3_10 (part 3/4) — coercion of a `J_doit ⊕ V_doit`-node back to
-- the original node universe `J ⊕ V`.
--
-- Used both internally (defining `E_doit` and `L_doit` of `doIt`
-- below) and externally (downstream rows comparing `G` and
-- `G_{do(W)}`).
--
-- The three cases correspond to: "still an input", "moved from output
-- to input by the intervention", and "still an output". The latter
-- two cases both produce `Sum.inr` of the underlying `V`-node, which
-- is the LN's identification `J ∪ V = J_{do(W)} ∪ V_{do(W)}` on the
-- nose.
def CDMG.doIt_toOld (_G : CDMG J V) (W : Set (J ⊕ V)) :
    (_G.J_doit W) ⊕ (_G.V_doit W) → J ⊕ V
  | Sum.inl (Sum.inl j)      => Sum.inl j
  | Sum.inl (Sum.inr ⟨v, _⟩) => Sum.inr v
  | Sum.inr ⟨v, _⟩           => Sum.inr v

-- def_3_10 (part 4/4) — the hard-intervention operator itself.
--
-- LN fragment (the full definition, with components):
-- /- G_{do(W)} := (J_{do(W)}, V_{do(W)}, E_{do(W)}, L_{do(W)}),
--    where
--      J_{do(W)} := J ∪ W,
--      V_{do(W)} := V ∖ W,
--      E_{do(W)} := E ∖ {v ⟶ w | v ∈ G, w ∈ W},
--      L_{do(W)} := L ∖ {v ↔ w | v ∈ G, w ∈ W}. -/
--
-- The new directed edges `E_doit` are the preimage of `G.E` under
-- `doIt_toOld` (extended to pairs). Because the target of an edge in
-- the new graph must be in `V_doit = V ∖ W`, the "edges into `W`" of
-- the LN are excluded **by typing**: any directed pair `(v, w)` with
-- `w : V` and `Sum.inr w ∈ W` simply cannot be expressed as a pair of
-- the new graph's domain.
--
-- The new bidirected edges `L_doit` are likewise the preimage of `G.L`
-- under the underlying-value coercion `V_doit ↪ V` (extended to
-- pairs). Both endpoints of an `L_doit`-edge live in `V_doit`, so the
-- LN's "edges into `W`" (bidirected variant) are again excluded by
-- typing — using `G.L_symm` one promotes the LN's one-sided filter
-- to "neither endpoint in `W`", which is what our typing enforces.
--
-- `L_symm` and `L_irrefl` for the new graph are inherited from the
-- original via `G.L_symm` and `G.L_irrefl`.
def CDMG.doIt (G : CDMG J V) (W : Set (J ⊕ V)) :
    CDMG (G.J_doit W) (G.V_doit W) where
  E := { e : (G.J_doit W ⊕ G.V_doit W) × G.V_doit W |
         (G.doIt_toOld W e.1, e.2.val) ∈ G.E }
  L := { p : G.V_doit W × G.V_doit W | (p.1.val, p.2.val) ∈ G.L }
  L_symm := fun h => G.L_symm h
  L_irrefl := fun h heq => G.L_irrefl h (congrArg Subtype.val heq)

end Chapter3
end Causality
