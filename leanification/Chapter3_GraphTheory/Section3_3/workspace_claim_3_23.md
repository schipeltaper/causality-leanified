# Workspace for claim_3_23 — SigmaOpenPathWalk

## The LN block (statement only — proof appears LATER in the LN at line 1655)

> Let $G=(J,V,E,L)$ be a CDMG. For $C \subseteq J \cup V$, and $w_1, w_2 \in J \cup V$, the following are equivalent:
> 1. there exists a $C$-$\sigma$-open **path** between $w_1$ and $w_2$ in $G$;
> 2. there exists a $C$-$\sigma$-open **walk** between $w_1$ and $w_2$ in $G$;
> 3. there exists a $C$-$\sigma$-open **walk** between $w_1$ and $w_2$ in $G$ such that all its colliders lie in $C$ (and not just in $\Anc^G(C)$).

## Infrastructure already in place

- `Walk G v w` (Section3_1/Walks.lean), with `support`, `length`, `nodeAt`
- `Walk.IsPath π : Prop` := `π.support.Nodup` (Section3_1/WalkPredicates.lean)
- `Walk.IsSigmaOpen π C : Prop` and `Walk.IsSigmaBlocked π C : Prop` (Section3_3/SigmaBlockedWalks.lean)
- `Walk.IsColliderAt π k : Prop` (Section3_3/CollidersAndNon.lean) — gives the LN's "$v_k$ is a collider on $\pi$"
- `Walk.IsBlockableNonColliderAt π k : Prop` (Section3_3/BlockableAndUnblockable.lean)
- `CDMG.AncSet G C : Set α` (Section3_1/FamilyReachability.lean) — the LN's $\Anc^G(C)$
- `CDMG.IsISigmaSeparated G A B C` (Section3_3/ISigmaSeparation.lean) — the principal separation predicate

## Statement-level formalization sketch

The Lean statement is a three-way `Iff` packaged as one or more `theorem`s. The cleanest LN-faithful shape is

```lean
theorem sigma_opens (G : CDMG α) (C : Set α) (w₁ w₂ : α) :
    (∃ (π : Walk G w₁ w₂), π.IsPath ∧ π.IsSigmaOpen C) ↔
    (∃ (π : Walk G w₁ w₂), π.IsSigmaOpen C) ↔
    (∃ (π : Walk G w₁ w₂), π.IsSigmaOpen C ∧
       ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) := by sorry
```

— except Lean's `↔` doesn't chain like that. Two natural splits:

(A) Two separate biconditionals: `sigma_open_path_iff_walk` and `sigma_open_walk_iff_all_colliders_in_C`. Mirrors the LN's two non-trivial proof steps ($2 \Leftrightarrow 1$ and $2 \Leftrightarrow 3$).

(B) One `theorem ... := And.intro / TFAE` packing all three. The Mathlib idiom is `List.TFAE`.

Decision deferred to the formalizer; the `review_design` verifier will sanity-check.

## Critical dependency

The LN's proof of $2 \implies 1$ uses `lem:replace_walk` (claim_3_27, title "LabelRoman") — a major lemma stating that on a σ-open walk, you can replace any subwalk between two same-strongly-connected-component nodes by a directed path, preserving σ-openness. claim_3_27 sits **AFTER** claim_3_23 in our `data.json`.

For the **statement** phase (current manager) this is not a blocker — we only need the Lean statement, and the body can be `sorry`. The Manager-B prover will need to either reorder claim_3_27 before claim_3_23, or push forward on the statement plus the $1 \Leftrightarrow 2$ direction first.

## Plan

1. `spawn_agent_sub_task` → `formalize_claim_in_lean.md` to write the Lean statement (with `sorry`).
2. `review_design` — full-LN-context check of the Lean shape.
3. `verify_equivalence` — focused statement-vs-LN check.
4. `add_design_choice_comments`.
5. `new_manager` — handoff to the proof phase, flagging the claim_3_27 / `lem:replace_walk` dependency.

## Run log

### Run 1 — statement-phase manager (2026-05-27)

Statement-phase completed. The Lean shape that PASSed `review_design` and `verify_equivalence` is:

```lean
theorem sigmaOpens_TFAE (G : CDMG α) (C : Set α) (w₁ w₂ : α) :
    List.TFAE
      [ (∃ π : Walk G w₁ w₂, π.IsPath ∧ π.IsSigmaOpen C),
        (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C),
        (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C ∧
          ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) ] := by
  sorry
```

Key design choices (captured in the comment block of the Lean file before reset, also reasoned through in workspace history):

- `List.TFAE` over alternatives (chained `Iff`, two separately-named biconditionals, bundled `∧` of bicons) — wins on LN-faithful "the following are equivalent" surface, on consumer ergonomics via `.out i j`, and on `tfae_have`/`tfae_finish` tactic support.
- Clause order matches LN literal: (1) path, (2) walk, (3) walk-with-colliders-in-$C$ ↔ list indices 0, 1, 2. Downstream consumers (`claim_3_24`, `claim_3_25`, `claim_3_28`) cite by clause number; reordering would break the citation pattern.
- All three clauses inlined as `∃ π : Walk G w₁ w₂, ...`; no auxiliary `IsSigmaOpenPath` / `IsSigmaOpenWalkAllCollidersIn` predicates (single-use, would require unfold on every consumer).
- `G : CDMG α` first (dot-projection), then `C`, then `w₁ w₂` (explicit, Unicode subscripts to mirror LN's $w_1, w_2$).
- Clause 3 uses `π.nodeAt k ∈ C` (vs `∈ G.AncSet C` for clause 2's `IsSigmaOpen`) — the strengthening is the *only* difference between clauses 2 and 3.
- `Walk.nil`-vacuity arguments justified that `w₁, w₂ ∈ G.J ∪ G.V` does not need to be a type-level guard.
- Name `sigmaOpens_TFAE`: LN's `prp:sigma_opens` camelCases to `sigmaOpens`, `_TFAE` is the Mathlib convention (cf. `t1Space_TFAE`).

### Run 2 — proof-phase manager (this run, 2026-05-27)

**Decision: reorder.** The LN's proof of `prp:sigma_opens` (lines 1655–1673 of `graphs.tex`) is structured as:
- `3 → 2`, `1 → 2`: trivial (paths are walks)
- `2 → 3`: collider-replacement via a directed path to $C$ and back. Uses walk-splicing primitives, the `AncSet` definitional content, but **not** `lem:replace_walk`.
- `2 → 1`: **explicitly invokes `lem:replace_walk`** (LN line 1669: "We now use Lemma~\ref{lem:replace_walk}…"). `lem:replace_walk` is claim_3_27 (`LabelRoman`) in our `data.json`.

The LN itself proves `lem:replace_walk` at lines 1620–1652, *immediately before* the proof of `prp:sigma_opens` at 1655–1673. Our data.json ordering put claim_3_23 (line 1382 statement) before claim_3_27 (line 1620 lemma) because it followed statement-declaration order, not proof-dependency order. The reorder restores LN-faithful proof-dependency order.

claim_3_27 itself does not depend on claim_3_23, 24, 25, or 26 — its proof analyzes the structure of a modified walk using def_3_17 (`IsSigmaOpen`), `Sc^G`, `Anc^G`, and basic collider/non-collider definitions, all of which are already in place. So claim_3_27 can be lifted ahead of claim_3_23 safely.

Issuing `reorder` with `PRECEDES: claim_3_27`. After reorder PASS, claim_3_27 will be solved first, then this row will be picked back up — the formalizer should recreate the `sigmaOpens_TFAE` shape above on the first pass (design analysis is in this workspace), and the prover can leanify the tex proof we have not yet written (the LN proof at 1655–1673 is the source — a TeX writer should copy it).
