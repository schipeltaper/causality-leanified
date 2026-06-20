# Workspace for claim_3_23 — SigmaOpenPathsWalks

## Turn 1 (2026-06-20) — manager analysis, decision: reorder

**Claim**: `Prp~\ref{prp:sigma_opens}` (`graphs.tex` line 1384) — for a CDMG `G`,
`C ⊆ J ∪ V`, and `w_1, w_2 ∈ J ∪ V`, the three existence claims (∃ `C`-σ-open
path; ∃ `C`-σ-open walk; ∃ `C`-σ-open walk with all colliders in `C`) are
equivalent.

**LN proof structure** (`graphs.tex` line 1655–1673):
- `3 ⟹ 2`, `1 ⟹ 2` trivial (paths are walks; (3) is a strengthening of (2)).
- `2 ⟹ 3`: collider-pull-into-`C` argument by extending each non-`C` collider
  via the directed path to its `C`-anchor and back. Self-contained.
- `2 ⟹ 1`: invokes **`Lemma~\ref{lem:replace_walk}`** (our `claim_3_27`) to
  iteratively contract repeated-SCC subwalks of a σ-open walk into directed
  paths inside the SCC, decreasing the multiplicity of repeated vertices until
  the walk is a path. This is the load-bearing direction.

**Prerequisite**: `claim_3_27` (`lem:replace_walk`, currently titled
"LabelRoman" in our data.json) is unsolved (`formalized=no`, `solved=no`).
Without it the proof has no clean Lean discharge — the replace_walk lemma is
an entire sub-argument with its own case analysis (fork / right-chain hinge
vs. collider-on-the-way) and reproducing it inline would dwarf the rest of
the proof.

**Order in LN itself**: the LN states `Prp~\ref{prp:sigma_opens}` first (line
1384) via `\begin{restatable}`, then later defines `Lem~\ref{lem:replace_walk}`
(line 1620), then proves the proposition via `\restateprpsigmaopens*` (line
1655). So the LN's *proof order* is already `replace_walk` → `prp:sigma_opens`,
matching the reorder request.

**Dependency check on `claim_3_27`**: needs `def_3_17` (σ-open walks; done),
`def_3_15` (collider / non-collider; done), `Sc^G` / `Anc^G` from `def_3_5`
(in `FamilyRelationships.lean`; done). No transitive dependency on `claim_3_23`
or any in-between row (`claim_3_24-26`), all of which come *after* `claim_3_23`
in solving order anyway.

**Decision**: emit `reorder PRECEDES: claim_3_27`. Reorder verifier should
PASS on the LN-proof citation evidence above.
