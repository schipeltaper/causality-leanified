# Workspace for claim_3_20 — AcyclicNonCollidersBlockable

## Role: DEPENDENT row in refactor `cdmg_typed_edges`

Pulled in because roots `def_3_1` (CDMG, now `refactor_CDMG` with `L : Finset (Sym2 Node)`) and `def_3_4` (Walk + typed `WalkStep` inductive, no stored ordered-pair) changed. The mathematical content of the LN claim is unchanged. Task = PORT the existing proof against the new upstream shapes.

## Files in scope

- `AcyclicNonCollidersBlockable.lean` — the original Lean (proof using old CDMG/Walk/IsBlockableNonCollider). Wrap old code in ORIGINAL markers; add REPLACEMENT block with new code targeting `refactor_*` upstream.
- `tex/refactor_claim_3_20_proof_AcyclicNonCollidersBlockable.tex` — must CREATE (only a stale .pdf is on disk; no .tex). Content can be near-identical to the original `tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex` (math unchanged), just update header metadata to reference the cdmg_typed_edges refactor.

## Upstream post-refactor shapes (confirmed via Explore subagent)

| Name | New decl name | Shape change relevant to this proof |
|------|---------------|---|
| `CDMG` | `refactor_CDMG` | `L : Finset (Sym2 Node)`; no `hL_symm`; `hL_irrefl` is `¬ s.IsDiag` |
| `Walk` | `refactor_Walk` | `cons` takes `(v : Node) (s : refactor_WalkStep G u v) (p : refactor_Walk G v w)` — no stored `a : Node × Node` |
| `WalkStep` | `refactor_WalkStep` | Type-level inductive with `.forwardE h`, `.backwardE h`, `.bidir h` |
| `IsDirectedWalk` | `refactor_IsDirectedWalk` | recursion: `.forwardE → recurse`, `.backwardE/.bidir → False` |
| `length`, `vertices`, `IsAcyclic` | `refactor_length`, `refactor_vertices`, `refactor_IsAcyclic` | mechanical retarget; same shape |
| `edges` | **DROPPED** — no `refactor_edges` exists; index-access proof patterns must be replaced with walk recursion / cons pattern-match |
| `Sc`, `Anc`, `Desc` | `refactor_Sc`, `refactor_Anc`, `refactor_Desc` | mechanical retarget; `Anc v = {w ∈ G ∧ ∃ p : refactor_Walk G w v, p.refactor_IsDirectedWalk}` |
| `IsCollider` | `refactor_IsCollider` | recursive on walk: `.nil → False`, `.cons _ _ .nil → False`, `cons _ _ (cons ...) at 0 → False`, `cons vk s₀ (cons _ s₁ _) at 1 → s₀.IsInto vk ∧ s₁.IsInto vk`, `cons _ _ p at k+2 → p.IsCollider (k+1)` |
| `IsNonCollider` | `refactor_IsNonCollider` | `k ≤ p.length ∧ ¬ p.IsCollider k` |
| `IsInto` (new helper) | `refactor_IsInto` | per-WalkStep: `.forwardE u→v → (w=v ∨ (s(u,v) ∈ L ∧ (w=u ∨ w=v)))`; `.backwardE u→v → (w=u ∨ (s(u,v) ∈ L ∧ ...))`; `.bidir → (w=u ∨ w=v)` |
| `IsBlockableNonCollider` | `refactor_IsBlockableNonCollider` | `IsNonCollider k ∧ (k=0 ∨ k=length ∨ HasBlockingLeftSlot k ∨ HasBlockingRightSlot k)` |
| `HasBlockingLeftSlot` (new helper) | `refactor_HasBlockingLeftSlot` | recursive: at `cons u (.backwardE _) _, 1 → u ∉ G.Sc v`; otherwise recursing or False |
| `HasBlockingRightSlot` (new helper) | `refactor_HasBlockingRightSlot` | recursive: at `cons u (.forwardE _) _, 0 → v ∉ G.Sc u`; otherwise recursing or False |

## Porting strategy

The original proof structure (Cases A: k=0, B: k=length, C: interior) ports cleanly because the disjunction shape of `refactor_IsBlockableNonCollider` is `k=0 ∨ k=length ∨ HasBlockingLeftSlot ∨ HasBlockingRightSlot` — same arms, just helpers replace the existential witness blocks.

The interior case (k ≥ 1, k < π.length) reduces by induction on π so position k of the outer walk becomes position 1 of some tail. At position 1 of `.cons vMid s₀ (.cons _ s₁ _)`, the `¬IsCollider` hypothesis is `¬(s₀.IsInto vMid ∧ s₁.IsInto vMid)`. Case-split:

* `¬ s₀.IsInto vMid`: must be `.backwardE` (other two constructors make `IsInto` True). Apply acyclicity to underlying `(vMid, u) ∈ G.E` → `u ∉ G.Sc vMid` → `HasBlockingLeftSlot 1`.
* `¬ s₁.IsInto vMid`: must be `.forwardE`. Apply acyclicity to underlying `(vMid, vNext) ∈ G.E` → `vNext ∉ G.Sc vMid` → `HasBlockingRightSlot 1`.

Acyclicity argument is unchanged from the LN: if `w ∈ Sc v_k` then prepending edge `(v_k, w) ∈ E` to a witness directed walk `w ⤳ v_k` gives a directed cycle of length ≥ 1, contradicting `refactor_IsAcyclic`. In the new shape this becomes `.cons w (.forwardE h) ρ : refactor_Walk G v_k v_k` with `refactor_IsDirectedWalk = ρ.refactor_IsDirectedWalk`.

The old `Walk.walkStep_at` / `walkStep_at_vertices` helpers (which extracted index-based vertex/edge data from the old Walk) are NOT NEEDED in the new proof — induction on the walk structure replaces them.

## Plan

1. Tex twin: create `tex/refactor_claim_3_20_proof_AcyclicNonCollidersBlockable.tex` with content near-identical to the original `tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex`. Update header comment metadata to indicate cdmg_typed_edges refactor.

2. Lean: wrap each of the 4 old private helpers AND the old `acyclic_non_colliders_blockable` theorem with `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <Name>` / `-- REFACTOR-BLOCK-ORIGINAL-END: <Name>` markers (one pair per declaration).

3. Lean: add REPLACEMENT blocks (with `refactor_` prefixed declaration names). One pair per declaration:
   * `refactor_outgoing_E_not_in_Sc` (net-new private helper — wraps the acyclicity-cycle argument once)
   * `refactor_blocking_interior_helper` (net-new private — induction on walk handling interior k ≥ 1)
   * `refactor_acyclic_non_colliders_blockable` (the main theorem; paired with the old theorem's ORIGINAL block — same `<Name>: acyclic_non_colliders_blockable`)

4. `lake build` clean.

5. Dispatch verifiers: `verify_tex_statement_plus_proof` on the twin → `verify_tex_proof` (mode prove) → eventually `solved` for the strict-equivalence gate.

## Run summaries

(none yet — first turn)
