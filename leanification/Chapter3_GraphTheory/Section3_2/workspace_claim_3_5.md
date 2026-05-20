# Workspace for claim_3_5 — BifurcationAlternative

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

---

# Manager decision (2026-05-20): Path 2, not Path 1

The plan below recommended Path 1 (tighten `Walk.bifurcationSource` in
`Section3_1/Bifurcation.lean`). The manager has chosen **Path 2** instead.

### Why not Path 1

* `bifurcationSource` is owned by **def_3_4** (item 6) — see the
  comment header at `Section3_1/Bifurcation.lean:317`. def_3_4 is a
  previously-solved row.
* The manager-side hard rule is: "Only edit files inside your row's
  subsection folder under `leanification/`." Section_3_1 is out of scope.
* The heavy `refactor` action would reset def_3_4 entirely and delete
  `Section3_1/Bifurcation.lean` — losing `IsBifurcation`,
  `BifurcationWitness`, `IsAllBackward`, `bifurcationSource`,
  `ne_of_isBifurcation`, `nil_not_isBifurcation`,
  `length_pos_of_isBifurcation`. That's a large amount of solid work
  thrown away for what is, on paper, a one-line tightening.

### What we do instead — Path 2

Encode the corner-case precondition as an extra conjunct on the LHS:

```lean
theorem bifurcation_alternative {G : CDMG α} {v w c : α} :
    (∃ π : Walk G v w, ∃ hb : π.IsBifurcation,
       π.bifurcationSource hb = some c ∧ c ≠ w)
    ↔ v ≠ w
      ∧ c ∈ Anc (G.hardInterventionOn ({w} : Set α)) v \ {v}
      ∧ c ∈ Anc (G.hardInterventionOn ({v} : Set α)) w \ {w}
```

**LN-faithfulness argument.** The LN's claim 3.5 proof prose (graphs.tex
lines 366–371) reads `v \hut \cdots \hut c \tuh \cdots \tuh w` *and*
calls the right half a "non-trivial directed path from $c$ to $w$".
"Non-trivial" is the LN's own implicit `c ≠ w`. The LN's def 3.4 item 6
("source = $v_k$ if hinge is directed") doesn't enforce it, but the
LN's claim 3.5 does — implicitly. Path 2 makes the implicit explicit at
the claim level (no change to def 3.4) instead of retroactively
tightening def 3.4 (which Path 1 would do).

**No `c ≠ v` conjunct needed.** Any `BifurcationWitness` has `bw.m' ≠ v`
because `IsBifurcation` requires `v ∉ π.support.tail` (the LN's "both
endnodes appear exactly once" clause), and `bw.m'` always sits at
position ≥ 1 in `π.support`. So `c = bw.m' ≠ v` is automatic.

**Forward-tax of Path 2.** The only future claims that have to repeat
the `c ≠ w` conjunct are *asymmetric* ones that relate "bifurcation
source" to ancestral / acyclic / topological properties of one of the
endpoints. Symmetric "source ↔ source" claims (e.g., claim_3_6's
marginalization-preserves-bifurcations) are corner-case-stable and need
no extra conjunct. So the forward-tax is small.

### Revised subtask order

* **Subtask 1** (tighten `bifurcationSource`): **dropped**.
* **Subtasks 2–7** (side-quest lemmas): relocate to Section_3_2.
  They go into `Section3_2/BifurcationAlternative.lean` as private
  helpers, or a sibling `Section3_2/BifurcationAlternativeHelpers.lean`
  if they grow. None of these need to live in Section_3_1.
* **Subtask 8** (promote `walkLiftHardInterventionOn`): keep — already
  in-scope (Section_3_2).
* **Subtask 9** (state claim_3_5): use the **Path 2** LHS above.
* **Subtasks 10–14** (TeX proof, verify, prove, simplify, comments,
  gate): unchanged in spirit. The ⟹ direction's "c ≠ w" step is now
  a direct unpack of the new LHS conjunct, no support-position
  bookkeeping needed there.

### What stays from the plan

The proof architecture (§C, §D) is largely unchanged. The side-quest
lemmas in §E are still needed; they just live in Section_3_2 instead
of Section_3_1. The walk-to-path side-quest (§E.4, the heavyweight
piece) is still the technical centerpiece of the ⟸ direction.

---

# Plan (plan_subtasks output, 2026-05-20)

## A. Statement formulation

The LN's iff (graphs.tex 361–364):
> ∃ bifurcation between $v$ and $w$ in $G$ with source $c$
> ⟺ $v \ne w$ ∧ $c \in \Anc^{G_{\doit(w)}}(v) \sm \{v\}$ ∧ $c \in \Anc^{G_{\doit(v)}}(w) \sm \{w\}$.

**Proposed Lean shape** (matches the existing `bifurcationSource` design block in `Section3_1/Bifurcation.lean` lines 50–58, 145–150 — which already committed to "`∃ π, π.IsBifurcation ∧ π.bifurcationSource = some c`" as the canonical phrasing for "bifurcation with source $c$"):

```lean
theorem bifurcation_alternative {G : CDMG α} {v w c : α} :
    (∃ π : Walk G v w, ∃ hb : π.IsBifurcation,
       π.bifurcationSource hb = some c)
    ↔ v ≠ w
      ∧ c ∈ Anc (G.hardInterventionOn {w}) v \ {v}
      ∧ c ∈ Anc (G.hardInterventionOn {v}) w \ {w}
```

### A1. Preconditions

No `hv : v ∈ G`, `hw : w ∈ G`, `hc : c ∈ G` are needed. All three are derivable:

* On the ⟹ side: π is non-trivial (`length_pos_of_isBifurcation`, already in Bifurcation.lean 395–399), so its first edge places `v ∈ G` via `G.E_subset`; symmetrically the last edge places `w ∈ G`; the hinge edge places `c ∈ G` (since hinge is backward with the underlying directed edge `c → bw.m` of `G.E`).
* On the ⟸ side: `Anc (G.hardInterventionOn {w}) v` membership requires `c ∈ G.hardInterventionOn {w} = (G.J ∪ {w}) ∪ (G.V \ {w})`, and the `\ {w}` exclusion gives `c ≠ w`, so `c ∈ G`. The set `Anc` also requires the walk to land at `v`, which combined with `v ≠ w` puts `v ∈ G`. Symmetrically `w ∈ G`.

Keep the statement clean — no explicit `hv`/`hw`/`hc`. Implicit `G`, `v`, `w`, `c` (recoverable from the conclusion).

### A2. Singleton hard intervention `{w}`

Use `G.hardInterventionOn ({w} : Set α)`. Precondition-free by `HardInterventionOn.lean`'s no-`W ⊆ G.J ∪ G.V` design (lines 88–125). For `w ∈ G`, the singleton `{w}` is automatically `⊆ G.J ∪ G.V`, so this is just a clean instantiation of def_3_10.

### A3. No helper `HasBifurcationWithSource` predicate

The existential nesting (`∃ π, ∃ hb, ...`) is one-off and only used in this row. Don't introduce an extra predicate.

### A4. ⚠ CRITICAL — Degenerate-source issue, must be resolved before stating

Under the current `bifurcationSource` (Bifurcation.lean 362–367), the claim is **literally false** as stated.

**Counterexample.** Take any walk `π = v \hut v₁ \hut … \hut v_{n-1} \hut w` (length `n ≥ 1`, all-backward, `v`, `w`, intermediate vertices pairwise distinct):

* `π.IsBifurcation` holds with the witness `bw` whose hinge is the last step (position `n-1`), `bw.m = v_{n-1}`, `bw.m' = w`, `bw.leftArm = first n-1 backward steps`, `bw.rightArm = .nil w`. Hinge is `.backward _`, so `bifurcationSource = some w`.
* So the LHS of the iff with `c = w` holds.
* But the RHS with `c = w` includes `w ∈ Anc^{G_{\doit(v)}}(w) \ {w}`, which is **false** (`w ∈ {w}`).

This is the LN's own implicit assumption: claim 3.5's prose "$v \hut \cdots \hut c \tuh \cdots \tuh w$" requires a non-empty `\tuh \cdots` block on the right (i.e., `c ≠ w`), which the LN def 3.4 item 6 doesn't enforce. The existing `bifurcationSource` is therefore *slightly looser* than the LN's claim 3.5 needs.

**Fix recommendation — Path 1 (preferred): tighten `bifurcationSource`.** One-line change to `Section3_1/Bifurcation.lean`:

```lean
noncomputable def bifurcationSource {v w : α} (π : Walk G v w)
    (hb : π.IsBifurcation) : Option α :=
  let bw := hb.2.2.2.some
  match bw.hinge, bw.rightArm with
  | .backward _, .cons _ _ => some bw.m'
  | _, _                   => none
```

Update the docstring + design block to record: "When the chosen witness's `rightArm` is trivial (LN's $k = n$ corner case), we return `none` — the LN's prose for claim 3.5 implicitly assumes `c ≠ w`, equivalently a non-trivial right arm. See the design discussion in this file's `bifurcationSource` block and `Section3_2/BifurcationAlternative.lean`."

* **Scope concern.** This is a Section_3_1 edit from a Section_3_2 row. We treat it as a *small fix* required for claim_3_5's faithfulness — analogous to the way claim_3_3's plan promoted the walk-lifting helpers to module-private. Document the LN-faithfulness rationale at the call site.
* **No downstream consumers yet**, so this is safe.
* The classical-choice non-uniqueness is unchanged (the design block on lines 138–150 of Bifurcation.lean already documents this).

**Path 2 (alternative): keep `bifurcationSource` as-is, encode `c ≠ w` in the LHS.** Replace the LHS by `∃ π hb, π.bifurcationSource hb = some c ∧ c ≠ w`. Less LN-faithful: bakes a constraint into every claim that quotes "bifurcation with source `c`" instead of fixing the source extractor once.

**Path 3 (not recommended): disprove the LN claim.** Treat the counterexample as a genuine LN defect. Inconsistent with the LN's own proof prose, which clearly *intends* the strict reading.

**→ Adopt Path 1.** First subtask of the plan (see §F).

### A5. Classical-choice ambiguity (for the ⟸ proof)

`bifurcationSource hb = some c` is checked through `hb.2.2.2.some` (a `Classical.choice`). For our constructed π in ⟸ (see §D), we'll need to argue that the BifurcationWitness of π is **unique** — i.e., any witness `bw'` must have `bw'.m' = c`. This is straightforward: in our explicit construction the hinge position is the unique transition point between all-backward steps and all-forward steps (no other split is compatible with `leftBackward` ∧ `rightDirected`). Detail in §D step 9.

## B. File layout

* **New Lean file**: `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`.
* **Aggregator update**: append `import Chapter3_GraphTheory.Section3_2.BifurcationAlternative` to `leanification/Chapter3_GraphTheory.lean`.
* **TeX**: the statement stub (`tex/claim_3_5_statement_BifurcationAlternative.tex`) already holds the verbatim claim; the proof stub (`tex/claim_3_5_proof_BifurcationAlternative.tex`) is empty and needs filling.
* **Side-quest files (Section_3_1)**:
  * Edit `Section3_1/Bifurcation.lean` (the `bifurcationSource` tightening; §A4).
  * Add walk-reversal/IsAllBackward/IsDirected interplay lemmas in `Section3_1/WalkPredicates.lean` (or `Section3_1/Bifurcation.lean` next to `IsAllBackward`). See §E.
  * Add `support_append`, possibly `support_reverse`, in `Section3_1/Walks.lean`. See §E.
  * Add walk-to-path lemma (or weaker "endpoint-only" variant) in `Section3_1/WalkPredicates.lean` (or a new `Section3_1/WalkShortening.lean` if it grows). See §E.
* **Lift up to G**: re-use the existing `walkLiftHardInterventionOn` family — recommend promoting them from `private` in `Section3_2/AcyclicUnderIntervention.lean` to public on `CDMG` namespace, so claim_3_5 (and future claim_3_8 / 3_11) can re-use. Alternative: re-derive locally. §E discusses.
* **Lift down to G_{do(W)}**: needed for ⟹ direction. Either inline structural recursion or a small public lemma. §E discusses.

## C. Proof architecture — "⟹"

Given `π : Walk G v w`, `hb : π.IsBifurcation`, `π.bifurcationSource hb = some c`.

After the §A4 tightening, `bifurcationSource hb = some c` unfolds to: letting `bw := hb.2.2.2.some`, we have `bw.hinge = .backward h` (for some `h : bw.m ⟵[G] bw.m'`), `bw.rightArm = .cons s_r p_r` for some `s_r, p_r` (non-trivial), and `bw.m' = c`.

### C1. Routine consequences

* `v ≠ w` — direct from `hb.1`.
* `c ≠ v` — `c = bw.m'` lies at position `1 + bw.leftArm.length ≥ 1` of `π.support`; combined with `v ∉ π.support.tail` (`hb.2.1`), `c ≠ v`.
* `c ≠ w` — with the tightening, `bw.rightArm.length ≥ 1`, so `bw.m'` appears at position `k := 1 + bw.leftArm.length` AND `w` appears at position `n = π.length`. If `c = w` then `bw.m'` would have to coincide with the final-position vertex; but `bw.m'` is at position `k ≤ n − 1` (since `rightArm.length ≥ 1`), so `bw.m' ∈ π.support.dropLast`, and `hb.2.2.1 : w ∉ π.support.dropLast` forces `c = bw.m' ≠ w`.
* `c ∈ G` — from the hinge edge `(c, bw.m) = (bw.m', bw.m) ∈ G.E`, apply `G.E_subset` and `CDMG.mem_iff`.

### C2. The `c ∈ Anc^{G_{\doit(w)}}(v) \ {v}` half

**Goal**: build a directed walk `A : Walk (G.hardInterventionOn {w}) c v`.

* **Step C2.1 — assemble a directed G-walk from `c` to `v`.** Define
  ```
  A_G : Walk G c v := .cons (.forward h) bw.leftArm.reverse
  ```
  using `h : c ⟶[G] bw.m` (which is the same proof as `h : bw.m ⟵[G] c` from the hinge; the relations `⟶[G]` and `⟵[G]` reduce to `(c, bw.m) ∈ G.E` definitionally, so no rewrite is needed — see the design comment in `Walks.lean` 252–254 around `reverse_forward`).
* **Step C2.2 — show `A_G.IsDirected`.** Leading step is `.forward`, so it reduces to `(bw.leftArm.reverse).IsDirected`. Use side-quest lemma `Walk.IsAllBackward → Walk.reverse.IsDirected` applied to `bw.leftBackward`. (§E)
* **Step C2.3 — show every step of `A_G` has target `≠ w`.** The leading step has target `bw.m`. The remaining steps come from `bw.leftArm.reverse`, whose support is `bw.leftArm.support.reverse` (side-quest `support_reverse`, §E). `bw.leftArm.support` traces positions `0 .. bw.leftArm.length` (= positions `0 .. k-1`) of `π.support`. Combined with `w ∉ π.support.dropLast = positions 0..n-1` (which contains `0..k-1` since `k ≤ n`), we get `w ∉ bw.leftArm.support`, hence `w` is not the target of any step in `bw.leftArm.reverse`. And `bw.m ≠ w` (also in `bw.leftArm.support`, hence not `w`).
* **Step C2.4 — restrict `A_G` to `G.hardInterventionOn {w}`.** Define a small local lift-down function (or use a public one — §E):
  ```
  walkRestrict : (π : Walk G a b) → (∀ s ∈ π.steps, s.target ∉ {w}) → Walk (G.hardInterventionOn {w}) a b
  ```
  Actually simpler: structural recursion on `A_G`, witnessing each step's target ≠ w with `mem_hardInterventionOn_E.mpr ⟨h_G, hnW⟩`. (For backward steps and bidir steps: backward step `(a ⟵[G] b)` lifts to `(a ⟵[G_{do(W)}] b)` iff `(b, a) ∈ G_{do(W)}.E` iff `a ∉ W` (`a` is the *target* of the underlying directed edge in `\hut` reading; wait, this is confusing — let me re-derive). Actually a `.backward h` in `WalkStep G a b` has `h : a ⟵[G] b` = `(b, a) ∈ G.E`. To lift to `WalkStep G_{do(W)} a b` we need `(b, a) ∈ G_{do(W)}.E`, which by `mem_hardInterventionOn_E` is `(b, a) ∈ G.E ∧ a ∉ W`. So we need `a ∉ W`, i.e., the *walk-step's target* `a` (= LN's source-of-arrow) is not in W. Hmm wait, a `.backward` step is a backward arrow; in walk-direction `a → b`, the underlying edge is `b → a`, so target *of the directed edge* is `a`, but target *of the walk step* is `b`. Confusing. Need to be careful.
  
  Actually, `mem_hardInterventionOn_E (G W) {p : α × α} : p ∈ (G.hardInterventionOn W).E ↔ p ∈ G.E ∧ p.2 ∉ W`. The `p.2` is the target of the directed edge. For `.forward h : WalkStep G v w` with `h : (v, w) ∈ G.E`, lifting requires `w ∉ W`. For `.backward h : WalkStep G v w` with `h : (w, v) ∈ G.E`, lifting requires `v ∉ W` (target of the underlying directed edge is `v`). For `.bidir h` — uses `L`, not `E`, so different (uses `mem_hardInterventionOn_L`).
  
  In our `A_G`: leading step is `.forward (h.1 : c ⟶[G] bw.m)` — target `bw.m ≠ w`, lift fine. Remaining steps come from `bw.leftArm.reverse`. `bw.leftArm.reverse`'s steps are the reverse of `bw.leftArm`'s steps. `bw.leftArm.IsAllBackward` — every step `.backward h` with `h : a ⟵[G] b` (in original direction). When reversed, this becomes `.forward h` (`WalkStep.reverse_backward`, Walks.lean 273). So `bw.leftArm.reverse` is all-forward. Each `.forward h'` step has `h' : (a, b) ∈ G.E` going from `a` to `b` in walk direction; target `b`. The `b` values trace the vertices of `bw.leftArm.support` in reverse, i.e., positions `0 .. k-1` of `π.support`. All ≠ w. ✓
* **Step C2.5 — conclude `c ∈ Anc(G_{do(w)})(v) \ {v}`.** Membership `c ∈ G_{do(w)} = G ∪ {w}`: from `c ∈ G` (C1). The directed walk = `A` (lifted via C2.4). `c ≠ v` (C1). Done.

### C3. The `c ∈ Anc^{G_{\doit(v)}}(w) \ {w}` half

Symmetric, easier because we use `bw.rightArm` directly (no reverse).

* **Step C3.1.** `bw.rightArm : Walk G c w`, IsDirected (`bw.rightDirected`).
* **Step C3.2 — every step of `bw.rightArm` has target `≠ v`.** Steps of `bw.rightArm` go through positions `k .. n` of `π.support`. The targets are positions `k+1 .. n`. All in `π.support.tail` (= positions `1..n`). `v ∉ π.support.tail` (`hb.2.1`). ✓
* **Step C3.3 — restrict to `G_{do(v)}`.** Same lift-down as C2.4, but for set `{v}` instead of `{w}`. All steps forward, target ≠ v at each step.
* **Step C3.4 — conclude.** `c ∈ G_{do(v)}` from `c ∈ G` and `c ≠ v`. Walk built. `c ≠ w` (C1). Done.

### C4. Stitch the three pieces

Trivial: ⟹ direction concludes by `⟨C1.v_ne_w, C2.5, C3.4⟩`.

**Difficulty estimate**: Medium. Bulk of the work is in the support-position bookkeeping for C2.3 / C3.2 and the lift-down construction (C2.4). Expect ~80–120 lines of Lean.

## D. Proof architecture — "⟸"

Given `v ≠ w`, `(hc_w : c ∈ Anc (G.hardInterventionOn {w}) v \ {v})`, `(hc_v : c ∈ Anc (G.hardInterventionOn {v}) w \ {w})`.

Unfold via `mem_Anc` (FamilyReachability.lean 122–125):
* `hc_w` gives `c ∈ G.hardInterventionOn {w}`, `A₀ : Walk (G.hardInterventionOn {w}) c v`, `A₀.IsDirected`, `c ≠ v`.
* `hc_v` gives `c ∈ G.hardInterventionOn {v}`, `B₀ : Walk (G.hardInterventionOn {v}) c w`, `B₀.IsDirected`, `c ≠ w`.

### D1. Shorten so `v` is only at the endpoint of `A₀` (resp. `w` for `B₀`)

`A₀` is a walk from `c` to `v`; it could revisit `v` in the interior. We need a walk `A : Walk(G_{do(w)}) c v` with `A.IsDirected` and `v ∉ A.support.dropLast`.

**Side-quest** (§E.4): a general walk-to-path lemma in `Section3_1/WalkPredicates.lean`:
```
theorem exists_isPath_of_isDirected {G : CDMG α} {a b : α}
    (p : Walk G a b) (hp : p.IsDirected) :
    ∃ q : Walk G a b, q.IsDirected ∧ q.IsPath
```
Proof: well-founded recursion on `p.length` (the manager's hint). If `p.IsPath`, done. Otherwise `p.support` has a repeat; take the first repeat at positions `i < j`, splice out the loop between them, get a strictly shorter walk with the same endpoints (and still directed because steps are unchanged). Apply IH.

(Caveat: `IsPath = support.Nodup`. The repeat-finding step needs a decidable-equality dance, since walk supports live in `List α` and we need to detect duplicates. Without `[DecidableEq α]` we can still use classical logic: `¬ Nodup → ∃ i j ...`. This is fine since `bifurcationSource` already uses classical.)

Apply to `A₀ : Walk(G_{do(w)}) c v` → get `A : Walk(G_{do(w)}) c v`, directed, `IsPath` (in particular `v` appears in `A.support` only at the last position).

Same to `B₀` → `B : Walk(G_{do(v)}) c w`, directed, `IsPath`.

### D2. Lift A, B up to G

Re-use `walkLiftHardInterventionOn` from `Section3_2/AcyclicUnderIntervention.lean`. Currently `private` (lines 92–106). **Recommendation**: promote to public (drop `private`, keep in the same file or factor out to a new `Section3_2/HardInterventionWalkLift.lean`). Re-use saves writing the same machinery twice.

After lifting:
* `A_G := walkLiftHardInterventionOn A : Walk G c v`, IsDirected (preserved by `walkLiftHardInterventionOn_isDirected`).
* `B_G := walkLiftHardInterventionOn B : Walk G c w`, IsDirected.

Key support property (preserved by lift — needs a one-line lemma `walkLiftHardInterventionOn_support : (walkLiftHardInterventionOn p).support = p.support`, immediate by induction):
* `v ∉ A_G.support.dropLast` (from `A.IsPath` + symmetric/positional reasoning, or directly: `v` only at the last position of `A.support` = `A_G.support`).
* `w ∉ A_G.support`: each step of `A` in `G.hardInterventionOn {w}` has target ≠ w (by `mem_hardInterventionOn_E`), so `w ∉ A.support.tail`. Plus `c ≠ w` means `w ≠ A.support.head = c`. So `w ∉ A.support`. ✓
* Symmetric for `B_G`: `w` only at the last position; `v ∉ B_G.support`.

### D3. Build π and the BifurcationWitness

`A_G` is non-trivial (`c ≠ v`), so we can split it as `A_G = .cons s₀ A_G'` for some leading step `s₀ : WalkStep G c m_A`, `A_G' : Walk G m_A v`. By `A_G.IsDirected`, `s₀ = .forward h` for some `h : c ⟶[G] m_A`, and `A_G'.IsDirected`.

Define:
* `leftArm := A_G'.reverse : Walk G v m_A`. By side-quest §E.2/E.3 (`IsDirected → reverse.IsAllBackward`), `leftArm.IsAllBackward`.
* `hinge := .backward h : WalkStep G m_A c`. `HasArrowheadAtSource` is `True` (`hasArrowheadAtSource_backward`, WalkPredicates.lean 160–161). ✓
* `rightArm := B_G : Walk G c w`. `IsDirected` from D2. ✓
* `decompose`: need `π = leftArm.append (.cons hinge rightArm)` where `π` is the constructed walk. **Define** `π := A_G.reverse.append B_G : Walk G v w`. Then unfold:
  `A_G.reverse = (.cons (.forward h) A_G').reverse = A_G'.reverse.append (.cons (.backward h) (.nil c))`.
  So `π = A_G'.reverse.append (.cons (.backward h) (.nil c)).append B_G`. By `append`-associativity (need a `Walk.append_assoc` lemma — likely missing, side-quest §E.5):
  `π = A_G'.reverse.append (.cons (.backward h) B_G)` (using `(.nil c).append B_G = B_G` via `nil_append`).
  Equals `leftArm.append (.cons hinge rightArm)`. ✓

### D4. The IsBifurcation predicate

Need `v ≠ w`, `v ∉ π.support.tail`, `w ∉ π.support.dropLast`, `Nonempty (BifurcationWitness π)`.

* `v ≠ w` — given.
* `Nonempty (BifurcationWitness π)` — `⟨bw_our⟩` with `bw_our` the explicit witness from D3.
* `v ∉ π.support.tail`:
  * `π.support` (using `support_append` side-quest §E.1):
    `π.support = leftArm.support.dropLast ++ (.cons hinge rightArm).support`.
    `(.cons hinge rightArm).support = m_A :: rightArm.support = m_A :: B_G.support`.
    `leftArm.support = A_G'.reverse.support = A_G'.support.reverse` (side-quest §E.6 `support_reverse`).
    `A_G' = A_G.tail` so `A_G'.support` is `A_G.support` minus the first `c` (`support_cons`-based reasoning).
  * Net: `π.support = ((A_G.support.tail).reverse).dropLast ++ (m_A :: B_G.support)`.
  * `v ∉ π.support.tail` ⟺ `v ∉ tail of the above`. Tail drops the first element, which is `v` (from `leftArm.support.head = v` — since `leftArm = A_G'.reverse : Walk G v m_A`, its support starts with `v`).
  * So need `v` not in `[remaining of leftArm.support] ++ [m_A, c, …, w]`.
    * `v ∉ leftArm.support.tail`: `leftArm.support = A_G'.support.reverse`. `A_G'.support` has `v` only at the *last* position (from D2, since `A_G.support` has `v` only at last, and `A_G' = A_G.tail` puts `A_G'.support`'s last = `A_G.support`'s last = `v`). Reversed → `v` only at position 0 of `leftArm.support`. So tail has no `v`. ✓
    * `v ∉ {m_A}`: `m_A ∈ leftArm.support`. If `m_A = v` (case `A_G.length = 1`, i.e., `A_G'` is `.nil v`, hence `m_A = v`), then `leftArm = .nil v`, `leftArm.support = [v]`, leftArm.support.tail = []. OK so degenerate but consistent.
      Actually wait: if `m_A = v`, then `bw.m = v`, leftArm = nil v, π = nil v . append (.cons hinge B_G) = .cons hinge B_G. π.support = [v, c, …, w]. tail = [c, …, w]. v ∉ tail iff v ≠ c (yes, c ≠ v) and v ∉ B_G.support (yes, D2). ✓
      Non-degenerate case `m_A ≠ v`: `m_A` appears in leftArm.support.tail (somewhere), and we just need v not to be `m_A`. Hmm, this needs more care. Actually, `m_A` appearing in support.tail is fine — we just need `v ≠ m_A` (since we're checking `v ∉ {m_A}`-type membership). And `v ≠ m_A`: if `m_A = v`, we're in the degenerate case above. Otherwise `v ≠ m_A`.
    * `v ∉ B_G.support` — from D2. ✓
* `w ∉ π.support.dropLast`:
  * `π.support.dropLast` = everything except the last element, which is `w` (last of `B_G.support`).
  * So need `w` not in `leftArm.support` ∪ `{m_A}` ∪ `B_G.support.dropLast`.
  * `w ∉ leftArm.support`: `leftArm.support = A_G'.support.reverse`. `w ∉ A_G.support` (D2) → `w ∉ A_G'.support` → `w ∉ leftArm.support`. ✓
  * `w ∉ {m_A}`: `m_A ∈ A_G.support` (it's the second vertex), and `w ∉ A_G.support`, so `m_A ≠ w`. ✓
  * `w ∉ B_G.support.dropLast`: from D2, `w` only at the last position of `B_G.support`, so not in dropLast. ✓

### D5. bifurcationSource hb = some c

After tightening per §A4: `bifurcationSource hb` matches on the chosen witness `bw_chosen = hb.2.2.2.some`. We need `bw_chosen.hinge = .backward _` ∧ `bw_chosen.m' = c` ∧ `bw_chosen.rightArm` non-trivial.

**Uniqueness argument (§A5).** Every BifurcationWitness `bw'` of π must have:
* `bw'.leftArm` all backward — possible only at the prefix of π consisting of backward steps. In our π, the backward steps occupy positions `0 .. (A_G.length − 1)` (the reversed forward-arm + the hinge become all backward steps). Forward steps occupy positions `A_G.length .. (A_G.length + B_G.length − 1)`.
* `bw'.rightArm` all forward — possible only at the suffix consisting of forward steps.
* `bw'.hinge` is the step between the all-backward prefix and the all-forward suffix.

Therefore `bw'.leftArm.length = A_G.length − 1`, `bw'.hinge.position = A_G.length − 1`, `bw'.m' = vertex at position A_G.length`. That vertex is exactly `c` (since the all-backward portion of π is `A_G.reverse`, ending at `c` at position `A_G.length`).

Hence `bw_chosen.m' = c` regardless of which witness `Classical.choice` picks. ✓

Similarly `bw_chosen.hinge = .backward h` (the only candidate) and `bw_chosen.rightArm = B_G` is non-trivial (B_G.length = B.length ≥ 1 since c ≠ w).

So `bifurcationSource hb = some c`. ✓

**Difficulty estimate**: Hard. The walk-to-path side-quest is non-trivial; the support-bookkeeping is messy; the uniqueness argument for `bifurcationSource` is delicate. Expect ~150–250 lines of Lean across the proof + side-quest files.

## E. Side-quest enumeration

In dependency order (each one a candidate subtask):

### E.1 `Walk.support_append`
```
theorem support_append {u v w : α} (p : Walk G u v) (q : Walk G v w) :
    (p.append q).support = p.support.dropLast ++ q.support
```
Lives in `Section3_1/Walks.lean`. Simple induction on `p`. Used pervasively in C/D.

### E.2 `Walk.IsAllBackward → Walk.reverse.IsDirected`
```
theorem isDirected_reverse_of_isAllBackward {v w : α} {p : Walk G v w}
    (hp : p.IsAllBackward) : p.reverse.IsDirected
```
Lives in `Section3_1/Bifurcation.lean` (next to `IsAllBackward`) or `WalkPredicates.lean`. Induction on `p`. Need a `Walk.IsDirected_append` helper:
```
theorem isDirected_append {u v w : α} {p : Walk G u v} {q : Walk G v w} :
    (p.append q).IsDirected ↔ p.IsDirected ∧ q.IsDirected
```
Then `p.reverse = p'.reverse.append (.cons s.reverse (.nil _))` for `p = .cons s p'`, etc.

### E.3 `Walk.IsDirected → Walk.reverse.IsAllBackward` (mirror of E.2)
Same shape; possibly fused with E.2 in one helper file. Needed for D3 (leftArm.IsAllBackward).

### E.4 Walk-to-path under IsDirected
```
theorem exists_isPath_of_isDirected {a b : α} (p : Walk G a b) (hp : p.IsDirected) :
    ∃ q : Walk G a b, q.IsDirected ∧ q.IsPath
```
Well-founded recursion on `p.length`. Heavyweight side-quest (the manager flagged this as the technical centerpiece). Lives in `Section3_1/WalkPredicates.lean` or a new `Section3_1/WalkShortening.lean`. Uses `support.Nodup` decidability via classical logic if needed.

Optionally weaker version: `∃ q, q.IsDirected ∧ b ∉ q.support.dropLast` (`b` only at the endpoint). Lighter to prove. Sufficient for our claim 3.5 if `IsPath` is overkill.

### E.5 `Walk.append_assoc`
```
theorem append_assoc {u v w x : α} (p : Walk G u v) (q : Walk G v w) (r : Walk G w x) :
    (p.append q).append r = p.append (q.append r)
```
Lives in `Section3_1/Walks.lean`. Standard induction on `p`.

### E.6 `Walk.support_reverse`
```
theorem support_reverse {v w : α} (p : Walk G v w) :
    p.reverse.support = p.support.reverse
```
Lives in `Section3_1/Walks.lean`. Induction on `p`, combined with `support_append` (E.1).

### E.7 Tighten `bifurcationSource` (§A4)
One-line edit to `Section3_1/Bifurcation.lean` 362–367. Update the function body, docstring, and design block. Verify no existing call sites break (`grep` confirms there are none yet).

### E.8 Promote `walkLiftHardInterventionOn` family
Drop `private` on `stepLiftHardInterventionOn`, `walkLiftHardInterventionOn`, `walkLiftHardInterventionOn_length`, `walkLiftHardInterventionOn_isDirected` in `Section3_2/AcyclicUnderIntervention.lean` 92–127. Also add a one-line lemma:
```
theorem walkLiftHardInterventionOn_support {W : Set α} {v w : α}
    (π : Walk (G.hardInterventionOn W) v w) :
    (walkLiftHardInterventionOn π).support = π.support
```
Trivial induction.

Optionally factor into a new file `Section3_2/HardInterventionWalkLift.lean` if the manager prefers separation. Keeping them in `AcyclicUnderIntervention.lean` works too — minor stylistic call.

### E.9 Down-lift (walk-restriction) helper
```
def walkRestrictHardInterventionOn (W : Set α) {a b : α} (π : Walk G a b)
    (h_steps : ∀ ⟨_, t, s⟩ ∈ π.???, t ∉ W) :
    Walk (G.hardInterventionOn W) a b
```
Or inline via structural recursion (no public helper). Inlining is cleaner if used only once.

For claim 3.5, the constraint is per-step "target ∉ W" (for the directed-edge case) and "either endpoint ∉ W" for bidir; but our A_G and B_G are all-directed so we only need the target-∉-W version.

### E.10 Decomposition lemma for `bifurcationSource hb = some c`
A one-shot helper:
```
theorem bifurcationSource_eq_some_iff {v w c : α} {π : Walk G v w}
    (hb : π.IsBifurcation) :
    π.bifurcationSource hb = some c ↔
      ∃ (m : α) (h : m ⟵[G] c) (sr : ...) (pr : ...),
        hb.2.2.2.some = ⟨m, c, _, .backward h, .cons sr pr, ..., ..., ..., ...⟩
```
Possibly too complex; might be cleaner to just `unfold bifurcationSource` and `match` inline in the proof.

## F. Subtask order

Plain numbered list. Each line is one dispatchable subtask with the worker + inputs.

1. **Tighten `bifurcationSource`** (`Section3_1/Bifurcation.lean`).
   * worker: dispatch via the manager (essentially a small `refactor_lean_code` or direct edit). No equivalent existing worker prompt matches perfectly — manager-direct edit is fine.
   * inputs: `Section3_1/Bifurcation.lean` lines 315–367 + design block. The patch is the §A4-recommended `match bw.hinge, bw.rightArm with` form. Update docstring and the design block to record the LN-faithfulness rationale.
   * rationale: claim_3_5's iff is false without this fix (see §A4 counterexample).
   * difficulty: trivial.
2. **`Walk.support_append`** (`Section3_1/Walks.lean`).
   * worker: `formalize_claim_in_lean` (treating it as a small definition / lemma row) — OR manager-direct edit if too small for a worker turn.
   * inputs: existing `support`, `append`, `support_cons`, `support_nil` lemmas in Walks.lean.
   * rationale: support of an append is used in §D4's support-bookkeeping.
   * difficulty: trivial.
3. **`Walk.support_reverse`** (`Section3_1/Walks.lean`).
   * worker: direct edit / mini-row.
   * inputs: §E.1, `reverse`, `reverse_cons`, `support_append` (subtask 2).
   * rationale: support of reverse = reversed support, needed for §D4.
   * difficulty: trivial.
4. **`Walk.append_assoc`** (`Section3_1/Walks.lean`).
   * worker: direct edit.
   * rationale: needed in §D3 to re-bracket the constructed walk.
   * difficulty: trivial.
5. **`Walk.IsDirected_append` + `IsAllBackward_append`** helpers.
   * worker: direct edit, in `Section3_1/Bifurcation.lean` (next to `IsAllBackward`) or `WalkPredicates.lean`.
   * rationale: scaffolding for subtask 6.
   * difficulty: trivial.
6. **Reverse interplay**: `isDirected_reverse_of_isAllBackward` and `isAllBackward_reverse_of_isDirected` (§E.2 + §E.3).
   * worker: direct edit / mini-row, in `Section3_1/Bifurcation.lean`.
   * inputs: subtask 5 + `WalkStep.reverse_backward` / `_forward`, existing `IsDirected` / `IsAllBackward` simp lemmas.
   * rationale: §D3's `leftArm.IsAllBackward`; §C2.2's `bw.leftArm.reverse.IsDirected`.
   * difficulty: small, but needs care with the inductive shape (`reverse` of `cons` is `append`, so the append helpers from subtask 5 are necessary).
7. **Walk-to-path under IsDirected (§E.4)**.
   * worker: `formalize_claim_in_lean` then `prove_claim_in_lean` (full row treatment, since it's non-trivial), in a new `Section3_1/WalkShortening.lean` file (or appended to `WalkPredicates.lean`).
   * inputs: `Walk.length`, `Walk.support`, `Walk.IsDirected`, `Walk.IsPath`, `List.Nodup` Mathlib API, well-founded recursion idiom.
   * rationale: the technical centerpiece of §D1.
   * difficulty: hard. The repeat-finding step needs care.
   * **Optional simplification**: prove the weaker "`b ∉ q.support.dropLast`" version only. Lower difficulty.
8. **Promote `walkLiftHardInterventionOn`** + add `_support` lemma (§E.8).
   * worker: direct edit in `Section3_2/AcyclicUnderIntervention.lean` (drop `private`, add the support lemma) — or factor to `Section3_2/HardInterventionWalkLift.lean`.
   * rationale: re-use the up-lift; avoid duplicating machinery.
   * difficulty: trivial.
9. **State claim_3_5** in `Section3_2/BifurcationAlternative.lean`.
   * worker: `formalize_claim_in_lean`.
   * inputs: claimmark text (statement TeX already in place), §A's proposed shape, `mem_Anc`, `hardInterventionOn`, `bifurcationSource` (tightened, subtask 1).
   * rationale: pin the statement before the proof; standard `formalize_claim_in_lean` flow.
   * difficulty: small. Body = `sorry`.
10. **Write TeX proof sketch** (`tex/claim_3_5_proof_BifurcationAlternative.tex`).
    * worker: `write_tex_proof` (or `expand_tex_proof` if the stub is reframed).
    * inputs: LN proof at graphs.tex 366–371; the §C and §D architectures above; subtask references to side-quest lemmas.
    * rationale: standard pipeline — TeX proof before Lean proof, per `write_tex_proof`'s mandate.
    * difficulty: medium. Need to translate the LN's compact prose into a multi-paragraph proof that names the Lean constructs (BifurcationWitness, hardInterventionOn, Anc, walk-shortening, etc.) without writing Lean syntax.
11. **Verify TeX proof** via `verify_tex_proof`.
12. **Prove claim_3_5 in Lean** (subtask 9's `sorry` → real proof).
    * worker: `prove_claim_in_lean`.
    * inputs: the TeX proof (subtask 10), all side-quest lemmas (subtasks 2–8).
    * rationale: standard pipeline.
    * difficulty: hard. Estimated ~150–250 lines.
13. **`add_design_choice_comments`** on the new file.
14. **`verify_row_solved`** + `mark_solved`.

The order above respects dependencies: tighten `bifurcationSource` first (subtask 1, since the statement depends on it); then the walk-data lemmas (subtasks 2–6) which the proof needs; then the harder walk-shortening (subtask 7); then the up-lift promotion (subtask 8); then the claim statement (subtask 9), TeX proof (10), TeX verify (11), Lean proof (12), comments (13), gate-verify (14).

A future manager handoff could batch subtasks 2–6 into one direct-edit round (they're all 5–15 line additions to existing files) to save dispatches.

## Confidence summary

The plan is high-confidence on the math: the LN's proof structure ports cleanly into Lean once the walk-data infrastructure (support_append, reverse interactions, walk-shortening) is in place. The two genuinely tricky pieces are (a) the **degenerate-source issue** (§A4), which requires a small but-load-bearing edit to `Section3_1/Bifurcation.lean` and which I strongly recommend the manager dispatches as the first subtask; and (b) the **walk-to-path side-quest** (§E.4 / subtask 7), which is the kind of well-founded-recursion lemma that's standard in Mathlib's `SimpleGraph.Walk` but absent from this project, so we have to build it ourselves. The remaining components — support manipulations, reverse-IsDirected interplay, up-lifting and down-lifting between `G` and `G_{do(W)}` — are all routine inductions, ~5–20 lines each. The Lean proof of claim_3_5 itself will be verbose (mostly support-bookkeeping for the IsBifurcation predicate's "v ∉ tail / w ∉ dropLast" conditions in both directions) but mechanical once the side-quests are in hand.

