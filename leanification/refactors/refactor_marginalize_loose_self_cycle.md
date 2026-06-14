# Refactor plan: marginalize_loose_self_cycle

**Status:** proposed (not yet executed)
**Date:** 2026-06-13
**Root ref:** def_3_14 (MarginalizationAK)
**Root chapter:** 3
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_marginalize_loose_self_cycle

## Why this refactor is needed

The current formalisation of `def_3_14` (marginalisation a.k.a. latent projection on CDMGs) tightens the LN's directed-walk-through-`W` predicate `Φ_E` with a self-cycle length restriction that the LN itself does *not* impose. The strict clause lives at two coordinated sites:

- `leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_14_MarginalizationAK.tex` clause (iii)(d) (line 40) plus its footnote at line 42 and the bottom "Asymmetry between (iii) and (iv)" paragraph at lines 75-81 (the part that reads "directed self-cycles … may appear in $E^{\sm W}$, but *only* when witnessed by a directed walk of length $\ge 2$ through $W$").
- `leanification/Chapter3_GraphTheory/Section3_2/MarginalizationAK.lean` predicate `MarginalizationΦE` at line 199-204, specifically the conjunct `(u = v → p.length ≥ 2)`.

The LN (`lecture-notes/lecture_notes/graphs.tex` lines 945-948) reads simply: "$E^{\sm W}$ consists of all directed edges $\ul{v} \tuh \ol{v}$ with $\ul{v},\ol{v} \in J \cup V \sm W$ for which there exists a directed walk in $G$: $\ul{v} \tuh w_1 \tuh \cdots \tuh w_{n-1} \tuh \ol{v}$, where all intermediate nodes $w_1,\dots,w_{n-1} \in W$ (if any).\footnote{Note that this may introduce self-cycles.}" — no length restriction on the self-cycle case. The restriction was added during chapter-init under the `[self_cycle_asymmetry_between_directed_and_bidirected]` block of `addition_to_the_LN` for `def_3_14` in `Chapter3_GraphTheory/data.json` (line 1821 of the data.json), and *was not* one of the subtleties surfaced by the row's `wording_check` (which flagged the asymmetry of (iii) vs. (iv) on self-edges in `L^{\sm W}` only — that asymmetry, `\ul{v} \neq \ol{v}` enforced on `L^{\sm W}` but not on `E^{\sm W}`, is legitimately load-bearing and stays).

The strict clause breaks two LN-intended properties of marginalisation:

**Pathology 1 — $G^{\sm \emptyset} \neq G$.** Under the strict def, a self-loop $(v,v) \in E$ requires a length-$\ge 2$ walk through $W$ to be preserved into $E^{\sm W}$. With $W = \emptyset$ there are no intermediates available, so length-$\ge 2$ walks through $W$ do not exist; hence $(v,v) \notin E^{\sm \emptyset}$ even though $(v,v) \in E$. Marginalisation with the empty set is no longer the identity on graphs that have any self-loop. This contradicts the LN's clean reading of $W = \emptyset$ as a no-op, which `claim_3_17`'s rewritten statement file already silently invokes at line 31: "(def \ref{def:G_marginalization} explicitly admits the $W = \emptyset$ input, in which case $G^{\sm \emptyset} = G$ verbatim by items~i.--iv.\ of that def)".

**Pathology 2 — `claim_3_17` (`MarginalizationsCommute`, this row's parent) is FALSE under the strict def.** Concrete counterexample (independently reproduced by the manager's verifier):
- $G = (J=\emptyset,\, V=\{v,w\},\, E=\{(v,w),(w,v)\},\, L=\emptyset)$, with $W_1=\{w\}$ and $W_2=\emptyset$.
- $E^{\sm W_1}$ contains $(v,v)$: the length-2 walk $v \to w \to v$ has intermediate $w \in W_1$ and length $\ge 2$, satisfying clause (iii)(d).
- $E^{\sm (W_1 \cup W_2)} = E^{\sm W_1}$ also contains $(v,v)$.
- $(E^{\sm W_1})^{\sm W_2} = (E^{\sm \{w\}})^{\sm \emptyset}$: for $(v,v)$ to be here, we need a length-$\ge 2$ walk in $G^{\sm W_1}$ with intermediates in $\emptyset$ — impossible. So $(v,v) \notin (E^{\sm W_1})^{\sm W_2}$.
- Hence $(E^{\sm W_1})^{\sm W_2} \subsetneq E^{\sm (W_1 \cup W_2)}$ on this $(G, W_1, W_2)$, so the LN's triple equality fails as a theorem.

The current `claim_3_17` row is in a state where its statement file has been written and its LN-faithful proof has been ported verbatim to `tex/claim_3_17_proof_MarginalizationsCommute.tex` (the LN's own `\Claude{}` proof at `graphs.tex` lines 1006-1118). Both are accurate against the LN, but the underlying `def_3_14`'s strict clause makes the LN proof's "$G^{\sm \emptyset}$ behaves trivially" implicit step false in the formalisation. The Lean theorem at `MarginalizationsCommute.lean:294-304` is `:= sorry`, and it cannot be closed without weakening `def_3_14` (or adding ugly side conditions on $W = \emptyset$ to every downstream marginalisation lemma — see "Why not the alternative" below).

A refactor of `def_3_14` — rather than a row-level workaround in `claim_3_17` — is the right scope: the divergence lives in the foundational definition, every downstream marginalisation lemma in chapter 3 (`claim_3_18`, `claim_3_19`, and any subsequent chapter that consumes latent projections) implicitly assumes the LN's clean $G^{\sm \emptyset} = G$ reading, and the strict clause was an `addition_to_the_LN` choice that the LN itself does not endorse (its footnote "Note that this may introduce self-cycles" is the LN explicitly *welcoming* self-cycles in $E^{\sm W}$, with no caveat on the length-1 case).

## Proposed new shape

Drop the self-cycle length conjunct from `MarginalizationΦE` and the corresponding clauses from `def_3_14`'s rewritten tex spec. The new predicate reads the LN literally: there exists `n ≥ 1` and a directed walk $(w_0=\ul{v}, w_1, \dots, w_n=\ol{v})$ in $G$ with consecutive $E$-edges and intermediates in $W$, with no extra restriction tying $n$ to the case $\ul{v} = \ol{v}$.

### `MarginalizationAK.lean` (`def_3_14`)

`MarginalizationΦE` becomes:

```lean
def MarginalizationΦE (G : CDMG Node) (W : Finset Node) (u v : Node) : Prop :=
  ∃ (p : Walk G u v),
    p.IsDirectedWalk ∧
    p.length ≥ 1 ∧
    (∀ x ∈ p.vertices.tail.dropLast, x ∈ W)
```

— i.e., the four-conjunct form drops to a three-conjunct form by removing `(u = v → p.length ≥ 2)`. Note that `MarginalizationΦL` and the `L^{∖W}` filter's `e.1 ≠ e.2` clause are untouched: the asymmetry between (iii) and (iv) — that bidirected self-edges are excluded from `L^{∖W}` outright while directed self-cycles may arise in `E^{∖W}` — is a legitimate consequence of the LN's literal "$\ul{v} \neq \ol{v}$" only appearing in clause (iv), and stays as-is.

The five private CDMG-axiom lemmas (`marginalize_hJV_disj`, `marginalize_hE_subset`, `marginalize_hL_subset`, `marginalize_hL_irrefl`, `marginalize_hL_symm`) are unaffected — none of them consume the strict clause.

The classical decidability instance `instDecidableMarginalizationΦE` is unaffected (still `Classical.propDecidable _`).

The `marginalize` def's `where`-body fields are unaffected at the level of source-text; only their *content* via `Φ_E` shifts (slightly more pairs admitted in the self-cycle case).

### `def_3_14_MarginalizationAK.tex`

Surgical edits, not a full rewrite:

- Clause (iii)(d) at line 40 — delete the whole `\item` (the "Self-cycle length restriction" item).
- Footnote at line 42 — delete the `\footnote{...}` that talks about the length-1 walk not being sufficient.
- Lines 40-42 (the in-words paragraph beginning "In words: $\Phi_E(\ul{v}, \ol{v})$ asserts ...") — strip the "clause~(d) imposes the additional self-cycle exclusion that, when $\ul{v} = \ol{v}$, a length-$1$ witness is not sufficient" sentence.
- Lines 75-81 ("Asymmetry between (iii) and (iv) regarding self-edges") — rewrite to keep only the legitimate $L^{\sm W}$ side of the asymmetry (i.e., "no $\ul{v} \neq \ol{v}$ on $E^{\sm W}$; explicit $\ul{v} \neq \ol{v}$ on $L^{\sm W}$"). Strip the length-1-walk caveat. The resulting paragraph stays a real preservation instruction for any future formaliser, just with the over-tight clause removed.
- The `\emph{No $\ul{v} \neq \ol{v}$ constraint.}` paragraph at line 44 — keep its first sentence ("The condition $\ul{v} \neq \ol{v}$ is *not* imposed in the set-builder for $E^{\sm W}$"). Strip "via a directed walk of length $\ge 2$ through $W$ that returns to $v$" from its second sentence; the corrected sentence simply says "self-cycles $(v, v) \in E^{\sm W}$ are admitted exactly under the witness conditions above, namely via a directed walk through $W$ that returns to $v$".

### `data.json` entry for `def_3_14` (`Chapter3_GraphTheory/data.json:1821`)

Rewrite `addition_to_the_LN` to drop the "Additionally, in clause (iii), a self-cycle …" final paragraph entirely. Keep:
- `[bifurcation_index_boundary_excludes_natural_cases]` block unchanged (independent — concerns the bifurcation index range in `Φ_L`, not self-cycles).
- The `[self_cycle_asymmetry_between_directed_and_bidirected]` heading, but the *body* shrinks to: "The asymmetry between clauses (iii) and (iv) regarding self-edges is intentional and shall be preserved by any formalization: directed self-cycles $v \tuh v$ may appear in $E^{\sm W}$ (as flagged by the footnote), while bidirected self-edges $v \huh v$ are excluded from $L^{\sm W}$ by the explicit $\ul{v} \neq \ol{v}$ constraint in clause (iv). A formalization should neither impose $\ul{v} \neq \ol{v}$ on $E^{\sm W}$ nor relax it on $L^{\sm W}$." — same as the current first paragraph, just dropping the second.

### `MarginalizationAK.lean`'s design-choice comment block

The comment block above `MarginalizationΦE` (lines 100-198) has multiple references to "(d) self-cycle restriction" and "u = v → p.length ≥ 2". Those references update in lock-step:
- Strike the "(d) self-cycle restriction" bullet at line 129-136.
- Remove "Why `p.length ≥ 1` and `u = v → p.length ≥ 2` as separate conjuncts" (lines 177-183) — no longer applicable.
- The "Asymmetry between (iii) and (iv) preserved" bullet (lines 602-617) needs to drop its "only via a walk of length ≥ 2 through `W`" mention but keep the rest ($E^{\sm W}$ has no `e.1 ≠ e.2`; $L^{\sm W}$ does).

This is documentation-cleanup, no semantic change beyond what the predicate change implies.

## Affected rows (consumers)

Hand-traced transitive consumers in chapter 3 (validate at `do_refactor.py init` time via `extras/find_dependents.py --chapter 3 --ref def_3_14`):

| Ref | Chapter | File | What changes for this row |
|-----|---------|------|---------------------------|
| `def_3_14` | 3 | `Section3_2/MarginalizationAK.lean` + `tex/def_3_14_MarginalizationAK.tex` + `data.json` | The foundational redesign itself (see "Proposed new shape" above). |
| `claim_3_16` | 3 | `Section3_2/MargPreservesAncestors.lean` + `tex/claim_3_16_*` | **Currently proven.** Proof reads `Φ_E` four-tuple via `⟨p, hp_dir, hp_pos, _, _⟩` (three call sites: `MargPreservesAncestors.lean:342`, `:3840`, `MarginalizationsCommute.lean` does not yet construct `Φ_E`), discarding the strict-clause witness via `_`. *Consumption* of `Φ_E` is unaffected: the new three-conjunct form destructures as `⟨p, hp_dir, hp_pos, _⟩`. *Construction* of `Φ_E` happens at `MargPreservesAncestors.lean:530` (proving `(v₁, m) ∈ marg.E` via "the head walk witnesses `Φ_E`"); under the new shape the `intro heq; exact absurd heq hv₁_eq_m` self-cycle-discharge step at lines 531-532 becomes dead code (the obligation is gone). The whole `by_cases hv₁_eq_m` at line 512-520 with its "the projected walk simply skips this loop" workaround becomes unnecessary too. The refactor row should *re-prove*, not just patch — the proof simplifies enough that mechanical patching may introduce dead branches; a clean re-prove is cheaper. |
| `claim_3_17` | 3 | `Section3_2/MarginalizationsCommute.lean` + `tex/claim_3_17_*` | **Currently `sorry`'d (in-progress row that triggered this refactor).** Statement file and LN-faithful proof tex are already written and verified equivalent to the LN. Under the loose def, the LN proof's directed-edge concatenation step (`Φ_E` for $G^{\sm (W_1 \cup W_2)}$ from $\Phi_E$ for $(G^{\sm W_1})^{\sm W_2}$) goes through without the strict-clause side condition. The Lean theorem signature stays exactly as it is at `MarginalizationsCommute.lean:294-303`; only the proof body needs to be filled in. |
| `claim_3_18` | 3 | `Section3_2/tex/claim_3_18_*` (no Lean yet) | **Not yet started.** Its statement is `(G_{\doit(W_1)})^{\sm W_2} = (G^{\sm W_2})_{\doit(W_1)}` with $W_1 \cap W_2 = \emptyset$. Standard tex stub only; no Lean exists. Under the strict def, the corner $W_2 = \emptyset$ would force the same pathology (LHS drops self-loops that the RHS preserves). The refactor unblocks any future formalisation of this lemma; concretely, this row's refactor-table entry simply re-runs the `formalize_*` actions for the first time against the loose def, picking up no carry-over technical debt. |
| `claim_3_19` | 3 | `Section3_2/tex/claim_3_19_*` (no Lean yet) | **Not yet started** ("MarginalizingOutThe…"; title is truncated in `data.json`). Similar story: standard tex stub only. Whether $W = \emptyset$ pathology bites depends on the exact body, but no Lean code is at risk yet — under the loose def the row is *unblocked* rather than *broken-and-repaired*. |

Crucially: **no other Lean file in the repo touches `MarginalizationΦE`, `MarginalizationΦL`, `G.marginalize`, or `MarginalizationAK`**. A `grep -rln "marginalize\|MarginalizationAK"` across `leanification/Chapter*/**/*.lean` returns only the four files in `Section3_2/` (`MarginalizationAK.lean`, `MargPreservesAncestors.lean`, `MarginalizationsCommute.lean`, plus the workspace markdown). The other Section3_2 files that appeared in the broad `\sm` grep (`HardInterventionOn.lean`, `NodeSplittingOn.lean`, etc.) mention the symbol `\sm` only in tex-comments, not as runtime references to the marginalisation operator. The chapter-3 aggregator `Chapter3_GraphTheory.lean:31-32` imports `MarginalizationAK` and `MargPreservesAncestors`; no other chapter aggregator depends on it (no chapter 4+ Lean code exists yet in this scaffold, per the `leanification/` directory listing). The refactor's blast radius is genuinely confined to chapter 3 sections covered above.

It is recommended that the human run `extras/find_dependents.py --chapter 3 --ref def_3_14` during `do_refactor.py init` to bullet-proof this hand-traced list (the script renames the def to `_REFACTOR_DISABLED`, runs `lake build`, scrapes every error site, restores). My hand trace agrees with what that scan should surface.

## Risks I see

- **`claim_3_16`'s proof is a re-prove, not a patch.** The proof uses underscore-discards on `Φ_E`'s four-tuple in three places and a `by_cases hv₁_eq_m` workaround in one place; mechanical text-patching could leave dead branches and silently broken match-arms. The refactor row's manager should opt for `prove_claim_in_lean` from a fresh `sorry` rather than syntactic patching of the existing proof body. The new proof is structurally identical and simpler.

- **`MarginalizationsCommute.lean` is currently `sorry`'d at `:304`.** Under loose def, this row's Lean proof becomes feasible, but the proof itself is not trivial (the directed-walk-concatenation and bifurcation-substitution parts of the LN's `\Claude{}` proof at `graphs.tex` lines 1006-1118 are quite long, and the bifurcation case is intricate). The refactor pipeline produces the *correct* def for the row to land on; it does *not* by itself solve the row. The refactor table will carry this row as an unsolved entry that the manager works through on the refactor branch.

- **Existing verifier passes on `def_3_14` were obtained under the strict-clause shape.** The strict-clause shape passed `verify_equivalence` / `verify_equivalence_strict` / `verify_with_examples` (all `=1` in the actions tracking at `data.json:1788-1790`) because the equivalence checker compared *against the rewritten tex spec*, not the LN literally — and the rewritten tex included the strict clause, so equivalence held. The loose-def shape will need to re-pass these gates after the refactor; the gates should still close cleanly (the new shape is strictly closer to the LN), but the row's verifier-action counters reset on the refactor branch.

- **Future chapters that have not yet been formalised may have already designed around the strict def via informal reading.** I checked the LN's downstream chapters (`causal_bayesian_networks.tex`, `scms2.tex`, `scms3.tex`, `counterfactuals.tex`, `conditional_independence.tex`, `fci.tex`) — all use marginalisation as the LN's clean operator (no length-1 caveats anywhere), so the LN side is consistent with the loose def. There is no leanification-side code in those chapters yet, so no built artefact would break. Documented here for completeness.

- **No deviations register entry exists for the strict clause.** `leanification/deviations.json` has one entry (`hard_intervention_l_symmetrized_removal` for `def_3_10`); nothing related to `def_3_14`'s self-cycle clause. So `--mark-deviations-resolved=auto` at `do_refactor.py finalize` time has nothing to flip for this refactor.

- **`MargPreservesAncestors.lean`'s comment at line 514-516 explicitly references the strict clause** as a justification for a `by_cases` workaround: "the marg-side self-edge `(v₁, v₁) ∈ marg.E` requires a length-`≥ 2` witness, but we can avoid producing such an edge entirely". When this row is re-proven, the comment must be updated (or removed); leaving it would be misleading.

## Why not the alternative (option B — keep strict `def_3_14`, add hypotheses to consumers)

Option B would force every downstream consumer of marginalisation to either (i) disclaim the $W = \emptyset$ corner, or (ii) restrict to graphs with no self-loops, or (iii) add a stronger hypothesis like "no length-1 directed self-cycle in $G$" to every claim's premise. Every option propagates the strict-clause hack through `claim_3_17` (the trivial $G^{\sm \emptyset} = G$ corner of the proof), `claim_3_18` (where $W_2 = \emptyset$ is a legitimate case of the joint-iteration claim), `claim_3_19` (whatever it ends up being, given the title "MarginalizingOutThe…" suggests an empty-marginalisation reduction), and continues into chapters 4+ wherever marginalisation feeds the do-calculus / identifiability / SWIG machinery. None of this friction exists in the LN itself, which reads marginalisation as a clean idempotent on $W = \emptyset$ and welcomes self-cycles. Option A (this refactor — drop the clause) preserves the LN's clean reading and confines the cleanup to one definition; option B propagates a self-inflicted divergence across the chapter.

## Recommended invocation

After review, the human executes:

```
git checkout server_setting_up_scaffold        # must be on this branch
python extras/do_refactor.py init \
    --chapter 3 \
    --root-ref def_3_14 \
    --name marginalize_loose_self_cycle
```

`do_refactor.py init` will: create the `refactor_marginalize_loose_self_cycle` branch, run `find_dependents.py` (bullet-proof transitive scan; expect it to surface `claim_3_16`, `claim_3_17`, `claim_3_18`, `claim_3_19` — and *only* those, modulo what `find_dependents` says about claim_3_18/claim_3_19 since they have no Lean files yet), run `initialize_refactor.py` to build `Chapter3_GraphTheory/Refactor_marginalize_loose_self_cycle/refactor_data.json`, commit, push the new branch. Then the human drives the refactor table with:

```
python scaffold/scripts/phase3_solving/solve_chapter.py --data-path \
    leanification/Chapter3_GraphTheory/Refactor_marginalize_loose_self_cycle/refactor_data.json
```

and finalises with:

```
python extras/do_refactor.py finalize --refactor-data \
    leanification/Chapter3_GraphTheory/Refactor_marginalize_loose_self_cycle/refactor_data.json \
    --mark-deviations-resolved=auto
python extras/do_refactor.py merge --refactor-data \
    leanification/Chapter3_GraphTheory/Refactor_marginalize_loose_self_cycle_DONE_<DATE>/refactor_data.json
```

once every refactor row is solved=yes (the `--push` and `--delete-remote-branch` flags on `merge` stay opt-in).

```
REFACTOR_PLAN_FILE: leanification/refactors/refactor_marginalize_loose_self_cycle.md
ROOT_REF: def_3_14
ROOT_CHAPTER: 3
NAME: marginalize_loose_self_cycle
RECOMMENDED_INVOCATION: python extras/do_refactor.py init --chapter 3 --root-ref def_3_14 --name marginalize_loose_self_cycle
```
