import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

/-!
# Walk prefix and suffix (Chapter 3 walk-splicing infrastructure)

This file provides `Walk.prefix` and `Walk.suffix`, plus the
characterisation lemmas needed to use them as structural sub-walk
extraction primitives. They are introduced *for* `claim_3_27`
(`lem:replace_walk`, see `lecture-notes/lecture_notes/graphs.tex`
lines 1620 -- 1652), whose main theorem expresses a spliced walk as
`(π.prefix i).append (σ.append (π.suffix j))` for a fresh middle
walk `σ`. They are not, however, *specific* to that theorem: the
prefix/suffix decomposition is the canonical way to talk about
"the walk with the subwalk between positions `i` and `j` replaced
by `σ`", and that pattern recurs throughout chapter 3 of the LN.

## Downstream consumers in chapter 3

The "modify a subwalk between two positions on a $\sigma$-open
walk" pattern shows up at least twice more in chapter 3 alone:

* `claim_3_23` (`2 \Rightarrow 3` direction, LN line 1669): the
  repetition-reduction argument for $\sigma$-open walks iterates
  `replace_walk` to collapse multiply-occurring $\Sc^G$-classes
  into single segments. The argument destructures the spliced walk
  as prefix / middle / suffix to count repeated nodes per segment
  -- which requires the prefix/suffix to be *separately
  addressable* structures, not buried inside an opaque
  `Walk.splice` operator.
* The $\sigma'$-open ($i\sigma$-separation) analogue of the same
  iff-equivalence (LN line 2071) follows the same pattern, with
  `replace_walk` plugged into the $\sigma'$-open variant of the
  iteration.

Beyond those, the same prefix/middle/suffix shape is the natural
expression for any "replace a subwalk" pattern in later chapters
(do-calculus rule applications often involve cutting a walk at
intervention points; counterfactual identification often involves
splicing along a backdoor path). So this file is *chapter-3 walk
infrastructure*, not a one-off helper.

## API (under `Causality.Walk`)

* `Walk.prefix π i : Walk G v (π.nodeAt i)` -- the prefix of `π`
  of length `i`, ending at vertex `π.nodeAt i`.
* `Walk.suffix π j : Walk G (π.nodeAt j) w` -- the suffix of `π`
  starting at position `j`.
* Per-constructor `@[simp]` characterisation lemmas
  (`prefix_nil` / `prefix_cons_zero` / `prefix_cons_succ` and the
  three `suffix_*` mirrors).
* Length identities: `length_prefix`, `length_suffix`.
* Position lookups: `nodeAt_prefix`, `nodeAt_suffix`.
* Recomposition: `prefix_append_suffix` -- the workhorse splicing
  identity `(π.prefix j).append (π.suffix j) = π` for
  `j ≤ π.length`.
* Endpoint-coincidence sanity lemmas, stated as `HEq`:
  `prefix_zero`, `prefix_length`, `suffix_zero`, `suffix_length`.

## Design notes

* **Junk-OK conventions.** `π.prefix i` returns `Walk.nil v` for
  `i = 0` *and* whenever the structural recursion runs off the
  end of `π` (`i ≥ π.length` on a non-trivial walk only collapses
  back to `nil` once both arguments are exhausted; pure `nil _`
  walks return `nil _` for any `i`). `π.suffix j` mirrors this:
  `π` itself for `j = 0`, the trivial walk on the endpoint for
  `j ≥ π.length`. The structural recursion exits both terminal
  cases without an explicit guard. Mirrors the `nodeAt`-junk
  convention from `SigmaBlockedWalks.lean`: the consumer always
  carries a side hypothesis `i ≤ π.length` / `j ≤ π.length` when
  the junk arm matters semantically.

* **Dependent return types `Walk G v (π.nodeAt i)` and
  `Walk G (π.nodeAt j) w`.** Encoding the sub-walk's endpoint as
  `π.nodeAt i` (a derived expression of the input) is what lets a
  composition `(π.prefix i).append σ` typecheck whenever
  `σ : Walk G (π.nodeAt i) _`. This is precisely the composition
  pattern `replace_walk` uses. The price is the four
  endpoint-coincidence sanity lemmas (`prefix_zero`,
  `prefix_length`, `suffix_zero`, `suffix_length`) need `HEq`
  rather than `Eq`, because `π.nodeAt 0 = v` and
  `π.nodeAt π.length = w` are *provable* but not *definitional*
  for a free variable `π`. Per the manager's plan, this is the
  right trade-off: every `nodeAt` lookup on the spliced walk
  reduces to a lookup on the original walk via `nodeAt_prefix` /
  `nodeAt_suffix` (clean `Eq`), without triggering the
  endpoint-coincidence cast.

* **`prefix` is a Lean 4 keyword** (reserved for the
  `prefix:50 ...` notation declaration). We escape it as
  `«prefix»` in the `def` header; call sites use `Walk.prefix` /
  `π.prefix i` without escape because the dot-projection /
  qualified-name lookup paths are not declaration positions.
  `suffix` is not a keyword and needs no escape.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### `Walk.prefix` -/

-- claim_3_27 (step 1, I1)
-- title: Walks -- prefix sub-walk
--
-- `π.prefix i` is the walk obtained by taking the first `i` steps of
-- `π`. Returns the trivial walk `nil v` at `i = 0` and (junk-OK)
-- `nil _` at any position once the recursion has run off the end of
-- the walk.
--
-- ## Design choice
--
-- * **Structural recursion on `π` first, then on `i`.** Matches the
--   recursive shape of `nodeAt` and `IsColliderAt` in sibling files:
--   the outer match strips one `cons`-edge off the front, the inner
--   match peels one position-index off the right. The two terminal
--   arms (the `.nil _` branch for any `i`, and the `.cons _ _, 0`
--   branch) both return `Walk.nil _`. The recursive
--   `.cons s p, i + 1` branch returns `Walk.cons s (p.prefix i)`.
--
-- * **Return type `Walk G v (π.nodeAt i)`.** Encoding the right
--   endpoint as `π.nodeAt i` is what lets the *common case* (the
--   composition `(π.prefix i).append σ` for `σ` starting at
--   `π.nodeAt i`) typecheck without explicit casts. See the module
--   docstring for the trade-off (`HEq` is paid by the four
--   endpoint-coincidence sanity lemmas).

/-- The sub-walk of `π` from position `0` to position `i`, ending
at vertex `π.nodeAt i`. -/
def «prefix» : {v w : α} → (π : Walk G v w) → (i : ℕ) → Walk G v (π.nodeAt i)
  | _, _, .nil _,    _     => .nil _
  | _, _, .cons _ _, 0     => .nil _
  | _, _, .cons s p, i + 1 => .cons s (p.prefix i)

/-! The next three `@[simp]` lemmas (`prefix_nil`,
`prefix_cons_zero`, `prefix_cons_succ`) are the per-constructor
characterisation of `Walk.prefix`: one lemma per arm of the
defining match. Without them, downstream `simp` calls and `rfl`
goals on expressions of the form `(...).prefix i` would have to
unfold the recursive definition by hand; with them, `simp` reduces
any concrete-shape `prefix` expression to a normal form. They are
the analogues of the per-constructor `nodeAt_*` lemmas in
`Section3_1/Walks.lean` and are kept `@[simp]` for the same
reason. -/

/-- The trivial walk's prefix is itself, at every position. -/
@[simp] theorem prefix_nil (v : α) (i : ℕ) :
    (Walk.nil v : Walk G v v).prefix i = Walk.nil v := by
  cases i <;> rfl

/-- The prefix of a `cons`-extended walk at position `0` is the
trivial walk on the source vertex. -/
@[simp] theorem prefix_cons_zero {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) :
    (Walk.cons s p).prefix 0 = Walk.nil v := rfl

/-- The prefix of a `cons`-extended walk at position `i + 1` peels
off the head step and recurses on the tail. -/
@[simp] theorem prefix_cons_succ {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) (i : ℕ) :
    (Walk.cons s p).prefix (i + 1) = Walk.cons s (p.prefix i) := rfl

/-! ### `Walk.suffix` -/

-- claim_3_27 (step 1, I2)
-- title: Walks -- suffix sub-walk
--
-- Mirror of `Walk.prefix`: `π.suffix j` is the walk obtained by
-- dropping the first `j` steps of `π`, starting at vertex
-- `π.nodeAt j`. Junk-OK for `j > π.length` (the recursion exits
-- early at the trailing `.nil _`).
--
-- ## Design choice
--
-- * **Mirror of `prefix`.** Same recursion shape: outer match on
--   `π`, inner match on `j`. The two terminal arms (the `.nil _`
--   branch and the `.cons _ _, 0` branch) return the maximal walk
--   on each side -- `Walk.nil _` and the full input walk
--   respectively. The recursive `.cons _ p, j + 1` branch drops
--   the head step and recurses on the tail.
--
-- * **Return type `Walk G (π.nodeAt j) w`.** Same reasoning as for
--   `prefix`: encoding the *left* endpoint as `π.nodeAt j` lets a
--   composition `σ.append (π.suffix j)` typecheck whenever
--   `σ : Walk G _ (π.nodeAt j)`. The downstream consumer
--   (`replace_walk`) splices via
--   `(π.prefix i).append (σ.append (π.suffix j))`, which is
--   precisely this composition shape twice.

/-- The sub-walk of `π` from position `j` to position `π.length`,
starting at vertex `π.nodeAt j`. -/
def «suffix» : {v w : α} → (π : Walk G v w) → (j : ℕ) → Walk G (π.nodeAt j) w
  | _, _, .nil v,    _     => .nil v
  | _, _, .cons s p, 0     => .cons s p
  | _, _, .cons _ p, j + 1 => p.suffix j

/-! The next three `@[simp]` lemmas are the `suffix` mirror of the
`prefix_*` per-constructor characterisation block above. Same
rationale: one per arm of the defining match, kept `@[simp]` so
downstream proofs do not need to unfold `Walk.suffix` by hand. -/

/-- The trivial walk's suffix is itself, at every position. -/
@[simp] theorem suffix_nil (v : α) (j : ℕ) :
    (Walk.nil v : Walk G v v).suffix j = Walk.nil v := by
  cases j <;> rfl

/-- The suffix of a `cons`-extended walk at position `0` is the
whole walk. -/
@[simp] theorem suffix_cons_zero {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) :
    (Walk.cons s p).suffix 0 = Walk.cons s p := rfl

/-- The suffix of a `cons`-extended walk at position `j + 1`
drops the head step and recurses on the tail. -/
@[simp] theorem suffix_cons_succ {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) (j : ℕ) :
    (Walk.cons s p).suffix (j + 1) = p.suffix j := rfl

/-! ### Length of prefix and suffix

These two lemmas (`length_prefix`, `length_suffix`) are the
workhorse arithmetic identities that let consumers reason about
positions on the spliced walk
`(π.prefix i).append (σ.append (π.suffix j))`: every position on
the spliced walk is either in `[0, i]` (covered by `prefix`), in
`[i, i + σ.length]` (covered by the middle), or in
`[i + σ.length, i + σ.length + (π.length - j)]` (covered by
`suffix`), and `length_prefix` / `length_suffix` are what turn
those bounds into concrete `Nat` arithmetic. Both are `@[simp]`
because every length-side-condition in `replace_walk`'s proof
ultimately bottoms out in one of these two rewrites.
-/

-- claim_3_27 (step 1, I3)
-- title: Walks -- length of the prefix sub-walk
/-- The prefix of length `i` (for `i ≤ π.length`) has length
exactly `i`. -/
@[simp] theorem length_prefix {v w : α} (π : Walk G v w) {i : ℕ}
    (h : i ≤ π.length) : (π.prefix i).length = i := by
  induction π generalizing i with
  | nil _ =>
    cases i with
    | zero => rfl
    | succ i => exact absurd h (by simp)
  | cons s p ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [length_cons] at h
      have h' : i ≤ p.length := by omega
      change (p.prefix i).length + 1 = i + 1
      exact congrArg (· + 1) (ih h')

-- claim_3_27 (step 1, I3)
-- title: Walks -- length of the suffix sub-walk
/-- The suffix from position `j` (for `j ≤ π.length`) has length
`π.length - j`. -/
@[simp] theorem length_suffix {v w : α} (π : Walk G v w) {j : ℕ}
    (h : j ≤ π.length) : (π.suffix j).length = π.length - j := by
  induction π generalizing j with
  | nil _ =>
    cases j with
    | zero => rfl
    | succ j => exact absurd h (by simp)
  | cons s p ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [length_cons] at h
      have h' : j ≤ p.length := by omega
      change (p.suffix j).length = (p.length + 1) - (j + 1)
      rw [ih h']
      omega

/-! ### `nodeAt` of prefix and suffix

These are the *single most important* lemmas in this file for
`replace_walk` and its consumers. The spliced walk
`(π.prefix i).append (σ.append (π.suffix j))` has the property
that its `nodeAt`-lookup at any position $k$ outside the middle
segment should agree with `π`'s `nodeAt`-lookup at the
corresponding position on `π`. `nodeAt_prefix` and `nodeAt_suffix`
are what discharge that obligation: every `nodeAt`-on-the-spliced-
walk goal -- whether it appears in a $\sigma$-openness argument,
in a "this node lies in $\Sc^G(w)$" argument, or in a repetition
count -- reduces, via these two lemmas, to a `nodeAt`-on-the-
original-`π` goal, which `h_open : π.IsSigmaOpen C` and the row's
other premises can already handle. Both lemmas are kept `@[simp]`
specifically so that `simp` chains involving the spliced walk's
position lookups close automatically. Removing the `@[simp]`
attribute would force every consumer to invoke them by hand --
which, given how many `nodeAt`-on-the-splice obligations
`replace_walk`'s proof generates, would balloon the proof size.
-/

-- claim_3_27 (step 1, I4)
-- title: Walks -- nodeAt on the prefix coincides with nodeAt on π
/-- `nodeAt` on the prefix of `π` coincides with `nodeAt` on `π`
at every position `k ≤ i` (where `i ≤ π.length`). -/
@[simp] theorem nodeAt_prefix {v w : α} (π : Walk G v w) {i k : ℕ}
    (hk : k ≤ i) (hi : i ≤ π.length) :
    (π.prefix i).nodeAt k = π.nodeAt k := by
  induction π generalizing i k with
  | nil v => rfl
  | cons s p ih =>
    cases i with
    | zero =>
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      rfl
    | succ i =>
      simp only [length_cons] at hi
      have hi' : i ≤ p.length := by omega
      cases k with
      | zero => rfl
      | succ k =>
        have hk' : k ≤ i := by omega
        change (p.prefix i).nodeAt k = p.nodeAt k
        exact ih hk' hi'

-- claim_3_27 (step 1, I4)
-- title: Walks -- nodeAt on the suffix coincides with shifted nodeAt on π
/-- `nodeAt` on the suffix `π.suffix j` at position `k` equals
`nodeAt` on `π` at the shifted position `j + k` (provided
`j + k ≤ π.length`). -/
@[simp] theorem nodeAt_suffix {v w : α} (π : Walk G v w) {j k : ℕ}
    (h : j + k ≤ π.length) :
    (π.suffix j).nodeAt k = π.nodeAt (j + k) := by
  induction π generalizing j k with
  | nil v =>
    have hj : j = 0 := by simp only [length_nil] at h; omega
    have hk : k = 0 := by simp only [length_nil] at h; omega
    subst hj; subst hk
    rfl
  | cons s p ih =>
    cases j with
    | zero =>
      change (cons s p).nodeAt k = (cons s p).nodeAt (0 + k)
      rw [Nat.zero_add]
    | succ j =>
      simp only [length_cons] at h
      have h' : j + k ≤ p.length := by omega
      have hadd : j + 1 + k = (j + k) + 1 := by omega
      change (p.suffix j).nodeAt k = (cons s p).nodeAt (j + 1 + k)
      rw [hadd, nodeAt_cons_succ]
      exact ih h'

/-! ### Recomposition: `prefix ⧺ suffix = π` -/

-- claim_3_27 (step 1)
-- title: Walks -- splicing identity: prefix then suffix recovers π
/-- The recomposition identity: appending the suffix from position
`j` onto the prefix of length `j` recovers `π` (for any
`j ≤ π.length`). This is the workhorse splicing identity used by
`replace_walk` to express the spliced walk
`(π.prefix i).append (σ.append (π.suffix j))` and reason about its
relationship to the original `π`.

## Design choice

* **`@[simp]` is load-bearing.** With this lemma marked `@[simp]`,
  any `simp` chain over expressions of the form
  `(π.prefix j).append (π.suffix j)` reduces them back to `π`
  without needing an explicit `rw`. This is the key rewrite for
  the *consistency* direction of `replace_walk`'s proof: showing
  that the spliced walk agrees with $\pi$ outside the replaced
  $[i, j]$-segment reduces, via `append_assoc` (in
  `SigmaBlockedReversal.lean`), to recomposing `prefix` and
  `suffix` on each side of the replacement middle and then
  collapsing each recomposition via this lemma.
* **One cut-point, not two.** This is the single-cut recomposition
  identity, even though `replace_walk` uses a two-cut splice
  (`(π.prefix i).append (σ.append (π.suffix j))` with `i < j`).
  The two-cut version factors through the single-cut form
  iteratively, so a dedicated two-cut identity would only repackage
  what the single-cut + `append_assoc` already deliver. -/
@[simp] theorem prefix_append_suffix {v w : α} (π : Walk G v w) {j : ℕ}
    (h : j ≤ π.length) :
    (π.prefix j).append (π.suffix j) = π := by
  induction π generalizing j with
  | nil _ =>
    cases j with
    | zero => rfl
    | succ j => exact absurd h (by simp)
  | cons s p ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [length_cons] at h
      have h' : j ≤ p.length := by omega
      change Walk.cons s ((p.prefix j).append (p.suffix j)) = Walk.cons s p
      exact congrArg _ (ih h')

/-! ### Endpoint-coincidence sanity lemmas (HEq)

These four lemmas (`prefix_zero`, `prefix_length`, `suffix_zero`,
`suffix_length`) characterise the *extreme* values of the
sub-walk index: position `0` and position `π.length`. They are
not normally needed by `replace_walk` itself -- the row's
`hij : i < j` and `hj : j ≤ π.length` rule out `i = π.length` and
`j = 0`, leaving the interesting cuts strictly interior -- but
they are exported here for two reasons. (1) Downstream consumers
of the prefix/suffix API may legitimately need a boundary cut
(e.g. claim_3_23's iteration could land on a final-segment
`replace_walk` invocation where `j = π.length`). (2) They are
the only `HEq` lemmas in this file, and segregating them in their
own block makes the `Eq` vs. `HEq` boundary explicit: the
recursion-and-lookup characterisations (`length_*`, `nodeAt_*`,
`prefix_append_suffix`) are all `Eq` and play cleanly with
`simp`; the endpoint-coincidences need `HEq` because the
dependent-type endpoint `π.nodeAt 0` / `π.nodeAt π.length` is
not *definitionally* equal to `v` / `w` for a free `π`. Keeping
them in their own block warns the consumer that they need a
`subst` / `cases hπ_endpoint` step to translate `HEq` to `Eq` at
the use site.
-/

-- claim_3_27 (step 1, sanity)
-- title: Walks -- prefix at position 0 is the trivial walk (HEq)
/-- The prefix at position `0` is the trivial walk on the source
vertex. Stated as `HEq` because the natural `Eq` statement has a
dependent-type mismatch: `π.prefix 0 : Walk G v (π.nodeAt 0)` while
`Walk.nil v : Walk G v v`, and `π.nodeAt 0 = v` is provable but
not *definitional* for a free variable `π`. -/
theorem prefix_zero {v w : α} (π : Walk G v w) :
    HEq (π.prefix 0) (Walk.nil v : Walk G v v) := by
  cases π <;> rfl

/-- Helper: HEq of two `cons`-walks reduces to HEq of their tails
plus equality of the tail's right-endpoint indices. Used to lift
the inductive hypothesis through a `cons` constructor in
`prefix_length` and `suffix_length`. -/
private theorem cons_heq_cons {v w u u' : α}
    (s : WalkStep G v w) (p : Walk G w u) (p' : Walk G w u')
    (hu : u = u') (hp : HEq p p') :
    HEq (Walk.cons s p) (Walk.cons s p') := by
  subst hu; cases hp; rfl

-- claim_3_27 (step 1, sanity)
-- title: Walks -- prefix at position π.length is π (HEq)
/-- The prefix at position `π.length` is the whole walk `π`. -/
theorem prefix_length {v w : α} (π : Walk G v w) :
    HEq (π.prefix π.length) π := by
  induction π with
  | nil _ => rfl
  | cons s p ih =>
    change HEq (Walk.cons s (p.prefix p.length)) (Walk.cons s p)
    exact cons_heq_cons s _ _ p.nodeAt_length ih

-- claim_3_27 (step 1, sanity)
-- title: Walks -- suffix at position 0 is π (HEq)
/-- The suffix at position `0` is the whole walk `π`. -/
theorem suffix_zero {v w : α} (π : Walk G v w) :
    HEq (π.suffix 0) π := by
  cases π <;> rfl

-- claim_3_27 (step 1, sanity)
-- title: Walks -- suffix at position π.length is the trivial walk (HEq)
/-- The suffix at position `π.length` is the trivial walk on the
endpoint. -/
theorem suffix_length {v w : α} (π : Walk G v w) :
    HEq (π.suffix π.length) (Walk.nil w : Walk G w w) := by
  induction π with
  | nil _ => rfl
  | cons _ p ih =>
    exact ih

end Walk

end Causality
