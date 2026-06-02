# Worker — refactor existing Lean code in a subsection

**When to use:** the manager has noticed that some Lean code in the row's subsection folder has grown awkward — duplicated logic, a file pushing 700+ lines with a natural split point, a definition that the rest of the theory wants in a different shape — and wants a focused refactor without changing what's been proven.

## Inputs you should receive from the manager

- The Lean file(s) in scope
- A specific refactor goal (e.g. "split `Walks.lean` at the d-separation/iσ-separation boundary", "rename `MyDef` → `…` everywhere in this folder", "lift this helper lemma out of the proof and into the file's preamble")
- Pointers to any callers within the subsection that depend on the affected declarations

## Hard invariants — do not violate

- **Theorem statements do not change.** Whatever was proven must still be proven, with the same name and signature, unless the manager explicitly authorised a rename (and then every call site within the subsection is updated).
- **No new `sorry` and no new `True`.** If your refactor breaks a proof, fix the proof — don't paper over it.
- **Builds clean.** `lake build` from `/home/11716061/` must succeed after the refactor.
- **Scope.** Only files inside the row's subsection folder under `leanification/`.

## What to do

1. **Read the goal carefully.** A refactor without a clear goal becomes a rewrite. If the goal is fuzzy, hand back to the manager with a request to sharpen it.
2. **Identify the affected declarations** and every internal call site.
3. **Plan the move/split/rename** before touching files. Note in scratch what each step is and which file ends up where.
4. **Execute in small steps**, building between them. Use the lean-lsp MCP (`lean_references`, `lean_diagnostic_messages`) to catch breakages early.
5. **Update or add comments** where the refactor exposes design choices that weren't documented before.
6. **Final build** must be clean.
7. **Report back** to the manager: what moved/renamed/split, what was changed in comments, what was deliberately *not* changed, and whether any unexpected coupling came to light.

## Rules

- Don't refactor `claude.md` or any file outside the subsection.
- Don't change the project's Lean toolchain or `lakefile.*`.
- Don't introduce a "compatibility shim" or stale re-exports — if a thing moves, callers move with it.
