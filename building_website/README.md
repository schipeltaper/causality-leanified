# `building_website/` — MVP for the side-by-side presentation site

A scratch area to develop the static site that presents the Forré–Mooij
leanification side-by-side (TeX on the left, Lean on the right), organised
by chapter → section → row. Once we like the look, we'll promote
`building_website/website/` to `website/` at the repo root.

## Folder layout

```
building_website/
├── README.md                       ← this file
├── scripts/
│   ├── tex_to_html.py              ← LaTeX-prose → HTML converter (math left for KaTeX)
│   ├── fetch_row.py                ← per-row data extractor (the workhorse)
│   └── build_manifest.py           ← generates the sidebar tree
└── website/
    ├── index.html                  ← shell page; sidebar + content containers
    ├── assets/
    │   ├── style.css               ← all styling
    │   └── app.js                  ← fetches JSON, renders entries
    └── data/                       ← generated artifacts (in git so GH Pages serves them)
        ├── manifest.json           ← sidebar tree
        └── def_3_1.json            ← one file per fetched row
```

## What it does today

Section 3.1 lives in the sidebar; **def_3_1** is fully fetched, every other
row is shown as "unavailable" (italic, click to see how to populate it).
Open `index.html` (served over HTTP, see below) and you'll see:

- left sidebar tree: Chapter 3 → 3.1 → 11 rows;
- a two-pane split with TeX on the left (KaTeX rendering) and the Lean
  `structure CDMG` on the right (highlight.js with the `lean` grammar);
- status badges (Formalised / No proof — definition);
- action buttons (View TeX source, View Lean source);
- collapsible **Lean comments & design notes** panel — surfaces every
  `--` / `/- … -/` comment block that lives directly above the
  declaration in the Lean file.

## The data pipeline

The script in `scripts/fetch_row.py` is the one place that knows how to
read a row of `data.json` and produce the six pieces the website needs.
For one `ref` (e.g. `def_3_1`) it emits a single JSON file:

```
{
  "ref":         "def_3_1",
  "kind":        "def",                ← "def" | "claim"
  "section":     "3.1",
  "title":       "CDMG",
  "type":        "definition",
  "status":      { "formalized": "yes", "proven": "n/a", "solved": "yes" },

  "tex_statement": {
    "raw":         "<verbatim TeX, with subfiles wrapper>",
    "html":        "<HTML rendering, math intact for KaTeX>",
    "env":         "Def",                ← the theorem env name
    "env_title":   "Conditional directed mixed graphs (CDMG)",
    "source_path": "leanification/.../def_3_1_CDMG.tex"
  },

  "tex_proof": null,                   ← non-null for claims
  "lean": [
    {
      "part":        null,             ← "1/3" etc. for multi-part claims
      "title":       "CDMG",
      "comments":    "<every -- and /- … -/ comment block above the decl>",
      "statement":   "structure CDMG (α : Type*) where ...",
      "proof":       null,             ← non-null for theorems/lemmas
      "source_path": "leanification/.../CDMG.lean",
      "source_line": 17
    }
  ]
}
```

### How extraction works

For a given `ref` like `def_3_1`:

1. **find the row.** Walks `leanification/Chapter*/data.json` until it
   finds a row whose `ref` matches. The row carries `section`, `title`,
   `def_or_claim`, `main_lean_file`, `lean_files`.

2. **TeX statement file.** Derived from the row:
   - `def`:   `…/Section<N>_<M>/tex/<ref>_<Title>.tex`
   - `claim`: `…/Section<N>_<M>/tex/<ref>_statement_<Title>.tex`

   Read, run through `tex_to_html.tex_to_html()`:
   - strip the `\documentclass[main]{subfiles}` / `\begin{document}` /
     bookkeeping framing,
   - unwrap the outer `\begin{Def}[Title]…\end{Def}` (or `Lem`, `Rem`,
     `Note`, `Cor`, `Prop`, `Thm`; plus the `defmark` / `claimmark`
     wrappers),
   - convert `\emph` / `\textbf` / `\refrow` / em-dashes / non-breaking
     spaces inline,
   - convert `\begin{enumerate}[label=\roman*.)]` blocks (including the
     `resume` option) into `<ol class="roman-paren">` with proper counter
     offsets,
   - leave every `$…$` / `\(…\)` / `$$…$$` / `\[…\]` math segment
     **untouched** — KaTeX renders those client-side.

3. **TeX proof file** (claims only). Read
   `…/<ref>_proof_<Title>.tex`, strip the wrapper, extract the body of
   `\begin{proof}…\end{proof}` and run it through the same prose
   converter.

4. **Lean blocks.** For each path in
   `[main_lean_file, *lean_files]` (de-duplicated), look for ref-marker
   comments of the form

   ```
   -- def_3_1
   -- title: CDMG
   ```

   or, for multi-part claims:

   ```
   -- claim_3_1 (part 1/3)
   -- title: JNodeProperties -- short description
   ```

   For each marker matching the target ref, slice the lines from that
   marker up to (but not including) the next marker for *any* ref, end
   of file, or a top-level `end` line. Then split:
   - `comments` — everything between the marker line and the first line
     that introduces a Lean declaration
     (`structure` / `def` / `abbrev` / `class` / `instance` /
     `inductive` / `theorem` / `lemma` / `example`).
   - `statement` — for theorem/lemma/example, everything up to and
     including `:= by` (or term-mode `:=`). For
     structure/def/abbrev/…, the whole block.
   - `proof` — for theorem/lemma/example, everything after the `:= by`
     opener. `null` for structure-family declarations.

5. **Emit.** Write
   `building_website/website/data/<ref>.json` (or stdout / a chosen
   path via `--out`).

### How the website consumes it

`app.js` is a thin renderer (~250 lines). On load:

1. `fetch('data/manifest.json')` → builds the sidebar tree.
2. Reads the URL hash (`#def_3_1`) or defaults to `def_3_1`,
   then `fetch('data/<ref>.json')`.
3. Builds DOM nodes for the entry — header, two-column split, optional
   proof panes (TeX + Lean), action buttons, and the collapsible
   "Lean comments" pre block.
4. Runs `renderMathInElement` (KaTeX) over the content and
   `hljs.highlightElement` on each `<pre><code class="language-lean">`.
5. `hashchange` re-renders.

Math macros that aren't native KaTeX are registered in `app.js` under
`KATEX_MACROS`; right now there are three:

```js
const KATEX_MACROS = {
  "\\ins": "\\subseteq",
  "\\x":   "\\times",
  "\\id":  "\\mathrm{id}",
};
```

As we ingest more rows we'll add `\hus`, `\tuh`, `\huh`, `\hut`, etc.,
matching `leanification/preamble.tex`.

## How to run it

```bash
# 1. (Re)generate one row's data
python3 building_website/scripts/fetch_row.py def_3_1

# 2. Update the sidebar manifest
python3 building_website/scripts/build_manifest.py

# 3. Serve the static site
cd building_website/website
python3 -m http.server 8000
# → http://localhost:8000
```

`fetch_row.py` works for any ref — `def_3_1`, `claim_3_4`, etc. —
provided the corresponding `data.json` row exists. The script's CLI:

```
python3 fetch_row.py <ref> [--out PATH | --stdout]
```

### Adding more rows

```bash
python3 building_website/scripts/fetch_row.py def_3_2
python3 building_website/scripts/fetch_row.py claim_3_1
python3 building_website/scripts/build_manifest.py
```

The manifest auto-detects which rows have a `data/<ref>.json` and marks
the sidebar accordingly (italic = not yet generated).

### Expanding the scope of the sidebar

`scripts/build_manifest.py` has a `SCOPE` dict at the top:

```python
SCOPE: dict[int, list[str] | None] = {
    3: ["3.1"],            # only section 3.1 of chapter 3
}
# Change to:
SCOPE: dict[int, list[str] | None] = {
    3: None,               # all sections of chapter 3
}
```

## What still needs polish (known gaps)

These are deliberate cuts for the MVP, not bugs:

1. **TeX prose converter coverage.** Today it handles every pattern that
   appears in `def_3_1`. As we fetch more rows we'll hit things like
   `\autoref`, `\cref`, custom theorem-like envs (`Aufgabe`, `Bsp`),
   nested itemize/enumerate, etc. — extend `tex_to_html.py` per
   pattern.
2. **Custom math macros.** Add to `KATEX_MACROS` in `app.js` as we
   encounter them. The full list lives in `leanification/preamble.tex`.
3. **TeX proof rendering for claims.** Wired but untested — `claim_3_X`
   will exercise it.
4. **Lean proof block extraction.** Splits at `:= by` correctly; doesn't
   yet handle multi-line `where` blocks at the end of a proof (those'd
   end up appended to the proof body, which is fine for display).
5. **No build step in CI yet.** The data files are committed to git
   so GitHub Pages serves them directly. Eventually we'd add an Actions
   workflow that re-runs `fetch_row.py` for every solved row + the
   manifest builder on every push to `main`.

## Deploying to GitHub Pages with a Namecheap subdomain

When the design is final, move `building_website/website/` →
`website/` (or `docs/`) at the repo root. Two routes:

### Route A — serve from a folder on main

In **repo settings → Pages**:

- Source: **Deploy from a branch**
- Branch: `main` / folder `/docs` (rename `website` → `docs` if you
  go this route; Pages only auto-serves `/`, `/docs`, or `/site`).

Commit a `CNAME` file in that folder with one line:

```
causality.yourdomain.com
```

### Route B — Actions workflow (preferred once we have a build step)

`.github/workflows/pages.yml`:

```yaml
name: Deploy site
on:
  push:
    branches: [main]
  workflow_dispatch:
permissions:
  contents: read
  pages: write
  id-token: write
jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: { python-version: "3.11" }
      - name: Regenerate site data
        run: |
          # Fetch every solved row + build manifest
          python3 - <<'PY'
          import json, subprocess
          from pathlib import Path
          for d in Path("leanification").glob("Chapter*/data.json"):
              data = json.loads(d.read_text())
              for row in data["rows"]:
                  if row.get("solved") == "yes":
                      subprocess.check_call(
                          ["python3", "building_website/scripts/fetch_row.py", row["ref"]]
                      )
          subprocess.check_call(["python3", "building_website/scripts/build_manifest.py"])
          PY
      - uses: actions/upload-pages-artifact@v3
        with: { path: ./building_website/website }
      - uses: actions/deploy-pages@v4
```

### Namecheap DNS

In **Advanced DNS** for the apex domain:

| Type    | Host        | Value                       | TTL  |
| ------- | ----------- | --------------------------- | ---- |
| `CNAME` | `causality` | `schipeltaper.github.io.`   | Auto |

(Trailing dot is significant.) For the apex itself, use four `A`
records to `185.199.108.153`, `…109.153`, `…110.153`, `…111.153`.

Then in repo settings → Pages → **Custom domain** enter
`causality.yourdomain.com` and tick **Enforce HTTPS** once the cert
provisions.

## Workflow suggestions (small scaffold tweaks)

The pipeline already works with the existing scaffold output. Two
optional changes would make it more robust:

1. **Explicit `-- END_STATEMENT <ref>` marker** in `.lean` files.
   Right now the slicer bounds at the *next* marker for any ref or
   `end` line. An explicit end marker would make slices unambiguous
   when one file packs many declarations.
2. **`depends_on: ["def_3_1"]`** field per row in `data.json`. Not used
   today, but it'd unlock the dep-graph visualisation later for ~free.

Neither is required.
