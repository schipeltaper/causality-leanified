# `building_website/` — the side-by-side presentation site

The static site at <https://leanification.samritchie.dev/> that presents
the Forré–Mooij leanification side-by-side: the lecture-notes statement
on the left, the Lean 4 formalisation on the right, organised by
chapter → section → row.

## Folder layout

```
building_website/
├── README.md                 ← this file
├── scripts/
│   ├── tex_to_html.py        ← LaTeX-prose → HTML converter (math left for KaTeX)
│   ├── fetch_row.py          ← per-row data assembler
│   └── build_manifest.py     ← sidebar tree generator
└── website/
    ├── index.html            ← shell page
    ├── .nojekyll
    ├── CNAME                 ← leanification.samritchie.dev
    ├── assets/
    │   ├── style.css
    │   └── app.js            ← client-side renderer
    └── data/                 ← generated artifacts (committed; GH Pages serves them)
        ├── manifest.json     ← sidebar tree
        └── <ref>.json        ← one per row
```

## Where the row data comes from

Since the website-builder migration (see, while it lasts,
`extras/temp_for_website_builder.md`) the leanification orchestrator
writes a per-row JSON at solve-time:

```
leanification/Chapter*/Section*/tex/<ref>_for_website.json
```

That file is the source of truth for a row's **Lean** side — it
carries a curated, source-ordered `lean_statement` list (one
`{name, kind, code}` per LN-level declaration, helpers filtered) plus
publication-ready `lean_explanation` and `design_choices` Markdown.
The website builder does **not** regenerate any of that — no Lean-file
walking, no marker parsing, no LLM step.

The **TeX** side is still rendered locally: the per-row `.tex` files
under each section's `tex/` folder go through `tex_to_html.py`.

## The pipeline

```
leanification/.../tex/<ref>_for_website.json   (Lean side: curated by the orchestrator)
leanification/.../tex/<ref>_*.tex              (TeX side: statement + proof)
                       │
                       ▼
        scripts/fetch_row.py <ref>             reads the for_website JSON,
                       │                       renders the TeX with tex_to_html
                       ▼
        website/data/<ref>.json                what the website fetches
                       │
        scripts/build_manifest.py              scans data/ → sidebar tree
                       ▼
        website/data/manifest.json
```

### `fetch_row.py`

```
python3 building_website/scripts/fetch_row.py <ref> [--out PATH | --stdout]
```

For one ref it:
1. globs `leanification/Chapter*/Section*/tex/<ref>_for_website.json`,
2. reads it for the Lean statement list + prose,
3. renders the sibling `.tex` statement (and, for claims, the proof
   file) with `tex_to_html.py`,
4. derives status (`for_website.json` only exists for solved rows, so a
   def is "formalised / no proof", a claim "formalised / proven"),
5. writes `website/data/<ref>.json`.

If a row has no `_for_website.json` it isn't solved/published — the
script exits with an error and the row simply won't appear available.

### `build_manifest.py`

Emits `data/manifest.json` (the sidebar tree). Coverage is the `SCOPE`
dict at the top of the file — currently `{3: ["3.1", "3.2"]}`. A row is
marked `available` iff its `data/<ref>.json` exists.

### Output JSON shape (`data/<ref>.json`)

```jsonc
{
  "ref": "def_3_1", "kind": "def", "section": "3.1",
  "title": "CDMG", "type": "definition",
  "status": { "formalized": "yes", "proven": "n/a", "solved": "yes" },
  "tex_statement": { "raw", "html", "env", "env_title", "source_path" },
  "tex_proof": null,                         // {raw,html,source_path} for claims
  "lean": [ { "name", "kind", "code" }, … ], // straight from for_website.json
  "lean_file_path": "leanification/.../CDMG.lean",
  "lean_explanation": "…markdown…",
  "design_choices":   "…markdown…"
}
```

## Run it

```bash
# regenerate every row of the sections in build_manifest.py's SCOPE
for f in leanification/Chapter3_GraphTheory/Section3_{1,2}/tex/*_for_website.json; do
  ref=$(basename "$f" _for_website.json)
  python3 building_website/scripts/fetch_row.py "$ref"
done
python3 building_website/scripts/build_manifest.py

# serve locally
cd building_website/website && python3 -m http.server 8000   # → http://localhost:8000
```

To add a section: drop it into `SCOPE` in `build_manifest.py`, run
`fetch_row.py` over its rows, run `build_manifest.py`, commit.

## The website (`website/`)

`app.js` is a thin client-side renderer. On load it fetches
`data/manifest.json` for the sidebar, then `data/<ref>.json` for the
hash-routed row:

- `#`/`#home`        → home page
- `#<ref>`           → entry view (TeX statement | Lean statement,
                       four action buttons, explanation panels)
- `#proof/<ref>`     → dedicated proof page (rendered proof `.tex`)

The Lean pane shows the `lean` list: a single declaration renders as
one code block; multiple declarations page through a prev/next
carousel. KaTeX renders math (project macros registered in
`KATEX_MACROS`); a custom Lean 4 grammar drives highlight.js.

## Deploy

`.github/workflows/pages.yml` runs on every push to `main`: it
re-runs `build_manifest.py`, then publishes `building_website/website/`
to GitHub Pages. `CNAME` + the Namecheap DNS record point the custom
domain at it.

## Testing

`/tmp/test_render.js` (a jsdom harness, not committed) exercises
`renderEntry` against every `data/<ref>.json` to catch render-time
crashes — worth recreating and running after any `app.js` change.
