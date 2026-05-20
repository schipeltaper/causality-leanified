# `temp_present/` — website pilot

A throwaway folder for sketching the visual presentation of the
formalisation. Once we like the look, we'll promote `temp_present/website/`
to `website/` at the repo root and wire up a build pipeline.

## What's here

```
temp_present/
├── README.md                  ← this file
└── website/
    ├── index.html             ← demo page for def 3.1
    ├── assets/
    │   └── style.css          ← all styling
    └── data/
        ├── def_3_1.tex        ← extracted TeX body (no preamble/subfiles wrapper)
        └── def_3_1.lean       ← extracted Lean snippet (just the structure decl)
```

## What it shows

A single fully-styled entry — **def 3.1 (CDMG)** — with:

- a left sidebar listing every row of section 3.1 (other sections collapsed
  with row-count placeholders);
- a two-column "split" with the TeX statement on the left and the Lean
  formalisation on the right;
- status badges (Formalised / No proof);
- an action row with "View TeX proof", "Download proof PDF", "View full Lean
  source", "View TeX source" buttons. The two proof buttons are disabled
  for definitions; they'll light up for claims (e.g. claim 3.1 once we
  port it);
- an expandable "Design choices & equivalence with the LN" panel below the
  split, surfacing the prose we already write in the Lean file's
  design-notes comments.

## How to view locally

The page is static — no build step yet for the pilot. Just:

```bash
# Option A: any static server
cd temp_present/website
python -m http.server 8000
# → open http://localhost:8000
```

```bash
# Option B: open the file directly
open temp_present/website/index.html
```

(Direct-file opening works because all dependencies — KaTeX, highlight.js
— are loaded from CDNs. If you want it to work offline, mirror those
under `assets/vendor/` and update the `<link>`/`<script>` paths.)

## Dependencies (all CDN-loaded)

| What           | Why                              | Source                                 |
| -------------- | -------------------------------- | -------------------------------------- |
| KaTeX 0.16.11  | Render inline / display math     | `cdn.jsdelivr.net/npm/katex@0.16.11`   |
| highlight.js 11.9.0 + `lean.min.js` | Lean syntax highlighting | `cdnjs.cloudflare.com/.../highlight.js` |

KaTeX is configured with the standard four delimiters (`$…$`, `$$…$$`,
`\(…\)`, `\[…\]`). Prose-level LaTeX (`\begin{enumerate}`, `\emph{}`,
`\begin{Def}…\end{Def}`) is NOT processed by KaTeX — only by the build
pipeline (see below). For the pilot, we've translated that prose
to HTML by hand.

## The pipeline we'd build next

For one definition, hand-translation is fine. For 35+ rows in chapter 3
alone, we need a script. The shape:

```
data.json + per-row .tex files + per-row .lean files
                       │
                       ▼
   scaffold/build_site.py   (parses TeX prose → HTML; extracts Lean snippets)
                       │
                       ▼
              website/index.html (TOC)
              website/3_1/def_3_1.html   ← one page per row
              website/3_1/def_3_2.html
              website/3_1/claim_3_1.html
              ...
```

Specifically, the build script would:

1. Read `data.json` for every chapter; build the sidebar nav (chapter →
   section → row) once and inject it into every page.
2. For each row, read its `tex_file` (or `tex_block` field in
   `data.json`) and convert the prose to HTML. KaTeX handles the math
   automatically. Prose translation needs a tiny converter for
   `\emph{}`, `\begin{enumerate}…\end{enumerate}`, `\begin{Def}…\end{Def}`,
   `\textbf{}`, etc. We have two options:
   - **Custom converter** (~150 LoC of Python). Faithful, narrow scope,
     no dependencies. Recommended.
   - **Pandoc** (`pandoc statement.tex -o statement.html --katex`).
     High-fidelity but adds a heavy dependency and emits surprising
     wrappers we'd have to strip.
3. For each row, read `main_lean_file` and extract the declaration named
   in the row (we'd add a small `-- BEGIN <ref>` / `-- END <ref>` marker
   convention to make this robust, OR parse the file and grab the
   `structure`/`def`/`theorem` block by name).
4. Emit one HTML page per row using a Jinja2 template; the TOC links
   already exist in the sidebar.
5. Optionally, emit a single bundle / SPA. Static-per-page is simpler
   and works perfectly with GitHub Pages caching.

## Workflow changes that would help

You said you're flexible on what the scaffold emits. A few small tweaks
would make build_site much simpler and reduce drift:

1. **Per-statement Lean range marker.** Wrap the statement in the `.lean`
   file with `-- BEGIN_STATEMENT def_3_1` / `-- END_STATEMENT def_3_1`
   comments, or just `-- @row def_3_1` immediately above the
   `structure`/`theorem`. The build script then doesn't need to parse
   Lean — it just slices by line.
2. **Per-statement TeX without the subfiles wrapper.** Keep
   `data.json`'s `tex_block` field as the canonical source (it already
   strips the wrapper). The pipeline would consume that field, not the
   raw `.tex` file.
3. **Explicit `\uses{…}` annotations in data.json.** Add a `depends_on:
   [def_3_1, def_3_3]` field per row. Free dependency graph downstream.
4. **`status` field that maps to badges.** You already have
   `formalized` / `proven` / `solved`. We just need to standardise the
   value vocabulary so the build script can map values → badge colours
   without special-casing.

None of this is required for the pilot; it's what would clean up the
generator once you've signed off on the look.

## Getting this onto your domain (GitHub Pages + Namecheap)

The site is fully static. Recommended setup:

### 1. Promote and publish

When the design is final, move:

```
temp_present/website/  →  /docs/   (or /website/)
```

In the repo settings → **Pages**:

- Source: **Deploy from a branch**
- Branch: `main`, folder: `/docs` (GitHub Pages natively serves
  `/docs`; if you prefer `/website` use a GitHub Actions workflow
  instead — also one-file, see below).

For an Actions-based deploy (more flexible — needed once we add a build
step), drop this into `.github/workflows/pages.yml`:

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
      - name: Build site
        run: python scaffold/build_site.py
      - uses: actions/upload-pages-artifact@v3
        with: { path: ./website-build }
      - uses: actions/deploy-pages@v4
```

### 2. Wire up the Namecheap subdomain

Pick a subdomain — say `causality.yourdomain.com`. Two steps:

a. **In the published folder, add a `CNAME` file** with one line:

   ```
   causality.yourdomain.com
   ```

   (When deploying via Actions, the `CNAME` should be included in the
   uploaded artifact — easiest is to commit it to `docs/CNAME` or have
   the build script copy it into `website-build/CNAME`.)

b. **In Namecheap → Advanced DNS** for the apex domain:

   | Type    | Host         | Value                          | TTL  |
   | ------- | ------------ | ------------------------------ | ---- |
   | `CNAME` | `causality`  | `schipeltaper.github.io.`      | Auto |

   (Note the trailing dot.) If you want the apex (e.g.
   `yourdomain.com` itself, not a subdomain) the records change — four
   `A` records pointing at GitHub's IPs (185.199.108.153,
   185.199.109.153, 185.199.110.153, 185.199.111.153) plus optionally
   an `AAAA` for IPv6.

c. In repo settings → Pages → **Custom domain**: enter
   `causality.yourdomain.com`. Tick **Enforce HTTPS** once the cert
   provisions (a few minutes to ~24h).

DNS usually propagates in 5–60 minutes for a subdomain.

## Open questions

These will affect the next iterations — answers welcome:

1. **One page per entry, or section-scrolling page?** Faabian gives a
   single long page per section. Tao gives one page per "chapter
   section". Single-entry pages are easier to deep-link (`/3_1/def_3_1`)
   but require more clicking. Sectional pages scroll more but match
   how textbooks read. We can do either — and even both (sectional
   page with stable anchors).
2. **Proof rendering.** For a claim with a proof, would you like:
   (a) inline-rendered TeX proof on the same page (under the split),
   (b) a separate `/3_1/claim_3_1/proof.html` page,
   (c) a downloaded PDF compiled by `scaffold/build_and_commit.sh`?
   Easiest is (a) for short proofs and (c) as a fallback link for
   long ones.
3. **Status / badge colour scheme.** Right now:
   - green "Formalised" = `formalized: "yes"`
   - grey "No proof (definition)" = `proven: "n/a"`
   - we'd add yellow "Sorry remaining" once we encounter one.
   Match what you want publicly visible.
4. **Dependency graph.** Worth building? leanblueprint gives it free
   but we'd have to ape it; pyvis/d3 + the per-row `depends_on` lists
   would do it in maybe a day. Useful for collaborators; less useful
   for casual readers.
5. **Pinning Lean snippets vs fetching live from `main`.** Build-time
   extraction freezes the snippet at deploy time (deterministic but
   can drift). Runtime fetch from raw.githubusercontent (via small
   JS) keeps the page always-current but adds a network call. Pinning
   is probably right — the deploy is cheap.
