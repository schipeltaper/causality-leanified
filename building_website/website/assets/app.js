/* =========================================================================
   Causality, Leanified — client-side renderer.

   On load, fetches `data/manifest.json` to build the left sidebar tree,
   then fetches `data/<ref>.json` (where <ref> comes from the URL hash, or
   defaults to def_3_1) and renders the entry into the main content area.

   All math expressions (KaTeX delimiters) are rendered after the DOM is
   populated. Lean code blocks are syntax-highlighted via highlight.js.
   ========================================================================= */

const DEFAULT_REF = "def_3_1";
const REPO_URL    = "https://github.com/schipeltaper/causality-leanified";
const REPO_BRANCH = "main";  // the file viewers link to this branch

/* KaTeX macros for project-specific math commands, mirroring
   `leanification/preamble.tex`. The TIKZ edge arrows (`\tuh`, `\hut`,
   `\huh`) are macros with an optional `[opts]` argument in the LaTeX
   preamble that draws a real arrow; KaTeX has no TIKZ, so we
   approximate with stock arrow tokens — the optional opts argument is
   harmless because in math expressions in this project these macros are
   only ever used as bare operator-style tokens (`v_1 \tuh v_2`).
   Extend this dict as new macros surface in later sections.            */
const KATEX_MACROS = {
  /* delimiter pairs ( \lp…\rp, \lB…\rB, \lI…\rI, \lC…\rC ) */
  "\\lp": "\\left(",  "\\rp": "\\right)",
  "\\lt": "\\left(",  "\\rt": "\\right)",
  "\\lB": "\\left[",  "\\rB": "\\right]",
  "\\lI": "\\left|",  "\\rI": "\\right|",
  "\\lC": "\\left\\{","\\rC": "\\right\\}",

  /* set operations */
  "\\ins": "\\subseteq",  "\\sni": "\\supseteq",
  "\\sm":  "\\setminus",  "\\x":   "\\times",
  "\\dcup": "\\mathbin{\\dot{\\cup}}",
  "\\bigdcup": "\\bigsqcup",
  "\\cmpl": "\\mathsf{c}",

  /* "such that" / conditioning bars */
  "\\st":     "\\mid",
  "\\given":  "\\mid",
  "\\kgiven": "\\,\\|\\,",

  /* number sets / blackboard */
  "\\N": "\\mathbb{N}", "\\Z": "\\mathbb{Z}",
  "\\R": "\\mathbb{R}", "\\Q": "\\mathbb{Q}",
  "\\E": "\\mathbb{E}", "\\Exp": "\\mathbb{E}",
  "\\I": "\\mathbf{1}",

  /* decorations */
  "\\id": "\\mathrm{id}",
  "\\ol": "\\overline",  "\\ul": "\\underline",

  /* graph-theoretic roman operators */
  "\\Pa": "\\mathrm{Pa}",   "\\pa": "\\mathrm{pa}",
  "\\Ch": "\\mathrm{Ch}",   "\\Anc": "\\mathrm{Anc}",
  "\\Desc": "\\mathrm{Desc}", "\\NonDesc": "\\mathrm{NonDesc}",
  "\\Dist": "\\mathrm{Dist}", "\\Sc": "\\mathrm{Sc}",
  "\\MBl": "\\mathrm{Mb}",  "\\Pred": "\\mathrm{Pred}",
  "\\Adj": "\\mathrm{Adj}", "\\AnCl": "\\mathrm{AnCl}",
  "\\Ant": "\\mathrm{Ant}", "\\Fa": "\\mathrm{Fa}",
  "\\Nb": "\\mathrm{Nb}",   "\\Sib": "\\mathrm{Sib}",
  "\\Di": "\\mathrm{Di}",

  /* construction / do-calculus operators */
  "\\doit": "\\operatorname{do}",
  "\\swig": "\\mathrm{swig}",
  "\\spl":  "\\mathrm{split}",
  "\\marg": "\\mathrm{mar}",  "\\moral": "\\mathrm{mor}",
  "\\ske":  "\\mathrm{ske}",  "\\can":  "\\mathrm{can}",
  "\\aug":  "\\mathrm{aug}",  "\\acy":  "\\mathrm{acy}",
  "\\Sym":  "\\mathrm{Sym}",

  /* (conditional) independence — the full Perp / iPerp family */
  "\\Indep":   "\\mathrel{\\perp\\!\\!\\!\\perp}",
  "\\nIndep":  "\\mathrel{\\not\\mkern-2mu\\perp\\!\\!\\!\\perp}",
  "\\Perp":    "\\perp",
  "\\nPerp":   "\\not\\perp",
  "\\dPerp":   "\\perp^{d}",
  "\\iPerp":   "\\perp^{i}",
  "\\mPerp":   "\\perp^{m}",
  "\\sPerp":   "\\perp^{\\sigma}",
  "\\isPerp":  "\\perp^{i\\sigma}",
  "\\imPerp":  "\\perp^{im}",
  "\\idPerp":  "\\perp^{id}",
  "\\ndPerp":  "\\not\\perp^{d}",
  "\\niPerp":  "\\not\\perp^{i}",
  "\\nmPerp":  "\\not\\perp^{m}",
  "\\nsPerp":  "\\not\\perp^{\\sigma}",
  "\\nisPerp": "\\not\\perp^{i\\sigma}",
  "\\nimPerp": "\\not\\perp^{im}",
  "\\nidPerp": "\\not\\perp^{id}",

  /* CDMG / PAG edge relations — TIKZ arrows in the LN; approximated
     here. `t`/`h`/`s`/`o` = tail / arrowhead / star ("either") /
     circle. The first letter is the endpoint at the LEFT argument,
     the second at the RIGHT. So `\tuh` = tail-…-head (right arrow). */
  "\\tuh": "\\mathrel{\\rightarrow}",
  "\\hut": "\\mathrel{\\leftarrow}",
  "\\huh": "\\mathrel{\\leftrightarrow}",
  "\\hus": "\\mathrel{\\leftarrow\\!{*}}",
  "\\suh": "\\mathrel{{*}\\!\\rightarrow}",
  "\\sus": "\\mathrel{{*}\\!\\leftrightarrow\\!{*}}",
  "\\ot":  "\\mathrel{\\leftarrow}",
  "\\oto": "\\mathrel{\\leftrightarrow}",
  "\\tut": "\\mathrel{-}",
};

/* `\Acal` … `\Zcal`  →  `\mathcal{A}` … `\mathcal{Z}`, plus the `\Abf`
   / `\Zbf` series. The LN defines all 52 via `\providecommand`; we
   register them up-front so any future row that uses one renders. */
for (let i = 0; i < 26; i++) {
  const c = String.fromCharCode(65 + i);
  KATEX_MACROS[`\\${c}cal`] = `\\mathcal{${c}}`;
  KATEX_MACROS[`\\${c}bf`]  = `\\mathbf{${c}}`;
}

/* ------------------------------------------------------------------ utils */

const $ = (sel, root = document) => root.querySelector(sel);

function el(tag, attrs = {}, ...children) {
  const node = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (v === null || v === undefined || v === false) continue;
    if (k === "class") node.className = v;
    else if (k === "html") node.innerHTML = v;
    else if (k.startsWith("on") && typeof v === "function") {
      node.addEventListener(k.slice(2).toLowerCase(), v);
    } else {
      node.setAttribute(k, v);
    }
  }
  for (const c of children) {
    if (c === null || c === undefined || c === false) continue;
    node.append(c instanceof Node ? c : document.createTextNode(c));
  }
  return node;
}

async function fetchJSON(url) {
  const r = await fetch(url, { cache: "no-store" });
  if (!r.ok) throw new Error(`fetch ${url} → HTTP ${r.status}`);
  return r.json();
}

function renderMath(root) {
  if (typeof renderMathInElement !== "function") return;
  renderMathInElement(root, {
    macros: KATEX_MACROS,
    delimiters: [
      { left: "$$", right: "$$", display: true  },
      { left: "\\[", right: "\\]", display: true  },
      { left: "$",  right: "$",  display: false },
      { left: "\\(", right: "\\)", display: false },
    ],
    throwOnError: false,
  });
}

/* ----------------------------------------------------------------------
   Lean pane.

   The row's JSON carries `lean_blocks: [{kind, code}]`, one entry per
   marker-wrapped region in the .lean source. `kind` is "main" for the
   row's headline declaration and "helper" for supporting decls the main
   one needs to type-check. Each block renders as its own block with a
   small label so the reader can tell support code apart from the
   headline declaration.
   ---------------------------------------------------------------------- */

/* Highlight every Lean code block inside `root` (idempotent). */
function highlightLeanIn(root) {
  if (typeof hljs === "undefined") return;
  registerLeanGrammar();
  root.querySelectorAll("pre code.language-lean").forEach((b) => {
    if (b.dataset.highlighted === "yes") return;
    hljs.highlightElement(b);
  });
}

/* Lean pane. Each block renders with:
     - a label (kind: main / helper)
     - a per-block "Comments ▾" button that flips this block's code
       between its bare `code` and its `code_annotated` variant (the
       same code with a `--` comment line above each non-trivial line).
       Default: off. Each block toggles independently.
     - a per-block "Explain ▾" button that toggles a Markdown
       explanation panel beneath the code (disabled if no explanation
       was generated). */
function buildLeanPane(data) {
  const body = el("div", { class: "pane-body lean-pane-body" });
  const blocks = data.lean_blocks || [];
  if (blocks.length === 0) {
    const userSkipped = data.status &&
      data.status.solved === "yes" &&
      data.status.formalized === "no";
    if (userSkipped) {
      body.append(el("div", { class: "user-skipped" },
        "User did not deem it necessary to formalize this into Lean."));
    } else {
      body.append(el("div", { class: "missing" }, "(no Lean blocks marked)"));
    }
    return body;
  }

  for (const b of blocks) {
    const kind = b.kind === "main" ? "main" : "helper";
    const codeNode = el("code", { class: "language-lean" }, b.code);
    const codePre  = el("pre", {}, codeNode);

    // Per-block comments toggle (only when a non-trivial annotated
    // version exists).
    const hasAnnotated = !!(b.code_annotated && b.code_annotated.trim() && b.code_annotated !== b.code);
    let commentsOn = false;
    const commentsBtn = el("button", {
      class: "block-comments-btn", type: "button",
      "aria-label": "Toggle line-by-line comments in this block",
      title: hasAnnotated
        ? "Show or hide a `-- comment` line above each non-trivial Lean line in this block."
        : "No annotated variant generated for this block.",
    }, "Comments");
    if (!hasAnnotated) {
      commentsBtn.disabled = true;
      commentsBtn.classList.add("disabled");
    } else {
      commentsBtn.textContent = "Comments ▾";
      commentsBtn.addEventListener("click", () => {
        commentsOn = !commentsOn;
        const next = commentsOn ? b.code_annotated : b.code;
        codePre.innerHTML = "";
        codePre.append(el("code", { class: "language-lean" }, next));
        commentsBtn.textContent = commentsOn ? "Comments ▴" : "Comments ▾";
        commentsBtn.classList.toggle("on", commentsOn);
        highlightLeanIn(codePre);
      });
    }

    // Per-block explanation panel.
    const explanation = (b.explanation || "").trim();
    const explanationDiv = el("div", { class: "block-explanation markdown-body" });
    if (explanation) {
      explanationDiv.innerHTML = typeof marked !== "undefined"
        ? marked.parse(explanation, { gfm: true, breaks: false })
        : `<pre>${explanation}</pre>`;
    }
    let explainOpen = false;
    const explainBtn = el("button", {
      class: "block-explain-btn", type: "button",
      "aria-label": "Toggle the human-language explanation for this block",
    }, "Explain");
    if (!explanation) {
      explainBtn.disabled = true;
      explainBtn.classList.add("disabled");
      explainBtn.title = "No explanation generated for this block yet.";
    } else {
      explainBtn.textContent = "Explain ▾";
      explainBtn.addEventListener("click", () => {
        explainOpen = !explainOpen;
        explainBtn.textContent = explainOpen ? "Explain ▴" : "Explain ▾";
        explainBtn.classList.toggle("open", explainOpen);
        explanationDiv.classList.toggle("open", explainOpen);
        if (explainOpen) renderMath(explanationDiv);
      });
    }

    body.append(
      el("div", { class: `lean-block lean-block-${kind}` },
        el("div", { class: "lean-block-header" },
          el("div", { class: "lean-block-label" }, kind),
          el("div", { class: "lean-block-controls" }, commentsBtn, explainBtn),
        ),
        codePre,
        explanationDiv,
      ),
    );
  }

  return body;
}

/* The TeX pane has two versions: the original LN excerpt
   (`tex_block_html`) shown by default, and the worker's unambiguous
   version (`tex_statement.html`) reachable via a toggle. The pane
   label updates to match. */
function buildTexPane(data) {
  const origHtml    = data.tex_block_html || "";
  const unambigHtml = (data.tex_statement && data.tex_statement.html) || "";
  const body        = el("div", { class: "pane-body" });
  const labelText   = el("span", { class: "pane-label-main" });
  const toggle      = el("button", { class: "tex-version-toggle", type: "button" });

  // If only one version is available, fall through to that one and hide
  // the toggle entirely.
  const haveBoth = !!(origHtml && unambigHtml);
  let showingOriginal = !!origHtml;  // default: original; falls back to unambig when only that exists

  function paint() {
    const html = showingOriginal ? origHtml : unambigHtml;
    body.innerHTML = html || "<em>(missing)</em>";
    labelText.textContent = showingOriginal
      ? "Statement (lecture notes)"
      : "Statement (unambiguous)";
    toggle.textContent = showingOriginal
      ? "Unambiguous version →"
      : "← Back to original";
    renderMath(body);
  }
  if (!haveBoth) {
    toggle.style.display = "none";
  } else {
    toggle.addEventListener("click", () => { showingOriginal = !showingOriginal; paint(); });
  }
  paint();

  return el("section", { class: "pane pane-tex" },
    el("div", { class: "pane-label" }, labelText, toggle),
    body,
  );
}

/* Lean 4 grammar for highlight.js. Registered as the canonical `lean` /
   `lean4` language; overrides the built-in `lean.js` (Lean 3-flavoured)
   that would otherwise be shipped from cdnjs. Aims for atom-one-light:
   keywords (purple), built-ins / types (red), tactics (blue), operators
   and arrows (azure), comments (grey-green), doc-comments (italic green). */
function registerLeanGrammar() {
  if (typeof hljs === "undefined" || hljs.getLanguage("lean4-custom")) return;
  hljs.registerLanguage("lean", function (hljs) {
    return {
      name: "Lean 4",
      aliases: ["lean", "lean4"],
      case_insensitive: false,
      keywords: {
        keyword: [
          // declaration introducers
          "abbrev","axiom","class","def","deriving","example","extends","instance",
          "inductive","mutual","namespace","noncomputable","prelude","private",
          "protected","section","structure","theorem","lemma","unsafe","universe",
          "variable","where","with",
          // imports / open
          "import","open","export","attribute",
          // term / type level
          "fun","λ","let","if","then","else","match","have","show","suffices",
          "use","from","return","do",
          // control words inside `by` blocks that read like keywords
          "by","at","in",
        ],
        literal: ["true","false","rfl","sorry","trivial","this","_"],
        built_in: [
          // core
          "Prop","Type","Sort","Nat","Int","Real","Rat","Bool","String","Char",
          "List","Array","Vector","Option","Sum","Prod","Unit","Empty","PUnit",
          "Decidable","Subtype","Function","Subsingleton","Inhabited",
          // mathlib & project
          "Set","Finset","Multiset","Quotient","Setoid","Equiv","Disjoint",
          "SimpleGraph","Preorder","PartialOrder","LinearOrder","Lattice",
          "CDMG","Adjacent","Walk",
        ],
        title: [
          // tactic-style tokens we want coloured distinctly
          "intro","apply","exact","refine","simp","ring","linarith","omega",
          "push_neg","rcases","cases","obtain","constructor","rwa","rw",
          "have","show","suffices","unfold","convert","trans","contradiction",
          "by_contra","decide","assumption","fin_cases","induction",
          "calc","change","clear","rename_i","specialize","split","exists",
        ],
      },
      contains: [
        // /-- doc-comments -/
        {
          className: "doctag",
          begin: /\/--/, end: /-\//,
          relevance: 5,
        },
        // /- block comments -/  (note: nestable in Lean, but highlight.js
        // can't truly nest these — close on first -/)
        hljs.COMMENT(/\/-/, /-\//),
        // -- line comments
        hljs.COMMENT(/--/, /$/),
        // strings
        hljs.QUOTE_STRING_MODE,
        // numbers
        { className: "number", begin: /\b\d+(\.\d+)?/, relevance: 0 },
        // operators, arrows, set-membership glyphs
        {
          className: "operator",
          begin: /:=|=>|→|↦|↔|⊆|⊂|⊃|∈|∉|∀|∃|×ˢ|⦃|⦄|≠|≤|≥|∪|∩|⟨|⟩|·|≃|≡/,
        },
        // implicit args  {x : α}  ⦃x : α⦄
        {
          className: "params",
          begin: /[⦃{]/, end: /[⦄}]/,
          relevance: 0,
          contains: [
            {
              className: "operator",
              begin: /:|,|→/,
              relevance: 0,
            },
          ],
        },
      ],
    };
  });
}

function highlightCode(root) {
  if (typeof hljs === "undefined") return;
  registerLeanGrammar();
  root.querySelectorAll("pre code.language-lean").forEach((b) => {
    // hljs adds .hljs and the data-highlighted="yes" attr; skip if already done.
    if (b.dataset.highlighted === "yes") return;
    hljs.highlightElement(b);
  });
}

/* --------------------------------------------------------------- sidebar */

function renderSidebar(manifest, activeRef) {
  const tree = $("#sidebar-tree");
  tree.innerHTML = "";
  for (const ch of manifest.chapters) {
    const chDetails = el("details", { class: "ch", open: "" },
      el("summary", {}, `Chapter ${ch.chapter} · ${ch.title}`)
    );
    for (const sec of ch.sections) {
      const ul = el("ul");
      for (const row of sec.rows) {
        const link = el(
          "a",
          {
            href: `#${row.ref}`,
            class: [
              row.ref === activeRef ? "active" : "",
              row.available ? "" : "unavailable",
            ].filter(Boolean).join(" "),
            title: row.available ? "" : "Run `scripts/fetch_row.py " + row.ref + "` to populate",
          },
          row.label,
        );
        ul.append(el("li", {}, link));
      }
      chDetails.append(el("details", { class: "sec", open: "" },
        el("summary", {}, `${sec.section}`),
        ul,
      ));
    }
    tree.append(chDetails);
  }
}

/* ---------------------------------------------------------------- entry */

function renderEntry(data) {
  const human = data.ref.replace(/_/g, " ").replace(/(\w+) (\d+) (\d+)/, "$1 $2.$3");
  // Prefer the row's `type` (definition / notation / remark / lemma) over
  // the coarser `kind` (def / claim) so the header reads "Notation 3.2"
  // for an actual \begin{Not} entry rather than "Definition 3.2".
  const TYPE_LABELS = {
    definition: "Definition",
    notation:   "Notation",
    remark:     "Remark",
    lemma:      "Lemma",
    theorem:    "Theorem",
    corollary:  "Corollary",
    proposition: "Proposition",
  };
  const kindWord = TYPE_LABELS[data.type] || (data.kind === "def" ? "Definition" : "Claim");
  const sectionNum = data.section;
  const nIn = data.ref.split("_").pop();

  // ---- header ----
  const userSkippedFormalization = data.status.solved === "yes"
    && data.status.formalized === "no";
  const statusBadges = userSkippedFormalization
    ? [el("span", { class: "badge badge-note" }, "Not formalised — by choice")]
    : [
        data.status.formalized === "yes" ? el("span", { class: "badge badge-ok" }, "Formalised") : null,
        data.kind === "def"
          ? el("span", { class: "badge badge-note" }, "No proof (definition)")
          : (data.status.proven === "yes"
              ? el("span", { class: "badge badge-ok" }, "Proof complete")
              : el("span", { class: "badge badge-warn" }, "Proof in progress")),
      ];

  const header = el("header", { class: "entry-header" },
    el("div", { class: "entry-kind" }, `${kindWord} ${sectionNum.split(".")[0]}.${nIn}`),
    el("h1", { class: "entry-title" }, data.tex_statement.env_title || data.title),
    el("div", { class: "entry-status" }, ...statusBadges),
  );

  // ---- split: TeX (LN original ↔ unambiguous) | Lean (per-block panels) ----
  const texPane = buildTexPane(data);
  const leanBody = buildLeanPane(data);
  const leanPane = el("section", { class: "pane pane-lean" },
    el("div", { class: "pane-label" }, "Formalisation"),
    leanBody,
  );

  const split = el("div", { class: "split" }, texPane, leanPane);

  // ---- actions ----
  //
  // Three buttons (in this order):
  //   1. View TeX proof   — claims only; navigates to #proof/<ref>
  //   2. View Lean source — always; opens main_lean_file on GitHub
  //   3. Design choices   — toggles the panel below; disabled until LLM-populated
  const actions = el("footer", { class: "entry-actions" });

  if (data.kind === "claim" && data.tex_proof && data.tex_proof.html) {
    actions.append(el("a", {
      class: "btn",
      href: `#proof/${data.ref}`,
    }, "View TeX proof"));
  } else {
    actions.append(el("button", {
      class: "btn btn-disabled", "aria-disabled": "true", disabled: "",
      title: "Definitions have no proof",
    }, "View TeX proof"));
  }

  if (data.lean_source_url) {
    actions.append(el("a", {
      class: "btn",
      href: data.lean_source_url,
      target: "_blank", rel: "noopener",
      title: data.lean_source_url,
    }, "View Lean source"));
  }

  function explanationButton(label, panelId, content) {
    if (!content || !content.trim()) {
      return el("button", { class: "btn btn-disabled", "aria-disabled": "true", disabled: "" }, label);
    }
    return el("button", {
      class: "btn btn-toggle",
      "data-target": panelId,
      onclick: (e) => {
        const panel = document.getElementById(panelId);
        if (!panel) return;
        const showing = panel.classList.toggle("open");
        e.currentTarget.classList.toggle("active", showing);
      },
    }, label);
  }
  actions.append(explanationButton("Design choices", `${data.ref}--design`, data.design_choices));

  // ---- Explanation panel (initially hidden, toggled by the button above) ----
  function explanationPanel(panelId, title, markdown) {
    if (!markdown || !markdown.trim()) return null;
    const rendered = typeof marked !== "undefined"
      ? marked.parse(markdown, { gfm: true, breaks: false })
      : `<pre>${markdown}</pre>`;
    return el("section", { id: panelId, class: "explanation-pane" },
      el("div", { class: "pane-label" }, title),
      el("div", { class: "pane-body markdown-body", html: rendered }),
    );
  }
  const designChoicesPanel = explanationPanel(`${data.ref}--design`, "Design choices", data.design_choices);

  // The page-wide "Lean explanation" button + panel is gone — per-block
  // Explain buttons (rendered inline within each .lean-block) replace it.

  const article = el("article", { class: "entry", id: data.ref },
    header,
    split,
    actions,
    designChoicesPanel,
  );
  return article;
}

/* The dedicated proof page (URL hash: `#proof/<ref>`). Renders the full
   contents of the per-row proof .tex file — the restated statement env
   followed by the \begin{proof}…\end{proof} body — both already turned
   into HTML by `fetch_row.py`. A single action button links out to the
   raw .tex file on GitHub. */
function renderProofPage(data) {
  const nIn = data.ref.split("_").pop();
  const sectionNum = data.section;

  const header = el("header", { class: "entry-header" },
    el("a", { class: "back-link", href: `#${data.ref}` }, "← Back to statement"),
    el("div", { class: "entry-kind" }, `Proof of Claim ${sectionNum.split(".")[0]}.${nIn}`),
    el("h1", { class: "entry-title" }, data.tex_statement.env_title || data.title),
  );

  if (!data.tex_proof || !data.tex_proof.html) {
    return el("article", { class: "entry placeholder" },
      header,
      el("div", { class: "missing-body" },
        el("p", {}, "No proof TeX file recorded for this row."),
      ),
    );
  }

  const body = el("section", { class: "proof-page-body" },
    el("div", { class: "pane-body", html: data.tex_proof.html }),
  );

  const actions = el("footer", { class: "entry-actions" },
    el("a", {
      class: "btn",
      href: `${REPO_URL}/blob/${REPO_BRANCH}/${data.tex_proof.source_path}`,
      target: "_blank", rel: "noopener",
    }, "View TeX source"),
  );

  return el("article", { class: "entry proof-page", id: `proof--${data.ref}` },
    header,
    body,
    actions,
  );
}

function renderMissing(ref) {
  return el("article", { class: "entry placeholder" },
    el("header", { class: "entry-header" },
      el("div", { class: "entry-kind" }, ref),
      el("h1", { class: "entry-title" }, "Not yet generated"),
    ),
    el("div", { class: "missing-body" },
      el("p", {}, `No data file exists for ${ref}. Run:`),
      el("pre", {}, el("code", {}, `python3 building_website/scripts/fetch_row.py ${ref}`)),
      el("p", {}, "Then refresh this page."),
    ),
  );
}

/* The home page. Lives at URL hash `#home` (and `#`/empty hash also
   routes here). Self-contained — no row data fetched. */
function renderHome(manifest) {
  let covered = 0, total = 0;
  for (const ch of manifest.chapters) {
    for (const sec of ch.sections) {
      total += sec.rows.length;
      covered += sec.rows.filter((r) => r.available).length;
    }
  }

  return el("article", { class: "entry home" },
    el("header", { class: "entry-header home-header" },
      el("div", { class: "entry-kind" }, "An MSc thesis experiment"),
      el("h1", { class: "entry-title home-title" }, "Causality, Leanified"),
      el("p", { class: "home-tagline" },
        "A Lean 4 formalisation of the Causality lecture notes, automatically generated with Claude Code integrated into a scaffold built by Sam Ritchie",
      ),
    ),

    el("section", { class: "home-section" },
      el("h2", {}, "What you're looking at"),
      el("p", {},
        "Each definition and claim from the lecture notes appears side-by-side: ",
        "the LaTeX statement on the left, its Lean 4 formalisation on the right. ",
        "For claims, ", el("strong", {}, "View TeX proof"),
        " opens the rendered lecture-notes proof. ",
        el("strong", {}, "Lean explanation"), " and ",
        el("strong", {}, "Design choices"),
        " surface notes on the formalisation.",
      ),
      // el("p", { class: "home-coverage" },
      //   `Coverage right now: ${covered} / ${total} rows from section 3.1 of chapter 3 (Graph Theory). Later sections are queued.`,
      // ),
    ),

    el("section", { class: "home-section" },
      el("h2", {}, "The project"),
      el("p", {},
        "This site is the visible output of an experiment by ",
        el("a", { href: "https://samritchie.dev", target: "_blank", rel: "noopener" }, "Sam Ritchie"),
        " (MSc thesis): can a ",
        el("a", { href: "https://claude.com/claude-code", target: "_blank", rel: "noopener" }, "Claude Code"),
        "-driven scaffold automate the formalisation of an entire graduate-level mathematics text? ",
        "Worker agents formalise the lecture notes step-by-step, ",
        el("code", {}, "lake build"),
        " verifies each result, and this site renders the side-by-side review. The scaffold and the full Lean development live in the ",
        el("a", { href: "https://github.com/schipeltaper/causality-leanified", target: "_blank", rel: "noopener" }, "GitHub repository"),
        ".",
      ),
    ),

    el("section", { class: "home-section home-resources" },
      el("h2", {}, "Resources"),
      el("ul", {},
        el("li", {},
          el("a", {
            href: "https://staff.fnwi.uva.nl/j.m.mooij/articles/causality_lecture_notes_2025.pdf",
            target: "_blank", rel: "noopener",
          }, "Original lecture notes — Forré & Mooij, 2025 (PDF)"),
        ),
        el("li", {},
          el("a", {
            href: "https://github.com/schipeltaper/causality-leanified",
            target: "_blank", rel: "noopener",
          }, "Repository on GitHub"),
        ),
        el("li", {},
          el("a", { href: "https://lean-lang.org/", target: "_blank", rel: "noopener" },
            "Lean 4 — the proof assistant"),
        ),
        el("li", {},
          el("a", { href: "https://claude.com/claude-code", target: "_blank", rel: "noopener" },
            "Claude Code — the agent framework"),
        ),
      ),
    ),

    el("section", { class: "home-section home-cta" },
      el("a", { href: "#def_3_1", class: "btn btn-cta" },
        "Start with def 3.1 — CDMG  →",
      ),
    ),
  );
}

/* ----------------------------------------------------------------- main */

async function loadRoute(route, manifest) {
  const content = $("#content");
  content.innerHTML = "";
  if (route.mode === "home") {
    content.append(renderHome(manifest));
    renderSidebar(manifest, null);
  } else {
    try {
      const data = await fetchJSON(`data/${route.ref}.json`);
      if (route.mode === "proof") {
        content.append(renderProofPage(data));
      } else {
        content.append(renderEntry(data));
      }
    } catch (e) {
      content.append(renderMissing(route.ref));
    }
    renderSidebar(manifest, route.ref);
  }
  renderMath(content);
  highlightCode(content);
  // Update active link in sidebar.
  const activeHash = route.mode === "home" ? null
                   : route.mode === "proof" ? `#${route.ref}`
                   : `#${route.ref}`;
  $("#sidebar-tree").querySelectorAll("a").forEach((a) => {
    a.classList.toggle("active", a.getAttribute("href") === activeHash);
  });
  // Scroll to top whenever the route changes.
  $("#content").scrollTop = 0;
  window.scrollTo({ top: 0 });
}

function routeFromHash() {
  const h = location.hash.replace(/^#/, "").trim();
  const REF_RE = /^(def|claim)_\d+_\d+$/;
  if (h === "" || h === "home") {
    return { mode: "home" };
  }
  if (h.startsWith("proof/")) {
    const ref = h.slice("proof/".length);
    return { mode: "proof", ref: REF_RE.test(ref) ? ref : DEFAULT_REF };
  }
  return { mode: "entry", ref: REF_RE.test(h) ? h : DEFAULT_REF };
}

async function main() {
  let manifest;
  try {
    manifest = await fetchJSON("data/manifest.json");
  } catch (e) {
    $("#content").innerHTML =
      "<p style='color:#a00;padding:2rem'>Failed to load manifest.json. "
      + "Are you serving the site over HTTP? (Try <code>python3 -m http.server</code> "
      + "in the <code>website/</code> directory.)</p>";
    return;
  }
  await loadRoute(routeFromHash(), manifest);
  window.addEventListener("hashchange", () => loadRoute(routeFromHash(), manifest));
}

document.addEventListener("DOMContentLoaded", main);
