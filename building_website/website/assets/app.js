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
  /* set operations */
  "\\ins":  "\\subseteq",
  "\\x":    "\\times",
  "\\sm":   "\\setminus",
  "\\id":   "\\mathrm{id}",

  /* number sets */
  "\\N":    "\\mathbb{N}",
  "\\Z":    "\\mathbb{Z}",
  "\\R":    "\\mathbb{R}",
  "\\Q":    "\\mathbb{Q}",

  /* large brace delimiter pair  ( \lC … \rC )  */
  "\\lC":   "\\left\\{",
  "\\rC":   "\\right\\}",

  /* graph-theoretic roman operators */
  "\\Pa":    "\\mathrm{Pa}",
  "\\Ch":    "\\mathrm{Ch}",
  "\\Anc":   "\\mathrm{Anc}",
  "\\Desc":  "\\mathrm{Desc}",
  "\\Dist":  "\\mathrm{Dist}",
  "\\Sc":    "\\mathrm{Sc}",
  "\\MBl":   "\\mathrm{Mb}",

  /* CDMG edge relations — TIKZ arrows in the LN; approximated here.
     `t`/`h`/`s` = tail / arrowhead / star (i.e. "either"). The first
     letter is the endpoint at the LEFT argument, the second at the
     RIGHT argument. So `\tuh` = tail-…-head (right arrow), etc.       */
  "\\tuh":   "\\mathrel{\\rightarrow}",
  "\\hut":   "\\mathrel{\\leftarrow}",
  "\\huh":   "\\mathrel{\\leftrightarrow}",
  "\\hus":   "\\mathrel{\\leftarrow\\!{*}}",
  "\\suh":   "\\mathrel{{*}\\!\\rightarrow}",
  "\\sus":   "\\mathrel{{*}\\!\\leftrightarrow\\!{*}}",
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
  const statusBadges = [
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

  // ---- split ----
  const texPane = el("section", { class: "pane pane-tex" },
    el("div", { class: "pane-label" }, "Statement (lecture notes)"),
    el("div", { class: "pane-body", html: data.tex_statement.html || "<em>(missing)</em>" }),
  );

  const leanBody = el("div", { class: "pane-body" });
  if (data.lean.length === 0) {
    leanBody.append(el("div", { class: "missing" }, "(no Lean blocks found)"));
  } else {
    for (const b of data.lean) {
      if (data.lean.length > 1 && b.part) {
        leanBody.append(el("div", { class: "lean-part-label" }, `part ${b.part}`));
      }
      const pre = el("pre", {}, el("code", { class: "language-lean" }, b.statement));
      leanBody.append(pre);
    }
  }

  const leanMainPath = data.lean[0]?.source_path;
  const leanPane = el("section", { class: "pane pane-lean" },
    el("div", { class: "pane-label" },
      "Formalisation",
      leanMainPath
        ? el("span", { class: "pane-label-aux" }, leanMainPath.split("/").pop())
        : null,
    ),
    leanBody,
  );

  const split = el("div", { class: "split" }, texPane, leanPane);

  // ---- actions ----
  const actions = el("footer", { class: "entry-actions" });

  const texSource = data.tex_statement.source_path;
  if (texSource) {
    actions.append(el("a", {
      class: "btn",
      href: `${REPO_URL}/blob/${REPO_BRANCH}/${texSource}`,
      target: "_blank", rel: "noopener",
    }, "View TeX source"));
  }
  if (leanMainPath) {
    actions.append(el("a", {
      class: "btn",
      href: `${REPO_URL}/blob/${REPO_BRANCH}/${leanMainPath}`,
      target: "_blank", rel: "noopener",
    }, "View Lean source"));
  }
  if (data.tex_proof && data.tex_proof.source_path) {
    actions.append(el("a", {
      class: "btn",
      href: `${REPO_URL}/blob/${REPO_BRANCH}/${data.tex_proof.source_path}`,
      target: "_blank", rel: "noopener",
    }, "View TeX proof"));
  } else if (data.kind === "def") {
    actions.append(el("a", { class: "btn btn-disabled", "aria-disabled": "true" },
                       "View TeX proof"));
  }

  // Explanation toggles — sit in the same action row, but open a panel
  // below the entry rather than navigating away. Disabled (greyed) when
  // the LLM step hasn't produced prose yet.
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
  actions.append(explanationButton("Lean explanation", `${data.ref}--lean-expl`, data.lean_explanation));
  actions.append(explanationButton("Design choices",   `${data.ref}--design`,    data.design_choices));

  // ---- TeX proof body (if claim) ----
  const proofBlock = data.tex_proof && data.tex_proof.html
    ? el("section", { class: "tex-proof-pane" },
        el("div", { class: "pane-label" }, "Proof (lecture notes)"),
        el("div", { class: "pane-body", html: data.tex_proof.html }),
      )
    : null;

  // ---- Lean proof body (if claim) ----
  const leanProofs = data.lean.filter((b) => b.proof);
  const leanProofBlock = leanProofs.length
    ? el("section", { class: "lean-proof-pane" },
        el("div", { class: "pane-label" }, "Lean proof"),
        el("div", { class: "pane-body" },
          ...leanProofs.flatMap((b) => [
            data.lean.length > 1 && b.part
              ? el("div", { class: "lean-part-label" }, `part ${b.part}`)
              : null,
            el("pre", {}, el("code", { class: "language-lean" }, b.proof)),
          ]).filter(Boolean)
        ),
      )
    : null;

  // ---- Explanation panels (initially hidden, toggled by the action buttons) ----
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
  const leanExplPanel    = explanationPanel(`${data.ref}--lean-expl`, "Lean explanation", data.lean_explanation);
  const designChoicesPanel = explanationPanel(`${data.ref}--design`,  "Design choices",   data.design_choices);

  // ---- assemble ----
  const article = el("article", { class: "entry", id: data.ref },
    header,
    split,
    proofBlock,
    leanProofBlock,
    actions,
    leanExplPanel,
    designChoicesPanel,
  );
  return article;
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

/* ----------------------------------------------------------------- main */

async function loadRef(ref, manifest) {
  const content = $("#content");
  content.innerHTML = "";
  try {
    const data = await fetchJSON(`data/${ref}.json`);
    content.append(renderEntry(data));
  } catch (e) {
    content.append(renderMissing(ref));
  }
  renderSidebar(manifest, ref);
  renderMath(content);
  highlightCode(content);
  // Update active link in sidebar
  $("#sidebar-tree").querySelectorAll("a").forEach((a) => {
    a.classList.toggle("active", a.getAttribute("href") === `#${ref}`);
  });
}

function refFromHash() {
  const h = location.hash.replace(/^#/, "").trim();
  return /^(def|claim)_\d+_\d+$/.test(h) ? h : DEFAULT_REF;
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
  await loadRef(refFromHash(), manifest);
  window.addEventListener("hashchange", () => loadRef(refFromHash(), manifest));
}

document.addEventListener("DOMContentLoaded", main);
