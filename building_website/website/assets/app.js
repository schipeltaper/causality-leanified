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

/* KaTeX macros for project-specific math commands. Extend as new ones appear.
   See `leanification/preamble.tex` for the originals. */
const KATEX_MACROS = {
  "\\ins": "\\subseteq",
  "\\x":   "\\times",
  "\\id":  "\\mathrm{id}",
};

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

function highlightCode(root) {
  if (typeof hljs === "undefined") return;
  root.querySelectorAll("pre code.language-lean").forEach((b) => hljs.highlightElement(b));
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
  const kindWord = data.kind === "def" ? "Definition" : "Claim";
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

  // ---- Lean comments / design notes (collapsible) ----
  const allComments = data.lean
    .filter((b) => b.comments && b.comments.trim())
    .map((b) => b.comments)
    .join("\n\n---\n\n");
  const commentsBlock = allComments
    ? el("details", { class: "design-notes" },
        el("summary", {}, "Lean comments & design notes"),
        el("div", { class: "design-notes-body" },
          el("pre", {}, el("code", { class: "language-lean" }, allComments)),
        ),
      )
    : null;

  // ---- assemble ----
  const article = el("article", { class: "entry", id: data.ref },
    header,
    split,
    proofBlock,
    leanProofBlock,
    actions,
    commentsBlock,
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
