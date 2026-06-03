"""Convert the LaTeX prose used in this project to HTML.

Math (`$…$`, `\\(…\\)`, `$$…$$`, `\\[…\\]`) is left intact; the website
renders it client-side with KaTeX. Project-specific math macros (`\\ins`,
`\\hus`, `\\tuh`, …) are registered as KaTeX macros in the website's
`app.js`, not expanded here.

Only the prose-level LaTeX that the scaffold actually emits is supported.
Extend as new patterns appear. The patterns currently handled:

  - subfiles wrapper:                            stripped
  - `\\def\\rowref{...}` / `\\def\\rowtitle{...}` stripped
  - `\\phantomsection`, `\\label{...}`           stripped
  - whole-line `%` comments                      stripped
  - `\\begin{defmark}`, `\\begin{claimmark}`     stripped (wrappers)
  - `\\begin{Def}[Title]…\\end{Def}` and friends body extracted, env + title returned
  - `\\begin{proof}…\\end{proof}`                rendered as a styled block
  - `\\begin{enumerate}[label=\\roman*.)]…`       → <ol class="roman-paren">
  - `\\begin{enumerate}[resume,label=\\roman*.)]` → <ol class="roman-paren"> with continued counter
  - `\\begin{enumerate}` / `\\begin{itemize}`     → <ol> / <ul>
  - `\\item[opt] …`                              → <li>…</li> (`[]` → no-marker)
  - `\\emph{X}` / `\\textit{X}`                  → <em>X</em>
  - `\\textbf{X}`                                → <strong>X</strong>
  - `\\refrow{ref}`                              → <a href="#ref"><code>ref</code></a>
  - `---`                                        → — (em dash)
  - `~`                                          → &nbsp;
  - `\\\\` (line break)                          → <br>
  - paragraph breaks (blank lines)               → </p><p>
"""

from __future__ import annotations
import re
from dataclasses import dataclass
from pathlib import Path


_REPO_ROOT = Path(__file__).resolve().parents[2]
_LABEL_REF_RE = re.compile(r"^(def|claim)_\d+_\d+")
_LABEL_INDEX: dict[str, str] | None = None


def _label_index() -> dict[str, str]:
    """Lazy-built map from LaTeX label (the `X` in `\\label{X}`) to the
    row ref that owns the file the label appears in. Walks every per-row
    .tex under leanification/ once.

    Used by inline_convert to turn `\\ref{X}` into a link to the row's
    page on the website. If a label isn't found (e.g. labels in the LN
    aggregate `main.tex` or unsolved rows), `\\ref{X}` still renders as
    inline code with the bare label."""
    global _LABEL_INDEX
    if _LABEL_INDEX is not None:
        return _LABEL_INDEX
    idx: dict[str, str] = {}
    label_re = re.compile(r"\\label\{([^}]+)\}")
    for tex in (_REPO_ROOT / "leanification").glob("Chapter*/Section*/tex/*.tex"):
        m = _LABEL_REF_RE.match(tex.name)
        if not m:
            continue
        ref = m.group(0)
        try:
            text = tex.read_text(encoding="utf-8")
        except OSError:
            continue
        for lm in label_re.finditer(text):
            label = lm.group(1)
            idx.setdefault(label, ref)
    _LABEL_INDEX = idx
    return idx


# Every theorem-like env declared in `leanification/preamble.tex` via
# `\newtheorem*{Name}{...}`. The body of a row's TeX file lives inside
# exactly one of these (sometimes nested inside a `defmark`/`claimmark`
# wrapper which we strip first). The order matters only for `match`
# fall-through — alternative envs are tried longest-name-first below.
THEOREM_ENVS = [
    "DefThm", "DefLem", "NotLem",
    "Construction", "Conclusion", "Motivation",
    "Def", "Lem", "Prp", "Cor", "Thm", "Con", "Fct", "Prn",
    "Not", "Rem", "Note", "Cau", "Eg", "Tho", "Exc", "Ques",
    "Expl", "Disc", "Axm", "Alg", "sa",
]
WRAPPER_ENVS = ["defmark", "claimmark"]


@dataclass
class TexBlock:
    body_html: str
    env: str | None
    title: str | None


def strip_subfiles_wrapper(tex: str) -> str:
    """Keep only what's between \\begin{document} and \\end{document}, drop
    bookkeeping directives, and remove whole-line `%` comments. Also
    rewrites `\\begin{restatable}{TYPE}{NAME}…\\end{restatable}` to
    `\\begin{TYPE}…\\end{TYPE}` so the downstream theorem-env unwrap
    handles it like any other Prp/Lem/Rem."""
    m = re.search(r"\\begin\{document\}(.*?)\\end\{document\}", tex, re.DOTALL)
    if m:
        tex = m.group(1)
    tex = re.sub(r"\\def\\row(ref|title)\{[^}]*\}", "", tex)
    tex = re.sub(r"\\phantomsection", "", tex)
    tex = re.sub(r"\\label\{[^}]*\}", "", tex)
    tex = re.sub(r"^\s*%.*$", "", tex, flags=re.MULTILINE)
    # `\begin{restatable}{TYPE}{NAME}…\end{restatable}` → `\begin{TYPE}…\end{TYPE}`
    def _restatable(m: re.Match) -> str:
        env_type = m.group(1)
        body     = m.group(3)
        return f"\\begin{{{env_type}}}{body}\\end{{{env_type}}}"
    tex = re.sub(
        r"\\begin\{restatable\}\{(\w+)\}\{(\w+)\}(.*?)\\end\{restatable\}",
        _restatable, tex, flags=re.DOTALL,
    )
    return tex


def _strip_proof_blocks(body: str) -> str:
    """Strip `\\begin{proof}…\\end{proof}` blocks from a body. Used only
    on STATEMENT files — statements should never contain a proof block,
    but some are authored with one embedded (e.g. claim_3_27 in the LN's
    convention) and showing that on the statement page mixes content
    that belongs on the dedicated proof page."""
    return _strip_balanced_env(body, "proof")


def _find_matching_end(text: str, env: str, after_begin: int) -> tuple[int, int] | None:
    """Find the `\\end{env}` that matches a `\\begin{env}` whose body
    starts at `after_begin`, accounting for any nested same-env begins.
    Returns (start, end) of the matching `\\end{…}` or None."""
    begin_re = re.compile(rf"\\begin\{{{re.escape(env)}\}}")
    end_re   = re.compile(rf"\\end\{{{re.escape(env)}\}}")
    depth = 1
    pos = after_begin
    while pos < len(text):
        nb = begin_re.search(text, pos)
        ne = end_re.search(text, pos)
        if ne is None:
            return None
        if nb is not None and nb.start() < ne.start():
            depth += 1
            pos = nb.end()
        else:
            depth -= 1
            if depth == 0:
                return (ne.start(), ne.end())
            pos = ne.end()
    return None


def _strip_balanced_env(text: str, env: str) -> str:
    """Remove every balanced `\\begin{env}…\\end{env}` block, including
    nested instances of the same env."""
    out: list[str] = []
    begin_re = re.compile(rf"\\begin\{{{re.escape(env)}\}}")
    pos = 0
    while True:
        m = begin_re.search(text, pos)
        if not m:
            out.append(text[pos:])
            break
        out.append(text[pos:m.start()])
        end = _find_matching_end(text, env, m.end())
        if end is None:
            out.append(text[m.start():])
            break
        pos = end[1]
    return "".join(out)



def unwrap_outer_env(tex: str) -> TexBlock:
    """Strip `\\begin{defmark|claimmark}…\\end{...}` wrappers, then peel off the
    outer theorem-like env (`Def`, `Lem`, …). Returns the inner body, the env
    name, and the title from `[…]` if present."""
    for w in WRAPPER_ENVS:
        tex = re.sub(rf"\\begin\{{{w}\}}\s*", "", tex)
        tex = re.sub(rf"\\end\{{{w}\}}\s*", "", tex)
    tex = tex.strip()
    for env in THEOREM_ENVS:
        m = re.match(
            rf"\\begin\{{{env}\}}(?:\[(.*?)\])?\s*(.*?)\s*\\end\{{{env}\}}\s*$",
            tex,
            re.DOTALL,
        )
        if m:
            return TexBlock(body_html=m.group(2), env=env, title=m.group(1))
    return TexBlock(body_html=tex, env=None, title=None)


def _convert_enumerate(body: str, klass: str, resume_from: int = 0) -> tuple[str, int]:
    """Convert `\\item …` chunks inside an enumerate body into <li> tags.
    Returns (html, item_count). `\\item[]` becomes a class="no-marker" li.
    `\\item[label]` (non-empty) is rendered with the label as a manual prefix
    in front of the body — we use this only for the `\\item[]` resume-skip
    pattern in practice."""
    # Process any nested enumerate/itemize/proof envs FIRST. Otherwise the
    # split-on-`\item` below would tear an inner enumerate apart along its
    # own `\item`s, attributing the inner items to the outer list.
    body = _convert_block_envs(body)
    parts = re.split(r"(?=\\item\b)", body)
    parts = [p for p in parts if p.strip()]
    lis: list[str] = []
    count = 0
    for p in parts:
        m = re.match(r"\\item\s*(?:\[(.*?)\])?\s*(.*)", p, re.DOTALL)
        if not m:
            continue
        label, content = m.group(1), m.group(2).strip()
        content = inline_convert(content)
        if label is not None and label == "":
            lis.append(f'<li class="no-marker">{content}</li>')
        elif label:
            lis.append(f'<li class="no-marker"><span class="manual-label">{label}</span> {content}</li>')
        else:
            count += 1
            lis.append(f"<li>{content}</li>")
    if resume_from:
        # `start` is for fallback (default <ol>); the inline style drives our
        # custom `::before` counter regardless of the resume offset.
        attrs = (
            f' start="{resume_from + 1}"'
            f' style="counter-reset: roman-counter {resume_from}"'
        )
    else:
        attrs = ""
    return f'<ol class="{klass}"{attrs}>{"".join(lis)}</ol>', count


def _convert_itemize(body: str) -> str:
    parts = re.split(r"(?=\\item\b)", body)
    parts = [p for p in parts if p.strip()]
    lis = []
    for p in parts:
        m = re.match(r"\\item\s*(.*)", p, re.DOTALL)
        if m:
            lis.append(f"<li>{inline_convert(m.group(1).strip())}</li>")
    return f'<ul>{"".join(lis)}</ul>'


def inline_convert(tex: str) -> str:
    """Apply inline replacements (emphasis, dashes, spaces, refrow).
    Math segments (`$…$`, `\\(…\\)`) are protected so the replacements don't
    touch their interior."""
    # Protect math.
    placeholders: list[str] = []
    def stash(m: re.Match) -> str:
        placeholders.append(m.group(0))
        return f"\x00MATH{len(placeholders) - 1}\x00"
    # Order matters: display first, then inline; `$$…$$` before `$…$`.
    protected = tex
    protected = re.sub(r"\$\$(.+?)\$\$", stash, protected, flags=re.DOTALL)
    protected = re.sub(r"\\\[(.+?)\\\]", stash, protected, flags=re.DOTALL)
    protected = re.sub(r"\\\((.+?)\\\)", stash, protected, flags=re.DOTALL)
    protected = re.sub(r"\$(.+?)\$", stash, protected, flags=re.DOTALL)

    # Now safe to apply prose replacements.
    protected = re.sub(r"\\emph\{([^{}]*)\}",   r"<em>\1</em>", protected)
    protected = re.sub(r"\\textit\{([^{}]*)\}", r"<em>\1</em>", protected)
    protected = re.sub(r"\\textbf\{([^{}]*)\}", r"<strong>\1</strong>", protected)
    # `\texttt{X}` → inline <code>; the inner text often has escaped
    # underscores `\_` which read better as literal `_` in monospace.
    protected = re.sub(
        r"\\texttt\{([^{}]*)\}",
        lambda m: f"<code>{m.group(1).replace(chr(92)+'_', '_')}</code>",
        protected,
    )
    # `\paragraph{X}` / `\subparagraph{X}` are LaTeX's inline-heading
    # commands (rendered bold-lead-in-on-its-own-line). Render as a
    # bold run on a new line.
    protected = re.sub(
        r"\\paragraph\{([^{}]*)\}",
        r'<br><strong class="tex-paragraph">\1</strong> ',
        protected,
    )
    protected = re.sub(
        r"\\subparagraph\{([^{}]*)\}",
        r'<br><strong class="tex-subparagraph">\1</strong> ',
        protected,
    )
    # `\footnote{X}` — drop. Footnotes work poorly on the web layout
    # and the proof body is the primary content.
    protected = re.sub(r"\\footnote\{[^{}]*\}", "", protected)
    # `\Claude{…}` — blue annotation macro from the LN preamble, used in
    # some proof files. Render as a styled inline note.
    protected = re.sub(
        r"\\Claude\{([^{}]*)\}",
        r'<span class="claude-note">Claude: \1</span>',
        protected,
    )
    def _refrow_sub(m: re.Match) -> str:
        ref = m.group(1).replace("\\_", "_")
        return f'<a href="#{ref}" class="refrow"><code>{ref}</code></a>'
    protected = re.sub(r"\\refrow\{([^{}]*)\}", _refrow_sub, protected)

    # `\ref{X}` — LaTeX cross-reference to a `\label{X}` defined elsewhere.
    # Resolve the label to its owning row's ref via the lazy index below;
    # link if found, otherwise show the bare label as styled inline code so
    # the user at least sees what was being referenced.
    def _ref_sub(m: re.Match) -> str:
        label = m.group(1).replace("\\_", "_")
        target_ref = _label_index().get(label)
        if target_ref:
            return f'<a href="#{target_ref}" class="refrow"><code>{label}</code></a>'
        return f"<code>{label}</code>"
    protected = re.sub(r"\\ref\{([^{}]*)\}", _ref_sub, protected)
    # Prose-level spacing / layout commands carry no meaning on the web —
    # drop them so they don't render as literal backslash text.
    protected = re.sub(
        r"\\(noindent|medskip|smallskip|bigskip|par|newpage|clearpage|centering|raggedright|raggedleft|null)\b",
        "", protected,
    )
    # LaTeX typographic quotes: `` … '' → “ … ”, ` … ' → ‘ … ’.
    # Only the doubled forms are converted unambiguously; the single
    # backtick / quote forms get used too often inside identifiers
    # (e.g. `J`, `V`) to safely convert globally.
    protected = protected.replace("``", "“").replace("''", "”")
    protected = protected.replace("---", "—")
    protected = protected.replace("--", "–")
    protected = protected.replace("~", "&nbsp;")
    protected = protected.replace("\\\\", "<br>")

    # Restore math.
    def restore(m: re.Match) -> str:
        return placeholders[int(m.group(1))]
    return re.sub(r"\x00MATH(\d+)\x00", restore, protected)


def _convert_math_envs(tex: str) -> str:
    """Convert LaTeX math environments to a KaTeX-compatible form by
    wrapping them in `\\[ … \\]` display-math delimiters. The body env
    is rewritten to KaTeX's `aligned` / `gathered` variants where
    needed (`align*` / `equation*` etc. are TeX-only)."""
    def repl(m: re.Match) -> str:
        env = m.group(1)
        body = m.group(2)
        if env in ("align", "align*"):
            return f"\\[\\begin{{aligned}}{body}\\end{{aligned}}\\]"
        if env in ("gather", "gather*", "eqnarray", "eqnarray*"):
            return f"\\[\\begin{{gathered}}{body}\\end{{gathered}}\\]"
        # equation / equation*  → plain display math
        return f"\\[{body}\\]"
    return re.sub(
        r"\\begin\{(align\*?|equation\*?|eqnarray\*?|gather\*?)\}(.*?)\\end\{\1\}",
        repl, tex, flags=re.DOTALL,
    )


def _convert_description(body: str) -> str:
    """`\\begin{description}\\item[term] body \\item[term] body\\end{description}`
    → an HTML <dl> list."""
    parts = re.split(r"(?=\\item\b)", body)
    parts = [p for p in parts if p.strip()]
    out: list[str] = []
    for p in parts:
        m = re.match(r"\\item\s*\[(.*?)\]\s*(.*)", p, re.DOTALL)
        if not m:
            continue
        out.append(
            f"<dt>{inline_convert(m.group(1))}</dt>"
            f"<dd>{inline_convert(m.group(2).strip())}</dd>"
        )
    return f"<dl>{''.join(out)}</dl>"


def _convert_block_envs(tex: str) -> str:
    """Convert enumerate/itemize/proof environments to HTML, with proper
    depth-aware matching so nested `\\begin{enumerate}…\\end{enumerate}`
    inside an outer enumerate (e.g. claim_3_24) doesn't get severed at
    the first inner `\\end`. enumerate's `resume` option carries the
    counter across consecutive lists. Each block-level conversion is
    surrounded by blank lines so the paragraph-wrapper treats it as a
    standalone block."""
    out: list[str] = []
    pos = 0
    resume_count = 0

    begin_re = re.compile(r"\\begin\{(enumerate|itemize|proof|quote|description|verbatim)\}(\[[^\]]*\])?")
    while True:
        m = begin_re.search(tex, pos)
        if not m:
            out.append(tex[pos:])
            break
        out.append(tex[pos:m.start()])
        env  = m.group(1)
        opts = (m.group(2) or "")[1:-1]
        body_start = m.end()
        end = _find_matching_end(tex, env, body_start)
        if end is None:
            # No matching end — leave the begin literal and move on.
            out.append(tex[m.start():m.end()])
            pos = m.end()
            continue
        body = tex[body_start:end[0]]
        if env == "enumerate":
            roman = "label=\\roman*.)" in opts
            resume = "resume" in opts
            klass = "roman-paren" if roman else "enum"
            html, count = _convert_enumerate(
                body, klass, resume_from=resume_count if resume else 0
            )
            resume_count = (resume_count if resume else 0) + count
            out.append(f"\n\n{html}\n\n")
        elif env == "itemize":
            out.append(f"\n\n{_convert_itemize(body)}\n\n")
            resume_count = 0
        elif env == "proof":
            inner = tex_body_to_html(body)
            out.append(
                f'\n\n<div class="tex-proof"><span class="proof-label">Proof.</span>{inner}</div>\n\n'
            )
            resume_count = 0
        elif env == "quote":
            inner = tex_body_to_html(body)
            out.append(f"\n\n<blockquote>{inner}</blockquote>\n\n")
            resume_count = 0
        elif env == "description":
            out.append(f"\n\n{_convert_description(body)}\n\n")
            resume_count = 0
        elif env == "verbatim":
            # Verbatim content is shown as-is in a <pre>; the body might
            # contain `<` or `&` that must be escaped first.
            esc = body.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            out.append(f"\n\n<pre class=\"verbatim\">{esc}</pre>\n\n")
            resume_count = 0
        pos = end[1]
    return "".join(out)


def _paragraphs(html: str) -> str:
    """Wrap top-level prose runs in <p>. Block-level constructs (ol, ul, div)
    are kept on their own. Blank lines split paragraphs."""
    # Split on blank lines; for each chunk decide whether it's already block
    # HTML or prose to wrap.
    chunks = re.split(r"\n\s*\n", html.strip())
    out: list[str] = []
    BLOCK_RE = re.compile(r"^\s*<(ol|ul|div|h\d|pre|table)\b")
    for c in chunks:
        c = c.strip()
        if not c:
            continue
        if BLOCK_RE.match(c):
            out.append(c)
        else:
            out.append(f"<p>{c}</p>")
    return "\n".join(out)


ENV_LABELS = {
    "Def": "Definition", "DefThm": "Definition / Theorem",
    "DefLem": "Definition / Lemma", "NotLem": "Notation / Lemma",
    "Lem": "Lemma", "Prp": "Proposition", "Cor": "Corollary",
    "Thm": "Theorem", "Con": "Conjecture", "Fct": "Fact",
    "Prn": "Principle", "Not": "Notation", "Rem": "Remark",
    "Note": "Note", "Cau": "Caution", "Eg": "Example",
    "Tho": "Thoughts", "Exc": "Exercise", "Ques": "Question",
    "Expl": "Explanation", "Disc": "Discussion", "Axm": "Axiom",
    "Alg": "Algorithm", "Construction": "Construction",
    "Conclusion": "Conclusion", "Motivation": "Motivation",
    "sa": "Theorem",
}


def _convert_theorem_envs(tex: str) -> str:
    """Convert any intermediate `\\begin{Def|Lem|Rem|…}[Title]…\\end{…}` env
    in the body into a styled `<div class="theorem-block">` block. Unlike
    `unwrap_outer_env`, this keeps the env framing (with a labelled
    header) so multiple envs on one page (e.g., a proof file that
    restates the statement before `\\begin{proof}`) render correctly."""
    pattern = re.compile(
        rf"\\begin\{{({'|'.join(THEOREM_ENVS)})\}}(?:\[(.*?)\])?\s*(.*?)\s*\\end\{{\1\}}",
        re.DOTALL,
    )
    def repl(m: re.Match) -> str:
        env = m.group(1)
        title = (m.group(2) or "").strip()
        body = m.group(3)
        body_html = tex_body_to_html(body)
        label = ENV_LABELS.get(env, env)
        title_html = f" — <span class=\"theorem-title\">{title}</span>" if title else ""
        return (
            f'\n\n<div class="theorem-block">'
            f'<div class="theorem-label">{label}{title_html}</div>'
            f'{body_html}</div>\n\n'
        )
    return pattern.sub(repl, tex)


def tex_body_to_html(tex_body: str) -> str:
    """Public: convert a TeX body (no subfiles/wrapper) to HTML prose with math
    delimiters intact for KaTeX."""
    # Wrap math envs (`align*`/`equation*`/…) in `\[ … \]` first so the
    # rest of the pipeline treats them like any other display math
    # rather than as prose text containing literal `\begin{align*}`.
    s = _convert_math_envs(tex_body)
    s = _convert_theorem_envs(s)
    s = _convert_block_envs(s)
    s = inline_convert(s)
    s = _paragraphs(s)
    return s


def tex_to_html(tex: str) -> TexBlock:
    """End-to-end statement renderer: subfiles wrapper → outer env →
    HTML body. Strips any `\\begin{proof}…\\end{proof}` block from the
    body — some statement files (e.g. claim_3_27_statement) embed a
    proof against their own header comment; that content belongs on the
    dedicated proof page, not the entry page."""
    s = strip_subfiles_wrapper(tex)
    block = unwrap_outer_env(s)
    block.body_html = tex_body_to_html(_strip_proof_blocks(block.body_html))
    return block
