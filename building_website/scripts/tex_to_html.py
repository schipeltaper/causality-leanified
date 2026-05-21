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
    bookkeeping directives, and remove whole-line `%` comments."""
    m = re.search(r"\\begin\{document\}(.*?)\\end\{document\}", tex, re.DOTALL)
    if m:
        tex = m.group(1)
    tex = re.sub(r"\\def\\row(ref|title)\{[^}]*\}", "", tex)
    tex = re.sub(r"\\phantomsection", "", tex)
    tex = re.sub(r"\\label\{[^}]*\}", "", tex)
    tex = re.sub(r"^\s*%.*$", "", tex, flags=re.MULTILINE)
    return tex


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
    def _refrow_sub(m: re.Match) -> str:
        ref = m.group(1).replace("\\_", "_")
        return f'<a href="#{ref}" class="refrow"><code>{ref}</code></a>'
    protected = re.sub(r"\\refrow\{([^{}]*)\}", _refrow_sub, protected)
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


def _convert_block_envs(tex: str) -> str:
    """Convert enumerate/itemize/proof environments to HTML, in order, with
    enumerate's `resume` option carrying the counter across consecutive lists.
    Each block-level conversion is surrounded by blank lines so the later
    paragraph-wrapper treats it as a standalone block."""
    out_parts: list[str] = []
    pos = 0
    resume_count = 0

    pattern = re.compile(
        r"\\begin\{(enumerate|itemize|proof)\}(\[[^\]]*\])?(.*?)\\end\{\1\}",
        re.DOTALL,
    )
    for m in pattern.finditer(tex):
        out_parts.append(tex[pos:m.start()])
        env, opts, body = m.group(1), (m.group(2) or "")[1:-1], m.group(3)
        if env == "enumerate":
            roman = "label=\\roman*.)" in opts
            resume = "resume" in opts
            klass = "roman-paren" if roman else "enum"
            html, count = _convert_enumerate(
                body, klass, resume_from=resume_count if resume else 0
            )
            resume_count = (resume_count if resume else 0) + count
            out_parts.append(f"\n\n{html}\n\n")
        elif env == "itemize":
            out_parts.append(f"\n\n{_convert_itemize(body)}\n\n")
            resume_count = 0
        elif env == "proof":
            inner = tex_body_to_html(body)
            out_parts.append(
                f'\n\n<div class="tex-proof"><span class="proof-label">Proof.</span>{inner}</div>\n\n'
            )
            resume_count = 0
        pos = m.end()
    out_parts.append(tex[pos:])
    return "".join(out_parts)


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


def tex_body_to_html(tex_body: str) -> str:
    """Public: convert a TeX body (no subfiles/wrapper) to HTML prose with math
    delimiters intact for KaTeX."""
    s = _convert_block_envs(tex_body)
    s = inline_convert(s)
    s = _paragraphs(s)
    return s


def tex_to_html(tex: str) -> TexBlock:
    """End-to-end: subfiles wrapper → outer env → HTML body."""
    s = strip_subfiles_wrapper(tex)
    block = unwrap_outer_env(s)
    block.body_html = tex_body_to_html(block.body_html)
    return block
