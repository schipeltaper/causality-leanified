#!/usr/bin/env python3
"""check_render.py — flag unrendered LaTeX commands in panel HTML.

Scans every panel JSON's rendered HTML (`tex_block_html`,
`tex_statement.html`, `tex_proof.html`) for `\\foo` tokens that would
either:

  1. **Show as raw text** on the website — `\\foo` appearing OUTSIDE
     math delimiters (`$…$`, `\\(…\\)`, `\\[…\\]`, `$$…$$`).  These are
     prose-mode commands `tex_to_html.py` didn't handle.

  2. **Trigger a KaTeX ParseError** — `\\foo` inside math delimiters
     that's not registered in `KATEX_MACROS` (in `app.js`) and isn't a
     KaTeX builtin.  These render as a red error box on the page with
     the source token visible.

For each finding, reports the panel ref, the field, the macro name,
and a few words of surrounding context.  Exits non-zero when any
issue is found so the per-row workflow stops before pushing a broken
render.

Recipe for clearing a finding:

  * Math-mode: add the macro to `KATEX_MACROS` in
    `building_website/website/assets/app.js`, mapping it to whatever
    KaTeX-compatible expansion you want (usually `\\mathrm{Name}` or
    `\\operatorname{name}`).
  * Prose-mode: add a substitution to `tex_to_html.py`'s
    `inline_convert` (e.g. `\\checkmark` → `✓`), or extend the
    "drop these" regex if the command should be elided.
  * False positive (the command is a KaTeX builtin this script
    doesn't know about): add it to `KATEX_BUILTINS` below.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DATA_DIR = REPO_ROOT / "building_website" / "website" / "data"
APP_JS_PATH = REPO_ROOT / "building_website" / "website" / "assets" / "app.js"

# Math delimiters (display-mode first so `$$` matches before `$`).
MATH_RE = re.compile(
    r"\$\$.*?\$\$|\\\[.*?\\\]|\\\(.*?\\\)|\$.*?\$",
    re.DOTALL,
)

# Backslash + letters (won't match `\,`, `\;`, `\!`, `\\`, etc.).
CMD_RE = re.compile(r"\\([A-Za-z]+)")

# KATEX_MACROS extraction from app.js: `"\\foo": …`.
KATEX_MACRO_RE = re.compile(r'"\\\\([A-Za-z]+)"\s*:')

# Generous allowlist of KaTeX builtins we expect to see in math segments.
# Extend as new commands appear that this script flags as false positives.
KATEX_BUILTINS: set[str] = set("""
    left right middle bigl bigr Bigl Bigr biggl biggr Biggl Biggr
    text mathrm mathbf mathit mathsf mathtt mathcal mathbb mathfrak
    textrm textbf textit textsf texttt textnormal
    boldsymbol operatorname displaystyle textstyle scriptstyle scriptscriptstyle
    overline underline overbrace underbrace overrightarrow overleftarrow
    widetilde widehat hat tilde bar vec dot ddot acute grave breve check mathring
    sum prod int oint iint iiint coprod bigcap bigcup bigvee bigwedge
    bigsqcup biguplus bigotimes bigoplus bigodot
    frac dfrac tfrac binom dbinom tbinom genfrac
    sqrt root
    cdot cdots ldots vdots ddots dots dotsc dotsb dotsm dotsi dotso
    pm mp times div ast star circ bullet oplus ominus otimes oslash odot
    cap cup setminus emptyset varnothing sqcup sqcap uplus
    subset subseteq supset supseteq subsetneq supsetneq subsetneqq supsetneqq
    sqsubset sqsubseteq sqsupset sqsupseteq
    in notin ni nni mid parallel perp angle measuredangle triangle triangleq
    forall exists nexists neg lnot vee wedge land lor implies iff
    Rightarrow Leftarrow Leftrightarrow rightarrow leftarrow leftrightarrow
    longrightarrow longleftarrow longleftrightarrow
    Longrightarrow Longleftarrow Longleftrightarrow
    twoheadrightarrow twoheadleftarrow rightarrowtail leftarrowtail
    to gets mapsto Mapsto longmapsto hookrightarrow hookleftarrow
    rightharpoonup leftharpoonup rightharpoondown leftharpoondown
    rightleftarrows leftrightarrows rightleftharpoons leftrightharpoons
    leadsto rightsquigarrow leftsquigarrow
    le ge leq geq ll gg lll ggg prec preceq succ succeq precsim succsim
    ne neq equiv simeq cong approx sim propto
    lvert rvert lVert rVert lvert rvert
    xrightarrow xleftarrow xRightarrow xLeftarrow xleftrightarrow xLeftrightarrow
    xmapsto xhookleftarrow xhookrightarrow
    bigm Bigm biggm Biggm bigl Bigl biggl Biggl bigr Bigr biggr Biggr
    aleph beth gimel hbar ell wp Re Im infty partial nabla
    quad qquad hspace hskip mspace thinspace negthinspace medspace negmedspace thickspace negthickspace
    big Big bigg Bigg
    overset underset stackrel
    label ref eqref tag
    begin end
    color textcolor colorbox fcolorbox
    rule kern
    phantom hphantom vphantom mathstrut strut
    not negthinspace
    sf rm bf it tt
    le ge ne
    alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa
    lambda mu nu xi omicron pi varpi rho varrho sigma varsigma tau upsilon
    phi varphi chi psi omega
    Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega
    prime degree celsius circ
    cdotp colon
""".split())

# Prose-mode commands that `tex_to_html.py` handles or deliberately drops.
PROSE_HANDLED: set[str] = set("""
    emph textit textbf texttt paragraph subparagraph footnote
    ref refrow eqref label phantomsection
    noindent medskip smallskip bigskip par newpage clearpage
    centering raggedright raggedleft null
    begin end documentclass document subfile
    item items rowref def Claude
    checkmark
    quad qquad
""".split())


def known_katex_macros() -> set[str]:
    text = APP_JS_PATH.read_text()
    macros = set(KATEX_MACRO_RE.findall(text))
    for letter_code in range(ord("A"), ord("Z") + 1):
        c = chr(letter_code)
        macros.add(f"{c}cal")
        macros.add(f"{c}bf")
    return macros


def scan_html(html: str, allowed_math: set[str]) -> list[tuple[str, str, str]]:
    """Return [(context, macro_name, snippet)] for each suspicious token.

    `context` is "MATH" or "PROSE"; `snippet` is ~30 chars on either
    side of the find, newlines collapsed."""
    findings: list[tuple[str, str, str]] = []
    last_end = 0
    for m in MATH_RE.finditer(html):
        prose_seg = html[last_end:m.start()]
        for c in CMD_RE.finditer(prose_seg):
            name = c.group(1)
            if name in PROSE_HANDLED:
                continue
            ctx = prose_seg[max(0, c.start() - 30):c.end() + 30]
            findings.append(("PROSE", name, " ".join(ctx.split())))
        math_body = m.group(0)
        for c in CMD_RE.finditer(math_body):
            name = c.group(1)
            if name in allowed_math:
                continue
            ctx = math_body[max(0, c.start() - 30):c.end() + 30]
            findings.append(("MATH", name, " ".join(ctx.split())))
        last_end = m.end()
    if last_end < len(html):
        prose_seg = html[last_end:]
        for c in CMD_RE.finditer(prose_seg):
            name = c.group(1)
            if name in PROSE_HANDLED:
                continue
            ctx = prose_seg[max(0, c.start() - 30):c.end() + 30]
            findings.append(("PROSE", name, " ".join(ctx.split())))
    return findings


def fields_to_scan(panel: dict) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    if panel.get("tex_block_html"):
        out.append(("tex_block_html", panel["tex_block_html"]))
    for sec in ("tex_statement", "tex_proof"):
        obj = panel.get(sec)
        if obj and obj.get("html"):
            out.append((f"{sec}.html", obj["html"]))
    return out


def main() -> None:
    allowed_math = known_katex_macros() | KATEX_BUILTINS
    total_findings = 0
    for path in sorted(DATA_DIR.glob("*.json")):
        if path.stem == "manifest":
            continue
        panel = json.loads(path.read_text())
        per_panel: list[str] = []
        for field_name, html in fields_to_scan(panel):
            findings = scan_html(html, allowed_math)
            if findings:
                per_panel.append(f"  {field_name}:")
                for ctx, name, snip in findings:
                    per_panel.append(f"    {ctx} \\{name}  «{snip}»")
                total_findings += len(findings)
        if per_panel:
            print(f"\n{path.stem}:")
            print("\n".join(per_panel))
    if total_findings:
        print(
            f"\n{total_findings} unrendered command(s) found across panels — "
            "see recipe in the docstring at the top of this script for the fix.",
            file=sys.stderr,
        )
        sys.exit(1)
    print("All panels render-clean.")


if __name__ == "__main__":
    main()
