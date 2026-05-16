"""Report .tex files that main.tex does not use.

A file counts as "used" if it is reachable from main.tex by following
\\input / \\include directives (commented-out ones are ignored). Every other
.tex file directly in the lecture notes directory is a candidate for deletion.
Subfolders (graphics/, claude/) are skipped: they hold figure sources and
analysis output, not lecture-note drafts.

Run:  python scaffold/find_unused_tex.py
"""
import re
from pathlib import Path

LECTURE_NOTES_DIR = (
    Path(__file__).resolve().parent.parent / "lecture-notes" / "lecture_notes"
)
MAIN_TEX = LECTURE_NOTES_DIR / "main.tex"

# \input{file} or \include{file} (also the brace-less \input file form).
# The (?![a-zA-Z]) guard stops \includegraphics / \inputencoding from matching.
_INPUT_RE = re.compile(
    r"\\(?:input|include)(?![a-zA-Z])\s*(?:\{([^}]+)\}|([^\s{}\\]+))"
)


def _strip_comments(text):
    """Drop LaTeX comments: everything after an unescaped '%' on each line."""
    return "\n".join(re.sub(r"(?<!\\)%.*", "", ln) for ln in text.splitlines())


def _inputs_of(tex_path):
    """Resolved paths of every file \\input/\\include'd by `tex_path`."""
    text = _strip_comments(tex_path.read_text(encoding="latin-1"))
    paths = []
    for braced, bare in _INPUT_RE.findall(text):
        name = (braced or bare).strip()
        if not name.endswith(".tex"):
            name += ".tex"
        paths.append((LECTURE_NOTES_DIR / name).resolve())
    return paths


def used_tex_files():
    """All .tex files reachable from main.tex, following \\input recursively."""
    used, stack = set(), [MAIN_TEX.resolve()]
    while stack:
        path = stack.pop()
        if path in used or not path.exists():
            continue
        used.add(path)
        stack.extend(_inputs_of(path))
    return used


def main():
    used = used_tex_files()
    all_tex = {p.resolve() for p in LECTURE_NOTES_DIR.glob("*.tex")}
    unused = sorted(all_tex - used)

    print(f"Used by main.tex : {len(used)} file(s)")
    print(f"Not used         : {len(unused)} file(s)\n")
    for path in unused:
        print(f"  {path.relative_to(LECTURE_NOTES_DIR)}")


if __name__ == "__main__":
    main()
