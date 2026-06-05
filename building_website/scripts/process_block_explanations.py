#!/usr/bin/env python3
"""Per-block explanations + line-by-line annotated code.

For a given row, walks every `lean_blocks[i]` and, in a single LLM
call per block, produces:

  - `explanation`    — a polished Markdown article that explains the
                       logic of THIS block as you'd say it to a human:
                       what is going on, how it maps to the LN, what
                       non-obvious naming / Mathlib idioms appear.
  - `code_annotated` — the same Lean code with a `-- …` comment line
                       inserted above each non-trivial line. Comments
                       explain the naming of identifiers introduced,
                       the Lean / Mathlib functions used, and the
                       logic of the line.

The two outputs share generation cost: one LLM call per block returns
both as a JSON object. Idempotent — re-runs skip blocks that already
carry both fields unless `--force` is given.

Usage:
    python3 building_website/scripts/process_block_explanations.py def_3_1
    python3 building_website/scripts/process_block_explanations.py def_3_1 --force
    python3 building_website/scripts/process_block_explanations.py --all
    python3 building_website/scripts/process_block_explanations.py --all --force

Requires `pip install anthropic` and `ANTHROPIC_API_KEY` in the env.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from fetch_row import REPO_ROOT, WEBSITE_DATA, REF_RE, find_row  # noqa: E402
from process_design_choices import _gather_preceding_comments    # noqa: E402

MODEL      = "claude-opus-4-7"
MAX_TOKENS = 4096

PROMPT = """\
You're producing two outputs for one Lean 4 declaration in a formalisation
of the Forré–Mooij Causality lecture notes.

## Row context

  ref:     {ref}
  kind:    {row_kind}     (definition or claim)
  section: {section}
  title:   {title}

## The lecture-notes statement (verbatim — for context, DO NOT restate)

```latex
{tex_block}
```

## Pre-statement comments the formalize worker wrote

(design rationale, naming notes, prior-formalisation pointers — may be empty)

```
{comments}
```

## All Lean blocks in this row

You're shown every block (helpers first, then mains) so you can see how the
focus block relates to the rest. The block you must explain is marked
**★ FOCUS** below; the others are CONTEXT only — do not produce output for
them.

{all_blocks_listing}

## Your two tasks for the FOCUS block

### 1. `explanation`

A polished Markdown article (flowing paragraphs, no headings) that explains
the **logic of this block** to a human reader — what is the block actually
doing, and what does it correspond to in the LN? Cover:

- what concept this declaration captures (one paragraph);
- non-obvious naming choices in this block's identifiers;
- any Mathlib / Lean idioms the reader might not recognise
  (one short sentence each);
- if the block is one piece of a multi-block row (e.g. a helper or one
  theorem of a multi-part claim), say where this piece sits in the whole.

Audience: a reader who knows Lean 4 basics but is not a Mathlib expert.
DO NOT restate the LN statement; DO NOT restate the Lean signature
verbatim. Inline code refs in `` `backticks` ``; math in `$…$`. ~80–200
words.

### 2. `code_annotated`

The SAME Lean source as the focus block, with a `--` comment line inserted
ABOVE each non-trivial line. Each comment explains one or more of:

- the **naming** of identifiers introduced on that line (what they stand
  for, why this name was chosen);
- the **Lean / Mathlib functions** used on that line (one short phrase per
  unfamiliar function);
- the **logic** the line carries out (what it is computing / asserting /
  matching).

Lines that need no commentary (blank lines, bare `where`, plain `|` in a
match) can be left without a comment above. The annotated version must
still be valid Lean — the only changes are the inserted `-- comment`
lines. Preserve the indentation and structure of the original code
exactly.

Important:
- keep the *original* lines unchanged — do not paraphrase them;
- inserted comments are short (one line each, ~10–15 words);
- the inserted comments must NOT use `/- … -/` block-comment syntax
  (that's harder to read on the rendered page) — only `--` line comments;
- comments inside the body of inductive constructors or pattern matches
  may be indented to match the line they describe.

## Output

STRICTLY a single JSON object on one line, no other text:

{{"explanation": "…", "code_annotated": "…"}}
"""


def _all_blocks_listing(blocks: list[dict], focus_idx: int) -> str:
    chunks: list[str] = []
    for i, b in enumerate(blocks):
        marker = "★ FOCUS" if i == focus_idx else "context"
        chunks.append(
            f"### block {i+1} ({b['kind']}) — {marker}\n```lean\n{b['code']}\n```"
        )
    return "\n\n".join(chunks)


def call_claude(
    *, ref: str, row_kind: str, section: str, title: str,
    tex_block: str, comments: str, all_blocks_listing: str,
) -> dict[str, str]:
    try:
        import anthropic  # type: ignore
    except ImportError:
        sys.exit("error: pip install anthropic")
    client = anthropic.Anthropic()
    prompt = PROMPT.format(
        ref=ref, row_kind=row_kind, section=section, title=title,
        tex_block=tex_block, comments=comments,
        all_blocks_listing=all_blocks_listing,
    )
    msg = client.messages.create(
        model=MODEL,
        max_tokens=MAX_TOKENS,
        messages=[{"role": "user", "content": prompt}],
    )
    text = "".join(b.text for b in msg.content if getattr(b, "type", None) == "text").strip()
    m = re.search(r"\{.*\}", text, re.DOTALL)
    if not m:
        sys.exit(f"error: model did not return JSON:\n{text}")
    try:
        obj = json.loads(m.group(0))
    except json.JSONDecodeError as e:
        sys.exit(f"error: malformed JSON from model: {e}\n{text}")
    if "explanation" not in obj or "code_annotated" not in obj:
        sys.exit(f"error: missing keys in model response: {list(obj)}")
    return obj


def process_one(ref: str, force: bool) -> bool:
    path = WEBSITE_DATA / f"{ref}.json"
    if not path.exists():
        print(f"[{ref}] error: {path} missing — run fetch_row.py first", file=sys.stderr)
        return False
    data = json.loads(path.read_text(encoding="utf-8"))
    row, _ = find_row(ref)
    main_lean_text = (REPO_ROOT / row["main_lean_file"]).read_text(encoding="utf-8")
    comments = _gather_preceding_comments(main_lean_text, ref)
    tex_block = (row.get("tex_block") or "").strip()
    blocks: list[dict] = data.get("lean_blocks") or []

    any_changed = False
    for i, blk in enumerate(blocks):
        if blk.get("explanation") and blk.get("code_annotated") and not force:
            continue
        listing = _all_blocks_listing(blocks, i)
        print(f"[{ref}] block {i+1}/{len(blocks)} ({blk['kind']}) — calling {MODEL}…")
        out = call_claude(
            ref=ref, row_kind=row["def_or_claim"], section=row.get("section", ""),
            title=row.get("title", ""), tex_block=tex_block, comments=comments,
            all_blocks_listing=listing,
        )
        blk["explanation"]    = out["explanation"]
        blk["code_annotated"] = out["code_annotated"]
        any_changed = True

    if any_changed:
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"[{ref}] wrote {path.relative_to(REPO_ROOT)}", file=sys.stderr)
    else:
        print(f"[{ref}] all blocks already populated (use --force to regenerate)")
    return True


def all_refs() -> list[str]:
    return sorted(
        p.stem for p in WEBSITE_DATA.glob("*.json")
        if p.stem != "manifest" and REF_RE.match(p.stem)
    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("ref", nargs="?")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()

    refs = all_refs() if args.all else ([args.ref] if args.ref else [])
    if not refs:
        ap.error("provide a ref or use --all")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        sys.exit("error: set ANTHROPIC_API_KEY")
    ok = True
    for r in refs:
        ok = process_one(r, args.force) and ok
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
