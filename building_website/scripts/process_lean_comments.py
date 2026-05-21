#!/usr/bin/env python3
"""Split a row's Lean comments into `lean_explanation` + `design_choices`.

The Lean files in this project carry rich `--` / `/- … -/` / `/-- … -/`
comments around every declaration — usually a mix of (a) what the code
does and how it uses Mathlib, (b) why the formalisation was structured
this way, and (c) verbatim LaTeX excerpts. The website renders (c)
already (as the TeX statement), so the comments are noise as a single
blob; this script asks Claude to disentangle (a) from (b) and produces
two short markdown panels.

The script reads `building_website/website/data/<ref>.json`, sends the
concatenated `lean[*].comments` to Claude with a strict JSON-output
prompt, and writes the resulting `lean_explanation` and `design_choices`
fields back into the same JSON file. Idempotent: a `--force` flag
re-processes rows that already have prose, otherwise skips them.

Usage:

    python3 building_website/scripts/process_lean_comments.py def_3_1
    python3 building_website/scripts/process_lean_comments.py def_3_1 --force
    python3 building_website/scripts/process_lean_comments.py --all
    python3 building_website/scripts/process_lean_comments.py --all --force

Requires `pip install anthropic` and `ANTHROPIC_API_KEY` in the env.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

REPO_ROOT     = Path(__file__).resolve().parents[2]
WEBSITE_DATA  = REPO_ROOT / "building_website" / "website" / "data"
MODEL         = "claude-opus-4-7"   # the most capable model as of writing
MAX_TOKENS    = 2048

PROMPT = """\
You are processing the comments that surround a Lean 4 declaration in a
formalisation of the Forré–Mooij Causality lecture notes.

## The lecture-notes statement (LaTeX, for your context only — DO NOT restate)

```latex
{tex_statement}
```

## The Lean code (declaration, comments stripped)

```lean
{statement}
```

## The Lean comments that surround the declaration (verbatim — `--` /
## `/- … -/` / `/-- … -/`; may include a verbatim LaTeX excerpt)

```
{comments}
```

## Your task

Produce TWO concise markdown texts. Audience: a reader who already
understands the basics of Lean 4.

### 1. `lean_explanation`

A focused explanation of THIS specific Lean code, covering only the
three things below. Skip a bullet if it isn't relevant. Be concise —
this is not a tutorial.

- **Complex Mathlib things used.** Any non-obvious Mathlib type,
  lemma, or notation in this declaration (e.g. `Disjoint`, `×ˢ`,
  `IsPartialOrder`, `Set.disjoint_left`, `Quotient`, instance-implicit
  args `⦃⦄`, universe-polymorphic `Type*`). One sentence each.

- **Structural divergence from the LaTeX.** If the Lean does NOT
  directly mirror the LaTeX (different decomposition, alternative
  representation, helper lemmas pulled out, multi-part claim split,
  …), say so and explain briefly. If it mirrors the LaTeX faithfully,
  skip this.

- **Naming.** Why specific identifiers were chosen — what does
  `disjoint_JV` stand for? Why `E_subset`? What does `hus` /
  `Adjacent` / `isAcyclic_iff_hasTopologicalOrder` mean? Just the
  non-obvious ones.

### 2. `design_choices`

ONLY the design justifications that are explicitly in the Lean
comments (typically phrased "we use X instead of Y because Z" or "we
encode … as … rather than …"). Do not invent extra justifications.
If the comments don't discuss any design decisions, output exactly:
`_No notable design choices._`

## Constraints

- DO NOT restate the LaTeX statement — the reader sees it rendered
  next to your output.
- DO NOT include raw Lean comment syntax (`--`, `/-`, `-/`, `/--`).
- Use clean prose paragraphs. Inline code references with `` `backticks` ``.
- Math expressions use `$…$` delimiters (KaTeX renders them).
- Target 80–250 words per section. Be concise.
- Output STRICTLY a JSON object on one line, no other text:

{{"lean_explanation": "…", "design_choices": "…"}}
"""


def call_claude(tex_statement: str, statement: str, comments: str) -> dict[str, str]:
    """Send one row's material to Claude and parse the JSON response."""
    try:
        import anthropic  # type: ignore
    except ImportError:
        sys.exit("error: pip install anthropic")
    client = anthropic.Anthropic()
    prompt = PROMPT.format(
        tex_statement=tex_statement, statement=statement, comments=comments,
    )
    msg = client.messages.create(
        model=MODEL,
        max_tokens=MAX_TOKENS,
        messages=[{"role": "user", "content": prompt}],
    )
    text = "".join(b.text for b in msg.content if b.type == "text").strip()
    # The model is asked for a JSON object, but tolerate fenced output.
    m = re.search(r"\{.*\}", text, re.DOTALL)
    if not m:
        sys.exit(f"error: model did not return JSON; got:\n{text}")
    try:
        obj = json.loads(m.group(0))
    except json.JSONDecodeError as e:
        sys.exit(f"error: malformed JSON from model: {e}\n{text}")
    if "lean_explanation" not in obj or "design_choices" not in obj:
        sys.exit(f"error: missing keys in model response: {obj}")
    return obj


def process_one(ref: str, force: bool) -> bool:
    path = WEBSITE_DATA / f"{ref}.json"
    if not path.exists():
        print(f"[{ref}] error: {path} missing — run fetch_row.py first", file=sys.stderr)
        return False
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("lean_explanation") and data.get("design_choices") and not force:
        print(f"[{ref}] already processed, skipping (use --force to overwrite)")
        return True
    statement     = "\n\n".join(b["statement"] for b in data.get("lean", []) if b.get("statement"))
    comments      = "\n\n---\n\n".join(b["comments"] for b in data.get("lean", []) if b.get("comments"))
    tex_statement = (data.get("tex_statement") or {}).get("raw") or ""
    if not comments.strip():
        print(f"[{ref}] no comments to process")
        data["lean_explanation"] = "_No comments accompany this declaration._"
        data["design_choices"]   = "_No notable design choices._"
    else:
        print(f"[{ref}] calling {MODEL}…")
        obj = call_claude(tex_statement, statement, comments)
        data["lean_explanation"] = obj["lean_explanation"]
        data["design_choices"]   = obj["design_choices"]
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"[{ref}] wrote {path.relative_to(REPO_ROOT)}")
    return True


def all_refs() -> list[str]:
    return sorted(
        p.stem for p in WEBSITE_DATA.glob("*.json")
        if p.stem != "manifest" and re.match(r"^(def|claim)_\d+_\d+$", p.stem)
    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("ref", nargs="?", help="row identifier; omit with --all")
    ap.add_argument("--all", action="store_true", help="process every data/<ref>.json")
    ap.add_argument("--force", action="store_true", help="overwrite existing prose")
    args = ap.parse_args()

    if args.all:
        refs = all_refs()
    elif args.ref:
        refs = [args.ref]
    else:
        ap.error("provide a ref or use --all")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        sys.exit("error: set ANTHROPIC_API_KEY in the environment")
    ok = True
    for r in refs:
        ok = process_one(r, args.force) and ok
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
