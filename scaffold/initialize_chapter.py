import json
import re
from pathlib import Path

# Load global variables from the JSON data file.
GLOBAL_VARS_PATH = Path(__file__).parent / "global_vars.json"
with open(GLOBAL_VARS_PATH) as f:
    global_vars = json.load(f)

current_chapter = global_vars["current_chapter"]

# The lecture notes live one directory up from the scaffold.
SCAFFOLD_DIR = Path(__file__).resolve().parent
LECTURE_NOTES_DIR = SCAFFOLD_DIR.parent / "lecture-notes" / "lecture_notes"
MAIN_TEX_PATH = LECTURE_NOTES_DIR / "main.tex"

# Where each chapter is formalized: leanification/{chapter}_{title}/
LEANIFICATION_DIR = SCAFFOLD_DIR.parent / "leanification"

# Initialize current chapter
def initialize():
    # Get title_chapter and tex_file_chapter
    (title_chapter, tex_file_chapter) = get_title_and_tex_file_chapter(current_chapter)

    create_folder(current_chapter, title_chapter)

    # Create empty data file in {current_chapter}_{title_chapter} folder
    create_data(current_chapter, title_chapter)

    # Find all defs and claims in current_chapter
    # TODO make Python script that calls Claude to do this

    # Wait for human confirmation

    # run create data script

    return tex_file_chapter

# Create empty data file in {current_chapter}_{title_chapter} within leanification folder
# It will represent a large table. Each row will be a claim or def from the lecture notes.
# Column titles: 
#   def or claim, 
#   checkmark solved or not, 
#   reference to the tex in the form ref[def/claim]_[chapter]_[nth item in this chapter],
#   Type (like definition, theorem, note, remark, lemma, corollary, etc.)
#   Date solved
#   Tips (like, the proof is at the end of this chapter in the lecture notes!)
#   Which tex file it is in
#   Lean file path (of the formalization of the statement)  
#   Actions_tracking (a new table that tracks how often each action is called for this row)
def create_data(current_chapter, title_chapter):
    """Create an empty data file for a chapter and return its Path.

    Writes ``data.json`` into the chapter's leanification folder. Each future
    row is one definition or claim from the lecture notes; this lays down the
    schema with an empty ``rows`` list. An existing data file is left as is,
    so tracked progress is never overwritten.
    """
    chapter_folder = create_folder(current_chapter, title_chapter)
    data_path = chapter_folder / "data.json"
    if data_path.exists():
        return data_path

    dataset = {
        "chapter": current_chapter,
        "title": title_chapter,
        "columns": [
            "def_or_claim",
            "solved",
            "ref",
            "type",
            "date_solved",
            "tips",
            "tex_file",
            "lean_file",
            "actions_tracking",
        ],
        "rows": [],
    }
    with open(data_path, "w", encoding="utf-8") as f:
        json.dump(dataset, f, indent=2, ensure_ascii=False)
    return data_path


# Create chapter folder in leanification folder: {current_chapter}_{title_chapter}
def create_folder(current_chapter, title_chapter):
    """Create the leanification folder for a chapter and return its Path.

    The folder is named ``{current_chapter}_{title}`` inside LEANIFICATION_DIR,
    with the title made safe for use as a folder name. Safe to call repeatedly:
    an existing folder is left untouched.
    """
    folder_name = f"{current_chapter}_{_sanitize_for_folder(title_chapter)}"
    chapter_folder = LEANIFICATION_DIR / folder_name
    chapter_folder.mkdir(parents=True, exist_ok=True)
    return chapter_folder


def _sanitize_for_folder(name):
    """Turn a chapter title into a valid folder name.

    Resolves common LaTeX escapes (e.g. ``\\&`` -> ``&``) and drops the
    characters Windows does not allow in folder names.
    """
    name = re.sub(r"\\([&%_#${}])", r"\1", name)  # \& -> &, \% -> %, ...
    name = re.sub(r'[<>:"/\\|?*]', "", name)      # drop illegal characters
    return re.sub(r"\s+", " ", name).strip(" .")


def get_title_and_tex_file_chapter(current_chapter):
    """Return (title, tex_file) for chapter number `current_chapter` (1-indexed).

    A "chapter" is a numbered \\section in the lecture notes. main.tex is the
    entry point: this walks its \\input chain in order and, for every
    \\section, records its title and the .tex file it appears in. Returns the
    `current_chapter`-th pair as (title_chapter, tex_file_chapter).
    """
    main_tex = _read_tex(MAIN_TEX_PATH)

    chapters = []  # (title, tex_file) for each numbered section, in order
    for name in _chapter_input_files(main_tex):
        tex_file = f"{name}.tex"
        tex_path = LECTURE_NOTES_DIR / tex_file
        if tex_path.exists():
            for title in _section_titles(_read_tex(tex_path)):
                chapters.append((title, tex_file))

    if not 1 <= current_chapter <= len(chapters):
        raise ValueError(
            f"current_chapter={current_chapter} is out of range; "
            f"the lecture notes contain {len(chapters)} chapters."
        )
    return chapters[current_chapter - 1]

def _strip_tex_comments(text):
    """Remove LaTeX comments: everything after an unescaped '%' on each line."""
    return "\n".join(
        re.sub(r"(?<!\\)%.*", "", line) for line in text.splitlines()
    )


def _read_tex(path):
    """Read a .tex file (lecture notes are latin-1 encoded), comments stripped."""
    return _strip_tex_comments(path.read_text(encoding="latin-1"))


def _chapter_input_files(main_tex):
    """Ordered list of files \\input by main.tex within the document body."""
    body = main_tex.split(r"\begin{document}", 1)[-1]
    return re.findall(r"\\input\{([^}]+)\}", body)


def _balanced_braces(text, start):
    """Content of a brace group whose first inner character is at index `start`."""
    depth = 1
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start:i].strip()
    return text[start:].strip()  # unbalanced braces: return whatever remains


def _section_titles(tex):
    """Titles of every numbered \\section{...} in `tex`, in document order.

    Starred sections (\\section*{...}, such as the foreword) are unnumbered,
    so they are not counted as chapters.
    """
    return [
        _balanced_braces(tex, m.end())
        for m in re.finditer(r"\\section\s*\{", tex)
    ]




if __name__ == "__main__":
    initialize(current_chapter)
