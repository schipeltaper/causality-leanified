"""Standardised ``sys.path`` setup for scaffold scripts.

The scaffold's Python files are organised under
``scaffold/scripts/<phase>/`` and ``scaffold/scripts/utils/`` -- one
folder per workflow phase, plus a ``utils/`` folder for cross-phase
helpers (subtlety_register, deviations, audit_helpers, …).

Every per-phase script imports this module as its first action::

    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    import _path_setup  # noqa: F401

After that, plain imports like ``from solve_chapter import …`` or
``from subtlety_register import …`` resolve regardless of which phase
folder the importing script lives in -- this module adds every phase
folder and ``utils/`` to ``sys.path``.

(Why not a real Python package with ``__init__.py`` files? Because
the scripts are invoked via ``python scaffold/scripts/<phase>/foo.py``
rather than ``python -m scaffold.scripts.<phase>.foo`` -- preserving
that interface is worth the small bit of sys.path gymnastics.)
"""

import sys
from pathlib import Path

_SCRIPTS_DIR = Path(__file__).resolve().parent
for _d in (
    _SCRIPTS_DIR / "utils",
    _SCRIPTS_DIR / "phase1_pre_initialization",
    _SCRIPTS_DIR / "phase2_initialization",
    _SCRIPTS_DIR / "phase3_solving",
    _SCRIPTS_DIR / "phase4_verifying",
):
    if _d.exists() and str(_d) not in sys.path:
        sys.path.insert(0, str(_d))
