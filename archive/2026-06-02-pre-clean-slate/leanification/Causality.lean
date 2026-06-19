-- Root of the `Causality` Lean library.
--
-- Each chapter has an aggregator file `Chapter<N>_<PascalCaseTitle>.lean`
-- next to its folder. This file imports the chapter aggregators so a
-- single `lake build` walks the whole project. The chapter aggregators
-- themselves are auto-managed by `scaffold/solving_current_row.py`.

import Chapter3_GraphTheory
