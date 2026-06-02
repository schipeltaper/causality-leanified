-- Lean library root for the causality formalization.
--
-- On a clean-slate leanification/ folder, this file imports nothing.
-- As each chapter is initialised (via `scaffold/initialize_chapter.py`)
-- the chapter aggregator `Chapter<N>_<Title>.lean` will be created
-- alongside this file and added as an import below, and the chapter's
-- glob will be added to `lakefile.toml`.
import Chapter3_GraphTheory
