#!/usr/bin/env bash
# run_refactor_pipeline.sh -- chain solve -> finalize -> merge for one
# refactor table, so a single background invocation drives the whole
# pipeline through to a server-branch merge.
#
# Usage:
#   scaffold/scripts/run_refactor_pipeline.sh <refactor_data.json> [flags]
#
# Where <refactor_data.json> is the path under
# `leanification/ChapterN_*/Refactor_<name>/refactor_data.json` (the
# pre-archive path, same one `do_refactor.py finalize` consumes).
#
# Flags (forwarded to `do_refactor.py finalize`):
#   --auto-rename-strays           rename stray `refactor_*` decls (default)
#   --mark-deviations-resolved=X   (default: auto)
#   --skip-dup-check               skip Pass 1.7 duplicate-decl gate
#
# Logs to $LOG (default: /tmp/refactor_pipeline_<name>.log). Each phase
# transition and exit code is logged, so a monitor can `tail -F` the
# file and grep for STEP / exit:.

set -u

REPO=/home/11716061/repo_scaffold2

if [ $# -lt 1 ]; then
  echo "Usage: $0 <refactor_data.json> [flags]" >&2
  exit 2
fi

DATA="$1"
shift

# Forward all remaining args to the finalize step.
FINALIZE_FLAGS=( --mark-deviations-resolved=auto --auto-rename-strays "$@" )

# Derive a log name from the refactor folder.
NAME=$(basename "$(dirname "$DATA")" | sed -E 's/^Refactor_//; s/_DONE_.*//; s/_BUILDFAIL_.*//')
LOG=${LOG:-/tmp/refactor_pipeline_${NAME}.log}

cd "$REPO" || exit 1

{
  echo "=== Pipeline started at $(date -u +%Y-%m-%dT%H:%M:%SZ) ==="
  echo "Refactor:  $NAME"
  echo "Data:      $DATA"
  echo "Finalize:  ${FINALIZE_FLAGS[*]}"
  echo "Branch:    $(git branch --show-current)"
  echo

  echo "--- STEP 1: solve_chapter on $DATA ---"
  python3 scaffold/scripts/phase3_solving/solve_chapter.py --data-path "$DATA"
  SOLVE_RC=$?
  echo "solve_chapter exit: $SOLVE_RC at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  if [ "$SOLVE_RC" -ne 0 ]; then
    echo "STEP 1 failed (rc=$SOLVE_RC); skipping finalize/merge."
    exit "$SOLVE_RC"
  fi

  echo
  echo "--- STEP 2: finalize ---"
  python3 extras/do_refactor.py finalize --refactor-data "$DATA" "${FINALIZE_FLAGS[@]}"
  FINALIZE_RC=$?
  echo "finalize exit: $FINALIZE_RC at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  if [ "$FINALIZE_RC" -ne 0 ]; then
    echo "STEP 2 failed (rc=$FINALIZE_RC); skipping merge."
    exit "$FINALIZE_RC"
  fi

  # Locate the archived path (DONE or BUILDFAIL, same as do_refactor.py merge accepts).
  CHAPTER_DIR=$(dirname "$DATA" | xargs dirname)
  DONE_DATA=$(ls -t "$CHAPTER_DIR"/Refactor_"$NAME"_DONE_*/refactor_data.json 2>/dev/null | head -1)
  if [ -z "$DONE_DATA" ]; then
    DONE_DATA=$(ls -t "$CHAPTER_DIR"/Refactor_"$NAME"_BUILDFAIL_*/refactor_data.json 2>/dev/null | head -1)
  fi
  if [ -z "$DONE_DATA" ]; then
    echo "Could not locate archived refactor_data.json after finalize; aborting merge."
    exit 2
  fi
  echo "Archived refactor_data: $DONE_DATA"

  echo
  echo "--- STEP 3: merge ---"
  python3 extras/do_refactor.py merge --refactor-data "$DONE_DATA"
  MERGE_RC=$?
  echo "merge exit: $MERGE_RC at $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  exit "$MERGE_RC"
} >> "$LOG" 2>&1
