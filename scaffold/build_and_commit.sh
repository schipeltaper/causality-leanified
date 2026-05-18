#!/usr/bin/env bash
# build_and_commit.sh
#
# The only sanctioned way to commit + push in this repo.
# Runs `lake build` from the Lean project root; only if the build is clean
# does it commit whatever is currently staged and push the current branch.
#
# Usage:
#   git add <files>                       # stage your changes first
#   scaffold/build_and_commit.sh "msg"    # build, commit, push

set -euo pipefail

REPO_DIR="/home/11716061/repo_scaffold2"
LEAN_PROJECT_DIR="/home/11716061"

if [[ $# -ne 1 || -z "${1// }" ]]; then
  echo "Usage: $0 \"<commit message>\"" >&2
  exit 2
fi
COMMIT_MSG="$1"

cd "$REPO_DIR"

echo ">>> Branch: $(git rev-parse --abbrev-ref HEAD)"
echo ">>> Staged changes:"
git diff --cached --stat
if git diff --cached --quiet; then
  echo "Nothing is staged. Run 'git add <files>' first, then re-run." >&2
  exit 3
fi

echo ">>> Running 'lake build' from $LEAN_PROJECT_DIR ..."
( cd "$LEAN_PROJECT_DIR" && lake build )
echo ">>> Build clean."

echo ">>> Committing ..."
git commit -m "$COMMIT_MSG"

echo ">>> Configuring pack size limit (UvA server quirk) ..."
git config pack.packSizeLimit 50m

echo ">>> Pushing ..."
git push

echo ">>> Done."
