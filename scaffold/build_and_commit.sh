#!/usr/bin/env bash
# build_and_commit.sh
#
# The only sanctioned way to commit + push in this repo.
# Stages every modified/new file in the working tree (git add -A), then
# runs `lake build` from the Lean project root; only if the build is
# clean does it commit and push the current branch.
#
# Usage:
#   scaffold/build_and_commit.sh "<commit message>"
#
# Before running, eyeball `git status` and make sure nothing unwanted
# (build artifacts, scratch files) is sitting in the working tree --
# auto-stage will sweep it in. Use `.gitignore` for anything persistent.

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

echo ">>> Auto-staging all changes in the working tree ..."
git add -A

echo ">>> Staged changes:"
git diff --cached --stat
if git diff --cached --quiet; then
  echo "Nothing to commit." >&2
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
