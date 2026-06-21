#!/usr/bin/env bash

# Export every changed file in a GitHub PR as its own git diff file.
#
# Usage:
#   scripts/export-pr-file-diffs.sh [PR_NUMBER] [OUT_DIR] [REPO_URL]
#
# Examples:
#   scripts/export-pr-file-diffs.sh
#   scripts/export-pr-file-diffs.sh 40147 pr_diff
#   scripts/export-pr-file-diffs.sh 40147 pr_diff https://github.com/leanprover-community/mathlib4
#
# Defaults:
#   PR_NUMBER = 40147
#   OUT_DIR   = pr_diff
#   REPO_URL  = https://github.com/leanprover-community/mathlib4
#
# Output naming:
#   Mathlib/Analysis/Integral.lean -> pr_diff/Mathlib-Analysis-Integral.diff
#
# Notes:
#   - Run this from inside a git repository.
#   - The script fetches refs/pull/<PR_NUMBER>/{head,merge} from REPO_URL.
#   - It uses the merge ref's first parent as the base, matching GitHub's
#     current PR "Files changed" comparison point.
#   - Existing files with the same output names are overwritten.

set -euo pipefail

pr_number="${1:-40147}"
out_dir="${2:-pr_diff}"
repo_url="${3:-https://github.com/leanprover-community/mathlib4}"

head_ref="refs/remotes/pr/${pr_number}/head"
merge_ref="refs/remotes/pr/${pr_number}/merge"

git rev-parse --show-toplevel >/dev/null

mkdir -p "$out_dir"

git fetch --no-tags "$repo_url" \
  "refs/pull/${pr_number}/head:${head_ref}" \
  "refs/pull/${pr_number}/merge:${merge_ref}"

base_ref="${merge_ref}^1"

count=0
while IFS= read -r -d '' path; do
  stem="${path%.*}"
  out_file="${out_dir}/${stem//\//-}.diff"
  git diff --output="$out_file" "${base_ref}...${head_ref}" -- "$path"
  count=$((count + 1))
  printf 'wrote %s\n' "$out_file"
done < <(git diff --name-only -z "${base_ref}...${head_ref}")

printf 'exported %d diff file(s) to %s\n' "$count" "$out_dir"
