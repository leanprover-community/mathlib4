#!/usr/bin/env bash
# Create Test Branch with Failing Verification (Merge Conflict)
# Creates a test branch where cherry-picking substantive commits fails due to
# dependencies on transient commits, causing a merge conflict.
#
# Usage: ./scripts/create_test_branch_fail_conflict.sh [base_branch]
#
# Arguments:
#   base_branch  Branch to base test branch on (default: current branch)

set -euo pipefail

BASE_BRANCH="${1:-$(git symbolic-ref --short HEAD)}"
TEST_BRANCH="ci-x-test-conflict-$(date +%s)"

echo "Creating test branch '$TEST_BRANCH' based on '$BASE_BRANCH'..."

# Create and checkout test branch
git checkout -b "$TEST_BRANCH" "$BASE_BRANCH"

# --- 1. Transient commit: add a marker (but we won't remove it) ---
echo "# LEFTOVER MARKER" >> RFC-commit-verification.md
git add -u
git commit -m "transient: add marker that should be removed"

# --- 2. Substantive commit: unrelated change ---
echo "# Added by test" >> RFC-commit-verification.md
git add -u
git commit -m "test: add comment"

# The substantive commit depends on the transient commit's changes (both modify same line range),
# so cherry-picking the substantive commit onto the base will fail with a merge conflict.

echo ""
echo "Test branch '$TEST_BRANCH' created with:"
echo "  - 1 transient commit (adds marker)"
echo "  - 1 substantive commit (adds text on the next line)"
echo ""
echo "Verification SHOULD FAIL because cherry-picking the substantive commit"
echo "onto the base causes a merge conflict (transient commits don't commute)."
echo ""
echo "Run verification with:"
echo "  ./scripts/verify_commits.sh $BASE_BRANCH"
echo ""
echo "To clean up:"
echo "  git checkout $BASE_BRANCH && git branch -D $TEST_BRANCH"
