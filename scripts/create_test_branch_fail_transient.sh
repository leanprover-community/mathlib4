#!/usr/bin/env bash
# Create Test Branch with Failing Transient Verification (Net Effect)
# Creates a test branch where transient commits have a net effect on the final tree.
# No merge conflicts occur - the substantive commit cherry-picks cleanly, but
# the final tree differs from what it would be without the transient commits.
#
# Usage: ./scripts/create_test_branch_fail_transient.sh [base_branch]
#
# Arguments:
#   base_branch  Branch to base test branch on (default: current branch)

set -euo pipefail

BASE_BRANCH="${1:-$(git symbolic-ref --short HEAD)}"
TEST_BRANCH="ci-x-test-transient-$(date +%s)"

echo "Creating test branch '$TEST_BRANCH' based on '$BASE_BRANCH'..."

# Create and checkout test branch
git checkout -b "$TEST_BRANCH" "$BASE_BRANCH"

# --- 1. Substantive commit: add a new file (completely independent) ---
cat > scripts/test_substantive.txt << 'EOF'
This is a substantive change that cherry-picks cleanly.
EOF
git add scripts/test_substantive.txt
git commit -m "add test_substantive.txt"

# --- 2. Transient commit: add a marker that we claim will be removed ---
echo "# LEFTOVER MARKER FROM TRANSIENT" >> RFC-commit-verification.md
git add -u
git commit -m "transient: add marker (will NOT be removed)"

# The transient commit modifies a different file than the substantive commit,
# so cherry-picking works fine. But the transient marker is never removed,
# so the final tree differs from base + substantive.

echo ""
echo "Test branch '$TEST_BRANCH' created with:"
echo "  - 1 substantive commit (adds scripts/test_substantive.txt)"
echo "  - 1 transient commit (adds marker to RFC - NOT removed)"
echo ""
echo "Verification SHOULD FAIL because:"
echo "  - Cherry-pick succeeds (no conflict)"
echo "  - But final tree != base + substantive (transient has net effect)"
echo ""
echo "Run verification with:"
echo "  ./scripts/verify_commits.sh $BASE_BRANCH"
echo ""
echo "To clean up:"
echo "  git checkout $BASE_BRANCH && git branch -D $TEST_BRANCH"
