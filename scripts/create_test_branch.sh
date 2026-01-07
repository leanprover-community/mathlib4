#!/usr/bin/env bash
# Create Test Branch for Commit Verification
# Creates a test branch with example transient, auto, and substantive commits
#
# Usage: ./scripts/create_test_branch.sh [base_branch]
#
# Arguments:
#   base_branch  Branch to base test branch on (default: current branch)

set -euo pipefail

BASE_BRANCH="${1:-$(git symbolic-ref --short HEAD)}"
TEST_BRANCH="ci-x-test-$(date +%s)"

echo "Creating test branch '$TEST_BRANCH' based on '$BASE_BRANCH'..."

# Create and checkout test branch
git checkout -b "$TEST_BRANCH" "$BASE_BRANCH"

# --- 1. Transient commit: add a test script ---
cat > scripts/test_refactor.sh << 'SCRIPT'
#!/usr/bin/env bash
# Test refactoring script - adds a marker to RFC
echo "# (refactored)" >> RFC-commit-verification.md
SCRIPT
chmod +x scripts/test_refactor.sh
git add scripts/test_refactor.sh
git commit -m "transient: add test_refactor.sh script"

# --- 2. Auto commit: run the script and commit the result ---
scripts/test_refactor.sh
git add -u
git commit -m "x: scripts/test_refactor.sh"

# --- 3. Transient commit: remove the script ---
git rm scripts/test_refactor.sh
git commit -m "transient: remove test_refactor.sh script"

echo ""
echo "Test branch '$TEST_BRANCH' created with:"
echo "  - 2 transient commits (add/remove script - zero net effect)"
echo "  - 1 auto commit (x: scripts/test_refactor.sh - adds refactor marker to RFC)"
echo ""
echo "Run verification with:"
echo "  ./scripts/verify_commits.sh $BASE_BRANCH"
echo ""
echo "To clean up:"
echo "  git checkout $BASE_BRANCH && git branch -D $TEST_BRANCH"
