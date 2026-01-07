#!/usr/bin/env bash
# Create Test Branch with Failing Auto Commit Verification
# Creates a test branch where an auto commit doesn't match its command output
#
# Usage: ./scripts/create_test_branch_failing_auto.sh [base_branch]
#
# Arguments:
#   base_branch  Branch to base test branch on (default: current branch)

set -euo pipefail

BASE_BRANCH="${1:-$(git symbolic-ref --short HEAD)}"
TEST_BRANCH="ci-x-test-fail-auto-$(date +%s)"

echo "Creating test branch '$TEST_BRANCH' based on '$BASE_BRANCH'..."

# Create and checkout test branch
git checkout -b "$TEST_BRANCH" "$BASE_BRANCH"

# --- 1. Create a script that we'll claim to run ---
# The script creates a specific output file
cat > scripts/test_auto.sh << 'SCRIPT'
#!/usr/bin/env bash
echo "correct output" > scripts/auto_output.txt
SCRIPT
chmod +x scripts/test_auto.sh
git add scripts/test_auto.sh
git commit -m "add test_auto.sh"

# --- 2. Auto commit that lies about its content ---
# The commit message says we ran test_auto.sh, but we actually create different content
echo "wrong output" > scripts/auto_output.txt
git add scripts/auto_output.txt
git commit -m "x: scripts/test_auto.sh"

echo ""
echo "Test branch '$TEST_BRANCH' created with:"
echo "  - 1 substantive commit (adds test_auto.sh)"
echo "  - 1 auto commit (claims to run test_auto.sh but has 'wrong output' instead of 'correct output')"
echo ""
echo "Verification SHOULD FAIL because the auto commit content doesn't match"
echo "what the command would actually produce."
echo ""
echo "Run verification with:"
echo "  ./scripts/verify_commits.sh $BASE_BRANCH"
echo ""
echo "To clean up:"
echo "  git checkout $BASE_BRANCH && git branch -D $TEST_BRANCH"
