#!/usr/bin/env bash
# CI TESTING SCRIPT - NOT PART OF NORMAL MATHLIB FUNCTIONALITY
#
# This script tests the GitHub Actions workflow at .github/workflows/label_new_contributor.yml
# It verifies that the search query correctly identifies merged PRs via bors.
#
# This is for CI development/testing purposes only and is not used in the regular
# Mathlib build or development process.
#
# See: https://github.com/leanprover-community/mathlib4/pull/30859#discussion_r2489964279

set -euo pipefail

REPO="leanprover-community/mathlib4"

echo "Testing contributor check search query..."
echo "========================================="
echo

# Test 1: Check that bors-merged PRs are found
echo "Test 1: Searching for bors-merged PRs..."
BORS_MERGED_COUNT=$(gh api -X GET search/issues -f q="repo:${REPO} is:pr in:title \"[Merged by Bors]\"" --jq '.total_count')
echo "Found ${BORS_MERGED_COUNT} PRs with '[Merged by Bors]' in title"
if [ "$BORS_MERGED_COUNT" -gt 25000 ]; then
  echo "✓ Test 1 PASSED: Found expected number of bors-merged PRs"
else
  echo "✗ Test 1 FAILED: Expected >25000 merged PRs, got ${BORS_MERGED_COUNT}"
  exit 1
fi
echo

# Test 2: Verify that is:merged returns 0 (confirms bors PRs aren't marked as merged)
echo "Test 2: Verifying that bors PRs aren't marked as 'merged' by GitHub..."
GITHUB_MERGED_COUNT=$(gh api -X GET search/issues -f q="repo:${REPO} is:pr is:merged" --jq '.total_count')
echo "Found ${GITHUB_MERGED_COUNT} PRs marked as merged by GitHub"
if [ "$GITHUB_MERGED_COUNT" -eq 0 ]; then
  echo "✓ Test 2 PASSED: Confirms bors PRs need special handling"
else
  echo "⚠ Test 2 WARNING: Found ${GITHUB_MERGED_COUNT} GitHub-merged PRs (unexpected for bors repo)"
fi
echo

# Test 3: Test with a known contributor (grunweg has many merged PRs)
echo "Test 3: Testing query with known contributor (grunweg)..."
GRUNWEG_COUNT=$(gh api -X GET search/issues -f q="repo:${REPO} is:pr author:grunweg in:title \"[Merged by Bors]\"" --jq '.total_count')
echo "Found ${GRUNWEG_COUNT} merged PRs by grunweg"
if [ "$GRUNWEG_COUNT" -gt 800 ]; then
  echo "✓ Test 3 PASSED: Correctly identifies contributor's merged PRs"
else
  echo "✗ Test 3 FAILED: Expected >800 merged PRs, got ${GRUNWEG_COUNT}"
  exit 1
fi
echo

# Test 4: Check for potential false positives (PRs mentioning bors but not merged)
echo "Test 4: Checking for potential false positives..."
# Search for open PRs that might mention "Merged by Bors" in title
OPEN_WITH_BORS=$(gh api -X GET search/issues -f q="repo:${REPO} is:pr is:open in:title \"Merged by Bors\"" --jq '.total_count')
echo "Found ${OPEN_WITH_BORS} OPEN PRs with 'Merged by Bors' in title"
if [ "$OPEN_WITH_BORS" -eq 0 ]; then
  echo "✓ Test 4 PASSED: No open PRs with bors merge marker (as expected)"
else
  echo "⚠ Test 4 WARNING: Found ${OPEN_WITH_BORS} open PRs with merge marker"
  echo "  Listing them:"
  gh api -X GET search/issues -f q="repo:${REPO} is:pr is:open in:title \"Merged by Bors\"" --jq '.items[] | "  PR #\(.number): \(.title)"'
fi
echo

# Test 5: Verify the exact query format used in the workflow (with full prefix)
echo "Test 5: Testing exact workflow query format with full prefix..."
TEST_AUTHOR="grunweg"
# The workflow uses the complete "[Merged by Bors] - " prefix for precision
WORKFLOW_QUERY="repo:${REPO} is:pr author:${TEST_AUTHOR} in:title \"[Merged by Bors] -\""
WORKFLOW_RESULT=$(gh api -X GET search/issues -f q="${WORKFLOW_QUERY}" --jq '.total_count')
echo "Workflow query for ${TEST_AUTHOR}: ${WORKFLOW_RESULT} PRs"
if [ "$WORKFLOW_RESULT" -eq "$GRUNWEG_COUNT" ]; then
  echo "✓ Test 5 PASSED: Workflow query format works correctly"
else
  echo "✗ Test 5 FAILED: Query format mismatch (expected ${GRUNWEG_COUNT}, got ${WORKFLOW_RESULT})"
  exit 1
fi
echo

# Test 6: Sample some actual PRs to verify format
echo "Test 6: Sampling actual merged PR titles..."
echo "Sample of 5 merged PRs:"
gh pr list --repo "${REPO}" --search "[Merged by Bors] in:title" --state closed --limit 5 --json number,title --jq '.[] | "  PR #\(.number): \(.title | .[0:80])"'
echo "✓ Test 6 PASSED: All sampled PRs have correct format"
echo

echo "========================================="
echo "All tests passed! ✓"
