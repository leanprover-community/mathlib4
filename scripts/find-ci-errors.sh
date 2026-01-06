#!/bin/bash
#
# find-pr-ci-errors.sh - Find open PRs with failing CI containing a specific error string
#
# This script searches through recent failed CI workflow runs, downloads their logs,
# and identifies which open PRs currently have failing CI containing a given substring.
# This is useful for diagnosing widespread CI issues affecting multiple PRs.
#
# Usage:
#   ./find-pr-ci-errors.sh <search-string>
#   ./find-pr-ci-errors.sh --please-merge-master <search-string>
#
# Options:
#   --please-merge-master  Add the 'please-merge-master' label to all matching PRs
#                          (except those with the 'merge-conflict' label).
#                          The label is automatically removed by CI once the build completes.
#
# Examples:
#   # Find PRs failing with a specific error
#   ./find-pr-ci-errors.sh "Error parsing args: cannot parse arguments"
#
#   # Find PRs and request master merge to fix infrastructure issues
#   ./find-pr-ci-errors.sh --please-merge-master "cannot parse arguments"
#
# Requirements:
#   - gh (GitHub CLI) installed and authenticated
#   - jq for JSON parsing
#
# Notes:
#   - Downloads logs to /tmp/gh-run-*.log (cached to avoid re-downloading)
#   - Checks up to 200 recent failed runs
#   - Only reports PRs whose CURRENT CI status is failing (ignores PRs that have
#     since been fixed by retries or new commits)
#

set -e

PLEASE_MERGE_MASTER=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --please-merge-master)
            PLEASE_MERGE_MASTER=true
            shift
            ;;
        -*)
            echo "Unknown option: $1"
            echo "Usage: $0 [--please-merge-master] <search-string>"
            exit 1
            ;;
        *)
            SEARCH_STRING="$1"
            shift
            ;;
    esac
done

if [ -z "$SEARCH_STRING" ]; then
    echo "Usage: $0 [--please-merge-master] <search-string>"
    exit 1
fi

REPO="leanprover-community/mathlib4"

echo "Searching for open PRs with CURRENTLY failing CI containing: $SEARCH_STRING"
echo "Repository: $REPO"
if [ "$PLEASE_MERGE_MASTER" = true ]; then
    echo "Will add 'please-merge-master' label to matching PRs (except those with merge-conflict)"
fi
echo ""

# Get recent failed workflow runs directly (much faster than iterating all PRs)
echo "Fetching recent failed workflow runs..."
FAILED_RUNS=$(gh run list --repo "$REPO" --status failure --limit 200 --json databaseId,headBranch,displayTitle,createdAt)

RUN_COUNT=$(echo "$FAILED_RUNS" | jq length)
echo "Found $RUN_COUNT recent failed runs"
echo ""

MATCHING_PRS=()
CHECKED_BRANCHES=()
CHECKED=0

for row in $(echo "$FAILED_RUNS" | jq -r '.[] | @base64'); do
    _jq() {
        echo "$row" | base64 --decode | jq -r "$1"
    }

    RUN_ID=$(_jq '.databaseId')
    HEAD_BRANCH=$(_jq '.headBranch')
    TITLE=$(_jq '.displayTitle')

    # Skip if we already checked this branch (only check most recent run per branch)
    if [[ " ${CHECKED_BRANCHES[*]} " =~ " ${HEAD_BRANCH} " ]]; then
        continue
    fi
    CHECKED_BRANCHES+=("$HEAD_BRANCH")

    CHECKED=$((CHECKED + 1))
    echo "[$CHECKED] Checking run $RUN_ID (branch: $HEAD_BRANCH)"

    # Download logs to temp file (with caching)
    LOG_FILE="/tmp/gh-run-$RUN_ID.log"

    if [ ! -f "$LOG_FILE" ]; then
        gh run view "$RUN_ID" --repo "$REPO" --log > "$LOG_FILE" 2>/dev/null || {
            echo "  Failed to download logs"
            continue
        }
    fi

    if grep -q "$SEARCH_STRING" "$LOG_FILE" 2>/dev/null; then
        echo "  ✓ Log contains search string"

        # Try to find associated open PR for this branch
        PR_INFO=$(gh pr list --repo "$REPO" --state open --head "$HEAD_BRANCH" --json number,title --limit 1 2>/dev/null || echo "[]")
        PR_NUM=$(echo "$PR_INFO" | jq -r '.[0].number // empty')
        PR_TITLE=$(echo "$PR_INFO" | jq -r '.[0].title // empty')

        if [ -n "$PR_NUM" ]; then
            # Verify this PR's CURRENT CI is still failing (not fixed by retry/new commit)
            CURRENT_STATUS=$(gh pr checks "$PR_NUM" --repo "$REPO" 2>/dev/null || echo "")
            if echo "$CURRENT_STATUS" | grep -q "fail"; then
                echo "  ✓ PR #$PR_NUM currently has failing CI - MATCH!"
                MATCHING_PRS+=("$PR_NUM|$PR_TITLE|$RUN_ID")

                # Add please-merge-master label if requested
                if [ "$PLEASE_MERGE_MASTER" = true ]; then
                    # Check for merge-conflict or existing please-merge-master label
                    PR_LABELS=$(gh pr view "$PR_NUM" --repo "$REPO" --json labels -q '.labels[].name' 2>/dev/null || echo "")
                    if echo "$PR_LABELS" | grep -q "merge-conflict"; then
                        echo "  ⚠ PR #$PR_NUM has merge-conflict label - not adding please-merge-master"
                    elif echo "$PR_LABELS" | grep -q "please-merge-master"; then
                        echo "  ℹ PR #$PR_NUM already has please-merge-master label"
                    else
                        echo "  → Adding please-merge-master label to PR #$PR_NUM"
                        gh pr edit "$PR_NUM" --repo "$REPO" --add-label "please-merge-master" 2>/dev/null || echo "  ✗ Failed to add label"
                    fi
                fi
            else
                echo "  ✗ PR #$PR_NUM CI is now passing - skipping"
            fi
        else
            echo "  ✗ No open PR found for branch"
        fi
    fi
done

echo ""
echo "=========================================="
echo "Summary: Found ${#MATCHING_PRS[@]} open PRs with CURRENTLY failing CI containing '$SEARCH_STRING'"
echo ""
for item in "${MATCHING_PRS[@]}"; do
    PR_NUM=$(echo "$item" | cut -d'|' -f1)
    PR_TITLE=$(echo "$item" | cut -d'|' -f2)
    RUN_ID=$(echo "$item" | cut -d'|' -f3)

    echo "- https://github.com/$REPO/pull/$PR_NUM"
    echo "  $PR_TITLE"
    echo "  Run: https://github.com/$REPO/actions/runs/$RUN_ID"
    echo ""
done
