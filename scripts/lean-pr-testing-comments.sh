## Create comments and labels on a Lean 4 PR after CI has finished on a `lean-pr-testing-NNNN` branch.
set -e

# TODO: The whole script ought to be rewritten in javascript, to avoid having to use curl for API calls.
#
# This is not meant to be run from the command line, only from CI.
# The inputs must be prepared as:
# env:
#   TOKEN: ${{ secrets.LEAN_PR_TESTING }}
#   GITHUB_CONTEXT: ${{ toJson(github) }}
#   WORKFLOW_URL: ${{ github.event.workflow_run.html_url }}
#   LINT_OUTCOME: ${{ steps.lint.outcome }}
#   TEST_OUTCOME: ${{ steps.test.outcome }}
#   BUILD_OUTCOME: ${{ steps.build.outcome }}

# Extract branch name and check if it matches the pattern.
branch_name=$(echo "$GITHUB_CONTEXT" | jq -r .ref | cut -d'/' -f3)
if [[ "$branch_name" =~ ^lean-pr-testing-([0-9]+)$ ]]; then
  pr_number="${BASH_REMATCH[1]}"
  current_time=$(date "+%Y-%m-%d %H:%M:%S")

  echo "This is a 'lean-pr-testing-$pr_number' branch, so we need to adjust labels and write a comment."

  if [ "$LINT_OUTCOME" == "success" ]; then
    echo "Removing label awaiting-mathlib-build"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels/awaiting-mathlib-build
    echo "Removing label breaks-mathlib"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels/breaks-mathlib
    echo "Adding label builds-mathlib"
    curl -L -s \
      -X POST \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels \
      -d '{"labels":["builds-mathlib"]}'
  else
    echo "Removing label builds-mathlib"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels/builds-mathlib
    echo "Adding label breaks-mathlib"
    curl -L -s \
      -X POST \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels \
      -d '{"labels":["breaks-mathlib"]}'
  fi

  # Use GitHub API to check if a comment already exists
  existing_comment=$(curl -L -s -H "Authorization: token $TOKEN" \
                          -H "Accept: application/vnd.github.v3+json" \
                          "https://api.github.com/repos/leanprover/lean4/issues/$pr_number/comments" \
                          | jq '.[] | select(.body | startswith("- ✅ Mathlib") or startswith("- ❌ Mathlib") or startswith("- 💥 Mathlib"))')
  existing_comment_id=$(echo "$existing_comment" | jq -r .id)
  existing_comment_body=$(echo "$existing_comment" | jq -r .body)

  branch="[lean-pr-testing-$pr_number](https://github.com/leanprover-community/mathlib4/compare/master...lean-pr-testing-$pr_number)"
  # Depending on the success/failure, set the appropriate message
  if [ "$LINT_OUTCOME" == "success" ]; then
    message="✅ Mathlib branch $branch has successfully built against this PR. ($current_time)"
  elif [ "$TEST_OUTCOME" == "success" ]; then
    message="❌ Mathlib branch $branch built against this PR, but linting failed. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$BUILD_OUTCOME" == "success" ]; then
    message="❌ Mathlib branch $branch built against this PR, but testing failed. ($current_time) [View Log]($WORKFLOW_URL)"
  else
    message="💥 Mathlib branch $branch failed against this PR. ($current_time) [View Log]($WORKFLOW_URL)"
  fi

  echo "$message"

  # Append new result to the existing comment or post a new comment
  if [ -z "$existing_comment_id" ]; then
    # Post new comment with a bullet point
    echo "Posting as new comment at leanprover/lean4/issues/$pr_number/comments"
    curl -L -s \
      -X POST \
      -H "Authorization: token $TOKEN" \
      -H "Accept: application/vnd.github.v3+json" \
      -d "$(jq --null-input --arg val "- $message" '{"body": $val}')" \
      "https://api.github.com/repos/leanprover/lean4/issues/$pr_number/comments"
  else
    # Append new result to the existing comment
    echo "Appending to existing comment at leanprover/lean4/issues/$pr_number/comments"
    updated_comment_body="$existing_comment_body\n- $message"
    curl -L -s \
      -X PATCH \
      -H "Authorization: token $TOKEN" \
      -H "Accept: application/vnd.github.v3+json" \
      -d "$(jq --null-input --arg val "- $updated_comment_body" '{"body": $val}')" \
      "https://api.github.com/repos/leanprover/lean4/issues/comments/$existing_comment_id"
  fi
fi
