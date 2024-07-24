## Create comments and labels on a Lean 4 PR after CI has finished on a `lean-pr-testing-NNNN` branch.
##
## See https://leanprover-community.github.io/contribute/tags_and_branches.html
set -e


# TODO: The whole script ought to be rewritten in javascript, to avoid having to use curl for API calls.
#
# This is not meant to be run from the command line, only from CI.
# The inputs must be prepared as:
# env:
#   TOKEN: ${{ secrets.LEAN_PR_TESTING }}
#   GITHUB_CONTEXT: ${{ toJson(github) }}
#   WORKFLOW_URL: https://github.com/${{ github.repository }}/actions/runs/${{ github.event.workflow_run.id }}
#   BUILD_OUTCOME: ${{ steps.build.outcome }}
#   NOISY_OUTCOME: ${{ steps.noisy.outcome }}
#   ARCHIVE_OUTCOME: ${{ steps.archive.outcome }}
#   COUNTEREXAMPLES_OUTCOME: ${{ steps.counterexamples.outcome }}
#   LINT_OUTCOME: ${{ steps.lint.outcome }}
#   TEST_OUTCOME: ${{ steps.test.outcome }}

# Extract branch name and check if it matches the pattern.
branch_name=$(echo "$GITHUB_CONTEXT" | jq -r .ref | cut -d'/' -f3)
if [[ "$branch_name" =~ ^lean-pr-testing-([0-9]+)$ ]]; then
  pr_number="${BASH_REMATCH[1]}"
  current_time=$(date "+%Y-%m-%d %H:%M:%S")

  echo "This is a 'lean-pr-testing-$pr_number' branch, so we need to adjust labels and write a comment."

  if [ "$TEST_OUTCOME" == "success" ]; then
    echo "Removing label awaiting-mathlib"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels/awaiting-mathlib
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
  elif [ "$LINT_OUTCOME" == "failure" ] || [ "$TEST_OUTCOME" == "failure" ] || [ "$COUNTEREXAMPLES_OUTCOME" == "failure" ] || [ "$ARCHIVE_OUTCOME" == "failure" ] || [ "$NOISY_OUTCOME" == "failure" ] || [ "$BUILD_OUTCOME" == "failure" ]; then
    echo "Removing label builds-mathlib"
    curl -L -s \
      -X DELETE \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels/builds-mathlib
    echo "Adding labels breaks-mathlib and release-ci"
    curl -L -s \
      -X POST \
      -H "Accept: application/vnd.github+json" \
      -H "Authorization: Bearer $TOKEN" \
      -H "X-GitHub-Api-Version: 2022-11-28" \
      https://api.github.com/repos/leanprover/lean4/issues/$pr_number/labels \
      -d '{"labels":["breaks-mathlib", "release-ci"]}'
  fi

  # Use GitHub API to check if a comment already exists
  existing_comment=$(curl -L -s -H "Authorization: token $TOKEN" \
                          -H "Accept: application/vnd.github.v3+json" \
                          "https://api.github.com/repos/leanprover/lean4/issues/$pr_number/comments" \
                          | jq 'first(.[] | select(.body | test("^- . Mathlib") or startswith("Mathlib CI status")) | select(.user.login == "leanprover-community-mathlib4-bot"))')
  existing_comment_id=$(echo "$existing_comment" | jq -r .id)
  existing_comment_body=$(echo "$existing_comment" | jq -r .body)

  branch="[lean-pr-testing-$pr_number](https://github.com/leanprover-community/mathlib4/compare/nightly-testing...lean-pr-testing-$pr_number)"
  # Depending on the success/failure, set the appropriate message
  if [ "$LINT_OUTCOME" == "cancelled" ] || [ "$TEST_OUTCOME" == "cancelled" ] || [ "$COUNTEREXAMPLES_OUTCOME" == "cancelled" ] || [ "$ARCHIVE_OUTCOME" == "cancelled" ] || [ "$NOISY_OUTCOME" == "cancelled" ] || [ "$BUILD_OUTCOME" == "cancelled" ]; then
    message="- 🟡 Mathlib branch $branch build against this PR was cancelled. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$TEST_OUTCOME" == "success" ]; then
    message="- ✅ Mathlib branch $branch has successfully built against this PR. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$BUILD_OUTCOME" == "failure" ] ; then
    message="- 💥 Mathlib branch $branch build failed against this PR. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$LINT_OUTCOME" == "failure" ]; then
    message="- ❌ Mathlib branch $branch built against this PR, but linting failed. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$COUNTEREXAMPLES_OUTCOME" == "failure" ]; then
    message="- ❌ Mathlib branch $branch built against this PR, but the counterexamples library failed. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$ARCHIVE_OUTCOME" == "failure" ]; then
    message="- ❌ Mathlib branch $branch built against this PR, but the archive failed. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$NOISY_OUTCOME" == "failure" ]; then
    message="- ❌ Mathlib branch $branch built against this PR, but was unexpectedly noisy. ($current_time) [View Log]($WORKFLOW_URL)"
  elif [ "$TEST_OUTCOME" == "failure" ]; then
    message="- ❌ Mathlib branch $branch built against this PR, but testing failed. ($current_time) [View Log]($WORKFLOW_URL)"
  else
    message="- 🟡 Mathlib branch $branch build this PR didn't complete normally. ($current_time) [View Log]($WORKFLOW_URL)"
  fi

  echo "$message"

  # Append new result to the existing comment or post a new comment
  if [ -z "$existing_comment_id" ]; then
    # Post new comment with a bullet point
    # Keep message in sync with https://github.com/leanprover/lean4/blob/master/.github/workflows/pr-release.yml
    intro="Mathlib CI status ([docs](https://leanprover-community.github.io/contribute/tags_and_branches.html)):"
    echo "Posting as new comment at leanprover/lean4/issues/$pr_number/comments"
    curl -L -s \
      -X POST \
      -H "Authorization: token $TOKEN" \
      -H "Accept: application/vnd.github.v3+json" \
      -d "$(jq --null-input --arg intro "$intro" --arg val "$message" '{"body": ($intro + "\n" + $val)}')" \
      "https://api.github.com/repos/leanprover/lean4/issues/$pr_number/comments"
  else
    # Append new result to the existing comment
    echo "Appending to existing comment at leanprover/lean4/issues/$pr_number/comments"
    curl -L -s \
      -X PATCH \
      -H "Authorization: token $TOKEN" \
      -H "Accept: application/vnd.github.v3+json" \
      -d "$(jq --null-input --arg existing "$existing_comment_body" --arg message "$message" '{"body":($existing + "\n" + $message)}')" \
      "https://api.github.com/repos/leanprover/lean4/issues/comments/$existing_comment_id"
  fi
fi
