#!/usr/bin/env bash

# Check if there are changes in the working directory
# (which should come from the linter removing deprecated declarations)
# and file a PR if necessary.
# Also set an output parameter 'message' containing a Zulip message
# DO NOT run this as a human; this is meant only for usage in automation!

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

set -x

remote_name=origin-bot
branch_name=deprecated-decls
owner_name=leanprover-community
from_date="${1:-from date not set}"
to_date="${2:-to date not set}"

# Exit if the branch already exists (a PR is already open)
git fetch --quiet "$remote_name"
git rev-parse --verify --quiet "refs/remotes/${remote_name}/${branch_name}" && exit 0

pr_title="chore: remove declarations deprecated between $from_date and $to_date"
pr_body='I am happy to remove some deprecated declarations for you! Please check if there are any remaining stray comments or other issues before merging.'

git checkout -b "$branch_name"
git add -u
git commit -m "$pr_title" || { echo "No changes to commit" && exit 0; }

gh_api() {
  local url="$1"
  shift
  curl -s -H "Authorization: token $DEPLOY_GITHUB_TOKEN" \
    "https://api.github.com/$url" "$@"
}

git push "${remote_name}" "HEAD:$branch_name"

pr_id="$(gh_api "repos/${owner_name}/mathlib4/pulls" -X POST -d @- <<EOF | jq -r .number
{
  "title": "$pr_title",
  "head": "$branch_name",
  "base": "master",
  "body": "$pr_body"
}
EOF
)"

printf $'message<<EOF\nPlease review #%s, which removes deprecated declarations between %s and %s. Pay special attention to whether there are stray comments that can also be deleted.\nEOF\n' "${pr_id}" "${from_date}" "${to_date}" | tee -a "${GITHUB_OUTPUT}"
