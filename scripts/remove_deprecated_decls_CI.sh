#!/usr/bin/env bash

# Check if there are removed deprecated declarations and file a PR if necessary.
# Also set an output parameter 'message' containing a Zulip message
# DO NOT run this as a human; this is meant only for automation usage!

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

# Exit if the branch already exists
git fetch --quiet "$remote_name"
git rev-parse --verify --quiet "refs/remotes/${remote_name}/${branch_name}" && exit 0

pr_title="chore: remove deprecated declarations from $DEPRECATION_DATE_FROM to $DEPRECATION_DATE_TO"
pr_body='I am happy to remove some deprecated declarations for you!'

git checkout -b "$branch_name"
git add -A
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

printf $'message<<EOF\n\'Please review #%s, which removes deprecated declarations older than %s.\'\nEOF\n' "${pr_id}" "${DEPRECATION_DATE}" | tee -a "${GITHUB_OUTPUT}"
