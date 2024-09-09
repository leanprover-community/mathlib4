#!/usr/bin/env bash

# Check if there are changes to `nolints.json` and file a PR updating it if necessary.
# DO NOT run this as a human; this is meant only for automation usage!

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

set -x

remote_name=origin-bot
branch_name=nolints
owner_name=leanprover-community

# Exit if the branch already exists
git fetch --quiet "$remote_name"
git rev-parse --verify --quiet "refs/remotes/${remote_name}/${branch_name}" && exit 0

# Exit if there are no changes relative to master
git diff-index --quiet "refs/remotes/${remote_name}/master" -- scripts/nolints.json && exit 0

pr_title='chore(scripts): update nolints.json
pr_body='I am happy to remove some nolints for you!'

git checkout -b "$branch_name"
git add scripts/nolints.json
git commit -m "$pr_title"

gh_api() {
  local url="$1"
  shift
  curl -s -H "Authorization: token $DEPLOY_GITHUB_TOKEN" \
    "https://api.github.com/$url" "$@"
}

git push "${remote_name}" "HEAD:$branch_name"

pr_id=$(gh_api "repos/${owner_name}/mathlib4/pulls" -X POST -d @- <<EOF | jq -r .number
{
  "title": "$pr_title",
  "head": "$branch_name",
  "base": "master",
  "body": "$pr_body"
}
EOF
)

gh_api "repos/${owner_name}/mathlib4/issues/${pr_id}/comments" -X POST -d @- <<EOF
{ "body": "bors r+" }
EOF
