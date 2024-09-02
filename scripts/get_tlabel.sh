#!/usr/bin/env bash

PR="${1}"

>&2 printf $'Using PR: \'%s\'\n' "${PR}"

tlabels="$(gh api --jq '.labels.[].name' "${PR}" | grep -- '^t-' || printf 'generic')"
# print to error, since the stdout is captured into `GITHUB_OUTPUT
>&2 printf 't-labels:\n---\n%s\n---\n' "${tlabels}"
# if there isn't exactly 1 `t-xxx` label, use `generic`
if [[ "$(wc -l <<<"${tlabels}")" -ne 1 ]]; then
  tlabels="generic"
fi
topicName="$maintainer merge: {tlabels}"
>&2 printf $'Post to topic: \'%s\'"\n' "${topicName}"
echo "topic=${topicName}"
