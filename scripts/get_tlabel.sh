#!/usr/bin/env bash

 : <<'BASH_MODULE_DOCS'

This script is used by the maintainer merge actions to extract
* either `t-xxx` if `t-xxx` is the unique `t-`label of the PR;
* or `generic` otherwise
and stores it in `tlabels`.

In turn, the string `tlabels` extracted above is converted into the
topic name `maintainer merge: tlabels` for the post to the
`maintainer merge` stream.

BASH_MODULE_DOCS

PR="${1}"

>&2 printf $'Using PR: \'%s\'\n' "${PR}"

tlabels="$(gh api --jq '.labels.[].name' "${PR}" | grep -- '^\(t-\|CI\|IMO\)' || printf 'generic\nlabel')"
# print to error, since the stdout is captured into `GITHUB_OUTPUT
>&2 printf 't-labels:\n---\n%s\n---\n' "${tlabels}"
# if there is exactly 1 `t-xxx`, `CI`, or `IMO` label, use `maintainer merge: t-xxx`
# if there isn't exactly 1 `t-xxx`, `CI`, or `IMO` label, use `maintainer merge`
if [[ "$(wc -l <<<"${tlabels}")" -ne 1 ]]; then
  topicName="maintainer merge"
else
  topicName="maintainer merge: ${tlabels}"
fi

>&2 printf $'Post to topic: \'%s\'\n' "${topicName}"
echo "topic=${topicName}"
