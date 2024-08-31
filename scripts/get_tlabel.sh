#!/usr/bin/env bash

tlabels="$(gh api --jq '.labels.[].name' "${PR}" | grep -- '^t-' || printf 'generic')"
>&2 printf 't-labels:\n---\n%s\n---\n' "${tlabels}"
if [[ "$(wc -l <<<"${tlabels}")" -ne 1 ]]; then
  tlabels="generic"
fi
>&2 printf 'echo "name=%s with a master-addition"\n' "${tlabels}"
echo "name=${tlabels} with a master-addition"
