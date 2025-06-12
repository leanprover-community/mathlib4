#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

 : <<BASH_DOC_MODULE
This script takes care of maintaining and updating the first message that starts with a given string in a PR.
It takes 3 inputs:

1. the path of a file containing the new message;
2. the beginning of the message, to identify whether to create a new or update an existing message;
3. the PR number.
BASH_DOC_MODULE

# If the first two arguments are missing, use the empty string as default value.

# the file containing the text of the message that will replace the current one
messageFile="${1:-}"
# the start of the message to locate it among all messages in the PR
comment_init="${2:-}"
# But we do complain if the PR number is missing.
PR="${3:-}"
if [[ -z $PR ]]; then
  printf $'Please enter a valid PR number.\nUsage: <new_message_file> <beginning_of_old_message> <pr_number>'
  exit 1
fi

baseURL="https://api.github.com/repos/${GITHUB_REPOSITORY}/issues"
printf 'Base url: %s\n' "${baseURL}"
method="POST"
if [[ -f "$messageFile" ]]; then
    url="${baseURL}/${PR}/comments"
    printf 'Base url: %s\n' "${url}"
    headers="Authorization: token ${GH_TOKEN}"
    comment_id=$(curl -s -S -H "Content-Type: application/json" -H "$headers" "$url" |
      jq --arg cID "${comment_init}" -r '.[] | select(.body | startswith($cID)) | .id' | head -1)
    echo "Comment id: '${comment_id}'"
    if [[ -n "$comment_id" ]]; then
        url="${baseURL}/comments/${comment_id}"
        method="PATCH"
    fi
    jq -Rs -n -c '{"body": inputs}' "${messageFile}" > "${messageFile}.json"
    curl -s -S -H "Content-Type: application/json" -H "$headers" -X "$method" -d @"${messageFile}.json" "$url"
fi
