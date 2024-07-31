#!/usr/bin/env bash

 : <<BASH_DOC_MODULE
This script takes care of maintaining and updating the first message that starts with a given string in a PR.
It takes 3 inputs:

1. the new message;
2. the beginning of the message, to identify whether to create a new or update an existing message;
3. the PR number.
BASH_DOC_MODULE

  # the text of the message that will replace the current one
  message="${1}"
  # the start of the message to locate it among all messages in the PR
  comment_init="${2}"
  # the PR number
  PR="${3}"

  data=$(jq -n --arg msg "$message" '{"body": $msg}')
  baseURL="https://api.github.com/repos/${GITHUB_REPOSITORY}/issues"
  printf 'Base url: %s\n' "${baseURL}"
  method="POST"
  if [[ -n "$message" ]]; then
      url="${baseURL}/${PR}/comments"
      printf 'Base url: %s\n' "${url}"
      headers="Authorization: token ${GITHUB_TOKEN}"
      comment_id=$(curl -s -S -H "Content-Type: application/json" -H "$headers" "$url" |
        jq --arg cID "${comment_init}" -r '.[] | select(.body | startswith($cID)) | .id' | head -1)
      echo "Comment id: '${comment_id}'"
      if [[ -n "$comment_id" ]]; then
          url="${baseURL}/comments/${comment_id}"
          method="PATCH"
      fi
      curl -s -S -H "Content-Type: application/json" -H "$headers" -X "$method" -d "$data" "$url"
  fi
