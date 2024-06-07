#!/usr/bin/env bash

  # the text of the message that will replace the current one
  message="${1}" #=$(python ./scripts/import-graph-report.py base.json head.json changed_files.txt)
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
        jq -r '.[] | select(.body | startswith('\"${comment_init}\"')) | .id' | head -1)
      echo "Comment id: '${comment_id}'"
      if [[ -n "$comment_id" ]]; then
          url="${baseURL}/comments/${comment_id}"
          method="PATCH"
      fi
      curl -s -S -H "Content-Type: application/json" -H "$headers" -X "$method" -d "$data" "$url"
  fi
