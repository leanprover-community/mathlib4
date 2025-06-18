#!/usr/bin/env bash

# Running `./formatGhPrList.sh <linkifier>` produces an .md-formatted table
# of all the issues in the current repository.
# Assuming that `<linkifier>#NNN` is a valid Zulip linkifier, the PRs will be clickable links.

repo="${1:-linkifier}"

gh pr list |
  awk -F$'\t' -v link="${repo}#" 'BEGIN{
    OFS="|"
    print "", " ID ", " TITLE ", " DATE ", " STATUS ", ""
    print "", " - ", " - ", " - ", " - ", ""
  }
    #(NR == 1){link=""}
    #(!(NR == 1)){link=lk}
    # skip the 3rd field, containing the branch name
    {
      date=$5
      gsub(/T.*/, "", date)
      print "", link $1, $2, date, $4, ""
    }'
