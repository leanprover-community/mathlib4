#!/bin/bash

# Check if required arguments are provided
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <repo_owner> <repo_name>"
    exit 1
fi

repo_owner=$1
repo_name=$2

git switch master

# Get the start and end dates
start_date=$(date -d '15 days ago - 1 day' +%Y-%m-%d)
end_date=$(date -d 'today' +%Y-%m-%d)

# find how many commits to master there have been in the last month
commits_in_range="$(git log --since="${start_date}" --until="${end_date}" --pretty=oneline | wc -l)"

printf '%s commits between %s and %s\n' "${commits_in_range}" "${start_date}" "${end_date}"

# Retrieve merged PRs from the last month, paginated
prs=$(gh pr list --repo "$repo_owner/$repo_name" --state closed --closedAt "${start_date}T00:00:00..${end_date}T23:59:59" --json number,labels,title,closed --limit "$((commits_in_range * 2))")

# Print PR numbers and their labels
echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels") - Closed: \(.closed) - Title: \(.title)"'
