#!/bin/bash

# Check if required arguments are provided
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <repo_owner> <repo_name>"
    exit 1
fi

repo_owner=$1
repo_name=$2

# Get the date for one month ago
one_month_ago=$(date -d '1 month ago' +%Y-%m-%d)

printf 'Dates after %s\n' "${one_month_ago}"

git switch master

# find how many commits to master there have been in the last month
last_month_commits="$(git log --since="$one_month_ago" --pretty=oneline | wc -l)"

# Retrieve merged PRs from the last month, paginated
prs=$(gh pr list --repo "$repo_owner/$repo_name" --state closed --search "closed:>$one_month_ago" --json number,labels,title --limit "$last_month_commits")

# Check if any PRs are found
if [ -z "$prs" ] || [ "$prs" = "[]" ]; then
    break
fi

# Print PR numbers and their labels
echo "$prs" | jq -r '.[] | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels") - Title: \(.title)"'
