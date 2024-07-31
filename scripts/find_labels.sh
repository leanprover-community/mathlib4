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

# Retrieve merged PRs from the last month
prs=$(gh pr list --repo "$repo_owner/$repo_name" --state merged --search "merged:>$one_month_ago" --json number,labels)

# Check if any PRs are found
if [ -z "$prs" ]; then
    echo "No merged pull requests found from the last month."
    exit 0
fi

# Print PR numbers and their labels
echo "$prs" | jq -r '.[] | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels")"'
