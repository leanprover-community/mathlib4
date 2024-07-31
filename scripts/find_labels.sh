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

page=1
per_page=100

while :; do
    # Retrieve merged PRs from the last month, paginated
    prs=$(gh pr list --repo "$repo_owner/$repo_name" --state merged --search "merged:>$one_month_ago" --json number,labels --limit "$per_page" --page "$page")

    # Check if any PRs are found
    if [ -z "$prs" ] || [ "$prs" = "[]" ]; then
        break
    fi

    # Print PR numbers and their labels
    echo "$prs" | jq -r '.[] | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels")"'

    page=$((page + 1))
done
