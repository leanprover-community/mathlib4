#!/bin/bash

# Check if required arguments are provided
if [ "$#" -ne 1 ]; then
    printf $'Usage: %s <repo_owner/repo_name>\n\nFor instance `%s leanprover-community/mathlib4`\n\n' "${0}" "${0}"
    exit 1
fi

repository=$1

git switch master

# Get the start and end dates
start_date="$(date -d '15 days ago - 1 day' +%Y-%m-%d)T00:00:00"
end_date="$(date -d 'today' +%Y-%m-%d)T23:59:59"

# find how many commits to master there have been in the last month
commits_in_range="$(git log --since="${start_date}" --until="${end_date}" --pretty=oneline | wc -l)"

printf '%s commits between %s and %s\n' "${commits_in_range}" "${start_date}" "${end_date}"

# Retrieve merged PRs from the last month, paginated
prs=$(gh pr list --repo "$repository" --state closed --base master --search "closed:${start_date}..${end_date}" --json number,labels,title --limit "$((commits_in_range * 2))")

# Print PR numbers and their labels
prs_to_print="$(echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels") - Title: \(.title)"')"

echo "${prs_to_print}"

only_gh="$(comm -23 <(echo "${prs_to_print}" | awk '{print $2}' | sort) <(git log --pretty=oneline --since="${start_date}" --until="${end_date}" | sed -n 's=.*(\(#[0-9]*\))$=\1=p' | sort))"

only_git="$(comm -13 <(echo "${prs_to_print}" | awk '{print $2}' | sort) <(git log --pretty=oneline --since="${start_date}" --until="${end_date}" | sed -n 's=.*(\(#[0-9]*\))$=\1=p' | sort))"

printf $'\n\nReports\n\n---\n'

if [ -z "${only_gh}" ]
then
  printf $'\nAll PRs are accounted for!\n'
else
  printf $'\nPRs not corresponding to a commit\n\n\'%s\'\n' "${only_gh}"
fi

if [ -z "${only_git}" ]
then
  printf $'\nAll commits are accounted for!\n'
else
  printf $'PRs not found by `gh`\n\n\'%s\'\n' "${only_git}"
fi

printf $'\n---\n'
