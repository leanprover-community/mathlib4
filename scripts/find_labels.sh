#!/bin/bash

# Check if required arguments are provided
if [ "$#" -ne 1 ]; then
    printf $'Usage: %s <repo_owner/repo_name>\n\nFor instance `%s leanprover-community/mathlib4`\n\n' "${0}" "${0}"
    exit 1
fi

git switch master

rm -rf found_by_gh.txt found_by_git.txt

findInRange () {

repository="${1}"

# Get the start and end dates
start_date="${2}"
end_date="${3}"

# find how many commits to master there have been in the last month
commits_in_range="$(git log --since="${start_date}" --until="${end_date}" --pretty=oneline | wc -l)"

# Retrieve merged PRs from the given range
prs=$(gh pr list --repo "$repository" --state closed --base master --search "closed:${start_date}..${end_date}" --json number,labels,title --limit "$((commits_in_range * 2))")

# Print PR numbers, their labels and their title
echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels") - Title: \(.title)"'

# Store to file `found_by_gh.txt` the PR numbers, as found by `gh`
echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "(#\(.number))"' | sort >> found_by_gh.txt

# Store to file `found_by_git.txt` the PR numbers, as found by looking at the commits to `master`
git log --pretty=oneline --since="${start_date}" --until="${end_date}" |
  sed -n 's=.*\((#[0-9]*)\)$=\1=p' | sort >> found_by_git.txt
}

commits_in_range="$(git log --since=2024-07-01T00:00:00 --until="$(date -d '2024-07-01 + 1 month - 1 day' +%Y-%m-%d)T23:59:59" --pretty=oneline | wc -l)"

findInRange "${1}" '2024-07-01T00:00:00' '2024-07-15T23:59:59'
findInRange "${1}" '2024-07-16T00:00:00' "$(date -d '2024-07-01 + 1 month - 1 day' +%Y-%m-%d)T23:59:59"

only_gh="$( comm -23 <(sort found_by_gh.txt) <(sort found_by_git.txt))"
only_git="$(comm -13 <(sort found_by_gh.txt) <(sort found_by_git.txt))"

printf $'\n---\nReports\n\n'

if [ -z "${only_gh}" ]
then
  printf $'\n* All PRs are accounted for!\n'
else
  printf $'\n* PRs not corresponding to a commit\n\n\'%s\'\n' "${only_gh}"
fi

if [ -z "${only_git}" ]
then
  printf $'\n* All commits are accounted for!\n'
else
  printf $'* PRs not found by `gh`\n\n\'%s\'\n' "${only_git}"
fi

printf $'\n---\n'

rm -rf found_by_gh.txt found_by_git.txt

git checkout -
