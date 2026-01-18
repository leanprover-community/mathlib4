#!/bin/bash
 : << 'BASH_MODULE_DOCS'

Usage: ./scripts/find_labels.sh owner/repo YYYY-MM

The script summarizes PRs by label and author in the given year-month range in the input GitHub repository.

It assumes that
* the merged PRs have been `[Merged by Bors]`;
* `gh auth status` is set for the repo;
* `jq` is installed.

BASH_MODULE_DOCS

# Check if required arguments are provided
if [ "$#" -ne 2 ]; then
    printf $'Usage: %s <repo_owner/repo_name> <YYYY-MM>\n\n' "${0}"
    printf $'For instance `%s leanprover-community/mathlib4 %s`\n\n' "${0}" "$(date +%Y-%m)"
    exit 1
fi

rm -rf found_by_gh.txt found_by_git.txt

findInRange () {

repository="${1}"

# Get the start and end dates
startDate="${2}"
endDate="${3}"

# find how many commits to master there have been in the given range
commits_in_range="$(git log --since="${startDate}" --until="${endDate}" --pretty=oneline | wc -l)"

# Retrieve merged PRs from the given range
prs=$(gh pr list --repo "$repository" --state closed --base master --search "closed:${startDate}..${endDate}" --json number,labels,title,author --limit "$((commits_in_range * 2))")

## Print PR numbers, their labels and their title
#echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "PR #\(.number) - Labels: \((.labels | map(.name) | join(", ")) // "No labels") - Title: \(.title)"'

# Store to file `found_by_gh.txt` the PR numbers, as found by `gh`
echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "(#\(.number))"' | sort >> found_by_gh.txt

# Store to file `found_by_git.txt` the PR numbers, as found by looking at the commits to `master`
git log --pretty=oneline --since="${startDate}" --until="${endDate}" |
  sed -n 's=.*\((#[0-9]*)\)$=\1=p' | sort >> found_by_git.txt

echo "$prs"
}

# the current year and month
yr_mth="${2}" #"$(date +%Y-%m)"
yr_mth_day=${yr_mth}-01

start_date="${yr_mth_day}T00:00:00"
#end_date="$(date -d "${yr_mth_day} + 1 month - 1 day" +%Y-%m-%d)T23:59:59"
end_date="$(date -d "${yr_mth_day} + 2 weeks" +%Y-%m-%d)T23:59:59"

mth="$(date -d "${yr_mth_day}" '+%B')"
prev_mth="$(date -d "${yr_mth_day} - 1 day" '+%B')"
#next_mth="$(date -d "${yr_mth_day} + 1 month" '+%B')"
next_mth="$(date -d "${yr_mth_day} + 2 weeks" '+%B')"

commits_in_range="$(git log --since="${start_date}" --until="${end_date}" --pretty=oneline | wc -l)"

printf $'\n\nBetween %s and %s there were\n' "${yr_mth_day}" "${end_date/%T*}"

printf $'* %s commits to `master` and\n' "${commits_in_range}"

(
findInRange "${1}" "${start_date}" "${yr_mth}-15T23:59:59" | sed -z 's=]\n*$=,\n='
findInRange "${1}" "${yr_mth}-16T00:00:00" "${end_date}"   | sed -z 's=^\[=='
) | jq -S -r '.[] |
  select(.title | startswith("[Merged by Bors]")) |
  "\(.labels | map(.name | select(startswith("t-"))) ) PR #\(.number) \(if .author.name == "" then .author.login else .author.name end): \(.title)"' |
  sort |
  awk 'BEGIN{ labels=""; con=0; total=0 }
    { total++
      if(!($1 in seen)) { con++; order[con]=$1; seen[$1]=0 }
      seen[$1]++
      gsub(/\[Merged by Bors\] - /, "")
      rest=$2; for(i=3; i<=NF; i++){rest=rest" "$i};acc[$1]=acc[$1]"\n"rest }
    END {
      printf("* %s closed PRs\n", total)
      for(i=1; i<=con; i++) {
        tag=order[i]
        gsub(/\[\]/, "Miscellaneous", tag)
        gsub(/["\][]/, "", tag)
        gsub(/,/, " ", tag)
        noPR=seen[order[i]]
        printf("\n%s, %s PR%s%s\n", tag, noPR, noPR == "1" ? "" : "s", acc[order[i]])
      }
    }
  '

only_gh="$( comm -23 <(sort found_by_gh.txt) <(sort found_by_git.txt) | sed 's=^=  =' | tr -d '()')"
only_git="$(comm -13 <(sort found_by_gh.txt) <(sort found_by_git.txt) | sed 's=^=  =' | tr -d '()')"

printf $'\n---\nReports\n\n'

if [ -z "${only_gh}" ]
then
  printf $'* All PRs are accounted for!\n'
else
  printf $'* PRs not corresponding to a commit (merged in %s, closed in %s?)\n%s\n' "${prev_mth}" "${mth}" "${only_gh}"
fi

if [ -z "${only_git}" ]
then
  printf $'\n* All commits are accounted for!\n'
else
  printf $'\n* PRs not found by `gh` (merged in %s, closed in %s?)\n%s\n' "${mth}" "${next_mth}" "${only_git}"
fi

printf -- $'---\n'

rm -rf found_by_gh.txt found_by_git.txt
