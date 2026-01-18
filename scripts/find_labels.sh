#!/bin/bash
 : << 'BASH_MODULE_DOCS'

Usage: ./scripts/find_labels.sh owner/repo startDate endDate

The script summarizes PRs by label and author in the given year-month range in the input GitHub repository.

It assumes that
* the merged PRs have been `[Merged by Bors]`;
* `gh auth status` is set for the repo;
* `jq` is installed.

BASH_MODULE_DOCS

# Check if required arguments are provided
if [ "$#" -ne 3 ]; then
    printf $'Usage: %s <repo_owner/repo_name> <startDate[YYYY-MM-DD]> <endDate[YYYY-MM-DD]>\n\n' "${0}"
    printf $'For instance `%s leanprover-community/mathlib4 %s %s`\n\n' "${0}" "$(date -d "today - 2 weeks" +%Y-%m-%d)" "$(date -d "today" +%Y-%m-%d)"
    printf $'The dates can also include time signatures, as in %s\n' "$(date -d '+1 hour' '+%FT%T')"
    exit 1
fi

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

commits_in_range="$(git log --since="${startDate}" --until="${endDate}" --pretty=oneline | wc -l)"

printf $'\n\nBetween %s and %s there were\n' "${startDate}" "${endDate/%T*}"

printf $'* %s commits to `master` and\n' "${commits_in_range}"

formattedPRs="$(echo "$prs" |
  jq -S -r '.[] |
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
  ')"

formatForGitHub () {
  echo "${1}" |
    sed '
      / [0-9]* PRs$/{
        s=^=</details><details><summary>\n=
        s=$=\n</summary>\n=
      }
      s=^PR \(#[0-9]* [^:]*\): .*=* \1 =' |
    sed -z '
      s=</details><details><summary>=<details><summary>=
      s=\n---\nReports\n\n=\n</details>\n\n---\n\n<details><summary>Reports</summary>\n\n=
      s=\n---[\n]*$=\n\n</details>\n&=
    '
}

formatForZulip () {
  echo "${1}" |
  sed '
  / [0-9]* PR[s]*$/{
    s=^=```\n\n```spoiler =
    }' |
    sed -z '
    s=\n```\n=\n=
    s=\n\n```\n=\n```\n=g
    s=\n$=\n```\n=
    '
}

formatForZulip "${formattedPRs}"

# Store to variable `found_by_gh` the PR numbers, as found by `gh`
found_by_gh="$(
  echo "$prs" | jq -r '.[] | select(.title | startswith("[Merged by Bors]")) | "(#\(.number))"' | sort -u
)"

# Store to variable `found_by_git` the PR numbers, as found by looking at the commits to `master`
found_by_git="$(
  git log --pretty=oneline --since="${startDate}" --until="${endDate}" |
    sed -n 's=.*\((#[0-9]*)\)$=\1=p' | sort -u
)"

only_gh="$(
  comm -23 <(printf $'%s\n' "${found_by_gh}") <(printf $'%s\n' "${found_by_git}") |
    sed 's=^=  =' | tr -d '()'
)"

only_git="$(
  comm -13 <(printf $'%s\n' "${found_by_gh}") <(printf $'%s\n' "${found_by_git}") |
    sed 's=^=  =' | tr -d '()'
)"

printf $'\n```spoiler Reports\n\n'

if [ -z "${only_gh}" ]
then
  printf $'* All PRs are accounted for!\n'
else
  printf $'* PRs not corresponding to a commit (merged before %s, closed on %s?)\n%s\n' "${startDate}" "${startDate}" "${only_gh}"
fi

if [ -z "${only_git}" ]
then
  printf $'\n* All commits are accounted for!\n'
else
  printf $'\n* PRs not found by `gh` (merged by %s, closed after %s?)\n%s\n' "${endDate}" "${endDate}" "${only_git}"
fi

printf -- $'```\n'
