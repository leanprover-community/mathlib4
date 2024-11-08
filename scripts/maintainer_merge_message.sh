#!/usr/bin/env bash

AUTHOR="${1}"   # adomani
BODY="${2}"     # message content, containing `maintainer {merge, delegate}`
GHsource="${3}" # one of `comment`, `review` or `review comment`
PR="${4}"       # the number of the PR
URL="${5}"      # the url link to the PR
PR_TITLE="${6}" # the title of the PR

mergeOrDelegate="neither merge nor delegate"
if printf '%s\n' "${BODY}" | grep -q "^maintainer merge"
then
  mergeOrDelegate=merge
elif printf '%s\n' "${BODY}" | grep -q "^maintainer delegate"
then
  mergeOrDelegate=delegate
fi

GHevent=nothing
if [ "${GHsource}" == "comment" ]
then
  GHevent=issue
elif [ "${GHsource/% */}" == "review" ]
then
  GHevent=pull_request
fi

#printf $'title<<EOF\n${{ format(\'{0} requested a maintainer %s from %s on PR [#{1}]({2}):\', github.event.%s.user.login, github.event.%s.number, github.event.%s.html_url ) }}\nEOF' "${mergeOrDelegate}" "${GHsource}" "${GHsource}" "${GHevent}" "${GHevent}"

printf '%s requested a maintainer %s from %s on PR [#%s](%s):\n' "${AUTHOR}" "${mergeOrDelegate}" "${GHsource}" "${PR}" "${URL}"
printf '> %s\n' "${PR_TITLE}"
