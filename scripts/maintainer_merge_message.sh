#!/usr/bin/env bash

AUTHOR="${1}"
BODY="${2}"
GHsource="${3}"
PR="${4}"
URL="${5}"
PR_TITLE="${6}"

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
