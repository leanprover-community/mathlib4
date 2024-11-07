#!/usr/bin/env bash

BODY="${1}"
GHsource="${2}"

mergeOrDelegate="neither merge nor delegate"
if printf '%s\n' "${BODY}" | grep "^maintainer merge"
then
  mergeOrDelegate=merge
elif printf '%s\n' "${BODY}" | grep "^maintainer delegate"
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

printf 'title<<EOF\ntext merge or delegate: "%s", GHsource: "%s", GHevent: "%s"\nEOF' "${mergeOrDelegate}" "${GHsource}" "${GHevent}"
