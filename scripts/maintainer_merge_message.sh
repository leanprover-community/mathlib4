#!/usr/bin/env bash

AUTHOR="${1:-AUTHOR not set}"         # the author of the review
M_or_D="${2:-M_or_D not set}"         # `merge` or `delegate`
EVENT_NAME="${3:-EVENT_NAME not set}" # one of `issue_comment`, `pull_request_review` or `pull_request_review_comment`
                                      # to be converted to `comment`, `review` or `review comment`
PR="${4:-PR not set}"                 # the number of the PR
URL="${5:-URL not set}"               # the url link to the PR
PR_TITLE="${6:-PR_TITLE not set}"     # the title of the PR
PR_COMMENT="${7:-PR_COMMENT not set}" # the comment that triggered the `maintainer merge` action
PR_AUTHOR="${8:-PR AUTHOR not set}"   # the author of the PR

# figure out if the GitHub event starting this action is a comment, a review or a review comment
# and set the `SOURCE` variable accordingly
case ${EVENT_NAME} in
  issue_comment)
  SOURCE='comment'
  ;;
  pull_request_review)
  SOURCE='review'
  ;;
  pull_request_review_comment)
  SOURCE='review comment'
  ;;
  *)
  SOURCE='unknown origin'
  ;;
esac

# for debugging, we print the available variables to stderr
>&2 echo "PR_TITLE:   '${PR_TITLE}'"
>&2 echo "AUTHOR:     '${AUTHOR}'"
>&2 echo "M_or_D:     '${M_or_D}'"
>&2 echo "PR_NUMBER:  '${PR_NUMBER}'"
>&2 echo "PR_URL:     '${PR_URL}'"
>&2 echo "title:      '${PR_TITLE}'"
>&2 echo "EVENT_NAME: '${EVENT_NAME}'"
>&2 printf 'COMMENT\n%s\nEND COMMENT\n' "${PR_COMMENT}"

printf '%s requested a maintainer **%s** from %s on PR [#%s](%s) by %s:\n' "${AUTHOR}" "${M_or_D/$'?'/}" "${SOURCE}" "${PR}" "${URL}" "${PR_AUTHOR}"
# if `maintainer merge/delegate` is followed by `?`, then print a `spoiler` with the full comment
if [ ${M_or_D: -1} == $'?' ]
then
  # replace backticks in the title with single quotes
  unbacktickedTitle="${PR_TITLE//\`/\'}"

  >&2 echo "neat title: '${unbacktickedTitle}'"

  printf '```spoiler %s\n%s\n```\n' "${unbacktickedTitle}" "${PR_COMMENT}"
# otherwise, just print the title of the PR
else
  printf '> %s\n' "${PR_TITLE}"
fi
