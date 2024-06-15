#!/usr/bin/env bash

#!/usr/bin/env bash

# Fetch all pull requests and write them to prs.json
gh api --paginate "repos/leanprover-community/mathlib4/pulls?state=all" > prs.json

# Fetch all issues and write them to issues.json
gh api --paginate "repos/leanprover-community/mathlib4/issues?state=all" > issues.json

# Start a new JSON file for the activity
echo "[" > activity.json

# Extract pull request numbers and fetch their activity
prs=$(jq -r ".[] | .number" prs.json)
for pr in $prs; do
  gh api --paginate "repos/leanprover-community/mathlib4/pulls/$pr/comments" \
     | jq -c '.[]' >> activity.json
done

# Extract issue numbers and fetch their activity
issues=$(jq -r ".[] | .number" issues.json)
for issue in $issues; do
  gh api --paginate "repos/leanprover-community/mathlib4/issues/$issue/events" \
     | jq -c '.[]' >> activity.json
done

# End the array in the JSON file
echo "]" >> activity.json


# # Create a new JSON file and start an array
# echo "[" > activity.json

# # Get all pull requests updated in the past 4 weeks
# response=$(gh api --paginate repos/leanprover-community/mathlib4/pulls\?state=all)

# # Extract pull request numbers
# prs=$(echo "$response" | jq ".[] | select(.updated_at > \"$(date -d '4 weeks ago' --iso-8601=seconds)\") | .number" | jq -r @sh)

# echo "Pull request numbers: $prs"

# # For each pull request, get all activity from the past 4 weeks
# for pr in $prs; do

#   # Remove quotes around the PR number
#   pr=${pr//\"/}

#   echo "Processing pull request number: $pr"

#   # # Get comments
#   # gh api repos/leanprover-community/mathlib4/issues/$pr/comments --paginate \
#   #    | jq -c '.[]' >> activity.json

#   # # Get labels
#   # gh api repos/leanprover-community/mathlib4/issues/$pr/labels --paginate \
#   #    | jq -c '.[]' >> activity.json

#   # # Get timeline events (includes various types of activity)
#   # gh api repos/leanprover-community/mathlib4/issues/$pr/timeline --paginate \
#   #    --header "Accept: application/vnd.github.mockingbird-preview" | jq -c '.[]' >> activity.json

# done

# # End the array in the JSON file
# echo "]" >> activity.json
