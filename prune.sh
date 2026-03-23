#!/bin/bash

# Fetch the latest state of remote branches and prune deleted branches
git fetch --prune

# Get the current date minus 30 days
THRESHOLD_DATE=$(date -d '200 days ago' +%s)

# Loop through remote branches
for branch in $(git branch -r | grep -v '\->'); do
    # Get the last commit date of the branch
    LAST_COMMIT_DATE=$(git log -1 --format=%ct "${branch#origin/}")

    # Check if the branch is older than the threshold
    if [[ $LAST_COMMIT_DATE -lt $THRESHOLD_DATE ]]; then
           # Delete the remote branch if it's older than 30 days
             echo "Deleting branch: ${branch#origin/}"  # Inform about the deletion
         git push origin --delete "${branch#origin/}" --  # Delete the branch
  fi
done
