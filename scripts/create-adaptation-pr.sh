#!/usr/bin/env bash

if [ $# -ne 2 ]; then
  echo "Usage: $0 <BUMPVERSION> <NIGHTLYDATE>"
  echo "BUMPVERSION: The upcoming release that we are targetting, e.g., 'v4.10.0'"
  echo "NIGHTLYDATE: The date of the nightly toolchain currently used on 'nightly-testing'"
  exit 1
fi

BUMPVERSION=$1 # "v4.10.0"
NIGHTLYDATE=$2 # "2024-06-25"

# Check if 'gh' command is available
if ! command -v gh &> /dev/null; then
    echo "'gh' (GitHub CLI) is not installed. Please install it and try again."
    exit 1
fi

# # Check the CI status of the latest commit on the 'nightly-testing' branch
# status=$(gh api repos/leanprover-community/mathlib4/commits/nightly-testing/status | jq -r '.state')
# if [ "$status" != "success" ]; then
#   echo "The latest commit on the 'nightly-testing' branch did not pass CI. Please fix the issues and try again."
#   exit 1
# fi

echo "### Creating a PR for the nightly adaptation for $NIGHTLYDATE"
echo "### [auto] checkout master and pull the latest changes"

git checkout master
git pull

echo
echo "### [auto] checkout 'bump/$BUMPVERSION' and merge the latest changes from 'origin/master'"

git checkout "bump/$BUMPVERSION"
git pull
git merge origin/master

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo "### [user] Conflict resolution"
  echo "There seem to be conflicts: please resolve them"
  echo "Open `pwd` in a new terminal and run 'git status'"
  echo "Make sure to commit the resolved conflicts, but do not push them"
  read -p "Press enter to continue, when you are done"
fi

git push

echo
echo "### [auto] create a new branch 'bump/nightly-$NIGHTLYDATE' and merge the latest changes from 'origin/nightly-testing'"

git checkout -b "bump/nightly-$NIGHTLYDATE"
git merge --squash origin/nightly-testing

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo "### [user] Conflict resolution"
  echo "There seem to be conflicts: please resolve them"
  echo "Open `pwd` in a new terminal and run 'git status'"
  echo "Run 'git add' on the resolved files, but do not commit"
  read -p "Press enter to continue, when you are done"
fi

echo
echo "### [auto] commit the changes and push the branch"

pr_title="chore: adaptations for nightly-$NIGHTLYDATE"
git commit -m "$pr_title"
git push --set-upstream origin "bump/nightly-$NIGHTLYDATE"

echo
echo "### [auto/user] create a PR for the new branch"
echo "Create a pull request, label with 'awaiting-review' and 'awaiting-CI'"
echo "Set the base of the PR to 'bump/$BUMPVERSION'"
echo "Here is a suggested 'gh' command to do this:"
gh_command="gh pr create -t \"$pr_title\" -b '' -l awaiting-review -l awaiting-CI -B bump/$BUMPVERSION"
echo "> $gh_command"
echo "Shall I run this command for you? (y/n)"
read answer
if [ "$answer" != "${answer#[Yy]}" ]; then
    gh_output=$(eval $gh_command)
    pr_number=$(echo $gh_output | grep -oP 'github.com/[^/]+/[^/]+/pull/\K\d+')
fi

echo
echo "### [user] post a link to the PR on Zulip"

zulip_title="#$pr_number adaptations for nightly-$NIGHTLYDATE"
zulip_body="> $pr_title #$pr_number"

echo "Post the link to the PR in a new thread on the #nightly-testing channel on Zulip"
echo "Here is a suggested message:"
echo "Title: $zulip_title"
echo " Body: $zulip_body"
read -p "Press enter to continue"

echo
echo "### [auto] checkout the 'nightly-testing' branch and merge the new PR into it"

git checkout nightly-testing
git pull
git merge "bump/nightly-$NIGHTLYDATE"

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo "### [user] Conflict resolution"
  echo "There seem to be conflicts: please resolve them"
  echo "Open `pwd` in a new terminal and run 'git status'"
  echo "Make sure to commit the resolved conflicts, but do not push them"
  read -p "Press enter to continue, when you are done"
fi

git push
