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

# Check the CI status of the latest commit on the 'nightly-testing' branch
status=$(gh api repos/leanprover-community/mathlib4/commits/nightly-testing/status | jq -r '.state')
if [ "$status" != "success" ]; then
  echo "The latest commit on the 'nightly-testing' branch did not pass CI. Please fix the issues and try again."
  exit 1
fi

git checkout master
git pull
git checkout "bump/$BUMPVERSION"
git pull
git merge origin/master


echo "Please check if there are any conflicts and resolve them"
echo "Open '`pwd`' in a new terminal and run 'git status'"
read -p "Press enter to continue"

git push


git checkout -b "bump/nightly-$NIGHTLYDATE"
git merge --squash origin/nightly-testing


echo "Please check if there are any conflicts and resolve them"
echo "Open '`pwd`' in a new terminal and run 'git status'"
read -p "Press enter to continue"

git commit -m "chore: adaptations for nightly-$NIGHTLYDATE"
git push --set-upstream origin "bump/nightly-$NIGHTLYDATE"


echo "Create a pull request, label with 'awaiting-review' and 'awaiting-CI'"
echo "Set the base of the PR to 'bump/$BUMPVERSION'"
echo "Here is a suggested 'gh' command to do this:"
gh_command="gh pr create -l awaiting-review -l awaiting-CI -B bump/$BUMPVERSION"

# Noninteractive version:
# gh_command="gh pr create -t 'Title of the PR' -b 'Body of the PR' -l awaiting-review -l awaiting-CI -B bump/$BUMPVERSION"

echo "> $gh_command"
echo "Are you happy with this command? (y/n)"
read answer
if [ "$answer" != "${answer#[Yy]}" ]; then
    eval $gh_command
fi

echo "Post the link to the PR in the #nightly-testing channel on Zulip: '#xyz adaptations for nightly-$NIGHTLYDATE'"

read -p "Press enter to continue"

git checkout nightly-testing
git merge "bump/nightly-$NIGHTLYDATE"

echo "Please check if there are any conflicts and resolve them"
echo "Open '`pwd`' in a new terminal and run 'git status'"
read -p "Press enter to continue"

git push
