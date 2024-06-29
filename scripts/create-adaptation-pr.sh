#!/usr/bin/env bash

if [ $# -ne 2 ]; then
  echo "Usage: $0 <BUMPVERSION> <NIGHTLYDATE>"
  echo "BUMPVERSION: The upcoming release that we are targetting, e.g., 'v4.10.0'"
  echo "NIGHTLYDATE: The date of the nightly toolchain currently used on 'nightly-testing'"
  exit 1
fi

BUMPVERSION=$1 # "v4.10.0"
NIGHTLYDATE=$2 # "2024-06-25"


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
echo "> gh pr create -l awaiting-review -l awaiting-CI -B bump/$BUMPVERSION"
echo "Post the link to the PR in the #nightly-testing channel on Zulip: '#xyz adaptations for nightly-$NIGHTLYDATE'"

read -p "Press enter to continue"

git checkout nightly-testing
git merge "bump/nightly-$NIGHTLYDATE"

echo "Please check if there are any conflicts and resolve them"
echo "Open '`pwd`' in a new terminal and run 'git status'"
read -p "Press enter to continue"

git push
