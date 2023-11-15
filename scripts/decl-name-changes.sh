#!/bin/bash

if [ -z $1 ]; then
  SHA=$(git merge-base master HEAD)
else
  SHA=$1
fi

if [ -z "$(git status --untracked-files=no --porcelain)" ]; then
  # Uncommitted changes in tracked files
  echo "working directory clean, proceeding ..."
else
  # Working directory clean excluding untracked files
  echo "Your working directory is dirty, cannot checkout other commits."
  exit
fi

# list of files added, copied or modified in Mathlib/
NEW=$(git diff --name-status $SHA | awk '$1 ~ /^[ACM]/ && $2 ~ /^Mathlib\// {print $2}')
# list of files deleted or modified in Mathlib/
OLD=$(git diff --name-status $SHA | awk '$1 ~ /^[DM]/ && $2 ~ /^Mathlib\// {print $2}')
# list of renamed files in Mathlib/ using the original name
MV_OLD=$(git diff --name-status $SHA | awk '$1 ~ /^[R]/ && $2 ~ /^Mathlib\// {print $2}')
# list of renamed files in Mathlib/ using the updated name
MV_NEW=$(git diff --name-status $SHA | awk '$1 ~ /^[R]/ && $2 ~ /^Mathlib\// {print $3}')

# get the cache
lake exe cache get

# list all declarations in changed (new) files
lake exe declsIn $NEW $MV_NEW > declsNew.txt

# checkout the old commit
git checkout $SHA

# check whether the common ancestor has the script available
if ! test -f scripts/declsIn.lean; then
  echo "common ancestor is too old, please merge master"
  rm declsNew.txt
  git checkout -
  exit
fi

# get the cache
lake exe cache get

# list all declarations in changed (old) files
lake exe declsIn $OLD $MV_OLD > declsOld.txt

# return to start point
git checkout -

diff -u declsOld.txt declsNew.txt

rm declsOld.txt declsNew.txt
