#!/bin/bash

while getopts :ho: flag
do
    case "${flag}" in
        h) HELP=true;;
        o) OUTFILE=${OPTARG};;
    esac
done

usage () {
  echo -e "A tool to find which declarations have been added or removed.
It will compare HEAD to the provided COMMIT, or, if no commit is provided,
it compares against the most recent common ancestor of HEAD and master.

USAGE:
\tdecl-name-changes.sh [OPTIONS] [COMMIT]

OPTIONS:
\t-h\tprint this help message
\t-o\tspecify an output file for the diff

Warning: Early termination of this script may result in a *detached head*
state. You can return to your original place with 'git switch -'.

If the calls to 'lake exe cache get' fail, or otherwise the oleans on disk
do not match, this script will fail to behave as expected."
}

if [ "$HELP" = true ]; then
  usage
  exit
fi

shift $(($OPTIND - 1))

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

if [ -z $OUTFILE ]; then
  diff -u declsOld.txt declsNew.txt
else
  diff -u declsOld.txt declsNew.txt | awk '/^[+-]/' > $OUTFILE
fi

rm declsOld.txt declsNew.txt
