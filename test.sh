#!/bin/bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

movedFiles=$(git diff --name-only --diff-filter DR origin/master...HEAD)
if [ -n "$movedFiles" ]; then
    echo "info: found removed file(s) $movedFiles"
fi
echo $movedFiles > tetmp.txt

git checkout origin/master
for file in $movedFiles; do
  deprecation=$(grep ^deprecated_module $file)
  # echo $deprecation
  if [ -z $deprecation ]; then
    echo "error: file $file was removed without deprecation"
  else
    echo "removing $file was fine"
  fi
done

git checkout HEAD
git switch -
