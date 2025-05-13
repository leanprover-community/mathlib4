#! /usr/bin/env bash

# How many commits back we scan.#
# The default is `2`, which means the commit before the current one.
commitNumber="${1:-2}"

# Retrieves the hash of the commit corresponding to `commitNumber`.
previousHash="$(
  git log --pretty=oneline "-${commitNumber}" | tail -1 | awk '{print $1}'
)"

printf 'Commit number: %s\n' "${commitNumber}"
printf 'Previous hash: %s\n' "${previousHash}"

# Lists and sorts all `.lean` files in `Mathlib/`.
# In particular, files in `MathlibTest`, `Archive`, `scripts`,... are exempt from this check.
getAllFiles () {
  git ls-files 'Mathlib/*.lean' | sort
}

# We are on master and we store the current list of files in `currentListOfFiles.txt`.
getAllFiles > currentListOfFiles.txt

git checkout "${previousHash}"
# We are now on the earlier commit and we store the list of old files in `oldListOfFiles.txt`.
getAllFiles > oldListOfFiles.txt
# Go back to master.
git checkout --quiet -

# `removedFiles` are the files that are present in `oldListOfFiles.txt`,
# but not in `currentListOfFiles.txt`.
# The lean counterpart of this script, `scripts/create_deprecated_module.lean`,
# recomputes this list anyway.
removedFiles="$(comm -13 currentListOfFiles.txt oldListOfFiles.txt)"
printf 'Files only in the old repository:\n---\n%s\n---\n' "${removedFiles}"

# For each file that only exists in the past repository, checkout the file again.
IFS=$'\n'
for file in ${removedFiles}
do
  printf 'git checkout %s %s\n' "${previousHash}" "${file}"
  #git checkout "${previousHash}" "${file}"
done
