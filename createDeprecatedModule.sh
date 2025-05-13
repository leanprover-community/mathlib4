#! /usr/bin/env bash

# How many commits back we scan.
# The default is `2`, which means the commit before the current one.
commitNumber="${1:-2}"

# With input a natural number `n`, retrieves the hash of `n` commits ago, where `n = 1` is
# the current commit.
getHash () {
  git log --pretty=oneline "-${1}" | tail -1 | awk '{print $1}'
}

currentHash="$(getHash 1)"
previousHash="$(getHash "${commitNumber}")"

printf 'Current hash: %s\n' "${currentHash}"
printf 'Commit number: %s\n' "${commitNumber}"
printf 'Previous hash: %s\n' "${previousHash}"

# `getAllFiles <hash>` lists and sorts all files in `Mathlib/` at the given commit hash.
# In particular, files in `MathlibTest`, `Archive`, `scripts`,... are exempt from this check.
getAllFiles () {
  git ls-tree -r --name-only "${1}" Mathlib/ | sort
}

# We store the list of files in the current repository in `currentListOfFiles.txt`.
getAllFiles "${currentHash}" > currentListOfFiles.txt

# We store the list of files in the previous repository in `oldListOfFiles.txt`.
getAllFiles "${previousHash}" > oldListOfFiles.txt

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
  printf 'Regenerating %s (from %s)\n' "${file}" "${previousHash}"
  git checkout "${previousHash}" "${file}"
done
