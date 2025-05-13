#! /usr/bin/env bash

commitNumber="${1:-2}"
printf 'Commit number: %s\n' "${commitNumber}"
git ls-files 'Mathlib/*.lean' > currentListOfFiles.txt
previousHash="$(
  git log --pretty=oneline "-${commitNumber}" | tail -1 | awk '{print $1}'
)"
printf 'Previous hash: %s\n' "${previousHash}"
git checkout "${previousHash}"
git ls-files 'Mathlib/*.lean' > oldListOfFiles.txt

removedFiles="$(comm -13 <(sort currentListOfFiles.txt) <(sort oldListOfFiles.txt))"
printf 'Files only in the old repository:\n---\n%s\n---\n' "${removedFiles}"

git checkout --quiet -
