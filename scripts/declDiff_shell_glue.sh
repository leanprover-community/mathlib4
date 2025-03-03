#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean

git checkout master
git checkout -

getDeclarations () {
  printf '* Download the cache\n'
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean &&

  printf $'* Save the declarations to \'%s\'\n' "${1}"
  printf '#all_declarations "%s"\n' "${1}" >> "${script_file}"
  #cat "${script_file}"

  lake env lean "${script_file}"
  # undo the local changes
  git restore .
}

getDeclarations decls_in_PR.txt
currentHash="$(git rev-parse HEAD)"
git checkout master...HEAD

git checkout "${currentHash}" "${script_file}"
getDeclarations decls_in_master.txt

printf 'Diff the declarations\n'

printf '```diff\n%s\n```\n' "$(diff decls_in_master.txt decls_in_PR.txt | grep "^[<>]")"
