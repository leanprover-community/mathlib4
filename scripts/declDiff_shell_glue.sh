#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean

git checkout master
git checkout -

getDeclarations () {
  # download the cache
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean &&
  printf '#all_declarations "%s"\n' "${1}" >> "${script_file}"
  cat "${script_file}"

  lake env lean "${script_file}"
}

printf 'Save the declarations in the PR branch\n'

getDeclarations decls_in_PR.txt
git checkout master...HEAD

printf 'Save the declarations in the master branch\n'
getDeclarations decls_in_master.txt

printf 'Diff the declarations\n'
# diff the declarations
diff decls_in_PR.txt decls_in_master.txt
