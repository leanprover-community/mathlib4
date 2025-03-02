#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean

echo '#all_declarations' >> "${script_file}"
cat "${script_file}"

getDeclarations () {
  # download the cache
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean
  lake build "${script_file}"
}

printf 'Save the declarations in the PR branch\n'

getDeclarations > decls_in_PR.txt
git checkout master...HEAD

printf 'Save the declarations in the master branch\n'
getDeclarations > decls_in_master.txt

printf 'Diff the declarations\n'
# diff the declarations
diff decls_in_PR.txt decls_in_master.txt
