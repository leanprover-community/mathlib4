#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean
PRdeclsFile=${1:-decls_in_PR.txt}
MSdeclsFile=${2:-decls_in_master.txt}

git checkout master
git checkout -

# Running `getDeclarations <file_name> <sep_string>`
# 1. downloads the cache for `Mathlib`, `Archive` and `Counterexamples`;
# 2. adds the line `#all_declarations <file_name>` to the declarations diff Lean script;
# 3. builds the declarations diff script, which in turn
# 4. saves to `<file_name>` all the declarations in the environment;
# 5. removes the line added to the declarations diff Lean script;
# 6. uses `<sep_string>` to signal when the text that the report should use starts.
getDeclarations () {
  printf '* Download the cache\n'
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean

  printf $'* Save the declarations to \'%s\'\n' "${1}"
  #printf $'#all_declarations "%s"\n' "${1}" >> "${script_file}"

  cp "${script_file}" Mathlib/declarations_diff_lean.lean
  printf $'def %s\' := 0\n#all_declarations "%s"\n' "${1}" "${1}" >> Mathlib/declarations_diff_lean.lean
  lake build Mathlib.declarations_diff_lean

  # undo the local changes
  rm -f Mathlib/declarations_diff_lean.lean
}

getDeclarations "${PRdeclsFile}"
PRhash="$(git rev-parse HEAD)"
git checkout master...HEAD

git checkout "${PRhash}" "${script_file}"
getDeclarations "${MSdeclsFile}"

# switch back to the PR branch
git checkout "${PRhash}"

printf 'Diff the declarations\n'

actualDiff="$(diff decls_in_master.txt "${PRdeclsFile}" | grep '^[<>]')"

printf '%s\n' "${actualDiff}"
