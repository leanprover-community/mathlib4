#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean

git checkout master
git checkout -

# Running `getDeclarations <file_name>`
# 1. downloads the cache for `Mathlib`, `Archive` and `Counterexamples`;
# 2. adds the line `#all_declarations <file_name>` to the declarations diff Lean script;
# 3. builds the declarations diff script, which in turn
# 4. saves to `<file_name>` all the declarations in the environment;
# 5. removes the line added to the declarations diff Lean script.
getDeclarations () {
  printf '* Download the cache\n'
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean &&

  printf $'* Save the declarations to \'%s\'\n' "${1}"
  printf $'def %s\' := 0\n#all_declarations "%s"\n' "${1}" "${1}" >> "${script_file}"
  #printf $'#all_declarations "%s"\n' "${1}" >> "${script_file}"

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

actualDiff="$(diff decls_in_master.txt decls_in_PR.txt | grep '^[<>]')"
echo "${actualDiff}"

printf '%s\n' "${actualDiff}"

printf $'LeanDiff<<EOF\n%q\nEOF' "${actualDiff}" |
  # show result in stdout and also store it in `GITHUB_OUTPUT`
  tee >(cat) >> "${GITHUB_OUTPUT}"
printf 'GETME!\n%s\n' "${actualDiff}"
