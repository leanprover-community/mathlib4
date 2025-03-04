#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean
PRdeclsFile=decls_in_PR.txt
MSdeclsFile=decls_in_master.txt
PR_NUMBER="${1:-NO_PR_NUMBER}"
PR_HASH="${2:-NO_PR_HASH}"

 : <<'BASH_MODULE_DOCS'
# Running `getDeclarations <PR_NUMBER> <PR_HASH>`
# 1. downloads the cache for `Mathlib`, `Archive` and `Counterexamples`;
# 2. copies the declarations diff Lean script to `Mathlib` and adds the line
     `#all_declarations <file_name>` to the file
# 3. builds the declarations diff script, which in turn
# 4. saves to `${PRdeclsFile}`/`${MSdeclsFile}` all the declarations in the environment as appropriate;
# 5. removes the line added to the declarations diff Lean script;
# 6. uses `<sep_string>` to signal when the text that the report should use starts.
BASH_MODULE_DOCS

# Running `getDeclarations <file_name>`
# 1. downloads the cache for `Mathlib`, `Archive` and `Counterexamples`;
# 2. copies the declarations diff Lean script to `Mathlib` and adds the line
#    `#all_declarations <file_name>` to the file
# 3. `lake build`s the declarations diff script, which in turn
# 4. saves to `<file_name>` all the declarations in the environment;
# 5. removes the copy of the declaration diff script from `Mathlib`.
getDeclarations () {
  local file=Mathlib/declarations_diff_lean.lean
  printf '* Download the cache\n'
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean

  printf $'* Save the declarations to \'%s\'\n' "${1}"

  cp "${script_file}" "${file}"
  printf $'@[to_additive] theorem Mul.%s\' : True := trivial\n#all_declarations "%s"\n' "${1}" "${1}" >> "${file}"
  #printf $'#all_declarations "%s"\n' "${1}" >> "${file}"
  lake build Mathlib.declarations_diff_lean

  # undo the local changes
  rm -f "${file}"
}

getDeclarations "${PRdeclsFile}"

git checkout origin/master...HEAD
masterHash="$(git rev-parse HEAD)"

# get the lean script file from master or the current PR if it does not exist there
# once the PR is merged, the `||`-branch can be removed
git checkout master:"${script_file}" ||
  git checkout "${PR_HASH}" "${script_file}"

getDeclarations "${MSdeclsFile}"

printf 'Diff the declarations\n'

diff "${MSdeclsFile}" "${PRdeclsFile}"
echo "*** End of diff ***"

messageStart=$'<details><summary><b>Declaration diff in Lean</b></summary>'
{
  printf '%s\n\n```diff\n' "${messageStart}"
  diff "${MSdeclsFile}" "${PRdeclsFile}" | grep '^[<>]'
  printf '```\n</details>\nPR: %s\n\nMaster: %s\n' "${PR_HASH}" "${masterHash}"
} > please_merge_master
printf -- $'--- Start of message ---\n%s\n--- End of message ---\n' "$(cat please_merge_master)"

./scripts/update_PR_comment.sh please_merge_master "${messageStart}" "${PR_NUMBER}"
