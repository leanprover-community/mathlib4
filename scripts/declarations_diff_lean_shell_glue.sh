#!/usr/bin/env bash

 : <<'BASH_MODULE_DOCS'
Running `./scripts/declarations_diff_lean_shell_glue.sh <PR_NUMBER> <PR_HASH>`
creates the two files `${PRdeclsFile}` and `${MSdeclsFile}`, containing all the declarations
in the environment the former for the PR, the latter for `master`.

It then creates/updates the declaration diff message on the PR with the diff of the two files.
BASH_MODULE_DOCS

script_file=scripts/declarations_diff.lean
PRdeclsFile=decls_in_PR.txt
MSdeclsFile=decls_in_master.txt
PR_NUMBER="${1:-NO_PR_NUMBER}"
PR_HASH="${2:-NO_PR_HASH}"

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
