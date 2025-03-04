#!/usr/bin/env bash

script_file=scripts/declarations_diff.lean
PRdeclsFile=decls_in_PR.txt
MSdeclsFile=decls_in_master.txt
PR_NUMBER="${1:-NO_PR_NUMBER}"
PR_HASH="${2:-NO_PR_HASH}"

# Running `getDeclarations <file_name> <sep_string>`
# 1. downloads the cache for `Mathlib`, `Archive` and `Counterexamples`;
# 2. adds the line `#all_declarations <file_name>` to the declarations diff Lean script;
# 3. builds the declarations diff script, which in turn
# 4. saves to `<file_name>` all the declarations in the environment;
# 5. removes the line added to the declarations diff Lean script;
# 6. uses `<sep_string>` to signal when the text that the report should use starts.
getDeclarations () {
  local file=Mathlib/declarations_diff_lean.lean
  printf '* Download the cache\n'
  lake exe cache get Archive.lean Counterexamples.lean Mathlib.lean

  printf $'* Save the declarations to \'%s\'\n' "${1}"
  #printf $'#all_declarations "%s"\n' "${1}" >> "${script_file}"

  cp "${script_file}" "${file}"
  printf $'def %s\' := 0\n#all_declarations "%s"\n' "${1}" "${1}" >> "${file}"
  lake build Mathlib.declarations_diff_lean

  # undo the local changes
  rm -f "${file}"
}

getDeclarations "${PRdeclsFile}"

git checkout origin/master...HEAD
masterHash="$(git rev-parse HEAD)"

# get the lean script file from the current PR -- update before merging into master
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
printf -- $'------\n%s------\n' "$(cat please_merge_master)"

./scripts/update_PR_comment.sh please_merge_master "${messageStart}" "${PR_NUMBER}"
