#! /usr/bin/env bash

# running `./scripts/decls_diff_hybrid.sh commit1 commit2`
# creates two files, `tempDecls1.txt` and `tempDecls2.txt`,
# the former containing all the declarations in `commit1`
# the latter containing all the declarations in `commit2`

# the location of the script
scr=scripts/list_decls.lean
commit1="${1}"
commit2="${2}"
temp1='tempDecls1.txt'
temp2='tempDecls2.txt'
currentHash="$(git rev-parse HEAD)"

# `getDecls`
# 1. retrieves the script file from either master or the PR commit
# 2. gets the cache
# 3. in the lean-script file, removes `--` before `list_decls` and parses the lean file
getDecls () {
  # we check out the script that is in the current branch
  git checkout -q "${currentHash}" "${scr}"
  lake exe cache get > /dev/null
  sed 's=^--\(list_decls\)=\1=' "${scr}" |
    lake env lean --stdin
}

# `processDeclsInOneCommit commitHash tempFile`
# stores the declarations in `commitHash` in the file `tempFile`
# makes sure to come back to the original git branch
processDeclsInOneCommit () {
  # check that the temporary file does not already exist, exiting otherwise
  if [ -f "${2}" ]; then
    printf 'File `%s` already exist, please rename and try again\n' "${2}"
    exit 1
  fi
  git checkout -q "${1}"
  getDecls > "${2}"
  git switch -q -
}

# save the declarations in `commit1` to `tempDecls1.txt`
processDeclsInOneCommit "${commit1}" "${temp1}"
# save the declarations in `commit2` to `tempDecls2.txt`
processDeclsInOneCommit "${commit2}" "${temp2}"
# restore the cache in the initial branch
lake exe cache get > /dev/null

printf 'Declarations only in %s\n%s\n\n' "${commit1}" "$(comm -23 <(sort "${temp1}") <(sort "${temp2}"))"
printf 'Declarations only in %s\n%s\n\n' "${commit2}" "$(comm -13 <(sort "${temp1}") <(sort "${temp2}"))"
