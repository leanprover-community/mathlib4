#! /bin/bash

if [ -z "${1}" ]
then
  commit="$( git merge-base master "$( git rev-parse --abbrev-ref HEAD )" )"
  read -p $'Type a commit number such that all diff lines containing `theorem/def`
correspond to deprecated declarations (use '"'${commit}'"' otherwise):
' comm
  [ -n "${comm}" ] && commit=${comm}
else
  commit="${1}"
fi

# check that the given commit is valid
git cat-file -e "${commit}" || { printf $'invalid commit hash \'%s\'\n' "${commit}";  exit 1; }

## we narrow the diff to lines beginning with `theorem`, `lemma` and a few other commands
begs="(theorem|lemma|inductive|structure|def|class|instance|alias|abbrev)"

##  `mkDeclAndDepr <file>` outputs a single line of the form
##  `@[deprecated (since := "yyyy-mm-dd")]||||alias yyy := xxx@@@`
##  for each modified declaration in `<file>`.
##  The separators `@@@` delimit different declarations.
##  The separators `||||` are later replaced by line breaks.
## To use a specific date, replace $(date +%Y-%m-%d) with 2024-04-17 for instance

mkDeclAndDepr () {
  git diff --unified=0 "${commit}" "${1}" |
    awk -v regex="[^+-]*${begs}" -v date="$(date +%Y-%m-%d)" '
    function depr(ol,ne) {
      return sprintf("@[deprecated (since := \"%s\")]||||alias %s := %s", date, ol, ne)
    }
    BEGIN{ plusRegex="^+" regex; minusRegex="^-" regex; }
    ($0 ~ minusRegex) {
      for(i=1; i<=NF; i++) {
        if (($i ~ /theorem$/) || ($i ~ /lemma$/)) { old=$(i+1) }
      }
    }
    ($0 ~ plusRegex) {
      for(i=1; i<=NF; i++) {
        if (($i ~ /theorem$/) || ($i ~ /lemma$/)) {
          sub(/^+/, "", $i)
          printf("%s %s ,%s@@@", $i, $(i+1), depr(old, $(i+1)))
        }
      }
    }'
}

##  `addDeprecations <file>` adds the deprecation statements to `<file>`,
##  using the first new line after the start of each declaration as position
addDeprecations () {
  awk -v data="$( mkDeclAndDepr "${1}" )" 'BEGIN{
    found=0
    split(data, pairs, "@@@")  ## we setup the data:
    for(i in pairs) {
      if (pairs[i] ~ ",") {
        split(pairs[i], declDepr, ",")
        lines[i]=declDepr[1]   ## `lines` contains `theorem/lemma name`s
        deprs[i]=declDepr[2]   ## `deprs` contains the deprecation statements
      }
    }
    currDep=""
    ## scanning the file, if we find an entries of `lines`, the we assign `currDep`
  } /theorem|lemma/ { for(l in lines) { if ($0 ~ lines[l]) { found=1; currDep=deprs[l] } } } {
    ## when we find the next empty line, we print the deprecation statement in `currDep`
    if ((found == 1) && (NF == 0)) {
      found=0
      printf("\n%s\n", currDep)
    }  ## we print all the lines anyway
    print $0 }
   END{ # in case the statement to deprecate is the last of the file
    if (found == 1) { printf("\n%s\n", currDep) } }' "${1}" |
  sed 's=||||=\n=g'
}

##  loops through the changed files and runs `addDeprecations` on each one of them
new="i_am_a_file_name_with_no_clashes"
while [ -f "${new}" ]; do new=${new}0; done
for fil in $( git diff --name-only ${commit} ); do
  printf $'Processing %s\n' "${fil}"
  addDeprecations "${fil}" > "${new}" ; mv "${new}" "${fil}"
done

 : <<'TEST_DECLARATIONS'

theorem ThmRemoved I'm no longer here
def DefRemoved I'm no longer here
lemma LemRemoved I'm no longer here

TEST_DECLARATIONS
