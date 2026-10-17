#! /usr/bin/env bash

 : <<'BASH_MODULE_DOC'

The script contained in this file tries to automatically generate deprecations for declarations
that were renamed in a PR.
The script is entirely text-based, so it makes several simplifying assumptions and may be easily
confused.

** Assumptions **
The script works under the assumption that the only modifications between `master` and the current
branch are renames of lemmas that should be deprecated.
The script inspects the relevant `git diff`, extracts the old name and the new one and uses this
information to insert deprecated aliases as needed.

Most other differences may confuse the script, although there is some slack.
Please, do not try to push the boundaries of the script, since it is quite simple-minded!

BASH_MODULE_DOC

if [ -z "${1}" ]
then
  commit="$( git merge-base master "$( git rev-parse --abbrev-ref HEAD )" )"
  read -p $'Type a commit number such that all diff lines containing `theorem/def`\ncorrespond to deprecated declarations (use '"'${commit}'"' otherwise):\n' comm
  [ -n "${comm}" ] && commit=${comm}
else
  commit="${1}"
fi

# check that the given commit is valid
git cat-file -e "${commit}" || { printf $'invalid commit hash \'%s\'\n' "${commit}";  exit 1; }

## we narrow the diff to lines beginning with `theorem`, `lemma` and a few other commands
begs="(theorem|lemma|inductive|structure|def|class|alias|abbrev)"
## regex for the first letter of an identifier (cf `Lean.isIdFirst`)
identRegex=[a-zA-Z_\u3b1-\u3ba\u3bc-\u3c9\u391-\u39f\u3a1-\u3a2\u3a4-\u3a9\u3ca-\u3fb\u1f00-\u1ffe\u2100-\u214f\u1d49c-\u1d59f]

##  `mkDeclAndDepr <file>` outputs a single line of the form
##  `@[deprecated (since := "yyyy-mm-dd")]||||alias yyy := xxx@@@`
##  for each modified declaration in `<file>`.
##  The separators `@@@` delimit different declarations.
##  The separators `||||` are later replaced by line breaks.
##
##  When a declaration is preceded by `@[to_additive]`, an additional deprecation alias is
##  emitted for the additive counterpart (e.g. `foo_mul`/`bar_mul` → also `foo_add`/`bar_add`).
##
## To use a specific date, replace $(date +%Y-%m-%d) with 2024-04-17 for instance
mkDeclAndDepr () {
  ## Use --unified=1 so that unchanged lines immediately before a changed declaration
  ## (e.g. `@[to_additive]` attributes) appear as context lines in the diff output.
  git diff --unified=1 "${commit}" "${1}" |
    awk -v regex="${begs}" -v idRegex="${identRegex}" -v date="$(date +%Y-%m-%d)" -v fil="${1}" '
    # with `perr` we print to stderr a summary of the deprecations
    function perr(msg) { print msg | "cat >&2"; close("cat >&2") }
    function depr(ol,ne) {
      aliasLine=sprintf("alias %s :=||||  %s", ol, ne)
      # if the `alias` line contains less than 100 characters long, we leave it on a single line
      if(length(aliasLine) <= 105) { sub(/\|\|\|\| /, "", aliasLine) }
      line=sprintf("@[deprecated (since := \"%s\")]||||%s", date, aliasLine)
      # if the `deprecated` and `alias` lines together contain less than 100 characters, we leave them on a single line
      if(length(line) <= 103) { sub(/\|\|\|\|/, " ", line) }
      return line
    }
    # Apply standard to_additive word substitutions to convert a multiplicative declaration
    # name into its additive counterpart (snake_case, matching Lean 4 / mathlib4 conventions).
    function toAdditiveName(name,    cmd, result) {
      cmd = "printf \"%s\" \"" name "\" | sed " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)mul\\([^a-zA-Z]\\|$\\)/\\1add\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)Mul\\([^a-zA-Z]\\|$\\)/\\1Add\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)one\\([^a-zA-Z]\\|$\\)/\\1zero\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)One\\([^a-zA-Z]\\|$\\)/\\1Zero\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)inv\\([^a-zA-Z]\\|$\\)/\\1neg\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)Inv\\([^a-zA-Z]\\|$\\)/\\1Neg\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)div\\([^a-zA-Z]\\|$\\)/\\1sub\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)Div\\([^a-zA-Z]\\|$\\)/\\1Sub\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)pow\\([^a-zA-Z]\\|$\\)/\\1nsmul\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)Pow\\([^a-zA-Z]\\|$\\)/\\1NSmul\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)npow\\([^a-zA-Z]\\|$\\)/\\1nsmul\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)zpow\\([^a-zA-Z]\\|$\\)/\\1zsmul\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)HPow\\([^a-zA-Z]\\|$\\)/\\1HSMul\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)hPow\\([^a-zA-Z]\\|$\\)/\\1hSMul\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)prod\\([^a-zA-Z]\\|$\\)/\\1sum\\2/g\" " \
        "-e \"s/\\([^a-zA-Z]\\|^\\)Prod\\([^a-zA-Z]\\|$\\)/\\1Sum\\2/g\""
      cmd | getline result
      close(cmd)
      return result
    }
    # `{plus/minus}Regex` makes sure that we find a declaration, followed by something that
    # could be an identifier. For instance, this filters out "We now prove theorem `my_name`."
    BEGIN{
      reps=1
      regexIdent=regex "  *" idRegex
      plusRegex="^\\+[^+-]*" regexIdent
      minusRegex="^-[^+-]*" regexIdent
      regex="^"regex"$"
      toAdditive=0
    }
    # Context lines (unchanged, start with a single space) — track @[to_additive] attributes.
    # The attribute appears on the line immediately before the declaration, so if we see it
    # as a context line, the next changed declaration is additivised.
    /^ / {
      stripped=$0; sub(/^ /, "", stripped)
      if (stripped ~ /^@\[to_additive/) { toAdditive=1 } else { toAdditive=0 }
    }
    # Reset on hunk boundaries
    /^@@/ { toAdditive=0 }
    ($0 ~ minusRegex) {
      for(i=1; i<=NF; i++) {
        strip=$i
        gsub(/^[+-]*/, "", strip)
        if (strip ~ regex) { old=$(i+1); break }
      }
    }
    # the check on `old` is to make sure that we found an "old" name to deprecate
    # otherwise, the declaration could be a genuinely new one.
    (($0 ~ plusRegex) && (!(old == ""))) {
      for(i=1; i<=NF; i++) {
        strip=$i
        gsub(/^[+-]*/, "", strip)
        if (strip ~ regex) {
          sub(/^\+/, "", $i)
          if (!(old == $(i+1))) {
            # print the line that passes on to `addDeprecations`
            printf("%s %s ,%s@@@", $i, $(i+1), depr(old, $(i+1)))
            # accumulate the summary of deprecations
            report[reps]=sprintf("%s\n", depr(old, $(i+1)))
            reps++
            # If preceded by @[to_additive], also emit a deprecation alias for the
            # additive counterpart (e.g. foo_mul -> foo_add, bar_mul -> bar_add).
            if (toAdditive) {
              addOld = toAdditiveName(old)
              addNew = toAdditiveName($(i+1))
              # Only emit the additive alias if the names actually differ from the
              # multiplicative ones (i.e. the name contains multiplicative vocabulary)
              # and the additive old/new names are themselves distinct.
              if ((addOld != old || addNew != $(i+1)) && (addOld != addNew)) {
                printf("%s %s ,%s@@@", $i, addNew, depr(addOld, addNew))
                report[reps]=sprintf("%s\n", depr(addOld, addNew))
                reps++
              }
            }
            # reset the "old name counter", since the deprecation happened
            old=""
            toAdditive=0
            break
          } else {
            # We found a keyword corresponding to a declaration, but the following word was not
            # different from the line prior to the change.  Hence, we do not need to deprecate.
            # reset the "old name counter", since the deprecation should not happen
            old=""
            toAdditive=0
            break
          }
        }
      }
    } END {
      # print to stderr a summary of deprecations
      if (!(reps == 1)) {
        perr("\n`" fil "` deprecations:")
        for(i=1; i<reps; i++)
        perr(i": " report[i])
      }
    }'
}

##  `addDeprecations <file>` adds the deprecation statements to `<file>`,
##  using the first new line after the start of each declaration as position
addDeprecations () {
  awk -v regex="${begs}" -v data="$( mkDeclAndDepr "${1}" )" 'BEGIN{
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
  } ($0 ~ regex) { for(l in lines) { if ($0 ~ lines[l]) { found=1; currDep=deprs[l] } } } {
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
  if [ "${fil/*./}" == "lean" ]
  then
    printf $'Processing %s\n' "${fil}"
    addDeprecations "${fil}" > "${new}" ; mv "${new}" "${fil}"
  fi
done

 : <<'TEST_DECLARATIONS'

theorem ThmRemoved I'm no longer here

def DefRemoved I'm no longer here

lemma LemRemoved I'm no longer here

TODO: parse `instance` only if they are named?

TEST_DECLARATIONS
