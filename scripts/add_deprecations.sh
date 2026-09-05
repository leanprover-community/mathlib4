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

** `to_additive` **
When the renamed declaration sits under `@[to_additive]`, the script also emits an additive
deprecation alias.  The additive deprecation comes first; the multiplicative deprecation is
tagged `to_additive existing` so the additive companion is rederived by the `to_additive`
machinery rather than left to drift.  For example, renaming `foo_mul` to `bar_mul` produces

```
@[deprecated (since := "...")]
alias foo_add := bar_add

@[to_additive existing, deprecated (since := "...")]
alias foo_mul := bar_mul
```

The additive name is computed by a small set of substitutions (`mul`/`add`, `prod`/`sum`,
`one`/`zero`, `inv`/`neg`, `div`/`sub`).  The script deliberately does not try to rename
typeclass prefixes such as `Monoid`, `Group`, or `Semigroup`; if such tokens remain, the
additive alias is skipped and should be handled by hand.

This is a stop-gap text-based heuristic; a Lean-aware diff would be a stronger long-term
solution.

BASH_MODULE_DOC

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
begs="(theorem|lemma|inductive|structure|def|class|alias|abbrev)"
## regex for the first letter of an identifier (cf `Lean.isIdFirst`)
identRegex=[a-zA-Z_\u3b1-\u3ba\u3bc-\u3c9\u391-\u39f\u3a1-\u3a2\u3a4-\u3a9\u3ca-\u3fb\u1f00-\u1ffe\u2100-\u214f\u1d49c-\u1d59f]

##  `mkDeclAndDepr <file>` outputs a single line of the form
##  `@[deprecated (since := "yyyy-mm-dd")]||||alias yyy := xxx@@@`
##  for each modified declaration in `<file>`.
##  The separators `@@@` delimit different declarations.
##  The separators `||||` are later replaced by line breaks.
## To use a specific date, replace $(date +%Y-%m-%d) with 2024-04-17 for instance
mkDeclAndDepr () {
  # `--unified=3` so that the `awk` block can spot `@[to_additive]` attached to
  # the renamed declaration via diff context; the rest of the script remains
  # text-based.
  git diff --unified=3 "${commit}" "${1}" |
    awk -v regex="${begs}" -v idRegex="${identRegex}" -v date="$(date +%Y-%m-%d)" -v fil="${1}" '
    # with `perr` we print to stderr a summary of the deprecations
    function perr(msg) { print msg | "cat >&2"; close("cat >&2") }
    # `toAdditiveName` applies the most common `to_additive` substitutions
    # to a declaration name.  Intentionally restricted to declaration-name
    # tokens (mul/add, prod/sum, one/zero, inv/neg, div/sub) — we deliberately
    # do not rename typeclass prefixes (Monoid, Group, Semigroup, ...) because
    # ordered substitution there is fragile (e.g. `CommMonoid` and `Monoid`
    # collide).  When the conservative substitution leaves a residual
    # typeclass token in the name, `nameLooksRisky` will flag the result and
    # the additive alias is skipped — those renames must be deprecated by hand.
    function toAdditiveName(name,    out) {
      out = name
      gsub(/mul/, "add", out)
      gsub(/Mul/, "Add", out)
      gsub(/prod/, "sum", out)
      gsub(/Prod/, "Sum", out)
      gsub(/one/, "zero", out)
      gsub(/One/, "Zero", out)
      gsub(/inv/, "neg", out)
      gsub(/Inv/, "Neg", out)
      gsub(/div/, "sub", out)
      gsub(/Div/, "Sub", out)
      return out
    }
    # `nameRiskyAt` returns 1 when `token` appears in `name` without being
    # immediately preceded by `Add` — i.e. when the conservative substitution
    # almost certainly missed a typeclass rename and the result is unsafe.
    function nameRiskyAt(name, token,    pos, prefix) {
      pos = index(name, token)
      if (pos == 0) return 0
      if (pos <= 3) return 1
      prefix = substr(name, pos - 3, 3)
      return (prefix == "Add") ? 0 : 1
    }
    function nameLooksRisky(name) {
      return nameRiskyAt(name, "Monoid") || \
             nameRiskyAt(name, "Group") || \
             nameRiskyAt(name, "Semigroup")
    }
    function depr(ol,ne,attrPrefix) {
      aliasLine=sprintf("alias %s :=||||  %s", ol, ne)
      # if the `alias` line contains less than 100 characters long, we leave it on a single line
      if(length(aliasLine) <= 105) { sub(/\|\|\|\| /, "", aliasLine) }
      line=sprintf("@[%sdeprecated (since := \"%s\")]||||%s", attrPrefix, date, aliasLine)
      # if the `deprecated` and `alias` lines together contain less than 100 characters, we leave them on a single line
      if(length(line) <= 103) { sub(/\|\|\|\|/, " ", line) }
      return line
    }
    # `{plus/minus}Regex` makes sure that we find a declaration, followed by something that
    # could be an identifier. For instance, this filters out "We now prove theorem `my_name`."
    BEGIN{
      reps=1
      regexIdent=regex "  *" idRegex
      plusRegex="^\\+[^+-]*" regexIdent
      minusRegex="^-[^+-]*" regexIdent
      regex="^"regex"$"
      toAdditivePending=0
    }
    # Reset the `to_additive` flag at hunk boundaries so it cannot leak between
    # unrelated renames in the same file.
    /^@@/ { toAdditivePending=0 }
    # Pick up `@[to_additive]` (or `@[..., to_additive, ...]`) appearing in a
    # diff context line near a renamed declaration.  We only react to context
    # lines (leading space) — when the `@[to_additive]` line is itself a `+`/`-`
    # the additive linkage is being added or removed, in which case generating
    # an additive deprecation alias would be wrong.
    /^ / {
      if ($0 ~ /@\[[^]]*to_additive[^a-zA-Z0-9_]/ ||
          $0 ~ /@\[[^]]*to_additive$/) { toAdditivePending=1 }
    }
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
            new=$(i+1)
            # When `@[to_additive]` was in scope, emit the additive alias FIRST
            # and tag the multiplicative alias with `to_additive existing` so the
            # additive deprecation is rederived through the `to_additive`
            # machinery — see Snir Broshi'\''s suggestion on issue #38550.
            # Skip the additive companion if our conservative substitution
            # cannot produce a different name on both sides; otherwise we would
            # generate `alias x := x`, which is bogus.
            emitAdditive=0
            if (toAdditivePending) {
              oldAdd=toAdditiveName(old)
              newAdd=toAdditiveName(new)
              # Emit only when the substitution actually changed both names AND
              # the result is free of unhandled typeclass tokens.  Otherwise
              # leave a TODO to the reviewer rather than ship a wrong alias.
              if ((oldAdd != old) && (newAdd != new) &&
                  !nameLooksRisky(oldAdd) && !nameLooksRisky(newAdd)) {
                emitAdditive=1
              }
            }
            if (emitAdditive) {
              addAlias=depr(oldAdd, newAdd, "")
              mulAlias=depr(old, new, "to_additive existing, ")
              # `||||||||` becomes a blank line after the final `sed` step,
              # separating the additive and multiplicative alias blocks.
              deprText=addAlias "||||||||" mulAlias
              report[reps]=sprintf("%s\n", addAlias)
              reps++
              report[reps]=sprintf("%s\n", mulAlias)
              reps++
            } else {
              deprText=depr(old, new, "")
              report[reps]=sprintf("%s\n", deprText)
              reps++
            }
            # print the line that passes on to `addDeprecations`
            printf("%s %s ,%s@@@", $i, new, deprText)
            # reset the "old name counter", since the deprecation happened
            old=""
            toAdditivePending=0
            break
          } else {
            # We found a keyword corresponding to a declaration, but the following word was not
            # different from the line prior to the change.  Hence, we do not need to deprecate.
            # reset the "old name counter", since the deprecation should not happen
            old=""
            toAdditivePending=0
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
        ## split on the FIRST comma only — the deprecation text may itself
        ## contain commas (e.g. `@[to_additive existing, deprecated ...]`).
        commaIdx = index(pairs[i], ",")
        lines[i] = substr(pairs[i], 1, commaIdx - 1)  ## `lines` contains `theorem/lemma name`s
        deprs[i] = substr(pairs[i], commaIdx + 1)     ## `deprs` contains the deprecation statements
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
