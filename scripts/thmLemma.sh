#!/usr/bin/env bash

##  running `produceSed <build_log>` on the output of `lake build`` produces a list of sed commands
##  that replace all doc-string-less `theorem`s with `lemma`s.
##  If you downloaded the build logs, then use `produceSed <build_log> 4` instead.
produceSed () {
  if [ -z "${2}" ]
  then
    sh=2
  else
    sh="${2}"  ##  if parsing the downloaded logs, set `sh` to `4`
  fi
  awk -F: -v ti="'" -v sh="${sh}" '($(sh) ~ /^ \.\//){
    fil=$(sh); gsub(/\.\//, "", fil); row=$(sh+1); col=$(sh+2); gsub(/-.*/, "", col)
    fils[fil]=fils[fil] ":" row "-" col
  } END{
    for(fil in fils){
      printf("sed -i %s\n", ti)
      split(fils[fil], pos, ":")
      for(p in pos) { if(pos[p] != ""){
        split(pos[p], rc, "-")
        printf("  %s{s=\\(.\\{%s\\}\\)\\(theorem\\)=\\1lemma=}\n", rc[1], rc[2])
      }}
      printf("%s%s\n", ti, fil)
    }
  }' "${1}"
}

: <<'DOES_NOT_PARSE'
## import the `theorem` vs `lemma` linter wherever `Mathlib.Tactic.Lemma` is imported
## (alternatively, the linter could be imported just in `Mathlib.Tactic.Lemma`)
sed -i 's=import Mathlib\.Tactic\.Lemma=&\nimport Mathlib.Tactic.ThmLemma=' $(
  grep "import Mathlib\.Tactic\.Lemma" $(git ls-files 'Mathlib/*.lean') |
   awk -F: '{printf " "$1}END{ print "" }')

## either build locally or push, wait for CI and then run `lake exe cache get`

## transform the output of `lake build` into the appropriate replacement and perform the replacement
eval "$(lake build | produceSed -)"

## commit all the `theorem` to `lemma` translations
git commit -am 'feat: doc-less `theorem` to `lemma`'
git push
DOES_NOT_PARSE
