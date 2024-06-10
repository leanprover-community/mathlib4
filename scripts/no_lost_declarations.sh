#!/usr/bin/env bash

## we narrow the diff to lines beginning with `theorem`, `lemma` and a few other commands
begs="(theorem|lemma|inductive|structure|def|class|instance)"

if [ "${1}" == "short" ]
then
  short=1
  shift
else short=0
fi

## if an input commit is given, compute the diff with that, otherwise, use the git-magic `...`
full_output=$(if [ -n "${1}" ]; then
  git diff --unified=0 "${1}"
else
  git diff origin/master...HEAD
fi |
  ## purge `@[...]`, to attempt to catch declaration names
  sed 's=@\[[^]]*\] ==; s=noncomputable ==; s=nonrec ==; s=protected ==' |
  ## extract lines that begin with '[+-]' followed by the input `theorem` or `lemma`
  ## in the `git diff`
  awk -v regex="^[+-]${begs}" 'BEGIN{ paired=0; added=0; removed=0 }
    /^--- a\//    { minusFile=$2 }  ## the path to the old file
    /^\+\+\+ b\// { plusFile=$2 }   ## the path to the new file
    ($0 ~ regex){
      ## `pm` is the first character of the line -- either + or -
      pm=substr($0, 1, 1)
      ## `rest` is the line starting from the second character
      rest=substr($0, 2)

      ## for each line,
      ## * `fil` records which file contains it and
      ## * `acc` whether it is added or subtracted.

      ## store in the array `fil` the (key, value) pair (line, file where it is)
      fil[rest]= (pm == "+") ? plusFile : minusFile
      ## the array `acc` records, for each line, whether it is + or -
      acc[rest]=acc[rest] pm
    }
  END {
    printf "|File|+-|Declaration|\n|-|-|-|"
    fin=""
    ## for each line...
    for(res in acc) {
      pm=acc[res]
      ## if it was added and subtracted, we increment `paired`,
      ## otherwise we increment one of `added` or `removed`.
      if(pm == "-+" || pm == "+-") { paired++ } else {
        if(pm == "+") { added++ } else removed++
        ## we also print a summary of the form "| sourceFile | `+-` | `line` |"
        fin=fin sprintf("| %s | `%s` | `%s` |\n", fil[res], pm, res)
      }
    }
    ## once we are done, we sort with respect to the column (6) that
    ## should correspond to the declaration type, resolving ties by looking at the
    ## declaration name
    print fin| "sort -k6 -k7"; close("sort -k6 -k7")
    ## we also tally the numbers of added, paired and removed declarations.
    printf("---\n* %s  added declarations\n* %s  removed declarations\n* %s  paired declarations", added, removed, paired)
  }'
)

## report may be empty, if every declaration is accounted for.
report="$(if [ "${short}" == "0" ]
then
  ## the full report is just what was computed above
  echo "${full_output}"
else
  ## the short report is a shortening and reformatting of the above
  ## basically, we want to keep just the names of the declarations
  ## but for nameless instance, we keep the whole line
  echo "${full_output}" |
  awk '{
    # strip out backticks
    gsub(/`/, "")
    # field 6 should be the declaration type.
    # if it is an instance and the next word does not begin with a character
    # then it is a nameless instance and we recreate the line
    # (which starts with the field 6 -- `instance`)
    if(($6 == "instance") && !($7 ~ /^[a-zA-Z]/)) {
      rest="instance"
      for(i=7; i<=NF-1; i++){rest=rest" "$i}
      # remove trailing `where` or `:=`
      gsub(/ where.*/, "", rest)
      gsub(/ :=.*/, "", rest)
      # accumulate in `acc` the whole line with value the 4th field -- this is the +- field.
      acc[rest]=acc[rest] $4
      # if the line is not a nameless instance, accumulate the declaration name and +-
    } else { acc[$7]=acc[$7] $4 } } END{
    for(d in acc) {
      if ((acc[d] == "+-") || (acc[d] == "-+")) {
        printf "" } else { printf("%s %s\n", acc[d], d)
      }
    }
  }' |
  ## what comes out is of the form `+- declName` or `+- instance [..]`
  ## so, sorting, counting repeated lines and omitting lines that are counted twice
  ## we should be left with "unique" lines or lines repeated at least 3 times
  ## we pretend that these last ones do not appear -- they will get printed, but not formatted
  sort | uniq -c | grep -v "^ *2 " |
  ## on the lines that contain `+` or `-`, remove the initial `<spaces> 1` and
  ## add backticks at the beginning and at the end of the line
  grep '\(+\|-\)' | sed 's=^ *1 =`=; s=^[^`]=`=; s=$=`='
fi)"

if [ -n "${report}" ]
then
  echo "${report}"
else
  echo "No declarations were harmed in the making of this PR! 🐙"
fi

printf $'<details>
  <summary>You can run this locally as follows</summary>\n\n
```bash
## summary with just the declaration names:
./scripts/no_lost_declarations.sh short <optional_commit>

## more verbose report:
./scripts/no_lost_declarations.sh <optional_commit>
```
</details>'
 : <<ReferenceTest
theorem oh hello
inductive triggers the count even if it is not lean code
instance [I pretend] {to be a nameless} instance where
def ohMy im a def
instance [I also pretend] {to be a nameless} instance :=
def testingLongDiff1 im a def
def testingLongDiff2 im a def
def testingLongDiff3 im a def
def testingLongDiff4 im a def
ReferenceTest
