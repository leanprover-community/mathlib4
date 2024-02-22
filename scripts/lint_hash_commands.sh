#!/usr/bin/env bash

## Usage:
## From the command-line, run `./Mathlib/lint_hash_commands.sh` or
## `./Mathlib/lint_hash_commands.sh anything` if you want a progress report.
## It runs Lean on a file with `import Mathlib`, so it is a good idea to have
## working `.olean`s.
##
## The output is a list of locations in `Mathlib/*.lean` files beginning with
## `<#cmd>`, where `<#cmd>` is a command beginning with `#`.
##
## *The script does *not* create new files nor does it modify/erase existing ones.*

## create a list of all the `#`-commands
getHashCommands () {
  printf $'import Mathlib\n#help command\n' |
    lake env lean --stdin |
    sed -n 's=^syntax "\(#[^"]*\)".*=^\1=p' |
    grep -v "#align$" |
    grep -v "#align_import$" |
    grep -v "#noalign$" |
    sort -u | tr '\n' , |
    sed 's=,$=='
}

## scans all the files in `Mathlib/*.lean` looking for lines that
## * begin with `#cmd`, where `#cmd` is an output of `getHashCommands`;
## * are not inside a comment block.
awk -v csvcmds="$( getHashCommands )" \
  -v con=$( git ls-files 'Mathlib/*.lean' | wc -l ) \
  -v verbose="${1}" \
 'function perr(errMsg) { print errMsg | "cat >&2"; close("cat >&2") }
  BEGIN{
    incomment=0
    split(csvcmds, cmds, ",")
    msg=""
    if(verbose != "") { print "Sniffing `#`-commands" }
  }
  ## lines that begin with `/-` are labeled as `incomment`
  /^\/-/ { incomment=1 }
  ## lines that contain `-/` are labeled as not `incomment`
  /-\// { incomment=0 }
  ## lines that begin with `#` and are not `incomment` get processed
  (/^#/ && incomment == "0") {
    for(cmd in cmds) { if ($0 ~ cmds[cmd]) {
      msg=msg sprintf("%s:%s:%s\n", FILENAME, FNR, $0) }
    } }
  (FNR == 1) {
    con--
    if(verbose != "" && con % 100 == 0) perr(sprintf("%5s files to go", con))
  } END{
    if (msg != "") {
      printf("The following `#`-command should not be present:\n\n%s", msg)
      exit 1
  }
}' $( git ls-files 'Mathlib/*.lean' )
