#! /bin/bash

src='f01069e1-9ea8-4195-8185-e5876b95baff' #'9a197688-9bf0-4c59-8bb4-16affe9579f1'
tgt='613072c0-b56d-4fd5-88cb-990b4680f7fb' #'cf9a210c-14f3-42e0-8ad8-827f5aed7f56'

# usage: parse this file with `. bench.sh` and then run
# `extractVariations commit1 commit2 > benchOutput.json`
#
# gets the json file for the comparison from http://speed.lean-fro.org/mathlib4
# and prints the files / categories with an instruction change of at least 10^9,
# first the ones that got slower, then the ones that got faster

extractVariations () {
  local threshold=1000000000
  local reg='^[0-9]+$'
  local src="${1}"
  local tgt="${2}"
  shift; shift
  if [[ "${1}" =~ ${reg} ]]
  then
    threshold="${1}"
    shift
  fi
  curl "http://speed.lean-fro.org/mathlib4/api/compare/${src}/to/${tgt}?all_values=true" |
  jq -r --arg thr "${threshold}" '.differences | .[] |
      ($thr|tonumber) as $th |
      select(.dimension.metric == "instructions" and ((.diff >= $th) or (.diff <= -$th)))
    ' |
    jq -c '[{file: .dimension.benchmark, diff: .diff, reldiff: .reldiff}]' |
    jq -n 'reduce inputs as $in (null; . + $in)'
}

 : <<'BASH_MAGMA_CODE'

curl "http://speed.lean-fro.org/mathlib4/api/compare/${src}/to/${tgt}?all_values=true" > temp.json

jq '.differences | .[] | select(.dimension.metric == "instructions") |  select(.diff >= 1000000000) | [.dimension.benchmark, .diff, (.reldiff * 100)]' temp.json > temp1
jq '.differences | .[] | select(.dimension.metric == "instructions") |  select(.diff <= -1000000000) | [.dimension.benchmark, .diff, (.reldiff * 100)]' temp.json > temp2

magma -b ~/lean4/significant.magma

// read in the two files with the data
// format is
// [
//   "~Mathlib.Analysis.NormedSpace.Star.Matrix",    //
//   1177909609,                                     // diff
//   0.86267198115728                                // reldiff
// ]

lines1 := Split(Read("temp1"));
lines2 := Split(Read("temp2"));

// parse into triples <"file", diff, reldiff>
assert IsDivisibleBy(#lines1, 5) and IsDivisibleBy(#lines2, 5);

for i -> l in lines1 do
  if l[#l] eq "," then Prune(~lines1[i]); end if;
end for;
for i -> l in lines2 do
  if l[#l] eq "," then Prune(~lines2[i]); end if;
end for;

function parse(lseq, i)
  name := Split(lseq[5*i+2], " ~\"")[1]; //"
  d := StringToInteger(lseq[5*i+3]);
  rd := eval lseq[5*i+4];
  return <name, d, rd>;
end function;

seq1 := [parse(lines1, i) : i in [0..(#lines1 div 5)-1]];
seq2 := [parse(lines2, i) : i in [0..(#lines2 div 5)-1]];

seq := [e : e in seq1 cat seq2 | e[1,1] ne "M"];
seq1 := [e : e in seq1 | e notin seq];
seq2 := [e : e in seq2 | e notin seq];

// sort
Sort(~seq1, func<x,y | y[2]-x[2]>);
Sort(~seq2, func<x,y | x[2]-y[2]>);

// print
procedure print_entry(e)
  if #e[1] gt 50 then
    printf "  %o:\n"*" "^55*"%o%o * 10⁹ (%o%o%%)\n", e[1], e[2] gt 0 select "+" else "",
           ChangePrecision(e[2]*1e-9, 5), e[3] gt 0 select "+" else "", ChangePrecision(e[3], 3);
  else
    printf "  %-51o  %o%o * 10⁹ (%o%o%%)\n", e[1]*":", e[2] gt 0 select "+" else "",
           ChangePrecision(e[2]*1e-9, 5), e[3] gt 0 select "+" else "", ChangePrecision(e[3], 3);
  end if;
end procedure;

printf "\n"*"="^78*"\n";
printf "General information:\n";
for e in seq do
  print_entry(e);
end for;
printf "\nFiles that got slower:\n";
for e in seq1 do
  print_entry(e);
end for;
printf "\nFiles that got faster:\n";
for e in seq2 do
  print_entry(e);
end for;
printf "="^78*"\n";

quit;
BASH_MAGMA_CODE
