#!/usr/bin/env bash

## Writes a human readable summary of the tactics tested so far.

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

mkdir -p $SCRIPT_DIR/../tactic_benchmark
cd $SCRIPT_DIR/../tactic_benchmark

tactics=`ls -d */ | cut -f1 -d'/'`

for tac in $tactics; do
  mkdir -p $tac
  cd $tac
  grep ✅ * | awk '{print $1 " " $2}' | sort > ../$tac.out
  grep ❌ * | awk '{print $1 " " $2}' | sort > ../$tac.failure
  grep -h "^\(✅\|❌\)" * | awk '{gsub(/[()s]/,""); s+=$3;}END{printf "%.0f\n",s}' > ../$tac.time
  cd ..
done

for tac in $tactics; do
  echo "Solved by $tac: " `cat $tac.out | wc -l` / `cat $tac.failure | wc -l` " in " `cat $tac.time`"s"
  for other in $tactics; do
    if [ "$tac" != "$other" ]; then
      echo "  but not $other: " `comm -23 $tac.out $other.out | wc -l`
    fi
  done
done
