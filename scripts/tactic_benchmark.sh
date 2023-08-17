#!/usr/bin/env bash

# Run either as `tactic_benchmark --aesop` to run aesop on all of Mathlib,
# or `tactic_benchmark --aesop Mathlib.Logic.Hydra` to run on just one file.
# Results will go in `tactic_benchmark/aesop/Mathlib.Logic.Hydra.bench`.


if [ "$#" -eq 1 ]; then
  rm -f ./build/lake.lock
  parallel -j32 ./scripts/tactic_benchmark.sh $1 -- `cat Mathlib.lean | sed -e 's/import //'`
else
  DIR=tactic_benchmark/${1#--}
  mkdir -p $DIR
  mod=$2
  echo $mod
  if [ ! -f $DIR/$mod.bench ]
  then
    lake exe tactic_benchmark $1 $mod > $DIR/$mod._bench && mv $DIR/$mod._bench $DIR/$mod.bench
  fi
fi
