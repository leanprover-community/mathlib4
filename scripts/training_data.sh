#!/usr/bin/env bash

## Generates pretty-printed descriptions of every goal/tactic pair.

# See the help text in `lake exe training_data` for a description of the output format.

# Run either as `scripts/training_data.sh` to run on all of Mathlib (several hours),
# or `scripts/training_data.sh Mathlib.Logic.Hydra` to run on just one file.
# Results will go in `build/training_data/Mathlib.Logic.Hydra.train`.

if [ "$#" -ne 1 ]; then
  rm -f ./build/lake.lock
  lake build training_data
  parallel -j32 ./scripts/training_data.sh -- `cat Mathlib.lean | sed -e 's/import //'`
else
  DIR=build/training_data
  mkdir -p $DIR
  mod=$1
  if [ ! -f $DIR/$mod.train ]; then
    echo $mod
    if [ ! -f build/bin/training_data ]; then
      lake build training_data
    fi
    build/bin/training_data --proofstep $mod > $DIR/$mod._train && mv $DIR/$mod._train $DIR/$mod.train
  fi
fi
