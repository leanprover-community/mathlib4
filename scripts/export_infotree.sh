#!/usr/bin/env bash

# Run either as `scripts/export_infotree.sh` to run on all of Mathlib,
# or `scripts/export_infotree.sh Mathlib.Logic.Hydra` to run on just one file.
# Results will go in `build/export_infotree/Mathlib.Logic.Hydra.json`.

# To pass the flags `--tactics --original --substantive` you have to modify the script below.
# TODO: proper command line arguments.

if [ "$#" -ne 1 ]; then
  rm -f ./build/lake.lock
  lake build export_infotree
  parallel -j32 ./scripts/export_infotree.sh -- `cat Mathlib.lean | sed -e 's/import //'`
else
  DIR=build/export_infotree
  mkdir -p $DIR
  mod=$1
  if [ ! -f $DIR/$mod.json ]; then
    echo $mod
    if [ ! -f build/bin/export_infotree ]; then
      lake build export_infotree
    fi
    build/bin/export_infotree --tactics --original --substantive $mod > $DIR/$mod._json && mv $DIR/$mod._json $DIR/$mod.json
    # build/bin/export_infotree $mod > $DIR/$mod._json && mv $DIR/$mod._json $DIR/$mod.json
  fi
fi
