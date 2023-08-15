#!/usr/bin/env bash

if [ "$#" -ne 1 ]; then
  parallel -j32 ./scripts/training_data.sh -- `cat Mathlib.lean | sed -e 's/import //'`
else
  OUT=training_data
  mod=$1
  echo $mod
  if [ ! -f $OUT/$mod.train ]
  then
    lake exe training_data $mod > $OUT/$mod._train && mv $OUT/$mod._train $OUT/$mod.train
  fi
fi
