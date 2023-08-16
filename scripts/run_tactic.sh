#!/usr/bin/env bash

rm -f ./build/lake.lock
parallel -j32 lake exe run_tactic $@ -- `cat Mathlib.lean | sed -e 's/import //'`
