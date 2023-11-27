import Mathlib

-- Run as `lake env lean scripts/countTransitiveImports.lean`
-- Prints the number of parts `A, B` such that `A` is transitively imported by `B`.

open Lean Meta
#eval show MetaM Nat from do
  let mut t := 0
  for (_, s) in (← getEnv).importGraph.transitiveClosure do
    t := t + s.size
  return t
