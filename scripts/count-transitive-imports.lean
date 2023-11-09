import Mathlib

open Lean Meta

#eval show MetaM Nat from do
  let mut t := 0
  for (_, s) in (← getEnv).importGraph.transitiveClosure do
    t := t + s.size
  return t

-- prints about 5 * 10^6
