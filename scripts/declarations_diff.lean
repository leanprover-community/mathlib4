import Lean
import Batteries -- technically not needed, since `Mathlib` already imports it
import Mathlib
import Archive
import Counterexamples

open Lean

/--
Prints each declaration in the environment that is not an internal detail.

CI uses the name of this command: if you change it, make sure to update the CI configuration.
-/
elab "#all_declarations " branch:str : command => do
  let mut sorted : Array String := ∅
  for (nm, _) in (← getEnv).constants do
    if !nm.isInternalDetail then
      sorted := sorted.binInsert (· < ·) nm.toString
  dbg_trace "* Writing {sorted.size} declarations to '{branch.getString}'"
  IO.FS.writeFile branch.getString <| .intercalate "\n" sorted.toList
