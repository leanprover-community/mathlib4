import Lean
import Batteries -- technically not needed, since `Mathlib` already imports it
import Mathlib
--import Archive
--import Counterexamples
import Lean.Elab.Command

open Lean

/--
Prints each declaration in the environment that is not an internal detail.

CI uses the name of this command: if you change it, make sure to update the CI configuration.
-/
elab "#all_declarations " branch:str : command => do
  let sorted : Array String := (← getEnv).constants.map₁.fold (init := ∅) fun tot nm _ =>
    if nm.isInternalDetail then
      tot
    else
      tot.binInsert (· < ·) nm.toString
  --for n in sorted do
  dbg_trace "Writing {sorted.size} declarations to '{branch.getString}'"
  IO.FS.writeFile branch.getString <| .intercalate "\n" sorted.toList
