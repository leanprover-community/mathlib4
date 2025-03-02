import Lean
import Batteries -- technically not needed, since `Mathlib` already imports it
import Mathlib
--import Archive
--import Counterexamples
import Lean.Elab.Command

open Lean

/-- Prints each declaration in the environment that is not an internal detail. -/
elab "#all_declarations" : command => do
  let sorted : Array String := (← getEnv).constants.map₁.fold (init := ∅) fun tot nm _ =>
    if nm.isInternalDetail then
      tot
    else
      tot.binInsert (· < ·) nm.toString
  --for n in sorted do
  --  dbg_trace n
  dbg_trace sorted

-- CI removes the initial `--` from the following line:
-- if you change it, make sure to update the CI configuration.
--#all_declarations
