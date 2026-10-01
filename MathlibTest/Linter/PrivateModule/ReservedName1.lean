module

import Mathlib.Init
import Mathlib.Tactic.Linter.PrivateModule
public import Lean.Elab.Command

@[expose] public section

open Lean

/-- Show reserved names that are local declarations, i.e. in `env.constants.map₂`. -/
elab "#show_new_reserved" : command => do
  let mut reserved := #[]
  for (c, _) in (← getEnv).constants.map₂ do
    if isReservedName (← getEnv) c then reserved := reserved.push c
  logInfo m!"reserved names: {reserved}"

def foo := true

-- `foo.eq_1` is reserved:
/-- info: true -/
#guard_msgs in
run_cmd do logInfo m!"{isReservedName (← getEnv) ``foo.eq_1}"

-- `foo.eq_1` is *not* generated in this module:
/-- info: reserved names: [] -/
#guard_msgs in
#show_new_reserved
