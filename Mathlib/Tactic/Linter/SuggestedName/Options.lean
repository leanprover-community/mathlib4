/-
Copyright (c) 2026 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

public meta import Lean.Linter.Init

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Options for the "suggested name linter"

The option for this environment linter needs to be imported in
every file where the linter should be active. For more
details look at the implementation file.
-/

open Lean

meta section

public register_option linter.envLinter.suggestedName : Bool := {
  defValue := true -- TODO
  descr := "warn when a theorem name does not use the proper capitalisation \
    according to the mathlib naming convention"
}

initialize Linter.addEnvLinterOption linter.envLinter.suggestedName
