/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
import Lean.Message

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Lint on `variable (foo : Bar)`, and emits a warning if Bar has
universe metavariables in its type. -/
public register_option linter.universeMVarInVariable : Bool :=
  { defValue := true
    descr := "enable the universeMVarInVariable linter" }

namespace universeMVarInVariableLinter

open Meta Term Linter in
def universeMVarInVariable : Linter where run := withSetOptionIn fun stx => do
  match stx with
  | `(variable $[$x:bracketedBinder]*)
  | `(variable $[$x:bracketedBinder]* in $t) =>
    runTermElabM <| fun fvars ↦ elabBinders x fun s => do
      for x in s do
        let v ← instantiateMVars <| ← inferType x
        if v.hasLevelMVar then
          logLint linter.universeMVarInVariable stx
            m!"type of variable contains universe metavariable! {v}"
  | _ => return

initialize addLinter universeMVarInVariable

end universeMVarInVariableLinter

end Mathlib.Linter
