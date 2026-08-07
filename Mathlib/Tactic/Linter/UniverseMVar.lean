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

/-- Lint on `variable (foo : Bar)`, and emits a warning if `Bar` has
universe metavariables in its type. -/
public register_option linter.universeMVarInVariable : Bool :=
  { defValue := true
    descr := "enable the universeMVarInVariable linter" }

namespace universeMVarInVariableLinter

open Parser.Term in
/- Returns `True` if the binder has no type annotation (this happens e.g when
updating a binder annotation) -/
private def isTypelessBinder : TSyntax ``Parser.Term.bracketedBinder → Bool
  | `(bracketedBinderF|($_*))
  | `(bracketedBinderF|{$_*})
  | `(bracketedBinderF|⦃$_*⦄)
  | `(bracketedBinderF|[$_]) => False
  | _ => True

open Meta Term in
/-- Lint on `variable (foo : Bar)`, and emits a warning if `Bar` has
universe metavariables in its type. -/
def universeMVarInVariable : Linter where run := withSetOptionIn fun stx => do
  match stx with
  | `(variable $[$x:bracketedBinder]*)
  | `(variable $[$x:bracketedBinder]* in $t) =>
    for binder in x do
      if !(isTypelessBinder binder) then
      runTermElabM <| fun f ↦ elabBinder binder fun s => do
        let v ← instantiateMVars <| ← inferType s
        if v.hasLevelMVar then
          logLint linter.universeMVarInVariable binder
            m!"type of variable contains universe metavariable! {v}"
  | _ => return

initialize addLinter universeMVarInVariable

end universeMVarInVariableLinter

end Mathlib.Linter
