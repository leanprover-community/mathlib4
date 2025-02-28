/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Tactic.Linter.Header

/-!
#  The "variableVariable" linter

The "variableVariable" linter emits a warning when it finds a pattern of the form
```
variable (X)

<single_declaration>

variable {X}
```
and suggests to use `variable (X) in` instead of `variable (X)`.
-/

open Lean Elab

namespace Mathlib.Linter

/--
The "variableVariable" linter emits a warning when it finds a pattern of the form
```
variable (X)

<single_declaration>

variable {X}
```
and suggests to use `variable (X) in` instead of `variable (X)`.
-/
register_option linter.variableVariable : Bool := {
  defValue := true
  descr := "enable the variableVariable linter"
}

/--
The `varsAndDeclsRef` contains the ranges of every command in a file, singling out
`variable` and `declaration` commands.
-/
initialize varsAndDeclsRef : IO.Ref (Std.HashMap String.Range String) ← IO.mkRef ∅

namespace VariableVariable

@[inherit_doc Mathlib.Linter.linter.variableVariable]
def variableVariableLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.variableVariable (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mut addedAlready? := false
  let stxRg := stx.getRange?.getD default
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declaration) with
  | none => pure ()
  | some decl =>
    let declName :=
      if let some dId := decl.find? (·.isOfKind ``Lean.Parser.Command.declId)
      then
        s!"declaration '{dId[0].getId}'"
      else
        "declaration anonymous"
    --dbg_trace "adding ({stxPos}, {declName}) to `varsAndDeclsRef`"
    varsAndDeclsRef.modify (·.insert stxRg declName)
    addedAlready? := true
  match stx with
  | `(variable ($x)) | `(variable {$x}) =>
    --dbg_trace "adding ({stxPos}, {x.raw.getId}) to `varsAndDeclsRef`"
    varsAndDeclsRef.modify (·.insert stxRg s!"variable {x.raw.getId}")
    addedAlready? := true
  | _ =>
    if !addedAlready? then
      varsAndDeclsRef.modify (·.insert stxRg "something else")
  if Parser.isTerminalCommand stx then
    let sorted := (← varsAndDeclsRef.get).toArray.qsort (·.1.start < ·.1.start)
    --Linter.logLint linter.variableVariable stx
    --  m!"{.joinSep (sorted.toList.map (fun d => m!"({d.1.start}, {d.2})")) "\n"}"
    for i in [:sorted.size - 2] do
      let (pos0, decl0) := sorted[i]!
      let (pos1, decl1) := sorted[i + 1]!
      let (pos2, decl2) := sorted[i + 2]!
      if decl0.startsWith "variable " && decl2 == decl0 && decl1.startsWith "declaration" then
        Linter.logLint linter.variableVariable (.ofRange pos1)
          m!"Consider using 'variable {decl0} in' for {decl1}"

initialize addLinter variableVariableLinter

end VariableVariable

end Mathlib.Linter
