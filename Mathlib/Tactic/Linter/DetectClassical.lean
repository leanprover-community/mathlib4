/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asei Inoue, Damiano Testa
-/
import Lean.Util.CollectAxioms
import Mathlib.Init

/-!
#  The "detectClassical" linter

The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The "detectClassical" linter emits a warning on declarations that depend on the `Classical.choice`
axiom.
-/
register_option linter.detectClassical : Bool := {
  defValue := true
  descr := "enable the detectClassical linter"
}

/--
The `linter.verbose.detectClassical` option is a flag to make the `detectClassical` linter emit
a confirmation on declarations that depend *not* on the `Classical.choice` axiom.
-/
register_option linter.verbose.detectClassical : Bool := {
  defValue := false
  descr := "enable the verbose setting for the detectClassical linter"
}

namespace DetectClassical

@[inherit_doc Mathlib.Linter.linter.detectClassical]
def detectClassicalLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.detectClassical (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let nms := (← getNamesFrom (stx.getPos?.getD default)).filter (! ·.getId.isInternal)
  let verbose? := Linter.getLinterValue linter.verbose.detectClassical (← getOptions)
  for constStx in nms do
    let constName := constStx.getId
    let axioms ← collectAxioms constName
    if axioms.isEmpty then
      if verbose? then
        logInfoAt constStx m!"'{constName}' does not depend on any axioms"
      return
    if !axioms.contains `Classical.choice then
      if verbose? then
        logInfoAt constStx
          m!"'{constName}' is non-classical and depends on axioms:\n{axioms.toList}"
    else
      Linter.logLint linter.detectClassical constStx
        m!"'{constName}' depends on 'Classical.choice'.\n\nAll axioms: {axioms.toList}\n"

initialize addLinter detectClassicalLinter

end DetectClassical

/--
The "unusedDecl" linter flags declarations that are not used by any declaration in the current file.
-/
register_option linter.unusedDecl : Bool := {
  defValue := true
  descr := "enable the unusedDecl linter"
}

structure UnusedDeclState where
  all : Array Syntax := ∅
  used : NameSet := ∅
  deriving Inhabited

initialize unusedDeclRef : IO.Ref UnusedDeclState ← IO.mkRef {}

elab "#unused" : command => do
  let unusedDecl := ← unusedDeclRef.get
  logInfo m!"all: {unusedDecl.all}\nused: {unusedDecl.used.toArray.qsort (·.toString < ·.toString)}"

namespace UnusedDecl

@[inherit_doc Mathlib.Linter.linter.unusedDecl]
def unusedDeclLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedDecl (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let nms := (← getNamesFrom (stx.getPos?.getD default)).filter (! ·.getId.isInternal)
  let env ← getEnv
  for constStx in nms do
    let constName := constStx.getId
    let some constInfo ← (pure <| env.find? constName : CommandElabM _ ) |
      throwError s!"unknown declaration '{constName}'"
    let decls := constInfo.getUsedConstantsAsSet
    unusedDeclRef.modify (fun {all, used} =>
      {all := all.push constStx, used := used.union (decls.erase constName)})
  if Parser.isTerminalCommand stx then
    let {all, used} ← unusedDeclRef.get
    let unused := all.filter (! used.contains ·.getId)
    for cst in unused do
      Linter.logLint linter.unusedDecl cst m!"'{cst}' is unused in this file"

initialize addLinter unusedDeclLinter

end UnusedDecl

end Mathlib.Linter
