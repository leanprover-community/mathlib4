/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asei Inoue, Damiano Testa
-/
import Lean.Util.CollectAxioms
import Mathlib.Init

/-!
#  The "disallowedAxioms" linter

The "disallowedAxioms" linter emits a warning on declarations that depend on any axiom
listed in the `disallowedAxiomsRef` `IO.Ref`.
-/

open Lean Elab Command

namespace Mathlib.Linter

-- should be made into an environment extension
/--
`disallowedAxiomsRef` contains the names of the disallowed axioms.
This is used by the `disallowedAxioms` linter.
-/
initialize disallowedAxiomsRef : IO.Ref NameSet ← IO.mkRef ∅

elab "#disallowed_axioms" : command => do
  logInfo m!"{(← disallowedAxiomsRef.get).toArray.qsort (·.toString < ·.toString)}"

initialize registerBuiltinAttribute {
    name := `disallowed_axiom
    descr := "An axiom that triggers the `disallowedAxioms` linter"
    add := fun decl attrStx kind ↦ do
      let some cinfo := (← getEnv).find? decl | throwError "unknown constant '{decl}'"
      unless cinfo.isAxiom do
        throwError "'{decl}' is not an axiom"
      disallowedAxiomsRef.modify (·.insert decl)
    applicationTime := .afterCompilation
  }

/--
The "disallowedAxioms" linter emits a warning on declarations that depend on any axiom
with the `disallowed_axiom` attribute.
-/
register_option linter.disallowedAxioms : Bool := {
  defValue := true
  descr := "enable the disallowedAxioms linter"
}

/--
The `linter.verbose.disallowedAxioms` option is a flag to make the `disallowedAxioms` linter emit
a confirmation on declarations that depend *not* on the `Classical.choice` axiom.
-/
register_option linter.verbose.disallowedAxioms : Bool := {
  defValue := false
  descr := "enable the verbose setting for the disallowedAxioms linter"
}

namespace DetectClassical

@[inherit_doc Mathlib.Linter.linter.disallowedAxioms]
def disallowedAxiomsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.disallowedAxioms (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let nms := (← getNamesFrom (stx.getPos?.getD default)).filter (! ·.getId.isInternal)
  let verbose? := Linter.getLinterValue linter.verbose.disallowedAxioms (← getOptions)
  for constStx in nms do
    let constName := constStx.getId
    let axioms ← collectAxioms constName
    if axioms.isEmpty then
      if verbose? then
        logInfoAt constStx m!"'{constName}' does not depend on any axioms"
      return
    let disallowedAxioms ← disallowedAxiomsRef.get
    let presentDisallowedAxioms := axioms.filter disallowedAxioms.contains
    if !presentDisallowedAxioms.isEmpty then
      logInfoAt constStx
        m!"'{constName}' depends on the following disallowed axioms:\n\
          {presentDisallowedAxioms.toList}\n\
          All axioms on which '{constName}' depends: {axioms.toList}"

initialize addLinter disallowedAxiomsLinter

end DetectClassical

/--
The "unusedDecl" linter flags declarations that are not used by any declaration in the current file.
-/
register_option linter.unusedDecl : Bool := {
  defValue := true
  descr := "enable the unusedDecl linter"
}

structure UnusedDeclState where
  all : Std.HashSet (String.Range × Name) := ∅
  used : NameSet := ∅
  deriving Inhabited

initialize unusedDeclRef : IO.Ref UnusedDeclState ← IO.mkRef {}

elab "#unused" : command => do
  let unusedDecl := ← unusedDeclRef.get
  let allSorted := unusedDecl.all.fold (init := #[]) (·.push ·.2) |>.qsort (·.toString < ·.toString)
  let unused := if 30 < unusedDecl.used.size then m!"{unusedDecl.used.size} used constants!" else
    m!"{unusedDecl.used.toArray.qsort (·.toString < ·.toString)}"
  logInfo m!"all: {allSorted}\nused: {unused}"

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
    let some constInfo := env.find? constName | throwError s!"unknown declaration '{constName}'"
    let decls := constInfo.getUsedConstantsAsSet
    unusedDeclRef.modify fun {all, used} => {
        all := all.insert (constStx.getRange?.getD default, constName)
        used := used.union (decls.erase constName)
      }
  if Parser.isTerminalCommand stx then
    let {all, used} ← unusedDeclRef.get
    let unused := all.filter (! used.contains ·.2)
    for (rg, cst) in unused do
      Linter.logLint linter.unusedDecl (.ofRange rg) m!"'{cst}' is unused in this file"

initialize addLinter unusedDeclLinter

end UnusedDecl

end Mathlib.Linter
