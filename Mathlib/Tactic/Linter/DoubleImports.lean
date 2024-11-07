/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ImportGraph.Imports
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.MinImports

/-! # The `doubleImports` linter

The `doubleImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, accumulating increasing import information.
This is better suited, for instance, to split files.
-/

open Lean Elab Command

/-!
#  The "doubleImports" linter

The "doubleImports" linter tracks information about minimal imports over several commands.
-/

/-- Does this declaration come from the current file? -/
def Lean.Name.isLocal (env : Environment) (decl : Name) : Bool :=
  -- I am not sure if this is at all the right way to go about it, but it seems to work in practice.
  (env.getModuleIdxFor? decl).isNone

/-- Does the declaration with this name depend on `def`s in the current file? -/
def Lean.Name.localDefDependencies (env : Environment) (decl : Name) : CoreM Bool := do
  let deps ← decl.transitivelyUsedConstants
  let constInfos := deps.toList.filterMap env.find?
  let defs := constInfos.filter (·.isDef)
  return defs.any fun constInfo => constInfo.name != decl && constInfo.name.isLocal env

/-- Does the declaration with this name depend on `def`s in the current file? -/
def Lean.Syntax.localDefDependencies (env : Environment) (decl : Syntax) : CoreM Bool := do
  let options ← resolveGlobalConst decl
  options.anyM (fun name => name.localDefDependencies env)

namespace Mathlib.Linter

/--
The `doubleImports` linter determines for each declaration if it can be moved higher up the import
hierarchy; if this is the case it will display a warning.

The linter does not place a warning on any declaration depending on a definition in the current file
(while it does place a warning on the definition itself).

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that is better suited, for instance, to split
files.
-/
register_option linter.doubleImports : Bool := {
  defValue := true
  descr := "enable the doubleImports linter"
}

namespace DoubleImports

open Mathlib.Command.MinImports

@[inherit_doc Mathlib.Linter.linter.doubleImports]
def doubleImportsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.doubleImports (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    if stx == (← `(command| set_option $(mkIdent `linter.doubleImports) true)) then return
    let env ← getEnv
    let id ← getId stx
    if id != .missing then
      let newImports := getIrredundantImports env (← getAllImports stx id)
      if newImports.size == 1 && !(← liftCoreM <| id.localDefDependencies env) then
        dbg_trace "imports for '{id}': {newImports.toArray.qsort (·.toString < ·.toString)}"

initialize addLinter doubleImportsLinter

end DoubleImports

end Mathlib.Linter
