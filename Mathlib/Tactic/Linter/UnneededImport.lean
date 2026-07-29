/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import ImportGraph.Imports.ImportGraph
public meta import ImportGraph.Graph.TransitiveClosure
public meta import Mathlib.Tactic.Linter.DeclaredNames

/-! # The `unneededImport` linter

The `unneededImport` linter accumulates the defining modules of the constants that the
declarations of the file use, with the exact declaration list of each command from the
`declaredNames` producer. At the end of the file, it reports a direct import when the other
imports cover every used module of its import closure. The message also reports the count of
modules that removal drops from the import closure, so findings with an effect on the closure
identify themselves.

Imports that only provide syntax, tactics, or attributes are invisible to constant analysis
and give false positives. Such imports need an ignore list, like `scripts/noshake.json`.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Enables the prototype `unneededImport` linter. -/
public register_option linter.unneededImport : Bool := {
  defValue := false
  descr := "enable the unneededImport linter"
}

/-- Persistent state of the `unneededImport` linter: the defining modules of all constants
that the declarations of the file use. -/
public structure UsedModules where
  /-- The modules that define the constants used so far. -/
  used : NameSet := {}
  deriving Inhabited

@[inherit_doc Mathlib.Linter.linter.unneededImport]
def unneededImportPost (readPre : PreStateFn) (stx : Syntax) (self : UsedModules) :
    CommandElabM UsedModules := do
  unless getLinterValue linter.unneededImport (← getLinterOptions) do
    return self
  let env ← getEnv
  let mut used := self.used
  if let some p := readPre declaredNames then
    for n in p.new do
      if let some ci := env.find? n then
        for c in ci.getUsedConstantsAsSet do
          if let some idx := env.getModuleIdxFor? c then
            used := used.insert env.allImportedModuleNames[idx.toNat]!
  if Parser.isTerminalCommand stx then
    let tc := env.importGraph.transitiveClosure
    let directs := env.header.imports.map (·.module) |>.filter fun m =>
      m != `Mathlib.Init && m.getRoot != `Init
    for m in directs do
      -- An import is removable when the other imports cover every used module of its closure.
      let below := (tc.getD m {}).insert m
      let neededHere := used.filter below.contains
      let othersCover (u : Name) : Bool := directs.any fun o =>
        o != m && (o == u || (tc.getD o {}).contains u)
      if neededHere.all othersCover then
        -- The count of modules that only this import brings into the closure.
        let exclusive := below.foldl (init := (0 : Nat)) fun n x =>
          if directs.any (fun o => o != m && (o == x || (tc.getD o {}).contains x)) then n
          else n + 1
        let impact := if exclusive == 0 then
          m!"the closure does not change: the other imports cover all of it"
        else
          m!"removing it also drops {exclusive} modules from the import closure"
        logLint linter.unneededImport stx
          m!"import '{m}' is possibly unneeded: the other imports cover every constant that \
            this file uses from its import closure; {impact}"
  return { used }

@[inherit_doc Mathlib.Linter.linter.unneededImport]
public initialize unneededImport : StatefulLinter UsedModules Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ readPre => unneededImportPost readPre stx self)

end Mathlib.Linter
