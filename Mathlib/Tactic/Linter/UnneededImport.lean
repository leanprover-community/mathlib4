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

Usage marking has three sources: the constants that the declarations of the file use, the
defining modules of the syntax node kinds of each command, and the defining modules of the
options that each command names. The second source covers imports that only provide syntax,
tactics, or attributes; the third covers imports that only provide an option, because
`set_option` belongs to core and its node kinds name no module of the file.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Enables the prototype `unneededImport` linter. -/
public register_option linter.unneededImport : Bool := {
  defValue := false
  descr := "enable the unneededImport linter"
}

/-- Collects the node kinds of a syntax tree. -/
partial def collectKinds (s : Syntax) (acc : NameSet) : NameSet :=
  let acc := if s.isOfKind `null ∨ s.isIdent ∨ s.isAtom then acc else acc.insert s.getKind
  s.getArgs.foldl (fun a c => collectKinds c a) acc

/-- Collects the identifiers of a syntax tree. -/
partial def collectIdents (s : Syntax) (acc : NameSet) : NameSet :=
  let acc := if s.isIdent then acc.insert s.getId else acc
  s.getArgs.foldl (fun a c => collectIdents c a) acc

/-- Persistent state of the `unneededImport` linter: the defining modules of all constants
that the declarations of the file use. -/
public structure UsedModules where
  /-- The modules that define the constants used so far. -/
  used : NameSet := {}
  /-- Whether a terminal command already produced the report of the file. -/
  reported : Bool := false
  deriving Inhabited

@[inherit_doc Mathlib.Linter.linter.unneededImport]
def unneededImportPost (readPre : PreStateFn) (stx : Syntax) (self : UsedModules) :
    CommandElabM UsedModules := do
  unless getLinterValue linter.unneededImport (← getLinterOptions) do
    return self
  let env ← getEnv
  let mut used := self.used
  -- The node kinds of the command name their parser constants, and each constant has a
  -- defining module. This marks imports that only provide syntax, tactics, or attributes.
  for k in collectKinds stx {} do
    if let some idx := env.getModuleIdxFor? k then
      used := used.insert env.allImportedModuleNames[idx.toNat]!
  -- An option name is the only reference that a `set_option` makes to the module that declares
  -- the option, so the option table provides the defining constant of each name.
  let optionDecls ← getOptionDecls
  for i in collectIdents stx {} do
    if let some d := optionDecls.find? i then
      if let some idx := env.getModuleIdxFor? d.declName then
        used := used.insert env.allImportedModuleNames[idx.toNat]!
  if let some p := readPre declaredNames then
    for n in p.new do
      if let some ci := env.find? n then
        for c in ci.getUsedConstantsAsSet do
          if let some idx := env.getModuleIdxFor? c then
            used := used.insert env.allImportedModuleNames[idx.toNat]!
  if Parser.isTerminalCommand stx && !self.reported then
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
          let modules := if exclusive == 1 then "module" else "modules"
          m!"removing it also drops {exclusive} {modules} from the import closure"
        logLint linter.unneededImport stx
          m!"import '{m}' is possibly unneeded: the other imports cover every constant that \
            this file uses from its import closure; {impact}"
    return { used, reported := true }
  return { self with used }

@[inherit_doc Mathlib.Linter.linter.unneededImport]
public initialize unneededImport : StatefulLinter UsedModules Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ readPre => unneededImportPost readPre stx self)

end Mathlib.Linter
