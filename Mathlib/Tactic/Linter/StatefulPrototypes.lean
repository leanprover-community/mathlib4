/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import ImportGraph.Imports.ImportGraph
public meta import ImportGraph.Graph.TransitiveClosure
public import Mathlib.Init

/-! # Prototype stateful linters: declared-names producer, unused `variable`, unneeded imports

This file is an experiment. It contains three stateful linters:

* `declaredNames` is a producer. Its pre phase computes the names that the current command
  declares, as a diff of `env.constants.map₂` against the names seen so far.
* `unusedVariableCommand` tracks the binders of `variable` commands per scope. It marks a
  binder as used when a new declaration binds the same user-facing name in its leading
  telescope. It reports binders with no use when their scope closes.
* `unneededImport` accumulates the defining modules of all constants that the declarations of
  the file use. At the end of the file, it reports direct imports whose import closure
  contains none of the used modules.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Enables the prototype `unusedVariableCommand` linter. -/
public register_option linter.unusedVariableCommand : Bool := {
  defValue := false
  descr := "enable the unusedVariableCommand linter"
}

/-- Enables the prototype `unneededImport` linter. -/
public register_option linter.unneededImport : Bool := {
  defValue := false
  descr := "enable the unneededImport linter"
}

/-- Persistent state of the `declaredNames` producer: the local constants seen so far. -/
public structure DeclaredSeen where
  /-- The names of `env.constants.map₂` entries that earlier commands declared. -/
  seen : NameSet := {}
  deriving Inhabited

/-- Pre-phase payload of the `declaredNames` producer: the constants of the current command. -/
public structure DeclaredNew where
  /-- The names that the current command added to the environment. -/
  new : Array Name := #[]
  deriving Inhabited

/--
The `declaredNames` producer computes the names that each command declares, as an exact
environment diff. Consumers read the payload with `readCurrentPreState`.
-/
public initialize declaredNames : StatefulLinter DeclaredSeen DeclaredNew ←
  registerStatefulLinter {}
    (pre := fun _ self _ => do
      let env ← getEnv
      let mut new := #[]
      for (n, _) in env.constants.map₂ do
        unless self.seen.contains n do
          new := new.push n
      return some { new })
    (post := fun _ self selfPre _ _ => do
      let some p := selfPre | return self
      return { seen := p.new.foldl (·.insert ·) self.seen })

/-! ### Unused `variable` linter -/

/-- One tracked binder of a `variable` command. -/
public structure VarEntry where
  /-- The user-facing binder name. -/
  name : Name
  /-- The binder ident, for the position of the warning. -/
  stx : Syntax
  /-- `true` when some declaration used the binder. -/
  used : Bool := false
  deriving Inhabited

/-- Persistent state of the `unusedVariableCommand` linter: tracked binders per scope level,
outermost first, and the count of `varDecls` already processed per level. -/
public structure UnusedVarState where
  /-- The tracked binders, one array per scope level (outermost first). -/
  levels : Array (Array VarEntry) := #[]
  /-- For each level, the number of `varDecls` entries already registered. -/
  counts : Array Nat := #[]
  deriving Inhabited

/-- Extracts the named binder idents of a `bracketedBinder`. Anonymous instance binders
yield nothing. -/
def binderIdents (b : Syntax) : Array Syntax :=
  let k := b.getKind
  if k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder ||
     k == ``Lean.Parser.Term.strictImplicitBinder then
    b[1].getArgs.filter (·.isIdent)
  else if k == ``Lean.Parser.Term.instBinder then
    -- `[name : Type]` has an ident in slot 1; `[Type]` does not.
    b[1].getArgs.filter (·.isIdent)
  else
    #[]

/-- Collects the binder names of the leading `∀`-telescope of `e`. -/
def leadingBinderNames (e : Expr) : NameSet :=
  go e {}
where
  go : Expr → NameSet → NameSet
    | .forallE n _ b _, acc => go b (acc.insert n.eraseMacroScopes)
    | .lam n _ b _, acc => go b (acc.insert n.eraseMacroScopes)
    | _, acc => acc

/-- Reports the unused entries of `lvl`. -/
def reportUnused (lvl : Array VarEntry) : CommandElabM Unit := do
  for v in lvl do
    unless v.used do
      logLint linter.unusedVariableCommand v.stx
        m!"variable '{v.name}' is never used in this scope"

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariablePost (readPre : PreStateFn) (stx : Syntax) (self : UnusedVarState) :
    CommandElabM UnusedVarState := do
  unless getLinterValue linter.unusedVariableCommand (← getLinterOptions) do
    return self
  let scopes := (← getScopes).toArray.reverse  -- outermost first
  let mut levels := self.levels
  let mut counts := self.counts
  -- Scope pops: report and drop the popped levels.
  if scopes.size < levels.size then
    for lvl in levels[scopes.size:] do
      reportUnused lvl
    levels := levels.extract 0 scopes.size
    counts := counts.extract 0 scopes.size
  -- Scope pushes: add empty levels.
  while levels.size < scopes.size do
    levels := levels.push #[]
    -- A new scope inherits the `varDecls` of its parent: start the count at the parent's size.
    let parentVarCount := if levels.size ≥ 2 then scopes[levels.size - 2]!.varDecls.size else 0
    counts := counts.push parentVarCount
  -- Register new binders per level. A `variable (x)` annotation update rebuilds binder
  -- groups with the original ident syntax: registration skips idents that some live level
  -- already tracks at the same position.
  let tracked : Std.HashSet (Name × String.Pos.Raw) := levels.foldl (init := {}) fun acc lvl =>
    lvl.foldl (init := acc) fun acc v => acc.insert (v.name, v.stx.getPos?.getD 0)
  for i in [0:scopes.size] do
    let vds := scopes[i]!.varDecls
    if counts[i]! < vds.size then
      let mut lvl := levels[i]!
      for b in vds[counts[i]!:] do
        for id in binderIdents b.raw do
          let key := (id.getId.eraseMacroScopes, id.getPos?.getD 0)
          unless tracked.contains key do
            lvl := lvl.push { name := key.1, stx := id }
      levels := levels.set! i lvl
      counts := counts.set! i vds.size
  -- Mark binders used by the declarations of this command.
  if let some p := readPre declaredNames then
    let env ← getEnv
    let mut usedNames : NameSet := {}
    for n in p.new do
      if let some ci := env.find? n then
        usedNames := leadingBinderNames ci.type |>.foldl (·.insert ·) usedNames
    if !usedNames.isEmpty then
      levels := levels.map fun lvl =>
        lvl.map fun v => if usedNames.contains v.name then { v with used := true } else v
  -- End of file: report every remaining level.
  if Parser.isTerminalCommand stx then
    for lvl in levels do
      reportUnused lvl
    return {}
  return { levels, counts }

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
public initialize unusedVariableCommand : StatefulLinter UnusedVarState Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ readPre => unusedVariablePost readPre stx self)

/-! ### Unneeded import linter -/

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
