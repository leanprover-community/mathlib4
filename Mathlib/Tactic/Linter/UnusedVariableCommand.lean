/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Mathlib.Tactic.Linter.DeclaredNames

/-! # The `unusedVariableCommand` linter

The `unusedVariableCommand` linter tracks the binders of `variable` commands per scope. It
marks a binder as used when a declaration of the scope binds the same user-facing name in its
leading telescope, with the exact declaration list of each command from the `declaredNames`
producer. It reports binders with no use when their scope closes, and at the end of the file.

Usage marking has two sources: the leading binder names of the declarations that each command
adds to the environment, and the identifier occurrences in each command's syntax. The second
source covers `example` commands and notations, which add no declaration. Identifier matching
is by name, so an unrelated identifier with the name of a binder also marks it: the linter
prefers false negatives to false positives.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Enables the prototype `unusedVariableCommand` linter. -/
public register_option linter.unusedVariableCommand : Bool := {
  defValue := false
  descr := "enable the unusedVariableCommand linter"
}

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

/-- Collects the identifier names of a syntax tree. -/
partial def collectIdents (s : Syntax) (acc : NameSet) : NameSet :=
  if s.isIdent then acc.insert s.getId.eraseMacroScopes
  else s.getArgs.foldl (fun a c => collectIdents c a) acc

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
  -- Mark binders used by the declarations of this command. Identifier occurrences in the
  -- command syntax also mark binders: this covers `example` commands and notations, which add
  -- no declaration to the environment. Binder-management commands do not count as usage.
  let mut usedNames : NameSet := {}
  unless #[``Lean.Parser.Command.variable, ``Lean.Parser.Command.omit,
      ``Lean.Parser.Command.include].contains stx.getKind do
    usedNames := collectIdents stx usedNames
  if let some p := readPre declaredNames then
    let env ← getEnv
    for n in p.new do
      if let some ci := env.find? n then
        usedNames := leadingBinderNames ci.type |>.foldl (·.insert ·) usedNames
  if true then
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

end Mathlib.Linter
