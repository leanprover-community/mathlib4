/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public meta import Mathlib.Tactic.Linter.DeclaredNames

/-! # The `openScoped` linter

The `openScoped` linter suggests `open scoped Foo` for a plain `open Foo` when the scope uses
the namespace only through its scoped declarations, such as scoped notation. The suggestion
keeps the scoped activations and withdraws unqualified name resolution.

Evidence has three sources. Syntax node kinds with the namespace as prefix show scoped usage:
the parsers of scoped notation live in their namespace. Constants of the namespace in the
declarations of the scope, and alias matches, show name resolution. A possible-resolution
guard suppresses the suggestion when any identifier of the scope could name a member of the
namespace: resolution through an open implies that the composed name exists, so an existence
check needs no resolution provenance.

The linter tracks only plain `open` commands with single-component namespaces. It skips
`open scoped`, `open ... (...)`, hiding and renaming forms, and relative opens such as the
`Meta` in `open Lean Meta`. A sweep over mathlib measured 98% precision for the suggestion;
the residual false positives come from name resolution in positions that produce no
declaration, such as attribute targets.
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The `openScoped` linter suggests `open scoped` for namespaces that a scope uses only
through scoped declarations. -/
public register_option linter.openScoped : Bool := {
  defValue := false
  descr := "enable the openScoped linter"
}

/-- One tracked namespace of a plain `open` command. -/
public structure OpenScopedEntry where
  /-- The namespace, as written. -/
  ns : Name
  /-- The ident of the namespace, for the position of the suggestion. -/
  stx : Syntax
  /-- `true` when the scope shows evidence of name resolution through the namespace. -/
  resolved : Bool := false
  /-- `true` when the scope used a scoped declaration of the namespace. -/
  scopedUse : Bool := false
  deriving Inhabited

/-- Persistent state of the `openScoped` linter: tracked entries per scope level. -/
public structure OpenScopedState where
  /-- Tracked entries per scope level, outermost first. -/
  levels : Array (Array OpenScopedEntry) := #[]
  deriving Inhabited

/-- Collects the identifier names of a syntax tree. -/
private partial def idents (s : Syntax) (acc : NameSet) : NameSet :=
  if s.isIdent then acc.insert s.getId.eraseMacroScopes
  else s.getArgs.foldl (fun a c => idents c a) acc

/-- Collects the node kinds of a syntax tree. -/
private partial def kinds (s : Syntax) (acc : NameSet) : NameSet :=
  let acc := if s.isOfKind `null ∨ s.isIdent ∨ s.isAtom then acc else acc.insert s.getKind
  s.getArgs.foldl (fun a c => kinds c a) acc

@[inherit_doc Mathlib.Linter.linter.openScoped]
def openScopedPost (readPre : PreStateFn) (stx : Syntax) (self : OpenScopedState) :
    CommandElabM OpenScopedState := do
  unless getLinterValue linter.openScoped (← getLinterOptions) do
    return self
  let report (lvl : Array OpenScopedEntry) : CommandElabM Unit := do
    for e in lvl do
      if e.scopedUse && !e.resolved then
        logLint linter.openScoped e.stx
          m!"namespace '{e.ns}' is used only through scoped declarations: \
            consider 'open scoped {e.ns}'"
  let scopes := (← getScopes).toArray.reverse
  let mut levels := self.levels
  if scopes.size < levels.size then
    for lvl in levels[scopes.size:] do report lvl
    levels := levels.extract 0 scopes.size
  while levels.size < scopes.size do
    levels := levels.push #[]
  let env ← getEnv
  -- Track a plain `open Foo Bar` command: single-component names only.
  if stx.isOfKind ``Lean.Parser.Command.open &&
      stx[1].getKind == ``Lean.Parser.Command.openSimple then
    let ids := stx[1].getArgs.foldl (init := #[]) fun acc a =>
      if a.isIdent then acc.push a else acc ++ a.getArgs.filter (·.isIdent)
    let i := scopes.size - 1
    let mut lvl := levels[i]!
    for id in ids do
      let n := id.getId.eraseMacroScopes
      if n.components.length == 1 then
        lvl := lvl.push { ns := n, stx := id }
    levels := levels.set! i lvl
  else
    -- The possible-resolution guard. The `open` command itself is exempt, so the namespace
    -- ident does not suppress its own entry.
    let names := idents stx {}
    levels := levels.map fun lvl => lvl.map fun e =>
      if e.resolved then e
      else if names.any (fun x =>
          let full := e.ns ++ x
          env.contains full ∨ !(getAliases env full false).isEmpty) then
        { e with resolved := true }
      else e
  let ks := kinds stx {}
  levels := levels.map fun lvl => lvl.map fun e =>
    if e.scopedUse then e
    else if ks.any (fun k => e.ns.isPrefixOf k) then { e with scopedUse := true } else e
  if let some p := readPre declaredNames then
    let mut consts : NameSet := {}
    for n in p.new do
      if let some ci := env.find? n then
        consts := ci.getUsedConstantsAsSet.foldl (·.insert ·) consts
    if !consts.isEmpty then
      levels := levels.map fun lvl => lvl.map fun e =>
        if e.resolved then e
        else if consts.any (fun c => e.ns.isPrefixOf c) then { e with resolved := true }
        else e
  if Parser.isTerminalCommand stx then
    for lvl in levels do report lvl
    return {}
  return { levels }

@[inherit_doc Mathlib.Linter.linter.openScoped]
public initialize openScopedLinter : StatefulLinter OpenScopedState Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ _ readPre => openScopedPost readPre stx self)

end Mathlib.Linter
