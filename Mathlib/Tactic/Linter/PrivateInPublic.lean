/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Meta.Tactic.TryThis
-- for `redundantOptionRanges`
public meta import Mathlib.Tactic.Linter.PrivateProof
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# The `privateInPublic` linter

This linter finds declarations which are exported *only* because they were declared with
`backward.privateInPublic` enabled, and which nothing public actually uses, and suggests deleting
the `set_option`s which export them.

This is the counterpart of the `privateProof` linter, which works per command and so cannot tell
whether the `set_option` on a *private declaration* is still needed: that depends on whether
anything else in the module still refers to it from an exporting environment. This linter answers
that question at the end of the module, once every declaration has been added.

This is a throwaway linter, intended only to drive a one-off sweep over Mathlib; it is not meant to
be enabled permanently.

## How it works

A private declaration is added to the public environment exactly when
`backward.privateInPublic` is set where it is declared (see `Lean.addDecl`); otherwise it is not
exported at all. So the candidates are the private declarations of the current module which are
present in `Environment.setExporting true`.

A candidate is *used* if it is reachable, through public positions, from a declaration of the
current module which is not itself private. A declaration's type is always a public position; for
its value we read off whether the public environment carries one. Note that this is not the same as
the body being recorded in the file: bodies are always recorded, but `Environment.setExporting true`
selects the exported view of a declaration, in which the value of an unexposed definition has been
replaced by an axiom, even in the current module. Declarations exported only because of
`backward.privateInPublic` are the exception, being exported *as is* (see `Lean.addDecl`), so their
bodies are public whether or not they are exposed — and rightly counted as such here, since a
candidate which stays exported keeps its body, and hence its references, in the public environment.

Theorem values are the one thing we do not follow, even for a private theorem exported as is. A
reference from a proof does not oblige the referenced declaration to be exported: an exported
theorem whose proof mentions an unexported private declaration is accepted.

For each unused candidate we look up its declaration range, find the command of the module
containing it, and suggest deleting the `set_option .. in`s in front of that command, exactly as
the `privateProof` linter does.

## Caveats

This linter assumes the `privateProof` linter's suggestions have already been applied: it asks only
whether anything *else* still needs the declaration to be exported, and does not check whether the
command it strips still needs the option in order to elaborate. That is almost never a concern: a
command all of whose declared names are private is elaborated in a non-exporting environment
throughout, signature and value alike (see the `withExporting` call in
`Lean.Elab.MutualDef.elabMutualDef`), so neither `abbrev` nor `@[expose]` makes any difference —
indeed `@[expose]` warns that it is meaningless on a private declaration. It can only arise for a
command declaring a public name alongside a private one, and the `privateProof` linter reports the
references responsible separately.

Deletions expose further deletions: once the last public use of an exported private declaration is
wrapped in `private`, that declaration becomes unused, and the linter suggests deleting its
`set_option` on the next run. A sweep should be iterated to a fixed point.

Note also that code actions produced by module linters are currently dropped (see the TODO in
`Lean.Elab.Command.runLintersAsync`), so the suggestions here are informational: the replacement
text and its range appear in the message, but there is no lightbulb to click.
-/

meta section

open Lean Elab Command Linter Meta.Tactic.TryThis

namespace Mathlib.Linter

/-- The `privateInPublic` linter flags declarations exported only because of
`backward.privateInPublic` which nothing public uses, and suggests deleting the `set_option`s
which export them. -/
public register_option linter.privateInPublic : Bool := {
  defValue := true
  descr := "enable the `privateInPublic` linter"
}

namespace PrivateInPublic

open Mathlib.Linter.PrivateProof (redundantOptionRanges)

/-- The constants mentioned by the public form of `n`: its type always, and its value when the
public environment records a definition with a body. -/
private def publicUses (publicEnv : Environment) (n : Name) : Array Name :=
  match publicEnv.find? n with
  | none => #[]
  | some ci =>
    let consts := ci.type.getUsedConstants
    match ci with
    | .defnInfo val => consts ++ val.value.getUsedConstants
    | .opaqueInfo val => consts ++ val.value.getUsedConstants
    | _ => consts

/-- The private declarations of the current module which are present in the public environment,
i.e. those declared with `backward.privateInPublic` enabled. -/
private def exportedPrivateNames : CommandElabM NameSet := do
  let env ← getEnv
  let publicEnv := env.setExporting true
  let mut names : NameSet := ∅
  for (n, _) in env.constants.map₂ do
    if isPrivateName n && publicEnv.contains n then
      names := names.insert n
  return names

/-- Those of `candidates` reachable from `worklist` through public positions. -/
private partial def reachable (publicEnv : Environment) (candidates : NameSet)
    (worklist : Array Name) (used : NameSet) : NameSet := Id.run do
  let some n := worklist.back? | return used
  let mut worklist := worklist.pop
  let mut used := used
  for c in publicUses publicEnv n do
    if candidates.contains c && !used.contains c then
      used := used.insert c
      worklist := worklist.push c
  return reachable publicEnv candidates worklist used

/-- The command of `cmds` containing `pos`. -/
private def commandAt? (cmds : Array Syntax) (pos : String.Pos.Raw) : Option Syntax :=
  cmds.find? fun cmd => cmd.getRange?.any (·.contains pos (includeStop := true))

/-- The main entry point of the `privateInPublic` linter. -/
private def run (cmds : Array Syntax) : CommandElabM Unit := do
  unless getLinterValue linter.privateInPublic (← getLinterOptions) do return
  if ← MonadLog.hasErrors then return
  unless (← getEnv).header.isModule do return
  let candidates ← exportedPrivateNames
  if candidates.isEmpty then return
  let env ← getEnv
  let publicEnv := env.setExporting true
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.map₂ do
    unless isPrivateName n do
      roots := roots.push n
  let used := reachable publicEnv candidates roots ∅
  let fileMap ← getFileMap
  -- The `set_option`s to delete, with the declarations which motivated deleting each of them.
  let mut deletions : Array (Lean.Syntax.Range × Array Name) := #[]
  for n in candidates do
    if used.contains n then continue
    let some declRanges ← findDeclarationRanges? n | continue
    let some cmd := commandAt? cmds (fileMap.ofPosition declRanges.range.pos) | continue
    for range in redundantOptionRanges cmd do
      if let some i := deletions.findIdx? (·.1 == range) then
        deletions := deletions.modify i fun (r, names) => (r, names.push n)
      else
        deletions := deletions.push (range, #[n])
  for (range, names) in deletions do
    let names := String.intercalate ", " <| names.toList.map fun n => s!"`{privateToUserName n}`"
    liftCoreM <| addSuggestion (Syntax.ofRange range)
      { suggestion := .string "", messageData? := m!"(delete)" }
      (origSpan? := Syntax.ofRange range)
      (header := s!"{names} exported only because of this `set_option`, but nothing public uses \
        it; delete it:")

/-- The `privateInPublic` linter proper: see the module docstring. -/
initialize addModuleLinter { run, name := `Mathlib.Linter.privateInPublic }

end PrivateInPublic

end Mathlib.Linter
