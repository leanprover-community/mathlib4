/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "unusedVariableCommand" linter

The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/

open Lean Parser Elab Command

namespace Mathlib.Linter

/--
The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/
register_option linter.unusedVariableCommand : Bool := {
  defValue := true
  descr := "enable the unusedVariableCommand linter"
}

namespace UnusedVariableCommand

/--
`usedVarsRef` collects the unique names of the variables that have been used somewhere
in its `NameSet` factor and the mapping from unique names to the `Syntax` node of the
corresponding variable in its second factor.

There is an exception, though: for variables introduced with `variable ... in`, the `Syntax`
node is the whole `variable` command.
-/
initialize usedVarsRef : IO.Ref (NameSet × NameMap Syntax) ← IO.mkRef ({}, {})

/-- returns the unique `Name`, the user `Name` and the `Expr` of each `variable` that is
present in the current context. -/
def includedVariables (plumb : Bool) : TermElabM (Array (Name × Name × Expr)) := do
  let c ← read
  let fvs := c.sectionFVars
  let mut varIds := #[]
  let lctx ← getLCtx
  --dbg_trace "fvs: {fvs.toList}"
  for (a, b) in fvs do
    --dbg_trace "{(lctx.findFVar? b).isSome}: {a} --> {b}?"
    let ref ← getRef
    if (lctx.findFVar? b).isNone then
      usedVarsRef.modify fun (used, varsDict) =>
        (used, if varsDict.contains a then
          varsDict
        else
          --let rg := ref.getRange?.getD default
          --dbg_trace "ext {(rg.start, rg.stop)} with '{a.eraseMacroScopes.toString}' from {a}"
          varsDict.insert a (.ofRange (ref.getRange?.getD default)))
    if (lctx.findFVar? b).isSome then
      let mut fd := .anonymous
      for (x, y) in c.sectionVars do
        --dbg_trace "going over {x}"
        if y == a then fd := x
      varIds := varIds.push (a, fd, b)
      if plumb then
        --dbg_trace "inserting {a}"
        usedVarsRef.modify fun (used, varsDict) => (used.insert a, varsDict)
  return varIds

elab "included_variables" plumb:(ppSpace &"plumb")? : tactic => Tactic.withMainContext do
    let (_plb, usedUserIds) := (← includedVariables plumb.isSome).unzip
    let msgs ← usedUserIds.mapM fun (userName, expr) =>
      return m!"'{userName}' of type '{← Meta.inferType expr}'"
    if ! msgs.isEmpty then
      logInfo m!"{msgs.foldl (m!"{·}\n" ++ m!"* {·}") "Included variables:"}"

open Lean.Parser.Term in
/-- Return identifier names in the given bracketed binder. -/
def getBracketedBinderIds : Syntax → CommandElabM (Array Syntax)
  | `(bracketedBinderF|($ids* $[: $ty?]? $(_annot?)?)) => return ids
  | `(bracketedBinderF|{$ids* $[: $ty?]?})             => return ids
  | `(bracketedBinderF|⦃$ids* : $_⦄)                   => return ids
  | `(bracketedBinderF|[$id : $_])                     => return #[id]
  | `(bracketedBinderF|[$f])                           => return #[f]
  | _                                                  => throwUnsupportedSyntax


@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariableCommandLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedVariableCommand (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- rather than just reporting on a `Parser.isTerminalCommand`,
  -- we look inside `stx` to find a terminal command.
  -- This simplifies testing: writing `open Nat in #exit` prints the current linter output
  if (stx.find? (Parser.isTerminalCommand ·)).isSome then
    liftTermElabM do
      let (used, all) ← usedVarsRef.get
      let sorted := used.toArray.qsort (·.toString < ·.toString)
      let unused := all.toList.filter (!sorted.contains ·.1)
      for (uniq, user) in unused do
        match uniq.eraseMacroScopes with
          | .anonymous => logInfoAt user m!"'{user}' is unused"
          | x          => logInfoAt user m!"'{x}' is unused"
  --
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.variable)).isSome then
    let scope ← getScope
    let pairs := scope.varUIds.zip (← scope.varDecls.mapM getBracketedBinderIds).flatten
    --dbg_trace "pairs: {pairs}"
    usedVarsRef.modify fun (used, varsDict) => Id.run do
      let mut newVarsDict := varsDict
      for (uniq, user) in pairs do
        newVarsDict := newVarsDict.insert uniq user
      (used, newVarsDict)
  if let some decl := stx.find? (#[``declaration, `lemma].contains <|·.getKind) then
    if decl[1].isOfKind ``Lean.Parser.Command.example then
      logInfo "skipping examples: they have access to all the variables anyway"
      return
    --dbg_trace "processing: {decl[1].getKind}"
    let renStx ← stx.replaceM fun s => match s.getKind with
        | ``declId        => return some (← `(declId| $(mkIdentFrom s[0] (s[0].getId ++ `_hello))))
        | ``declValSimple => return some (← `(declValSimple| := by included_variables plumb; sorry))
        | _               => return none
    let s ← get
    elabCommand renStx
    set s

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

end Mathlib.Linter
