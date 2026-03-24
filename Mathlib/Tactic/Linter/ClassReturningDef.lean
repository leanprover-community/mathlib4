/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.MinImports

/-! # The `classReturningDef` linter

If a definition returns a class (possibly after binders),
then it should be marked `reducible` or `implicit_reducible`.
-/

open Lean Meta Elab Command Linter Mathlib.Command.MinImports

meta section

namespace Mathlib.Linter

public register_option linter.classReturningDef : Bool := {
  defValue := true
  descr := "enable the classReturningDef linter"
}

/-- Returns `true` if the type (after removing binders) is a class. -/
private def returnsClass (type : Expr) : MetaM Bool := do
  forallTelescopeReducing type fun _ body => do
    match body.getAppFn with
    | Expr.const typeName _ =>
        -- Ignore `Setoid`
        if typeName == ``Setoid || typeName == ``Decidable || typeName == `Fintype then
          return false
        let typeExpr := mkConst typeName
        return (← isClass? typeExpr).isSome
    | _ =>
        return false

/-- A linter warning if a definition outputs a class
    (possibly after parameters) but is not marked reducible. -/
def classReturningDefLinter : Linter where
  name := `classReturningDef
  run stx := do
    unless Linter.getLinterValue linter.classReturningDef (← getLinterOptions) do
      return
    let declName ← getDeclName stx
    -- Skip if reducible / implicit_reducible / abbrev
    if (← Lean.isReducible declName) ||
        (← Lean.isImplicitReducible declName) then
      return

    let env ← getEnv
    let some decl := env.find? declName | return

    match decl with
    | .defnInfo defInfo =>
        Lean.Elab.Command.liftTermElabM do
          let type ← inferType defInfo.value
          if (← returnsClass type) then
            log m!"definition `{declName}` returns a class \
                  but is not marked @[reducible] or @[implicit_reducible].\n\
                  Consider marking it @[implicit_reducible]. \n\
                  Otherwise, use `set_option linter.classReturningDef false` inside a section \
                  enclosing the definition to disable the linter."
    | _ => return

initialize addLinter classReturningDefLinter

end Mathlib.Linter

end
