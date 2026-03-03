/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Init
public import ImportGraph.Tools.FindHome

/-! # The `classReturningDef` linter

If a definition returns a class, then it should be marked `reducible` or `implicit_reducible`.
-/

open Lean Meta Elab Command Linter Mathlib.Command.MinImports

meta section

namespace Mathlib.Linter

/-- A linter warning if a definition outputs a class but is not marked reducible. -/
def classReturningDef : Linter where
  name := `classReturningDef
  run stx := do
    let declName ← getDeclName stx
    -- Skip if either reducible/abbrev or implicit_reducible
    if (← Lean.isReducible declName) ||
        (← Lean.isImplicitReducible declName) then
      return
    let env ← getEnv
    let some decl := env.find? declName | return
    match decl with
    | .defnInfo defInfo =>
        -- Inspect the type inside TermElabM
        Lean.Elab.Command.liftTermElabM do
          let type ← inferType defInfo.value
          let resultType := type.getAppFn
          match resultType with
          | Expr.const typeName _ =>
              let typeExpr := mkConst typeName
              if (← isClass? typeExpr).isSome then
                log m!"definition `{declName}` returns the class `{typeName}` but is not \
                  marked @[reducible] or @[implicit_reducible]. \
                  Consider marking it @[implicit_reducible]."
          | _ => return
    | _ => return

initialize addLinter classReturningDef

end Mathlib.Linter

end
