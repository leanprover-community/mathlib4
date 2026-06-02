module

public import Batteries.Tactic.Lint.Basic
public meta import Batteries.Lean.Position
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Command
public meta import Mathlib.Tactic.Linter.Declaration.Types
meta import Mathlib.Lean.Elab.InfoTree

open Lean Elab Command Term

namespace Mathlib.Tactic.Linter

public meta section

def runDeclarationLinters (cmd : Syntax) : CommandElabM Unit := do
  let some pos := cmd.getPos? | throwError "Could not find position for syntax:{indentD cmd}"
  let env ← getEnv
  let decls := pos.getDeclsAfter env (← getFileMap)
  let mut data : Declarations ← decls.foldlM (init := {}) fun acc name => do
    -- TODO: replace with just `isAutoDecl` after batteries#1831
    let isAuto ← pure (isReservedName (← getEnv) name) <||>
      liftCoreM (Batteries.Tactic.Lint.isAutoDecl (privateToUserName name))
    return acc.insert name { name, isAuto : DeclarationData }
  -- Special-case `example`
  if cmd.isExample then
    data := data.insert `_example { name := `_example, isAuto := false }
  for t in ← getInfoTrees do
    data := t.foldDeclBodyInfos (init := data) fun body ctx info data =>
      if let some name := ctx.parentDecl? then
        data.setBodyWithContext body ctx info name
      else
        data
  let declLinters := sorry
  for linter in declLinters do
    try linter cmd decls catch _ => finally (reset)
