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

def fulfillBodyPromises (trees : PersistentArray InfoTree)
    (bodies : NameMap (IO.Promise BodyWithContext)) :
    BaseIO (Array (Option Name × BodyWithContext)) := do
  let mut extraBodies := #[]
  for t in trees do
    extraBodies ← t.foldDeclBodyInfosM (init := extraBodies) fun body ctx info extra => do
      if let some name := ctx.parentDecl? then
        if let some p := bodies.get? name then
          p.resolve { body, ctx, info : BodyWithContext }
          return extra
        else
          return extra.push (some name, { body, ctx, info : BodyWithContext })
      else
        return extra.push (none, { body, ctx, info : BodyWithContext })
  return extraBodies

def fulfillBodyPromisesAsync (trees : PersistentArray InfoTree)
    (bodies : NameMap (IO.Promise BodyWithContext)) :
    BaseIO (Task (Array (Option Name × BodyWithContext))) :=
  BaseIO.asTask <| fulfillBodyPromises trees bodies

def runDeclarationLintersAsync (cmd : Syntax) : CommandElabM Unit := do
  let some pos := cmd.getPos? | throwError "Could not find position for syntax:{indentD cmd}"
  let env ← getEnv
  let decls := pos.getDeclsAfter env (← getFileMap)
  let mut data : Declarations := {}
  let mut bodies : NameMap (IO.Promise BodyWithContext) := {}
  for decl in decls do
    -- TODO: replace with just `isAutoDecl` after batteries#1831
    let isAuto ← pure (isReservedName (← getEnv) decl) <||>
      liftCoreM (Batteries.Tactic.Lint.isAutoDecl (privateToUserName decl))
    let body ← IO.Promise.new
    bodies := bodies.insert decl body
    data := data.insert decl { name := decl, body := body.result?, isAuto : DeclarationData }
  -- Should we special case `example` instead here? I suspect not...
  let extraBodiesTask ← fulfillBodyPromisesAsync (← getInfoTrees) bodies

  let declLinters := sorry
  -- for linter in declLinters do
  --   sorry
    -- try linter cmd decls catch _ => finally (reset)
