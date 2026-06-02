module

public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Command
public import Mathlib.Lean.Elab.InfoTree

open Lean Elab Command Term InfoTree

namespace Mathlib.Tactic.Linter

public section

structure BodyWithContext where
  body : Body
  ctx  : ContextInfo
  info : Info

structure DeclarationData where
  name : Name
  bodyCtx : Option BodyWithContext := none
  isAuto : Bool

abbrev Declarations := NameMap DeclarationData

abbrev DeclarationM := ReaderT Declarations CommandElabM

def Declarations.setBodyWithContext (body : Body) (ctx : ContextInfo) (info : Info) (name : Name)
    (decls : Declarations) : Declarations :=
  decls.alter name fun
    | none => none
    | some data => some { data with bodyCtx := some { body, ctx, info } }

-- Could instead pass one declaration in at a time, but why restrict ourselves?
structure DeclarationLinter where
  run : Syntax → DeclarationM Unit

partial def _root_.Lean.Syntax.isExample : Syntax → Bool
  | `(command| $_ in $cmd) => cmd.raw.isExample
  | decl => decl.isOfKind ``Parser.Command.declaration &&
    decl[1].isOfKind ``Parser.Command.«example»
