/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Additions to the delaborator
-/

namespace Lean.PrettyPrinter.Delaborator

open Lean.Meta Lean.SubExpr SubExpr

namespace SubExpr

variable {α : Type} [Inhabited α]
variable {m : Type → Type} [Monad m]

section Descend

variable [MonadReaderOf SubExpr m] [MonadWithReaderOf SubExpr m]
variable [MonadLiftT MetaM m] [MonadControlT MetaM m]
variable [MonadLiftT IO m]

/-- Assuming the current expression is a lambda or pi,
descend into the body using the given name `n` for the username of the fvar.
Provides `x` with the fresh fvar for the bound variable.
See also `Lean.PrettyPrinter.Delaborator.SubExpr.withBindingBody`. -/
def withBindingBody' (n : Name) (x : Expr → m α) : m α := do
  let e ← getExpr
  Meta.withLocalDecl n e.binderInfo e.bindingDomain! fun fvar =>
    descend (e.bindingBody!.instantiate1 fvar) 1 (x fvar)

end Descend

end SubExpr

/-- Assuming the current expression in a lambda or pi,
descend into the body using an unused name generated from the binder's name.
Provides `d` with both `Syntax` for the bound name as an identifier
as well as the fresh fvar for the bound variable.
See also `Lean.PrettyPrinter.Delaborator.withBindingBodyUnusedName`. -/
def withBindingBodyUnusedName' {α} (d : Syntax → Expr → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  let stxN ← annotateCurPos (mkIdent n)
  withBindingBody' n <| d stxN

/-- Update `OptionsPerPos` at the given position, setting the key `n`
to have the boolean value `v`. -/
def OptionsPerPos.setBool (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool) :
    OptionsPerPos :=
  let e := opts.findD p {} |>.setBool n v
  opts.insert p e
