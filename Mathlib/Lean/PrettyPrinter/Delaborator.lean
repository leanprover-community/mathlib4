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

end SubExpr

/-- Assuming the current expression in a lambda or pi,
descend into the body using an unused name generated from the binder's name.
Provides `d` with both `Syntax` for the bound name as an identifier
as well as the fresh fvar for the bound variable.
See also `Lean.PrettyPrinter.Delaborator.withBindingBodyUnusedName`. -/
def withBindingBodyUnusedName' {α} (d : Syntax → Expr → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)

/-- Update `OptionsPerPos` at the given position, setting the key `n`
to have the boolean value `v`. -/
def OptionsPerPos.setBool (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool) :
    OptionsPerPos :=
  let e := opts.findD p {} |>.setBool n v
  opts.insert p e
