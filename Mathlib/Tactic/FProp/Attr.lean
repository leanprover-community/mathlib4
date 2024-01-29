/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Mathlib.Tactic.FProp.Decl
import Mathlib.Tactic.FProp.Theorems

namespace Mathlib
open Lean Meta

namespace Meta.FProp

/-- -/
def isLambdaRule (f : Expr) : MetaM Bool :=
  match f with
  | .lam _ _ xBody _ =>
    let fn := xBody.getAppFn
    if fn.isConst then
      return false
    else
      return true
  | .fvar .. => do
    if (← inferType f).forallArity ≥ 2 then
      return true
    else
      return false
  | _ => return false


-- TODO: add support for specifying priority and discharger
-- open Lean.Parser.Tactic
-- syntax (name:=Attr.fprop) "fprop" (prio)? (discharger)? : attr

def fpropHelpString : String :=
"`fprop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap` ..."

initialize fpropAttr : Unit ←
  registerBuiltinAttribute {
    name  := `fprop
    descr := fpropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx attrKind =>
       discard <| MetaM.run do
       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do
         if b.isProp then
           addFPropDecl declName none
         else
           addTheorem declName attrKind
    erase := fun _declName =>
      throwError "can't remove `fprop` attribute (not implemented yet)"
  }
