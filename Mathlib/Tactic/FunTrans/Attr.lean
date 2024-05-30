/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Mathlib.Tactic.FunTrans.Decl
import Mathlib.Tactic.FunTrans.Theorems

/-!
## `funTrans` attribute
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunTrans


private def funTransHelpString : String :=
"`funTrans` tactic to compute function transformations like `fderiv` or `adjoint`"

/-- Initialization of `funTrans` attribute -/
initialize funTransAttr : Unit ←
  registerBuiltinAttribute {
    name  := `fun_trans
    descr := funTransHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx attrKind =>
       discard <| MetaM.run do
       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do
         if b.isEq then
           addTheorem declName attrKind
         else
           addFunTransDecl declName
    erase := fun _declName =>
      throwError "can't remove `funTrans` attribute (not implemented yet)"
  }
