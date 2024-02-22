/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Mathlib.Tactic.FunProp.Decl
import Mathlib.Tactic.FunProp.Theorems

/-!
## `funProp` attribute
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp

-- TODO: add support for specifying priority and discharger
-- open Lean.Parser.Tactic
-- syntax (name:=Attr.funProp) "funProp" (prio)? (discharger)? : attr

private def funPropHelpString : String :=
"`funProp` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`"

/-- Initialization of `funProp` attribute -/
initialize funPropAttr : Unit ←
  registerBuiltinAttribute {
    name  := `fun_prop
    descr := funPropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx attrKind =>
       discard <| MetaM.run do
       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do
         if b.isProp then
           addFunPropDecl declName
         else
           addTheorem declName attrKind
    erase := fun _declName =>
      throwError "can't remove `funProp` attribute (not implemented yet)"
  }
