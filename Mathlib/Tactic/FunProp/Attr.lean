/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Tactic.FunProp.Decl
public import Mathlib.Tactic.FunProp.Theorems

/-!
## `funProp` attribute
-/

public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

private def funPropHelpString : String :=
"`fun_prop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`"

syntax (name := fun_prop) "fun_prop" (&"always_try_transition")? : attr


/-- Initialization of `funProp` attribute -/
initialize
  registerBuiltinAttribute {
    name  := `fun_prop
    descr := funPropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
       discard <| MetaM.run do
       let eagerTransition :=
         match stx with
         | `(attr| fun_prop always_try_transition) => true | _ => false
       let info ← getConstInfo declName
       forallTelescope info.type fun _ b => do
         if b.isProp then
           addFunPropDecl declName eagerTransition
         else
           addTheorem declName attrKind
    erase := fun _declName =>
      throwError "can't remove `funProp` attribute (not implemented yet)"
  }

end Meta.FunProp

end Mathlib
