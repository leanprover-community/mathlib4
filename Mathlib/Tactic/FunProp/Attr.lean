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

syntax (name:=fun_prop) "fun_prop" ident* : attr

/-- Initialization of `funProp` attribute -/
initialize
  registerBuiltinAttribute {
    name  := `fun_prop
    descr := funPropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
       match stx with
       | `(attr| fun_prop $xs:ident*) =>
         discard <| MetaM.run do
         let info ← getConstInfo declName
         forallTelescope info.type fun _ b => do
           let outArgNames := xs.map (·.getId)
           if b.isProp then
             addFunPropDecl declName outArgNames
           else
             addTheorem declName attrKind
       | _ =>
         Elab.throwUnsupportedSyntax
    erase := fun _declName =>
      throwError "can't remove `funProp` attribute (not implemented yet)"
  }

end Meta.FunProp

end Mathlib
