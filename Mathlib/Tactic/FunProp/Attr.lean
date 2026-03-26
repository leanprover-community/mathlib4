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

/-- Attribute for marking `fun_prop` definitions and theorems.

For `fun_prop` definition like `HasFDerivAt` you can additionally specify the output argument `f'`
as `fun_prop out f'`. With this `fun_prop` can solve `HasFDerivAt f ?f' x` by filling the
metavariable `?f'` first and then proving the proposition.  -/
syntax (name:=fun_prop) "fun_prop" (&"out" ident*)? : attr

/-- Initialization of `funProp` attribute -/
initialize
  registerBuiltinAttribute {
    name  := `fun_prop
    descr := funPropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
       match stx with
       | `(attr| fun_prop $[out $xs:ident*]?) =>
         discard <| MetaM.run do
         let info ← getConstInfo declName
         forallTelescope info.type fun _ b => do
           let outArgNames := (xs.getD #[]).map (·.getId)
           if b.isProp then
             addFunPropDecl declName outArgNames
           else
             if xs.isSome then
               throwError "Can not specify output arguments on a theorem!"
             addTheorem declName attrKind
       | _ =>
         Elab.throwUnsupportedSyntax
    erase := fun _declName =>
      throwError "can't remove `funProp` attribute (not implemented yet)"
  }

end Meta.FunProp

end Mathlib
