/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Tactic.FProp.FPropDecl
import Mathlib.Tactic.FProp.FPropLambdaTheorems
import Mathlib.Tactic.FProp.FPropTheorems

namespace Mathlib
open Lean Meta

namespace Meta.FProp

def isLambdaRule (f : Expr) : Bool :=
  match f with
  | .lam _ _ xBody _ => 
    let fn := xBody.getAppFn
    if fn.isConst then 
      false
    else 
      true
  | .const _ _ => false
  | _ => true

open Lean Qq Meta Elab Term in
initialize fpropAttr : TagAttribute ←
  registerTagAttribute
    `fprop
    "Attribute to tag the basic rules for a function property." 
    (validate := fun declName => discard <| MetaM.run do
       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do
         if b.isProp then
           addFPropDecl declName none
         else
           let .some (_, f) ← getFProp? b
             | throwError "unrecognized fprop"

           if isLambdaRule f then
             addLambdaTheorem declName
           else
             addTheorem declName .global 1000)
      
      

  
  

