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

/-- The attribute `fun_prop` is used to marks function property definitions like `Continuous`
and function property theorems like `Continuous.comp`.

Option `always_try_transition`: some definitions can have `@[fun_prop always_try_transition]`

  By default, for performance reasons, `fun_prop` applies transition theorems like
  `Differentiable ℝ f → Continuous f` only on functions that can not be further decomposed
  (i.e. written at `f ∘ g` for nontrivial `f` and `g`). This option allows to apply transition
  theorems at any stage of the proof search.

  This option is important for some function properties like `Integrable` as it does not have
  general composition theorem stating `Integrable f → Integrable g → Integrable (f ∘ g)` and
  very often integrability can be inferred from continuity. Therefore we might want to apply,
  `IsCompact s → ContinuousOn f s → IntegrableOn f s` very early on.-/
syntax (name := fun_prop) "fun_prop" (&"always_try_transition")? : attr


@[inherit_doc fun_prop]
initialize
  registerBuiltinAttribute {
    name  := `fun_prop
    descr := funPropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
       discard <| MetaM.run do
       let alwaysTryTransition :=
         match stx with
         | `(attr| fun_prop always_try_transition) => true | _ => false
       let info ← getConstInfo declName
       forallTelescope info.type fun _ b => do
         if b.isProp then
           addFunPropDecl declName alwaysTryTransition
         else
           addTheorem declName attrKind
    erase := fun _declName =>
      throwError "can't remove `funProp` attribute (not implemented yet)"
  }

end Meta.FunProp

end Mathlib
