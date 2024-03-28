/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Basic

import Mathlib.Tactic.FunProp.ToStd

/-!
## `fun_prop` Environment extension that stores all registered morphism coercions.
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp


private local instance : Ord Name := ⟨Name.quickCmp⟩


/-- Environment extension storing all morphism coercions. -/
initialize morCoeDeclsExt : SimpleScopedEnvExtension Name (Std.RBSet Name compare) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := .ofArray #[`DFunLike.coe] _
    addEntry := fun d n => d.insert n
  }


/-- Register morphism coercion. -/
def addMorCoeDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName
  let type := info.type

  forallTelescope type fun xs b => do

  let n := xs.size

  -- coercion needs at least two arguments
  if n < 2 then throwError "invalid morphism coercion, expecting function of at least two arguments"

  let x := xs[n-1]!
  let f := xs[n-2]!
  if ¬(← x.fvarId!.getBinderInfo).isExplicit ||
     ¬(← f.fvarId!.getBinderInfo).isExplicit then
    throwError "invalid morphism coercion, last two argumets are expected to be explicit"

  modifyEnv fun env => morCoeDeclsExt.addEntry env declName

  trace[Meta.Tactic.fun_prop.attr]
    "registered new morphism coercion `{declName}`
     morphism: {← ppExpr f} : {← ppExpr (← inferType f)}
     argument: {← ppExpr x} : {← ppExpr (← inferType x)}
     return value: {← ppExpr b}"


/-- Initialization of `fun_prop_coe` attribute -/
initialize morCoeAttr : Unit ←
  registerBuiltinAttribute {
    name  := `fun_prop_coe
    descr := "registers morphism coercion for `fun_prop` and `fun_trans` tactics"
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx _attrKind =>
       discard <| MetaM.run do
       addMorCoeDecl declName
    erase := fun _declName =>
      throwError "can't remove `fun_prop_coe` attribute (not implemented yet)"
  }
