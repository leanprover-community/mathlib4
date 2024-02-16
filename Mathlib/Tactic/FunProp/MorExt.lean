/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Alter

import Mathlib.Tactic.LiftLets

/-!
## `funProp` environment extension that stores all registered coercions from a morphism to a function
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


private local instance : Ord Name := ⟨Name.quickCmp⟩

/-- -/
initialize morCoeDeclsExt : SimpleScopedEnvExtension Name (Std.RBSet Name compare) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d n => d.insert n
  }


/-- -/
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


/-- Initialization of `funProp` attribute -/
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


def isMorCoe (name : Name) : CoreM Bool := do
  return morCoeDeclsExt.getState (← getEnv) |>.contains name

structure MorApp where
  coe : Expr
  fn  : Expr
  arg : Expr


def isMorApp? (e : Expr) : CoreM (Option MorApp) := do

  let .app (.app coe f) x := e | return none
  let .some n := coe.getAppFn.constName? | return none

  if ← isMorCoe n then
    return .some { coe := coe, fn := f, arg := x }
  else
    return none


partial def morWhnfPred (e : Expr) (pred : Expr → MetaM Bool) (cfg : WhnfCoreConfig := {}) : MetaM Expr := do
  whnfEasyCases e fun e => do
    let e ← whnfCore e cfg

    if let .some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← morWhnfPred f pred cfg
      if cfg.zeta then
        return (coe.app f).app x
      else
        return ← f.liftLets fun xs f' =>
          mkLambdaFVars xs ((coe.app f').app x)

    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => morWhnfPred e pred cfg
        | none   => return e
    else
      return e


def morWhnf (e : Expr)  (cfg : WhnfCoreConfig := {}) : MetaM Expr := morWhnfPred e (fun _ => return false) cfg
