/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Lean.Elab

open Lean Meta

#check show_term_elab 1

elab "fast_instance%" arg:term : term <= expectedType => do
  let .some className ← Lean.Meta.isClass? expectedType |
    throwError "Can only be used for classes"
  let ctor := Lean.getStructureCtor (← getEnv) className
  let provided ← Lean.Elab.Term.elabTermEnsuringType arg (some expectedType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

  -- TODO: withNewMCtxDepth do
  -- create universe variables
  let levels ← Meta.mkFreshLevelMVarsFor (.ctorInfo ctor)
  let mut e := Expr.const ctor.name levels
  -- get argument types
  let (mvars, binders, _body) ← forallMetaTelescope (← inferType e)
  unless (← isDefEq _body expectedType) do
    Lean.logError "Could not work out type of instance"
    return provided
  e := mkAppN e mvars
  -- the parameters should haev been assigned by unification
  for arg in mvars.extract 0 ctor.numParams do
    guard (← arg.mvarId!.isAssigned)
  -- substitute parent classes with direct instances, if possible
  for arg in mvars.extract ctor.numParams (ctor.numParams + ctor.numFields),
      bi in binders.extract ctor.numParams (ctor.numParams + ctor.numFields) do
    if let .instImplicit := bi then
      if let .some new_arg ← trySynthInstance (← inferType arg) then
        if ← isDefEq arg new_arg then
          continue
        else
          Lean.logError m!"Field is not defeq, given{indentExpr arg}\ncalculate{indentExpr new_arg}"
  e ← instantiateMVars e
  -- must be defeq to what the user passed
  if !(← isDefEq provided e) then
    let (provided', e') ← Lean.Meta.addPPExplicitToExposeDiff (← whnf provided) e
    Lean.logError m!"Not defeq, given{indentExpr provided'}\ncalculated{indentExpr e'}"
    return provided
  pure e
