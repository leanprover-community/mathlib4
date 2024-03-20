/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Lean.Elab

open Lean Meta

elab "fast_instance%" arg:term : term <= expectedType => do
  let .some className ← Lean.Meta.isClass? expectedType |
    throwError "Can only be used for classes"
  let ctor := Lean.getStructureCtor (← getEnv) className
  let provided ← Lean.Elab.Term.elabTerm arg (some expectedType)
  -- create universe variables
  let levels ← Meta.mkFreshLevelMVarsFor (.ctorInfo ctor)
  let mut e := Expr.const ctor.name levels
  -- get argument types
  let (mvars, binders, _body_) ← forallMetaTelescope (←inferType e)
  e := mkAppN e mvars
  guard (← isDefEq (←inferType e) expectedType)
  e ← instantiateMVars e
  -- substitute parent classes with direct instances, if possible
  for arg in mvars.extract ctor.numParams (ctor.numParams + ctor.numFields),
      bi in binders.extract ctor.numParams (ctor.numParams + ctor.numFields) do
    if let .instImplicit := bi then
      if let .some new_arg ← trySynthInstance (←inferType arg) then
        arg.mvarId!.assign new_arg
  -- must be defeq to what the user passed
  if !(← isDefEq provided e) then
    Lean.logError "Not defeq"
  pure e
