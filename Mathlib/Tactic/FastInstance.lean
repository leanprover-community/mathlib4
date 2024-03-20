/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieserf
-/

import Lean.Elab

/-!
# The `fast_instance%` term elaborator
-/

open Lean Meta

private partial def makeFastInstance (provided : Expr) : MetaM Expr := do
  let ty ← inferType provided
  let .some className ← Lean.Meta.isClass? ty | do
    Lean.logError "Can only be used for classes"
    return provided
  let ctor := Lean.getStructureCtor (← getEnv) className

  -- TODO: withNewMCtxDepth do
  -- create universe variables
  let levels ← Meta.mkFreshLevelMVarsFor (.ctorInfo ctor)
  let mut e := Expr.const ctor.name levels
  -- get argument types
  let (mvars, binders, _body) ← forallMetaTelescope (← inferType e)
  unless (← isDefEq _body ty) do
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
      let arg_ty ← inferType arg
      if let .some new_arg ← trySynthInstance arg_ty then
        if ← isDefEq arg new_arg then
          continue
        else
          Lean.logError m!"Field is not defeq, given{indentExpr arg}\ncalculate{indentExpr new_arg}"
      else
        let new_arg ← makeFastInstance arg
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

syntax (name := fastInstance) "fast_instance%" term : term

/-- This elaborator can improve performance when inserted before uses of `Function.Injective.ring`
etc. -/
@[term_elab fastInstance]
def elabFastInstance : Elab.Term.TermElab
  | `(term| fast_instance% $arg), expectedType => do
    -- passthrough the term
    let provided ← Lean.Elab.Term.elabTermEnsuringType arg expectedType
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    makeFastInstance provided
  | _, _ => Elab.throwUnsupportedSyntax
