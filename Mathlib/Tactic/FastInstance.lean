/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieserf
-/

import Lean.Elab.ComputedFields
import Lean.Meta.Tactic.ElimInfo

/-!
# The `fast_instance%` term elaborator
-/

open Lean Meta
private partial def makeFastInstance (provided : Expr) : MetaM Expr := do
  let ty ← inferType provided
  if (← inferType ty).isProp || ty.isProp then return provided else
  let constName := ty.constName?
  match constName with
  | some `Decidable => return provided
  | some `DecidableEq => return provided
  | _ =>
  withTraceNode `Tactic.fast_instance (fun e => return m!"{exceptEmoji e} type: {ty}") do
  let className ← isClass? ty
    -- | throwError "Can only be used for classes, but given term of type{indentExpr ty}"
  match className with
  | none => return provided
  | some className =>
  if let .some new ← trySynthInstance ty then
    if ← withReducibleAndInstances <| isDefEq provided new then
      trace[Tactic.fast_instance] "replaced with synthesized instance"
      return new
    else
      if ← withDefault <| isDefEq provided new then
        trace[Tactic.fast_instance] "defeq only at default transparency"
      -- withReducibleAndInstances do
      -- uncomment these to see reduced terms. occasionally useful
      --let provided ← whnf provided
      --let new ← whnf new
      -- throwError "\
      --   Provided instance {indentExpr provided}\n\
      --   is not defeq to inferred instance{indentExpr new}"
  -- let ctor := getStructureCtor (← getEnv) className
  let env ← getEnv
  let ctor := match env.find? className with
  | some (.inductInfo { isRec := false, ctors := [ctorName], .. }) =>
    match env.find? ctorName with
    | some (ConstantInfo.ctorInfo val) => some val
    | _ => none
  | _ => none
  match ctor with
  | none => return provided
  | some ctor =>
  withReducible <| forallTelescopeReducing ty fun tyArgs _ => do
    let provided' ← withReducibleAndInstances <| whnf <| mkAppN provided tyArgs
    -- unless provided'.isAppOf ctor.name do
    --   throwError "\
    --     Provided instance does not reduce to constructor application{indentExpr provided}"
    let mut args := provided'.getAppArgs
    let instParams ← withReducible <| forallTelescopeReducing ctor.type fun args _ =>
      args.mapM fun arg => return (← arg.fvarId!.getBinderInfo).isInstImplicit
    unless args.size == instParams.size do
      return provided
      -- throwError "Incorrect number of arguments for constructor application{indentExpr provided}"
    for i in [ctor.numParams:args.size] do
      if instParams[i]! then
        args := args.set! i (← makeFastInstance args[i]!)
    let provided' := mkAppN provided'.getAppFn args
    mkLambdaFVars tyArgs provided'
-- private partial def makeFastInstance (provided : Expr) : MetaM Expr := do
--   let ty ← inferType provided
--   let .some className ← Lean.Meta.isClass? ty | do
--     Lean.logError "Can only be used for classes"
--     return provided
--   let ctor := Lean.getStructureCtor (← getEnv) className
--
--   -- TODO: withNewMCtxDepth do
--   -- create universe variables
--   let levels ← Meta.mkFreshLevelMVarsFor (.ctorInfo ctor)
--   let mut e := Expr.const ctor.name levels
--   -- get argument types
--   let (mvars, binders, _body) ← forallMetaTelescope (← inferType e)
--   unless (← isDefEq _body ty) do
--     Lean.logError "Could not work out type of instance"
--     return provided
--   e := mkAppN e mvars
--   -- the parameters should have been assigned by unification
--   for arg in mvars.extract 0 ctor.numParams do
--     guard (← arg.mvarId!.isAssigned)
--   -- substitute parent classes with direct instances, if possible
--   for arg in mvars.extract ctor.numParams (ctor.numParams + ctor.numFields),
--       bi in binders.extract ctor.numParams (ctor.numParams + ctor.numFields) do
--     if let .instImplicit := bi then
--       let arg_ty ← inferType arg
--       let new_arg ← do
--         if let .some new_arg ← trySynthInstance arg_ty then
--           pure new_arg
--         else
--           makeFastInstance arg
--       if ← withReducibleAndInstances <| isDefEq arg new_arg then
--         continue
--       else
--         Lean.logError m!"Field is not defeq, given{indentExpr arg}\ncalculate{indentExpr new_arg}"
--   e ← instantiateMVars e
--   -- must be defeq to what the user passed
--   if !(← isDefEq provided e) then
--     let (provided', e') ← Lean.Meta.addPPExplicitToExposeDiff (← whnf provided) e
--     Lean.logError m!"Not defeq, given{indentExpr provided'}\ncalculated{indentExpr e'}"
--     return provided
--   pure e

/-- `fast_instance% inst` takes an expression for a typeclass instance `inst`, and unfolds it into
constructor applications that leverage existing instances.

For instance, when used as
```lean
instance instSemiring : Semiring X := sorry
instance instRing : Ring X := fast_instance% fast_instance% Function.Injective.ring ..
```
this will define `instRing` as a nested constructor application that refers to `instSemiring`.
The advantage is then that `instRing.toSemiring` unifies almost immediately with `instSemiring`,
rather than having to break it down into smaller pieces. -/
syntax (name := fastInstance) "fast_instance%" term : term

@[term_elab fastInstance, inherit_doc fastInstance]
def elabFastInstance : Elab.Term.TermElab
  | `(term| fast_instance% $arg), expectedType => do
    -- passthrough the term
    let provided ← Lean.Elab.Term.elabTermEnsuringType arg expectedType
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    makeFastInstance provided
  | _, _ => Elab.throwUnsupportedSyntax

builtin_initialize
  registerTraceClass `Tactic.fast_instance
