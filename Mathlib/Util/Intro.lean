/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Replace

/-!

# Variations on intro

This modules provides some functions for doing `revert`/`intro` in such a way that one
can preserve `FVarId`s. This is important for the editor feature where you can see all uses of a
variable. It's also important for making sure the unused variables linter doesn't give spurious
results.
-/

open Lean Meta

/-- A reimplementation of `introNImp` in `Lean.Meta.Tactic.Intro`, but modified to take a list
of `fvarIds` to use, and specialized for our specific use case. -/
private partial def introNPImp' (mvarId : MVarId) (fvarIds : Array FVarId) :
    MetaM (Array FVarId × MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `introN'
    let (fvars, mvarId) ← loop fvarIds.size (← getLCtx) #[] 0 (← mvarId.getType)
    return (fvars.map Expr.fvarId!, mvarId)
where
  loop (i : Nat) (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (type : Expr) :
      MetaM (Array Expr × MVarId) := do
    match i, type with
    | 0, type =>
      let type := type.instantiateRevRange j fvars.size fvars
      withReader ({· with lctx := lctx }) do
        withNewLocalInstances fvars j do
          let type := type.headBeta
          let newMVar ← mkFreshExprSyntheticOpaqueMVar type (← mvarId.getTag)
          mvarId.assign (← mkLambdaFVars fvars newMVar)
          return (fvars, newMVar.mvarId!)
    | i+1, .letE n type val body _ =>
      let type   := type.instantiateRevRange j fvars.size fvars
      let type   := type.headBeta
      let val    := val.instantiateRevRange j fvars.size fvars
      let fvarId := fvarIds[fvars.size]!
      let lctx   := lctx.mkLetDecl fvarId n type val
      let fvars  := fvars.push (.fvar fvarId)
      loop i lctx fvars j body
    | i+1, .forallE n type body c =>
      let type   := type.instantiateRevRange j fvars.size fvars
      let type   := type.headBeta
      let fvarId := fvarIds[fvars.size]!
      let lctx   := lctx.mkLocalDecl fvarId n type c
      let fvars  := fvars.push (.fvar fvarId)
      loop i lctx fvars j body
    | i+1, type =>
      let type := type.instantiateRevRange j fvars.size fvars
      withReader (fun ctx => { ctx with lctx := lctx }) do
        withNewLocalInstances fvars j do
          /- We used to use just `whnf`, but it produces counterintuitive behavior if
             - `type` is a metavariable `?m` such that `?m := let x := v; b`, or
             - `type` has `MData` or annotations such as `optParam` around a `let`-expression.

             `whnf` instantiates metavariables, and consumes `MData`, but it also expands the `let`.
          -/
          let newType := (← instantiateMVars type).cleanupAnnotations
          if newType.isForall || newType.isLet then
            loop (i+1) lctx fvars fvars.size newType
          else
            let newType ← whnf newType
            if newType.isForall then
              loop (i+1) lctx fvars fvars.size newType
            else
              throwTacticEx `introN mvarId "insufficient number of binders"

/--
Variant of `Lean.MVarId.introNP'` where you can supply an array of `FVarId`s to use.
The `FVarId`s must not already be used.

This is a low-level function.
-/
def Lean.MVarId.introNP' (mvarId : MVarId) (fvarIds : Array FVarId) :
    MetaM (Array FVarId × MVarId) :=
  if fvarIds.isEmpty then
    return (#[], mvarId)
  else
    introNPImp' mvarId fvarIds

/--
Reverts the variables specified by `fvarIds`, calls the function, then does intro again on all
the reverted variables.

The metavariable that `f` returns *must* be in a form that is "`intro`-compatible" with the one
it is given.

This function preserves the `FVarId`s of all reverted local variables.
-/
def Lean.MVarId.withReverted (mvarId : MVarId) (fvarIds : Array FVarId)
    (f : Array FVarId → MVarId → MetaM (MVarId × α))
    (preserveOrder : Bool := false) (clearAuxDeclsInsteadOfRevert := false) :
    MetaM (Array FVarId × MVarId × α) := do
  let (fvarIds, mvarId) ← mvarId.revert fvarIds preserveOrder clearAuxDeclsInsteadOfRevert
  let (mvarId, v) ← f fvarIds mvarId
  let (fvarIds, mvarId) ← mvarId.introNP' fvarIds
  return (fvarIds, mvarId, v)

/-- This is a replacement for `Lean.MVarId.changeLocalDecl` that fixes the issue that it does
not preserve `FVarId`s, which causes spurious unused variable errors. -/
def Lean.MVarId.changeLocalDecl' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let (_, mvarId', _) ← mvarId.withReverted #[fvarId] fun _ mvarId' => mvarId'.withContext do
    match ← mvarId'.getType with
    | .forallE n d b c => do check d; finalize mvarId' (mkForall n c typeNew b)
    | .letE n t v b _  => do check t; finalize mvarId' (mkLet n typeNew v b)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId'
where
  check (typeOld : Expr) : MetaM Unit := do
    if checkDefEq && not (← isDefEq typeNew typeOld) then
      throwTacticEx `changeHypothesis mvarId
        m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
  finalize (mvarId : MVarId) (targetNew : Expr) : MetaM (MVarId × Unit) := do
    let mvarId ← mvarId.replaceTargetDefEq targetNew
    return (mvarId, ())
