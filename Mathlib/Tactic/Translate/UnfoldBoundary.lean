/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Lean.Meta.Tactic.Delta
public meta import Batteries.Lean.NameMapAttribute
public import Mathlib.Init

/-!
# Modify proof terms so that they don't rely on unfolding certain constants

This file defines a procedure for inserting casts into (proof) terms in order to make them
well typed in a setting where certain constants aren't allowed to be unfolded.

We make use of `withCanUnfoldPred` in order to modify which constants can and cannot be unfolded.
This way, `whnf` and `isDefEq` do not unfold these constants.

So, the procedure is to check that an expression is well typed, using `isDefEq`, and whenever
there is a type mismatch, we try to insert a cast.

There are two kinds of casts:
- Equality casts. This is for propositions and terms,
  where it is possible to prove that one is equal to the other. For example `Monotone`.
- explicit casting functions, both for unfolding and folding. This is for Types, where we
  cannot express their equivalence with an equality. For example `DecidableLE`.
-/

meta section

namespace Mathlib.Tactic.UnfoldBoundary

open Lean Meta

structure UnfoldBoundaries where
  /-- For propositions and terms of types, we store a rewrite theorem that unfolds it. -/
  unfolds : NameMap SimpTheorem
  /-- For types, we store a cast for translating from and to the type respectively. -/
  casts : NameMap (Name × Name)
  /-- The functions that we want to unfold again after the translation has happened. -/
  insertionFuns : NameMap Unit

/-- Modify the `MetaM` context to not allow unfolding the constants for which we would like
to insert explicit casts. -/
def withBlockUnfolding {α} (b : UnfoldBoundaries) (x : MetaM α) : MetaM α := do
  withCanUnfoldPred (fun _ cinfo =>
    return !b.unfolds.contains cinfo.name
      && !b.casts.contains cinfo.name) x

def run {α} (b : UnfoldBoundaries) (x : SimpM α) : MetaM α :=
  withBlockUnfolding b do withTransparency TransparencyMode.all do
  let ctx ← Simp.mkContext { Simp.neutralConfig with implicitDefEqProofs := false }
  (·.1) <$> Simp.SimpM.run ctx {} (methods := { pre }) x
where
  pre (e : Expr) : SimpM Simp.Step := do
    let .const c _ ← whnf e.getAppFn | return .continue
    let some thm := b.unfolds.find? c | return .continue
    let some r ← Simp.tryTheorem? e thm | return .continue
    return .done r

/-- Given a term `e`, add casts to it to unfold constants appearing in it. -/
partial def unfoldConsts (b : UnfoldBoundaries) (e : Expr) : SimpM Expr := do
  let eType ← inferType e
  let e ← do
    let r ← Simp.simp eType
    if let some pf := r.proof? then
      mkAppOptM ``cast #[eType, r.expr, pf, e]
    else
      pure e
  let eTypeWhnf ← whnf (← inferType e)
  if let .const c us := eTypeWhnf.getAppFn then
    if let some (cast, _) := b.casts.find? c then
      let e := .app (mkAppN (.const cast us) eTypeWhnf.getAppArgs) e
      return ← unfoldConsts b e
  return e

/-- Given a term `e` which we want to get to have type `expectedType`, return a term of type
`expectedType` by adding cast to `e` that unfold constants in `expectedType`. -/
partial def refoldConsts (b : UnfoldBoundaries) (e expectedType : Expr) : SimpM Expr := do
  let goal ← mkFreshExprMVar expectedType
  go e goal.mvarId!
  instantiateMVars goal
where
  go (e : Expr) (goal : MVarId) : SimpM Unit := do
    let goal ← do
      let r ← Simp.simp (← goal.getType)
      match r.proof? with
      | some proof => goal.replaceTargetEq r.expr proof
      | none => pure goal
    forallTelescope (← goal.getType) fun xs tgt => do
      let tgt ← whnf tgt
      if let .const c us := tgt.getAppFn then
        if let some (_, cast) := b.casts.find? c then
          let cast := mkAppN (.const cast us) tgt.getAppArgs
          let .forallE _ α _ _ ← inferType cast | throwError s!"{cast} is not of the right form"
          let goal' ← mkFreshExprMVar α
          go (mkAppN e xs) goal'.mvarId!
          goal.assign <| ← mkLambdaFVars xs <| .app cast goal'
          return
      if ← isDefEq (← goal.getType) (← inferType e) then
        goal.assign e
      else
        throwError "Failed to insert casts to make {e} have type {← goal.getType}."

/-- Given an expression `e` with expected type `type`, if `e` doesn't have that type,
use a cast to turn `e` into that type. -/
def mkAppWithCast (f a : Expr) (b : UnfoldBoundaries) : SimpM Expr :=
  try
    checkApp f a
    return f.app a
  catch _ =>
    let f ← unfoldConsts b f
    let .forallE _ d _ _ ← whnf (← inferType f) | throwFunctionExpected f
    let a ← unfoldConsts b a
    let a ← refoldConsts b a d
    return f.app a

def mkCast (e expectedType : Expr) (b : UnfoldBoundaries) : SimpM Expr := do
  if ← isDefEq (← inferType e) expectedType then
    return e
  let e ← unfoldConsts b e
  refoldConsts b e expectedType

/-- Extensions for handling abstraction boundaries for definitions that shouldn't be unfolded. -/
public structure UnfoldBoundaryExt where
  /-- The `cast` attribute is used to tag declarations `foo` that should not be unfolded in
  a proof that is translated. Instead, a rewrite with an equality theorem is inserted.
  This equality theorem then may be translated by the translation attribute. -/
  unfolds : NameMapExtension SimpTheorem
  /-- The `cast_fun` attribute is used to tag types that should not be unfolded in a proof that
  is translated. Instead, a casting function is inserted. This casting function then may be
  translated by the translation attribute. -/
  casts : NameMapExtension (Name × Name)
  /-- `insertionFuns` stores the functions that may end up in an expression after inserting casts
  and applying the translation. -/
  insertionFuns : NameMapExtension Unit

def UnfoldBoundaryExt.toUnfoldBoundaries (b : UnfoldBoundaryExt) :
    CoreM UnfoldBoundaries := do
  let env ← getEnv
  return {
    unfolds := b.unfolds.getState env
    casts := b.casts.getState env
    insertionFuns := b.insertionFuns.getState env }

/-- Modify `e` so that it has type `expectedType`. -/
public def UnfoldBoundaryExt.cast (e expectedType : Expr) (b : UnfoldBoundaryExt) : MetaM Expr := do
  let b ← b.toUnfoldBoundaries
  run b do
    mkCast e expectedType b

/-- Modify `e` so that it is well typed if the constants in `b` cannot be unfolded.

Note: it may be that `e` contains some constant whose type is not well typed in this setting.
  We don't make an effort to replace such constants.
  It seems that this approximation works well enough. -/
public def UnfoldBoundaryExt.insertBoundaries (e : Expr) (b : UnfoldBoundaryExt) : MetaM Expr := do
  let b ← b.toUnfoldBoundaries
  run b do
    transform e (post := fun e ↦ e.withApp fun f args => do
      let mut f := f
      for arg in args do
        try
          f ← mkAppWithCast f arg b
        catch e =>
          throwError "failed to deal with {f} applied to {arg}\n{e.toMessageData}"
      return .done f)

/-- Unfold all of the auxiliary functions that were insertedy as unfold boundaries. -/
public def UnfoldBoundaryExt.unfoldInsertions (e : Expr) (b : UnfoldBoundaryExt) : CoreM Expr := do
  let b ← b.toUnfoldBoundaries
  Meta.deltaExpand e b.insertionFuns.contains

end Mathlib.Tactic.UnfoldBoundary
