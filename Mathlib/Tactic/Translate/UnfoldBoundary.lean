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

def withBlockUnfolding {α} (b : UnfoldBoundaries) (x : MetaM α) : MetaM α := do
  withCanUnfoldPred (fun _ cinfo =>
    return !b.unfolds.contains cinfo.name
      && !b.casts.contains cinfo.name) x

def unfold (e : Expr) (unfolds : NameMap SimpTheorem) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext { Simp.neutralConfig with implicitDefEqProofs := false }
  (·.1) <$> Simp.main e ctx (methods := { pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    let .const c _ ← whnf e.getAppFn | return .continue
    let some thm := unfolds.find? c | return .continue
    let some r ← Simp.tryTheorem? e thm | return .continue
    return .done r


def refoldConsts (e expectedType : Expr) (b : UnfoldBoundaries) : MetaM Expr := do
  let goal ← mkFreshExprMVar expectedType
  go e goal.mvarId!
  instantiateMVars goal
where
  go (e : Expr) (goal : MVarId) : MetaM Unit := do
    let r ← unfold (← goal.getType) b.unfolds
    let goal ← match r.proof? with
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
        throwError "Error: could not cast {e} into the type {← goal.getType}."

def unfoldConsts (e : Expr) (b : UnfoldBoundaries) : MetaM Expr := do
  let eType ← inferType e
  let eTypeWhnf ← whnf eType
  if let .const c us := eTypeWhnf.getAppFn then
    if let some (cast, _) := b.casts.find? c then
      let e := .app (mkAppN (.const cast us) eTypeWhnf.getAppArgs) e
      return ← unfoldConsts e b
  let r ← unfold eType b.unfolds
  let some pf := r.proof? | return e
  mkAppOptM ``cast #[eType, r.expr, pf, e]

/-- Given an expression `e` with expected type `type`, if `e` doesn't have that type,
use a cast to turn `e` into that type. -/
def mkAppWithCast (f a : Expr) (b : UnfoldBoundaries) : MetaM Expr :=
  try
    checkApp f a
    return f.app a
  catch _ =>
    let f ← unfoldConsts f b
    let .forallE _ d _ _ ← whnf (← inferType f) | throwFunctionExpected f
    let a ← unfoldConsts a b
    let a ← refoldConsts a d b
    return f.app a

def mkCast (e expectedType : Expr) (b : UnfoldBoundaries) : MetaM Expr := do
  if ← isDefEq (← inferType e) expectedType then
    return e
  let e ← unfoldConsts e b
  let e ← refoldConsts e expectedType b
  if ← isDefEq (← inferType e) expectedType then
    return e
  else
    throwError "{e} does not match the expected type {expectedType}"

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
  withBlockUnfolding b do withTransparency TransparencyMode.all do
    mkCast e expectedType b

/-- Modify `e` so that it is well typed if the constants in `b` cannot be unfolded.

Note: it may be that `e` contains some constant whose type is not well typed in this setting.
  We don't make an effort to replace such constants.
  It seems that this approximation works well enough. -/
public def UnfoldBoundaryExt.insertBoundaries (e : Expr) (b : UnfoldBoundaryExt) : MetaM Expr := do
  let b ← b.toUnfoldBoundaries
  withBlockUnfolding b do withTransparency TransparencyMode.all do
    transform e (post := fun e ↦ e.withApp fun f args => do
      let mut f := f
      for arg in args do
        try
          f ← mkAppWithCast f arg b
        catch e =>
          throwError "failed to deal with {f} applied to {arg}\n{e.toMessageData}"
      return .done f)

/-- Unfold all of the auxiliary functions that were insertedy as unfold boundaries. -/
public def UnfoldBoundaryExt.unfoldInsertions (e : Expr) (b : UnfoldBoundaryExt) :
    CoreM Expr := do
  let b ← b.toUnfoldBoundaries
  Meta.deltaExpand e b.insertionFuns.contains

end Mathlib.Tactic.UnfoldBoundary
