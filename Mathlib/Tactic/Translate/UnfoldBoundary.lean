/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Batteries.Lean.NameMapAttribute
public import Mathlib.Init

/-!
# Modify proof terms so that they don't rely on unfolding certain constants
-/

namespace Mathlib.Tactic.UnfoldBoundary

public section identification

universe u

/-- `Identification` is used by translation attributes to insert abstraction boundaries in terms
that need to be translated-/
structure Identification (α β : Type u) : Type u where
  /-- The unfolding function. -/
  toFun : α → β
  /-- The refolding function. -/
  invFun : β → α

/-- The identity `Identification`. -/
@[expose]
def Identification.Id {α : Type u} : Identification α α where
  toFun x := x
  invFun x := x

end identification

meta section

open Lean Meta

structure UnfoldBoundaries where
  unfolds : NameMap SimpTheorem
  casts : NameMap Name

def withBlockUnfolding {α} (boundaries : UnfoldBoundaries) (x : MetaM α) : MetaM α := do
  withCanUnfoldPred (fun _ cinfo =>
    return !boundaries.unfolds.contains cinfo.name && !boundaries.casts.contains cinfo.name) x

def unfold (e : Expr) (unfolds : NameMap SimpTheorem) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext { Simp.neutralConfig with implicitDefEqProofs := false }
    (congrTheorems := (← getSimpCongrTheorems))
  (·.1) <$> Simp.main e ctx (methods := { pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    let .const c _ ← whnf e.getAppFn | return .continue
    let some thm := unfolds.find? c | return .continue
    let some r ← Simp.tryTheorem? e thm | return .continue
    return .done r


def refoldConsts (e expectedType : Expr) (boundaries : UnfoldBoundaries) : MetaM Expr := do
  let goal ← mkFreshExprMVar expectedType
  go e goal.mvarId!
  instantiateMVars goal
where
  go (e : Expr) (goal : MVarId) : MetaM Unit := do
    let r ← unfold (← goal.getType) boundaries.unfolds
    let goal ← match r.proof? with
      | some proof => goal.replaceTargetEq r.expr proof
      | none => pure goal
    forallTelescope (← goal.getType) fun xs tgt => do
      if let .const c _ := (← whnf tgt).getAppFn then
        if let some cast := boundaries.casts.find? c then
          let cast ← mkConstWithFreshMVarLevels cast
          let (mvars, _, type) ← forallMetaTelescope (← inferType cast)
          let_expr f@Identification α β := type | throwError "expected `Identification`, not {type}"
          if ← isDefEq tgt α then
            let goal' ← mkFreshExprMVar (← instantiateMVars β)
            go (mkAppN e xs) goal'.mvarId!
            goal.assign <| ← mkLambdaFVars xs <|
              mkApp4 (.const ``Identification.invFun f.constLevels!) α β (mkAppN cast mvars) goal'
            return
          else
            throwError "identification `{cast}` could not be applied at {tgt}"
      if ← isDefEq (← goal.getType) (← inferType e) then
        goal.assign e
      else
        throwError "Error: could not cast {e} into the type {← goal.getType}."

def unfoldConsts (e : Expr) (boundaries : UnfoldBoundaries) : MetaM Expr := do
  let eType ← inferType e
  if let .const c _ := (← whnf eType).getAppFn then
    if let some cast := boundaries.casts.find? c then
      let cast ← mkConstWithFreshMVarLevels cast
      let (mvars, _, type) ← forallMetaTelescope (← inferType cast)
      let_expr f@Identification α β := type | throwError "expected Identification, not {type}"
      if ← isDefEq eType α then
        let e := mkApp4 (.const ``Identification.toFun f.constLevels!) α β (mkAppN cast mvars) e
        return ← unfoldConsts e boundaries
      else
        throwError "Error: identification `{cast}` could not be applied at {eType}"
  let r ← unfold eType boundaries.unfolds
  let some pf := r.proof? | return e
  mkAppOptM ``cast #[eType, r.expr, pf, e]

/-- Given an expression `e` with expected type `type`, if `e` doesn't have that type,
use a cast to turn `e` into that type. -/
def mkAppWithCast (f a : Expr) (boundaries : UnfoldBoundaries) : MetaM Expr :=
  try
    checkApp f a
    return f.app a
  catch _ =>
    let f ← unfoldConsts f boundaries
    let .forallE _ d _ _ ← whnf (← inferType f) | throwFunctionExpected f
    let a ← unfoldConsts a boundaries
    let a ← refoldConsts a d boundaries
    return f.app a

def mkCast (e expectedType : Expr) (boundaries : UnfoldBoundaries) : MetaM Expr := do
  if ← isDefEq (← inferType e) expectedType then
    return e
  let e ← unfoldConsts e boundaries
  let e ← refoldConsts e expectedType boundaries
  if ← isDefEq (← inferType e) expectedType then
    return e
  else
    throwError "{e} does not match the expected type {expectedType}"

public section

/-- Extensions for handling abstraction boundaries for definitions that shouldn't be unfolded. -/
structure UnfoldBoundaryExt where
  /-- The `dont_unfold` attribute is used to tag declarations `foo` that should not be unfolded in
  a proof that is translated. Instead, the unfold theorem `foo.eq_def` is inserted. -/
  unfolds : NameMapExtension SimpTheorem
  /-- The `cast` attribute is used to tag casting functions `foo.val` for declarations `foo` that
  should not be unfolded in a proof that is translated. -/
  casts : NameMapExtension Name

/-- Modify `e` so that it has type `expectedType`. -/
def UnfoldBoundaryExt.cast (e expectedType : Expr) (boundaries : UnfoldBoundaryExt) :
    MetaM Expr := do
  let env ← getEnv
  let boundaries := {
    unfolds := boundaries.unfolds.getState env
    casts := boundaries.casts.getState env }
  withBlockUnfolding boundaries do withTransparency TransparencyMode.all do
    mkCast e expectedType boundaries

/-- Modify `e` so that it is well typed if the constants in `boundaries` cannot be unfolded. -/
def UnfoldBoundaryExt.insertBoundaries (e : Expr) (boundaries : UnfoldBoundaryExt) :
    MetaM Expr := do
  let env ← getEnv
  let boundaries := {
    unfolds := boundaries.unfolds.getState env
    casts := boundaries.casts.getState env }
  withBlockUnfolding boundaries do withTransparency TransparencyMode.all do
    instantiateMVars <| ← transform e (post := fun e ↦ e.withApp fun f args => do
      let mut f := f
      for arg in args do
        try
          f ← mkAppWithCast f arg boundaries
        catch e =>
          throwError "failed to deal with {f} applied to {arg}\n{e.toMessageData}"
      return .done f)

end

end

end Mathlib.Tactic.UnfoldBoundary
