/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nick Kuhn, Arend Mellendijk, Christian Merten, Calle Sönne, Adam Topaz
-/

import Mathlib.Algebra.Algebra.Tower
import Lean.Attributes

/-!

# Algebraize tactic

TODO

-/

open Lean Elab Tactic Term Meta

namespace Lean.Attr

/-- TODO


-/
def algebraizeGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize $name:ident) => return name.getId
  -- TODO: instead of throwing an error, if thm is `RingHom.Property`, this should return
  -- `Algebra.Property`
  | `(attr| algebraize) => throwError "algebraize requires an argument"
  | _ => throwError "unexpected algebraize argument"

initialize algebraizeAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `algebraize,
    descr := "TODO",
    getParam := algebraizeGetParam }

end Lean.Attr

namespace Mathlib.Tactic

/-- TODO

The reason we demand both `f` and `ft` as arguments (even though `f` can be inferred from `ft`) is
because before calling this function in `algebraize`, we have already computed `ft`

-/
def addAlgebraInstanceFromRingHom (f ft : Expr) : TacticM Unit := withMainContext do
  let (_, l) := ft.getAppFnArgs
  let alg ← mkAppOptM `Algebra #[l[0]!, l[1]!, none, none]
  try let _ ← synthInstance alg
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `algInst
    let mvar ← mvarid.define nm alg (← mkAppM `RingHom.toAlgebra #[f])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

/-- TODO


-/
def addIsScalarTowerInstanceFromRingHomComp (f : Expr) : TacticM Unit := withMainContext do
  -- TODO: this one is not very type safe, I am sure there will be errors in more complicated
  -- expressions. Maybe this one should be reverted to the Qq version
  let (_, l) := f.getAppFnArgs
  let tower ← mkAppOptM `IsScalarTower #[l[0]!, l[1]!, l[2]!, none, none, none]
  try
    let _ ← synthInstance tower
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `scalarTowerInst
    -- This is quite ugly, so I might prefer Qq reason for this reason
    -- Maybe I can use forallTelescope on `IsScalarTower.of_algebraMap_eq' somehow here?
    let h ← mkFreshExprMVar (← mkAppM `Eq #[
      ← mkAppOptM `algebraMap #[l[0]!, l[2]!, none, none, none],
      ← mkAppM `RingHom.comp #[
        ← mkAppOptM `algebraMap #[l[1]!, l[2]!, none, none, none],
        ← mkAppOptM `algebraMap #[l[0]!, l[1]!, none, none, none]
    ]])
    h.mvarId!.refl
    let mvar ← mvarid.define nm tower
      (← mkAppOptM `IsScalarTower.of_algebraMap_eq'
        #[l[0]!, l[1]!, l[2]!, none, none, none, none, none, none, h])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

/-- TODO



-/
def searchContext (t : Array Expr) : TacticM Unit := withMainContext do
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then return
    let (nm, args) := decl.type.getAppFnArgs
    match Attr.algebraizeAttr.getParam? (← getEnv) nm with
    | some p =>
      let f := args[args.size - 1]!
      -- Check if `f` appears in the list of functions we have algebraized
      if ¬ (← t.anyM (fun j => Meta.isDefEq j f)) then return

      let cinfo ← getConstInfo p
      let n ← getExpectedNumArgs cinfo.type
      let pargs := Array.mkArray n (none : Option Expr)
      let pargs := pargs.set! 0 args[0]!
      let pargs := pargs.set! 1 args[1]!
      let tp ← mkAppOptM p pargs

      liftMetaTactic fun mvarid => do
        let nm ← mkFreshUserName `AlgebraizeInst
        let (_, mvar) ← mvarid.note nm decl.toExpr tp
        return [mvar]
    | none => return

syntax "algebraize" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    let t ← t.mapM fun i => Term.elabTerm i none
    -- We loop through the given terms and add algebra instances
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const `RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError "Expected a `RingHom`" -- TODO: improve message
    -- After having added the algebra instances we try to add scalar tower instances
    for f in t do
      match f.getAppFn with
      | Expr.const `RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue

    -- We then search through the local context to find other instances of algebraize
    searchContext t

-- version of algebraize prime which only adds algebra instances & scalar towers
syntax "algebraize'" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize' $[$t:term]*) => do
    let t ← t.mapM fun i => Term.elabTerm i none
    -- We loop through the given terms and add algebra instances
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const `RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError "Expected a `RingHom`" -- TODO: improve message
    -- After having added the algebra instances we try to add scalar tower instances
    for f in t do
      match f.getAppFn with
      | Expr.const `RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue

end Mathlib.Tactic
