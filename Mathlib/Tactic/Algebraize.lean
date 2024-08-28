/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nick Kuhn, Arend Mellendijk, Christian Merten, Calle Sönne, Adam Topaz
-/

import Mathlib.Algebra.Algebra.Tower
import Lean.Attributes

/-!

# Algebraize tactic

This file defines the `algebraize` tactic. The basic functionality of this tactic is to
automatically add `Algebra` instances given `RingHom`s. For example, `algebraize f g` where
`f : A →+* B` and `g : B →+* C` are `RinHom`'s, will add the instances `Algebra A B` and
`Algebra B C` corresponding to these `RingHom`s.

# Further functionality

When given a composition of `RingHom`'s, e.g. `algebraize g.comp f`, the tactic will also try to
add the instance `IsScalarTower A B C` if possible.

After having added suitable `Algebra` and `IsScalarTower` instances, the tactic will search through
the local context for `RingHom` properties that can be converted properties of the corresponding
`Algebra`. For example, given `f : A →+* B` and `hf : f.FiniteType`, then `algebraize f` will add
the instance `Algebra A B` and the corresponding property `Algebra.FiniteType A B`. The tactic knows
which `RingHom` properties have a corresponding `Algebra` property through the `algebraize`
attribute. This attribute has a parameter `name` which should be the name of the corresponding
`Algebra` property. For example, `Algebra.FiniteType` is tagged as follows:
```
@[algebraize Algebra.FiniteType]
def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
```

To skip searching through the local context and adding corresponding `Algebra` properties, use
`algebraize'` which only adds `Algebra` and `IsScalarTower` instances.

## TODO / Upcoming work

For now, one always needs to give the name of the corresponding `Algebra` property as an argument
to the `algebraize` attribute. However, often this can be inferred from the name of the declaration
with the tag (i.e. `RingHom.FiniteType` corresponds `Algebra.FiniteType`). It would be nice to
add functionality that defaults to this name if no argument is given to the `algebraize` attribute.

Make this function safer: catch more possible errors, and improve error messages.

-/

open Lean Elab Tactic Term Meta

namespace Lean.Attr

/-- A user attribute that is used to tag `RingHom` properties that can be converted to `Algebra`
properties. The attribute has a parameter `name` which should be the name of the corresponding
`Algebra` property. -/
def algebraizeGetParam (_ : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize $name:ident) => return name.getId
  /- TODO: instead of throwing an error, if thm is `RingHom.Property`, this should return
    `Algebra.Property` -/
  | `(attr| algebraize) => throwError "algebraize requires an argument"
  | _ => throwError "unexpected algebraize argument"

initialize algebraizeAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `algebraize,
    descr :=
"Tag that lets the `algebraize` tactic know which `Algebra` property corresponds to this `RingHom`
property.",
    getParam := algebraizeGetParam }

end Lean.Attr

namespace Mathlib.Tactic

namespace Algebraize

/-- Given an expression `f` of type `RingHom A B`, given by the parameter `ft`, this function adds
the instance `Algebra A B` to the context (if it does not already exist).

There is no particular reason why we demand both `f` and `ft` as arguments (as `ft` can be inferred
from `f`). However, before calling this function in `algebraize`, we have already computed `ft`,
so this saves us from having to recompute it.
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

/-- Given an expression `g.comp f` which is the composition of two `RingHom`s, this function adds
the instance `IsScalarTower A B C` to the context (if it does not already exist). -/
def addIsScalarTowerInstanceFromRingHomComp (fn : Expr) : TacticM Unit := withMainContext do
  -- TODO: this one is not very type safe, I am sure there will be errors in more complicated
  -- expressions. Maybe this one should be reverted to the Qq version
  let (_, l) := fn.getAppFnArgs
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

/-- This function takes an array of expressions `t`, all of which are assumed to be `RingHom`'s,
and searches through the local context to find any additional properties of these `RingHoms`,
then it tries to add the corresponding `Algebra` properties to the context. -/
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

end Algebraize

open Algebraize

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

/-- Version of `algebraize`, which only adds algebra instances and `IsScalarTower` instances. -/
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
