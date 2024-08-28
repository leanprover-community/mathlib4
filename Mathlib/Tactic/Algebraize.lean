/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nick Kuhn, Arend Mellendijk, Christian Merten, Calle Sönne, Adam Topaz
-/

import Mathlib.Algebra.Algebra.Tower

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
attribute. This attribute has a parameter `name` which should be the name of a constructor of the
the corresponding `Algebra` property, which takes the `RingHom` property as an argument.

In many cases, if `hf : f.Property` is a `RingHom` property, one can access the corresponding
`Algebra` property just by a type hint, i.e. `hf : Algebra.Property`. In these cases, one does not
have to give a constructor as an argument to the `algebraize` attribute, and can instead just give
the name of the `Algebra` property. For example, `RingHom.FiniteType` is tagged as follows:
```
@[algebraize]
def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
```
This does not work with `RingHom.Flat`, which is instead tagged as follows
```
@[algebraize Algebra.Flat.out]
class RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop where
  out : f.toAlgebra.Flat := by infer_instance
```

To avoid searching through the local context and adding corresponding `Algebra` properties, use
`algebraize'` which only adds `Algebra` and `IsScalarTower` instances.

-/

open Lean Elab Tactic Term Meta

namespace Lean.Attr

/-- Function that extracts the name of the corresponding `Algebra` property from the a `RingHom`
property that has been tagged with the `algebraize` attribute. This is done by either returning the
parameter of the attribute, or by assuming that the tagged declaration has name `RingHom.Property`
and then returning `Algebra.Property`. -/
def algebraizeGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize $name:ident) => return name.getId
  /- If no argument is provided, assume `thm` is of the form `RingHom.Property`,
  and return `Algebra.Property` -/
  | `(attr| algebraize) =>
    match thm with
    | .str `RingHom t => return .str `Algebra t
    | _ =>
      throwError "theorem name must be of the form `RingHom.Property` if no argument is provided"
  | _ => throwError "unexpected algebraize argument"

/-- A user attribute that is used to tag `RingHom` properties that can be converted to `Algebra`
properties.

The attribute has a parameter `name` which should be the name of the corresponding
`Algebra` property (or a constructor of it). If no argument is provided, the attribute assumes that
the tagged declaration has name `RingHom.Property` and the corresponding `Algebra` property has name
`Algebra.Property`.

Furthermore, it is assumed that the last argument of the `RingHom` property is the `RingHom` itself,
and that the declaration corresponding to `name`

-/
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

/-- Given an expression `f` of type `RingHom A B` where `A` and `B` are commutative semirings,
this function adds the instance `Algebra A B` to the context (if it does not already exist).

This function also requries the type of `f`, given by the parameter `ft`. The reason this is done
(even though `ft` can be inferred from `f`) is to avoid recomputing `ft` in the `algebraize` tactic,
as when `algebraize` calls `addAlgebraInstanceFromRingHom` it has already computed `ft`.
-/
def addAlgebraInstanceFromRingHom (f ft : Expr) : TacticM Unit := withMainContext do
  let (_, l) := ft.getAppFnArgs
  -- The type of the corresponding algebra instance
  let alg ← mkAppOptM `Algebra #[l[0]!, l[1]!, none, none]
  try let _ ← synthInstance alg -- If the instance already exists, we do not do anything
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `algInst
    let mvar ← mvarid.define nm alg (← mkAppM `RingHom.toAlgebra #[f])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

/-- Given an expression `g.comp f` which is the composition of two `RingHom`s, this function adds
the instance `IsScalarTower A B C` to the context (if it does not already exist). -/
def addIsScalarTowerInstanceFromRingHomComp (fn : Expr) : TacticM Unit := withMainContext do
  let (_, l) := fn.getAppFnArgs
  let tower ← mkAppOptM `IsScalarTower #[l[0]!, l[1]!, l[2]!, none, none, none]
  try let _ ← synthInstance tower -- If the instance already exists, we do not do anything
  catch _ => liftMetaTactic fun mvarid => do
    let nm ← mkFreshUserName `scalarTowerInst
    let h ← mkFreshExprMVar (← mkAppM `Eq #[
      ← mkAppOptM `algebraMap #[l[0]!, l[2]!, none, none, none],
      ← mkAppM `RingHom.comp #[
        ← mkAppOptM `algebraMap #[l[1]!, l[2]!, none, none, none],
        ← mkAppOptM `algebraMap #[l[0]!, l[1]!, none, none, none]]])
    -- Note: this could fail, but then `algebraize` will just continue, and won't add this instance
    h.mvarId!.refl
    let mvar ← mvarid.define nm tower
      (← mkAppOptM `IsScalarTower.of_algebraMap_eq'
        #[l[0]!, l[1]!, l[2]!, none, none, none, none, none, none, h])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

/-- This function takes an array of expressions `t`, all of which are assumed to be `RingHom`'s,
and searches through the local context to find any additional properties of these `RingHoms`,
then it tries to add the corresponding `Algebra` properties to the context. It only looks for
properties that have been tagged with the `algebraize` attribute, and uses this to find the
corresponding `Algebra` property. -/
def searchContext (t : Array Expr) : TacticM Unit := withMainContext do
  let ctx ← MonadLCtx.getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then return
    let (nm, args) := decl.type.getAppFnArgs
    -- Check if the type of the current hypothesis has been tagged with the `algebraize` attribute
    match Attr.algebraizeAttr.getParam? (← getEnv) nm with
    -- If it has, `p` will be the name of the corresponding `Algebra` property (or a constructor)
    | some p =>
      -- The last argument is the `RingHom` property is assumed to be `f` (TODO MENTION ELSEWHERE)
      let f := args[args.size - 1]!
      -- Check that `f` appears in the list of functions given to `algebraize`
      if ¬ (← t.anyM (fun j => Meta.isDefEq j f)) then return

      let cinfo ← getConstInfo p
      let n ← getExpectedNumArgs cinfo.type
      let pargs := Array.mkArray n (none : Option Expr)
      /- If the attribute points to the corresponding `Algebra` property itself, we assume that it
      is definitionally the same as the `RingHom` property. Then, we just need to construct its type
      and the local declaration will already give a valid term. -/
      if cinfo.isInductive then
        let pargs := pargs.set! 0 args[0]!
        let pargs := pargs.set! 1 args[1]!
        let tp ← mkAppOptM p pargs -- This should be the type `Algebra.Property A B`
        liftMetaTactic fun mvarid => do
          let nm ← mkFreshUserName `AlgebraizeInst
          let (_, mvar) ← mvarid.note nm decl.toExpr tp
          return [mvar]
      /- Otherwise, the attribute points to a constructor of the `Algebra` property. In this case,
      we assume that the `RingHom` property is the last argument of the constructor (and that
      this is all we need to supply explicitly). -/
      else
        let pargs := pargs.set! (n - 1) decl.toExpr
        let val ← mkAppOptM p pargs
        liftMetaTactic fun mvarid => do
          let nm ← mkFreshUserName `AlgebraizeInst
          let (_, mvar) ← mvarid.note nm val
          return [mvar]
    | none => return

end Algebraize

open Algebraize

/-- Tactic that, given `RingHom`s, adds the corresponding `Algebra` and (if possible)
`IsScalarTower` instances, as well as `Algebra` corresponding to `RingHom` properties available
as hypotheses.

Example: given `f : A →+* B` and `g : B →+* C`, and `hf : f.FiniteType`, `algebraize f g` will add
the instances `Algebra A B`, `Algebra B C`, and `Algebra.FiniteType A B`.

See the `algebraize` tag for instructions on what properties can be added. -/
syntax "algebraize" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    let t ← t.mapM fun i => Term.elabTerm i none
    -- We loop through the given terms and add algebra instances
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const `RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError m!"{f} is not of type `RingHom`"
    -- After having added the algebra instances we try to add scalar tower instances
    for f in t do
      match f.getAppFn with
      | Expr.const `RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue

    -- Search through the local context to find other instances of algebraize
    searchContext t

/-- Version of `algebraize`, which only adds `Algebra` instances and `IsScalarTower` instances. -/
syntax "algebraize'" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize' $[$t:term]*) => do
    let t ← t.mapM fun i => Term.elabTerm i none
    -- We loop through the given terms and add algebra instances
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const `RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError m!"{f} is not of type `RingHom`"
    -- After having added the algebra instances we try to add scalar tower instances
    for f in t do
      match f.getAppFn with
      | Expr.const `RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue


end Mathlib.Tactic
