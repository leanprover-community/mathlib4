/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nick Kuhn, Arend Mellendijk, Christian Merten, Calle Sönne, Adam Topaz
-/

import Mathlib.Algebra.Algebra.Tower

/-!

## Algebraize tactic

This file defines the `algebraize` tactic. The basic functionality of this tactic is to
automatically add `Algebra` instances given `RingHom`s. For example, `algebraize [f, g]` where
`f : A →+* B` and `g : B →+* C` are `RingHom`s, will add the instances `Algebra A B` and
`Algebra B C` corresponding to these `RingHom`s.

## Further functionality

When given a composition of `RingHom`s, e.g. `algebraize [g.comp f]`, the tactic will also try to
add the instance `IsScalarTower A B C` if possible.

After having added suitable `Algebra` and `IsScalarTower` instances, the tactic will search through
the local context for `RingHom` properties that can be converted to properties of the corresponding
`Algebra`. For example, given `f : A →+* B` and `hf : f.FiniteType`, then `algebraize [f]` will add
the instance `Algebra A B` and the corresponding property `Algebra.FiniteType A B`. The tactic knows
which `RingHom` properties have a corresponding `Algebra` property through the `algebraize`
attribute.

## Algebraize attribute

The `algebraize` attribute is used to tag `RingHom` properties that can be converted to `Algebra`
properties. It assumes that the tagged declaration has a name of the form `RingHom.Property` and
that the corresponding `Algebra` property has the name `Algebra.Property`.

If not, the `Name` of the corresponding algebra property can be provided as optional argument. The
specified declaration should be one of the following:

1. An inductive type (i.e. the `Algebra` property itself), in this case it is assumed that the
`RingHom` and the `Algebra` property are definitionally the same, and the tactic will construct the
`Algebra` property by giving the `RingHom` property as a term. Due to how this is performed, we also
need to assume that the `Algebra` property can be constructed only from the homomorphism, so it
cannot have any other explicit arguments.
2. A lemma (or constructor) proving the `Algebra` property from the `RingHom` property. In this case
it is assumed that the `RingHom` property is the final argument, and that no other explicit argument
is needed. The tactic then constructs the `Algebra` property by applying the lemma or constructor.

Here are three examples of properties tagged with the `algebraize` attribute:
```
@[algebraize]
def RingHom.FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
```
An example when the `Name` is provided (as the `Algebra` does not have the expected name):
```
@[algebraize Module.Finite]
def RingHom.Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B
```
An example with a constructor as parameter (as the two properties are not definitionally the same):
```
@[algebraize Algebra.Flat.out]
class RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop where
  out : f.toAlgebra.Flat := by infer_instance
```

## algebraize_only

To avoid searching through the local context and adding corresponding `Algebra` properties, use
`algebraize_only` which only adds `Algebra` and `IsScalarTower` instances.
-/

open Lean Elab Tactic Term Meta

namespace Lean.Attr

/-- Function that extracts the name of the corresponding `Algebra` property from a `RingHom`
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
properties. Using an (optional) parameter, it will also generate a `Name` of a declaration which
will help the `algebraize` tactic access the corresponding `Algebra` property.

There are two cases for what declaration corresponding to this `Name` can be.

1. An inductive type (i.e. the `Algebra` property itself), in this case it is assumed that the
`RingHom` and the `Algebra` property are definitionally the same, and the tactic will construct the
`Algebra` property by giving the `RingHom` property as a term.
2. A lemma (or constructor) proving the `Algebra` property from the `RingHom` property. In this case
it is assumed that the `RingHom` property is the final argument, and that no other explicit argument
is needed. The tactic then constructs the `Algebra` property by applying the lemma or constructor.

Finally, if no argument is provided to the `algebraize` attribute, it is assumed that the tagged
declaration has name `RingHom.Property` and that the corresponding `Algebra` property has name
`Algebra.Property`. The attribute then returns `Algebra.Property` (so assume case 1 above). -/
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

This function also requires the type of `f`, given by the parameter `ft`. The reason this is done
(even though `ft` can be inferred from `f`) is to avoid recomputing `ft` in the `algebraize` tactic,
as when `algebraize` calls `addAlgebraInstanceFromRingHom` it has already computed `ft`. -/
def addAlgebraInstanceFromRingHom (f ft : Expr) : TacticM Unit := withMainContext do
  let (_, l) := ft.getAppFnArgs
  -- The type of the corresponding algebra instance
  let alg ← mkAppOptM ``Algebra #[l[0]!, l[1]!, none, none]
  -- If the instance already exists, we do not do anything
  unless (← synthInstance? alg).isSome do
  liftMetaTactic fun mvarid => do
    let nm ← mkFreshBinderNameForTactic `algInst
    let mvar ← mvarid.define nm alg (← mkAppM ``RingHom.toAlgebra #[f])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

/-- Given an expression `g.comp f` which is the composition of two `RingHom`s, this function adds
the instance `IsScalarTower A B C` to the context (if it does not already exist). -/
def addIsScalarTowerInstanceFromRingHomComp (fn : Expr) : TacticM Unit := withMainContext do
  let (_, l) := fn.getAppFnArgs
  let tower ← mkAppOptM ``IsScalarTower #[l[0]!, l[1]!, l[2]!, none, none, none]
  -- If the instance already exists, we do not do anything
  unless (← synthInstance? tower).isSome do
  liftMetaTactic fun mvarid => do
    let nm ← mkFreshBinderNameForTactic `scalarTowerInst
    let h ← mkFreshExprMVar (← mkAppM ``Eq #[
      ← mkAppOptM ``algebraMap #[l[0]!, l[2]!, none, none, none],
      ← mkAppM ``RingHom.comp #[
        ← mkAppOptM ``algebraMap #[l[1]!, l[2]!, none, none, none],
        ← mkAppOptM ``algebraMap #[l[0]!, l[1]!, none, none, none]]])
    -- Note: this could fail, but then `algebraize` will just continue, and won't add this instance
    h.mvarId!.refl
    let val ← mkAppOptM ``IsScalarTower.of_algebraMap_eq'
      #[l[0]!, l[1]!, l[2]!, none, none, none, none, none, none, h]
    let mvar ← mvarid.define nm tower val
    let (_, mvar) ← mvar.intro1P
    return [mvar]

/-- This function takes an array of expressions `t`, all of which are assumed to be `RingHom`s,
and searches through the local context to find any additional properties of these `RingHoms`, after
which it tries to add the corresponding `Algebra` properties to the context. It only looks for
properties that have been tagged with the `algebraize` attribute, and uses this tag to find the
corresponding `Algebra` property. -/
def addProperties (t : Array Expr) : TacticM Unit := withMainContext do
  let ctx ← getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then return
    let (nm, args) := (← instantiateMVars decl.type).getAppFnArgs
    -- Check if the type of the current hypothesis has been tagged with the `algebraize` attribute
    match Attr.algebraizeAttr.getParam? (← getEnv) nm with
    -- If it has, `p` will either be the name of the corresponding `Algebra` property, or a
    -- lemma/constructor.
    | some p =>
      let cinfo ← try getConstInfo p catch _ =>
        logWarning m!"Hypothesis {decl.toExpr} has type{indentD decl.type}.\n\
          Its head symbol {.ofConstName nm} is (effectively) tagged with `@[algebraize {p}]`, \
          but no constant{indentD p}\nhas been found.\n\
          Check for missing imports, missing namespaces or typos."
        return
      let p' ← mkConstWithFreshMVarLevels p
      let (pargs, _, _) ← forallMetaTelescope (← inferType p')
      let tp' := mkAppN p' pargs

      let getValType : MetaM (Option (Expr × Expr)) := do
        /- If the attribute points to the corresponding `Algebra` property itself, we assume that it
        is definitionally the same as the `RingHom` property. Then, we just need to construct its
        type and the local declaration will already give a valid term. -/
        if cinfo.isInductive then
          pargs[0]!.mvarId!.assignIfDefEq args[0]!
          pargs[1]!.mvarId!.assignIfDefEq args[1]!
          -- This should be the type `Algebra.Property A B`
          let tp ← instantiateMVars tp'
          if ← isDefEqGuarded decl.type tp then return (decl.toExpr, tp)
          else return none
        /- Otherwise, the attribute points to a lemma or a constructor for the `Algebra` property.
        In this case, we assume that the `RingHom` property is the last argument of the lemma or
        constructor (and that this is all we need to supply explicitly). -/
        else
          try pargs.back!.mvarId!.assignIfDefEq decl.toExpr catch _ => return none
          let val ← instantiateMVars tp'
          let tp ← inferType val -- This should be the type `Algebra.Property A B`.
          return (val, tp)
      let some (val, tp) ← getValType | return
      /- Find all arguments to `Algebra.Property A B` or `Module.Property A B` which are
        of the form `RingHom.toAlgebra f`, `RingHom.toModule f`
        or `Algebra.toModule (RingHom.toAlgebra f)`. -/
      let ringHom_args ← tp.getAppArgs.filterMapM <| fun x => liftMetaM do
        let y := (← whnfUntil x ``Algebra.toModule) >>= (·.getAppArgs.back?)
        return ((← whnfUntil (y.getD x) ``RingHom.toAlgebra) <|> (← whnfUntil x ``RingHom.toModule))
          >>= (·.getAppArgs.back?)
      /- Check that we're not reproving a local hypothesis, and that all involved `RingHom`s are
        indeed arguments to the tactic. -/
      unless (← synthInstance? tp).isSome || !(← ringHom_args.allM (fun z => t.anyM
        (withoutModifyingMCtx <| isDefEq z ·))) do
      liftMetaTactic fun mvarid => do
        let nm ← mkFreshBinderNameForTactic `algebraizeInst
        let (_, mvar) ← mvarid.note nm val tp
        return [mvar]
    | none => return

/-- Configuration for `algebraize`. -/
structure Config where
  /-- If true (default), the tactic will search the local context for `RingHom` properties
    that can be converted to `Algebra` properties. -/
  properties : Bool := true
deriving Inhabited

/-- Function elaborating `Algebraize.Config`. -/
declare_config_elab elabAlgebraizeConfig Algebraize.Config

end Algebraize

open Algebraize Lean.Parser.Tactic

/-- A list of terms passed to `algebraize` as argument. -/
syntax algebraizeTermSeq := " [" withoutPosition(term,*,?) "]"

/-- Tactic that, given `RingHom`s, adds the corresponding `Algebra` and (if possible)
`IsScalarTower` instances, as well as `Algebra` corresponding to `RingHom` properties available
as hypotheses.

Example: given `f : A →+* B` and `g : B →+* C`, and `hf : f.FiniteType`, `algebraize [f, g]` will
add the instances `Algebra A B`, `Algebra B C`, and `Algebra.FiniteType A B`.

See the `algebraize` tag for instructions on what properties can be added.

The tactic also comes with a configuration option `properties`. If set to `true` (default), the
tactic searches through the local context for `RingHom` properties that can be converted to
`Algebra` properties. The macro `algebraize_only` calls
`algebraize -properties`,
so in other words it only adds `Algebra` and `IsScalarTower` instances. -/
syntax "algebraize " optConfig (algebraizeTermSeq)? : tactic

elab_rules : tactic
  | `(tactic| algebraize $cfg:optConfig $args) => withMainContext do
    let cfg ← elabAlgebraizeConfig cfg
    let t ← match args with
    | `(algebraizeTermSeq| [$rs,*]) => rs.getElems.mapM fun i => Term.elabTerm i none
    | _ =>
      throwError ""
    if t.size == 0 then
      logWarningAt args "`algebraize []` without arguments has no effect!"
    -- We loop through the given terms and add algebra instances
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const ``RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError m!"{f} is not of type `RingHom`"
    -- After having added the algebra instances we try to add scalar tower instances
    for f in t do
      match f.getAppFn with
      | Expr.const ``RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue

    -- Search through the local context to find other instances of algebraize
    if cfg.properties then
      addProperties t
  | `(tactic| algebraize $[$config]?) => do
    throwError "`algebraize` expects a list of arguments: `algebraize [f]`"

/-- Version of `algebraize`, which only adds `Algebra` instances and `IsScalarTower` instances,
but does not try to add any instances about any properties tagged with
`@[algebraize]`, like for example `Finite` or `IsIntegral`. -/
syntax "algebraize_only" (ppSpace algebraizeTermSeq)? : tactic

macro_rules
  | `(tactic| algebraize_only $[$args]?) =>
    `(tactic| algebraize -properties $[$args]?)

end Mathlib.Tactic
