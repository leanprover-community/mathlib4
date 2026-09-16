/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public meta import Mathlib.Lean.Meta.Simp
public meta import Mathlib.Util.AddRelatedDecl

/-!
# The `to_app` attribute

Adding `@[to_app]` to a lemma named `F` of shape `∀ .., η = θ`, where either
* `η θ : f ⟶ g` are 2-morphisms in some bicategory, or
* `η θ : NatTrans F G` are natural transformations between functors,
creates a new lemma named `F_app` stating equality of their components. Both sides are simplified
using the basic lemmas about components listed in `catAppSimp`.

For a theorem about an arbitrary bicategory `B`, this first substitutes `Cat` for the quantified
`B` and `Cat.bicategory` for its instance. A theorem already about `Cat` only needs the projection
from 2-morphisms to natural transformations. A theorem about natural transformations is used
directly, retaining its universe parameters, including independent source and target universes.

When the simplified equation holds by `rfl`, the generated declaration uses that proof. Lean's
usual inference determines whether it is a `defeq` or `backward_defeq` lemma; the latter is used
by `dsimp` only with `set_option backward.defeqAttrib.useBackward true`.

So, for example, if the conclusion of `F` is `f ◁ η = θ` then the conclusion of `F_app` will be
`η.toNatTrans.app (f.obj X) = θ.toNatTrans.app X`.

This is useful for automatically generating lemmas that can be applied to expressions of 1-morphisms
in `Cat` which contain components of 2-morphisms.

There is also a term elaborator `to_app_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory
namespace Mathlib.Tactic.CategoryTheory.ToApp

/-- Simplify components of natural transformations and 2-morphisms in `Cat`. -/
def catAppSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [
    ``Cat.Hom.comp_toFunctor, ``Functor.comp_obj, ``Cat.Hom.comp_obj, ``Cat.whiskerLeft_app,
    ``Cat.whiskerRight_app, ``Cat.Hom₂.id_app, ``Cat.Hom₂.comp_app, ``Cat.eqToHom_app,
    ``NatTrans.id_app', ``NatTrans.vcomp_app, ``NatTrans.id_app, ``NatTrans.comp_app,
    ``NatTrans.hcomp_id_app, ``NatTrans.id_hcomp_app, ``Functor.whiskerLeft_app,
    ``Functor.whiskerRight_app, ``CategoryTheory.eqToHom_app,
    ``Cat.leftUnitor_hom_app, ``Cat.leftUnitor_inv_app, ``Cat.rightUnitor_hom_app,
    ``Cat.rightUnitor_inv_app, ``Cat.associator_hom_app, ``Cat.associator_inv_app, ``eqToHom_refl,
    ``Category.comp_id, ``Category.id_comp] e
    (config := { decide := false })

/--
Given a term of type `∀ ..., η = θ`, where `η θ : f ⟶ g` are 2-morphisms in some bicategory
`B`, which is bound by the `∀` binder, get the corresponding equation in the bicategory `Cat`.
This substitutes the bicategory and its instance; it does not embed an arbitrary bicategory
into `Cat`. An equation already in `Cat` can also be used directly.

It is important here that the levels in the term are level metavariables, as otherwise these will
not be reassignable to the corresponding levels of `Cat`. -/
def toCatExpr (e : Expr) : MetaM Expr := do
  let (args, binderInfos, conclusion) ← forallMetaTelescopeReducing (← inferType e)
  -- Find the expression corresponding to the bicategory, by analyzing `η = θ` (i.e. conclusion)
  let some (type, _, _) := (← whnf conclusion).eq?
    | throwError "`to_app` expects an equality"
  let some type ← whnfUntil type ``Quiver.Hom
    | throwError "`to_app` expects an equality of natural transformations or 2-morphisms"
  let f := type.getArg! 2
  let some type ← whnfUntil (← inferType f) ``Quiver.Hom
    | throwError "`to_app` expects an equality of natural transformations or 2-morphisms"
  let B := type.getArg! 0
  let inst? ← args.findM? fun x => do
    let some type ← whnfUntil (← inferType x) ``Bicategory | return false
    return type.getArg! 0 == B
  -- Create level metavariables to be used for `Cat.{v, u}`
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  -- Assign `B` to `Cat.{v, u}`
  unless ← isDefEq B (.const ``Cat [v, u]) do
    throwError "`to_app` cannot specialize the bicategory {B} to `Cat`"
  -- Assign the right bicategory instance to `Cat.{v, u}`
  -- An equality already in `Cat` need not have a quantified bicategory instance.
  if let some inst := inst? then
    unless ← isDefEq inst (.const ``CategoryTheory.Cat.bicategory [v, u]) do
      throwError "`to_app` cannot specialize the bicategory instance to `Cat.bicategory`"
  -- Abstract the remaining arguments, retaining each original binder's explicitness.
  (args.zip binderInfos).foldrM (fun (arg, bi) value => do
    if arg == B || inst? == some arg then return value
    mkLambdaFVars #[arg] value (binderInfoForMVars := bi)) (mkAppN e args)

universe v u in
lemma toNatTrans_congr {C D : Cat.{v, u}} {F G : C ⟶ D} {η θ : F ⟶ G} (h : η = θ) :
  η.toNatTrans = θ.toNatTrans := congr(($h).toNatTrans)

/--
Given morphisms `f g : C ⟶ D` in the bicategory `Cat`, and an equation `η = θ` between 2-morphisms
(possibly after a `∀` binder), produce the equation `η.toNatTrans = θ.toNatTrans`
-/
def toNatTransExpr (e : Expr) : MetaM Expr := do
  forallTelescopeReducing (← inferType e) fun xs _ => do
    mkLambdaFVars xs (← mkAppM ``toNatTrans_congr #[mkAppN e xs])

/-- The two kinds of component projections, or a bicategory that still needs specialization. -/
inductive EqKind where
  | natTrans
  | cat
  | bicategory
  deriving BEq

/-- Inspect the equality before constructing a component proof.
Reducing the morphism type also handles notation and abbreviations. -/
def eqKind (e : Expr) : MetaM EqKind := do
  forallTelescopeReducing (← inferType e) (whnfType := true) fun _ type => do
    let some (type, _, _) := type.consumeMData.eq?
      | throwError "`to_app` expects an equality"
    let type ← whnf type
    if type.isAppOf ``NatTrans then return .natTrans
    if type.isAppOf ``Cat.Hom₂ then return .cat
    return .bicategory

/--
Given a theorem whose conclusion is an equation between either natural transformations between
functors or 2-morphisms in a bicategory, produce the component equation and its proof.
Simplify the component expressions and try `rfl` before constructing a proof from the source
theorem.
Keep the type separate so that a `rfl` proof does not replace the right-hand side by the left.
-/
def toAppTypeAndProof (e : Expr) : MetaM (Expr × Expr) := do
  let kind ← eqKind e
  let e ← if kind == .bicategory then toCatExpr e else pure e
  let app (η : Expr) : MetaM Expr := do
    let η ← if kind == .natTrans then pure η else mkAppM ``Cat.Hom₂.toNatTrans #[η]
    mkAppM ``NatTrans.app #[η]
  forallTelescopeReducing (← inferType e) (whnfType := true) fun xs eq => do
    let some (_, lhs, rhs) := eq.consumeMData.eq? | throwError "`to_app` expects an equality"
    let lhs ← app lhs
    let rhs ← app rhs
    forallBoundedTelescope (← inferType lhs) (some 1) fun ys _ => do
      let lhs ← catAppSimp (mkAppN lhs ys)
      let rhs ← catAppSimp (mkAppN rhs ys)
      let type ← mkEq lhs.expr rhs.expr
      -- Check the simplified statement: some of the simplification lemmas are not definitional.
      -- Do not assign the caller's metavariables merely to make this equation reflexive.
      let pf ← if ← withNewMCtxDepth <| isDefEq lhs.expr rhs.expr then
        mkEqRefl lhs.expr
      else do
        let e := mkAppN e xs
        let e ← if kind == .natTrans then pure e else toNatTransExpr e
        let mut pf ← mkAppM ``NatTrans.congr_app #[e, ys[0]!]
        if let some lhsProof := lhs.proof? then
          pf ← mkEqTrans (← mkEqSymm lhsProof) pf
        if let some rhsProof := rhs.proof? then
          pf ← mkEqTrans pf rhsProof
        pure pf
      return (← mkForallFVars (xs ++ ys) type, ← mkLambdaFVars (xs ++ ys) pf)

/-- Construct a componentwise equality, preserving its simplified statement as the inferred type. -/
def toAppExpr (e : Expr) : MetaM Expr := do
  let (type, pf) ← toAppTypeAndProof e
  mkExpectedTypeHint pf type

/--
Adding `@[to_app]` to a lemma named `F` of shape `∀ .., η = θ`, where either
* `η θ : f ⟶ g` are 2-morphisms in some bicategory, or
* `η θ : NatTrans F G` are natural transformations between functors,
creates a new lemma named `F_app` stating equality of components. A quantified bicategory is first
specialized to `Cat`; 2-morphisms in `Cat` are projected to natural transformations.
For natural transformations between functors `C ⥤ D`, the result is
`∀ ... (X : C), η.app X = θ.app X`, simplified on both sides using `catAppSimp`.

Note that if you want both the lemma and the new lemma to be `simp` lemmas, you should tag the lemma
`@[to_app (attr := simp)]`. The variant `@[simp, to_app]` on a lemma `F` will tag `F` with
`@[simp]`, but not `F_app` (this is sometimes useful).
-/
syntax (name := to_app) "to_app" optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `to_app
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_app $optAttr) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_app` can only be used as a global attribute"
    let tgt := src.appendAfter "_app"
    addRelatedDeclWithType src tgt ref optAttr fun value levels => do
      if (← eqKind value) != .bicategory then
        let (type, pf) ← toAppTypeAndProof value
        return (type, pf, levels)
      let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
      let value := value.instantiateLevelParams levels levelMVars
      let (type, pf) ← toAppTypeAndProof value
      -- Generalize both the statement and proof, including levels absent from a `rfl` proof.
      let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false)
        (← mkExpectedTypeHint pf type)
      setMCtx r.mctx
      return (r.expr.appFn!.appArg!, r.expr.appArg!, r.newParamNames.toList)
  | _ => throwUnsupportedSyntax }

open Term in
/--
Given an equation `t` of the form `η = θ` between either natural transformations between functors or
2-morphisms `f ⟶ g` with `f g : C ⟶ D` in the bicategory `Cat` (possibly after a `∀` binder),
`to_app_of% t` produces the equation `∀ (X : C), η.app X = θ.app X` for an object
`X` in the relevant source category, and simplify it suitably using basic lemmas about
`NatTrans.app`.
-/
elab "to_app_of% " t:term : term => do
  toAppExpr (← withSynthesizeLight <| elabTerm t none)

end Mathlib.Tactic.CategoryTheory.ToApp
