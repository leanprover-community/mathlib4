/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Util.AddRelatedDecl

/-!
# The `to_app` attribute

Adding `@[to_app]` to a lemma named `F` of shape `∀ .., η = θ`, where `η θ : f ⟶ g` are 2-morphisms
in some bicategory, create a new lemma named `F_app`. This lemma is obtained by specializing the
bicategory in which the equality is taking place to `Cat`, then applying `NatTrans.app` to obtain
a proof of `∀ ... (X : Cat), η.app X = θ.app X`, and finally simplifying the conclusion using the
following basic lemmas about `NatTrans.app`:
`Cat.whiskerLeft_app`, `Cat.whiskerRight_app`, `Cat.id_app`, `Cat.comp_app` and `Cat.eqToHom_app`

So, for example, if the conclusion of `F` is `f ◁ η = θ` then the conclusion of `F_app` will be
`η.app (f.obj X) = θ.app X`.

This is useful for automatically generating lemmas that can be applied to expressions of 1-morphisms
in `Cat` which contain components of 2-morphisms.

There is also a term elaborator `to_app_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic
open Qq

namespace CategoryTheory

/-- Simplify an expression in `Cat` using basic properties of `NatTrans.app`. -/
def catAppSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [
    ``Cat.whiskerLeft_app, ``Cat.whiskerRight_app, ``Cat.id_app, ``Cat.comp_app,
    ``Cat.eqToHom_app] e
    (config := { decide := false })

/--
Given a term of type `∀ ..., η = θ`, where `η θ : f ⟶ g` are 2-morphisms in some bicategory
`B`, which is bound by the `∀` binder, get the corresponding equation in the bicategory `Cat`.

The term is also required to only contain universe metavariables, and these should also be passed
as an argument `levelMVars` to this function. This is necessary because when specializing to `Cat`,
we need to set the levels of the bicategory argument that gets specialized in terms of the levels of
`Cat`.

It is also important that in arguments to the `∀` binder, the bicategory `B` to be specialized is
followed immediately by immediately by the instance `[Bicategory B]`. Otherwise this function will
not be able to find, and replace, this instance.
(Note: this issue would go away if one could use `mkAppOptM'` directly, but it tries to initalize
all instance arguments, so it can not be used in this case.)
-/
def toCatExpr (e : Expr) (levelMVars : List Level) : MetaM Expr := do
  let (args, binderInfos, conclusion) ← forallMetaTelescope (← inferType e)
  -- Find the metavariable corresponding to the bicategory, by anylizing `η = θ` (i.e. conclusion)
  let η := (Expr.getAppArgsN conclusion 2)[0]! -- `η` in the equality above
  let f := (Expr.getAppArgsN (← inferType η) 2)[0]! -- the domain of `η`
  let a := (Expr.getAppArgsN (← inferType f) 2)[1]! -- the domain of `f`
  let B_pre ← inferType a -- the bicategory
  let B := (← getMVars B_pre)[0]!
  let some BIdx := args.findIdx? (· == .mvar B)
    | throwError "Can not find the bicategory {B} in the arguments of {e}"
  -- Create level metavariables to be used for `Cat.{v u}`
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  -- Assign the right level of B, so that it corresponds to the level of `Cat`
  let _ ← isLevelDefEq (← Meta.getDecLevel B_pre) (Level.max (Level.max (u.succ) u) (v.succ))
  B.assign (.const ``Cat [u, v])
  let some inst := args[BIdx + 1]?
    | throwError "The bicategory {B} is not immediately followed by a bicategory instance in {e}"
  -- Assign the right levels for the bicategory instance of `B`
  let instlvl ← Meta.getLevel (← inferType inst)
  let instlvlMVars := levelMVars.filter fun l => l.occurs instlvl && l != u
  forM instlvlMVars fun l => do
    let _ ← isLevelDefEq l (Level.max u v)
  inst.mvarId!.assign (← synthInstanceQ q(Bicategory.{max u v, max u v} Cat.{u, v}))
  /- NOTE: if there was a version of `mkAppOptM'` that didn't try to initialize all instances,
    we could use that here and return immediately. Instead we use `mkLambdaFVars` below. -/
  let applied := mkAppN e args
  let mvars := (← getMVars applied).map (Expr.mvar)
  -- Erease the binderinfos for the bicategory and the instance
  let binderInfos := binderInfos.eraseIdx BIdx
  let binderInfos := binderInfos.eraseIdx BIdx
  let rec
  /-- Recursive function which applies `mkLambdaFVars` stepwise
  (so that each step can have different binderinfos) -/
    apprec (i : Nat) (e : Expr) : MetaM Expr := do
    if i < mvars.size then
      let mvar := mvars[i]!
      let bi := binderInfos[i]!
      let e ← mkLambdaFVars #[mvar] (← apprec (i + 1) e) (binderInfoForMVars := bi)
      return e
    else
      return e
  let applied ← apprec 0 applied
  return applied

/--
Given morphisms `f g : C ⟶ D` in the bicategory `Cat`, and an equation `η = θ` between 2-morphisms
(possibly after a `∀` binder), produce the equation `∀ (X : C), f.app X = g.app X`, and simplify
it using basic lemmas about `NatTrans.app`. -/
def toAppExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType catAppSimp (← mkAppM ``NatTrans.congr_app #[e])) e

/--
Adding `@[to_app]` to a lemma named `F` of shape `∀ .., η = θ`, where `η θ : f ⟶ g` are 2-morphisms
in some bicategory, create a new lemma named `F_app`. This lemma is obtained by specializing the
bicategory in which the equality is taking place to `Cat`, then applying `NatTrans.app` to obtain
a proof of `∀ ... (X : Cat), η.app X = θ.app X`, and finally simplifying the conclusion using some
basic lemmas in the bicategory `Cat`:
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

So, for example, if the conclusion of `F` is `f ◁ η = θ` then the conclusion of `F_app` will be
`η.app (f.obj X) = θ.app X`.

This is useful for automatically generating lemmas that can be applied to expressions of 1-morphisms
in `Cat` which contain components of 2-morphisms.

Note that if you want both the lemma and the new lemma to be `simp` lemmas, you should tag the lemma
`@[to_app (attr := simp)]`. The variant `@[simp, to_app]` on a lemma `F` will tag `F` with
`@[simp]`, but not `F_app` (this is sometimes useful).
-/
syntax (name := to_app) "to_app" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `to_app
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_app $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_app` can only be used as a global attribute"
    addRelatedDecl src "_app" ref stx? fun type value levels => do
      let levelMVars ← levels.mapM λ _ => mkFreshLevelMVar
      let value ← mkExpectedTypeHint value type
      let value := value.instantiateLevelParams levels levelMVars
      let newValue ← toAppExpr (← toCatExpr value levelMVars)
      let r := (← getMCtx).levelMVarToParam (λ _ => false) (λ _ => false) newValue
      let output := (r.expr, r.newParamNames.toList)
      pure output
  | _ => throwUnsupportedSyntax }

open Term in
/--
Given an equation `t` of the form `η = θ` between 2-morphisms `f ⟶ g` with `f g : C ⟶ D` in the
bicategory `Cat` (possibly after a `∀` binder), `to_app_of% t` produces the equation
`∀ (X : C), η.app X = θ.app X` (where `X` is an object in the domain of `f` and `g`), and simplifies
it suitably using basic lemmas about `NatTrans.app`.
-/
elab "to_app_of% " t:term : term => do
  toAppExpr (← elabTerm t none)

end CategoryTheory
