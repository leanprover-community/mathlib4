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
a proof of `∀ ... (X : Cat), η.app X = θ.app X`, and finally simplifying the conclusion using some
basic lemmas in the bicategory `Cat`:
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for automatically generating bicategorical lemmas about 2-morphisms which the
simplifier can use in expressions that might involve both components of 2-morphisms,
and 1-morphisms. (TODO: write more)

There is also a term elaborator `to_app_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic
open Qq

namespace CategoryTheory

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics.  -/
-- TODO: is this even needed?
theorem eq_app' {C D : Cat} {f g : C ⟶ D} {η θ : f ⟶ g} (w : η = θ) (X : C) :
    η.app X = θ.app X :=
  congrArg (NatTrans.app · X) w

/-- Simplify an expression in `Cat` using basic properties of `NatTrans.app`. -/
def catAppSimp (e : Expr) : MetaM Simp.Result :=
  -- TODO: figure out which ones are necessary
  simpOnlyNames [
    ``Cat.whiskerLeft_app, ``Cat.whiskerRight_app, ``Cat.id_app, ``Cat.comp_app,
    ``Cat.eqToHom_app] e
    (config := { decide := false })

/--
Given a term of type `∀ ..., η = θ`, where `η θ : f ⟶ g` are 2-morphisms in some bicategory
`B`, which is bound by the `∀` binder, get the corresponding equation in the bicategory `Cat`. -/
-- TODO: mention levelMVars argument in docstring above
def to_appExpr (e : Expr) (levelMVars : List Level) : MetaM Expr := do
  let (args, binderInfos, conclusion) ← forallMetaTelescope (← inferType e)
  -- Find the metavariable corresponding to the bicategory, by anylizing `η = θ` (i.e. conclusion)
  let η := (Expr.getAppArgsN conclusion 2)[0]! -- `η` in the equality above
  let f := (Expr.getAppArgsN (← inferType η) 2)[0]! -- the domain of `η`
  let a := (Expr.getAppArgsN (← inferType f) 2)[1]! -- the domain of `f`
  let B_pre ← inferType a -- the bicategory
  let B := (← getMVars B_pre)[0]!
  let some BIdx := args.findIdx? (· == .mvar B)
    | throwError "TODO"
  -- Create level metavariables to be used for `Cat.{v u}`
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  -- Assign the right level of B, so that it corresponds to the level of `Cat`
  let _ ← isLevelDefEq (← Meta.getDecLevel B_pre) (Level.max (Level.max (u.succ) u) (v.succ))
  B.assign (.const ``Cat [u, v])
  let some inst := args[BIdx + 1]?
    | throwError "TODO"
  -- Assign the right levels for the bicategory instance of `B`
  let instlvl ← Meta.getLevel (← inferType inst)
  let instlvlMVars := levelMVars.filter fun l => l.occurs instlvl && l != u
  forM instlvlMVars fun l => do
    let _ ← isLevelDefEq l (Level.max u v)
  inst.mvarId!.assign (← synthInstanceQ q(Bicategory.{max u v, max u v} Cat.{u, v}))
  -- TODO: would be better if I could use `mkAppOptM'` straight away, but it
  -- tries to initialize all instance arguments :(
  let applied := mkAppN e args
  let mvars := (← getMVars applied).map (Expr.mvar)
  -- Erease the binderinfos for the bicategory and the instance
  let binderInfos := binderInfos.eraseIdx BIdx
  let binderInfos := binderInfos.eraseIdx BIdx
  -- Recursive function which applies `mkLambdaFVars` stepwise
  -- (so that each step can have different binderinfos)
  let rec apprec (i : Nat) (e : Expr) : MetaM Expr := do
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
  mapForallTelescope (fun e => do simpType catAppSimp (← mkAppM ``eq_app' #[e])) e

/--
Adding `@[to_app]` to a lemma named `F` of shape `∀ .., η = θ`, where `η θ : f ⟶ g` are 2-morphisms
in some bicategory, create a new lemma named `F_app`. This lemma is obtained by specializing the
bicategory in which the equality is taking place to `Cat`, then applying `NatTrans.app` to obtain
a proof of `∀ ... (X : Cat), η.app X = θ.app X`, and finally simplifying the conclusion using some
basic lemmas in the bicategory `Cat`:
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

TODO: whiskering example
So, for example, if the conclusion of `F` is `a ≫ f = g` then
the conclusion of `F_assoc` will be `a ≫ (b ≫ h) = g ≫ h` (note that `≫` reassociates
to the right so the brackets will not appear in the statement).

This is useful for automatically generating bicategorical lemmas about 2-morphisms which the
simplifier can use in expressions that might involve both components of 2-morphisms,
and 1-morphisms. (TODO: write more)

Note that if you want both the lemma and the new lemma to be
`simp` lemmas, you should tag the lemma `@[to_app (attr := simp)]`.
The variant `@[simp, to_app]` on a lemma `F` will tag `F` with `@[simp]`,
but not `F_app` (this is sometimes useful).
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
      let newValue ←toAppExpr (← to_appExpr value levelMVars)
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
