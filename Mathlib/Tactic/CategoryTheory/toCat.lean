/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Util.AddRelatedDecl
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The `toCat` attribute

Adding `@[toCat]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ⟶ Y` in some category
will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for automatically generating lemmas which the simplifier can use even on expressions
.......

There is also a term elaborator `toCat_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic
open Qq

namespace CategoryTheory

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics.  -/
theorem eq_app' {C D : Cat} {f g : C ⟶ D} {η θ : f ⟶ g} (w : η = θ) (X : C) :
    η.app X = θ.app X :=
  congrArg (NatTrans.app · X) w

/-- Simplify an expression using only the axioms of a category. -/
def catAppSimp (e : Expr) : MetaM Simp.Result :=
  -- TODO: figure out which ones are necessary
  simpOnlyNames [
    --``Category.comp_id, ``Category.id_comp, ``Category.assoc,
    ``Cat.id_obj, ``Cat.id_map, ``Cat.comp_obj, ``Cat.comp_map,
    ``Cat.whiskerLeft_app, ``Cat.whiskerRight_app, ``Cat.id_app, ``Cat.comp_app,
    ``Cat.eqToHom_app] e
    (config := { decide := false })

#check Lean.Expr.updateFVar!

#check Term.withSynthesize

#check mkLambdaFVars
#check forallMetaTelescopeReducing

#check getLevelMVarAssignment?
#check getLevel

#check getLevelMVarAssignment?

/--
Given an equation `f = g` between 2-morphisms `X ⟶ Y` in an arbitrary bicategory (possibly after a
`∀` binder), get the corresponding equation in the bicategory `Cat`. -/
def toCatExpr (e : Expr) : MetaM Expr := do

--   -- should return (something like) mkAppOptM' ... type e
--   -- can `observing?` be used to infer bicat instance
--   -- need to have modified the type for this?



  -- Get type of `η`, should be `f ⟶ g` --> get the type of `f`, should be `C ⟶ D`.
  -- Replace `D` with `Cat`.
  -- forallTelescope e fun xs eq => do
  --   logInfo m!"xs: {xs}"
  --   logInfo m!"eq: {eq}"

  --   let η := (Expr.getAppArgsN eq 2)[0]!
  --   logInfo m!"args': {η}"

  --   let f := (Expr.getAppArgsN (← inferType η) 2)[0]!
  --   logInfo m!"f: {f}"

  --   let b := (Expr.getAppArgsN (← inferType f) 2)[1]!
  --   logInfo m!"b: {b}"

  --   let B ← inferType b
  --   logInfo m!"B: {B}"

  --   let u ← Meta.mkFreshLevelMVar
  --   let v ← Meta.mkFreshLevelMVar
  --   --let B := B.abstract #[q(Cat.{v, u})]
  --   logInfo m!"B': {B.isFVar}"

  let (args, _, conclusion) ← forallMetaTelescope (← inferType e)
  logInfo m!"args at start: {args}"

  let η := (Expr.getAppArgsN conclusion 2)[0]!

  let f := (Expr.getAppArgsN (← inferType η) 2)[0]!

  let D := (Expr.getAppArgsN (← inferType f) 2)[1]!

  let B_pre ← inferType D

  let B ← Meta.getMVars B_pre

  let CAT := B[0]!
  logInfo m!"cat: {CAT}"
 -- logInfo m!"cat level: {← getLevel (Expr.mvar Cat)}"
  -- Don't make new levels here! infer from B what levels should be used
  let u ← Meta.mkFreshLevelMVar
  let v ← Meta.mkFreshLevelMVar
  --let u ← instantiateLevelMVars u
  --let v ← instantiateLevelMVars v

  CAT.assign q(Cat.{v, u})
  --let CAT_inst ← synthInstanceQ q(Bicategory.{max v u, max v u} Cat.{v, u})
  --let _ ← instantiateMVars B_pre

  let args2 ← args.mapM instantiateMVars
  logInfo m!"args2: {args2}"
  let i := args2.findIdx? fun x => !x.hasExprMVar
  let inst := (← Meta.getMVars (args2.get! (i.get! + 1)))[0]!
  inst.assign (← synthInstanceQ q(Bicategory.{max v u, max v u} Cat.{v, u}))
  logInfo m!"mvars: {← Meta.getMVars (args2.get! (i.get! + 1))}"
  logInfo m!"inst: {inst}"
  let args2 := ← args.mapM instantiateMVars
  --let args2 := args2.set! (i.get! + 1) (← synthInstance (← inferType (args2.get! (i.get! + 1))))
  -- need to assign instead??
  --let args2 := args2.set! (i.get! + 1) CAT_inst
  logInfo m!"args2_set: {args2}"
  --let args2 := ← args.mapM instantiateMVars
  --logInfo m!"args2: {args2}"
  --let args2.get! (i.get! + 1) ← synthInstance
  --if i.isSome then args2[i.get]

  --let args4 := (args2.map fun i ↦ if i.hasExprMVar then none else some i)
  --logInfo m!"args4: {args4}"
  let e ← instantiateMVars e


  -- TODO: need to figure out how to specialize here!!
  let applied := (mkAppN e args2) --.abstractM args2
  let applied2 ← mkLambdaFVars ((← Meta.getMVars applied).map (Expr.mvar)) applied
  logInfo m!"e:{e}"
  logInfo m!"APP: {applied2}"

  -- FINAL STEP: try to synthesize instance!

  -- Get corresponding metavariable to D?
  -- replace it with Cat
  -- Done!

  return ← instantiateMVars applied2
  --mkForallFVars args3 conclusion
  -- Step 1: get the type of `η`


  -- Step 2: get the type of `f`

  -- Step 3: replace `D` with `Cat` in the type of `f`

  --sorry

-- variable (B C : Cat) (f g : B ⟶ C) (h : ∀ (η θ : f ⟶ g), η = θ)


  --let TEST := toCat q(∀ (B C : Cat), B = C)

-- example (B C : Cat) (f g : B ⟶ C) (h : ∀ (η θ : f ⟶ g), η = θ) : True := by
--   toCat

-- ∀ ..., η = θ
/--
Given morphisms `f g : C ⟶ D` in the bicategory `Cat`, and an equation `η = θ` between 2-morphisms
(possibly after a `∀` binder), produce the equation `∀ (X : C), f.app X = g.app X`, and simplify
it using basic lemmas in `Cat`. -/
def toAppExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do
    logInfo m!"e: {e}"
    -- NOW IM HAVING A UNIVERSE ISSUE!!!
    simpType catAppSimp (← mkAppM ``eq_app' #[e])) e

-- #eval show Lean.Elab.Term.TermElabM _ from do



--   let stx : Syntax ← `(∀ (B : Type*) [Bicategory B] {a b : B} (f g : a ⟶ b)
--     (η θ : f ⟶ g), η = θ)
--   let expr ← Elab.Term.elabTermAndSynthesize stx none
--   --let asdf ← toAppExpr (← mkExpectedTypeHint expr (← inferType expr))
--   let expr' ← toCatExpr expr
--   let (xs, _, e) ← forallMetaTelescope expr'
--   let expr₂ ← toAppExpr e
--   --let expr₂ ← toAppExpr (← mkExpectedTypeHint expr' (← inferType expr'))
--   --let expr₂ ← toAppExpr expr'
--   --logInfo m!"expr: {expr₂}"

/--
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`, where `f g : X ⟶ Y` are
morphisms in some category, will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).
So, for example, if the conclusion of `F` is `a ≫ b = g` then
the conclusion of `F_assoc` will be `a ≫ (b ≫ h) = g ≫ h` (note that `≫` reassociates
to the right so the brackets will not appear in the statement).

This attribute is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

Note that if you want both the lemma and the reassociated lemma to be
`simp` lemmas, you should tag the lemma `@[reassoc (attr := simp)]`.
The variant `@[simp, reassoc]` on a lemma `F` will tag `F` with `@[simp]`,
but not `F_apply` (this is sometimes useful).
-/
syntax (name := to_app) "to_app" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

-- TODO HERE: need to figure out how to replace second bicategory with Cat..?
initialize registerBuiltinAttribute {
  name := `to_app
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_app $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_app` can only be used as a global attribute"
    addRelatedDecl src "_app" ref stx? fun type value levels => do
      -- NOTE: value: fun {B} [Bicategory B] ... => mapComp ...
      -- NOTE: type: ∀ {B} [Bicategory B] ... => mapComp ...
      logInfo m!"TYPE: {← mkExpectedTypeHint value type}"
      pure (← toAppExpr (← toCatExpr (← mkExpectedTypeHint value type)), levels)
  | _ => throwUnsupportedSyntax }

open Term in
/--
`reassoc_of% t`, where `t` is
an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
elab "to_app_of% " t:term : term => do
  logInfo m!"CAT: {(← elabTerm t none)}"
  logInfo m!"eq_app : {(← mkAppM ``eq_app' #[(← elabTerm t none)])}"

  -- this might be hackier than I want later? (requires providing args explicitly..)
  toCatExpr (← elabTerm t none)




variable {B : Type*} [Bicategory B] {C : Type*} [Bicategory C]

example {a b c d : B} (F : OplaxFunctor B Cat) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : True := by
  --haveI : Bicategory Cat := inferInstance
  have := OplaxFunctor.mapComp_assoc_right F f g h
  --have := to_app_of% OplaxFunctor.mapComp_assoc_right F f g h





  trivial




end CategoryTheory
