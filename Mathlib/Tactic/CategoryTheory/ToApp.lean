/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Util.AddRelatedDecl
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The `to_app` attribute

Adding `@[to_app]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ⟶ Y` in some category
will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for automatically generating lemmas which the simplifier can use even on expressions
.......

There is also a term elaborator `to_app_of% t` for use within proofs.
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

/--
Given an equation `f = g` between 2-morphisms `X ⟶ Y` in an arbitrary bicategory (possibly after a
`∀` binder), get the corresponding equation in the bicategory `Cat`. -/

-- Maybe let this take a list of levels?
def to_appExpr (e : Expr) (levelMVars : List Level) : MetaM Expr := do
  let (args, _, conclusion) ← forallMetaTelescope (← inferType e)

  -- Find bicategory metavariable
  let η := (Expr.getAppArgsN conclusion 2)[0]!
  let f := (Expr.getAppArgsN (← inferType η) 2)[0]!
  let D := (Expr.getAppArgsN (← inferType f) 2)[1]!
  let B_pre ← inferType D
  let B ← getMVars B_pre
  -- assign bicategory metavariable
  let CAT := B[0]!
  let some CATIdx := args.findIdx? (· == .mvar CAT)
    | throwError "TODO"

  -- TODO: problem here?
  let u ← mkFreshLevelMVar
  --Meta.getDecLevel B_pre
  let v ← mkFreshLevelMVar
  -- Assign level for the bicategory
  let _ ← isLevelDefEq (← Meta.getDecLevel B_pre) (Level.max (Level.max (u.succ) u) (v.succ))

  CAT.assign (.const ``Cat [u, v])
  let some inst := args[CATIdx + 1]?
    | throwError "TODO"

  -- Assign levels for the bicategory instance
  let instlvl ← Meta.getLevel (← inferType inst)
  let instlvlMVars := levelMVars.filter fun l => l.occurs instlvl && l != u
  forM instlvlMVars fun l => do
    let _ ← isLevelDefEq l (Level.max u v)

  inst.mvarId!.assign (← synthInstanceQ q(Bicategory.{max u v, max u v} Cat.{u, v}))

  let applied ← mkAppOptM' e (args.map some)
  -- let applied := mkAppN e args
  let applied ← mkLambdaFVars ((← getMVars applied).map (Expr.mvar)) applied
  return applied

/--
Given morphisms `f g : C ⟶ D` in the bicategory `Cat`, and an equation `η = θ` between 2-morphisms
(possibly after a `∀` binder), produce the equation `∀ (X : C), f.app X = g.app X`, and simplify
it using basic lemmas in `Cat`. -/
def toAppExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do
    logInfo m!"e: {e}"
    logInfo m!"e type: {← inferType e}"
    simpType catAppSimp (← mkAppM ``eq_app' #[e])) e

def addRelatedDecl2 (src : Name) (suffix : String) (ref : Syntax)
    (attrs? : Option (Syntax.TSepArray `Lean.Parser.Term.attrInstance ","))
    (construct : Expr → Expr → List Name → MetaM (Expr × List Name)) :
    MetaM Unit := do
  let tgt := match src with
    | Name.str n s => Name.mkStr n <| s ++ suffix
    | x => x
  addDeclarationRanges tgt {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange ref }
  let info ← getConstInfo src
  let (newValue, newLevels) ← construct info.type info.value! info.levelParams
  let newValue ← instantiateMVars newValue
  let newType ← instantiateMVars (← inferType newValue)
  match info with
  | ConstantInfo.thmInfo info =>
    addAndCompile <| .thmDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
  | ConstantInfo.defnInfo info =>
    -- Structure fields are created using `def`, even when they are propositional,
    -- so we don't rely on this to decided whether we should be constructing a `theorem` or a `def`.
    addAndCompile <| if ← isProp newType then .thmDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
      else .defnDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
  | _ => throwError "Constant {src} is not a theorem or definition."
  if isProtected (← getEnv) src then
    setEnv <| addProtected (← getEnv) tgt
  let attrs := match attrs? with | some attrs => attrs | none => #[]
  _ ← Term.TermElabM.run' <| do
    let attrs ← elabAttrs attrs
    Term.applyAttributes src attrs
    Term.applyAttributes tgt attrs


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

initialize registerBuiltinAttribute {
  name := `to_app
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_app $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_app` can only be used as a global attribute"
    addRelatedDecl2 src "_app" ref stx? fun type value levels => do
      logInfo m!"tp: {type}"
      logInfo m!"val: {value}"
      logInfo m!"valtp: {← inferType value}"
      let levelMVars ← levels.mapM λ _ => mkFreshLevelMVar
      let value := value.instantiateLevelParams levels levelMVars
      let newValue ← to_appExpr value levelMVars
      logInfo m!"val: {newValue}"
      logInfo m!"valtp: {← inferType newValue}"
      let r := (← getMCtx).levelMVarToParam (λ _ => false) (λ _ => false) newValue
      let newExpr ← toAppExpr (← mkExpectedTypeHint r.expr (← inferType r.expr))
      let output := (newExpr, r.newParamNames.toList)
      logInfo m!"hello {output}"
      pure output
  | _ => throwUnsupportedSyntax }

open Term in
/--
`to_app_of% t`, where `t` is
an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
elab "to_app_of% " t:term : term => do
  logInfo m!"CAT: {(← elabTerm t none)}"
  logInfo m!"eq_app : {(← mkAppM ``eq_app' #[(← elabTerm t none)])}"
  -- this might be hackier than I want later? (requires providing args explicitly..)
  to_appExpr (← elabTerm t none) sorry


end CategoryTheory
