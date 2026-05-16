/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.Util.AddRelatedDecl

/-!
# The `specialize_map` attribute

Adding `@[specialize_map F]` to a lemma of shape `∀ .., f = g`, where `f` and `g` are morphisms
in a category, creates a new lemma by applying `@[map]` and then specializing the functor variable
with the expression `F`, which should have type `∀ .., C ⥤ D` for some categories `C`, `D`.
The binders of `F` are unified with the binders of the tagged lemma, and any remaining binders are
abstracted over in the generated declaration. Finally, `dsimp` is run on the result.
-/

public meta section

open Lean Meta Elab Tactic Term
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.SpecializeMap

open Mathlib.Tactic.CategoryTheory.Map

/-- Build a `dsimp` context unfolding exactly the listed declarations. -/
def mkDSimpContext (unfold : List Name) : MetaM Simp.Context := do
  let simpTheorems ← unfold.foldlM (init := ({} : SimpTheorems)) fun s n =>
    s.addDeclToUnfold n
  Simp.mkContext {} (simpTheorems := #[simpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)

/-- `dsimp` on a single expression, packaged for use with `simpEq`. -/
def dsimpSimp (unfold : List Name) (e : Expr) : MetaM Simp.Result := do
  let ctx ← mkDSimpContext unfold
  let (e', _) ← Meta.dsimp e ctx
  return { expr := e' }

private def unfoldNamesInValue (n : Name) : MetaM (List Name) := do
  let env ← getEnv
  let some info := env.find? n | return []
  let some value := info.value? | return []
  pure <| value.getUsedConstants.toList.filter fun m =>
    match env.find? m with
    | some info => info.value?.isSome
    | none => false

private partial def collectDSimpUnfoldNames
    (depth : Nat) (seeds : List Name) : MetaM (List Name) := do
  let rec go (depth : Nat) (seen frontier : List Name) : MetaM (List Name) := do
    let frontier := frontier.filter fun n => !(seen.contains n)
    let seen := seen ++ frontier
    if frontier.isEmpty || depth == 0 then
      pure seen
    else
      let next ← frontier.foldlM (init := []) fun acc n => do
        return acc ++ (← unfoldNamesInValue n)
      go (depth - 1) seen next
  go depth [] seeds

private partial def openExprWithMVarsAux (f : Expr) (args : Array Expr)
    (type : Expr) : MetaM (Array Expr × Expr) := do
  match type with
  | .forallE n d b _ =>
      let d := d.instantiateRev args
      let mvar ← mkFreshExprMVar d MetavarKind.natural n
      openExprWithMVarsAux f (args.push mvar) b
  | _ => do
      let type ← whnfD (type.instantiateRev args)
      if type.isForall then
        openExprWithMVarsAux f args type
      else
        pure (args, mkAppN f args)

private def openExprWithMVars (f : Expr) : MetaM (Array Expr × Expr) := do
  openExprWithMVarsAux f #[] (← inferType f)

private def unassigned (xs : Array Expr) : MetaM (Array Expr) := do
  xs.filterM fun x =>
    if x.isMVar then
      return !(← x.mvarId!.isAssigned)
    else
      return true

private def binderDependsOn (x y : Expr) : MetaM Bool := do
  if x == y then
    return false
  if x.isFVar then
    localDeclDependsOn' (← x.fvarId!.getDecl) y
  else
    exprDependsOn' (← instantiateMVars (← inferType x)) y

private partial def orderBinders (vars : Array Expr) : MetaM (Array Expr) := do
  let rec go (pending acc : Array Expr) : MetaM (Array Expr) := do
    if pending.isEmpty then
      return acc
    let mut progress := false
    let mut rest := #[]
    let mut acc := acc
    for x in pending do
      let dependsOnPending ← pending.anyM fun y => binderDependsOn x y
      if dependsOnPending then
        rest := rest.push x
      else
        progress := true
        acc := acc.push x
    if progress then
      go rest acc
    else
      pure (acc ++ pending)
  go vars #[]

private def extractSourceCatFromEq (eqTy : Expr) : MetaM Expr := do
  let some (α, _, _) := eqTy.cleanupAnnotations.eq? |
    throwError "`@[specialize_map]` expects an equality"
  let (``Quiver.Hom, #[C, _, _, _]) := α.getAppFnArgs |
    throwError "`@[specialize_map]` expects an equality of morphisms"
  pure C

private def extractFunctorSource (F : Expr) : MetaM Expr := do
  let Fty ← instantiateMVars (← inferType F)
  let (``CategoryTheory.Functor, #[src, _, _, _]) := Fty.getAppFnArgs |
    throwError "`@[specialize_map]` expects a term whose type reduces to `∀ .., C ⥤ D`"
  pure src

/--
Generic engine for `specialize_map`: instantiate both the tagged theorem and the functor template
with metavariables, unify the functor source with the source category of the tagged lemma, apply the
same mapping construction as `@[map]`, and abstract over all remaining unsolved variables.
-/
def specializeMapExpr (pf : Expr) (functorExpr : Expr) : TermElabM Expr := do
  let pf ← match pf.getAppFn.constName? with
    | some declName => mkConstWithFreshMVarLevels declName
    | none => pure pf
  let helperName? := functorExpr.getAppFn.constName?
  let unfold ← collectDSimpUnfoldNames 1 helperName?.toList
  let (xs, pfApp) ← openExprWithMVars pf
  let eqTy := (← inferType pfApp).cleanupAnnotations
  let sourceCat ← extractSourceCatFromEq eqTy

  let (ys, F) ← openExprWithMVars functorExpr
  let Fsrc ← extractFunctorSource F
  unless ← isDefEq Fsrc sourceCat do
    throwError
      "`@[specialize_map]` could not unify the source of the functor with the source \
       category of the lemma"

  let pf₁ ← mapExprWithFunctor pfApp F
  let ys ← unassigned ys
  let xs ← unassigned xs
  let vars ← orderBinders (xs ++ ys)
  let pf₂ ← instantiateMVars pf₁
  let pf₂ ← elimMVarDeps vars pf₂
  let pf₃ ← mkLambdaFVars vars pf₂
  let pf₄ ← instantiateMVars pf₃
  let (pf₄, _) ← Meta.dsimp pf₄ (← mkDSimpContext unfold)
  let pf₅ ← simpType (dsimpSimp unfold) pf₄
  let pf₅ ← instantiateMVars pf₅
  pure pf₅

private partial def elabSpecializeMapTerm (t : Syntax) : TermElabM Expr := do
  match t with
  | `(term| ($t)) => elabSpecializeMapTerm t
  | `(term| @$id:ident) | `(term| $id:ident) =>
    if (← withRef id <| isLocalIdent? id).isNone then
      try mkConstWithFreshMVarLevels (← resolveGlobalConstNoOverload id)
      catch _ => elabTerm t none
    else
      elabTerm t none
  | _ => elabTerm t none

/-- Optional `suffix := "..."` argument for `@[specialize_map ...]`. -/
syntax specializeMapSuffix := " (" &"suffix" " := " str ")"

/--
`@[specialize_map F]` generates a related declaration by specializing the generic map lemma with
`F`, which should be an identifier whose type reduces to `∀ .., C ⥤ D`.

Use `@[specialize_map F (suffix := "_foo")]` to override the generated declaration suffix, and
`@[specialize_map F (attr := reassoc)]` to apply further attributes to both the original and the
specialized declaration.
-/
syntax (name := specializeMapStx)
  "specialize_map " ident (specializeMapSuffix)? optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `specializeMapStx
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| specialize_map $F:ident $[(suffix := $suffix:str)]? $optAttr) => MetaM.run' do
    if kind != AttributeKind.global then
      throwError "`specialize_map` can only be used as a global attribute"
    let suffix := suffix.map (·.getString) |>.getD "_specializeMap"
    let tgt := src.appendAfter suffix
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| withSynthesize do
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let Fexpr ← withSynthesizeLight <| elabSpecializeMapTerm F
        let pf ← specializeMapExpr value Fexpr
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        pure (r.expr, r.newParamNames.toList)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic.CategoryTheory.SpecializeMap
