/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Tactic.CategoryTheory.Map

/-!
# The `specialize_map` attribute

Adding `@[specialize_map F]` to a lemma of shape `∀ .., f = g`, where `f` and `g` are morphisms
in a category, creates a new lemma by applying `@[map]` and then specializing the functor variable
with the expression `F`, which should have type `∀ .., C ⥤ D` for some categories `C`, `D`.
The binders of `F` are unified with the binders of the tagged lemma, and any remaining binders are
abstracted over in the generated declaration, preserving their explicitness and instance status.
Parameters retain their order except when specialization introduces new dependencies. Universe
parameters are ordered by their roles as in `@[map]`. Finally, `dsimp` unfolds `F` and the
definitions used in its body in the result.
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

/-- `dsimp` on a single expression, packaged for use with `simpType`. -/
def dsimpSimp (unfold : List Name) (e : Expr) : MetaM Simp.Result := do
  let ctx ← mkDSimpContext unfold
  let (e', _) ← Meta.dsimp e ctx
  return { expr := e' }

/-- Specializing the source category can introduce dependencies on the template's parameters.
Move those parameters before the binders that need them, preserving the order otherwise. -/
private partial def orderBinders (vars : Array Expr) : MetaM (Array Expr) := do
  if vars.isEmpty then
    return #[]
  let some x ← vars.findM? (fun x => do
    let type ← instantiateMVars (← inferType x)
    return !(← vars.anyM fun y => exprDependsOn' type y)) |
    throwError "cyclic dependencies in specialized map parameters"
  return #[x] ++ (← orderBinders (vars.erase x))

/--
Instantiate the theorem and functor template with metavariables, specialize the proof produced by
`mapExpr`, and abstract over the remaining parameters with their original binder information.
-/
def specializeMapExpr (pf functorExpr : Expr) : TermElabM Expr := do
  let (ys, yInfos, functorType) ← forallMetaTelescopeReducing (← inferType functorExpr)
  unless (← whnf functorType).isAppOf ``CategoryTheory.Functor do
    throwError "`@[specialize_map]` expects a declaration whose type reduces to `∀ .., C ⥤ D`"
  let F := mkAppN functorExpr ys
  let mapped ← mapExpr pf `specialize_map
  let (args, infos, _) ← forallMetaTelescopeReducing (← inferType mapped)
  -- `mapExpr` appends the target category, its instance, and the functor after the source binders.
  let functor := args.back!
  let xs := args.extract 0 (args.size - 3)
  let xInfos := infos.extract 0 (infos.size - 3)
  unless ← isDefEq (← inferType functor) functorType do
    throwError
      "`@[specialize_map]` could not unify the source of the functor with the source \
       category of the lemma"
  functor.mvarId!.assign F
  -- Unification may identify parameters; retain the source binder information in that case.
  let mut binders := #[]
  for (x, info) in (xs ++ ys).zip (xInfos ++ yInfos) do
    let x' ← instantiateMVars x
    if x'.isMVar && !binders.any (·.1 == x') then
      x'.mvarId!.setUserName (← x.mvarId!.getDecl).userName
      binders := binders.push (x', info)
  let vars ← orderBinders (binders.map (·.1))
  let pf ← instantiateMVars (mkAppN mapped args)
  let pf ← elimMVarDeps vars pf
  let pf ← vars.foldrM (init := pf) fun x pf => do
    let some (_, info) := binders.find? (·.1 == x) | unreachable!
    mkLambdaFVars #[x] pf (binderInfoForMVars := info)
  let mut unfold := functorExpr.getAppFn.constName?.toList
  for name in unfold do
    if let some value := (← getConstInfo name).value? then
      for name in value.getUsedConstants do
        if (← getConstInfo name).value?.isSome then
          unfold := unfold.insert name
  simpType (dsimpSimp unfold) pf

/-- Optional `suffix := "..."` argument for `@[specialize_map ...]`. -/
syntax specializeMapSuffix := atomic(" (" &"suffix" " := " str ")")

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
  descr := "specialize a map lemma to a functor template"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| specialize_map $F:ident $[(suffix := $suffix:str)]? $optAttr) => MetaM.run' do
    if kind != AttributeKind.global then
      throwError "`specialize_map` can only be used as a global attribute"
    let suffix := suffix.map (·.getString) |>.getD "_specializeMap"
    let tgt := src.appendAfter suffix
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| withSynthesize do
        -- The source universes may specialize to composite levels, e.g. for functor categories.
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let Fexpr ← mkConstWithFreshMVarLevels (← resolveGlobalConstNoOverload F)
        let pf ← specializeMapExpr value Fexpr
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        setMCtx r.mctx
        let ordered ← orderMapUniverses (← inferType r.expr) [] r.newParamNames.toList
        pure (r.expr, ordered)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic.CategoryTheory.SpecializeMap
