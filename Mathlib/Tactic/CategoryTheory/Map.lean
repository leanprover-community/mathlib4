/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Lean.Meta.Simp
public import Mathlib.Util.AddRelatedDecl

/-!
# The `map` attribute

Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_map` of the form
`∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and then applies
`simp only [Functor.map_comp, Functor.map_id]`.

Declarations tagged with `@[map_functor]` register concrete functors. For each registered functor
compatible with the source category of `H`, `@[map]` also generates a specialized lemma
`H_map_<functorDeclName>` by specializing `F` to that functor and simplifying the result with
`dsimp`.

There is also a term elaborator `map_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Map

initialize mapFunctorExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (init := #[]) (· ++ ·)
  }

/-- Flatten a declaration name into an underscore-separated suffix. -/
private def flattenName : Name → String
  | .anonymous => ""
  | .str .anonymous s => s
  | .num .anonymous n => toString n
  | .str p s => s!"{flattenName p}_{s}"
  | .num p n => s!"{flattenName p}_{n}"

/-- The target name for the `@[map]` specialization at a registered functor. -/
private def specializedMapName (src functorName : Name) : Name :=
  src.appendAfter s!"_map_{flattenName (privateToUserName functorName)}"

/-- Read the registered `@[map_functor]` functors. -/
private def getMapFunctors : CoreM (Array Name) :=
  return mapFunctorExt.getState (← getEnv)

/-- Extract the source and target categories from a functor type. -/
private def extractFunctorType? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnf (← instantiateMVars ty)
  let (``CategoryTheory.Functor, args) := ty.getAppFnArgs | return none
  if args.size == 4 then
    return some (args[0]!, args[2]!)
  else
    return none

/-- Validate that a declaration tagged with `@[map_functor]` is a concrete functor constant. -/
private def validateMapFunctorDecl (declName : Name) : MetaM Unit := do
  let F ← mkConstWithFreshMVarLevels declName
  let Fty := (← inferType F).cleanupAnnotations
  if Fty.isForall then
    throwError "`map_functor` expects a declaration whose type is directly a functor, not a family"
  unless (← extractFunctorType? Fty).isSome do
    throwError "`map_functor` expects a declaration whose type reduces to `C ⥤ D`"

/-- `simp only` with `Functor.map_comp` and `Functor.map_id` on a single expression
(used on each side via `simpEq`). -/
def mapCompSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Functor.map_comp, ``Functor.map_id] e (config := { decide := false })

/-- Apply `dsimp` to an expression. -/
def dsimpExpr (e : Expr) : MetaM Expr := do
  let ctx ← Simp.Context.mkDefault
  return (← Meta.dsimp (← instantiateMVars e) ctx #[]).1

private def extractCatInstanceFromEq (eqTy : Expr) : MetaM (Expr × Expr) := do
  let some (α, _, _) := eqTy.cleanupAnnotations.eq? | throwError "`@[map]` expects an equality"
  let (``Quiver.Hom, #[_, instQuiv, _, _]) := α.getAppFnArgs |
    throwError "`@[map]` expects an equality of morphisms"
  let (``CategoryTheory.CategoryStruct.toQuiver, #[_, instCS]) := instQuiv.getAppFnArgs |
    throwError "`@[map]` expects an equality of morphisms"
  let (``CategoryTheory.Category.toCategoryStruct, #[C, instC]) := instCS.getAppFnArgs |
    throwError "`@[map]` expects an equality of morphisms"
  return (C, instC)

/-- Build the functor `map` lemma for `e : f = g` with target category levels `uLev`, `vLev`. -/
def mapExprHomAux (e : Expr) (uLev vLev : Level) : MetaM Expr := do
  let eqTy := (← inferType e).cleanupAnnotations
  let (C, instC) ← extractCatInstanceFromEq eqTy
  let Dsort := mkSort (Level.succ uLev)
  withLocalDecl `D .implicit Dsort fun dFVar => do
    let catD := mkApp (.const ``CategoryTheory.Category [vLev, uLev]) dFVar
    withLocalDecl `instD .instImplicit catD fun instDFVar => do
      let Fty ← mkAppOptM ``CategoryTheory.Functor #[C, instC, dFVar, instDFVar]
      withLocalDecl `F .default Fty fun fFVar => do
        let pf₀ ← mkAppM ``CategoryTheory.Functor.congr_map #[fFVar, e]
        let ty ← instantiateMVars (← inferType pf₀)
        let (_, pf') ← simpEq (fun e' => mapCompSimp e') ty pf₀
        mkLambdaFVars #[dFVar, instDFVar, fFVar] pf'

/--
For `e : f = g`, build `∀ ⦃D⦄ [Category D] (F : C ⥤ D), …` with
`simp only [Functor.map_comp, Functor.map_id]` on each side of `F.map f = F.map g`, using fresh
level names `uD` (objects) and `vD` (morphisms) for the target category (for `@[map]` declarations).
-/
def mapExprHom (e : Expr) (uD vD : Name) : MetaM Expr :=
  mapExprHomAux e (Level.param uD) (Level.param vD)

/--
Given a proof `pf` of `∀ .., f = g` with `f g` morphisms in a category, produce a proof of the
`map` lemma, quantifying over every target category `D` and every functor `F : C ⥤ D` (using two
fresh level parameters per generated lemma).

Returns the target category's level names for `levelParams`, after `levelMVarToParam` on the rest.
-/
def mapExpr (pf : Expr) : MetaM (Expr × Array Name) := do
  let uD ← mkFreshUserName `u
  let vD ← mkFreshUserName `v
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let inner ← mapExprHom pfApp uD vD
    let full ← mkLambdaFVars xs inner
    return (full, #[uD, vD])

/-- Version of `mapExpr` for `TermElabM`. -/
def mapExpr' (pf : Expr) : TermElabM (Expr × Array Name) := do
  mapExpr pf

/--
Like `mapExpr`, but uses fresh level metavariables for the target category so that `map_of% t` can
specialize to any `D` and `F` in context (see `addRelatedDecl` path for rigid universe parameters).
-/
def mapExprMVars (pf : Expr) : MetaM Expr := do
  let uLev ← mkFreshLevelMVar
  let vLev ← mkFreshLevelMVar
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let inner ← mapExprHomAux pfApp uLev vLev
    mkLambdaFVars xs inner

/-- `mapExprMVars` lifted to `TermElabM`. -/
def mapExprElab (pf : Expr) : TermElabM Expr :=
  liftMetaM <| mapExprMVars pf

/--
Produce the `@[map]`-specialized proof obtained by fixing `F` to a registered concrete functor and
then simplifying with `dsimp`. Returns `none` when the functor has an incompatible source category.
-/
def mapSpecializedExpr (pf F : Expr) : MetaM (Option Expr) := do
  let Fty := (← inferType F).cleanupAnnotations
  let some (CF, _) ← extractFunctorType? Fty
    | throwError "`@[map]` internal error: registered declaration is not a functor"
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let eqTy := (← inferType pfApp).cleanupAnnotations
    let (C, _) ← extractCatInstanceFromEq eqTy
    unless ← isDefEq C CF do
      return none
    let pf₀ ← mkAppM ``CategoryTheory.Functor.congr_map #[F, pfApp]
    let ty ← instantiateMVars (← inferType pf₀)
    let (ty', pf') ← simpEq (fun e => mapCompSimp e) ty pf₀
    let ty'' ← dsimpExpr ty'
    let pf'' ← mkExpectedTypeHint pf' ty''
    return some (← mkLambdaFVars xs pf'')

/--
Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_map` of the form
`∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and then applies
`simp only [Functor.map_comp, Functor.map_id]`. For each compatible registered `@[map_functor]`
declaration `G`, it also creates `H_map_<G>` by specializing `F := G` and applying `dsimp`.

Use `@[map (attr := simp)]` to mark both the original lemma and `H_map` as `simp` lemmas, and
`@[reassoc (attr := map)]` to generate `_map` versions of both the original lemma the reassociated
version.
-/
syntax (name := map) "map" optAttrArg : attr
syntax (name := map_functor) "map_functor" : attr

initialize registerBuiltinAttribute {
  name := `map_functor
  descr := "Register a concrete functor for specialized `@[map]` lemmas."
  applicationTime := .afterTypeChecking
  add := fun declName stx kind => match stx with
  | `(attr| map_functor) => do
    if kind != AttributeKind.global then
      throwError "`map_functor` can only be used as a global attribute"
    MetaM.run' do validateMapFunctorDecl declName
    modifyEnv (mapFunctorExt.addEntry · declName)
  | _ => throwUnsupportedSyntax }

initialize registerBuiltinAttribute {
  name := `map
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| map $optAttr) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`map` can only be used as a global attribute"
    let tgt := src.appendAfter "_map"
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let (pf, tgtLevelNames) ← mapExpr' value
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        let outLevels := tgtLevelNames.toList ++ r.newParamNames.toList
        pure (r.expr, outLevels)
    for functorName in ← getMapFunctors do
      let info ← withoutExporting <| getConstInfo src
      let levelMVars ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      let value := (Expr.const src (info.levelParams.map mkLevelParam)).instantiateLevelParams
        info.levelParams levelMVars
      let F ← mkConstWithFreshMVarLevels functorName
      if (← mapSpecializedExpr value F).isSome then
        addRelatedDecl src (specializedMapName src functorName) ref optAttr fun value levels => do
          Term.TermElabM.run' <| Term.withSynthesize do
            let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
            let value := value.instantiateLevelParams levels levelMVars
            let F ← mkConstWithFreshMVarLevels functorName
            let some pf ← mapSpecializedExpr value F
              | throwError "`@[map]` internal error: specialization disappeared unexpectedly"
            let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
            pure (r.expr, r.newParamNames.toList)
  | _ => throwUnsupportedSyntax }

/--
`map_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with a functor applied and
`simp only [Functor.map_comp, Functor.map_id]` on each side.
-/
elab "map_of% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  mapExprElab e

end Mathlib.Tactic.CategoryTheory.Map
