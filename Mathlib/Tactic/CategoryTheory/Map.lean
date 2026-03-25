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

Adding `@[map]` to a lemma named `F` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category, creates a new lemma named `F_map` that universally quantifies over every target
category `D` and every functor `F : C ⥤ D`, states the corresponding `F.map` equality, then applies
`simp only [Functor.map_comp]` independently to the left- and right-hand sides of that equality.

There is also a term elaborator `map_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Map

/-- `simp only` with `Functor.map_comp` and other standard `CategoryTheory`
lemmas on a single expression (used on each side via `simpEq`). -/
def mapCompSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Functor.map_comp, ``Functor.map_id, ``Category.id_comp, ``Category.comp_id,
    ``Category.assoc] e (config := { decide := false })

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
`simp only [Functor.map_comp]` on each side of `F.map f = F.map g`, using fresh level names `uD`
(objects) and `vD` (morphisms) for the target category (for `@[map]` declarations).
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
Adding `@[map]` to a lemma named `F` of shape `∀ .., f = g`, where `f` and `g` are morphisms in a
category, generates `F_map`, quantifying over every target category `D` (fresh universes) and every
functor `F : C ⥤ D`, then `simp only [Functor.map_comp]` on each side of the `F.map` equation.

Use `@[map (attr := simp)]` to mark both the original lemma and `F_map` as `simp` lemmas (see
`@[reassoc (attr := simp)]`).

If the original declaration is tagged with `to_dual`, then `F_map` gets `@[to_dual none]`. In the
rare case that only `F_map` should be tagged with `to_dual`, use `@[map +to_dual]`.
-/
syntax toDualOpt := " +" &"to_dual"

syntax (name := map) "map" (toDualOpt)? optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `map
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| map $[$toDual:toDualOpt]? $optAttr) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`map` can only be used as a global attribute"
    let toDual := toDual.isSome || (Translate.findTranslation? (← getEnv) ToDual.data src).isSome
    let tgt := src.appendAfter "_map"
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let (pf, tgtLevelNames) ← mapExpr' value
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        let outLevels := tgtLevelNames.toList ++ r.newParamNames.toList
        pure (r.expr, outLevels)
    if toDual then
      liftCommandElabM <| Command.elabCommand <| ←
        `(command| attribute [to_dual none] $(mkIdent tgt))
  | _ => throwUnsupportedSyntax }

/--
`map_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with a functor applied and `simp only [Functor.map_comp]` on
each side.
-/
elab "map_of% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  mapExprElab e

end Mathlib.Tactic.CategoryTheory.Map
