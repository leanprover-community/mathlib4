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

There is also a term elaborator `map_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Map

/-- `simp only` with `Functor.map_comp` and `Functor.map_id` on a single expression
(used on each side via `simpEq`). -/
def mapCompSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Functor.map_comp, ``Functor.map_id] e (config := { decide := false })

/--
Given the type of an equality between morphisms, extract the source category `C` together with a
synthesized `Category C` instance.

Throws an error if the input is not an equality or not an equality in a hom type.
-/
def extractCatInstanceFromEq (eqTy : Expr) : MetaM (Expr × Expr) := do
  let some (α, _, _) := eqTy.cleanupAnnotations.eq? | throwError "`@[map]` expects an equality"
  let (``Quiver.Hom, #[C, _, _, _]) := α.getAppFnArgs |
    throwError "`@[map]` expects an equality of morphisms"
  let uObj ← mkFreshLevelMVar
  let vHom ← mkFreshLevelMVar
  let catTy := .app (.const ``CategoryTheory.Category [vHom, uObj]) C
  let instC ← synthInstance catTy
  return (C, instC)

/-- Build the mapped equality for `e : f = g` under a specific functor `F`, simplifying with
`simp only [Functor.map_comp, Functor.map_id]`. -/
def mapExprWithFunctor (e : Expr) (F : Expr) : MetaM Expr := do
  let lem₀ ← mkConstWithFreshMVarLevels ``CategoryTheory.Functor.congr_map
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 10
  let instC := args[1]!
  let instD := args[3]!
  args[4]!.mvarId!.assignIfDefEq F
  args[9]!.mvarId!.assignIfDefEq e
  if instC.isMVar then
    let t ← instantiateMVars (← inferType instC)
    try instC.mvarId!.assign (← synthInstance t) catch _ => pure ()
  if instD.isMVar then
    let t ← instantiateMVars (← inferType instD)
    try instD.mvarId!.assign (← synthInstance t) catch _ => pure ()
  let pf₀ := mkAppN lem₀ args
  let ty ← instantiateMVars (← inferType pf₀)
  let (_, pf') ← simpEq (fun e' => mapCompSimp e') ty pf₀
  pure pf'

/-- Build the functor `map` lemma for `e : f = g` with target category levels `uLev`, `vLev`. -/
def mapExprHom (e : Expr) (uLev vLev : Level) : MetaM Expr := do
  let eqTy := (← inferType e).cleanupAnnotations
  let (C, instC) ← extractCatInstanceFromEq eqTy
  let Dsort := .sort (Level.succ uLev)
  withLocalDecl `D .implicit Dsort fun dFVar => do
    let catD := .app (.const ``CategoryTheory.Category [vLev, uLev]) dFVar
    withLocalDecl `instD .instImplicit catD fun instDFVar => do
      let Fty ← mkAppOptM ``CategoryTheory.Functor #[C, instC, dFVar, instDFVar]
      withLocalDecl `F .default Fty fun fFVar => do
        let pf' ← mapExprWithFunctor e fFVar
        mkLambdaFVars #[dFVar, instDFVar, fFVar] pf'

/--
Given a proof `pf` of `∀ .., f = g` with `f g` morphisms in a category, produce a proof of the
`map` lemma, quantifying over every target category `D` and every functor `F : C ⥤ D` (using two
fresh level parameters per generated lemma).

Returns the target category's object-level and morphism-level names (`uD`, then `vD`) so the caller
can place them in the generated declaration's `levelParams` in its preferred order.
-/
def mapExpr (pf : Expr) : MetaM (Expr × Array Name) := do
  let uD ← mkFreshUserName `u
  let vD ← mkFreshUserName `v
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let inner ← mapExprHom pfApp (.param uD) (.param vD)
    let full ← mkLambdaFVars xs inner
    return (full, #[uD, vD])

/--
Like `mapExpr`, but uses fresh level metavariables for the target category so that `map_of% t` can
specialize to any `D` and `F` in context (see `addRelatedDecl` path for rigid universe parameters).
-/
def mapExprMVars (pf : Expr) : MetaM Expr := do
  let uLev ← mkFreshLevelMVar
  let vLev ← mkFreshLevelMVar
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let inner ← mapExprHom pfApp uLev vLev
    mkLambdaFVars xs inner

/--
Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_map` of the form
`∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and then applies
`simp only [Functor.map_comp, Functor.map_id]`.

Use `@[map (attr := simp)]` to mark both the original lemma and `H_map` as `simp` lemmas, and
`@[map (attr := reassoc)]` to generate reassociated versions of both the original lemma and the
`_map` lemma (`@[reassoc (attr := map)]` generates `_map` versions of both the original and the
reassociated lemma, but this is of course less general than `@[map (attr := reassoc)]`). All four
lemmas can be registered as `simp` lemmas with `@[map (attr := reassoc (attr := simp))]`.
-/
syntax (name := mapStx) "map" optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `mapStx
  descr := "Generate a companion `_map` lemma by applying a functor to an equality of morphisms."
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
        let (pf, tgtLevelNames) ← mapExpr value
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        let outLevels := match r.newParamNames.toList, tgtLevelNames.toList with
          | [srcObj, srcHom], [tgtObj, tgtHom] => [srcHom, tgtHom, srcObj, tgtObj]
          | _, _ => tgtLevelNames.toList ++ r.newParamNames.toList
        pure (r.expr, outLevels)
  | _ => throwUnsupportedSyntax }

/--
Auxiliary definition for `map_of%`
-/
private partial def elabMapOfTerm (t : Syntax) : Term.TermElabM Expr := do
  match t with
  | `(term| ($t)) => elabMapOfTerm t
  | `(term| @$id:ident) | `(term| $id:ident) =>
    if (← withRef id <| Term.isLocalIdent? id).isNone then
      try mkConstWithFreshMVarLevels (← resolveGlobalConstNoOverload id)
      catch _ => Term.elabTerm t none
    else
      Term.elabTerm t none
  | _ => Term.elabTerm t none

/--
`map_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with a functor applied and
`simp only [Functor.map_comp, Functor.map_id]` on each side.
-/
elab "map_of% " t:term : term => do
  let e ← Term.withSynthesizeLight <| elabMapOfTerm t
  mapExprMVars e

end Mathlib.Tactic.CategoryTheory.Map
