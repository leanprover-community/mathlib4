/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Tactic.CategoryTheory.MapOpposite
public import Mathlib.Lean.Meta.Simp
public import Mathlib.Util.AddRelatedDecl

/-!
# The `map` attribute

Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates new lemmas `H_op`, `H_map`, and `H_op_map`.

- `H_op` applies `Quiver.Hom.op` to both sides and simplifies with `simp only [op_comp, op_id]`.
- `H_map` has the form `∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and simplifies with
  `simp only [Functor.map_comp, Functor.map_id]`.
- `H_op_map` applies the same `map` procedure to `H_op`.

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

/-- Empty `(attr := ...)` syntax for `addRelatedDecl` without touching the source decl. -/
private def emptyOptAttrArg : TSyntax ``optAttrArg :=
  ⟨Syntax.node .none ``optAttrArg #[]⟩

/-- Apply an `(attr := ...)` bundle to a single declaration. -/
private def applyOptAttrsToDecl (decl : Name) (attrs : TSyntax ``optAttrArg) : MetaM Unit :=
  Term.TermElabM.run' do
    let attrs ← elabOptAttrArg attrs
    Term.applyAttributes decl attrs

/-- Apply just the named attributes from an `(attr := ...)` bundle to a declaration. -/
private def applySelectedOptAttrsToDecl (decl : Name) (attrs : TSyntax ``optAttrArg)
    (names : List Name) : MetaM Unit :=
  Term.TermElabM.run' do
    let attrs ← elabOptAttrArg attrs
    Term.applyAttributes decl <| attrs.filter (fun attr => attr.name ∈ names)

/-- Build `Category Cᵒᵖ` from `C` and `[Category C]` using matching universe levels. -/
private def mkOppositeCategoryInst (C instC : Expr) : MetaM Expr := do
  let instCty ← inferType instC
  let (.const ``CategoryTheory.Category [v, u]) := instCty.getAppFn |
    throwError "`@[map]` expects a category instance"
  return mkAppN (.const ``Mathlib.Tactic.CategoryTheory.Map.mapOppositeCategory [u, v]) #[C, instC]

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

/-- Simplify a single `Quiver.Hom.op` expression using `mapOp_comp` and `mapOp_id`. -/
def opHomSimp (e : Expr) : MetaM Simp.Result := do
  let e := (← instantiateMVars e).cleanupAnnotations
  match e.getAppFnArgs with
  | (``Quiver.Hom.op, opArgs) =>
    let some inner := opArgs.back? | return { expr := e }
    let inner := inner.cleanupAnnotations
    match inner.getAppFnArgs with
    | (``CategoryTheory.CategoryStruct.comp, compArgs) =>
      if h : 2 ≤ compArgs.size then
        let f := compArgs[compArgs.size - 2]
        let g := compArgs[compArgs.size - 1]
        let pf ← mkAppM ``Mathlib.Tactic.CategoryTheory.Map.mapOp_comp #[f, g]
        let some (_, _, rhs) := (← inferType pf).eq? | return { expr := e }
        return { expr := rhs, proof? := some pf }
      else
        return { expr := e }
    | (``CategoryTheory.CategoryStruct.id, idArgs) =>
      let some X := idArgs.back? | return { expr := e }
      let pf ← mkAppM ``Mathlib.Tactic.CategoryTheory.Map.mapOp_id #[X]
      let some (_, _, rhs) := (← inferType pf).eq? | return { expr := e }
      return { expr := rhs, proof? := some pf }
    | _ => return { expr := e }
  | _ => return { expr := e }

/-- Apply `dsimp` to an expression. -/
def dsimpExpr (e : Expr) : MetaM Expr := do
  let ctx ← Simp.Context.mkDefault
  return (← Meta.dsimp (← instantiateMVars e) ctx #[]).1

private def extractCatInstanceFromEq (eqTy : Expr) : MetaM (Expr × Expr) := do
  let some (α, _, _) := eqTy.cleanupAnnotations.eq? | throwError "`@[map]` expects an equality"
  let (``Quiver.Hom, #[C, instQuiv, _, _]) := α.getAppFnArgs |
    throwError "`@[map]` expects an equality of morphisms; got {α}"
  match instQuiv.getAppFnArgs with
  | (``CategoryTheory.CategoryStruct.toQuiver, #[_, instCS]) =>
    let (``CategoryTheory.Category.toCategoryStruct, #[_, instC]) := instCS.getAppFnArgs |
      throwError "`@[map]` expects an equality of morphisms; got category-struct {instCS}"
    return (C, instC)
  | (``Quiver.opposite, #[C₀, instQuiv₀]) =>
    let (``CategoryTheory.CategoryStruct.toQuiver, #[_, instCS₀]) := instQuiv₀.getAppFnArgs |
      throwError "`@[map]` expects an equality of morphisms"
    let (``CategoryTheory.Category.toCategoryStruct, #[_, instC₀]) := instCS₀.getAppFnArgs |
      throwError "`@[map]` expects an equality of morphisms"
    let instC ← mkOppositeCategoryInst C₀ instC₀
    return (C, instC)
  | _ => throwError "`@[map]` expects an equality of morphisms"

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
Apply `Quiver.Hom.op` to both sides of a morphism equality and simplify with
`op_comp`/`op_id`.
-/
def opExprCore (e : Expr) : MetaM Expr := do
  let eqTy := (← inferType e).cleanupAnnotations
  let some (α, _, _) := eqTy.eq? | throwError "`@[map]` expects an equality"
  let _ ← extractCatInstanceFromEq eqTy
  withLocalDecl `f .default α fun fVar => do
    let opFnBody ← mkAppM ``Quiver.Hom.op #[fVar]
    let opFn ← mkLambdaFVars #[fVar] opFnBody
    let pf₀ ← mkCongrArg opFn e
    let ty ← instantiateMVars (← inferType pf₀)
    let (_, pf') ← simpEq (fun e' => opHomSimp e') ty pf₀
    return pf'

/--
Given a proof `pf` of `∀ .., f = g` with `f g` morphisms in a category, produce a proof of the
corresponding `_op` lemma.
-/
def opExpr (pf : Expr) : MetaM Expr := do
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let inner ← opExprCore pfApp
    mkLambdaFVars xs inner

/-- Version of `opExpr` for `TermElabM`. -/
def opExpr' (pf : Expr) : TermElabM Expr :=
  liftMetaM <| opExpr pf

/--
Build the `_op_map` lemma for `e : f = g` by first applying `Quiver.Hom.op` and simplifying, then
mapping the resulting equality out of `Cᵒᵖ`.
-/
def opMapExprHomAux (e : Expr) (uLev vLev : Level) : MetaM Expr := do
  let eqTy := (← inferType e).cleanupAnnotations
  let (C, instC) ← extractCatInstanceFromEq eqTy
  let opPf ← opExprCore e
  let opEqTy := (← inferType opPf).cleanupAnnotations
  let some (α, lhs, rhs) := opEqTy.eq? | throwError "`@[map]` expects an equality"
  let (``Quiver.Hom, #[Copp, _, X, Y]) := α.getAppFnArgs |
    throwError "`@[map]` expects an equality of morphisms"
  let instOpp ← mkOppositeCategoryInst C instC
  let instOppTy ← inferType instOpp
  let (.const ``CategoryTheory.Category [vC, uC]) := instOppTy.getAppFn |
    throwError "`@[map]` expects a category instance"
  let Dsort := mkSort (Level.succ uLev)
  withLocalDecl `D .implicit Dsort fun dFVar => do
    let catD := mkApp (.const ``CategoryTheory.Category [vLev, uLev]) dFVar
    withLocalDecl `instD .instImplicit catD fun instDFVar => do
      let Fty := mkAppN (.const ``CategoryTheory.Functor [vC, vLev, uC, uLev])
        #[Copp, instOpp, dFVar, instDFVar]
      withLocalDecl `F .default Fty fun fFVar => do
        let pf₀ ← mkAppOptM ``CategoryTheory.Functor.congr_map
          #[Copp, instOpp, dFVar, instDFVar, fFVar, X, Y, lhs, rhs, opPf]
        let ty ← instantiateMVars (← inferType pf₀)
        let (_, pf') ← simpEq (fun e' => mapCompSimp e') ty pf₀
        mkLambdaFVars #[dFVar, instDFVar, fFVar] pf'

/-- Given `pf : ∀ .., f = g`, produce the corresponding `_op_map` proof. -/
def opMapExpr (pf : Expr) : MetaM (Expr × Array Name) := do
  let uD ← mkFreshUserName `u
  let vD ← mkFreshUserName `v
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pfApp := mkAppN pf xs
    let inner ← opMapExprHomAux pfApp (Level.param uD) (Level.param vD)
    let full ← mkLambdaFVars xs inner
    return (full, #[uD, vD])

/-- Version of `opMapExpr` for `TermElabM`. -/
def opMapExpr' (pf : Expr) : TermElabM (Expr × Array Name) := do
  opMapExpr pf

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
in some category `C`, creates `H_op`, `H_map`, and `H_op_map`.

- `H_op` applies `Quiver.Hom.op` to both sides and simplifies with `simp only [op_comp, op_id]`.
- `H_map` has the form `∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and simplifies with
  `simp only [Functor.map_comp, Functor.map_id]`.
- `H_op_map` applies the same `map` procedure to `H_op`.

For each compatible registered `@[map_functor]` declaration `G`, it also creates
`H_map_<G>` by specializing `F := G` and applying `dsimp`.

Use `@[map (attr := simp)]` to mark the original lemma and all generated `map` lemmas as
`simp` lemmas. Other copied attributes continue to apply to the original lemma, `H_map`, and the
specialized `H_map_<G>` lemmas.
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
    let noAttr := emptyOptAttrArg
    let opTgt := src.appendAfter "_op"
    let tgt := src.appendAfter "_map"
    let opMapTgt := src.appendAfter "_op_map"
    addRelatedDecl src opTgt ref noAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let pf ← opExpr' value
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        pure (r.expr, r.newParamNames.toList)
    addRelatedDecl src tgt ref noAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let (pf, tgtLevelNames) ← mapExpr' value
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        let outLevels := tgtLevelNames.toList ++ r.newParamNames.toList
        pure (r.expr, outLevels)
    addRelatedDecl src opMapTgt ref noAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
        let value := value.instantiateLevelParams levels levelMVars
        let (pf, tgtLevelNames) ← opMapExpr' value
        let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
        let outLevels := tgtLevelNames.toList ++ r.newParamNames.toList
        pure (r.expr, outLevels)
    let mut specializedTargets := #[]
    for functorName in ← getMapFunctors do
      let info ← withoutExporting <| getConstInfo src
      let levelMVars ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      let value := (Expr.const src (info.levelParams.map mkLevelParam)).instantiateLevelParams
        info.levelParams levelMVars
      let F ← mkConstWithFreshMVarLevels functorName
      if (← mapSpecializedExpr value F).isSome then
        let specializedTgt := specializedMapName src functorName
        addRelatedDecl src specializedTgt ref noAttr fun value levels => do
          Term.TermElabM.run' <| Term.withSynthesize do
            let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
            let value := value.instantiateLevelParams levels levelMVars
            let F ← mkConstWithFreshMVarLevels functorName
            let some pf ← mapSpecializedExpr value F
              | throwError "`@[map]` internal error: specialization disappeared unexpectedly"
            let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) pf
            pure (r.expr, r.newParamNames.toList)
        specializedTargets := specializedTargets.push specializedTgt
    applyOptAttrsToDecl src optAttr
    applyOptAttrsToDecl tgt optAttr
    applySelectedOptAttrsToDecl opTgt optAttr [`simp]
    applySelectedOptAttrsToDecl opMapTgt optAttr [`simp]
    for specializedTgt in specializedTargets do
      applyOptAttrsToDecl specializedTgt optAttr
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
