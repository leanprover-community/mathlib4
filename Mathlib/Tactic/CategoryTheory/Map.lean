/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Lean.Meta.Simp
public import Mathlib.Util.AddRelatedDecl
public import Qq

/-!
# The `map` attribute

Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_map` of the form
`∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and then applies
`simp only [Functor.map_comp, Functor.map_id]`.

The generated lemma preserves the source's universe parameters in their original order,
followed by the target category's object and morphism universe parameters.

There is also a term elaborator `map_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic Qq
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Map

/-- `simp only` with `Functor.map_comp` and `Functor.map_id` on a single expression
(used on each side via `simpEq`). -/
def mapCompSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Functor.map_comp, ``Functor.map_id] e (config := { decide := false })

/-- Build the functor `map` lemma for `e : f = g` with target category levels `uLev`, `vLev`. -/
def mapExprHom (type : Q(Prop)) (e : Q($type)) (uLev vLev : Level) : Term.TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let C ← mkFreshExprMVarQ q(Type u)
  let instC ← mkFreshExprMVarQ q(Category.{v} $C) .synthetic
  let X ← mkFreshExprMVarQ q($C)
  let Y ← mkFreshExprMVarQ q($C)
  let f ← mkFreshExprMVarQ q($X ⟶ $Y)
  let g ← mkFreshExprMVarQ q($X ⟶ $Y)
  let eqType : Q(Prop) := q($f = $g)
  unless ← isDefEq type eqType do
    throwError "`@[map]` expects an equality of morphisms"
  let _ : $type =Q $eqType := ⟨⟩
  let mappedType : Q(Prop) := q(∀ {D : Type uLev} [_instD : Category.{vLev} D] (F : $C ⥤ D),
    F.map $f = F.map $g)
  let mappedProof : Q($mappedType) := q(fun {D : Type uLev} [_instD : Category.{vLev} D]
    (F : $C ⥤ D) => F.congr_map $e)
  -- As in `reassoc_of%`, let simplification use the instance even if synthesis is still pending.
  let inst := instC.mvarId!
  let (pf, ()) ← withEnsuringLocalInstance inst do
    let (_, pf) ← simpEq mapCompSimp mappedType mappedProof
    return (pf, ())
  -- Rewriting can determine the source category after this elaborator returns.
  unless ← Term.synthesizeInstMVarCore inst do
    Term.registerSyntheticMVarWithCurrRef inst (.typeClass none)
  return pf

/--
Given a proof `pf` of `∀ .., f = g` with `f g` morphisms in a category, produce a proof of the
`map` lemma, quantifying over every target category `D` and every functor `F : C ⥤ D`.
The target category uses fresh universe metavariables, which the attribute generalizes to
parameters and `map_of%` leaves for the surrounding elaboration to determine.
-/
def mapExpr (pf : Expr) : Term.TermElabM Expr := do
  let uLev ← mkFreshLevelMVar
  let vLev ← mkFreshLevelMVar
  forallTelescopeReducing (← inferType pf) (whnfType := true) fun xs type => do
    let type := (← instantiateMVars type).consumeMData
    let some _ := type.eq? | throwError "`@[map]` expects an equality"
    let type : Q(Prop) := type
    let pfApp := mkAppN pf xs
    let inner ← mapExprHom type pfApp uLev vLev
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
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| map $optAttr) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`map` can only be used as a global attribute"
    let tgt := src.appendAfter "_map"
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let pf ← mapExpr value
        -- Preserve the source parameters and append the target object and morphism universes,
        -- in the order in which their binders occur in the generated proof.
        let r := (← getMCtx).levelMVarToParam levels.contains (fun _ => false) pf
        setMCtx r.mctx
        pure (r.expr, levels ++ r.newParamNames.toList)
  | _ => throwUnsupportedSyntax }

/--
`map_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with a functor applied and
`simp only [Functor.map_comp, Functor.map_id]` on each side.
-/
elab "map_of% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  mapExpr e

end Mathlib.Tactic.CategoryTheory.Map
