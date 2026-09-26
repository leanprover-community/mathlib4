/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Lean.Meta.Simp
public import Mathlib.Util.AddRelatedDecl
public import Qq

/-!
# The `op` attribute

Adding `@[op]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_op` by applying `Quiver.Hom.op` to both sides
and then simplifying with `simp only [op_comp, op_id]`.

There is also a term elaborator `op_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic Qq
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Op

/-- `simp only` with `op_comp` and `op_id` on a single expression (used on each side via
`simpEq`). -/
def opSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``op_comp, ``op_id] e (config := { decide := false })

/-- Build the `op` lemma for `e : f = g`, simplifying the resulting equality with `op_comp` and
`op_id`. -/
def opExprHom (type : Q(Prop)) (e : Q($type)) : Term.TermElabM Expr := do
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
    throwError "`@[op]` expects an equality of morphisms"
  let _ : $type =Q $eqType := ⟨⟩
  let opType : Q(Prop) := q(Quiver.Hom.op $f = Quiver.Hom.op $g)
  let opProof : Q($opType) := q(congrArg Quiver.Hom.op $e)
  -- As in `map_of%`, let simplification use the instance even if synthesis is still pending.
  let inst := instC.mvarId!
  let (pf, ()) ← withEnsuringLocalInstance inst do
    let (type, pf) ← simpEq opSimp opType opProof
    -- `op_comp` and `op_id` are definitional equalities, so the proof alone need not change.
    return (← mkExpectedTypeHint pf type, ())
  -- Rewriting can determine the source category after this elaborator returns.
  unless ← Term.synthesizeInstMVarCore inst do
    Term.registerSyntheticMVarWithCurrRef inst (.typeClass none)
  return pf

/--
Given a proof `pf` of `∀ .., f = g` with `f g` morphisms in a category, produce a proof of the
corresponding `op` lemma.
-/
def opExpr (pf : Expr) : Term.TermElabM Expr := do
  forallTelescopeReducing (← inferType pf) (whnfType := true) fun xs type => do
    let type := (← instantiateMVars type).consumeMData
    let some _ := type.eq? | throwError "`@[op]` expects an equality"
    let type : Q(Prop) := type
    let pfApp := mkAppN pf xs
    let inner ← opExprHom type pfApp
    mkLambdaFVars xs inner

/--
Adding `@[op]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms in
some category `C`, creates a new lemma named `H_op` by applying `Quiver.Hom.op` to both sides and
then simplifying with `simp only [op_comp, op_id]`.

Use `@[op (attr := map)]` to mark both the original lemma and `H_op` with `map`, and similarly
for `reassoc` and other attributes.
-/
syntax (name := opStx) "op" optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `opStx
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| op $optAttr) => MetaM.run' do
    if kind != AttributeKind.global then
      throwError "`op` can only be used as a global attribute"
    let tgt := src.appendAfter "_op"
    addRelatedDecl src tgt ref optAttr fun value levels => do
      Term.TermElabM.run' <| Term.withSynthesize do
        let pf ← opExpr value
        pure (pf, levels)
  | _ => throwUnsupportedSyntax }

/--
`op_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with `Quiver.Hom.op` applied to both sides and
`simp only [op_comp, op_id]` on each side.
-/
elab "op_of% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  opExpr e

end Mathlib.Tactic.CategoryTheory.Op
