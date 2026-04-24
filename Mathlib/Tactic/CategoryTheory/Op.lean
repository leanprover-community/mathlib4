/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Lean.Meta.Simp
public import Mathlib.Util.AddRelatedDecl

/-!
# The `op` attribute

Adding `@[op]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_op` by applying `Quiver.Hom.op` to both sides
and then simplifying with `simp only [op_comp, op_id]`.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Op

/-- `simp only` with `op_comp` and `op_id` on a single expression (used on each side via
`simpEq`). -/
def opSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``op_comp, ``op_id] e (config := { decide := false })

private def assertEqHom (eqTy : Expr) : MetaM Unit := do
  let some (α, _, _) := eqTy.cleanupAnnotations.eq? | throwError "`@[op]` expects an equality"
  let (``Quiver.Hom, #[_, _, _, _]) := α.getAppFnArgs |
    throwError "`@[op]` expects an equality of morphisms"
  pure ()

/-- A variant of `congrArg Quiver.Hom.op` with a convenient argument order for metaprogramming. -/
@[to_dual none] theorem eq_op' {C : Type*} [Category* C]
    {X Y : C} {f g : X ⟶ Y} (w : f = g) : f.op = g.op := by
  simpa using congrArg Quiver.Hom.op w

/-- Build the `op` lemma for `e : f = g`, simplifying the resulting equality with `op_comp` and
`op_id`. -/
def opExprHom (e : Expr) : MetaM (Expr × Array MVarId) := do
  assertEqHom (← inferType e)
  let lem₀ ← mkConstWithFreshMVarLevels ``eq_op'
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 7
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[6]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType opSimp (mkAppN lem₀ args), #[inst.mvarId!])

/--
Given a proof `pf` of `∀ .., f = g` with `f g` morphisms in a category, produce a proof of the
corresponding `op` lemma.
-/
def opExpr (pf : Expr) : MetaM (Expr × Array MVarId) := do
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pf := mkAppN pf xs
    let (pf, insts) ← opExprHom pf
    return (← mkLambdaFVars xs pf, insts)

/--
Version of `opExpr` for the `TermElabM` monad. Handles instance metavariables automatically.
-/
def opExpr' (pf : Expr) : TermElabM Expr := do
  let (e, insts) ← opExpr pf
  for inst in insts do
    inst.withContext do
      unless ← Term.synthesizeInstMVarCore inst do
        Term.registerSyntheticMVarWithCurrRef inst (.typeClass none)
  return e

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
        let pf ← opExpr' value
        pure (pf, levels)
  | _ => throwUnsupportedSyntax }

/--
`op_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with `Quiver.Hom.op` applied to both sides and
`simp only [op_comp, op_id]` on each side.
-/
elab "op_of% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  opExpr' e

end Mathlib.Tactic.CategoryTheory.Op
