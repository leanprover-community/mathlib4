/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro, Gabriel Ebner
-/

import Lean
import Mathlib.Tactic.NormCast.CoeExt
import Mathlib.Tactic.RunCmd

open Lean Meta

namespace Tactic.NormCast

/--
`label` is a type used to classify `norm_cast` lemmas.
* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
inductive Label
  | elim
  | move
  | squash
  deriving DecidableEq, Repr, Inhabited

open Mathlib.Tactic.NormCast

def getSimpArgs (e : Expr) : MetaM (Array Expr) := do
  match ← mkCongrSimp? e.getAppFn with
  | none => return e.getAppArgs
  | some {argKinds, ..} =>
    let mut args := #[]
    for a in e.getAppArgs, k in argKinds do
      if k matches CongrArgKind.eq then
        args := args.push a
    return args

def isCoeOf? (e : Expr) : MetaM (Option Expr) := do
  if let Expr.const fn .. := e.getAppFn then
    if let some info ← getCoeFnInfo? fn then
      if e.getAppNumArgs == info.numArgs then
        return e.getArg! info.coercee
  return none

/-- Count how many coercions are at the top of the expression. -/
partial def countHeadCoes (e : Expr) : MetaM Nat := do
  if let some e ← isCoeOf? e then
    return (← countHeadCoes e) + 1
  else
    return 0

/-- Count how many coercions are inside the expression, including the top ones. -/
partial def countCoes (e : Expr) : MetaM Nat := do
  if let some e ← isCoeOf? e then
    return (← countCoes e) + 1
  else
    -- TODO: function coercions
    lambdaTelescope e fun xs e =>
      return (← (← getSimpArgs e).mapM countCoes).foldl (·+·) 0

/-- Count how many coercions are inside the expression, excluding the top ones. -/
def countInternalCoes (e : Expr) : MetaM Nat :=
  return (← countCoes e) - (← countHeadCoes e)

/-- Classifies a declaration of type `ty` as a `norm_cast` rule. -/
def classifyType (ty : Expr) : MetaM Label :=
  forallTelescopeReducing ty fun xs ty => do
    let ty ← whnf ty
    let (lhs, rhs) ←
      if ty.isAppOfArity ``Eq 3 then pure (ty.getArg! 1, ty.getArg! 2)
      else if ty.isAppOfArity ``Iff 2 then pure (ty.getArg! 0, ty.getArg! 1)
      else throwError "norm_cast: lemma must be = or ↔, but is{indentExpr ty}"
    let lhs_coes ← countCoes lhs
    if lhs_coes = 0 then throwError "norm_cast: badly shaped lemma, lhs must contain at least one coe{indentExpr lhs}"
    let lhs_head_coes ← countHeadCoes lhs
    let lhs_internal_coes ← countInternalCoes lhs
    let rhs_head_coes ← countHeadCoes rhs
    let rhs_internal_coes ← countInternalCoes rhs
    if lhs_head_coes = 0 then
      return Label.elim
    else if lhs_head_coes = 1 then do
      unless rhs_head_coes = 0 do throwError "norm_cast: badly shaped lemma, rhs can't start with coe{indentExpr rhs}"
      if rhs_internal_coes = 0 then
        return Label.squash
      else
        return Label.move
    else if rhs_head_coes < lhs_head_coes then do
      return Label.squash
    else do
      throwError "norm_cast: badly shaped shaped squash lemma, rhs must have fewer head coes than lhs{indentExpr ty}"

initialize pushCastExt : SimpExtension ←
  registerSimpAttr `push_cast (extName := `Tactic.NormCast.pushCastExt) $
    "The `push_cast` simp attribute uses `norm_cast` lemmas " ++
    "to move casts toward the leaf nodes of the expression."

/--  The `norm_cast` attribute stores three simp sets. -/
structure NormCastExtension where
  up : SimpExtension
  down : SimpExtension
  squash : SimpExtension
  deriving Inhabited

initialize normCastExt : NormCastExtension ← pure {
  up := ← mkSimpExt `Tactic.NormCast.normCastExt.up
  down := ← mkSimpExt `Tactic.NormCast.normCastExt.down
  squash := ← mkSimpExt `Tactic.NormCast.normCastExt.squash
}

/-- `addElim decl` adds `decl` as an `elim` lemma to the cache. -/
def addElim (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit :=
  addSimpTheorem normCastExt.up decl false (inv := false) kind prio

/-- `addMove decl` adds `decl` as a `move` lemma to the cache. -/
def addMove (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl false (inv := false) kind prio
  addSimpTheorem normCastExt.up decl false (inv := true) kind prio
  addSimpTheorem normCastExt.down decl false (inv := false) kind prio

/-- `addSquash decl` adds `decl` as a `squash` lemma to the cache. -/
def addSquash (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl false (inv := false) kind prio
  addSimpTheorem normCastExt.squash decl false (inv := false) kind prio
  addSimpTheorem normCastExt.down decl false (inv := false) kind prio

/-- `addInfer decl` infers the label of `decl` and adds it to the cache.

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
def addInfer (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  let ty := (← getConstInfo decl).type
  match ← classifyType ty with
  | Label.elim => addElim decl kind prio
  | Label.squash => addSquash decl kind prio
  | Label.move => addMove decl kind prio

namespace Attr
syntax normCastLabel := &"elim" <|> &"move" <|> &"squash"
syntax (name := normCast) "norm_cast" (ppSpace normCastLabel)? (ppSpace num)? : attr
end Attr

initialize registerBuiltinAttribute {
  name := `normCast
  descr := "attribute for norm_cast"
  add := fun decl stx kind => MetaM.run' do
    let `(attr| norm_cast $[$label:normCastLabel]? $[$prio]?) := stx | unreachable!
    let prio := (prio.bind Syntax.isNatLit?).getD (eval_prio default)
    match label.bind Syntax.isStrLit? with
    | "elim" => addElim decl kind prio
    | "move" => addMove decl kind prio
    | "squash" => addSquash decl kind prio
    | none => addInfer decl kind prio
    | _ => unreachable!
}
