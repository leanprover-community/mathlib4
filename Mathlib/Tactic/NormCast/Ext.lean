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

def getSimpArgs (e : Expr) : MetaM (Array Expr) := do
  match ← mkCongrSimp? e.getAppFn with
  | none => return e.getAppArgs
  | some {argKinds, ..} =>
    let mut args := #[]
    for a in e.getAppArgs, k in argKinds do
      if k matches CongrArgKind.eq then
        args := args.push a
    return args

/-- Count how many coercions are at the top of the expression. -/
partial def countHeadCoes (e : Expr) : MetaM Nat := do
  if let Expr.const fn .. := e.getAppFn then
    if let some info ← getCoeFnInfo? fn then
      if e.getAppNumArgs >= info.numArgs then
        return (← countHeadCoes (e.getArg! info.coercee)) + 1
  return 0

/-- Count how many coercions are inside the expression, including the top ones. -/
partial def countCoes (e : Expr) : MetaM Nat :=
  lambdaTelescope e fun _ e => do
    if let Expr.const fn .. := e.getAppFn then
      if let some info ← getCoeFnInfo? fn then
        if e.getAppNumArgs >= info.numArgs then
          let mut coes := (← countHeadCoes (e.getArg! info.coercee)) + 1
          for i in [info.numArgs:e.getAppNumArgs] do
            coes := coes + (← countCoes (e.getArg! i))
          return coes
    return (← (← getSimpArgs e).mapM countCoes).foldl (·+·) 0

/-- Count how many coercions are inside the expression, excluding the top ones. -/
def countInternalCoes (e : Expr) : MetaM Nat :=
  return (← countCoes e) - (← countHeadCoes e)

/-- Classifies a declaration of type `ty` as a `norm_cast` rule. -/
def classifyType (ty : Expr) : MetaM Label :=
  forallTelescopeReducing ty fun _ ty => do
    let ty ← whnf ty
    let (lhs, rhs) ←
      if ty.isAppOfArity ``Eq 3 then pure (ty.getArg! 1, ty.getArg! 2)
      else if ty.isAppOfArity ``Iff 2 then pure (ty.getArg! 0, ty.getArg! 1)
      else throwError "norm_cast: lemma must be = or ↔, but is{indentExpr ty}"
    let lhsCoes ← countCoes lhs
    if lhsCoes = 0 then throwError "norm_cast: badly shaped lemma, lhs must contain at least one coe{indentExpr lhs}"
    let lhsHeadCoes ← countHeadCoes lhs
    let rhsHeadCoes ← countHeadCoes rhs
    let rhsInternalCoes ← countInternalCoes rhs
    if lhsHeadCoes = 0 then
      return Label.elim
    else if lhsHeadCoes = 1 then do
      unless rhsHeadCoes = 0 do throwError "norm_cast: badly shaped lemma, rhs can't start with coe{indentExpr rhs}"
      if rhsInternalCoes = 0 then
        return Label.squash
      else
        return Label.move
    else if rhsHeadCoes < lhsHeadCoes then do
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
  addSimpTheorem normCastExt.up decl (post := true) (inv := false) kind prio

/-- `addMove decl` adds `decl` as a `move` lemma to the cache. -/
def addMove (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl (post := true) (inv := false) kind prio
  addSimpTheorem normCastExt.up decl (post := true) (inv := true) kind prio
  addSimpTheorem normCastExt.down decl (post := true) (inv := false) kind prio

/-- `addSquash decl` adds `decl` as a `squash` lemma to the cache. -/
def addSquash (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl (post := true) (inv := false) kind prio
  addSimpTheorem normCastExt.squash decl (post := true) (inv := false) kind prio
  addSimpTheorem normCastExt.down decl (post := true) (inv := false) kind prio

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


/--
The `norm_cast` attribute should be given to lemmas that describe the
behaviour of a coercion in regard to an operator, a relation, or a particular
function.

It only concerns equality or iff lemmas involving `↑`, `⇑` and `↥`, describing the behavior of
the coercion functions.
It does not apply to the explicit functions that define the coercions.

Examples:
```lean
@[norm_cast] theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n

@[norm_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1

@[norm_cast] theorem cast_id : ∀ n : ℚ, ↑n = n

@[norm_cast] theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n

@[norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n

@[norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1
```

Lemmas tagged with `@[norm_cast]` are classified into three categories: `move`, `elim`, and
`squash`. They are classified roughly as follows:

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes

`norm_cast` uses `move` and `elim` lemmas to factor coercions toward the root of an expression
and to cancel them from both sides of an equation or relation. It uses `squash` lemmas to clean
up the result.

Occasionally you may want to override the automatic classification.
You can do this by giving an optional `elim`, `move`, or `squash` parameter to the attribute.

```lean
@[simp, norm_cast elim] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n := by
  rw [← of_real_nat_cast, of_real_re]
```

Don't do this unless you understand what you are doing.

A full description of the tactic, and the use of each lemma category, can be found at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
syntax (name := normCast) "norm_cast" (ppSpace normCastLabel)? (ppSpace num)? : attr
end Attr

initialize registerBuiltinAttribute {
  name := `normCast
  descr := "attribute for norm_cast"
  add := fun decl stx kind => MetaM.run' do
    let `(attr| norm_cast $[$label:normCastLabel]? $[$prio]?) := stx | unreachable!
    let prio := (prio.bind (·.1.isNatLit?)).getD (eval_prio default)
    match label.bind (·.1.isStrLit?) with
    | "elim" => addElim decl kind prio
    | "move" => addMove decl kind prio
    | "squash" => addSquash decl kind prio
    | none => addInfer decl kind prio
    | _ => unreachable!
}
