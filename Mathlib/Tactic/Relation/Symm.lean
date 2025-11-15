/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Meta.Tactic.Symm
import Qq

/-!
# `relSidesIfSymm?`
-/

open Lean Meta Symm Qq

namespace Mathlib.Tactic

open Lean.Elab.Tactic

/-- If `e` is the form `@R .. x y`, where `R` is a symmetric
relation, return `some (R, x, y)`.
As a special case, if `e` is `@HEq α a β b`, return ``some (`HEq, a, b)``. -/
def _root_.Lean.Expr.relSidesIfSymm? (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (_, lhs, rhs) := e.eq? then
    return (``Eq, lhs, rhs)
  if let some (lhs, rhs) := e.iff? then
    return (``Iff, lhs, rhs)
  if let some (_, lhs, _, rhs) := e.heq? then
    return (``HEq, lhs, rhs)
  if let .app (.app rel lhs) rhs := e then
    unless (← (symmExt.getState (← getEnv)).getMatch rel).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none

end Mathlib.Tactic

/-- Given a term `e : Prop` of the form `a ~ b`, use `@[symm]` lemmas to construct a `Simp.Result`
proving the equivalence of `e` with `b ~ a` . -/
def Lean.Expr.eqSymm (e : Expr) : MetaM Simp.Result := do
  have e : Q(Prop) := e
  let .app (.app rel lhs) rhs := e | failure
  let lemmas ← (Symm.symmExt.getState (← getEnv)).getMatch rel
  guard !lemmas.isEmpty <|> throwError "no appropriate symmetry lemma found"
  have e' : Q(Prop) := .app (.app rel rhs) lhs
  let ((pf1 : Q($e → $e')), (pf2 : Q($e' → $e))) : Q($e → $e') × Q($e' → $e) := ← do
    let m1 ← mkFreshExprMVarQ q($e → $e')
    let m2 ← mkFreshExprMVarQ q($e' → $e)
    let s ← saveState
    for lem in lemmas do
      restoreState s
      let [] ← m1.mvarId!.applyConst lem | failure
      let [] ← m2.mvarId!.applyConst lem | failure
      return (← instantiateMVars m1, ← instantiateMVars m2)
    throwError "no appropriate symmetry lemma found"
  let pf : Q($e = $e') := q(propext ⟨$pf1, $pf2⟩)
  pure { expr := e', proof? := some pf }
