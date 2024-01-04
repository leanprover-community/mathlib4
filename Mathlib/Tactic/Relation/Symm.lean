/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Lean.Meta
import Std.Tactic.Relation.Symm
import Lean.Elab.Tactic.Location

/-!
# `symm_saturate` tactic

For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`.
-/

set_option autoImplicit true

open Lean Meta

namespace Lean.MVarId

/-- For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`. -/
def symmSaturate (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g' := g
  let hyps ← getLocalHyps
  let types ← hyps.mapM inferType
  for h in hyps do try
    let symm ← h.applySymm
    let symmType ← inferType symm
    if ¬ (← types.anyM (isDefEq symmType)) then
      (_, g') ← g'.note ((← h.fvarId!.getUserName).appendAfter "_symm") symm
  catch _ => g' ← pure g'
  return g'

end Lean.MVarId

namespace Mathlib.Tactic

open Lean.Elab.Tactic Std.Tactic

/-- For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`. -/
elab "symm_saturate" : tactic => liftMetaTactic1 fun g => g.symmSaturate

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
    unless (← (symmExt.getState (← getEnv)).getMatch rel symmExt.config).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none
