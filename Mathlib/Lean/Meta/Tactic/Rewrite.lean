/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Patrick Massot, Kyle Miller
-/
import Mathlib.Init
import Lean.Meta.Tactic.Rewrite

/-!
# Additional declarations for `Lean.Meta.Tactic.Rewrite`
-/

namespace Lean.Expr

open Meta

/--
Rewrites `e` via some `eq`, producing a proof `e = e'` for some `e'`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

/--
Rewrites the type of `e` via some `eq`, then moves `e` into the new type via `Eq.mp`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← (← inferType e).rewrite eq) e

end Lean.Expr
