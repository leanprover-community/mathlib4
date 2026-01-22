/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Tactic.Field
public import Qq

/-!
# Zeroness oracle

This module implements the (eventual) zeroness oracle. The function
`proveFunEqZero` tries to prove that a function is eventually zero.

This is used in the trimming procedure when we suspect that a multiseries represents
a zero function. Without the oracle, we would need to trim infinite amount of cancellations.
-/

public meta section

open Filter

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

/-- Proves that `f` is eventually zero. -/
def proveFunEqZero (f : Q(ℝ → ℝ)) : TacticM <| Q($f =ᶠ[atTop] 0) := do
  let e ← mkFreshExprMVarQ q(∀ x, $f x = 0)
  let res ← evalTacticAt (← `(tactic| intro; simp <;> field)) e.mvarId!
  if res.isEmpty then
    return q(EventuallyEq.of_eq (funext $e))
  throwError f!"Cannot prove that {← ppExpr f} =ᶠ[atTop] 0. You can use a `have` " ++
    "statement to provide the sign of the expression."

end ComputeAsymptotics
