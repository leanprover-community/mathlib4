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

public meta section

open Filter

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

def proveFunEqZero (f : Q(ℝ → ℝ)) : TacticM <| Q($f =ᶠ[atTop] 0) := do
  let e ← mkFreshExprMVarQ q(∀ x, $f x = 0)
  let res ← evalTacticAt (← `(tactic| intro; simp <;> field)) e.mvarId!
  if res.isEmpty then
    return q(EventuallyEq.of_eq (funext $e))
  throwError f!"Cannot prove that {← ppExpr f} =ᶠ[atTop] 0. You can use a `have` " ++
    "statement to provide the sign of the expression."

end ComputeAsymptotics
