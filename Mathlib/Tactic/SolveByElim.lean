/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.Core
import Mathlib.Lean.LocalContext

/-!
A primitive replacement for Lean3's `solve_by_elim` tactic.
We'll gradually bring it up to feature parity.
-/

open Lean.Elab.Tactic

/-- Attempt to solve the given metavariable by repeating applying a local hypothesis. -/
def Lean.Meta.solveByElim : Nat → MVarId → MetaM Unit
  | 0, _ => throwError "fail"
  | n+1, goal => do
      -- We attempt to find a local declaration which can be applied,
      -- and for which all resulting sub-goals can be discharged using `solveByElim n`.
      (← getLCtx).firstDeclM fun localDecl => do
        guard ¬ localDecl.isAuxDecl
        for g in (← goal.apply localDecl.toExpr) do solveByElim n g

namespace Lean.Tactic

open Lean.Parser.Tactic

syntax (name := solveByElim) "solve_by_elim" "*"? (config)?
  (&" only")? (" [" simpArg,* "]")? (" with " (colGt ident)+)? : tactic

elab_rules : tactic | `(tactic| solve_by_elim) => do withMainContext do
  Meta.solveByElim 6 (← getMainGoal)

end Lean.Tactic
