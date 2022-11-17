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

open Lean Meta Elab Tactic

/-- Return local hypotheses which are not "implementation detail", as `Expr`s. -/
def Lean.Meta.getLocalHyps : MetaM (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

initialize registerTraceClass `solveByElim

/-- Attempt to solve the given metavariable by repeating applying a list of facts. -/
def Lean.Meta.solveByElim (es : List Expr) : Nat → MVarId → MetaM Unit
| 0, _ => throwError "solve_by_elim exceeded its recursion limit"
| n+1, goal => do
  trace[solveByElim] "Working on: {goal}"
  -- We attempt to find an expression which can be applied,
  -- and for which all resulting sub-goals can be discharged using `solveByElim n`.
  es.firstM (fun e ↦ do
    trace[solveByElim] "Trying to apply: {e}"
    for g in (← goal.apply e) do
      if ¬ (← g.isAssigned) then solveByElim es n g)

namespace Lean.Tactic

open Lean.Parser.Tactic

/-- Attempt to solve the given metavariable by repeating applying one of the given expressions,
or a local hypothesis. -/
def solveByElimImpl (only : Bool) (es : List Expr) (n : Nat) (g : MVarId) : MetaM Unit := do
  let es ← (if only then return es else return es ++ (← getLocalHyps).toList)
  Lean.Meta.solveByElim es n g

syntax (name := solveByElim) "solve_by_elim" "*"? (config)? (&" only")? (simpArgs)? : tactic

elab_rules : tactic | `(tactic| solve_by_elim $[only%$o]? $[[$[$t:term],*]]?) => withMainContext do
  let es ← (t.getD #[]).toList.mapM (elabTerm ·.raw none)
  solveByElimImpl o.isSome es 6 (← getMainGoal)

end Lean.Tactic
