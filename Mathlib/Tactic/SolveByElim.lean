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

initialize registerTraceClass `Meta.Tactic.solveByElim

/-- Attempt to solve the given metavariable by repeating applying a list of facts. -/
def Mathlib.Meta.solveByElim (es : List Expr) : Nat → MVarId → MetaM Unit
| 0, _ => throwError "solve_by_elim exceeded its recursion limit"
| n+1, goal => do
  trace[Meta.Tactic.solveByElim] "Working on: {goal}"
  -- We attempt to find an expression which can be applied,
  -- and for which all resulting sub-goals can be discharged using `solveByElim n`.
  es.firstM fun e => do
    trace[Meta.Tactic.solveByElim] "Trying to apply: {e}"
    for g in (← goal.apply e) do
      if ¬ (← g.isAssigned) then solveByElim es n g

namespace Mathlib.Tactic

open Lean.Parser.Tactic

/-- Attempt to solve the given metavariable by repeating applying one of the given expressions,
or a local hypothesis. -/
def solveByElimImpl (only : Bool) (es : List Expr) (n : Nat) (g : MVarId) : MetaM Unit := do
  let es ← (if only then return es else return es ++ (← getLocalHyps).toList)
  Mathlib.Meta.solveByElim es n g

/--
`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `max_depth` recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs back-tracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congr_fun` and `congr_arg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ, attr₁, ... attrᵣ]` also applies the named lemmas,as well as
  all lemmas tagged with the specified attributes.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congr_fun`, or `congr_arg` unless they are explicitly included.
* `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions, removing the specified ones.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated sub-goals
- `discharger`: a subsidiary tactic to try at each step when no lemmas apply
  (e.g. `cc` may be helpful).
- `preApply`: a subsidiary tactic to run at each step before applying lemmas (e.g. `intros`).
- `accept`: a subsidiary tactic `List Expr → Tactic` that at each step,
  before any lemmas are applied, is passed the original proof terms
  as reported by `getGoals` when `solve_by_elim` started
  (but which may by now have been partially solved by previous `apply` steps).
  If the `accept` tactic fails,
  `solve_by_elim` will abort searching the current branch and backtrack.
  This may be used to filter results, either at every step of the search,
  or filtering complete results
  (by testing for the absence of metavariables, and then the filtering condition).
-/
syntax (name := solveByElim) "solve_by_elim" "*"? (config)? (&" only")? (simpArgs)? : tactic

elab_rules : tactic | `(tactic| solve_by_elim $[only%$o]? $[[$[$t:term],*]]?) => withMainContext do
  let es ← (t.getD #[]).toList.mapM (elabTerm ·.raw none)
  solveByElimImpl o.isSome es 6 (← getMainGoal)
