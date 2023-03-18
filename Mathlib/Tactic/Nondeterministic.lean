/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Scott Morrison
-/
import Lean.Meta.Basic

/-!
# Running nondeterministic tactics

A nondeterministic tactic is a function `tac : MVarId → MetaM (List (MetaM (List MVarId)))`,
that returns several alternative solutions to a goal.
The outermost list gives the alternatives,
while the innermost list gives the new subgoals in that alternative.

The function `nondeterministic` recursively runs such a nondeterministic tactic on a goal,
backtracking to other alternatives whenever a branch fails.
The argument `recurse` allows deciding whether to proceed into each subgoal,
or to "suspend" it, returning it to the caller.

The implementation is in `nondeterministicMany`, which allows starting with a collection of goals,
backtracking across all of them
(so successful solutions to an earlier goal may be rejected
if they preclude finding solutions to later goals).
-/

/--
`nondeterministicMany` runs a "nondeterministic" tactic
`tac : MVarId → MetaM (List (MetaM (List MVarId)))`
recursively on a collection of goals, backtracking as necessary.
For each subgoal, it evaluates `recurse : MVarId → MetaM Bool` to decide whether
to continue solving that goal, or to "suspend" the goal, returning it to the caller. -/
def Lean.MVarId.nondeterministicMany
    (tac : MVarId → MetaM (List (MetaM (List MVarId)))) (recurse : MVarId → MetaM Bool)
    (maxSteps : Nat) (goals : List MVarId) : MetaM (List MVarId) := do
match maxSteps, goals with
| 0, _ => failure
| _, [] => pure []
| maxSteps + 1, g::gs => do
  for choice in ← tac g do
    let mvars? ← observing? do
      let mut mvars' := []
      for mvar in ← choice do
        if ← recurse mvar then
          mvars' := (← nondeterministicMany tac recurse maxSteps (mvar :: gs)) ++ mvars'
        else
          mvars' := mvar :: mvars'
      mvars' := (← nondeterministicMany tac recurse maxSteps gs) ++ mvars'
      return mvars'
    if let some mvars := mvars? then
      return mvars
  failure

/--
`nondeterministic` runs a "nondeterministic" tactic
`tac : MVarId → MetaM (List (MetaM (List MVarId)))`
recursively on a goal, backtracking as necessary.
For each subgoal, it evaluates `recurse` to decide whether to continue solving that goal,
or to "suspend" the goal, returning it to the caller. -/
def Lean.MVarId.nondeterministic
    (tac : MVarId → MetaM (List (MetaM (List MVarId))))
    (recurse : MVarId → MetaM Bool) (maxSteps : Nat) (g : MVarId) : MetaM (List MVarId) :=
nondeterministicMany tac recurse maxSteps [g]
