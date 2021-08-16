/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.Tactic.OpenPrivate
import Lean

/-
This file adds support for a block structuring tactic. Blocks are started by an initial `-` and
all tactics in the same indentation level are part of a block:

```
- tac1
  tac2
  tac3
```
In this version, `tac1` produces two subgoals that are handled by `tac2` and `tac3` respectively:
```
- tac1
  - tac2
  - tac3
```
Blocks are a simple way to make it clear where and how goals are produced and discharged.
Furthermore, errors in one block do not affect the processing of the rest of the proof: every block
always discharges the goal it is tasked with, and will report a (non-fatal) error if not all
subgoals are handled.

Note: until https://github.com/leanprover/lean4/issues/451 is resolved, tactics that end in an
expression will break this parser, so you have to put parentheses around the tactic like so:
```
(apply And.intro)
- subgoal
- subgoal
```
-/
namespace Lean
namespace Elab
namespace Tactic

/- Close the main goal using the given tactic. If it fails,
  log the error and `admit` all remaining goals -/
def closeAllOrAdmit : TacticM Unit := do
  let gs ← getUnsolvedGoals
  unless gs.isEmpty do
    try Term.reportUnsolvedGoals gs catch ex => logException ex
    for g in gs do
      admitGoal g
    setGoals []

/- Focus the goal, i.e. suppress all goals except the main goal, run `tac`, then admit any
unproven goals and restore the remaining goals. -/
def focusAndBlock (tac : TacticM Unit) : TacticM Unit := do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  try tac catch ex => logException ex
  closeAllOrAdmit
  setGoals mvarIds

open private evalManyTacticOptSemi in evalTacticSeq1Indented in
-- TODO: why doesn't `tacticSeq?` work here?
elab (name := block) tk:"-" tacs:optional(tacticSeq) : tactic =>
  withRef tk $ do
    focusAndBlock $ do
    if let some stx := tacs then
      evalTacticSeq stx

end Tactic
end Elab

end Lean

/-
example : (0 < 1 ∧ 2 < 3) ∧ 3 < 4 := by
  split
  - split
    - decide
    - decide
  - decide
-/
