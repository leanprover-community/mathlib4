/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/

import Lean
import Std.Data.List.Basic
import Mathlib.Init.Data.Nat.Notation

namespace Mathlib.Tactic

open Lean Elab.Tactic

/--
If the current goals are `g₁ ⋯ gᵢ ⋯ gₙ`, `splitGoalsAndGetNth i` returns
`(gᵢ, [g₁, ⋯, gᵢ₋₁], [gᵢ₊₁, ⋯, gₙ])`.

If `reverse` is passed as `true`, the `i`-th goal is picked by counting backwards.
For instance, `splitGoalsAndGetNth 1 true` puts the last goal in the first component
of the returned term.
-/
def splitGoalsAndGetNth (nth : ℕ) (reverse : Bool := false) :
    TacticM (MVarId × List MVarId × List MVarId) := do
  if nth = 0 then throwError "goals are 1-indexed"
  let goals ← getGoals
  let nGoals := goals.length
  if nth > nGoals then throwError "goal index out of bounds"
  let n := if ¬reverse then nth - 1 else nGoals - nth
  let (gl, g :: gr) := goals.splitAt n | throwNoGoalsToBeSolved
  pure (g, gl, gr)

/--
`pick_goal n` will move the `n`-th goal to the front.

`pick_goal -n` will move the `n`-th goal (counting from the bottom) to the front.

See also `Tactic.rotate_goals`, which moves goals from the front to the back and vice-versa.
-/
elab "pick_goal " reverse:"-"? n:num : tactic => do
  let (g, gl, gr) ← splitGoalsAndGetNth n.1.toNat !reverse.isNone
  setGoals $ g :: (gl ++ gr)

/-- `swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals. -/
macro "swap" : tactic => `(tactic| pick_goal 2)

/--
`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals, replacing the chosen goal.
-/
elab "on_goal " reverse:"-"? n:num " => " seq:tacticSeq : tactic => do
  let (g, gl, gr) ← splitGoalsAndGetNth n.1.toNat !reverse.isNone
  setGoals [g]
  evalTactic seq
  setGoals $ gl ++ (← getUnsolvedGoals) ++ gr
