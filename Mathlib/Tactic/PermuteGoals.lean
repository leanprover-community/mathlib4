/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arthur Paulino, Mario Carneiro
-/

import Lean
import Mathlib.Data.List.Defs

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
  let (g, gl, gr) ← splitGoalsAndGetNth n.toNat !reverse.isNone
  setGoals $ g :: (gl ++ gr)

/-- `swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals. -/
macro "swap" : tactic => `(pick_goal 2)

syntax signedNum := "-"? num

/--
`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

`on_goal n₁ n₂ n₃ => tacSeq` runs the tactic sequence on each of the selected goals.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals without reordering the list. For example, if goals `2` and `4` are selected
in the list `[1, 2, 3, 4, 5]`, where goal `2` produces `2a`, `2b`, and `4` produces `4a`,
the resulting list of goals is `[1, 2a, 2b, 3, 4a, 5]`.
-/
elab "on_goal" args:(ppSpace signedNum)+ " => " seq:tacticSeq : tactic => do
  match args.getArgs with
  | #[arg] =>
    let (g, gl, gr) ← splitGoalsAndGetNth arg[1].toNat !arg[0].isNone
    setGoals [g]
    evalTactic seq
    setGoals $ gl ++ (← getUnsolvedGoals) ++ gr
  | args =>
    let goals := (← getGoals).toArray
    let idxs ← args.mapM fun arg => do
      let nth := arg[1].toNat
      if nth = 0 then throwError "goals are 1-indexed"
      if nth > goals.size then throwError "goal index out of bounds"
      pure $ if arg[0].isNone then nth - 1 else goals.size - nth
    let newGoals ← idxs.mapM fun i => (i, ·) <$> do
      let g := goals[i]
      if ← Meta.isExprMVarAssigned g then return []
      setGoals [g]
      evalTactic seq
      getUnsolvedGoals
    let mut start := 0
    let mut result := #[]
    for (i, out) in newGoals.insertionSort (·.1 < ·.1) do
      for j in [start:i] do result := result.push goals[j]
      for g in out do result := result.push g
      start := i + 1
    for j in [start:goals.size] do result := result.push goals[j]
    setGoals result.toList

/--
`on_goals n₁ n₂ n₃ => tacSeq` is similar to `on_goal n₁ n₂ n₃ => tacSeq`, but `tacSeq` is
only run once, on a goal state composed of all the selected goals.
The subgoals that are generated are placed at the head of the list, and any unselected
goals are placed at the end. For example, if goals `2` and `4` are selected from `[1, 2, 3, 4, 5]`
and the tactic on `[2, 4]` produces goals `[a, b, c]`, then the resulting list of goals
is `[a, b, c, 1, 3, 5]`.
-/
elab "on_goals" args:(ppSpace signedNum)+ " => " seq:tacticSeq : tactic => do
  let goals := (← getGoals).toArray
  let mut usedGoals := mkArray goals.size false
  let mut idxs := #[]
  for arg in args.getArgs do
    let nth := arg[1].toNat
    if nth = 0 then throwError "goals are 1-indexed"
    if nth > goals.size then throwError "goal index out of bounds"
    let i := if arg[0].isNone then nth - 1 else goals.size - nth
    idxs := idxs.push i
    usedGoals := usedGoals.set! i true
  setGoals (idxs.map (goals[·])).toList
  evalTactic seq
  let mut result := #[]
  for i in [:goals.size] do
    if !usedGoals[i] then
      result := result.push goals[i]
  appendGoals result.toList
