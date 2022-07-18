import Lean

open Lean Meta Elab Tactic

/-- `guard_goal_nums n` succeeds if there are exactly `n` goals and fails otherwise. -/
elab (name := guardGoalNums) "guard_goal_nums " n:num : tactic => do
  let num_goals := (← getGoals).length
  guard (num_goals = n.getNat) <|>
    throwError "expected {n.getNat} goals but found {num_goals}"
