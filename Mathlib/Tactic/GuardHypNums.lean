import Lean

open Lean Meta Elab Tactic

elab (name := guardHypNums) "guard_hyp_nums " n:num : tactic => do
  let num_goals := (← getGoals).length
  guard (num_goals = n.getNat) <|>
    throwError "expected {n.getNat} goals but found {num_goals}"
