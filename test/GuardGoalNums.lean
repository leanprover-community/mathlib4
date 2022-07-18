import Mathlib.Tactic.GuardHypNums

example : true ∧ true := by
  constructor
  guard_goal_nums 2
  all_goals {constructor}

example : (true ∧ true) ∧ (true ∧ true) := by
  constructor <;> constructor
  guard_goal_nums 4
  all_goals {constructor}
