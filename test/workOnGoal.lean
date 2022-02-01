import Mathlib.Tactic.WorkOnGoal

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros
  constructor
  work_on_goal 1
    guard_target == q ∧ r
    constructor
    assumption
    -- Note that we have not closed all the subgoals here.
  guard_target == p
  assumption
  guard_target == r
  assumption
