import Mathlib.Tactic.PermuteGoals

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros
  constructor
  on_goal 2 =>
    guard_target == q ∧ r
    constructor
    assumption
    -- Note that we have not closed all the subgoals here.
  guard_target == p
  assumption
  guard_target == r
  assumption

example (p q r : Prop) : p → q → r → p ∧ q ∧ r := by
  intros a b c
  constructor
  fail_if_success on_goal -3 => exact a
  fail_if_success on_goal -1 => exact a
  fail_if_success on_goal 0 => exact a
  fail_if_success on_goal 2 => exact a
  fail_if_success on_goal 3 => exact a
  on_goal 1 => exact a
  constructor
  swap
  exact c
  exact b

example (p q : Prop) : p → q → p ∧ q := by
  intros a b
  constructor
  fail_if_success pick_goal -3
  fail_if_success pick_goal 0
  fail_if_success pick_goal 3
  pick_goal -1
  exact b
  exact a

example (p : Prop) : p → p := by
  intros
  fail_if_success swap -- can't swap with a single goal
  assumption

example {P : ℕ → Prop} (h : ∀ n, P n) : P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  on_goal 2 => guard_target == P 2
  on_goal 2 => guard_target == P 2
  on_goal 1 => guard_target == P 1
  on_goal 1 3 => apply fun {α} x y : α => x
  on_goal 1 => guard_target == P 1
  on_goal 2 => guard_target == P 1
  on_goal 3 => guard_target == P 2
  on_goal 4 => guard_target == P 3
  on_goal 5 => guard_target == P 3
  on_goal 6 => guard_target == P 4
  on_goal 7 => guard_target == P 5
  all_goals apply h

example {P : ℕ → Prop} (h : ∀ n, P n) : P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  on_goals 2 4 =>
    on_goal 1 => guard_target == P 2
    on_goal 2 => guard_target == P 4
    swap
  on_goal 1 => guard_target == P 4
  on_goal 2 => guard_target == P 2
  on_goal 3 => guard_target == P 1
  on_goal 4 => guard_target == P 3
  on_goal 5 => guard_target == P 5
  all_goals apply h
