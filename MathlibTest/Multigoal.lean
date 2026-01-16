import Mathlib.Tactic.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Linter.Multigoal
import Mathlib.Util.SleepHeartbeats
import Mathlib.Tactic.SuccessIfFailWithMsg

set_option linter.style.multiGoal true

-- A deactivated linter does nothing.
set_option linter.style.multiGoal false in
example : True := by
  by_cases 0 = 0
  exact .intro
  exact .intro

#guard_msgs(drop warning) in
/--
warning: The following tactic starts with 2 goals and ends with 1 goal, 1 of which is not operated on.
  exact .intro
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : True := by
  by_cases 0 = 0
  exact .intro
  exact .intro

#guard_msgs(drop warning) in
/--
warning: The following tactic starts with 2 goals and ends with 1 goal, 1 of which is not operated on.
  assumption
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example {n : Nat} (hn : n = 0) : n + 0 = 0 := by
  conv =>
    congr
    rw [← Nat.add_zero 0]
  conv_lhs =>
    congr
    rw [← Nat.add_zero n]
    rfl
  conv_rhs =>
    rw [← Nat.add_zero 0]
    congr
    rfl
    rfl
  by_cases 0 = 0
  assumption
  assumption

set_option linter.unusedTactic false in
#guard_msgs(drop warning) in
/--
warning: The following tactic starts with 2 goals and ends with 1 goal, 1 of which is not operated on.
  rfl
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example (p : Prop) (hp : p) : (0 = 0 ∧ p) ∨ 0 = 0 := by
  iterate left; decide
  repeat' left; decide
  refine Or.inl ⟨?_, ?_⟩
  rfl
  assumption

#guard_msgs(drop warning) in
/--
warning: The following tactic starts with 3 goals and ends with 2 goals, 2 of which are not operated on.
  rfl
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
---
warning: The following tactic starts with 2 goals and ends with 1 goal, 1 of which is not operated on.
  trivial
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : 0 = 0 ∧ 0 = 0 ∧ 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  rfl
  trivial
  rfl

example (p : Bool) : 0 = 0 := by
  cases p
  case' false => rfl
  case' true => rfl

#guard_msgs in
-- `assumption'` is allowed, as it is useful precisely when there are multiple active goals.
example (p : Bool) (f : False) {h : 0 = 0} : 0 = 0 ∧ 0 = 1 := by
  cases p <;>
  constructor
  assumption'
  any_goals cases f

#guard_msgs in
-- `focus` is ignored.
example : True ∧ True := by
  constructor
  focus
    exact .intro
  focus
    exact .intro

set_option linter.unusedTactic false in
example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl

-- We test that a tactic closing all remaining goals does not trigger the linter.
macro "bi_trivial" : tactic => `(tactic| (trivial; trivial))

example : True ∧ True := by
  constructor
  bi_trivial

-- Exclude `fail_if_success` and `success_if_fail_with_msg` from linting.
example : True := by
  fail_if_success done
  success_if_fail_with_msg "internal exception #5" done
  exact .intro

/-!
Testing that it does not flag tactics that do nothing.
This used to trigger the multigoal linter.
-/
elab "my_skip" : tactic => pure ()
set_option linter.unusedTactic false in
example : True := by
  my_skip
  trivial

-- Test the linter applies within have statements
#guard_msgs(drop warning) in
/--
  warning: The following tactic starts with 2 goals and ends with 1 goal, 1 of which is not operated on.
  trivial
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
example : true ∧ true := by
  have : true ∧ true := by
    constructor
    trivial
    trivial
  exact this
