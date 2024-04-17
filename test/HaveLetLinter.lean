import Mathlib.Tactic.HaveLetLinter
import Mathlib.Tactic.Tauto

#guard_msgs in
-- check that `tauto` does not trigger the linter
example : True := by
  tauto

#guard_msgs in
-- replace is ignored, no matter what
example : True := by
  let zero := 0
  replace _zero := zero
  let eq := (rfl : 0 = 0)
  replace _eq := eq
  exact .intro

set_option linter.haveLet false in
set_option linter.haveLet true in
/--
warning: 'Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
---
warning: 'Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
---
warning: 'Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
---
warning: 'Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
-/
#guard_msgs in
example : True := by
  have _a := 0
  have _b : Nat := 0
  have _b : 0 = 0 := rfl
  have _oh : Nat := 0
  have _b : Nat := 2
  tauto

set_option linter.haveLet false in
set_option linter.haveLet true in
/--
warning: 'Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
-/
#guard_msgs in
example : True := by
  have := Nat.succ ?_;
  exact .intro
  exact 0

#guard_msgs in
example : True := by
  have := And.intro (Nat.add_comm ?_ ?_) (Nat.add_comm ?_ ?_)
  apply True.intro
  exact 0
  exact 0
  exact 0
  exact 0

#guard_msgs in
example (h : False) : True := by
  have : False := h
  exact .intro

-- (← `(tactic| have := 0))

set_option linter.haveLet false in
set_option linter.haveLet true in
/--
warning: 'Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
-/
#guard_msgs in
theorem ghi : True := by
  have : Nat := Nat.succ 1;
  exact .intro
