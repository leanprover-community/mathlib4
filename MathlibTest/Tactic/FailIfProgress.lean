module
import Mathlib.Tactic.FailIfProgress
import Mathlib.Tactic.Basic

set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option pp.unicode.fun true

section success

/--
error: progress made on
⊢ 1 = 1
-/
#guard_msgs in
example : 1 = 1 := by fail_if_progress rfl

/--
error: progress made on
h : 1 = 1
⊢ True
-/
#guard_msgs in
example (h : 1 = 1) : True := by
  fail_if_progress simp
  trivial

/--
error: progress made on
p : Prop
hp : p
⊢ p
-/
#guard_msgs in
example {p : Prop} (hp : p) : p := by
  fail_if_progress simp [hp]

set_option linter.unusedTactic false

example (a : Nat) : 2 + 0 = 4 := by
  fail_if_not_idempotent simp
  fail_if_progress fail_if_not_idempotent norm_cast

example : 1 + 1 = 2 := by
  -- simp; fail_if_progress simp would error
  fail_if_not_idempotent simp
