import Mathlib.Tactic.SuccessIfFailWithMsg
example : True := by
  success_if_fail_with_msg "No goals to be solved" trivial; trivial
  trivial

example : Nat → Nat → True := by
  success_if_fail_with_msg "No goals to be solved"
    intro _ _
    trivial
    trivial
  intros; trivial

/--
info: Update with tactic error message: "No goals to be solved"
---
error: tactic '
  intro _ _
  trivial
  trivial' failed, but got different error message:

No goals to be solved
-/
#guard_msgs in
example : Nat → Nat → True := by
  success_if_fail_with_msg "No goals"
    intro _ _
    trivial
    trivial
  intros; trivial

def err (t : Bool) := if t then
  "Invalid rewrite argument: Expected an equality or iff proof or definition name, but `Nat.le_succ n` is a proof of
  n ≤ n.succ"
  else
    "not that message
⊢ True"

set_option linter.unusedVariables false in
example (n : Nat) : True := by
  success_if_fail_with_msg (err true) rw [Nat.le_succ n]
  trivial

example : True := by
  success_if_fail_with_msg (err false) fail "not that message"
  trivial

/- In the following, we use `success_if_fail_with_msg` to write tests for
`success_if_fail_with_msg`, since the inner one should fail with a certain message. -/

example : True := by
  success_if_fail_with_msg "tactic 'trivial' succeeded, but was expected to fail"
    success_if_fail_with_msg "message" trivial
  trivial

def err₂ := "tactic 'fail \"different message!\"' failed, but got different error message:

different message!
⊢ True"

example : True := by
  success_if_fail_with_msg err₂
    success_if_fail_with_msg "message" fail "different message!"
  trivial

open Lean Meta Mathlib Tactic

def alwaysFails : MetaM Unit := do throwError "I failed!"

def doesntFail : MetaM Unit := do
  try successIfFailWithMessage "I failed!" alwaysFails
  catch _ => throwError "I *really* failed."

#guard_msgs in
#eval doesntFail
