import Mathlib.Tactic.Says
import Aesop

-- removing changes to the `simp` set after this test was created
attribute [-simp] Nat.add_left_cancel_iff Nat.add_right_cancel_iff

set_option autoImplicit true
/--
info: Try this:
  [apply] (show_term exact 37) says exact 37
-/
#guard_msgs in
example : Nat := by
  (show_term exact 37) says

-- Note that this implicitly tests that we have turned off `linter.unreachableTactic`.
example : Nat := by
  (show_term exact 37) says exact 37

/--
info: Try this:
  [apply] simp? says simp only [List.length_append]
-/
#guard_msgs in
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says

example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says simp only [List.length_append]

/-- error: Tactic `have := 0` did not produce a 'Try this:' suggestion. -/
#guard_msgs in
example : true := by
  have := 0 says

/--
error: Tactic `(run_tac
    do
      Lean.logInfo "hi!")` did not produce a 'Try this:' suggestion.
-/
#guard_msgs in
example : true := by
  (run_tac do Lean.logInfo "hi!") says

-- Check that `says` does not reverify the right-hand-side.
set_option says.no_verify_in_CI true in
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says skip
  simp

-- Check that with `says.verify` `says` will reverify that the left-hand-side constructs
-- the right-hand-side.
set_option says.verify true in
/--
error: Tactic `simp?` produced `simp only [List.length_append]`,
but was expecting it to produce `simp only []`!

You can reproduce this error locally using `set_option says.verify true`.
-/
#guard_msgs in
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says simp only []

set_option linter.unreachableTactic false
set_option linter.unusedTactic false in
-- Now we check that `says` does not consume following tactics unless they are indented.
/-- error: Tactic `simp` did not produce a 'Try this:' suggestion. -/
#guard_msgs in
example : True := by
  simp says
  trivial

set_option says.verify true in
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says simp only [List.length_append]
  -- This is a comment to test that `says` ignores following comments.

set_option says.no_verify_in_CI true in
example : True := by
  simp says
    trivial

set_option says.verify true in
/-- error: Tactic `simp` did not produce a 'Try this:' suggestion. -/
#guard_msgs in
example : True := by
  simp says
    trivial

-- Check that if the CI environment variable is set, we reverify all `says` statements.
example : True := by
  fail_if_success
    run_tac do guard (← IO.getEnv "CI").isSome
    simp says trivial
  trivial

-- Check that verification works even with multi-line suggestions, as produced by aesop
def P : Prop := True
def Q : Prop := True
@[simp]
def very_long_lemma_name_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : Q → P := fun _ => trivial
@[simp]
def very_long_lemma_name_bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb : Q := trivial
/--
info: Try this:
  [apply] aesop? says
    simp_all only [very_long_lemma_name_bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,
      very_long_lemma_name_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa]
-/
#guard_msgs in
example : P := by
  aesop? says
