import Mathlib.Tactic.Says
import Mathlib.Tactic.RunCmd

/--
info: Try this: (show_term exact 37) says exact 37
-/
#guard_msgs in
example : Nat := by
  (show_term exact 37) says

-- Note that this implicitly tests that we have turned off `linter.unreachableTactic`.
example : Nat := by
  (show_term exact 37) says exact 37

/--
info: Try this: simp? says simp only [List.length_append]
-/
#guard_msgs in
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says

example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says simp only [List.length_append]

/--
error: Tactic `have := 0` did not produce any messages.
-/
#guard_msgs in
example : true := by
  have := 0 says

/--
error: Tactic output did not begin with 'Try this:': hi!
-/
#guard_msgs in
example : true := by
  (run_tac do Lean.logInfo "hi!") says

-- Check that with the default settings `says` does not reverify the right-hand-side.
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says simp only []
  simp

-- Now that with `says.verify` `says` will reverify that the left-hand-side constructs
-- the right-hand-side.
set_option says.verify true in
/--
error: Tactic `simp?` produced `simp only [List.length_append]`,
but was expecting it to produce `simp only []`!
-/
#guard_msgs in
example (x y : List α) : (x ++ y).length = x.length + y.length := by
  simp? says simp only []

/- Now we check that `says` does not consume following tactics unless they are indented. -/
set_option linter.unreachableTactic false
/--
error: Tactic `simp` did not produce any messages.
-/
#guard_msgs in
example : True := by
  simp says
  trivial

example : True := by
  simp says
    trivial

set_option says.verify true in
/--
error: Tactic `simp` did not produce any messages.
-/
#guard_msgs in
example : True := by
  simp says
    trivial
