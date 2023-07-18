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
error: Tactic `have := 0` did not produce any message.
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
