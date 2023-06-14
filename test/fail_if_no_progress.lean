import Mathlib.Tactic.FailIfNoProgress

section success

example : 1 = 1 := by fail_if_no_progress rfl
example (h : 1 = 1) : True := by
  fail_if_no_progress simp at h
  trivial

end success

section failure

example (x : Bool) (h : x = true) : x = true := by
  fail_if_success
    fail_if_no_progress simp
  exact h


example (x : Bool) (h : x = true) : True := by
  fail_if_success
    fail_if_no_progress simp at h
  trivial

end failure
