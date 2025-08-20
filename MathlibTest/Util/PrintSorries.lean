import Mathlib.Util.PrintSorries

/--
error: unsolved goals
this : True
⊢ True
-/
#guard_msgs in
theorem foo : True := by
  have : True :=
  sorry

/--
info: foo has sorry
foo has sorry (from error)
-/
#guard_msgs in
#print sorries foo
