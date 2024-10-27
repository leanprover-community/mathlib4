import Mathlib.Tactic.Observe
/-- info: Try this: have h : x + y = y + x := Nat.add_comm x y -/
#guard_msgs in
example (x y : Nat) : True := by
  observe? h : x + y = y + x
  guard_hyp h : x + y = y + x
  trivial
