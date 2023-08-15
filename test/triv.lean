import Mathlib.Tactic.Basic

example : True := by
  triv

example : 2 + 2 = 4 := by
  triv

-- Verify the difference in behaviour between `triv` and `trivial`.
example (P : Prop) (h1 : P) (h2 : ¬ P) : False := by
  fail_if_success triv -- fails
  trivial -- succeeds
