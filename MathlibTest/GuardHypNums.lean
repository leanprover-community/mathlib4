import Mathlib.Tactic.GuardHypNums

set_option linter.unusedTactic false

example (a b c : Nat) (_ : a = b) (_ : c = 3) : true := by
  guard_hyp_nums 6
  trivial

example : true := by
  guard_hyp_nums 1
  trivial
