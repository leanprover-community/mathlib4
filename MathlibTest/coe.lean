import Mathlib.Tactic.Coe

example : { n : Nat // n > 3 } → Nat := (↑)
