import Mathlib.NumberTheory.Padics.PadicVal

/--
info: 100000
-/
#guard_msgs in
/- Previously this would hang -/
#eval padicValNat 2 (2 ^ 100000)
