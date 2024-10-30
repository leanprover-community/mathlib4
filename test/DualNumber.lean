import Mathlib.Algebra.DualNumber

open DualNumber

/-- info: 0 + 0*ε -/
#guard_msgs in
#eval (0 : ℕ[ε])

/-- info: 2 + 0*ε -/
#guard_msgs in
#eval (2 : ℕ[ε])

/-- info: 6 + 0*ε -/
#guard_msgs in
#eval (2 + 4 : ℕ[ε])

/-- info: 2 + 0*ε + (0 + 0*ε)*ε -/
#guard_msgs in
#eval (2 : (ℕ[ε])[ε])
