import Mathlib.Algebra.DualNumber

open DualNumber

/-- info: true -/
#guard_msgs in
#eval toString (repr (0 : ℕ[ε])) = "0 + 0*ε"


/-- info: true -/
#guard_msgs in
#eval toString (repr (2 : ℕ[ε])) = "2 + 0*ε"


/-- info: true -/
#guard_msgs in
#eval toString (repr (2 + 4 : ℕ[ε])) = "6 + 0*ε"


/-- info: true -/
#guard_msgs in
#eval toString (repr (2 : (ℕ[ε])[ε])) = "2 + 0*ε + (0 + 0*ε)*ε"
