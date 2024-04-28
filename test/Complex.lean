import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DualNumber

open DualNumber

/-- info: true -/
#guard_msgs in
#eval toString (repr (0 : ℂ)) = "Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I"

/-- info: true -/
#guard_msgs in
#eval toString (repr (1 : ℂ)) = "Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I"

/-- info: true -/
#guard_msgs in
#eval toString (repr (4 : ℂ)) = "Real.ofCauchy (sorry /- 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I"

/-- info: true -/
#guard_msgs in
#eval toString (repr (Complex.I : ℂ)) = "Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/)*I"

/-- info: true -/
#guard_msgs in
#eval toString (repr (0 : ℂ[ε])) = "Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I + (Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I)*ε"
