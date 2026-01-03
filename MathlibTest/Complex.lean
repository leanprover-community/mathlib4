import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DualNumber

open DualNumber

/--
info: Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I
-/
#guard_msgs in
#eval (0 : ℂ)

/--
info: Real.mk (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/) + Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I
-/
#guard_msgs in
#eval (1 : ℂ)

/--
info: Real.mk (sorry /- 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, ... -/) + Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I
-/
#guard_msgs in
#eval (4 : ℂ)

/--
info: Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.mk (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/)*I
-/
#guard_msgs in
#eval (Complex.I : ℂ)

/--
info: Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I + (Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.mk (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I)*ε
-/
#guard_msgs in
#eval (0 : ℂ[ε])
