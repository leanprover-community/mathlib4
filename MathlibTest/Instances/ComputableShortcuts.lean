/-
This test must import everything to make the noncomputable instances which we don't want available.
-/
import Mathlib

section Real

/-- info: Real.ofCauchy (sorry /- 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, ... -/) -/
#guard_msgs in
#eval LinearMap.mul ℝ ℝ 2 3

/-- info: Real.ofCauchy (sorry /- -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, ... -/) -/
#guard_msgs in
#eval LinearEquiv.neg ℝ (2 : ℝ)

end Real

section Complex

/--
info: Real.ofCauchy (sorry /- 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I
-/
#guard_msgs in
#eval LinearMap.mul ℂ ℂ 2 3

/--
info: Real.ofCauchy (sorry /- -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I
-/
#guard_msgs in
#eval LinearEquiv.neg ℂ (2 : ℂ)

end Complex
