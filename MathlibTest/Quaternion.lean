import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

open Quaternion
/--
info: { re := 0, imI := 0, imJ := 0, imK := 0 }
-/
#guard_msgs in
#eval (0 : ℍ[ℚ])

/--
info: { re := 1, imI := 0, imJ := 0, imK := 0 }
-/
#guard_msgs in
#eval (1 : ℍ[ℚ])

/--
info: { re := 4, imI := 0, imJ := 0, imK := 0 }
-/
#guard_msgs in
#eval (4 : ℍ[ℚ])

/--
info: { re := Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/), imI := Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/), imJ := Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/), imK := Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) }
-/
#guard_msgs in
#eval (⟨0, 0, 0, 0⟩ : ℍ[ℝ])

/--
info: { re := Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/), imI := Real.ofCauchy (sorry /- 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, ... -/), imJ := Real.ofCauchy (sorry /- 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, ... -/), imK := Real.ofCauchy (sorry /- 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, ... -/) }
-/
#guard_msgs in
#eval (⟨1, 2, 3, 4⟩ : ℍ[ℝ])

/--
info: { re := ⟨0, 0⟩, imI := ⟨0, 0⟩, imJ := ⟨0, 0⟩, imK := ⟨0, 0⟩ }
-/
#guard_msgs in
#eval (0 : ℍ[GaussianInt])
