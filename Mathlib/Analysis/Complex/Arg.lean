/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Rays in the complex numbers

This file links the definition `SameRay ℝ x y` with the equality of arguments of complex numbers,
the usual way this is considered.

## Main statements

* `Complex.sameRay_iff` : Two complex numbers are on the same ray iff one of them is zero, or they
  have the same argument.
* `Complex.abs_add_eq/Complex.abs_sub_eq`: If two nonzero complex numbers have the same argument,
  then the triangle inequality is an equality.
* `Complex.sameRay_of_mul_of_real_pos`, `Complex.inv_norm_smul_eq_of_mul_of_real_pos`,
  `Complex.aligned_of_mul_of_real_pos`: positive real scaling preserves `SameRay` and unit phase.
  See also `SameRay.inv_norm_smul_eq` in `Mathlib/Analysis/Normed/Module/Ray.lean`.

-/

public section


variable {x y : ℂ}

namespace Complex

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
theorem sameRay_iff : SameRay ℝ x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp
  simp only [hx, hy, sameRay_iff_norm_smul_eq, arg_eq_arg_iff hx hy]
  simp [field, hx, mul_comm, eq_comm]

theorem sameRay_iff_arg_div_eq_zero : SameRay ℝ x y ↔ arg (x / y) = 0 := by
  rw [← Real.Angle.toReal_zero, ← arg_coe_angle_eq_iff_eq_toReal, sameRay_iff]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  simp [hx, hy, arg_div_coe_angle, sub_eq_zero]

theorem norm_add_eq_iff : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  sameRay_iff_norm_add.symm.trans sameRay_iff

theorem norm_sub_eq_iff : ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  sameRay_iff_norm_sub.symm.trans sameRay_iff

theorem sameRay_of_arg_eq (h : x.arg = y.arg) : SameRay ℝ x y :=
  sameRay_iff.mpr <| Or.inr <| Or.inr h

theorem norm_add_eq (h : x.arg = y.arg) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
  (sameRay_of_arg_eq h).norm_add

theorem norm_sub_eq (h : x.arg = y.arg) : ‖x - y‖ = ‖‖x‖ - ‖y‖‖ :=
  (sameRay_of_arg_eq h).norm_sub

variable {z w : ℂ} {c lam : ℝ}

/-- `z / ‖z‖` agrees with the real scalar action of `‖z‖⁻¹`. -/
lemma div_norm_eq_inv_norm_smul (hz : z ≠ 0) : z / (‖z‖ : ℂ) = (‖z‖)⁻¹ • z := by
  simp [div_eq_inv_mul, ofReal_inv, real_smul, mul_comm]

/-- If `z = c * w` with `c > 0`, then `z` and `w` lie on the same closed ray. -/
lemma sameRay_of_mul_of_real_pos (hc_pos : 0 < c) (h : z = (c : ℂ) * w) : SameRay ℝ z w := by
  rw [h]
  exact SameRay.sameRay_pos_smul_left w hc_pos

/-- If `z = c * w` with `c > 0` and both are nonzero, their unit vectors agree. -/
lemma inv_norm_smul_eq_of_mul_of_real_pos (hc_pos : 0 < c) (h : z = (c : ℂ) * w) (hz : z ≠ 0)
    (hw : w ≠ 0) : (‖z‖)⁻¹ • z = (‖w‖)⁻¹ • w :=
  SameRay.inv_norm_smul_eq hz hw (sameRay_of_mul_of_real_pos hc_pos h)

/-- If `z = c * w` with `c > 0` and both are nonzero, they have the same normalized phase. -/
lemma aligned_of_mul_of_real_pos (hc_pos : 0 < c) (h : z = (c : ℂ) * w) (hz : z ≠ 0)
    (hw : w ≠ 0) : z / (‖z‖ : ℂ) = w / (‖w‖ : ℂ) := by
  rw [div_norm_eq_inv_norm_smul hz, div_norm_eq_inv_norm_smul hw,
    inv_norm_smul_eq_of_mul_of_real_pos hc_pos h hz hw]

end Complex
