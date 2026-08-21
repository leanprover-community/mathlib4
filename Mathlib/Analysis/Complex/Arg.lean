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
* `Complex.div_ofReal_eq_inv_smul`, `Complex.div_norm_eq_inv_norm_smul`: division by a real
  scalar agrees with inverse scalar multiplication.
* `Complex.sameRay_iff_aligned`: two nonzero complex numbers are on the same ray iff they have
  the same phase.
* `Complex.exists_nonneg_mul_of_sameRay`: the `*` form of `SameRay.exists_nonneg_right`.
* `Complex.sameRay_ofReal_mul`, `Complex.aligned_of_mul_of_real_pos`: nonnegative real scaling
  preserves `SameRay`, and positive real scaling preserves the phase.
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

variable {z w : ℂ} {c : ℝ}

/-- Division by a real scalar agrees with inverse real scalar multiplication. -/
lemma div_ofReal_eq_inv_smul (r : ℝ) (z : ℂ) : z / (r : ℂ) = r⁻¹ • z := by
  simp [div_eq_inv_mul, ofReal_inv, real_smul, mul_comm]

/-- `z / ‖z‖` agrees with the real scalar action of `‖z‖⁻¹`. -/
lemma div_norm_eq_inv_norm_smul : z / (‖z‖ : ℂ) = (‖z‖)⁻¹ • z :=
  div_ofReal_eq_inv_smul (‖z‖) z

/-- Two nonzero complex numbers lie on the same closed ray iff they have the same phase. -/
lemma sameRay_iff_aligned (hz : z ≠ 0) (hw : w ≠ 0) :
    SameRay ℝ z w ↔ z / (‖z‖ : ℂ) = w / (‖w‖ : ℂ) := by
  rw [div_norm_eq_inv_norm_smul, div_norm_eq_inv_norm_smul]
  exact sameRay_iff_inv_norm_smul_eq_of_ne hz hw

alias ⟨aligned_of_sameRay, _⟩ := sameRay_iff_aligned

/-- A nonnegative real multiple of `w` lies on the same closed ray as `w`. -/
lemma sameRay_ofReal_mul (hc : 0 ≤ c) : SameRay ℝ ((c : ℂ) * w) w := by
  rw [← real_smul]
  exact SameRay.sameRay_nonneg_smul_left w hc

/-- A complex number on the same ray as a nonzero `w` is a nonnegative real multiple of `w`. -/
lemma exists_nonneg_mul_of_sameRay (h : SameRay ℝ z w) (hw : w ≠ 0) :
    ∃ k : ℝ, 0 ≤ k ∧ z = (k : ℂ) * w := by
  obtain ⟨k, hk, hz⟩ := h.exists_nonneg_right hw
  exact ⟨k, hk, by rwa [real_smul] at hz⟩

/-- A positive real multiple of a nonzero `w` has the same phase as `w`. -/
lemma aligned_of_mul_of_real_pos (hc_pos : 0 < c) (hw : w ≠ 0) :
    ((c : ℂ) * w) / (‖(c : ℂ) * w‖ : ℂ) = w / (‖w‖ : ℂ) :=
  aligned_of_sameRay (mul_ne_zero (ofReal_ne_zero.2 hc_pos.ne') hw) hw
    (sameRay_ofReal_mul hc_pos.le)

end Complex
