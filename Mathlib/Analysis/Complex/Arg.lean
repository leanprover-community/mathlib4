/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Module.Normalize
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
* `Complex.exists_nonneg_mul_of_sameRay`: the `*` form of `SameRay.exists_nonneg_right`.
* `Complex.sameRay_ofReal_mul`, `Complex.normalize_ofReal_mul`: nonnegative real scaling
  preserves `SameRay`, and positive real scaling preserves the phase.
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

/-- A nonnegative real multiple of `w` lies on the same closed ray as `w`. -/
lemma sameRay_ofReal_mul (hc : 0 ≤ c) : SameRay ℝ ((c : ℂ) * w) w := by
  rw [← real_smul]
  exact SameRay.sameRay_nonneg_smul_left w hc

/-- A complex number on the same ray as a nonzero `w` is a nonnegative real multiple of `w`. -/
lemma exists_nonneg_mul_of_sameRay (h : SameRay ℝ z w) (hw : w ≠ 0) :
    ∃ k : ℝ, 0 ≤ k ∧ z = (k : ℂ) * w := by
  obtain ⟨k, hk, hz⟩ := h.exists_nonneg_right hw
  exact ⟨k, hk, by rwa [real_smul] at hz⟩

/-- A positive real multiple of `w` has the same phase as `w`. -/
lemma normalize_ofReal_mul (hc : 0 < c) (w : ℂ) :
    NormedSpace.normalize ((c : ℂ) * w) = NormedSpace.normalize w := by
  rw [← real_smul, NormedSpace.normalize_smul_of_pos hc]

end Complex
