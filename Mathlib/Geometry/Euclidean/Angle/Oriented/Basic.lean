/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces.

## Main definitions

* `Orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

## Implementation notes

The definitions here use the `Real.angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/


noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}
variable [NormedAddCommGroup V] [NormedAddCommGroup V']
variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']
variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "ω" => o.areaForm

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0.
See `InnerProductGeometry.angle` for the corresponding unoriented angle definition. -/
def oangle (x y : V) : Real.Angle :=
  Complex.arg (o.kahler x y)

/-- Oriented angles are continuous when the vectors involved are nonzero. -/
@[fun_prop]
theorem continuousAt_oangle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
    ContinuousAt (fun y : V × V => o.oangle y.1 y.2) x := by
  refine (Complex.continuousAt_arg_coe_angle ?_).comp ?_
  · exact o.kahler_ne_zero hx1 hx2
  exact ((continuous_ofReal.comp continuous_inner).add
    ((continuous_ofReal.comp o.areaForm'.continuous₂).mul continuous_const)).continuousAt

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp]
theorem oangle_zero_left (x : V) : o.oangle 0 x = 0 := by simp [oangle]

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp]
theorem oangle_zero_right (x : V) : o.oangle x 0 = 0 := by simp [oangle]

/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp]
theorem oangle_self (x : V) : o.oangle x x = 0 := by
  rw [oangle, kahler_apply_self, ← ofReal_pow]
  convert QuotientAddGroup.mk_zero (AddSubgroup.zmultiples (2 * π))
  apply arg_ofReal_of_nonneg
  positivity

/-- If the angle between two vectors is nonzero, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y ≠ 0) : x ≠ 0 := by
  rintro rfl; simp at h

/-- If the angle between two vectors is nonzero, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y ≠ 0) : y ≠ 0 := by
  rintro rfl; simp at h

/-- If the angle between two vectors is nonzero, the vectors are not equal. -/
theorem ne_of_oangle_ne_zero {x y : V} (h : o.oangle x y ≠ 0) : x ≠ y := by
  rintro rfl; simp at h

/-- If the angle between two vectors is `π`, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π`, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π`, the vectors are not equal. -/
theorem ne_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x ≠ y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π / 2`, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π / 2`, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π / 2`, the vectors are not equal. -/
theorem ne_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) : x ≠ y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `-π / 2`, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `-π / 2`, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `-π / 2`, the vectors are not equal. -/
theorem ne_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) : x ≠ y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the sign of the angle between two vectors is nonzero, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign ≠ 0) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between two vectors is nonzero, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign ≠ 0) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between two vectors is nonzero, the vectors are not equal. -/
theorem ne_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign ≠ 0) : x ≠ y :=
  o.ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between two vectors is positive, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is positive, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is positive, the vectors are not equal. -/
theorem ne_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x ≠ y :=
  o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is negative, the first vector is nonzero. -/
theorem left_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is negative, the second vector is nonzero. -/
theorem right_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is negative, the vectors are not equal. -/
theorem ne_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x ≠ y :=
  o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
theorem oangle_rev (x y : V) : o.oangle y x = -o.oangle x y := by
  simp only [oangle, o.kahler_swap y x, Complex.arg_conj_coe_angle]

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp]
theorem oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0 := by
  simp [o.oangle_rev y x]

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
theorem oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle (-x) y = o.oangle x y + π := by
  simp only [oangle, map_neg]
  convert Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
theorem oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x (-y) = o.oangle x y + π := by
  simp only [oangle, map_neg]
  convert Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp]
theorem two_zsmul_oangle_neg_left (x y : V) :
    (2 : ℤ) • o.oangle (-x) y = (2 : ℤ) • o.oangle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_left hx hy]

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp]
theorem two_zsmul_oangle_neg_right (x y : V) :
    (2 : ℤ) • o.oangle x (-y) = (2 : ℤ) • o.oangle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_right hx hy]

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp]
theorem oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y := by simp [oangle]

/-- Negating the first vector produces the same angle as negating the second vector. -/
theorem oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y) := by
  rw [← neg_neg y, oangle_neg_neg, neg_neg]

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp]
theorem oangle_neg_self_left {x : V} (hx : x ≠ 0) : o.oangle (-x) x = π := by
  simp [oangle_neg_left, hx]

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp]
theorem oangle_neg_self_right {x : V} (hx : x ≠ 0) : o.oangle x (-x) = π := by
  simp [oangle_neg_right, hx]

/-- Twice the angle between the negation of a vector and that vector is 0. -/
theorem two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • o.oangle (-x) x = 0 := by
  by_cases hx : x = 0 <;> simp [hx]

/-- Twice the angle between a vector and its negation is 0. -/
theorem two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • o.oangle x (-x) = 0 := by
  by_cases hx : x = 0 <;> simp [hx]

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp]
theorem oangle_add_oangle_rev_neg_left (x y : V) : o.oangle (-x) y + o.oangle (-y) x = 0 := by
  rw [oangle_neg_left_eq_neg_right, oangle_rev, neg_add_cancel]

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp]
theorem oangle_add_oangle_rev_neg_right (x y : V) : o.oangle x (-y) + o.oangle y (-x) = 0 := by
  rw [o.oangle_rev (-x), oangle_neg_left_eq_neg_right, add_neg_cancel]

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
theorem oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
    o.oangle (r • x) y = o.oangle x y := by simp [oangle, Complex.arg_real_mul _ hr]

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
theorem oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
    o.oangle x (r • y) = o.oangle x y := by simp [oangle, Complex.arg_real_mul _ hr]

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
theorem oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
    o.oangle (r • x) y = o.oangle (-x) y := by
  rw [← neg_neg r, neg_smul, ← smul_neg, o.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
theorem oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
    o.oangle x (r • y) = o.oangle x (-y) := by
  rw [← neg_neg r, neg_smul, ← smul_neg, o.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp]
theorem oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : o.oangle (r • x) x = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp]
theorem oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : o.oangle x (r • x) = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp]
theorem oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    o.oangle (r₁ • x) (r₂ • x) = 0 := by
  rcases hr₁.lt_or_eq with (h | h)
  · simp [h, hr₂]
  · simp [h.symm]

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
theorem two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • o.oangle (r • x) y = (2 : ℤ) • o.oangle x y := by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
theorem two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • o.oangle x (r • y) = (2 : ℤ) • o.oangle x y := by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} : (2 : ℤ) • o.oangle (r • x) x = 0 := by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} : (2 : ℤ) • o.oangle x (r • x) = 0 := by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp]
theorem two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} :
    (2 : ℤ) • o.oangle (r₁ • x) (r₂ • x) = 0 := by by_cases h : r₁ = 0 <;> simp [h]

/-- If the spans of two vectors are equal, twice angles with those vectors on the left are
equal. -/
theorem two_zsmul_oangle_left_of_span_eq {x y : V} (z : V) (h : (ℝ ∙ x) = ℝ ∙ y) :
    (2 : ℤ) • o.oangle x z = (2 : ℤ) • o.oangle y z := by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_left_of_ne_zero _ _ (Units.ne_zero _)).symm

/-- If the spans of two vectors are equal, twice angles with those vectors on the right are
equal. -/
theorem two_zsmul_oangle_right_of_span_eq (x : V) {y z : V} (h : (ℝ ∙ y) = ℝ ∙ z) :
    (2 : ℤ) • o.oangle x y = (2 : ℤ) • o.oangle x z := by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_right_of_ne_zero _ _ (Units.ne_zero _)).symm

/-- If the spans of two pairs of vectors are equal, twice angles between those vectors are
equal. -/
theorem two_zsmul_oangle_of_span_eq_of_span_eq {w x y z : V} (hwx : (ℝ ∙ w) = ℝ ∙ x)
    (hyz : (ℝ ∙ y) = ℝ ∙ z) : (2 : ℤ) • o.oangle w y = (2 : ℤ) • o.oangle x z := by
  rw [o.two_zsmul_oangle_left_of_span_eq y hwx, o.two_zsmul_oangle_right_of_span_eq x hyz]

/-- The oriented angle between two vectors is zero if and only if the angle with the vectors
swapped is zero. -/
theorem oangle_eq_zero_iff_oangle_rev_eq_zero {x y : V} : o.oangle x y = 0 ↔ o.oangle y x = 0 := by
  rw [oangle_rev, neg_eq_zero]

/-- The oriented angle between two vectors is zero if and only if they are on the same ray. -/
theorem oangle_eq_zero_iff_sameRay {x y : V} : o.oangle x y = 0 ↔ SameRay ℝ x y := by
  rw [oangle, kahler_apply_apply, Complex.arg_coe_angle_eq_iff_eq_toReal, Real.Angle.toReal_zero,
    Complex.arg_eq_zero_iff]
  simpa using o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay x y

/-- The oriented angle between two vectors is `π` if and only if the angle with the vectors
swapped is `π`. -/
theorem oangle_eq_pi_iff_oangle_rev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle y x = π := by
  rw [oangle_rev, neg_eq_iff_eq_neg, Real.Angle.neg_coe_pi]

/-- The oriented angle between two vectors is `π` if and only they are nonzero and the first is
on the same ray as the negation of the second. -/
theorem oangle_eq_pi_iff_sameRay_neg {x y : V} :
    o.oangle x y = π ↔ x ≠ 0 ∧ y ≠ 0 ∧ SameRay ℝ x (-y) := by
  rw [← o.oangle_eq_zero_iff_sameRay]
  constructor
  · intro h
    by_cases hx : x = 0; · simp [hx, Real.Angle.pi_ne_zero.symm] at h
    by_cases hy : y = 0; · simp [hy, Real.Angle.pi_ne_zero.symm] at h
    refine ⟨hx, hy, ?_⟩
    rw [o.oangle_neg_right hx hy, h, Real.Angle.coe_pi_add_coe_pi]
  · rintro ⟨hx, hy, h⟩
    rwa [o.oangle_neg_right hx hy, ← Real.Angle.sub_coe_pi_eq_add_coe_pi, sub_eq_zero] at h

/-- The oriented angle between two vectors is zero or `π` if and only if those two vectors are
not linearly independent. -/
theorem oangle_eq_zero_or_eq_pi_iff_not_linearIndependent {x y : V} :
    o.oangle x y = 0 ∨ o.oangle x y = π ↔ ¬LinearIndependent ℝ ![x, y] := by
  rw [oangle_eq_zero_iff_sameRay, oangle_eq_pi_iff_sameRay_neg,
    sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent]

/-- The oriented angle between two vectors is zero or `π` if and only if the first vector is zero
or the second is a multiple of the first. -/
theorem oangle_eq_zero_or_eq_pi_iff_right_eq_smul {x y : V} :
    o.oangle x y = 0 ∨ o.oangle x y = π ↔ x = 0 ∨ ∃ r : ℝ, y = r • x := by
  rw [oangle_eq_zero_iff_sameRay, oangle_eq_pi_iff_sameRay_neg]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | ⟨-, -, h⟩)
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, rfl⟩ := h.exists_nonneg_left hx
      exact Or.inr ⟨r, rfl⟩
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, hy⟩ := h.exists_nonneg_left hx
      refine Or.inr ⟨-r, ?_⟩
      simp [hy]
  · rcases h with (rfl | ⟨r, rfl⟩); · simp
    by_cases hx : x = 0; · simp [hx]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · rw [← neg_smul]
      exact Or.inr ⟨hx, smul_ne_zero hr.ne hx,
        SameRay.sameRay_pos_smul_right x (Left.neg_pos_iff.2 hr)⟩
    · simp [hr]
    · exact Or.inl (SameRay.sameRay_pos_smul_right x hr)

/-- The oriented angle between two vectors is not zero or `π` if and only if those two vectors
are linearly independent. -/
theorem oangle_ne_zero_and_ne_pi_iff_linearIndependent {x y : V} :
    o.oangle x y ≠ 0 ∧ o.oangle x y ≠ π ↔ LinearIndependent ℝ ![x, y] := by
  rw [← not_or, ← not_iff_not, Classical.not_not,
    oangle_eq_zero_or_eq_pi_iff_not_linearIndependent]

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
theorem eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0 := by
  rw [oangle_eq_zero_iff_sameRay]
  constructor
  · rintro rfl
    simp; rfl
  · rcases eq_or_ne y 0 with (rfl | hy)
    · simp
    rintro ⟨h₁, h₂⟩
    obtain ⟨r, hr, rfl⟩ := h₂.exists_nonneg_right hy
    have : ‖y‖ ≠ 0 := by simpa using hy
    obtain rfl : r = 1 := by
      apply mul_right_cancel₀ this
      simpa [norm_smul, abs_of_nonneg hr] using h₁
    simp

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
theorem eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : x = y ↔ o.oangle x y = 0 :=
  ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2, fun ha =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
theorem eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y ↔ ‖x‖ = ‖y‖ :=
  ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1, fun hn =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp]
theorem oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x y + o.oangle y z = o.oangle x z := by
  simp_rw [oangle]
  rw [← Complex.arg_mul_coe_angle, o.kahler_mul y x z]
  · congr 1
    exact mod_cast Complex.arg_real_mul _ (by positivity : 0 < ‖y‖ ^ 2)
  · exact o.kahler_ne_zero hx hy
  · exact o.kahler_ne_zero hy hz

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp]
theorem oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle y z + o.oangle x y = o.oangle x z := by rw [add_comm, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp]
theorem oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x z - o.oangle x y = o.oangle y z := by
  rw [sub_eq_iff_eq_add, o.oangle_add_swap hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp]
theorem oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x z - o.oangle y z = o.oangle x y := by rw [sub_eq_iff_eq_add, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
theorem oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x y + o.oangle y z + o.oangle z x = 0 := by simp [hx, hy, hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
theorem oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π := by
  rw [o.oangle_neg_left hx hy, o.oangle_neg_left hy hz, o.oangle_neg_left hz hx,
    show o.oangle x y + π + (o.oangle y z + π) + (o.oangle z x + π) =
      o.oangle x y + o.oangle y z + o.oangle z x + (π + π + π : Real.Angle) by abel,
    o.oangle_add_cyc3 hx hy hz, Real.Angle.coe_pi_add_coe_pi, zero_add, zero_add]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
theorem oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π := by
  simp_rw [← oangle_neg_left_eq_neg_right, o.oangle_add_cyc3_neg_left hx hy hz]

/-- Pons asinorum, oriented vector angle form. -/
theorem oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    o.oangle x (x - y) = o.oangle (y - x) y := by simp [oangle, h]

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ‖x‖ = ‖y‖) :
    o.oangle y x = π - (2 : ℤ) • o.oangle (y - x) y := by
  rw [two_zsmul]
  nth_rw 1 [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
  rw [eq_sub_iff_add_eq, ← oangle_neg_neg, ← add_assoc]
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at h
    exact hn h
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy)
  convert o.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm) using 1
  simp

/-- The angle between two vectors, with respect to an orientation given by `Orientation.map`
with a linear isometric equivalence, equals the angle between those two vectors, transformed by
the inverse of that equivalence, with respect to the original orientation. -/
@[simp]
theorem oangle_map (x y : V') (f : V ≃ₗᵢ[ℝ] V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).oangle x y = o.oangle (f.symm x) (f.symm y) := by
  simp [oangle, o.kahler_map]

@[simp]
protected theorem _root_.Complex.oangle (w z : ℂ) :
    Complex.orientation.oangle w z = Complex.arg (conj w * z) := by
  simp [oangle, mul_comm z]

/-- The oriented angle on an oriented real inner product space of dimension 2 can be evaluated in
terms of a complex-number representation of the space. -/
theorem oangle_map_complex (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : V) :
    o.oangle x y = Complex.arg (conj (f x) * f y) := by
  rw [← Complex.oangle, ← hf, o.oangle_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

/-- Negating the orientation negates the value of `oangle`. -/
theorem oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -o.oangle x y := by
  simp [oangle]

/-- The inner product of two vectors is the product of the norms and the cosine of the oriented
angle between the vectors. -/
theorem inner_eq_norm_mul_norm_mul_cos_oangle (x y : V) :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ * Real.Angle.cos (o.oangle x y) := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [oangle, Real.Angle.cos_coe, Complex.cos_arg, o.norm_kahler]
  · simp only [kahler_apply_apply, real_smul, add_re, ofReal_re, mul_re, I_re, ofReal_im]
    simp [field]
  · exact o.kahler_ne_zero hx hy

/-- The cosine of the oriented angle between two nonzero vectors is the inner product divided by
the product of the norms. -/
theorem cos_oangle_eq_inner_div_norm_mul_norm {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.Angle.cos (o.oangle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) := by
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle]
  field_simp

/-- The cosine of the oriented angle between two nonzero vectors equals that of the unoriented
angle. -/
theorem cos_oangle_eq_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.Angle.cos (o.oangle x y) = Real.cos (InnerProductGeometry.angle x y) := by
  rw [o.cos_oangle_eq_inner_div_norm_mul_norm hx hy, InnerProductGeometry.cos_angle]

/-- The oriented angle between two nonzero vectors is plus or minus the unoriented angle. -/
theorem oangle_eq_angle_or_eq_neg_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x y = InnerProductGeometry.angle x y ∨
      o.oangle x y = -InnerProductGeometry.angle x y :=
  Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 <| o.cos_oangle_eq_cos_angle hx hy

/-- The unoriented angle between two nonzero vectors is the absolute value of the oriented angle,
converted to a real. -/
theorem angle_eq_abs_oangle_toReal {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    InnerProductGeometry.angle x y = |(o.oangle x y).toReal| := by
  have h0 := InnerProductGeometry.angle_nonneg x y
  have hpi := InnerProductGeometry.angle_le_pi x y
  rcases o.oangle_eq_angle_or_eq_neg_angle hx hy with (h | h)
  · rw [h, eq_comm, Real.Angle.abs_toReal_coe_eq_self_iff]
    exact ⟨h0, hpi⟩
  · rw [h, eq_comm, Real.Angle.abs_toReal_neg_coe_eq_self_iff]
    exact ⟨h0, hpi⟩

/-- If the sign of the oriented angle between two vectors is zero, either one of the vectors is
zero or the unoriented angle is 0 or π. -/
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V}
    (h : (o.oangle x y).sign = 0) :
    x = 0 ∨ y = 0 ∨ InnerProductGeometry.angle x y = 0 ∨ InnerProductGeometry.angle x y = π := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.angle_eq_abs_oangle_toReal hx hy]
  rw [Real.Angle.sign_eq_zero_iff] at h
  rcases h with (h | h) <;> simp [h, Real.pi_pos.le]

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
theorem oangle_eq_of_angle_eq_of_sign_eq {w x y z : V}
    (h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z)
    (hs : (o.oangle w x).sign = (o.oangle y z).sign) : o.oangle w x = o.oangle y z := by
  by_cases h0 : (w = 0 ∨ x = 0) ∨ y = 0 ∨ z = 0
  · have hs' : (o.oangle w x).sign = 0 ∧ (o.oangle y z).sign = 0 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using hs.symm
      · simpa using hs.symm
      · simpa using hs
      · simpa using hs
    rcases hs' with ⟨hswx, hsyz⟩
    have h' : InnerProductGeometry.angle w x = π / 2 ∧ InnerProductGeometry.angle y z = π / 2 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using h.symm
      · simpa using h.symm
      · simpa using h
      · simpa using h
    rcases h' with ⟨hwx, hyz⟩
    have hpi : π / 2 ≠ π := by
      intro hpi
      rw [div_eq_iff, eq_comm, ← sub_eq_zero, mul_two, add_sub_cancel_right] at hpi
      · exact Real.pi_pos.ne.symm hpi
      · exact two_ne_zero
    have h0wx : w = 0 ∨ x = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hswx
      simpa [hwx, Real.pi_pos.ne.symm, hpi] using h0'
    have h0yz : y = 0 ∨ z = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hsyz
      simpa [hyz, Real.pi_pos.ne.symm, hpi] using h0'
    rcases h0wx with (h0wx | h0wx) <;> rcases h0yz with (h0yz | h0yz) <;> simp [h0wx, h0yz]
  · push_neg at h0
    rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq hs]
    rwa [o.angle_eq_abs_oangle_toReal h0.1.1 h0.1.2,
      o.angle_eq_abs_oangle_toReal h0.2.1 h0.2.2] at h

/-- If the signs of two oriented angles between nonzero vectors are equal, the oriented angles are
equal if and only if the unoriented angles are equal. -/
theorem angle_eq_iff_oangle_eq_of_sign_eq {w x y z : V} (hw : w ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hs : (o.oangle w x).sign = (o.oangle y z).sign) :
    InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔
    o.oangle w x = o.oangle y z := by
  refine ⟨fun h => o.oangle_eq_of_angle_eq_of_sign_eq h hs, fun h => ?_⟩
  rw [o.angle_eq_abs_oangle_toReal hw hx, o.angle_eq_abs_oangle_toReal hy hz, h]

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
negations of each other, then the oriented angles are negations of each other (even in degenerate
cases). -/
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg {w x y z : V}
    (h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z)
    (hs : (o.oangle w x).sign = -(o.oangle y z).sign) : o.oangle w x = -o.oangle y z := by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg, ← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm] at h
  exact o.oangle_eq_of_angle_eq_of_sign_eq h hs

/-- If the signs of two oriented angles between nonzero vectors are negations of each other, the
oriented angles are negations of each other if and only if the unoriented angles are equal. -/
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {w x y z : V} (hw : w ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) (hs : (o.oangle w x).sign = -(o.oangle y z).sign) :
    InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔
      o.oangle w x = -o.oangle y z := by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg, ← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm]
  exact o.angle_eq_iff_oangle_eq_of_sign_eq hw hx hz hy hs

/-- The oriented angle between two vectors equals the unoriented angle if the sign is positive. -/
theorem oangle_eq_angle_of_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) :
    o.oangle x y = InnerProductGeometry.angle x y := by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_right ?_
  intro hxy
  rw [hxy, Real.Angle.sign_neg, neg_eq_iff_eq_neg, ← SignType.neg_iff, ← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

/-- The oriented angle between two vectors equals minus the unoriented angle if the sign is
negative. -/
theorem oangle_eq_neg_angle_of_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) :
    o.oangle x y = -InnerProductGeometry.angle x y := by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_left ?_
  intro hxy
  rw [hxy, ← SignType.neg_iff, ← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

/-- The oriented angle between two nonzero vectors is zero if and only if the unoriented angle
is zero. -/
theorem oangle_eq_zero_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x y = 0 ↔ InnerProductGeometry.angle x y = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [o.angle_eq_abs_oangle_toReal hx hy]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

/-- The oriented angle between two vectors is `π` if and only if the unoriented angle is `π`. -/
theorem oangle_eq_pi_iff_angle_eq_pi {x y : V} :
    o.oangle x y = π ↔ InnerProductGeometry.angle x y = π := by
  by_cases hx : x = 0
  · simp [hx, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  by_cases hy : y = 0
  · simp [hy, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [o.angle_eq_abs_oangle_toReal hx hy, h]
    simp [Real.pi_pos.le]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

/-- One of two vectors is zero or the oriented angle between them is plus or minus `π / 2` if
and only if the inner product of those vectors is zero. -/
theorem eq_zero_or_oangle_eq_iff_inner_eq_zero {x y : V} :
    x = 0 ∨ y = 0 ∨ o.oangle x y = (π / 2 : ℝ) ∨ o.oangle x y = (-π / 2 : ℝ) ↔ ⟪x, y⟫ = 0 := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, or_iff_right hx, or_iff_right hy]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [o.angle_eq_abs_oangle_toReal hx hy, Real.Angle.abs_toReal_eq_pi_div_two_iff]
  · convert o.oangle_eq_angle_or_eq_neg_angle hx hy using 2 <;> rw [h]
    simp only [neg_div, Real.Angle.coe_neg]

/-- If the oriented angle between two vectors is `π / 2`, the inner product of those vectors
is zero. -/
theorem inner_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) :
    ⟪x, y⟫ = 0 :=
  o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 <| Or.inr <| Or.inr <| Or.inl h

/-- If the oriented angle between two vectors is `π / 2`, the inner product of those vectors
(reversed) is zero. -/
theorem inner_rev_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) :
    ⟪y, x⟫ = 0 := by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_pi_div_two h]

/-- If the oriented angle between two vectors is `-π / 2`, the inner product of those vectors
is zero. -/
theorem inner_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    ⟪x, y⟫ = 0 :=
  o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 <| Or.inr <| Or.inr <| Or.inr h

/-- If the oriented angle between two vectors is `-π / 2`, the inner product of those vectors
(reversed) is zero. -/
theorem inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    ⟪y, x⟫ = 0 := by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h]

/-- Negating the first vector passed to `oangle` negates the sign of the angle. -/
@[simp]
theorem oangle_sign_neg_left (x y : V) : (o.oangle (-x) y).sign = -(o.oangle x y).sign := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_left hx hy, Real.Angle.sign_add_pi]

/-- Negating the second vector passed to `oangle` negates the sign of the angle. -/
@[simp]
theorem oangle_sign_neg_right (x y : V) : (o.oangle x (-y)).sign = -(o.oangle x y).sign := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_right hx hy, Real.Angle.sign_add_pi]

/-- Multiplying the first vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp]
theorem oangle_sign_smul_left (x y : V) (r : ℝ) :
    (o.oangle (r • x) y).sign = SignType.sign r * (o.oangle x y).sign := by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

/-- Multiplying the second vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp]
theorem oangle_sign_smul_right (x y : V) (r : ℝ) :
    (o.oangle x (r • y)).sign = SignType.sign r * (o.oangle x y).sign := by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

/-- Auxiliary lemma for the proof of `oangle_sign_smul_add_right`; not intended to be used
outside of that proof. -/
theorem oangle_smul_add_right_eq_zero_or_eq_pi_iff {x y : V} (r : ℝ) :
    o.oangle x (r • x + y) = 0 ∨ o.oangle x (r • x + y) = π ↔
    o.oangle x y = 0 ∨ o.oangle x y = π := by
  simp_rw [oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, Fintype.not_linearIndependent_iff,
    Fin.sum_univ_two, Fin.exists_fin_two]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • (r • x + y) = 0 at h
    refine ⟨![m 0 + m 1 * r, m 1], ?_⟩
    change (m 0 + m 1 * r) • x + m 1 • y = 0 ∧ (m 0 + m 1 * r ≠ 0 ∨ m 1 ≠ 0)
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul] at h
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul, add_zero] at h0
    simp [h0] at hm
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • y = 0 at h
    refine ⟨![m 0 - m 1 * r, m 1], ?_⟩
    change (m 0 - m 1 * r) • x + m 1 • (r • x + y) = 0 ∧ (m 0 - m 1 * r ≠ 0 ∨ m 1 ≠ 0)
    rw [sub_smul, smul_add, smul_smul, ← add_assoc, sub_add_cancel]
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul, sub_zero] at h0
    simp [h0] at hm

/-- Adding a multiple of the first vector passed to `oangle` to the second vector does not change
the sign of the angle. -/
@[simp]
theorem oangle_sign_smul_add_right (x y : V) (r : ℝ) :
    (o.oangle x (r • x + y)).sign = (o.oangle x y).sign := by
  by_cases h : o.oangle x y = 0 ∨ o.oangle x y = π
  · rwa [Real.Angle.sign_eq_zero_iff.2 h, Real.Angle.sign_eq_zero_iff,
      oangle_smul_add_right_eq_zero_or_eq_pi_iff]
  have h' : ∀ r' : ℝ, o.oangle x (r' • x + y) ≠ 0 ∧ o.oangle x (r' • x + y) ≠ π := by
    intro r'
    rwa [← o.oangle_smul_add_right_eq_zero_or_eq_pi_iff r', not_or] at h
  let s : Set (V × V) := (fun r' : ℝ => (x, r' • x + y)) '' Set.univ
  have hc : IsConnected s := isConnected_univ.image _ (by fun_prop)
  have hf : ContinuousOn (fun z : V × V => o.oangle z.1 z.2) s := by
    refine continuousOn_of_forall_continuousAt fun z hz => o.continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [s, Set.mem_image] at hz
      obtain ⟨r', -, rfl⟩ := hz
      simp only
      intro hz
    · simpa [hz] using (h' 0).1
    · simpa [hz] using (h' r').1
  have hs : ∀ z : V × V, z ∈ s → o.oangle z.1 z.2 ≠ 0 ∧ o.oangle z.1 z.2 ≠ π := by grind
  have hx : (x, y) ∈ s := by
    convert Set.mem_image_of_mem (fun r' : ℝ => (x, r' • x + y)) (Set.mem_univ 0)
    simp
  have hy : (x, r • x + y) ∈ s := Set.mem_image_of_mem _ (Set.mem_univ _)
  convert Real.Angle.sign_eq_of_continuousOn hc hf hs hx hy

/-- Adding a multiple of the second vector passed to `oangle` to the first vector does not change
the sign of the angle. -/
@[simp]
theorem oangle_sign_add_smul_left (x y : V) (r : ℝ) :
    (o.oangle (x + r • y) y).sign = (o.oangle x y).sign := by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm x, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the first vector passed to `oangle` from the second vector does
not change the sign of the angle. -/
@[simp]
theorem oangle_sign_sub_smul_right (x y : V) (r : ℝ) :
    (o.oangle x (y - r • x)).sign = (o.oangle x y).sign := by
  rw [sub_eq_add_neg, ← neg_smul, add_comm, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the second vector passed to `oangle` from the first vector does
not change the sign of the angle. -/
@[simp]
theorem oangle_sign_sub_smul_left (x y : V) (r : ℝ) :
    (o.oangle (x - r • y) y).sign = (o.oangle x y).sign := by
  rw [sub_eq_add_neg, ← neg_smul, oangle_sign_add_smul_left]

/-- Adding the first vector passed to `oangle` to the second vector does not change the sign of
the angle. -/
@[simp]
theorem oangle_sign_add_right (x y : V) : (o.oangle x (x + y)).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_add_right x y 1, one_smul]

/-- Adding the second vector passed to `oangle` to the first vector does not change the sign of
the angle. -/
@[simp]
theorem oangle_sign_add_left (x y : V) : (o.oangle (x + y) y).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_add_smul_left x y 1, one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector does not change the
sign of the angle. -/
@[simp]
theorem oangle_sign_sub_right (x y : V) : (o.oangle x (y - x)).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_sub_smul_right x y 1, one_smul]

/-- Subtracting the second vector passed to `oangle` from the first vector does not change the
sign of the angle. -/
@[simp]
theorem oangle_sign_sub_left (x y : V) : (o.oangle (x - y) y).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_sub_smul_left x y 1, one_smul]

/-- Subtracting the second vector passed to `oangle` from a multiple of the first vector negates
the sign of the angle. -/
@[simp]
theorem oangle_sign_smul_sub_right (x y : V) (r : ℝ) :
    (o.oangle x (r • x - y)).sign = -(o.oangle x y).sign := by
  rw [← oangle_sign_neg_right, sub_eq_add_neg, oangle_sign_smul_add_right]

/-- Subtracting the first vector passed to `oangle` from a multiple of the second vector negates
the sign of the angle. -/
@[simp]
theorem oangle_sign_smul_sub_left (x y : V) (r : ℝ) :
    (o.oangle (r • y - x) y).sign = -(o.oangle x y).sign := by
  rw [← oangle_sign_neg_left, sub_eq_neg_add, oangle_sign_add_smul_left]

/-- Subtracting the second vector passed to `oangle` from the first vector negates the sign of
the angle. -/
theorem oangle_sign_sub_right_eq_neg (x y : V) :
    (o.oangle x (x - y)).sign = -(o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_sub_right x y 1, one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector negates the sign of
the angle. -/
theorem oangle_sign_sub_left_eq_neg (x y : V) :
    (o.oangle (y - x) y).sign = -(o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_sub_left x y 1, one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector then swapping the
vectors does not change the sign of the angle. -/
@[simp]
theorem oangle_sign_sub_right_swap (x y : V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign := by
  rw [oangle_sign_sub_right_eq_neg, o.oangle_rev y x, Real.Angle.sign_neg]

/-- Subtracting the second vector passed to `oangle` from the first vector then swapping the
vectors does not change the sign of the angle. -/
@[simp]
theorem oangle_sign_sub_left_swap (x y : V) : (o.oangle (x - y) x).sign = (o.oangle x y).sign := by
  rw [oangle_sign_sub_left_eq_neg, o.oangle_rev y x, Real.Angle.sign_neg]

/-- The sign of the angle between a vector, and a linear combination of that vector with a second
vector, is the sign of the factor by which the second vector is multiplied in that combination
multiplied by the sign of the angle between the two vectors. -/
theorem oangle_sign_smul_add_smul_right (x y : V) (r₁ r₂ : ℝ) :
    (o.oangle x (r₁ • x + r₂ • y)).sign = SignType.sign r₂ * (o.oangle x y).sign := by
  simp

/-- The sign of the angle between a linear combination of two vectors and the second vector is
the sign of the factor by which the first vector is multiplied in that combination multiplied by
the sign of the angle between the two vectors. -/
theorem oangle_sign_smul_add_smul_left (x y : V) (r₁ r₂ : ℝ) :
    (o.oangle (r₁ • x + r₂ • y) y).sign = SignType.sign r₁ * (o.oangle x y).sign := by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm (r₁ • x), oangle_sign_smul_add_smul_right,
    mul_neg]

/-- The sign of the angle between two linear combinations of two vectors is the sign of the
determinant of the factors in those combinations multiplied by the sign of the angle between the
two vectors. -/
theorem oangle_sign_smul_add_smul_smul_add_smul (x y : V) (r₁ r₂ r₃ r₄ : ℝ) :
    (o.oangle (r₁ • x + r₂ • y) (r₃ • x + r₄ • y)).sign =
      SignType.sign (r₁ * r₄ - r₂ * r₃) * (o.oangle x y).sign := by
  by_cases hr₁ : r₁ = 0
  · rw [hr₁, zero_smul, zero_mul, zero_add, zero_sub, Left.sign_neg,
      oangle_sign_smul_left, add_comm, oangle_sign_smul_add_smul_right, oangle_rev,
      Real.Angle.sign_neg, sign_mul, mul_neg, mul_neg, neg_mul, mul_assoc]
  · rw [← o.oangle_sign_smul_add_right (r₁ • x + r₂ • y) (r₃ • x + r₄ • y) (-r₃ / r₁), smul_add,
      smul_smul, smul_smul, div_mul_cancel₀ _ hr₁, neg_smul, ← add_assoc, add_comm (-(r₃ • x)), ←
      sub_eq_add_neg, sub_add_cancel, ← add_smul, oangle_sign_smul_right,
      oangle_sign_smul_add_smul_left, ← mul_assoc, ← sign_mul, add_mul, mul_assoc, mul_comm r₂ r₁, ←
      mul_assoc, div_mul_cancel₀ _ hr₁, add_comm, neg_mul, ← sub_eq_add_neg, mul_comm r₄,
      mul_comm r₃]

/-- A base angle of an isosceles triangle is acute, oriented vector angle form. -/
theorem abs_oangle_sub_left_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) :
    |(o.oangle (y - x) y).toReal| < π / 2 := by
  by_cases hn : x = y; · simp [hn, Real.pi_pos]
  have hs : ((2 : ℤ) • o.oangle (y - x) y).sign = (o.oangle (y - x) y).sign := by
    conv_rhs => rw [oangle_sign_sub_left_swap]
    rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h, Real.Angle.sign_pi_sub]
  rw [Real.Angle.sign_two_zsmul_eq_sign_iff] at hs
  rcases hs with (hs | hs)
  · rw [oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_sameRay_neg, neg_sub] at hs
    rcases hs with ⟨hy, -, hr⟩
    rw [← exists_nonneg_left_iff_sameRay hy] at hr
    rcases hr with ⟨r, hr0, hr⟩
    rw [eq_sub_iff_add_eq] at hr
    nth_rw 2 [← one_smul ℝ y] at hr
    rw [← add_smul] at hr
    rw [← hr, norm_smul, Real.norm_eq_abs, abs_of_pos (Left.add_pos_of_nonneg_of_pos hr0 one_pos),
      mul_left_eq_self₀, or_iff_left (norm_ne_zero_iff.2 hy), add_eq_right] at h
    rw [h, zero_add, one_smul] at hr
    exact False.elim (hn hr.symm)
  · exact hs

/-- A base angle of an isosceles triangle is acute, oriented vector angle form. -/
theorem abs_oangle_sub_right_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) :
    |(o.oangle x (x - y)).toReal| < π / 2 :=
  (o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h).symm ▸ o.abs_oangle_sub_left_toReal_lt_pi_div_two h

/-- `y` has equal unoriented angles to `x` and `z` if and only if it has equal oriented angles
(bisects the angle) or `x` and `z` are on the same ray. -/
lemma angle_eq_iff_oangle_eq_or_sameRay {x y z : V} (hx : x ≠ 0) (hz : z ≠ 0) :
    InnerProductGeometry.angle x y = InnerProductGeometry.angle y z ↔
      o.oangle x y = o.oangle y z ∨ SameRay ℝ x z := by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hr : SameRay ℝ x z
  · obtain ⟨r, hrp, rfl⟩ := hr.exists_pos_left hx hz
    simp [hr, hrp, InnerProductGeometry.angle_comm]
  simp only [hr, or_false]
  by_cases hs : (o.oangle x y).sign = (o.oangle y z).sign
  · rw [o.angle_eq_iff_oangle_eq_of_sign_eq hx hy hy hz hs]
  · have hn : o.oangle x y ≠ o.oangle y z := by grind
    simp only [hn, iff_false]
    intro he
    apply hr
    by_cases hs' : (o.oangle x y).sign = -(o.oangle y z).sign
    · rw [o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg hx hy hy hz hs'] at he
      rw [← o.oangle_eq_zero_iff_sameRay, ← o.oangle_add hx hy hz]
      simp [he]
    · have h0 : (o.oangle x y).sign = 0 ∨ (o.oangle y z).sign = 0 := by
        revert hs hs'
        generalize (o.oangle x y).sign = sxy
        generalize (o.oangle y z).sign = syz
        decide +revert
      have h0' : InnerProductGeometry.angle y z = 0 ∨ InnerProductGeometry.angle y z = π := by
        rcases h0 with h0 | h0
          <;> simpa [*] using o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0
      rcases h0' with h0' | h0'
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 he
        simp_all
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 he
        simp_all

end Orientation
