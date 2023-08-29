/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.Convex.Side
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

#align_import geometry.euclidean.angle.oriented.affine from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Oriented angles.

This file defines oriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

-/


noncomputable section

open FiniteDimensional Complex

open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

abbrev o := @Module.Oriented.positiveOrientation

/-- The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If
either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the
corresponding unoriented angle definition. -/
def oangle (p₁ p₂ p₃ : P) : Real.Angle :=
  o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
#align euclidean_geometry.oangle EuclideanGeometry.oangle

scoped notation "∡" => EuclideanGeometry.oangle

/-- Oriented angles are continuous when neither end point equals the middle point. -/
theorem continuousAt_oangle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
    ContinuousAt (fun y : P × P × P => ∡ y.1 y.2.1 y.2.2) x := by
  let f : P × P × P → V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  -- ⊢ ContinuousAt (fun y => ∡ y.fst y.snd.fst y.snd.snd) x
  have hf1 : (f x).1 ≠ 0 := by simp [hx12]
  -- ⊢ ContinuousAt (fun y => ∡ y.fst y.snd.fst y.snd.snd) x
  have hf2 : (f x).2 ≠ 0 := by simp [hx32]
  -- ⊢ ContinuousAt (fun y => ∡ y.fst y.snd.fst y.snd.snd) x
  exact (o.continuousAt_oangle hf1 hf2).comp ((continuous_fst.vsub continuous_snd.fst).prod_mk
    (continuous_snd.snd.vsub continuous_snd.fst)).continuousAt
#align euclidean_geometry.continuous_at_oangle EuclideanGeometry.continuousAt_oangle

/-- The angle ∡AAB at a point. -/
@[simp]
theorem oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0 := by simp [oangle]
                                                            -- 🎉 no goals
#align euclidean_geometry.oangle_self_left EuclideanGeometry.oangle_self_left

/-- The angle ∡ABB at a point. -/
@[simp]
theorem oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0 := by simp [oangle]
                                                             -- 🎉 no goals
#align euclidean_geometry.oangle_self_right EuclideanGeometry.oangle_self_right

/-- The angle ∡ABA at a point. -/
@[simp]
theorem oangle_self_left_right (p₁ p₂ : P) : ∡ p₁ p₂ p₁ = 0 :=
  o.oangle_self _
#align euclidean_geometry.oangle_self_left_right EuclideanGeometry.oangle_self_left_right

/-- If the angle between three points is nonzero, the first two points are not equal. -/
theorem left_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₁ ≠ p₂ := by
  rw [← @vsub_ne_zero V]; exact o.left_ne_zero_of_oangle_ne_zero h
  -- ⊢ p₁ -ᵥ p₂ ≠ 0
                          -- 🎉 no goals
#align euclidean_geometry.left_ne_of_oangle_ne_zero EuclideanGeometry.left_ne_of_oangle_ne_zero

/-- If the angle between three points is nonzero, the last two points are not equal. -/
theorem right_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₃ ≠ p₂ := by
  rw [← @vsub_ne_zero V]; exact o.right_ne_zero_of_oangle_ne_zero h
  -- ⊢ p₃ -ᵥ p₂ ≠ 0
                          -- 🎉 no goals
#align euclidean_geometry.right_ne_of_oangle_ne_zero EuclideanGeometry.right_ne_of_oangle_ne_zero

/-- If the angle between three points is nonzero, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₁ ≠ p₃ := by
  rw [← (vsub_left_injective p₂).ne_iff]; exact o.ne_of_oangle_ne_zero h
  -- ⊢ p₁ -ᵥ p₂ ≠ p₃ -ᵥ p₂
                                          -- 🎉 no goals
#align euclidean_geometry.left_ne_right_of_oangle_ne_zero EuclideanGeometry.left_ne_right_of_oangle_ne_zero

/-- If the angle between three points is `π`, the first two points are not equal. -/
theorem left_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_of_oangle_eq_pi EuclideanGeometry.left_ne_of_oangle_eq_pi

/-- If the angle between three points is `π`, the last two points are not equal. -/
theorem right_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.right_ne_of_oangle_eq_pi EuclideanGeometry.right_ne_of_oangle_eq_pi

/-- If the angle between three points is `π`, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_right_of_oangle_eq_pi EuclideanGeometry.left_ne_right_of_oangle_eq_pi

/-- If the angle between three points is `π / 2`, the first two points are not equal. -/
theorem left_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_of_oangle_eq_pi_div_two EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two

/-- If the angle between three points is `π / 2`, the last two points are not equal. -/
theorem right_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.right_ne_of_oangle_eq_pi_div_two EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two

/-- If the angle between three points is `π / 2`, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_right_of_oangle_eq_pi_div_two EuclideanGeometry.left_ne_right_of_oangle_eq_pi_div_two

/-- If the angle between three points is `-π / 2`, the first two points are not equal. -/
theorem left_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_of_oangle_eq_neg_pi_div_two EuclideanGeometry.left_ne_of_oangle_eq_neg_pi_div_two

/-- If the angle between three points is `-π / 2`, the last two points are not equal. -/
theorem right_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.right_ne_of_oangle_eq_neg_pi_div_two EuclideanGeometry.right_ne_of_oangle_eq_neg_pi_div_two

/-- If the angle between three points is `-π / 2`, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_right_of_oangle_eq_neg_pi_div_two EuclideanGeometry.left_ne_right_of_oangle_eq_neg_pi_div_two

/-- If the sign of the angle between three points is nonzero, the first two points are not
equal. -/
theorem left_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1
#align euclidean_geometry.left_ne_of_oangle_sign_ne_zero EuclideanGeometry.left_ne_of_oangle_sign_ne_zero

/-- If the sign of the angle between three points is nonzero, the last two points are not
equal. -/
theorem right_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1
#align euclidean_geometry.right_ne_of_oangle_sign_ne_zero EuclideanGeometry.right_ne_of_oangle_sign_ne_zero

/-- If the sign of the angle between three points is nonzero, the first and third points are not
equal. -/
theorem left_ne_right_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1
#align euclidean_geometry.left_ne_right_of_oangle_sign_ne_zero EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero

/-- If the sign of the angle between three points is positive, the first two points are not
equal. -/
theorem left_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
                                              -- 🎉 no goals
#align euclidean_geometry.left_ne_of_oangle_sign_eq_one EuclideanGeometry.left_ne_of_oangle_sign_eq_one

/-- If the sign of the angle between three points is positive, the last two points are not
equal. -/
theorem right_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₃ ≠ p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
                                               -- 🎉 no goals
#align euclidean_geometry.right_ne_of_oangle_sign_eq_one EuclideanGeometry.right_ne_of_oangle_sign_eq_one

/-- If the sign of the angle between three points is positive, the first and third points are not
equal. -/
theorem left_ne_right_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
                                                    -- 🎉 no goals
#align euclidean_geometry.left_ne_right_of_oangle_sign_eq_one EuclideanGeometry.left_ne_right_of_oangle_sign_eq_one

/-- If the sign of the angle between three points is negative, the first two points are not
equal. -/
theorem left_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₁ ≠ p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
                                              -- 🎉 no goals
#align euclidean_geometry.left_ne_of_oangle_sign_eq_neg_one EuclideanGeometry.left_ne_of_oangle_sign_eq_neg_one

/-- If the sign of the angle between three points is negative, the last two points are not equal.
-/
theorem right_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₃ ≠ p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
                                               -- 🎉 no goals
#align euclidean_geometry.right_ne_of_oangle_sign_eq_neg_one EuclideanGeometry.right_ne_of_oangle_sign_eq_neg_one

/-- If the sign of the angle between three points is negative, the first and third points are not
equal. -/
theorem left_ne_right_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
                                                    -- 🎉 no goals
#align euclidean_geometry.left_ne_right_of_oangle_sign_eq_neg_one EuclideanGeometry.left_ne_right_of_oangle_sign_eq_neg_one

/-- Reversing the order of the points passed to `oangle` negates the angle. -/
theorem oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃ :=
  o.oangle_rev _ _
#align euclidean_geometry.oangle_rev EuclideanGeometry.oangle_rev

/-- Adding an angle to that with the order of the points reversed results in 0. -/
@[simp]
theorem oangle_add_oangle_rev (p₁ p₂ p₃ : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0 :=
  o.oangle_add_oangle_rev _ _
#align euclidean_geometry.oangle_add_oangle_rev EuclideanGeometry.oangle_add_oangle_rev

/-- An oriented angle is zero if and only if the angle with the order of the points reversed is
zero. -/
theorem oangle_eq_zero_iff_oangle_rev_eq_zero {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0 :=
  o.oangle_eq_zero_iff_oangle_rev_eq_zero
#align euclidean_geometry.oangle_eq_zero_iff_oangle_rev_eq_zero EuclideanGeometry.oangle_eq_zero_iff_oangle_rev_eq_zero

/-- An oriented angle is `π` if and only if the angle with the order of the points reversed is
`π`. -/
theorem oangle_eq_pi_iff_oangle_rev_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π :=
  o.oangle_eq_pi_iff_oangle_rev_eq_pi
#align euclidean_geometry.oangle_eq_pi_iff_oangle_rev_eq_pi EuclideanGeometry.oangle_eq_pi_iff_oangle_rev_eq_pi

/-- An oriented angle is not zero or `π` if and only if the three points are affinely
independent. -/
theorem oangle_ne_zero_and_ne_pi_iff_affineIndependent {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π ↔ AffineIndependent ℝ ![p₁, p₂, p₃] := by
  rw [oangle, o.oangle_ne_zero_and_ne_pi_iff_linearIndependent,
    affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3), ←
    linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3)).toEquiv]
  convert Iff.rfl
  -- ⊢ (fun i => Matrix.vecCons p₁ ![p₂, p₃] ↑i -ᵥ Matrix.vecCons p₁ ![p₂, p₃] 1) ∘ …
  ext i
  -- ⊢ ((fun i => Matrix.vecCons p₁ ![p₂, p₃] ↑i -ᵥ Matrix.vecCons p₁ ![p₂, p₃] 1)  …
  fin_cases i <;> rfl
  -- ⊢ ((fun i => Matrix.vecCons p₁ ![p₂, p₃] ↑i -ᵥ Matrix.vecCons p₁ ![p₂, p₃] 1)  …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align euclidean_geometry.oangle_ne_zero_and_ne_pi_iff_affine_independent EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent

/-- An oriented angle is zero or `π` if and only if the three points are collinear. -/
theorem oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π ↔ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  rw [← not_iff_not, not_or, oangle_ne_zero_and_ne_pi_iff_affineIndependent,
    affineIndependent_iff_not_collinear_set]
#align euclidean_geometry.oangle_eq_zero_or_eq_pi_iff_collinear EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear

/-- If twice the oriented angles between two triples of points are equal, one triple is affinely
independent if and only if the other is. -/
theorem affineIndependent_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
    AffineIndependent ℝ ![p₁, p₂, p₃] ↔ AffineIndependent ℝ ![p₄, p₅, p₆] := by
  simp_rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.two_zsmul_ne_zero_iff, h]
  -- 🎉 no goals
#align euclidean_geometry.affine_independent_iff_of_two_zsmul_oangle_eq EuclideanGeometry.affineIndependent_iff_of_two_zsmul_oangle_eq

/-- If twice the oriented angles between two triples of points are equal, one triple is collinear
if and only if the other is. -/
theorem collinear_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ Collinear ℝ ({p₄, p₅, p₆} : Set P) := by
  simp_rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, h]
  -- 🎉 no goals
#align euclidean_geometry.collinear_iff_of_two_zsmul_oangle_eq EuclideanGeometry.collinear_iff_of_two_zsmul_oangle_eq

/-- If corresponding pairs of points in two angles have the same vector span, twice those angles
are equal. -/
theorem two_zsmul_oangle_of_vectorSpan_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : vectorSpan ℝ ({p₁, p₂} : Set P) = vectorSpan ℝ ({p₄, p₅} : Set P))
    (h₃₂₆₅ : vectorSpan ℝ ({p₃, p₂} : Set P) = vectorSpan ℝ ({p₆, p₅} : Set P)) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ := by
  simp_rw [vectorSpan_pair] at h₁₂₄₅ h₃₂₆₅
  -- ⊢ 2 • ∡ p₁ p₂ p₃ = 2 • ∡ p₄ p₅ p₆
  exact o.two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅
  -- 🎉 no goals
#align euclidean_geometry.two_zsmul_oangle_of_vector_span_eq EuclideanGeometry.two_zsmul_oangle_of_vectorSpan_eq

/-- If the lines determined by corresponding pairs of points in two angles are parallel, twice
those angles are equal. -/
theorem two_zsmul_oangle_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : line[ℝ, p₁, p₂] ∥ line[ℝ, p₄, p₅]) (h₃₂₆₅ : line[ℝ, p₃, p₂] ∥ line[ℝ, p₆, p₅]) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq] at h₁₂₄₅ h₃₂₆₅
  -- ⊢ 2 • ∡ p₁ p₂ p₃ = 2 • ∡ p₄ p₅ p₆
  exact two_zsmul_oangle_of_vectorSpan_eq h₁₂₄₅ h₃₂₆₅
  -- 🎉 no goals
#align euclidean_geometry.two_zsmul_oangle_of_parallel EuclideanGeometry.two_zsmul_oangle_of_parallel

/-- Given three points not equal to `p`, the angle between the first and the second at `p` plus
the angle between the second and the third equals the angle between the first and the third. -/
@[simp]
theorem oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ :=
  o.oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)
#align euclidean_geometry.oangle_add EuclideanGeometry.oangle_add

/-- Given three points not equal to `p`, the angle between the second and the third at `p` plus
the angle between the first and the second equals the angle between the first and the third. -/
@[simp]
theorem oangle_add_swap {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃ :=
  o.oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)
#align euclidean_geometry.oangle_add_swap EuclideanGeometry.oangle_add_swap

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the first and the second equals the angle between the second and the third. -/
@[simp]
theorem oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃ :=
  o.oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)
#align euclidean_geometry.oangle_sub_left EuclideanGeometry.oangle_sub_left

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the second and the third equals the angle between the first and the second. -/
@[simp]
theorem oangle_sub_right {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂ :=
  o.oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)
#align euclidean_geometry.oangle_sub_right EuclideanGeometry.oangle_sub_right

/-- Given three points not equal to `p`, adding the angles between them at `p` in cyclic order
results in 0. -/
@[simp]
theorem oangle_add_cyc3 {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 :=
  o.oangle_add_cyc3 (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)
#align euclidean_geometry.oangle_add_cyc3 EuclideanGeometry.oangle_add_cyc3

/-- Pons asinorum, oriented angle-at-point form. -/
theorem oangle_eq_oangle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁ := by
  simp_rw [dist_eq_norm_vsub V] at h
  -- ⊢ ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁
  rw [oangle, oangle, ← vsub_sub_vsub_cancel_left p₃ p₂ p₁, ← vsub_sub_vsub_cancel_left p₂ p₃ p₁,
    o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
#align euclidean_geometry.oangle_eq_oangle_of_dist_eq EuclideanGeometry.oangle_eq_oangle_of_dist_eq

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ ≠ p₃)
    (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : ℤ) • ∡ p₁ p₂ p₃ := by
  simp_rw [dist_eq_norm_vsub V] at h
  -- ⊢ ∡ p₃ p₁ p₂ = ↑π - 2 • ∡ p₁ p₂ p₃
  rw [oangle, oangle]
  -- ⊢ Orientation.oangle o (p₃ -ᵥ p₁) (p₂ -ᵥ p₁) = ↑π - 2 • Orientation.oangle o ( …
  convert o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1
  · rw [← neg_vsub_eq_vsub_rev p₁ p₃, ← neg_vsub_eq_vsub_rev p₁ p₂, o.oangle_neg_neg]
    -- 🎉 no goals
  · rw [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]; simp
    -- ⊢ ↑π - 2 • Orientation.oangle o (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) = ↑π - 2 • Orientation.o …
                                                        -- 🎉 no goals
  · simpa using hn
    -- 🎉 no goals
#align euclidean_geometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq EuclideanGeometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
theorem abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₁ p₂ p₃).toReal| < π / 2 := by
  simp_rw [dist_eq_norm_vsub V] at h
  -- ⊢ |Real.Angle.toReal (∡ p₁ p₂ p₃)| < π / 2
  rw [oangle, ← vsub_sub_vsub_cancel_left p₃ p₂ p₁]
  -- ⊢ |Real.Angle.toReal (Orientation.oangle o (p₁ -ᵥ p₂) (p₁ -ᵥ p₂ - (p₁ -ᵥ p₃))) …
  exact o.abs_oangle_sub_right_toReal_lt_pi_div_two h
  -- 🎉 no goals
#align euclidean_geometry.abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq EuclideanGeometry.abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
theorem abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₂ p₃ p₁).toReal| < π / 2 :=
  oangle_eq_oangle_of_dist_eq h ▸ abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq h
#align euclidean_geometry.abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq EuclideanGeometry.abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq

/-- The cosine of the oriented angle at `p` between two points not equal to `p` equals that of the
unoriented angle. -/
theorem cos_oangle_eq_cos_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    Real.Angle.cos (∡ p₁ p p₂) = Real.cos (∠ p₁ p p₂) :=
  o.cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)
#align euclidean_geometry.cos_oangle_eq_cos_angle EuclideanGeometry.cos_oangle_eq_cos_angle

/-- The oriented angle at `p` between two points not equal to `p` is plus or minus the unoriented
angle. -/
theorem oangle_eq_angle_or_eq_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂ :=
  o.oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)
#align euclidean_geometry.oangle_eq_angle_or_eq_neg_angle EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle

/-- The unoriented angle at `p` between two points not equal to `p` is the absolute value of the
oriented angle. -/
theorem angle_eq_abs_oangle_toReal {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal| :=
  o.angle_eq_abs_oangle_toReal (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)
#align euclidean_geometry.angle_eq_abs_oangle_to_real EuclideanGeometry.angle_eq_abs_oangle_toReal

/-- If the sign of the oriented angle at `p` between two points is zero, either one of the points
equals `p` or the unoriented angle is 0 or π. -/
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {p p₁ p₂ : P}
    (h : (∡ p₁ p p₂).sign = 0) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π := by
  convert o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h <;> simp
  -- ⊢ p₁ = p ↔ p₁ -ᵥ p = 0
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
#align euclidean_geometry.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero EuclideanGeometry.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
theorem oangle_eq_of_angle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
    (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
  o.oangle_eq_of_angle_eq_of_sign_eq h hs
#align euclidean_geometry.oangle_eq_of_angle_eq_of_sign_eq EuclideanGeometry.oangle_eq_of_angle_eq_of_sign_eq

/-- If the signs of two nondegenerate oriented angles between points are equal, the oriented
angles are equal if and only if the unoriented angles are equal. -/
theorem angle_eq_iff_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂)
    (hp₄ : p₄ ≠ p₅) (hp₆ : p₆ ≠ p₅) (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
  o.angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃) (vsub_ne_zero.2 hp₄)
    (vsub_ne_zero.2 hp₆) hs
#align euclidean_geometry.angle_eq_iff_oangle_eq_of_sign_eq EuclideanGeometry.angle_eq_iff_oangle_eq_of_sign_eq

/-- The oriented angle between three points equals the unoriented angle if the sign is
positive. -/
theorem oangle_eq_angle_of_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) :
    ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃ :=
  o.oangle_eq_angle_of_sign_eq_one h
#align euclidean_geometry.oangle_eq_angle_of_sign_eq_one EuclideanGeometry.oangle_eq_angle_of_sign_eq_one

/-- The oriented angle between three points equals minus the unoriented angle if the sign is
negative. -/
theorem oangle_eq_neg_angle_of_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    ∡ p₁ p₂ p₃ = -∠ p₁ p₂ p₃ :=
  o.oangle_eq_neg_angle_of_sign_eq_neg_one h
#align euclidean_geometry.oangle_eq_neg_angle_of_sign_eq_neg_one EuclideanGeometry.oangle_eq_neg_angle_of_sign_eq_neg_one

/-- The unoriented angle at `p` between two points not equal to `p` is zero if and only if the
unoriented angle is zero. -/
theorem oangle_eq_zero_iff_angle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
    ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0 :=
  o.oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)
#align euclidean_geometry.oangle_eq_zero_iff_angle_eq_zero EuclideanGeometry.oangle_eq_zero_iff_angle_eq_zero

/-- The oriented angle between three points is `π` if and only if the unoriented angle is `π`. -/
theorem oangle_eq_pi_iff_angle_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π :=
  o.oangle_eq_pi_iff_angle_eq_pi
#align euclidean_geometry.oangle_eq_pi_iff_angle_eq_pi EuclideanGeometry.oangle_eq_pi_iff_angle_eq_pi

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle. -/
theorem angle_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₁ p₂ p₃ = π / 2 := by
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  -- ⊢ inner (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) = 0
  exact o.inner_eq_zero_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle
(reversed). -/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  -- ⊢ ∠ p₁ p₂ p₃ = π / 2
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align euclidean_geometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle is `π / 2`. -/
theorem angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₁ p₂ p₃ = π / 2 := by
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  -- ⊢ inner (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) = 0
  exact o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h
  -- 🎉 no goals
#align euclidean_geometry.angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle (reversed) is
`π / 2`. -/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  -- ⊢ ∠ p₁ p₂ p₃ = π / 2
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h
  -- 🎉 no goals
#align euclidean_geometry.angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two

/-- Swapping the first and second points in an oriented angle negates the sign of that angle. -/
theorem oangle_swap₁₂_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign := by
  rw [eq_comm, oangle, oangle, ← o.oangle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←
    vsub_sub_vsub_cancel_left p₁ p₃ p₂, ← neg_vsub_eq_vsub_rev p₃ p₂, sub_eq_add_neg,
    neg_vsub_eq_vsub_rev p₂ p₁, add_comm, ← @neg_one_smul ℝ]
  nth_rw 2 [← one_smul ℝ (p₁ -ᵥ p₂)]
  -- ⊢ Real.Angle.sign (Orientation.oangle o (p₁ -ᵥ p₂) (1 • (p₁ -ᵥ p₂) + -1 • (p₃  …
  rw [o.oangle_sign_smul_add_smul_right]
  -- ⊢ ↑SignType.sign (-1) * Real.Angle.sign (Orientation.oangle o (p₁ -ᵥ p₂) (p₃ - …
  simp
  -- 🎉 no goals
#align euclidean_geometry.oangle_swap₁₂_sign EuclideanGeometry.oangle_swap₁₂_sign

/-- Swapping the first and third points in an oriented angle negates the sign of that angle. -/
theorem oangle_swap₁₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign := by
  rw [oangle_rev, Real.Angle.sign_neg, neg_neg]
  -- 🎉 no goals
#align euclidean_geometry.oangle_swap₁₃_sign EuclideanGeometry.oangle_swap₁₃_sign

/-- Swapping the second and third points in an oriented angle negates the sign of that angle. -/
theorem oangle_swap₂₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign := by
  rw [oangle_swap₁₃_sign, ← oangle_swap₁₂_sign, oangle_swap₁₃_sign]
  -- 🎉 no goals
#align euclidean_geometry.oangle_swap₂₃_sign EuclideanGeometry.oangle_swap₂₃_sign

/-- Rotating the points in an oriented angle does not change the sign of that angle. -/
theorem oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign := by
  rw [← oangle_swap₁₂_sign, oangle_swap₁₃_sign]
  -- 🎉 no goals
#align euclidean_geometry.oangle_rotate_sign EuclideanGeometry.oangle_rotate_sign

/-- The oriented angle between three points is π if and only if the second point is strictly
between the other two. -/
theorem oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  rw [oangle_eq_pi_iff_angle_eq_pi, angle_eq_pi_iff_sbtw]
  -- 🎉 no goals
#align euclidean_geometry.oangle_eq_pi_iff_sbtw EuclideanGeometry.oangle_eq_pi_iff_sbtw

/-- If the second of three points is strictly between the other two, the oriented angle at that
point is π. -/
theorem _root_.Sbtw.oangle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₂ p₃ = π :=
  oangle_eq_pi_iff_sbtw.2 h
#align sbtw.oangle₁₂₃_eq_pi Sbtw.oangle₁₂₃_eq_pi

/-- If the second of three points is strictly between the other two, the oriented angle at that
point (reversed) is π. -/
theorem _root_.Sbtw.oangle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₂ p₁ = π := by
  rw [oangle_eq_pi_iff_oangle_rev_eq_pi, ← h.oangle₁₂₃_eq_pi]
  -- 🎉 no goals
#align sbtw.oangle₃₂₁_eq_pi Sbtw.oangle₃₂₁_eq_pi

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point is zero. -/
theorem _root_.Wbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 := by
  by_cases hp₂p₁ : p₂ = p₁; · simp [hp₂p₁]
  -- ⊢ ∡ p₂ p₁ p₃ = 0
                              -- 🎉 no goals
  by_cases hp₃p₁ : p₃ = p₁; · simp [hp₃p₁]
  -- ⊢ ∡ p₂ p₁ p₃ = 0
                              -- 🎉 no goals
  rw [oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁]
  -- ⊢ ∠ p₂ p₁ p₃ = 0
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁
  -- 🎉 no goals
#align wbtw.oangle₂₁₃_eq_zero Wbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point is zero. -/
theorem _root_.Sbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
  h.wbtw.oangle₂₁₃_eq_zero
#align sbtw.oangle₂₁₃_eq_zero Sbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point (reversed) is zero. -/
theorem _root_.Wbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 := by
  rw [oangle_eq_zero_iff_oangle_rev_eq_zero, h.oangle₂₁₃_eq_zero]
  -- 🎉 no goals
#align wbtw.oangle₃₁₂_eq_zero Wbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point (reversed) is zero. -/
theorem _root_.Sbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
  h.wbtw.oangle₃₁₂_eq_zero
#align sbtw.oangle₃₁₂_eq_zero Sbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point is zero. -/
theorem _root_.Wbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.symm.oangle₂₁₃_eq_zero
#align wbtw.oangle₂₃₁_eq_zero Wbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point is zero. -/
theorem _root_.Sbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.wbtw.oangle₂₃₁_eq_zero
#align sbtw.oangle₂₃₁_eq_zero Sbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point (reversed) is zero. -/
theorem _root_.Wbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.symm.oangle₃₁₂_eq_zero
#align wbtw.oangle₁₃₂_eq_zero Wbtw.oangle₁₃₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point (reversed) is zero. -/
theorem _root_.Sbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.wbtw.oangle₁₃₂_eq_zero
#align sbtw.oangle₁₃₂_eq_zero Sbtw.oangle₁₃₂_eq_zero

/-- The oriented angle between three points is zero if and only if one of the first and third
points is weakly between the other two. -/
theorem oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ↔ Wbtw ℝ p₂ p₁ p₃ ∨ Wbtw ℝ p₂ p₃ p₁ := by
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  -- ⊢ ∡ p₁ p₂ p₃ = 0 ↔ Wbtw ℝ p₂ p₁ p₃ ∨ Wbtw ℝ p₂ p₃ p₁
                              -- 🎉 no goals
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  -- ⊢ ∡ p₁ p₂ p₃ = 0 ↔ Wbtw ℝ p₂ p₁ p₃ ∨ Wbtw ℝ p₂ p₃ p₁
                              -- 🎉 no goals
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂, angle_eq_zero_iff_ne_and_wbtw]
  -- ⊢ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ ↔ Wbtw ℝ p₂ p₁ p₃ ∨ Wb …
  simp [hp₁p₂, hp₃p₂]
  -- 🎉 no goals
#align euclidean_geometry.oangle_eq_zero_iff_wbtw EuclideanGeometry.oangle_eq_zero_iff_wbtw

/-- An oriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
theorem _root_.Wbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Wbtw ℝ p₂ p₁ p₁') (hp₁p₂ : p₁ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  -- ⊢ ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃
                              -- 🎉 no goals
  by_cases hp₁'p₂ : p₁' = p₂; · rw [hp₁'p₂, wbtw_self_iff] at h; exact False.elim (hp₁p₂ h)
  -- ⊢ ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃
                                -- ⊢ ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃
                                                                 -- 🎉 no goals
  rw [← oangle_add hp₁'p₂ hp₁p₂ hp₃p₂, h.oangle₃₁₂_eq_zero, zero_add]
  -- 🎉 no goals
#align wbtw.oangle_eq_left Wbtw.oangle_eq_left

/-- An oriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
theorem _root_.Sbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Sbtw ℝ p₂ p₁ p₁') :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
  h.wbtw.oangle_eq_left h.ne_left
#align sbtw.oangle_eq_left Sbtw.oangle_eq_left

/-- An oriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
theorem _root_.Wbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Wbtw ℝ p₂ p₃ p₃') (hp₃p₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' := by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ← oangle_rev]
                                   -- 🎉 no goals
#align wbtw.oangle_eq_right Wbtw.oangle_eq_right

/-- An oriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
theorem _root_.Sbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Sbtw ℝ p₂ p₃ p₃') :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
  h.wbtw.oangle_eq_right h.ne_left
#align sbtw.oangle_eq_right Sbtw.oangle_eq_right

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between it and the second point. -/
@[simp]
theorem oangle_midpoint_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  by_cases h : p₁ = p₂; · simp [h]
  -- ⊢ ∡ (midpoint ℝ p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃
                          -- 🎉 no goals
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_left
  -- 🎉 no goals
#align euclidean_geometry.oangle_midpoint_left EuclideanGeometry.oangle_midpoint_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between the second point and that point. -/
@[simp]
theorem oangle_midpoint_rev_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm, oangle_midpoint_left]
  -- 🎉 no goals
#align euclidean_geometry.oangle_midpoint_rev_left EuclideanGeometry.oangle_midpoint_rev_left

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between it and the second point. -/
@[simp]
theorem oangle_midpoint_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₃ p₂) = ∡ p₁ p₂ p₃ := by
  by_cases h : p₃ = p₂; · simp [h]
  -- ⊢ ∡ p₁ p₂ (midpoint ℝ p₃ p₂) = ∡ p₁ p₂ p₃
                          -- 🎉 no goals
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_right
  -- 🎉 no goals
#align euclidean_geometry.oangle_midpoint_right EuclideanGeometry.oangle_midpoint_right

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between the second point and that point. -/
@[simp]
theorem oangle_midpoint_rev_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₂ p₃) = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm, oangle_midpoint_right]
  -- 🎉 no goals
#align euclidean_geometry.oangle_midpoint_rev_right EuclideanGeometry.oangle_midpoint_rev_right

/-- Replacing the first point by one on the same line but the opposite ray adds π to the oriented
angle. -/
theorem _root_.Sbtw.oangle_eq_add_pi_left
    {p₁ p₁' p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₁') (hp₃p₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ + π := by
  rw [← h.oangle₁₂₃_eq_pi, oangle_add_swap h.left_ne h.right_ne hp₃p₂]
  -- 🎉 no goals
#align sbtw.oangle_eq_add_pi_left Sbtw.oangle_eq_add_pi_left

/-- Replacing the third point by one on the same line but the opposite ray adds π to the oriented
angle. -/
theorem _root_.Sbtw.oangle_eq_add_pi_right
    {p₁ p₂ p₃ p₃' : P} (h : Sbtw ℝ p₃ p₂ p₃') (hp₁p₂ : p₁ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' + π := by
  rw [← h.oangle₃₂₁_eq_pi, oangle_add hp₁p₂ h.right_ne h.left_ne]
  -- 🎉 no goals
#align sbtw.oangle_eq_add_pi_right Sbtw.oangle_eq_add_pi_right

/-- Replacing both the first and third points by ones on the same lines but the opposite rays
does not change the oriented angle (vertically opposite angles). -/
theorem _root_.Sbtw.oangle_eq_left_right {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : Sbtw ℝ p₁ p₂ p₁')
    (h₃ : Sbtw ℝ p₃ p₂ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃' := by
  rw [h₁.oangle_eq_add_pi_left h₃.left_ne, h₃.oangle_eq_add_pi_right h₁.right_ne, add_assoc,
    Real.Angle.coe_pi_add_coe_pi, add_zero]
#align sbtw.oangle_eq_left_right Sbtw.oangle_eq_left_right

/-- Replacing the first point by one on the same line does not change twice the oriented angle. -/
theorem _root_.Collinear.two_zsmul_oangle_eq_left {p₁ p₁' p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₁'} : Set P)) (hp₁p₂ : p₁ ≠ p₂) (hp₁'p₂ : p₁' ≠ p₂) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  -- ⊢ 2 • ∡ p₁ p₂ p₃ = 2 • ∡ p₁' p₂ p₃
                              -- 🎉 no goals
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · have hw' : Sbtw ℝ p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩
    -- ⊢ 2 • ∡ p₁ p₂ p₃ = 2 • ∡ p₁' p₂ p₃
    rw [hw'.oangle_eq_add_pi_left hp₃p₂, smul_add, Real.Angle.two_zsmul_coe_pi, add_zero]
    -- 🎉 no goals
  · rw [hw.oangle_eq_left hp₁'p₂]
    -- 🎉 no goals
  · rw [hw.symm.oangle_eq_left hp₁p₂]
    -- 🎉 no goals
#align collinear.two_zsmul_oangle_eq_left Collinear.two_zsmul_oangle_eq_left

/-- Replacing the third point by one on the same line does not change twice the oriented angle. -/
theorem _root_.Collinear.two_zsmul_oangle_eq_right {p₁ p₂ p₃ p₃' : P}
    (h : Collinear ℝ ({p₃, p₂, p₃'} : Set P)) (hp₃p₂ : p₃ ≠ p₂) (hp₃'p₂ : p₃' ≠ p₂) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃' := by
  rw [oangle_rev, smul_neg, h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂, ← smul_neg, ← oangle_rev]
  -- 🎉 no goals
#align collinear.two_zsmul_oangle_eq_right Collinear.two_zsmul_oangle_eq_right

/-- Two different points are equidistant from a third point if and only if that third point
equals some multiple of a `π / 2` rotation of the vector between those points, plus the midpoint
of those points. -/
theorem dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint {p₁ p₂ p : P} (h : p₁ ≠ p₂) :
    dist p₁ p = dist p₂ p ↔
      ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) (p₂ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₂ = p := by
  refine' ⟨fun hd => _, fun hr => _⟩
  -- ⊢ ∃ r, r • ↑(Orientation.rotation o ↑(π / 2)) (p₂ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₂ = p
  · have hi : ⟪p₂ -ᵥ p₁, p -ᵥ midpoint ℝ p₁ p₂⟫ = 0 := by
      rw [@dist_eq_norm_vsub' V, @dist_eq_norm_vsub' V, ←
        mul_self_inj (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_mul_norm, ←
        real_inner_self_eq_norm_mul_norm] at hd
      simp_rw [vsub_midpoint, ← vsub_sub_vsub_cancel_left p₂ p₁ p, inner_sub_left, inner_add_right,
        inner_smul_right, hd, real_inner_comm (p -ᵥ p₁)]
      abel
    rw [@Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ _ o,
      or_iff_right (vsub_ne_zero.2 h.symm)] at hi
    rcases hi with ⟨r, hr⟩
    -- ⊢ ∃ r, r • ↑(Orientation.rotation o ↑(π / 2)) (p₂ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₂ = p
    rw [eq_comm, ← eq_vadd_iff_vsub_eq] at hr
    -- ⊢ ∃ r, r • ↑(Orientation.rotation o ↑(π / 2)) (p₂ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₂ = p
    exact ⟨r, hr.symm⟩
    -- 🎉 no goals
  · rcases hr with ⟨r, rfl⟩
    -- ⊢ dist p₁ (r • ↑(Orientation.rotation o ↑(π / 2)) (p₂ -ᵥ p₁) +ᵥ midpoint ℝ p₁  …
    simp_rw [@dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, left_vsub_midpoint, right_vsub_midpoint,
      invOf_eq_inv, ← neg_vsub_eq_vsub_rev p₂ p₁, ← mul_self_inj (norm_nonneg _) (norm_nonneg _), ←
      real_inner_self_eq_norm_mul_norm, inner_sub_sub_self]
    simp [-neg_vsub_eq_vsub_rev]
    -- 🎉 no goals
#align euclidean_geometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint EuclideanGeometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint

open AffineSubspace

/-- Given two pairs of distinct points on the same line, such that the vectors between those
pairs of points are on the same ray (oriented in the same direction on that line), and a fifth
point, the angles at the fifth point between each of those two pairs of points have the same
sign. -/
theorem _root_.Collinear.oangle_sign_of_sameRay_vsub {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ ≠ p₂)
    (hp₃p₄ : p₃ ≠ p₄) (hc : Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P))
    (hr : SameRay ℝ (p₂ -ᵥ p₁) (p₄ -ᵥ p₃)) : (∡ p₁ p₅ p₂).sign = (∡ p₃ p₅ p₄).sign := by
  by_cases hc₅₁₂ : Collinear ℝ ({p₅, p₁, p₂} : Set P)
  -- ⊢ Real.Angle.sign (∡ p₁ p₅ p₂) = Real.Angle.sign (∡ p₃ p₅ p₄)
  · have hc₅₁₂₃₄ : Collinear ℝ ({p₅, p₁, p₂, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂
    have hc₅₃₄ : Collinear ℝ ({p₅, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄
    rw [Set.insert_comm] at hc₅₁₂ hc₅₃₄
    -- ⊢ Real.Angle.sign (∡ p₁ p₅ p₂) = Real.Angle.sign (∡ p₃ p₅ p₄)
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂
    -- ⊢ Real.Angle.sign (∡ p₁ p₅ p₂) = Real.Angle.sign (∡ p₃ p₅ p₄)
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄
    -- ⊢ Real.Angle.sign (∡ p₁ p₅ p₂) = Real.Angle.sign (∡ p₃ p₅ p₄)
    rw [← Real.Angle.sign_eq_zero_iff] at hs₁₅₂ hs₃₅₄
    -- ⊢ Real.Angle.sign (∡ p₁ p₅ p₂) = Real.Angle.sign (∡ p₃ p₅ p₄)
    rw [hs₁₅₂, hs₃₅₄]
    -- 🎉 no goals
  · let s : Set (P × P × P) :=
      (fun x : line[ℝ, p₁, p₂] × V => (x.1, p₅, x.2 +ᵥ (x.1 : P))) ''
        Set.univ ×ˢ {v | SameRay ℝ (p₂ -ᵥ p₁) v ∧ v ≠ 0}
    have hco : IsConnected s :=
      haveI : ConnectedSpace line[ℝ, p₁, p₂] := AddTorsor.connectedSpace _ _
      (isConnected_univ.prod (isConnected_setOf_sameRay_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _
        (continuous_fst.subtype_val.prod_mk (continuous_const.prod_mk
          (continuous_snd.vadd continuous_fst.subtype_val))).continuousOn
    have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) s := by
      refine' ContinuousAt.continuousOn fun p hp => continuousAt_oangle _ _
      all_goals
        simp_rw [Set.mem_image, Set.mem_prod, Set.mem_univ, true_and_iff, Prod.ext_iff] at hp
        obtain ⟨q₁, q₅, q₂⟩ := p
        dsimp only at hp ⊢
        obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
        dsimp only [Subtype.coe_mk, Set.mem_setOf] at hv ⊢
        obtain ⟨hvr, -⟩ := hv
        rintro rfl
        refine' hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan _).2 (collinear_pair _ _ _))
      · exact hq
      · refine' vadd_mem_of_mem_direction _ hq
        rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
        obtain ⟨r, -, rfl⟩ := hvr
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hsp : ∀ p : P × P × P, p ∈ s → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π := by
      intro p hp
      simp_rw [Set.mem_image, Set.mem_prod, Set.mem_setOf, Set.mem_univ, true_and_iff,
        Prod.ext_iff] at hp
      obtain ⟨q₁, q₅, q₂⟩ := p
      dsimp only at hp ⊢
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
      dsimp only [Subtype.coe_mk, Set.mem_setOf] at hv ⊢
      obtain ⟨hvr, hv0⟩ := hv
      rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
      obtain ⟨r, -, rfl⟩ := hvr
      change q ∈ line[ℝ, p₁, p₂] at hq
      rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
      refine' affineIndependent_of_ne_of_mem_of_not_mem_of_mem _ hq
          (fun h => hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan h).2 (collinear_pair _ _ _))) _
      · rwa [← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero]
      · refine' vadd_mem_of_mem_direction _ hq
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hp₁p₂s : (p₁, p₅, p₂) ∈ s := by
      simp_rw [Set.mem_image, Set.mem_prod, Set.mem_setOf, Set.mem_univ, true_and_iff, Prod.ext_iff]
      refine' ⟨⟨⟨p₁, left_mem_affineSpan_pair _ _ _⟩, p₂ -ᵥ p₁⟩,
        ⟨SameRay.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, _⟩
      simp
    have hp₃p₄s : (p₃, p₅, p₄) ∈ s := by
      simp_rw [Set.mem_image, Set.mem_prod, Set.mem_setOf, Set.mem_univ, true_and_iff, Prod.ext_iff]
      refine' ⟨⟨⟨p₃, hc.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hp₁p₂⟩, p₄ -ᵥ p₃⟩,
        ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, _⟩
      simp
    convert Real.Angle.sign_eq_of_continuousOn hco hf hsp hp₃p₄s hp₁p₂s
    -- 🎉 no goals
#align collinear.oangle_sign_of_same_ray_vsub Collinear.oangle_sign_of_sameRay_vsub

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or second and third points have the same sign. -/
theorem _root_.Sbtw.oangle_sign_eq {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₂ p₄ p₃).sign :=
  haveI hc : Collinear ℝ ({p₁, p₂, p₂, p₃} : Set P) := by simpa using h.wbtw.collinear
                                                          -- 🎉 no goals
  hc.oangle_sign_of_sameRay_vsub _ h.left_ne h.ne_right h.wbtw.sameRay_vsub
#align sbtw.oangle_sign_eq Sbtw.oangle_sign_eq

/-- Given three points in weak order on the same line, with the first not equal to the second,
and a fourth point, the angles at the fourth point between the first and second or first and
third points have the same sign. -/
theorem _root_.Wbtw.oangle_sign_eq_of_ne_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw ℝ p₁ p₂ p₃)
    (hne : p₁ ≠ p₂) : (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  haveI hc : Collinear ℝ ({p₁, p₂, p₁, p₃} : Set P) := by
    simpa [Set.insert_comm p₂] using h.collinear
    -- 🎉 no goals
  hc.oangle_sign_of_sameRay_vsub _ hne (h.left_ne_right_of_ne_left hne.symm) h.sameRay_vsub_left
#align wbtw.oangle_sign_eq_of_ne_left Wbtw.oangle_sign_eq_of_ne_left

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or first and third points have the same sign. -/
theorem _root_.Sbtw.oangle_sign_eq_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne
#align sbtw.oangle_sign_eq_left Sbtw.oangle_sign_eq_left

/-- Given three points in weak order on the same line, with the second not equal to the third,
and a fourth point, the angles at the fourth point between the second and third or first and
third points have the same sign. -/
theorem _root_.Wbtw.oangle_sign_eq_of_ne_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw ℝ p₁ p₂ p₃)
    (hne : p₂ ≠ p₃) : (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign := by
  simp_rw [oangle_rev p₃, Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]
  -- 🎉 no goals
#align wbtw.oangle_sign_eq_of_ne_right Wbtw.oangle_sign_eq_of_ne_right

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the second and third or first and third points have the same sign. -/
theorem _root_.Sbtw.oangle_sign_eq_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
  h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right
#align sbtw.oangle_sign_eq_right Sbtw.oangle_sign_eq_right

/-- Given two points in an affine subspace, the angles between those two points at two other
points on the same side of that subspace have the same sign. -/
theorem _root_.AffineSubspace.SSameSide.oangle_sign_eq {s : AffineSubspace ℝ P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SSameSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  by_cases h : p₁ = p₂; · simp [h]
  -- ⊢ Real.Angle.sign (∡ p₁ p₄ p₂) = Real.Angle.sign (∡ p₁ p₃ p₂)
                          -- 🎉 no goals
  let sp : Set (P × P × P) := (fun p : P => (p₁, p, p₂)) '' {p | s.SSameSide p₃ p}
  -- ⊢ Real.Angle.sign (∡ p₁ p₄ p₂) = Real.Angle.sign (∡ p₁ p₃ p₂)
  have hc : IsConnected sp := (isConnected_setOf_sSameSide hp₃p₄.2.1 hp₃p₄.nonempty).image _
    (continuous_const.prod_mk (Continuous.Prod.mk_left _)).continuousOn
  have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) sp := by
    refine' ContinuousAt.continuousOn fun p hp => continuousAt_oangle _ _
    all_goals
      simp_rw [Set.mem_image, Set.mem_setOf] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      dsimp only
      rintro rfl
    · exact hp'.2.2 hp₁
    · exact hp'.2.2 hp₂
  have hsp : ∀ p : P × P × P, p ∈ sp → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π := by
    intro p hp
    simp_rw [Set.mem_image, Set.mem_setOf] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    dsimp only
    rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
    exact affineIndependent_of_ne_of_mem_of_not_mem_of_mem h hp₁ hp'.2.2 hp₂
  have hp₃ : (p₁, p₃, p₂) ∈ sp :=
    Set.mem_image_of_mem _ (sSameSide_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩)
  have hp₄ : (p₁, p₄, p₂) ∈ sp := Set.mem_image_of_mem _ hp₃p₄
  -- ⊢ Real.Angle.sign (∡ p₁ p₄ p₂) = Real.Angle.sign (∡ p₁ p₃ p₂)
  convert Real.Angle.sign_eq_of_continuousOn hc hf hsp hp₃ hp₄
  -- 🎉 no goals
#align affine_subspace.s_same_side.oangle_sign_eq AffineSubspace.SSameSide.oangle_sign_eq

/-- Given two points in an affine subspace, the angles between those two points at two other
points on opposite sides of that subspace have opposite signs. -/
theorem _root_.AffineSubspace.SOppSide.oangle_sign_eq_neg {s : AffineSubspace ℝ P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SOppSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign := by
  have hp₁p₃ : p₁ ≠ p₃ := by rintro rfl; exact hp₃p₄.left_not_mem hp₁
  -- ⊢ Real.Angle.sign (∡ p₁ p₄ p₂) = -Real.Angle.sign (∡ p₁ p₃ p₂)
  rw [← (hp₃p₄.symm.trans (sOppSide_pointReflection hp₁ hp₃p₄.left_not_mem)).oangle_sign_eq hp₁ hp₂,
    ← oangle_rotate_sign p₁, ← oangle_rotate_sign p₁, oangle_swap₁₃_sign,
    (sbtw_pointReflection_of_ne ℝ hp₁p₃).symm.oangle_sign_eq _]
#align affine_subspace.s_opp_side.oangle_sign_eq_neg AffineSubspace.SOppSide.oangle_sign_eq_neg

end EuclideanGeometry
