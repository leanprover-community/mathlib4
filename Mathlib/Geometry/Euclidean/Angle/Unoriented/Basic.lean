/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

#align_import geometry.euclidean.angle.unoriented.basic from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Angles between vectors

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `InnerProductGeometry.angle` is the undirected angle between two vectors.

-/


assert_not_exists HasFDerivAt

assert_not_exists ConformalAt

noncomputable section

open Real Set

open BigOperators

open Real

open RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. See `Orientation.oangle` for the corresponding oriented angle
definition. -/
def angle (x y : V) : ℝ :=
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))
#align inner_product_geometry.angle InnerProductGeometry.angle

theorem continuousAt_angle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
    ContinuousAt (fun y : V × V => angle y.1 y.2) x :=
  Real.continuous_arccos.continuousAt.comp <|
    continuous_inner.continuousAt.div
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd)).continuousAt
      (by simp [hx1, hx2])
          -- 🎉 no goals
#align inner_product_geometry.continuous_at_angle InnerProductGeometry.continuousAt_angle

theorem angle_smul_smul {c : ℝ} (hc : c ≠ 0) (x y : V) : angle (c • x) (c • y) = angle x y := by
  have : c * c ≠ 0 := mul_ne_zero hc hc
  -- ⊢ angle (c • x) (c • y) = angle x y
  rw [angle, angle, real_inner_smul_left, inner_smul_right, norm_smul, norm_smul, Real.norm_eq_abs,
    mul_mul_mul_comm _ ‖x‖, abs_mul_abs_self, ← mul_assoc c c, mul_div_mul_left _ _ this]
#align inner_product_geometry.angle_smul_smul InnerProductGeometry.angle_smul_smul

@[simp]
theorem _root_.LinearIsometry.angle_map {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F) (u v : E) :
    angle (f u) (f v) = angle u v := by
  rw [angle, angle, f.inner_map_map, f.norm_map, f.norm_map]
  -- 🎉 no goals
#align linear_isometry.angle_map LinearIsometry.angle_map

@[simp, norm_cast]
theorem _root_.Submodule.angle_coe {s : Submodule ℝ V} (x y : s) :
    angle (x : V) (y : V) = angle x y :=
  s.subtypeₗᵢ.angle_map x y
#align submodule.angle_coe Submodule.angle_coe

/-- The cosine of the angle between two vectors. -/
theorem cos_angle (x y : V) : Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
  Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2
#align inner_product_geometry.cos_angle InnerProductGeometry.cos_angle

/-- The angle between two vectors does not depend on their order. -/
theorem angle_comm (x y : V) : angle x y = angle y x := by
  unfold angle
  -- ⊢ arccos (inner x y / (‖x‖ * ‖y‖)) = arccos (inner y x / (‖y‖ * ‖x‖))
  rw [real_inner_comm, mul_comm]
  -- 🎉 no goals
#align inner_product_geometry.angle_comm InnerProductGeometry.angle_comm

/-- The angle between the negation of two vectors. -/
@[simp]
theorem angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y := by
  unfold angle
  -- ⊢ arccos (inner (-x) (-y) / (‖-x‖ * ‖-y‖)) = arccos (inner x y / (‖x‖ * ‖y‖))
  rw [inner_neg_neg, norm_neg, norm_neg]
  -- 🎉 no goals
#align inner_product_geometry.angle_neg_neg InnerProductGeometry.angle_neg_neg

/-- The angle between two vectors is nonnegative. -/
theorem angle_nonneg (x y : V) : 0 ≤ angle x y :=
  Real.arccos_nonneg _
#align inner_product_geometry.angle_nonneg InnerProductGeometry.angle_nonneg

/-- The angle between two vectors is at most π. -/
theorem angle_le_pi (x y : V) : angle x y ≤ π :=
  Real.arccos_le_pi _
#align inner_product_geometry.angle_le_pi InnerProductGeometry.angle_le_pi

/-- The angle between a vector and the negation of another vector. -/
theorem angle_neg_right (x y : V) : angle x (-y) = π - angle x y := by
  unfold angle
  -- ⊢ arccos (inner x (-y) / (‖x‖ * ‖-y‖)) = π - arccos (inner x y / (‖x‖ * ‖y‖))
  rw [← Real.arccos_neg, norm_neg, inner_neg_right, neg_div]
  -- 🎉 no goals
#align inner_product_geometry.angle_neg_right InnerProductGeometry.angle_neg_right

/-- The angle between the negation of a vector and another vector. -/
theorem angle_neg_left (x y : V) : angle (-x) y = π - angle x y := by
  rw [← angle_neg_neg, neg_neg, angle_neg_right]
  -- 🎉 no goals
#align inner_product_geometry.angle_neg_left InnerProductGeometry.angle_neg_left

/-- The angle between the zero vector and a vector. -/
@[simp]
theorem angle_zero_left (x : V) : angle 0 x = π / 2 := by
  unfold angle
  -- ⊢ arccos (inner 0 x / (‖0‖ * ‖x‖)) = π / 2
  rw [inner_zero_left, zero_div, Real.arccos_zero]
  -- 🎉 no goals
#align inner_product_geometry.angle_zero_left InnerProductGeometry.angle_zero_left

/-- The angle between a vector and the zero vector. -/
@[simp]
theorem angle_zero_right (x : V) : angle x 0 = π / 2 := by
  unfold angle
  -- ⊢ arccos (inner x 0 / (‖x‖ * ‖0‖)) = π / 2
  rw [inner_zero_right, zero_div, Real.arccos_zero]
  -- 🎉 no goals
#align inner_product_geometry.angle_zero_right InnerProductGeometry.angle_zero_right

/-- The angle between a nonzero vector and itself. -/
@[simp]
theorem angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 := by
  unfold angle
  -- ⊢ arccos (inner x x / (‖x‖ * ‖x‖)) = 0
  rw [← real_inner_self_eq_norm_mul_norm, div_self (inner_self_ne_zero.2 hx : ⟪x, x⟫ ≠ 0),
    Real.arccos_one]
#align inner_product_geometry.angle_self InnerProductGeometry.angle_self

/-- The angle between a nonzero vector and its negation. -/
@[simp]
theorem angle_self_neg_of_nonzero {x : V} (hx : x ≠ 0) : angle x (-x) = π := by
  rw [angle_neg_right, angle_self hx, sub_zero]
  -- 🎉 no goals
#align inner_product_geometry.angle_self_neg_of_nonzero InnerProductGeometry.angle_self_neg_of_nonzero

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp]
theorem angle_neg_self_of_nonzero {x : V} (hx : x ≠ 0) : angle (-x) x = π := by
  rw [angle_comm, angle_self_neg_of_nonzero hx]
  -- 🎉 no goals
#align inner_product_geometry.angle_neg_self_of_nonzero InnerProductGeometry.angle_neg_self_of_nonzero

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle x (r • y) = angle x y := by
  unfold angle
  -- ⊢ arccos (inner x (r • y) / (‖x‖ * ‖r • y‖)) = arccos (inner x y / (‖x‖ * ‖y‖))
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    mul_comm _ r, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hr)]
#align inner_product_geometry.angle_smul_right_of_pos InnerProductGeometry.angle_smul_right_of_pos

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle (r • x) y = angle x y := by
  rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]
  -- 🎉 no goals
#align inner_product_geometry.angle_smul_left_of_pos InnerProductGeometry.angle_smul_left_of_pos

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
    angle x (r • y) = angle x (-y) := by
  rw [← neg_neg r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr),
    angle_neg_right]
#align inner_product_geometry.angle_smul_right_of_neg InnerProductGeometry.angle_smul_right_of_neg

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) : angle (r • x) y = angle (-x) y := by
  rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]
  -- 🎉 no goals
#align inner_product_geometry.angle_smul_left_of_neg InnerProductGeometry.angle_smul_left_of_neg

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem cos_angle_mul_norm_mul_norm (x y : V) : Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫ := by
  rw [cos_angle, div_mul_cancel_of_imp]
  -- ⊢ ‖x‖ * ‖y‖ = 0 → inner x y = 0
  simp (config := { contextual := true }) [or_imp]
  -- 🎉 no goals
#align inner_product_geometry.cos_angle_mul_norm_mul_norm InnerProductGeometry.cos_angle_mul_norm_mul_norm

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem sin_angle_mul_norm_mul_norm (x y : V) :
    Real.sin (angle x y) * (‖x‖ * ‖y‖) = Real.sqrt (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) := by
  unfold angle
  -- ⊢ sin (arccos (inner x y / (‖x‖ * ‖y‖))) * (‖x‖ * ‖y‖) = sqrt (inner x x * inn …
  rw [Real.sin_arccos, ← Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
    ← Real.sqrt_mul' _ (mul_self_nonneg _), sq,
    Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm]
  by_cases h : ‖x‖ * ‖y‖ = 0
  -- ⊢ sqrt ((1 - inner x y / (‖x‖ * ‖y‖) * (inner x y / (‖x‖ * ‖y‖))) * (‖x‖ * ‖y‖ …
  · rw [show ‖x‖ * ‖x‖ * (‖y‖ * ‖y‖) = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) by ring, h, mul_zero,
      mul_zero, zero_sub]
    cases' eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy
    -- ⊢ sqrt 0 = sqrt (-(inner x y * inner x y))
    · rw [norm_eq_zero] at hx
      -- ⊢ sqrt 0 = sqrt (-(inner x y * inner x y))
      rw [hx, inner_zero_left, zero_mul, neg_zero]
      -- 🎉 no goals
    · rw [norm_eq_zero] at hy
      -- ⊢ sqrt 0 = sqrt (-(inner x y * inner x y))
      rw [hy, inner_zero_right, zero_mul, neg_zero]
      -- 🎉 no goals
  · field_simp [h]
    -- ⊢ sqrt (‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) - inner x y * inner x y) = sqrt (‖x‖ * ‖x‖ * ( …
    ring_nf
    -- 🎉 no goals
#align inner_product_geometry.sin_angle_mul_norm_mul_norm InnerProductGeometry.sin_angle_mul_norm_mul_norm

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
theorem angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_one_iff, Real.arccos_eq_zero, LE.le.le_iff_eq,
    eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2
  -- 🎉 no goals
#align inner_product_geometry.angle_eq_zero_iff InnerProductGeometry.angle_eq_zero_iff

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
theorem angle_eq_pi_iff {x y : V} : angle x y = π ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_neg_one_iff, Real.arccos_eq_pi, LE.le.le_iff_eq]
  -- ⊢ -1 ≤ inner x y / (‖x‖ * ‖y‖)
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
  -- 🎉 no goals
#align inner_product_geometry.angle_eq_pi_iff InnerProductGeometry.angle_eq_pi_iff

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
    angle x z + angle y z = π := by
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩
  -- ⊢ angle x z + angle (r • x) z = π
  rw [angle_smul_left_of_neg x z hr, angle_neg_left, add_sub_cancel'_right]
  -- 🎉 no goals
#align inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi InnerProductGeometry.angle_add_angle_eq_pi_of_angle_eq_pi

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
theorem inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
  Iff.symm <| by simp (config := { contextual := true }) [angle, or_imp]
                 -- 🎉 no goals
#align inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two

/-- If the angle between two vectors is π, the inner product equals the negative product
of the norms. -/
theorem inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by
  simp [← cos_angle_mul_norm_mul_norm, h]
  -- 🎉 no goals
#align inner_product_geometry.inner_eq_neg_mul_norm_of_angle_eq_pi InnerProductGeometry.inner_eq_neg_mul_norm_of_angle_eq_pi

/-- If the angle between two vectors is 0, the inner product equals the product of the norms. -/
theorem inner_eq_mul_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ⟪x, y⟫ = ‖x‖ * ‖y‖ := by
  simp [← cos_angle_mul_norm_mul_norm, h]
  -- 🎉 no goals
#align inner_product_geometry.inner_eq_mul_norm_of_angle_eq_zero InnerProductGeometry.inner_eq_mul_norm_of_angle_eq_zero

/-- The inner product of two non-zero vectors equals the negative product of their norms
if and only if the angle between the two vectors is π. -/
theorem inner_eq_neg_mul_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) ↔ angle x y = π := by
  refine' ⟨fun h => _, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  -- ⊢ angle x y = π
  have h₁ : ‖x‖ * ‖y‖ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  -- ⊢ angle x y = π
  rw [angle, h, neg_div, div_self h₁, Real.arccos_neg_one]
  -- 🎉 no goals
#align inner_product_geometry.inner_eq_neg_mul_norm_iff_angle_eq_pi InnerProductGeometry.inner_eq_neg_mul_norm_iff_angle_eq_pi

/-- The inner product of two non-zero vectors equals the product of their norms
if and only if the angle between the two vectors is 0. -/
theorem inner_eq_mul_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ angle x y = 0 := by
  refine' ⟨fun h => _, inner_eq_mul_norm_of_angle_eq_zero⟩
  -- ⊢ angle x y = 0
  have h₁ : ‖x‖ * ‖y‖ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  -- ⊢ angle x y = 0
  rw [angle, h, div_self h₁, Real.arccos_one]
  -- 🎉 no goals
#align inner_product_geometry.inner_eq_mul_norm_iff_angle_eq_zero InnerProductGeometry.inner_eq_mul_norm_iff_angle_eq_zero

/-- If the angle between two vectors is π, the norm of their difference equals
the sum of their norms. -/
theorem norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ‖x - y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_sub_pow_two_real, inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring
  -- 🎉 no goals
#align inner_product_geometry.norm_sub_eq_add_norm_of_angle_eq_pi InnerProductGeometry.norm_sub_eq_add_norm_of_angle_eq_pi

/-- If the angle between two vectors is 0, the norm of their sum equals
the sum of their norms. -/
theorem norm_add_eq_add_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_add_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h]
  ring
  -- 🎉 no goals
#align inner_product_geometry.norm_add_eq_add_norm_of_angle_eq_zero InnerProductGeometry.norm_add_eq_add_norm_of_angle_eq_zero

/-- If the angle between two vectors is 0, the norm of their difference equals
the absolute value of the difference of their norms. -/
theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rw [← sq_eq_sq (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖)), norm_sub_pow_two_real,
    inner_eq_mul_norm_of_angle_eq_zero h, sq_abs (‖x‖ - ‖y‖)]
  ring
  -- 🎉 no goals
#align inner_product_geometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero InnerProductGeometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero

/-- The norm of the difference of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is π. -/
theorem norm_sub_eq_add_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x - y‖ = ‖x‖ + ‖y‖ ↔ angle x y = π := by
  refine' ⟨fun h => _, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  -- ⊢ angle x y = π
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy]
  -- ⊢ inner x y = -(‖x‖ * ‖y‖)
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  -- ⊢ inner x y = -(‖x‖ * ‖y‖)
  rw [← sq_eq_sq hxy₁ hxy₂, norm_sub_pow_two_real] at h
  -- ⊢ inner x y = -(‖x‖ * ‖y‖)
  calc
    ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y‖ ^ 2 - (‖x‖ + ‖y‖) ^ 2) / 2 := by linarith
    _ = -(‖x‖ * ‖y‖) := by ring
#align inner_product_geometry.norm_sub_eq_add_norm_iff_angle_eq_pi InnerProductGeometry.norm_sub_eq_add_norm_iff_angle_eq_pi

/-- The norm of the sum of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is 0. -/
theorem norm_add_eq_add_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔ angle x y = 0 := by
  refine' ⟨fun h => _, norm_add_eq_add_norm_of_angle_eq_zero⟩
  -- ⊢ angle x y = 0
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  -- ⊢ inner x y = ‖x‖ * ‖y‖
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x + y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  -- ⊢ inner x y = ‖x‖ * ‖y‖
  rw [← sq_eq_sq hxy₁ hxy₂, norm_add_pow_two_real] at h
  -- ⊢ inner x y = ‖x‖ * ‖y‖
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by linarith
    _ = ‖x‖ * ‖y‖ := by ring
#align inner_product_geometry.norm_add_eq_add_norm_iff_angle_eq_zero InnerProductGeometry.norm_add_eq_add_norm_iff_angle_eq_zero

/-- The norm of the difference of two non-zero vectors equals the absolute value
of the difference of their norms if and only the angle between the two vectors is 0. -/
theorem norm_sub_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| ↔ angle x y = 0 := by
  refine' ⟨fun h => _, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  -- ⊢ angle x y = 0
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  -- ⊢ inner x y = ‖x‖ * ‖y‖
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 := by
    rw [h]
    exact sq_abs (‖x‖ - ‖y‖)
  rw [norm_sub_pow_two_real] at h1
  -- ⊢ inner x y = ‖x‖ * ‖y‖
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by linarith
    _ = ‖x‖ * ‖y‖ := by ring
#align inner_product_geometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero InnerProductGeometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero

/-- The norm of the sum of two vectors equals the norm of their difference if and only if
the angle between them is π/2. -/
theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ = ‖x - y‖ ↔ angle x y = π / 2 := by
  rw [← sq_eq_sq (norm_nonneg (x + y)) (norm_nonneg (x - y)),
    ← inner_eq_zero_iff_angle_eq_pi_div_two x y, norm_add_pow_two_real, norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith
  -- ⊢ ‖x‖ ^ 2 + 2 * inner x y + ‖y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner x y + ‖y‖ ^ 2 → inne …
                  -- ⊢ inner x y = 0
                  -- ⊢ ‖x‖ ^ 2 + 2 * inner x y + ‖y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner x y + ‖y‖ ^ 2
                              -- 🎉 no goals
                              -- 🎉 no goals
#align inner_product_geometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two InnerProductGeometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two

/-- The cosine of the angle between two vectors is 1 if and only if the angle is 0. -/
theorem cos_eq_one_iff_angle_eq_zero : cos (angle x y) = 1 ↔ angle x y = 0 := by
  rw [← cos_zero]
  -- ⊢ cos (angle x y) = cos 0 ↔ angle x y = 0
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)
  -- 🎉 no goals
#align inner_product_geometry.cos_eq_one_iff_angle_eq_zero InnerProductGeometry.cos_eq_one_iff_angle_eq_zero

/-- The cosine of the angle between two vectors is 0 if and only if the angle is π / 2. -/
theorem cos_eq_zero_iff_angle_eq_pi_div_two : cos (angle x y) = 0 ↔ angle x y = π / 2 := by
  rw [← cos_pi_div_two]
  -- ⊢ cos (angle x y) = cos (π / 2) ↔ angle x y = π / 2
  apply injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  -- ⊢ π / 2 ∈ Icc 0 π
  constructor <;> linarith [pi_pos]
  -- ⊢ 0 ≤ π / 2
                  -- 🎉 no goals
                  -- 🎉 no goals
#align inner_product_geometry.cos_eq_zero_iff_angle_eq_pi_div_two InnerProductGeometry.cos_eq_zero_iff_angle_eq_pi_div_two

/-- The cosine of the angle between two vectors is -1 if and only if the angle is π. -/
theorem cos_eq_neg_one_iff_angle_eq_pi : cos (angle x y) = -1 ↔ angle x y = π := by
  rw [← cos_pi]
  -- ⊢ cos (angle x y) = cos π ↔ angle x y = π
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)
  -- 🎉 no goals
#align inner_product_geometry.cos_eq_neg_one_iff_angle_eq_pi InnerProductGeometry.cos_eq_neg_one_iff_angle_eq_pi

/-- The sine of the angle between two vectors is 0 if and only if the angle is 0 or π. -/
theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi :
    sin (angle x y) = 0 ↔ angle x y = 0 ∨ angle x y = π := by
  rw [sin_eq_zero_iff_cos_eq, cos_eq_one_iff_angle_eq_zero, cos_eq_neg_one_iff_angle_eq_pi]
  -- 🎉 no goals
#align inner_product_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi InnerProductGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/-- The sine of the angle between two vectors is 1 if and only if the angle is π / 2. -/
theorem sin_eq_one_iff_angle_eq_pi_div_two : sin (angle x y) = 1 ↔ angle x y = π / 2 := by
  refine' ⟨fun h => _, fun h => by rw [h, sin_pi_div_two]⟩
  -- ⊢ angle x y = π / 2
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two, ← abs_eq_zero, abs_cos_eq_sqrt_one_sub_sin_sq, h]
  -- ⊢ sqrt (1 - 1 ^ 2) = 0
  simp
  -- 🎉 no goals
#align inner_product_geometry.sin_eq_one_iff_angle_eq_pi_div_two InnerProductGeometry.sin_eq_one_iff_angle_eq_pi_div_two

end InnerProductGeometry
