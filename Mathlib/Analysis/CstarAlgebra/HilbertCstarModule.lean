/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Hilbert C⋆-modules

FIXME

## Main declarations

## Implementation note

FIXME
-/

open scoped ComplexOrder RightActions

/-- A *Hilbert C⋆-module* is a complex linear space `E` endowed with a right `A`-module structure
(where `A` is typically a C⋆-algebra) and an inner product `⟪x, y⟫_A` which satisfies the
following properties. -/
class HilbertCstarModule (A : outParam <| Type*) (E : Type*) [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul Aᵐᵒᵖ E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x} {y} {z} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x} : 0 ≤ inner x x
  inner_self {x} : inner x x = 0 ↔ x = 0
  inner_op_smul_right {a : A} {x y : E} : inner x (y <• a) = inner x y * a
  inner_smul_right_complex {z : ℂ} {x} {y} : inner x (z • y) = z • inner x y
  star_inner x y : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self x : ‖x‖ = √‖inner x x‖

attribute [simp] HilbertCstarModule.inner_add_right HilbertCstarModule.star_inner
  HilbertCstarModule.inner_op_smul_right HilbertCstarModule.inner_smul_right_complex

namespace HilbertCstarModule

section general

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [AddCommGroup E] [Module ℂ A]
  [Module ℂ E] [PartialOrder A] [SMul Aᵐᵒᵖ E] [StarModule ℂ A] [Norm A] [Norm E]
  [HilbertCstarModule A E]

local notation "⟪" x ", " y "⟫" => inner (𝕜 := A) x y

@[simp]
lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  rw [← star_star (r := ⟪x + y, z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp]
lemma inner_op_smul_left {a : A} {x y : E} : ⟪x <• a, y⟫ = star a * ⟪x, y⟫ := by
  rw [← star_inner]; simp

@[simp]
lemma inner_smul_left_complex {z : ℂ} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x, y⟫ := by
  rw [← star_inner]
  simp

@[simp]
lemma inner_smul_left_real {z : ℝ} {x y : E} : ⟪z • x, y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • x = (z : ℂ) • x := by simp
  rw [h₁, ← star_inner, inner_smul_right_complex]
  simp

@[simp]
lemma inner_smul_right_real {z : ℝ} {x y : E} : ⟪x, z • y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • y = (z : ℂ) • y := by simp
  rw [h₁, ← star_inner, inner_smul_left_complex]
  simp

/-- The function `y ↦ ⟪x, y⟫` bundled as a linear map. -/
def innerRightL (x : E) : E →ₗ[ℂ] A where
  toFun y := ⟪x, y⟫
  map_add' z y := by simp
  map_smul' z y := by simp

/-- The function `y ↦ ⟪y, x⟫` bundled as a conjugate-linear map. -/
def innerLeftL (x : E) : E →ₗ⋆[ℂ] A where
  toFun y := ⟪y, x⟫
  map_add' z y := by simp
  map_smul' z y := by simp

lemma inner_eq_innerRightL (x y : E) : ⟪x, y⟫ = innerRightL x y := rfl

lemma inner_eq_innerLeftL (x y : E) : ⟪x, y⟫ = innerLeftL y x := rfl

@[simp] lemma inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by simp [inner_eq_innerRightL]
@[simp] lemma inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by simp [inner_eq_innerLeftL]
@[simp] lemma inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ := by simp [inner_eq_innerRightL]
@[simp] lemma inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ := by simp [inner_eq_innerLeftL]
@[simp] lemma inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [inner_eq_innerRightL]
@[simp] lemma inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [inner_eq_innerLeftL]

@[simp]
lemma inner_sum_right {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : E} {y : ι → E} :
    ⟪x, ∑ i ∈ s, y i⟫ = ∑ i ∈ s, ⟪x, y i⟫ := by
  induction s using Finset.induction_on
  case empty => simp
  case insert a t a_notmem_t hbase =>
    simp_rw [Finset.sum_insert a_notmem_t]
    simp only [inner_add_right, hbase]

@[simp]
lemma inner_sum_left {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → E} {y : E} :
    ⟪∑ i ∈ s, x i, y⟫ = ∑ i ∈ s, ⟪x i, y⟫ := by rw [← star_inner y]; simp

@[simp]
lemma isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint ⟪x, x⟫_A := star_inner _ _

end general

section normed

variable {A E : Type*} [NonUnitalNormedRing A] [StarRing A] [CstarRing A] [PartialOrder A]
  [CompleteSpace A] [StarOrderedRing A] [AddCommGroup E] [NormedSpace ℂ A]
  [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E]
  [StarModule ℂ A] [hsm : HilbertCstarModule A E] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

local notation "⟪" x ", " y "⟫" => inner (𝕜 := A) x y

variable (A) in
/-- The norm associated with a Hilbert C⋆-module. It is not registered as a norm, since a type
might already have a norm defined on it. -/
noncomputable def norm : Norm E where
  norm x := Real.sqrt ‖⟪x, x⟫‖

--attribute [local instance] norm

--lemma norm_eq_sqrt_norm_inner_self {x : E} : ‖x‖ = Real.sqrt ‖⟪x, x⟫‖ := rfl

lemma inner_self_eq_norm_sq {x : E} : ‖⟪x, x⟫‖ = ‖x‖ ^ 2 := by simp [norm_eq_sqrt_norm_inner_self]

@[simp] lemma norm_zero : ‖(0 : E)‖ = 0 := by simp [norm_eq_sqrt_norm_inner_self]

@[simp]
lemma norm_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0 :=
  ⟨fun h => by simpa [norm_eq_sqrt_norm_inner_self, inner_self] using h, fun h => by simp [norm, h]⟩

lemma norm_nonneg {x : E} : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self]; positivity

lemma norm_pos {x : E} (hx : x ≠ 0) : 0 < ‖x‖ := by
  simp only [norm_eq_sqrt_norm_inner_self, Real.sqrt_pos, norm_pos_iff]
  intro H
  rw [inner_self] at H
  exact hx H

@[simp]
lemma norm_neg {x : E} : ‖-x‖ = ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self]

lemma norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖ := by simp [norm_eq_sqrt_norm_inner_self]

lemma smul_nonneg_iff {a : A} {r : ℝ} (hr : 0 < r) : 0 ≤ a ↔ 0 ≤ r • a := by
  refine ⟨smul_nonneg (le_of_lt hr), fun hra => ?_⟩
  have : a = r⁻¹ • (r • a) := by
    rw [smul_smul, inv_mul_cancel]
    exact (MulAction.one_smul a).symm
    exact Ne.symm (ne_of_lt hr)
  rw [this]
  refine smul_nonneg ?_ hra
  positivity

@[simp]
protected lemma norm_smul {r : ℝ} {x : E} : ‖r • x‖ = ‖r‖ * ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self, norm_eq_sqrt_norm_inner_self x]
  simp only [inner_smul_left_real, inner_smul_right_real, _root_.norm_smul, ← mul_assoc]
  rw [Real.sqrt_mul (by positivity)]
  congr
  exact Real.sqrt_mul_self (by positivity)

lemma cauchy_schwarz₁ (x y : E) : ⟪y, x⟫ * ⟪x, y⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫ := by
  rcases eq_or_ne x 0 with h|h
  · simp [h]
  · have h₁ : ∀ (a : A),
        (0 : A) ≤ ‖x‖ ^ 2 • (star a * a) - ‖x‖ ^ 2 • (⟪y, x⟫ * a)
                  - ‖x‖ ^ 2 • (star a * ⟪x, y⟫) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := fun a => by
      calc (0 : A) ≤ ⟪x <• a - ‖x‖ ^ 2 • y, x <• a - ‖x‖ ^ 2 • y⟫_A := by
                      exact inner_self_nonneg
            _ = star a * ⟪x, x⟫ * a - ‖x‖ ^ 2 • (⟪y, x⟫ * a)
                  - ‖x‖ ^ 2 • (star a * ⟪x, y⟫) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      simp only [inner_sub_right, inner_op_smul_right, inner_sub_left,
                        inner_op_smul_left, inner_smul_left_real, sub_mul, smul_mul_assoc,
                        inner_smul_right_real, smul_sub]
                      abel
            _ ≤ ‖x‖ ^ 2 • (star a * a) - ‖x‖ ^ 2 • (⟪y, x⟫ * a)
                  - ‖x‖ ^ 2 • (star a * ⟪x, y⟫) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      gcongr
                      calc _ ≤ ‖⟪x, x⟫_A‖ • (star a * a) := CstarRing.conjugate_le_norm_smul
                        _ = (Real.sqrt ‖⟪x, x⟫_A‖) ^ 2 • (star a * a) := by
                                  congr
                                  have : 0 ≤ ‖⟪x, x⟫_A‖ := by positivity
                                  rw [Real.sq_sqrt this]
                        _ = ‖x‖ ^ 2 • (star a * a) := by rw [← norm_eq_sqrt_norm_inner_self]
    specialize h₁ ⟪x, y⟫
    simp only [star_inner, sub_self, zero_sub, le_neg_add_iff_add_le, add_zero] at h₁
    rwa [smul_le_smul_iff_of_pos_left (pow_pos (norm_pos h) _)] at h₁

lemma cauchy_schwarz₂ (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  have := calc ‖⟪x, y⟫‖ ^ 2 = ‖⟪y, x⟫ * ⟪x, y⟫‖ := by
                rw [← star_inner x, CstarRing.norm_star_mul_self, pow_two]
    _ ≤ ‖‖x‖^ 2 • ⟪y, y⟫‖ := by
                refine CstarRing.norm_le_norm_of_nonneg_of_le ?_ (cauchy_schwarz₁ x y)
                rw [← star_inner x]
                exact star_mul_self_nonneg ⟪x, y⟫_A
    _ = ‖x‖ ^ 2 * ‖⟪y, y⟫‖ := by simp [_root_.norm_smul]
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
                simp only [norm_eq_sqrt_norm_inner_self, _root_.norm_nonneg, Real.sq_sqrt]
    _ = (‖x‖ * ‖y‖) ^ 2 := by simp only [mul_pow]
  refine (pow_le_pow_iff_left (R := ℝ) (_root_.norm_nonneg ⟪x, y⟫_A) ?_ (by norm_num)).mp this
  exact mul_nonneg norm_nonneg norm_nonneg

lemma norm_triangle (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    calc _ ≤ ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
          simp only [norm_eq_sqrt_norm_inner_self, inner_add_right, inner_add_left, ← add_assoc,
            _root_.norm_nonneg, Real.sq_sqrt]
          exact norm_add₃_le _ _ _
      _ ≤ ‖⟪x, x⟫‖ + ‖⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖⟪x, x⟫‖ + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖⟪y, y⟫‖ := by
          gcongr <;> exact cauchy_schwarz₂ _ _
      _ = ‖x‖ ^ 2 + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
          simp [norm_eq_sqrt_norm_inner_self]
      _ = (‖x‖ + ‖y‖) ^ 2 := by simp only [add_pow_two, add_left_inj]; ring
  refine (pow_le_pow_iff_left norm_nonneg ?_ (by norm_num)).mp h
  exact add_nonneg norm_nonneg norm_nonneg

/-- This allows us to get `NormedAddCommGroup` and `NormedSpace` instances on `E` via
`NormedAddCommGroup.ofCore` and `NormedSpace.ofCore`. -/
lemma normedSpaceCore : NormedSpace.Core ℂ E where
  norm_nonneg x := norm_nonneg
  norm_eq_zero_iff x := norm_zero_iff x
  norm_smul c x := by simp [norm_eq_sqrt_norm_inner_self, _root_.norm_smul, ← mul_assoc]
  norm_triangle x y := norm_triangle x y

end normed

end HilbertCstarModule
