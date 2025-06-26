/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.

Several facts about the real trigonometric functions have the proofs deferred here, rather than
`Analysis.SpecialFunctions.Trigonometric.Basic`,
as they are most easily proved by appealing to the corresponding fact for complex trigonometric
functions, or require additional imports which are not available in that file.
-/


noncomputable section

namespace Complex

open Set Filter

open scoped Real

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ θ ≡ π / 2 [PMOD ↑π] := by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 := by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero, zero_mul,
      add_eq_zero_iff_eq_neg, neg_eq_neg_one_mul, ← div_eq_iff (exp_ne_zero _), ← exp_sub]
    ring_nf
  rw [cos, h, ← exp_pi_mul_I, exp_eq_exp_iff_modEq, mul_right_comm]
  have : IsRegular (2 * I) := isRegular_of_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
  conv_rhs => rw [← this.left.mul_modEq_mul_left]
  congr! 1
  · ring
  · field_simp; ring

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ θ ≡ 0 [PMOD ↑π] := by
  rw [← Complex.cos_sub_pi_div_two, cos_eq_zero_iff, AddCommGroup.sub_modEq_iff_modEq_add]
  exact AddCommGroup.ModEq.congr (by rfl) (by simp)

/-- The tangent of a complex number is equal to zero
iff this number is equal to `k * π / 2` for an integer `k`.

Note that this lemma takes into account that we use zero as the junk value for division by zero.
See also `Complex.tan_eq_zero_iff'`. -/
theorem tan_eq_zero_iff {θ : ℂ} : tan θ = 0 ↔ θ ≡ 0 [PMOD (π / 2 : ℂ)] := by
  rw [tan, div_eq_zero_iff, ← mul_eq_zero, ← mul_right_inj' two_ne_zero, mul_zero,
    ← mul_assoc, ← sin_two_mul, sin_eq_zero_iff, ← AddCommGroup.mul_modEq_mul_left two_ne_zero,
    mul_zero]

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 := by
  rw [ne_eq, cos_eq_zero_iff, AddCommGroup.modEq_comm, AddCommGroup.modEq_iff_eq_add_zsmul,
    not_exists]
  field_simp; ring_nf

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π := by
  rw [ne_eq, sin_eq_zero_iff, AddCommGroup.modEq_zero_left_iff_eq_zsmul, not_exists]
  simp_rw [zsmul_eq_mul]

theorem tan_ne_zero_iff {θ : ℂ} : tan θ ≠ 0 ↔ ∀ k : ℤ, (k * π / 2 : ℂ) ≠ θ := by
  rw [ne_eq, tan_eq_zero_iff, AddCommGroup.modEq_zero_left_iff_eq_zsmul, not_exists]
  simp_rw [zsmul_eq_mul, mul_div_assoc, ne_comm]

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (.symm <| by use n; simp [zsmul_eq_mul, mul_div_assoc])

/-- If the tangent of a complex number is well-defined,
then it is equal to zero iff the number is equal to `k * π` for an integer `k`.

See also `Complex.tan_eq_zero_iff` for a version that takes into account junk values of `θ`. -/
theorem tan_eq_zero_iff' {θ : ℂ} (hθ : cos θ ≠ 0) : tan θ = 0 ↔ θ ≡ 0 [PMOD (π : ℂ)] := by
  simp only [tan, hθ, div_eq_zero_iff, sin_eq_zero_iff]; simp [eq_comm]

theorem cos_eq_cos_iff {x y : ℂ} :
    cos x = cos y ↔ x ≡ y [PMOD (2 * π : ℂ)] ∨ x ≡ -y [PMOD (2 * π : ℂ)] :=
  calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by norm_num : (2 : ℂ) ≠ 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_comm
    _ ↔ _ := by
      field_simp [sin_eq_zero_iff, (by norm_num : -(2 : ℂ) ≠ 0),
        sub_eq_iff_eq_add, mul_comm (2 : ℂ), mul_right_comm _ (2 : ℂ)]
      rw [← zero_div 2, AddCommGroup.div_modEq_div two_ne_zero,
        AddCommGroup.div_modEq_div two_ne_zero,
        AddCommGroup.sub_modEq_iff_modEq_add, zero_add, ← zero_sub,
        AddCommGroup.modEq_sub_iff_add_modEq]


theorem sin_eq_sin_iff {x y : ℂ} :
    sin x = sin y ↔ x ≡ y [PMOD (2 * π : ℂ)] ∨ x ≡ π - y [PMOD (2 * π : ℂ)] := by
  simp_rw [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, AddCommGroup.ModEq.sub_iff_right .rfl,
    neg_sub, AddCommGroup.sub_modEq_iff_modEq_add]
  ring_nf

theorem cos_eq_one_iff {x : ℂ} : cos x = 1 ↔ x ≡ 0 [PMOD (2 * π : ℂ)] := by
  rw [← cos_zero, cos_eq_cos_iff, neg_zero, or_self]

theorem cos_eq_neg_one_iff {x : ℂ} : cos x = -1 ↔ x ≡ π [PMOD (2 * π : ℂ)] := by
  rw [← neg_eq_iff_eq_neg, ← cos_sub_pi, cos_eq_one_iff, AddCommGroup.sub_modEq_iff_modEq_add,
    zero_add]

theorem sin_eq_one_iff {x : ℂ} : sin x = 1 ↔ x ≡ π / 2 [PMOD (2 * π : ℂ)] := by
  rw [← cos_sub_pi_div_two, cos_eq_one_iff, AddCommGroup.sub_modEq_iff_modEq_add,
    zero_add]

theorem sin_eq_neg_one_iff {x : ℂ} : sin x = -1 ↔ x ≡ -(π / 2) [PMOD (2 * π : ℂ)] := by
  rw [← neg_eq_iff_eq_neg, ← cos_add_pi_div_two, cos_eq_one_iff,
    ← AddCommGroup.modEq_sub_iff_add_modEq, zero_sub]

theorem tan_add {x y : ℂ}
    (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
      (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
  · rw [tan, sin_add, cos_add, ←
      div_div_div_cancel_right₀ (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
      add_div, sub_div]
    simp only [← div_mul_div_comm, tan, mul_one, one_mul, div_self (cos_ne_zero_iff.mpr h1),
      div_self (cos_ne_zero_iff.mpr h2)]
  · haveI t := tan_int_mul_pi_div_two
    obtain ⟨hx, hy, hxy⟩ := t (2 * k + 1), t (2 * l + 1), t (2 * k + 1 + (2 * l + 1))
    simp only [Int.cast_add, Int.cast_two, Int.cast_mul, Int.cast_one, hx, hy] at hx hy hxy
    rw [hx, hy, add_zero, zero_div, mul_div_assoc, mul_div_assoc, ←
      add_mul (2 * (k : ℂ) + 1) (2 * l + 1) (π / 2), ← mul_div_assoc, hxy]

theorem tan_add' {x y : ℂ}
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

theorem tan_two_mul {z : ℂ} : tan (2 * z) = (2 : ℂ) * tan z / ((1 : ℂ) - tan z ^ 2) := by
  by_cases h : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2
  · rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
  · rw [not_forall_not] at h
    rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]

theorem tan_add_mul_I {x y : ℂ}
    (h :
      ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y * I ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y * I = (2 * l + 1) * π / 2) :
    tan (x + y * I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) := by
  rw [tan_add h, tan_mul_I, mul_assoc]

theorem tan_eq {z : ℂ}
    (h :
      ((∀ k : ℤ, (z.re : ℂ) ≠ (2 * k + 1) * π / 2) ∧
          ∀ l : ℤ, (z.im : ℂ) * I ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, (z.re : ℂ) = (2 * k + 1) * π / 2) ∧
          ∃ l : ℤ, (z.im : ℂ) * I = (2 * l + 1) * π / 2) :
    tan z = (tan z.re + tanh z.im * I) / (1 - tan z.re * tanh z.im * I) := by
  convert tan_add_mul_I h; exact (re_add_im z).symm

open scoped Topology

theorem continuousOn_tan : ContinuousOn tan {x | cos x ≠ 0} :=
  continuousOn_sin.div continuousOn_cos fun _x => id

@[continuity]
theorem continuous_tan : Continuous fun x : {x | cos x ≠ 0} => tan x :=
  continuousOn_iff_continuous_restrict.1 continuousOn_tan

theorem cos_eq_iff_quadratic {z w : ℂ} :
    cos z = w ↔ exp (z * I) ^ 2 - 2 * w * exp (z * I) + 1 = 0 := by
  rw [← sub_eq_zero]
  field_simp [cos, exp_neg, exp_ne_zero]
  refine Eq.congr ?_ rfl
  ring

theorem cos_surjective : Function.Surjective cos := by
  intro x
  obtain ⟨w, w₀, hw⟩ : ∃ w ≠ 0, 1 * (w * w) + -2 * x * w + 1 = 0 := by
    rcases exists_quadratic_eq_zero one_ne_zero
        ⟨_, (cpow_nat_inv_pow _ two_ne_zero).symm.trans <| pow_two _⟩ with
      ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    rintro rfl
    simp only [zero_add, one_ne_zero, mul_zero] at hw
  refine ⟨log w / I, cos_eq_iff_quadratic.2 ?_⟩
  rw [div_mul_cancel₀ _ I_ne_zero, exp_log w₀]
  convert hw using 1
  ring

@[simp]
theorem range_cos : Set.range cos = Set.univ :=
  cos_surjective.range_eq

theorem sin_surjective : Function.Surjective sin := by
  intro x
  rcases cos_surjective x with ⟨z, rfl⟩
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩

@[simp]
theorem range_sin : Set.range sin = Set.univ :=
  sin_surjective.range_eq

end Complex

namespace Real

open scoped Real

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ θ ≡ π / 2 [PMOD ↑π] :=
  mod_cast @Complex.cos_eq_zero_iff θ

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 :=
  mod_cast @Complex.cos_ne_zero_iff θ

theorem cos_eq_cos_iff {x y : ℝ} :
    cos x = cos y ↔ x ≡ y [PMOD (2 * π)] ∨ x ≡ -y [PMOD (2 * π)]  :=
  mod_cast @Complex.cos_eq_cos_iff x y

theorem sin_eq_sin_iff {x y : ℝ} :
    sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
  mod_cast @Complex.sin_eq_sin_iff x y

theorem cos_eq_neg_one_iff {x : ℝ} : cos x = -1 ↔ ∃ k : ℤ, π + k * (2 * π) = x :=
  mod_cast @Complex.cos_eq_neg_one_iff x

theorem sin_eq_one_iff {x : ℝ} : sin x = 1 ↔ ∃ k : ℤ, π / 2 + k * (2 * π) = x :=
  mod_cast @Complex.sin_eq_one_iff x

theorem sin_eq_neg_one_iff {x : ℝ} : sin x = -1 ↔ ∃ k : ℤ, -(π / 2) + k * (2 * π) = x :=
  mod_cast @Complex.sin_eq_neg_one_iff x

theorem tan_eq_zero_iff {θ : ℝ} : tan θ = 0 ↔ ∃ k : ℤ, k * π / 2 = θ :=
  mod_cast @Complex.tan_eq_zero_iff θ

theorem tan_eq_zero_iff' {θ : ℝ} (hθ : cos θ ≠ 0) : tan θ = 0 ↔ ∃ k : ℤ, k * π = θ := by
  revert hθ
  exact_mod_cast @Complex.tan_eq_zero_iff' θ

theorem tan_ne_zero_iff {θ : ℝ} : tan θ ≠ 0 ↔ ∀ k : ℤ, k * π / 2 ≠ θ :=
  mod_cast @Complex.tan_ne_zero_iff θ

end Real
