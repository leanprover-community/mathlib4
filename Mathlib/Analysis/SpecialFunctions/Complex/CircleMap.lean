/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Fabrizio Barroero, Christopher Hoskin
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# circleMap

This file defines the circle map $θ ↦ c + R e^{θi}$,  a parametrization of a circle.

## Main definitions

* `circleMap c R`: the exponential map $θ ↦ c + R e^{θi}$.

## Tags

-/
noncomputable section circleMap

open Complex Filter Function Metric Pointwise Real Set

/-- The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center
`c` and radius `|R|`. -/
def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)

@[simp]
theorem circleMap_sub_center (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [circleMap]

theorem circleMap_zero (R θ : ℝ) : circleMap 0 R θ = R * exp (θ * I) := zero_add _

@[simp]
theorem norm_circleMap_zero (R : ℝ) (θ : ℝ) : ‖circleMap 0 R θ‖= |R| := by simp [circleMap]

@[deprecated (since := "2025-02-17")] alias abs_circleMap_zero := norm_circleMap_zero

theorem circleMap_mem_sphere' (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by simp

theorem circleMap_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    circleMap c R θ ∈ sphere c R := by
  simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' c R θ

theorem circleMap_mem_closedBall (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    circleMap c R θ ∈ closedBall c R :=
  sphere_subset_closedBall (circleMap_mem_sphere c hR θ)

@[simp]
theorem circleMap_eq_center_iff {c : ℂ} {R : ℝ} {θ : ℝ} : circleMap c R θ = c ↔ R = 0 := by
  simp [circleMap, Complex.exp_ne_zero]

@[simp]
theorem circleMap_zero_radius (c : ℂ) : circleMap c 0 = const ℝ c :=
  funext fun _ => circleMap_eq_center_iff.2 rfl

theorem circleMap_ne_center {c : ℂ} {R : ℝ} (hR : R ≠ 0) {θ : ℝ} : circleMap c R θ ≠ c :=
  mt circleMap_eq_center_iff.1 hR

lemma circleMap_mul (R₁ R₂ θ₁ θ₂ : ℝ) :
    (circleMap 0 R₁ θ₁) * (circleMap 0 R₂ θ₂) = circleMap 0 (R₁ * R₂) (θ₁ + θ₂) := by
  simp only [circleMap_zero, ofReal_mul, ofReal_add, add_mul, Complex.exp_add]
  ring

lemma circleMap_div (R₁ R₂ θ₁ θ₂ : ℝ) :
    (circleMap 0 R₁ θ₁) / (circleMap 0 R₂ θ₂) = circleMap 0 (R₁ / R₂) (θ₁ - θ₂) := by
  simp only [circleMap_zero, ofReal_div, ofReal_sub, sub_mul, Complex.exp_sub]
  ring

lemma circleMap_inv (R θ : ℝ) : (circleMap 0 R θ)⁻¹ = circleMap 0 R⁻¹ (-θ) := by
  simp [circleMap_zero, Complex.exp_neg, mul_comm]

lemma circleMap_pow (n : ℕ) (R θ : ℝ) : (circleMap 0 R θ) ^ n = circleMap 0 (R ^ n) (n * θ) := by
  simp [circleMap_zero, mul_pow, ← Complex.exp_nat_mul, ← mul_assoc]

lemma circleMap_zpow (n : ℤ) (R θ : ℝ) : (circleMap 0 R θ) ^ n = circleMap 0 (R ^ n) (n * θ) := by
  simp [circleMap_zero, mul_zpow, ← exp_int_mul, ← mul_assoc]

lemma circleMap_pi_div_two (c : ℂ) (R : ℝ) : circleMap c R (π / 2) = c + R * I := by
  simp only [circleMap, ofReal_div, ofReal_ofNat, exp_pi_div_two_mul_I]

lemma circleMap_neg_pi_div_two (c : ℂ) (R : ℝ) : circleMap c R (-π / 2) = c - R * I := by
  simp only [circleMap, ofReal_div, ofReal_neg, ofReal_ofNat, exp_neg_pi_div_two_mul_I, mul_neg]
  rfl

/-- `circleMap` is `2π`-periodic. -/
theorem periodic_circleMap (c : ℂ) (R : ℝ) : Periodic (circleMap c R) (2 * π) := fun θ =>
  by simp [circleMap, add_mul, exp_periodic _]

theorem Set.Countable.preimage_circleMap {s : Set ℂ} (hs : s.Countable) (c : ℂ) {R : ℝ}
    (hR : R ≠ 0) : (circleMap c R ⁻¹' s).Countable :=
  show (((↑) : ℝ → ℂ) ⁻¹' ((· * I) ⁻¹'
      (exp ⁻¹' ((R * ·) ⁻¹' ((c + ·) ⁻¹' s))))).Countable from
    (((hs.preimage (add_right_injective _)).preimage <|
      mul_right_injective₀ <| ofReal_ne_zero.2 hR).preimage_cexp.preimage <|
        mul_left_injective₀ I_ne_zero).preimage ofReal_injective

lemma circleMap_eq_circleMap_iff {a b R : ℝ} (c : ℂ) (h_R : R ≠ 0) :
    circleMap c R a = circleMap c R b ↔ ∃ (n : ℤ), a * I = b * I + n * (2 * π * I) := by
  have : circleMap c R a = circleMap c R b ↔ (exp (a * I)).arg = (exp (b * I)).arg := by
    simp [circleMap, ext_norm_arg_iff, h_R]
  simp [this, arg_eq_arg_iff, exp_eq_exp_iff_exists_int]

lemma eq_of_circleMap_eq {a b R : ℝ} {c : ℂ} (h_R : R ≠ 0) (h_dist : |a - b| < 2 * π)
    (h : circleMap c R a = circleMap c R b) : a = b := by
  rw [circleMap_eq_circleMap_iff c h_R] at h
  obtain ⟨n, hn⟩ := h
  simp only [show n * (2 * π * I) = (n * 2 * π) * I by ring, ← add_mul, mul_eq_mul_right_iff,
    I_ne_zero, or_false] at hn
  norm_cast at hn
  simp only [hn, Int.cast_mul, Int.cast_ofNat, mul_assoc, add_sub_cancel_left, abs_mul,
    Nat.abs_ofNat, abs_of_pos Real.pi_pos] at h_dist
  field_simp at h_dist
  norm_cast at h_dist
  simp [hn, Int.abs_lt_one_iff.mp h_dist]

/-- `circleMap` is injective on `Ι a b` if the distance between `a` and `b` is at most `2π`. -/
theorem injOn_circleMap_of_abs_sub_le {a b R : ℝ} {c : ℂ} (h_R : R ≠ 0) (_ : |a - b| ≤ 2 * π) :
    (Ι a b).InjOn (circleMap c R) := by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_R _ h
  rw [abs_lt]
  constructor <;> linarith [max_sub_min_eq_abs' a b]

theorem circleMap_not_mem_ball (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ ∉ ball c R := by
  simp [Complex.dist_eq, le_abs_self]

theorem circleMap_ne_mem_ball {c : ℂ} {R : ℝ} {w : ℂ} (hw : w ∈ ball c R) (θ : ℝ) :
    circleMap c R θ ≠ w :=
  (ne_of_mem_of_not_mem hw (circleMap_not_mem_ball _ _ _)).symm

/-- The range of `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem range_circleMap (c : ℂ) (R : ℝ) : range (circleMap c R) = sphere c |R| :=
  calc
    range (circleMap c R) = c +ᵥ R • range fun θ : ℝ => exp (θ * I) := by
      simp (config := { unfoldPartialApp := true }) only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, comp_def, real_smul]
    _ = sphere c |R| := by
      rw [range_exp_mul_I, smul_sphere R 0 zero_le_one]
      simp

/-- The image of `(0, 2π]` under `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem image_circleMap_Ioc (c : ℂ) (R : ℝ) : circleMap c R '' Ioc 0 (2 * π) = sphere c |R| := by
  rw [← range_circleMap, ← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0, zero_add]

theorem hasDerivAt_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : ℂ)).const_add c

theorem differentiable_circleMap (c : ℂ) (R : ℝ) : Differentiable ℝ (circleMap c R) := fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt

/-- The circleMap is real analytic. -/
theorem analyticOnNhd_circleMap (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℝ (circleMap c R) Set.univ := by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

/-- The circleMap is continuously differentiable. -/
theorem contDiff_circleMap (c : ℂ) (R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (circleMap c R) :=
  (analyticOnNhd_circleMap c R).contDiff

@[continuity, fun_prop]
theorem continuous_circleMap (c : ℂ) (R : ℝ) : Continuous (circleMap c R) :=
  (differentiable_circleMap c R).continuous

@[fun_prop, measurability]
theorem measurable_circleMap (c : ℂ) (R : ℝ) : Measurable (circleMap c R) :=
  (continuous_circleMap c R).measurable

@[simp]
theorem deriv_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : deriv (circleMap c R) θ = circleMap 0 R θ * I :=
  (hasDerivAt_circleMap _ _ _).deriv

theorem deriv_circleMap_eq_zero_iff {c : ℂ} {R : ℝ} {θ : ℝ} :
    deriv (circleMap c R) θ = 0 ↔ R = 0 := by simp [I_ne_zero]

theorem deriv_circleMap_ne_zero {c : ℂ} {R : ℝ} {θ : ℝ} (hR : R ≠ 0) :
    deriv (circleMap c R) θ ≠ 0 :=
  mt deriv_circleMap_eq_zero_iff.1 hR

theorem lipschitzWith_circleMap (c : ℂ) (R : ℝ) : LipschitzWith (Real.nnabs R) (circleMap c R) :=
  lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
    NNReal.coe_le_coe.1 <| by simp

theorem continuous_circleMap_inv {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R) :
    Continuous fun θ => (circleMap z R θ - w)⁻¹ := by
  have : ∀ θ, circleMap z R θ - w ≠ 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circleMap_ne_mem_ball hw θ
  -- Porting note: was `continuity`
  exact Continuous.inv₀ (by fun_prop) this

theorem circleMap_preimage_codiscrete {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    map (circleMap c R) (codiscrete ℝ) ≤ codiscreteWithin (Metric.sphere c |R|) := by
  intro s hs
  apply (analyticOnNhd_circleMap c R).preimage_mem_codiscreteWithin
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    have := ha.deriv.eq_of_nhds
    simp [hR] at this
  · rwa [Set.image_univ, range_circleMap]

end circleMap
