/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integral representations of `rpow`

This file contains an integral representation of the `rpow` function between 0 and 1: we show
that there exists a measure on ℝ such that `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ` for
the integrand `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`.

This representation is useful for showing that `rpow` is operator monotone and operator concave
in this range; that is, `cfc rpow` is monotone/concave. The integrand can be shown to be
operator monotone and concave through direct means, and this integral lifts these properties
to `rpow`.

## Notes

Here we only compute the integral up to a constant, even though the actual constant can be
computed via contour integration. We chose to avoid this, as the constant is seldom if ever
relevant in applications, and would needlessly complicate the proof.

## Main declarations

+ `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`
+ `exists_measure_rpow_eq_integral`: there exists a measure on `ℝ` such that
  `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ`

## TODO

+ Show operator monotonicity and concavity of `rpow` over `Icc 0 1` as outlined above
+ Give analogous representations for the ranges `Ioo (-1) 0` and `Ioo 1 2`.

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace Real

/-- Integrand for representing `x ↦ x ^ p` for `p ∈ (0,1)` -/
noncomputable def rpowIntegrand₀₁ (p t x : ℝ) : ℝ := t ^ p * (t⁻¹ - (t + x)⁻¹)

variable {p t x : ℝ}

@[simp]
lemma rpowIntegrand₀₁_zero_right : rpowIntegrand₀₁ p t 0 = 0 := by simp [rpowIntegrand₀₁]

lemma rpowIntegrand₀₁_zero_left (hp : 0 < p) : rpowIntegrand₀₁ p 0 x = 0 := by
  simp [rpowIntegrand₀₁, Real.zero_rpow hp.ne']

lemma rpowIntegrand₀₁_nonneg (hp : 0 < p) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ rpowIntegrand₀₁ p t x := by
  unfold rpowIntegrand₀₁
  cases eq_or_gt_of_le ht with
  | inl ht_zero => simp [ht_zero, Real.zero_rpow (ne_of_gt hp)]
  | inr ht_pos =>
    refine mul_nonneg (by positivity) ?_
    rw [sub_nonneg]
    gcongr
    linarith

lemma rpowIntegrand₀₁_eq_pow_div (hp : p ∈ Ioo 0 1) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p t x = t ^ (p - 1) * x / (t + x) := by
  by_cases ht' : t = 0
  case neg =>
    have hxt : t + x ≠ 0 := by positivity
    calc _ = (t : ℝ) ^ p * (t⁻¹ - (t + x)⁻¹) := rfl
      _ = (t : ℝ) ^ p * ((t + x - t) / (t * (t + x))) := by
          simp only [inv_eq_one_div]
          rw [div_sub_div _ _ (by aesop) (by aesop)]
          simp
      _ = t ^ p / t * x / (t + x) := by field_simp
      _ = t ^ (p - 1) * x / (t + x) := by congr; exact (Real.rpow_sub_one ht' p).symm
  case pos =>
    simp only [mem_Ioo] at hp
    have hp₂ : p - 1 ≠ 0 := by linarith
    simp [rpowIntegrand₀₁, ht', hp.1.ne', hp₂]

lemma rpowIntegrand₀₁_eqOn_pow_div (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    Set.EqOn (rpowIntegrand₀₁ p · x) (fun t => t ^ (p - 1) * x / (t + x)) (Ioi 0) := by
  intro t ht
  simp [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]

lemma rpowIntegrand₀₁_apply_mul (hp : p ∈ Ioo 0 1) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p (x * t) x = (rpowIntegrand₀₁ p t 1) * x ^ (p - 1) := by
  have hxt : 0 ≤ x * t := by positivity
  rw [rpowIntegrand₀₁_eq_pow_div hp hxt hx, rpowIntegrand₀₁_eq_pow_div hp ht zero_le_one]
  by_cases hx_zero : x = 0
  case neg =>
    calc _ = x ^ (p - 1) * (t ^ (p - 1) * (x / (x * t + x))) := by
              rw [← mul_assoc, mul_div_assoc, Real.mul_rpow hx ht]
      _ = x ^ (p - 1) * (t ^ (p - 1) * 1 / (t + 1)) := by
              have : x * t + x = x * (t + 1) := by ring
              rw [mul_div_assoc, this, div_mul_eq_div_mul_one_div, div_self hx_zero, one_mul]
      _ = t ^ (p - 1) * 1 / (t + 1) * x ^ (p - 1) := by rw [mul_comm]
  case pos =>
    rw [mem_Ioo] at hp
    simp [hx_zero, Real.zero_rpow (by linarith : p - 1 ≠ 0)]

lemma rpowIntegrand₀₁_apply_mul' (hp : p ∈ Ioo 0 1) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p (x * t) x * x  = (rpowIntegrand₀₁ p t 1) * x ^ p := by
  simp only [rpowIntegrand₀₁_apply_mul hp ht hx, mul_assoc]
  congr
  simpa using Eq.symm <| Real.rpow_add' hx (by aesop : (p - 1) + 1 ≠ 0)

lemma rpowIntegrand₀₁_apply_mul_eqOn_Ici (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ici 0) :=
  fun _ ht => rpowIntegrand₀₁_apply_mul' hp ht hx

lemma continuousOn_rpowIntegrand₀₁ (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    ContinuousOn (rpowIntegrand₀₁ p · x) (Ioi 0) := by
  refine ContinuousOn.congr ?_ <| rpowIntegrand₀₁_eqOn_pow_div hp hx
  have h₀ : ContinuousOn (· ^ (p - 1) : ℝ → ℝ) (Ioi 0) := .rpow_const (by fun_prop) <|
    fun t ht => .inl ht.ne'
  fun_prop (disch := intros; simp_all; positivity)

lemma aestronglyMeasurable_rpowIntegrand₀₁ (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    AEStronglyMeasurable (rpowIntegrand₀₁ p · x) (volume.restrict (Ioi 0)) :=
  (continuousOn_rpowIntegrand₀₁ hp hx).aestronglyMeasurable measurableSet_Ioi

lemma rpowIntegrand₀₁_le_rpow_sub_two_mul_self (hp : p ∈ Ioo 0 1) (ht : 0 < t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p t x ≤ t ^ (p - 2) * x := calc
  _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]
  _ ≤ t ^ (p - 1) * x / t := by gcongr; linarith
  _ = t ^ (p - 1) / t * x := by ring
  _ = t ^ (p - 2) * x := by
    congr
    rw [← Real.rpow_sub_one (by positivity)]
    congr 1
    ring

lemma rpowIntegrand₀₁_le_rpow_sub_one (hp : p ∈ Ioo 0 1) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p t x ≤ t ^ (p - 1) := by
  by_cases hx_zero : x = 0
  case pos =>
    simp only [rpowIntegrand₀₁, one_div, hx_zero, add_zero, sub_self, mul_zero]
    positivity
  case neg =>
    calc
    _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp ht hx]
    _ ≤ t ^ (p - 1) * x / x := by gcongr; linarith
    _ = t ^ (p - 1) * (x / x) := by ring
    _ = t ^ (p - 1) * 1 := by congr; exact (div_eq_one_iff_eq hx_zero).mpr rfl
    _ = _ := by simp

lemma rpowIntegrand₀₁_one_ge_rpow_sub_two (hp : p ∈ Ioo 0 1) (ht : 1 ≤ t) :
    (1 : ℝ) / 2 * t ^ (p - 2) ≤ rpowIntegrand₀₁ p t 1 := calc
  _ = t ^ (p - 1) * (1 / 2 * 1 / t) := by
            have : p - 2 = p - 1 - 1 := by ring
            rw [this, Real.rpow_sub (by linarith), Real.rpow_one]
            ring
  _ ≤ t ^ (p - 1) * (1 / (t + 1)) := by
            gcongr t ^ (p - 1) * ?_
            rw [mul_div_assoc, one_div_mul_one_div,
              one_div_le_one_div (by positivity) (by positivity)]
            linarith
  _ = rpowIntegrand₀₁ p t 1 := by
            rw [rpowIntegrand₀₁_eq_pow_div hp (by linarith) zero_le_one, mul_div_assoc]

/- This lemma is private because it is strictly weaker than `integrableOn_rpowIntegrand₀₁_Ioi` -/
private lemma integrableOn_rpowIntegrand₀₁_Ioc (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioc 0 1) := by
  refine IntegrableOn.congr_set_ae (t := Ioo 0 1) ?_ (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ContinuousOn.mono (continuousOn_rpowIntegrand₀₁ hp hx) Ioo_subset_Ioi_self
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 1)) ?finitebound ?ae_le
    case finitebound =>
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      rw [← IntegrableOn, intervalIntegral.integrableOn_Ioo_rpow_iff]
      · linarith
      · exact zero_lt_one
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht.1) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_one hp (le_of_lt ht.1) hx

/- This lemma is private because it is strictly weaker than `integrableOn_rpowIntegrand₀₁_Ioi` -/
private lemma integrableOn_rpowIntegrand₀₁_Ioi_one (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioi 1) := by
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_rpowIntegrand₀₁ hp hx |>.mono (Set.Ioi_subset_Ioi zero_le_one)
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 2) * x) ?finitebound ?ae_le
    case finitebound =>
      refine HasFiniteIntegral.mul_const ?_ _
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      refine integrableOn_Ioi_rpow_of_lt ?_ zero_lt_one
      linarith
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (by positivity) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_two_mul_self hp (by positivity) hx

lemma integrableOn_rpowIntegrand₀₁_Ioi (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioi 0) := by
  /- The integral converges because it is `O(t ^ (p-1))` at the origin and `O(t ^ (p-2))` at
  infinity. Hence we break the integral into two parts. -/
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact IntegrableOn.union (integrableOn_rpowIntegrand₀₁_Ioc hp hx)
    (integrableOn_rpowIntegrand₀₁_Ioi_one hp hx)

lemma integrableOn_rpowIntegrand₀₁_Ici (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ici 0) :=
  integrableOn_rpowIntegrand₀₁_Ioi hp hx |>.congr_set_ae Ioi_ae_eq_Ici.symm

lemma integral_rpowIntegrand₀₁_eq_rpow_mul_const (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    (∫ t in Ioi 0, rpowIntegrand₀₁ p t x) = x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) := by
  -- We use the change of variables formula with `f t = x * t`. Here `g = rpowIntegrand₀₁ p · x`.
  obtain (rfl | hx) := hx.eq_or_lt
  · simp [rpowIntegrand₀₁, Real.zero_rpow hp.1.ne']
  suffices ∫ t in Ioi 0, ((rpowIntegrand₀₁ p · x) ∘ (x * ·)) t * x =
      x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) by
    rwa [integral_comp_mul_deriv_Ioi (by fun_prop), mul_zero] at this
    · exact tendsto_id.const_mul_atTop hx
    · simpa using fun t _ ↦ hasDerivWithinAt_id t (Ioi t) |>.const_mul x
    · simpa [Set.image_mul_left_Ioi hx] using continuousOn_rpowIntegrand₀₁ hp hx.le
    · simpa [Set.image_mul_left_Ici hx] using integrableOn_rpowIntegrand₀₁_Ici hp hx.le
    · simp only [Function.comp, rpowIntegrand₀₁_apply_mul' hp hx.le]
      rw [integrableOn_congr_fun (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le) measurableSet_Ici]
      exact Integrable.mul_const (integrableOn_rpowIntegrand₀₁_Ici hp zero_le_one) _
  have heqOn : EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ioi 0) :=
    EqOn.mono Ioi_subset_Ici_self (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le)
  simp only [Function.comp, setIntegral_congr_fun measurableSet_Ioi heqOn,
    ← smul_eq_mul (b := x ^ p), integral_smul_const]
  rw [smul_eq_mul, mul_comm]

lemma le_integral_rpowIntegrand₀₁_one (hp : p ∈ Ioo 0 1) :
    -1 / (2 * (p - 1)) ≤ ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := calc
  _ = (1 / 2) * -((1 : ℝ) ^ (p - 1)) / (p - 1) := by rw [← div_div]; simp [neg_div]
  _ = ∫ t in Ioi 1, (1 / 2) * t ^ (p - 2) := by
        simp only [mem_Ioo] at hp
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
        ring_nf   -- ring alone succeeds but gives a warning
  _ ≤ ∫ t in Ioi 1, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
        · refine Integrable.const_mul ?_ _
          simp only [mem_Ioo] at hp
          exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
        · exact integrableOn_rpowIntegrand₀₁_Ioi_one hp zero_le_one
        · exact fun t ht =>  rpowIntegrand₀₁_one_ge_rpow_sub_two hp (le_of_lt ht)
  _ ≤ ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_set (integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one) ?_ ?_
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
          exact rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) zero_le_one
        · exact .of_forall <| Set.Ioi_subset_Ioi zero_le_one

lemma integral_rpowIntegrand₀₁_one_pos (hp : p ∈ Ioo 0 1) :
    0 < ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := calc
  0 < -1 / (2 * (p - 1)) := by
      rw [neg_div, neg_pos, one_div_neg]
      simp only [mem_Ioo] at hp
      linarith
  _ ≤ ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := le_integral_rpowIntegrand₀₁_one hp

/-- The integral representation of the function `x ↦ x^p` (where `p ∈ (0, 1)`) . -/
lemma rpow_eq_const_mul_integral (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    x ^ p = (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹ * ∫ t in Ioi 0, rpowIntegrand₀₁ p t x := by
  rcases eq_or_gt_of_le hx with hx_zero|_
  case inl =>
    simp only [mem_Ioo] at hp
    simp [hx_zero, Real.zero_rpow (by linarith)]
  case inr =>
    have : ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 ≠ 0 :=
      ne_of_gt <| integral_rpowIntegrand₀₁_one_pos hp
    rw [integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hx, mul_comm, mul_assoc, mul_inv_cancel₀
      this, mul_one]

/-- The integral representation of the function `x ↦ x^p` (where `p ∈ (0, 1)`) . -/
lemma exists_measure_rpow_eq_integral (hp : p ∈ Ioo 0 1) :
    ∃ μ : Measure ℝ, (∀ᵐ t ∂μ, 0 < t) ∧ ∀ x, 0 ≤ x → x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ := by
  let C : ℝ≥0 :=
    { val := (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹
      property := by
        rw [inv_nonneg]
        exact le_of_lt <| integral_rpowIntegrand₀₁_one_pos hp }
  let μ : Measure ℝ := C • volume.restrict (Ioi 0)
  refine ⟨μ, ?_, fun x hx => ?_⟩
  · refine Measure.ae_smul_measure ?_ _
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ht
  · rw [integral_smul_nnreal_measure, rpow_eq_const_mul_integral hp hx]
    simp [C, NNReal.smul_def]

end Real
