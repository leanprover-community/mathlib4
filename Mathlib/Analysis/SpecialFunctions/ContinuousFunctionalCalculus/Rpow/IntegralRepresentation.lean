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

/-- Integrand for representing `x ↦ x^p` for `p ∈ (0,1)` -/
noncomputable def rpowIntegrand₀₁ (p t x : ℝ) : ℝ := t ^ p * (t⁻¹ - (t + x)⁻¹)

variable {p t x : ℝ}

@[simp]
lemma rpowIntegrand₀₁_zero_right : rpowIntegrand₀₁ p t 0 = 0 := by simp [rpowIntegrand₀₁]

lemma rpowIntegrand₀₁_zero_left (hp : 0 < p) : rpowIntegrand₀₁ p 0 x = 0 := by
  have : p ≠ 0 := ne_of_gt hp
  simp only [rpowIntegrand₀₁, Real.zero_rpow this, div_zero, zero_add, one_div, zero_sub,
    mul_neg, zero_mul, neg_zero]

lemma rpowIntegrand₀₁_nonneg (hp : 0 < p) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ rpowIntegrand₀₁ p t x := by
  unfold rpowIntegrand₀₁
  rcases eq_or_gt_of_le ht with ht_zero|ht_pos
  case inl => simp [ht_zero, Real.zero_rpow (ne_of_gt hp)]
  case inr =>
    refine mul_nonneg (by positivity) ?_
    rw [sub_nonneg]
    gcongr
    linarith

lemma rpowIntegrand₀₁_eq_pow_div (hp : p ∈ Ioo 0 1) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p t x = t ^ (p - 1) * x / (t + x) := by
  by_cases ht' : t = 0
  case neg =>
    have hxt : t + x ≠ 0 := by
      have : 0 < t + x := by positivity
      exact Ne.symm (ne_of_lt this)
    calc _ = (t : ℝ) ^ p * (t⁻¹ - (t + x)⁻¹) := rfl
      _ = (t : ℝ) ^ p * ((t + x - t) / (t * (t + x))) := by
          congr
          simp only [inv_eq_one_div]
          rw [div_sub_div _ _ (by aesop) (by aesop)]
          congr <;> aesop
      _ = t ^ p * x / (t * (t + x)) := by ring
      _ = (t ^ p * x / t) / (t + x) := Eq.symm (div_div ((t : ℝ) ^ p * ↑x) (↑t) (↑t + ↑x))
      _ = (t ^ p / t * x) / (t + x) := by field_simp
      _ = t ^ p / t * x / (t + x) := by ring
      _ = t ^ (p - 1) * x / (t + x) := by congr; exact (Real.rpow_sub_one ht' p).symm
  case pos =>
    simp only [mem_Ioo] at hp
    have hp₁ : p ≠ 0 := Ne.symm (ne_of_lt hp.1)
    have hp₂ : p - 1 ≠ 0 := by linarith
    simp [rpowIntegrand₀₁, ht', hp₁, hp₂]

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
              rw [← mul_assoc, mul_div_assoc]
              congr
              exact Real.mul_rpow hx ht
      _ = x ^ (p - 1) * (t ^ (p - 1) * 1 / (t + 1)) := by
              congr 1
              simp only [mul_div_assoc]
              congr 1
              have : x * t + x = x * (t + 1) := by ring
              rw [this, div_mul_eq_div_mul_one_div, div_self hx_zero, one_mul]
      _ = t ^ (p - 1) * 1 / (t + 1) * x ^ (p - 1) := by rw [mul_comm]
  case pos =>
    simp [hx_zero]
    apply Or.inr
    refine Real.zero_rpow ?_
    rw [mem_Ioo] at hp
    linarith

lemma rpowIntegrand₀₁_apply_mul' (hp : p ∈ Ioo 0 1) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rpowIntegrand₀₁ p (x * t) x * x  = (rpowIntegrand₀₁ p t 1) * x ^ p := by
  simp only [rpowIntegrand₀₁_apply_mul hp ht hx, mul_assoc]
  congr
  by_cases hx_zero : x = 0
  case neg =>
    have : 0 < x := lt_of_le_of_ne hx fun a => hx_zero (id (Eq.symm a))
    field_simp [Real.rpow_sub this]
  case pos =>
    have : p ≠ 0 := by rw [mem_Ioo] at hp; linarith
    simp [hx_zero, Real.zero_rpow this]

lemma rpowIntegrand₀₁_apply_mul_eqOn_Ici (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ici 0) :=
  fun _ ht => rpowIntegrand₀₁_apply_mul' hp ht hx

lemma continuousOn_rpowIntegrand₀₁ (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    ContinuousOn (rpowIntegrand₀₁ p · x) (Ioi 0) := by
  refine ContinuousOn.congr ?_ <| rpowIntegrand₀₁_eqOn_pow_div hp hx
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.mul ?_ continuousOn_const
    exact ContinuousOn.rpow_const (by fun_prop) fun t ht => Or.inl <| Ne.symm (ne_of_lt ht)
  · refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t ht
    simp only [mem_Ioo] at *
    have : 0 < t + x := add_pos_of_pos_of_nonneg ht hx
    exact Ne.symm (ne_of_lt this)

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
      change IntegrableOn (fun t => t ^ (p - 1)) (Set.Ioo 0 1) volume
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff]
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
    refine ContinuousOn.mono (continuousOn_rpowIntegrand₀₁ hp hx) fun t ht => ?_
    calc 0 < 1 := zero_lt_one
      _ < t := ht
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 2) * x) ?finitebound ?ae_le
    case finitebound =>
      refine HasFiniteIntegral.mul_const ?_ _
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      refine integrableOn_Ioi_rpow_of_lt ?_ zero_lt_one
      linarith
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht' : 0 ≤ t := calc
        0 ≤ 1 := zero_le_one
        _ ≤ t := le_of_lt ht
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 ht' hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_two_mul_self hp (zero_lt_one.trans ht) hx

lemma integrableOn_rpowIntegrand₀₁_Ioi (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioi 0) := by
  /- The integral converges because it is `O(t ^ (p-1))` at the origin and `O(t ^ (p-2))` at
  infinity. Hence we break the integral into two parts. -/
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    · rw [Set.mem_union]
      by_cases ht' : t ≤ 1
      · exact Or.inl ⟨ht, ht'⟩
      · push_neg at ht'
        exact Or.inr ht'
    · rw [Set.mem_union] at ht
      rcases ht with ht|ht
      · exact ht.1
      · calc (0 : ℝ) < 1 := zero_lt_one
          _ < t := ht
  rw [hunion]
  exact IntegrableOn.union (integrableOn_rpowIntegrand₀₁_Ioc hp hx)
    (integrableOn_rpowIntegrand₀₁_Ioi_one hp hx)

lemma integrableOn_rpowIntegrand₀₁_Ici (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ici 0) :=
  IntegrableOn.congr_set_ae (integrableOn_rpowIntegrand₀₁_Ioi hp hx)
    (EventuallyEq.symm Ioi_ae_eq_Ici)

lemma integral_rpowIntegrand₀₁_eq_rpow_mul_const (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) :
    (∫ t in Ioi 0, rpowIntegrand₀₁ p t x) = x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) := by
  -- We use the change of variables formula with `f t = x * t`. Here `g = rpowIntegrand₀₁ p · x`.
  by_cases hx_zero : x = 0
  case pos =>
    simp only [rpowIntegrand₀₁, one_div, hx_zero, add_zero, sub_self, mul_zero, integral_zero, zero_eq_mul,
      le_refl]
    apply Or.inl
    refine Real.zero_rpow ?_
    rw [mem_Ioo] at hp
    linarith
  case neg =>
    have hx_pos : 0 < x := lt_of_le_of_ne hx fun a => hx_zero (id (Eq.symm a))
    let f (t : ℝ) := x * t
    let g (t : ℝ) := rpowIntegrand₀₁ p t x
    let f' (_ : ℝ) := x
    have f_Ioi : f '' (Ioi 0) = Ioi 0 := by
      simp only [f]
      ext t
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [mem_image] at h
        obtain ⟨z, hz⟩ := h
        rw [← hz.2, mem_Ioi]
        obtain ⟨hz1, hz2⟩ := hz
        rw [mem_Ioi] at hz1
        positivity
      · rw [mem_image]
        refine ⟨t / x, ?_, mul_div_cancel₀ _ hx_zero⟩
        simp only [mem_Ioi] at *
        positivity
    have f_Ici : f '' (Ici 0) = Ici 0 := by
      simp only [f]
      ext t
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [mem_image] at h
        obtain ⟨z, hz⟩ := h
        rw [← hz.2, mem_Ici]
        obtain ⟨hz1, hz2⟩ := hz
        rw [mem_Ici] at hz1
        positivity
      · rw [mem_image]
        refine ⟨t / x, ?_, mul_div_cancel₀ _ hx_zero⟩
        simp only [mem_Ici] at *
        positivity
    have hf : ContinuousOn f (Ici 0) := by fun_prop
    have hft : Tendsto f atTop atTop := Tendsto.const_mul_atTop hx_pos fun ⦃U⦄ a => a
    have hff' : ∀ t ∈ Ioi 0, HasDerivWithinAt f (f' x) (Ioi t) t := by
      intro t _
      apply HasDerivAt.hasDerivWithinAt
      simp only [f', f]
      have : x = x * 1 := by simp
      nth_rewrite 2 [this]
      exact HasDerivAt.const_mul x <| hasDerivAt_id' t
    have hg_cont : ContinuousOn g (f '' Ioi 0) := by
      rw [f_Ioi]
      exact continuousOn_rpowIntegrand₀₁ hp hx
    have hg1 : IntegrableOn g (f '' Ici 0) := by
      rw [f_Ici]
      exact integrableOn_rpowIntegrand₀₁_Ici hp hx
    have hg2 : IntegrableOn (fun t => (g ∘ f) t * f' x) (Ici 0) := by
      simp only [g, f, f', Function.comp, rpowIntegrand₀₁_apply_mul' hp hx]
      rw [integrableOn_congr_fun (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx) measurableSet_Ici]
      exact Integrable.mul_const (integrableOn_rpowIntegrand₀₁_Ici hp zero_le_one) _
    have hrw : (∫ t in Ioi 0, rpowIntegrand₀₁ p t x) = (∫ t in Ioi (f 0), g t) := by
      simp [g, f]
    rw [hrw, ← integral_comp_mul_deriv_Ioi hf hft hff' hg_cont hg1 hg2]
    simp only [f, g, f', Function.comp]
    have heqOn : EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
        (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ioi 0) :=
      EqOn.mono Ioi_subset_Ici_self (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx)
    rw [setIntegral_congr_fun measurableSet_Ioi heqOn]
    simp only [← smul_eq_mul (b := x ^ p), integral_smul_const]
    rw [smul_eq_mul, mul_comm]

lemma le_integral_rpowIntegrand₀₁_one (hp : p ∈ Ioo 0 1) :
    -1 / (2 * (p - 1)) ≤ ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := calc
  _ = (1 / 2) * -((1 : ℝ) ^ (p - 1)) / (p - 1) := by rw [← div_div]; simp [neg_div]
  _ = (1 / 2) * ∫ t in Ioi 1, t ^ (p - 2) := by
        simp only [mem_Ioo] at hp
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
        ring_nf   -- ring alone succeeds but gives a warning
  _ = ∫ t in Ioi 1, (1 / 2) * t ^ (p - 2) := by
        exact Eq.symm (integral_mul_left (1 / 2) fun a => a ^ (p - 2))
  _ ≤ ∫ t in Ioi 1, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
        · refine Integrable.const_mul ?_ _
          simp only [mem_Ioo] at hp
          exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
        · exact integrableOn_rpowIntegrand₀₁_Ioi_one hp zero_le_one
        · exact fun t ht =>  rpowIntegrand₀₁_one_ge_rpow_sub_two hp (le_of_lt ht)
  _ ≤ ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_set (integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one) ?_ ?_
        · unfold EventuallyLE
          refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
          exact rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) zero_le_one
        · refine Filter.Eventually.of_forall ?_
          change Ioi 1 ⊆ Ioi 0
          intro t ht
          simp only [mem_Ioi] at *
          linarith

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
    ∃ μ : Measure ℝ, ∀ x, 0 ≤ x → x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ := by
  let C : ℝ≥0 := ⟨(∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹, by
      rw [inv_nonneg]
      exact le_of_lt <| integral_rpowIntegrand₀₁_one_pos hp⟩
  let μ : Measure ℝ := C • volume.restrict (Ioi 0)
  refine ⟨μ, fun x hx => ?_⟩
  have : C • ∫ t in Ioi 0, rpowIntegrand₀₁ p t x = (C : ℝ) • ∫ t in Ioi 0, rpowIntegrand₀₁ p t x :=
    rfl
  rw [integral_smul_nnreal_measure, rpow_eq_const_mul_integral hp hx, this]
  rfl

end Real
