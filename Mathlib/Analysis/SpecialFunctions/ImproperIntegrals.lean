/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Louis (Yiyang) Liu
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `intervalIntegral`).

## See also

- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: specific integrals over finite intervals
- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`: integral of `exp (-x ^ 2)`
- `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`: integrability of `(1+‖x‖)^(-r)`.
-/

public section


open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

theorem integrableOn_exp_Iic (c : ℝ) : IntegrableOn exp (Iic c) := by
  refine
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => ?_)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le

theorem integrableOn_exp_neg_Ioi (c : ℝ) : IntegrableOn (fun (x : ℝ) => exp (-x)) (Ioi c) :=
  Iff.mp integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_Iic (-c)).comp_neg_Ici

theorem integral_exp_Iic (c : ℝ) : ∫ x : ℝ in Iic c, exp x = exp c := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) ?_
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _

theorem integral_exp_Iic_zero : ∫ x : ℝ in Iic 0, exp x = 1 :=
  exp_zero ▸ integral_exp_Iic 0

theorem integral_exp_neg_Ioi (c : ℝ) : (∫ x : ℝ in Ioi c, exp (-x)) = exp (-c) := by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

theorem integral_exp_neg_Ioi_zero : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 := by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

theorem integrableOn_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simpa [Complex.norm_exp] using
      (integrableOn_Ioi_comp_mul_left_iff (fun x => exp (-x)) c (a := -a.re) (by simpa)).mpr <|
        integrableOn_exp_neg_Ioi _

theorem integrableOn_exp_mul_complex_Iic {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Iic c) := by
  simpa using Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)).comp_neg_Iio

theorem integrableOn_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Ioi c) := by
  have := Integrable.norm <| integrableOn_exp_mul_complex_Ioi (a := a) (by simpa using ha) c
  simpa [Complex.norm_exp] using this

theorem integrableOn_exp_mul_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Iic c) := by
  have := Integrable.norm <| integrableOn_exp_mul_complex_Iic (a := a) (by simpa using ha) c
  simpa [Complex.norm_exp] using this

theorem integral_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    ∫ x : ℝ in Set.Ioi c, Complex.exp (a * x) = - Complex.exp (a * c) / a := by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_exp_mul_complex_Ioi ha c) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := a) (by aesop), id_eq]
  suffices Tendsto (fun x : ℝ ↦ Complex.exp (a * x)) atTop (𝓝 0) by
    simpa using this.sub_const _ |>.div_const _
  simpa [Complex.tendsto_exp_nhds_zero_iff] using tendsto_const_nhds.neg_mul_atTop ha tendsto_id

theorem integral_exp_mul_complex_Iic {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    ∫ x : ℝ in Set.Iic c, Complex.exp (a * x) = Complex.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, ← Complex.ofReal_neg,
    integral_comp_neg_Ioi (f := fun x : ℝ ↦ Complex.exp (a * x))]
    using integral_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)

set_option backward.isDefEq.respectTransparency false in
theorem integral_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    ∫ x : ℝ in Set.Ioi c, Real.exp (a * x) = - Real.exp (a * c) / a := by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re, integral_exp_mul_complex_Ioi (by simpa using ha), RCLike.re_to_complex,
    RCLike.re_to_complex, Complex.div_ofReal_re, Complex.neg_re]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using ha) _

theorem integral_exp_mul_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ in Set.Iic c, Real.exp (a * x) = Real.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, integral_comp_neg_Ioi (f := fun x : ℝ ↦ Real.exp (a * x))]
    using integral_exp_mul_Ioi (a := -a) (by simpa) (-c)

/-- If `-m < c`, then `(fun t : ℝ ↦ (t + m) ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_add_rpow_Ioi_of_lt {a c m : ℝ} (ha : a < -1) (hc : -m < c) :
    IntegrableOn (fun (x : ℝ) ↦ (x + m) ^ a) (Ioi c) := by
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t ↦ (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    convert (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show a + 1 ≠ 0 by linarith]
    left; linarith [mem_Ici.mp hx, id_eq x]
  have ht : Tendsto (fun t ↦ ((t + m) ^ (a + 1)) / (a + 1)) atTop (nhds (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ m tendsto_id) |>.div_const _
  exact integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t ht ↦ rpow_nonneg (by linarith [mem_Ioi.mp ht]) a) ht

/-- If `0 < c`, then `(fun t : ℝ ↦ t ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_Ioi_rpow_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ t ^ a) (Ioi c) := by
  simpa using integrableOn_add_rpow_Ioi_of_lt ha (by simpa : -0 < c)

theorem integrableOn_Ioi_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioi t) ↔ s < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  have : IntegrableOn (fun x ↦ x⁻¹) (Ioi (max 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have x_one : 1 ≤ x := ((le_max_left _ _).trans_lt (mem_Ioi.1 hx)).le
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans x_one)]
    rw [← Real.rpow_neg_one x]
    exact Real.rpow_le_rpow_of_exponent_le x_one h
  exact not_integrableOn_Ioi_inv this

theorem integrableAtFilter_rpow_atTop_iff {s : ℝ} :
    IntegrableAtFilter (fun x : ℝ ↦ x ^ s) atTop ↔ s < -1 := by
  refine ⟨fun ⟨t, ht, hint⟩ ↦ ?_, fun h ↦
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr h⟩⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp ht
  refine (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right a 1))).mp ?_
  exact hint.mono_set <| fun x hx ↦ ha _ <| (le_max_left a 1).trans hx.le

/-- The real power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_rpow (s : ℝ) : ¬ IntegrableOn (fun x ↦ x ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_gt s (-1) with hs | hs
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioi (1 : ℝ)) := h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_rpow_iff zero_lt_one] at this
    exact hs.not_gt this

theorem setIntegral_Ioi_zero_rpow (s : ℝ) : ∫ x in Ioi (0 : ℝ), x ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

theorem integral_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi c, t ^ a = -c ^ (a + 1) / (a + 1) := by
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    convert (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t => t ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_rpow_of_lt ha hc) ht using 1
  simp only [neg_div, zero_div, zero_sub]

theorem integrableOn_Ioi_norm_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ ‖(t : ℂ) ^ a‖) (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc.trans hx)]

theorem integrableOn_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ a) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp <| integrableOn_Ioi_norm_cpow_of_lt ha hc
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt

theorem integrableOn_Ioi_norm_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ s‖) (Ioi t) ↔ s.re < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_norm_cpow_of_lt h ht⟩
  refine (integrableOn_Ioi_rpow_iff ht).mp <| h.congr_fun (fun a ha ↦ ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht.trans ha)]

theorem integrableOn_Ioi_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi t) ↔ s.re < -1 :=
  ⟨fun h ↦ (integrableOn_Ioi_norm_cpow_iff ht).mp h.norm, fun h ↦ integrableOn_Ioi_cpow_of_lt h ht⟩

theorem integrableOn_Ioi_deriv_ofReal_cpow {s : ℂ} {t : ℝ} (ht : 0 < t) (hs : s.re < 0) :
    IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ s) (Set.Ioi t) := by
  have h : IntegrableOn (fun x : ℝ ↦ s * x ^ (s - 1)) (Set.Ioi t) := by
    refine (integrableOn_Ioi_cpow_of_lt ?_ ht).const_mul _
    rwa [Complex.sub_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel]
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.deriv_ofReal_cpow_const (ht.trans hx).ne' (fun h ↦ (Complex.zero_re ▸ h ▸ hs).false)]

theorem integrableOn_Ioi_deriv_norm_ofReal_cpow {s : ℂ} {t : ℝ} (ht : 0 < t) (hs : s.re ≤ 0) :
    IntegrableOn (deriv fun x : ℝ ↦ ‖(x : ℂ) ^ s‖) (Set.Ioi t) := by
  rw [integrableOn_congr_fun (fun x hx ↦ by
    rw [deriv_norm_ofReal_cpow _ (ht.trans hx)]) measurableSet_Ioi]
  obtain hs | hs := eq_or_lt_of_le hs
  · simp_rw [hs, zero_mul]
    exact integrableOn_zero
  · replace hs : s.re - 1 < -1 := by rwa [sub_lt_iff_lt_add, neg_add_cancel]
    exact (integrableOn_Ioi_rpow_of_lt hs ht).const_mul s.re

/-- The complex power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_cpow (s : ℂ) :
    ¬ IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_gt s.re (-1) with hs | hs
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioo (0 : ℝ) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi 1) :=
      h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_cpow_iff zero_lt_one] at this
    exact hs.not_gt this

theorem setIntegral_Ioi_zero_cpow (s : ℂ) : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

theorem integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, (t : ℂ) ^ a) = -(c : ℂ) ^ (a + 1) / (a + 1) := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : ℝ => ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.congr' ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
    dsimp only
    rw [integral_cpow, id]
    refine Or.inr ⟨?_, notMem_uIcc_of_lt hc hx⟩
    apply_fun Complex.re
    rw [Complex.neg_re, Complex.one_re]
    exact ha.ne
  simp_rw [← zero_sub, sub_div]
  refine (Tendsto.div_const ?_ _).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
  simp_rw [neg_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re]

theorem integrable_inv_one_add_sq : Integrable fun (x : ℝ) ↦ (1 + x ^ 2)⁻¹ := by
  suffices Integrable fun (x : ℝ) ↦ (1 + ‖x‖ ^ 2) ^ ((-2 : ℝ) / 2) by simpa [rpow_neg_one]
  exact integrable_rpow_neg_one_add_norm_sq (by simp)

@[simp]
theorem integral_Iic_inv_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Iic i, (1 + x ^ 2)⁻¹ = arctan i + (π / 2) :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    |>.trans (sub_neg_eq_add _ _)

@[simp]
theorem integral_Ioi_inv_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Ioi i, (1 + x ^ 2)⁻¹ = (π / 2) - arctan i :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]
theorem integral_univ_inv_one_add_sq : ∫ (x : ℝ), (1 + x ^ 2)⁻¹ = π :=
  (by ring : π = (π / 2) - (-(π / 2))) ▸ integral_of_hasDerivAt_of_tendsto hasDerivAt_arctan'
    integrable_inv_one_add_sq (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

namespace Frullani

open Metric

variable {f : ℝ → ℝ} {a b c d L R : ℝ}

lemma comp_mul_left_div (hf : ContinuousOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ContinuousOn (fun x ↦ f (c * x) / x) (uIcc a b) := by
  have hsub : uIcc a b ⊆ Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  apply hf.comp_mul_left_div continuousOn_id
  all_goals intro x hx
  · exact mul_pos hc (hsub hx)
  · exact ne_of_gt (hsub hx)

lemma intervalIntegrable_comp_mul_div (hf : ContinuousOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : IntervalIntegrable (fun x ↦ f (c * x) / x) volume a b :=
  (comp_mul_left_div hf ha hb hc).intervalIntegrable

lemma exists_integral_div_eq_mul_log (hf : ContinuousOn f (Ici 0)) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    ∃ d ∈ uIcc (a * c) (b * c), ∫ x in (a * c)..(b * c), f x / x = f d * log (b / a) := by
  have hac := mul_pos ha hc
  have hbc := mul_pos hb hc
  have hf' : ContinuousOn f (uIcc (a * c) (b * c)) :=
    hf.mono (by simp [uIcc, Icc_subset_Ici_iff, hac.le, hbc.le])
  obtain ⟨d, hd, heq⟩ := _root_.exists_integral_div_eq_mul_log hac hbc hf'
  rw [mul_div_mul_right b a (ne_of_gt hc)] at heq
  exact ⟨d, hd, heq⟩

lemma integral_comp_mul_div {ε r : ℝ} (hc : 0 < c) :
    ∫ x in ε..r, f (c * x) / x = ∫ x in c * ε..c * r, f x / x := by
  let u : ℝ → ℝ := fun x ↦ f x / x
  change _ = ∫ x in c * ε..c * r, u x
  have : (fun x ↦ f (c * x) / x) = fun x ↦ c * u (c * x) := by
    ext x
    field
  simp [this]

lemma min_mul_le_of_mem_uIcc_mul {y : ℝ} (hy : 0 ≤ y)
    (hd : d ∈ uIcc (a * y) (b * y)) : min a b * y ≤ d := by
  grind [mem_uIcc, min_mul_of_nonneg a b hy]

lemma le_max_mul_of_mem_uIcc_mul {y : ℝ} (hy : 0 ≤ y)
    (hd : d ∈ uIcc (a * y) (b * y)) : d ≤ max a b * y := by
  grind [mem_uIcc, max_mul_of_nonneg a b hy]

lemma pos_of_mem_uIcc_mul (ha : 0 < a) (hb : 0 < b) {y : ℝ} (hy : 0 < y)
    (hd : d ∈ uIcc (a * y) (b * y)) : 0 < d := by
  grind [mem_uIcc, mul_pos ha hy, mul_pos hb hy]

/-- **Frullani's integral**, limit form. If `f` is continuous on `(0, ∞)` with `f x → L` as `x → 0⁺`
and `f x → R` as `x → +∞`, and `0 < a` and `0 < b`, then
`∫ x in ε..r, (f (a * x) - f (b * x)) / x → (L - R) * log (b / a)` as `ε → 0⁺` and `r → +∞`. -/
theorem tendsto_intervalIntegral (hf : ContinuousOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun p : ℝ × ℝ ↦ ∫ x in p.1..p.2, (f (a * x) - f (b * x)) / x) ((𝓝[>] 0) ×ˢ atTop)
      (𝓝 ((L - R) * log (b / a))) := by
  let u := fun x ↦ f x / x
  have hsubset {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : uIcc p q ⊆ Ioi 0 := by
    simp [uIcc, Icc_subset_Ioi_iff, hp, hq]
  have hint {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : IntervalIntegrable u volume p q := by
    simpa using intervalIntegrable_comp_mul_div hf hp hq one_pos
  have hint' {c p q : ℝ} (hc : 0 < c) (hp : 0 < p) (hq : 0 < q) :
      IntervalIntegrable (fun x ↦ f (c * x) / x) volume p q :=
    intervalIntegrable_comp_mul_div hf hp hq hc
  have hmvt {y : ℝ} (hy : 0 < y) : ∃ d ∈ uIcc (a * y) (b * y),
      ∫ x in (a * y)..(b * y), u x = f d * log (b / a) := by
    have h := _root_.exists_integral_div_eq_mul_log (mul_pos ha hy) (mul_pos hb hy)
      (hf.mono (hsubset (mul_pos ha hy) (mul_pos hb hy)))
    field_simp at h
    simpa [mul_comm] using h
  choose! d hd_mem hd_eq using fun y (hy : 0 < y) ↦ hmvt hy
  have hsplit {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) : ∫ x in ε..r, (f (a * x) - f (b * x)) / x =
      (∫ x in (a * ε)..(b * ε), u x) - ∫ x in (a * r)..(b * r), u x := by
    calc
      _ = (∫ x in ε..r, f (a * x) / x) - ∫ x in ε..r, f (b * x) / x := by
        simp_rw [sub_div]
        exact integral_sub (hint' ha hε hr) (hint' hb hε hr)
      _ = (∫ y in a * ε..a * r, u y) - ∫ y in b * ε..b * r, u y := by
        rw [integral_comp_mul_div ha, integral_comp_mul_div hb]
      _ = _ := integral_interval_sub_interval_comm
        (hint (mul_pos ha hε) (mul_pos ha hr))
        (hint (mul_pos hb hε) (mul_pos hb hr))
        (hint (mul_pos ha hε) (mul_pos hb hε))
  have hd_zero : Tendsto (fun ε ↦ f (d ε)) (𝓝[>] 0) (𝓝 L) := by
    apply hL.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      · exact (by simpa using tendsto_const_nhds.mul (@tendsto_id ℝ (𝓝 0)) :
            Tendsto (fun ε ↦ max a b * ε) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
          (pos_of_mem_uIcc_mul ha hb hε (hd_mem ε hε)).le
      · exact eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
          le_max_mul_of_mem_uIcc_mul hε.le (hd_mem ε hε)
    · exact eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
        mem_Ioi.2 (pos_of_mem_uIcc_mul ha hb hε (hd_mem ε hε))
  have hd_atTop : Tendsto (fun r ↦ f (d r)) atTop (𝓝 R) := by
    apply hR.comp
    have hm : 0 < min a b := by grind
    have h_lim : Tendsto (fun y ↦ min a b * y) atTop atTop := by
      simpa [tendsto_const_mul_atTop_of_pos hm] using tendsto_id
    apply tendsto_atTop_mono' atTop _ h_lim
    exact eventually_atTop.2 ⟨1, fun r hr ↦
      min_mul_le_of_mem_uIcc_mul (by linarith) (hd_mem r (by linarith))⟩
  have h_ev : (fun p : ℝ × ℝ ↦ ∫ x in p.1..p.2, (f (a * x) - f (b * x)) / x) =ᶠ[(𝓝[>] 0) ×ˢ atTop]
      fun p ↦ (f (d p.1) - f (d p.2)) * log (b / a) := by
    filter_upwards [prod_mem_prod (eventually_nhdsWithin_of_forall fun _ h ↦ h)
      (eventually_atTop.2 ⟨1, fun _ h ↦ lt_of_lt_of_le one_pos h⟩)] with ⟨ε, r⟩ ⟨hε, hr⟩
    rw [hsplit hε hr, hd_eq _ hε, hd_eq _ hr]
    ring
  rw [tendsto_congr' h_ev]
  exact ((hd_zero.comp tendsto_fst).sub (hd_atTop.comp tendsto_snd)).mul tendsto_const_nhds

/-- **Frullani's integral**. If `f` is continuous on `(0, ∞)` with `f x → L` as `x → 0⁺` and
`f x → R` as `x → +∞`, `0 < a` and `0 < b`, and `x ↦ (f (a * x) - f (b * x)) / x` is integrable on
`(0, ∞)`, then
`∫ x in Ioi 0, (f (a * x) - f (b * x)) / x = (L - R) * log (b / a)`. -/
theorem integral_Ioi_eq (hf : ContinuousOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R))
    (hint : IntegrableOn (fun x ↦ (f (a * x) - f (b * x)) / x) (Ioi 0)) :
    ∫ x in Ioi 0, (f (a * x) - f (b * x)) / x = (L - R) * log (b / a) := by
  have h_lim := (tendsto_intervalIntegral hf ha hb hL hR).mono_left curry_le_prod
  set g := fun x ↦ (f (a * x) - f (b * x)) / x with hg
  apply tendsto_nhds_unique
    (hint.continuousWithinAt_Ici_primitive_Ioi.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
  rw [tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds] at h_lim
  specialize h_lim (ε / 2) (by positivity)
  rw [eventually_curry_iff, Filter.Eventually, mem_nhdsWithin_iff] at h_lim
  obtain ⟨δ, hδ_pos, hδ⟩ := h_lim
  simp_rw [subset_def, mem_inter_iff, mem_ball] at hδ
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx hdist
  specialize hδ x ⟨hdist, hx⟩
  rw [mem_setOf] at hδ
  have hint' : IntegrableOn g (Ioi x) := hint.mono (by grind) (by simp)
  have htends := intervalIntegral_tendsto_integral_Ioi x hint' tendsto_id
  have hle := le_of_tendsto (htends.dist tendsto_const_nhds) (hδ.mono (fun _ hy ↦ hy.le))
  linarith

end Frullani
