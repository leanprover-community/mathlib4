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

lemma comp_mul_left_div
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {p q : ℝ} (p_pos : 0 < p) (q_pos : 0 < q) {c : ℝ}
    (c_pos : 0 < c) : ContinuousOn (fun x ↦ f (c * x) / x) (uIcc p q) := by
  have hsub : uIcc p q ⊆ Ici 0 := by simp [uIcc, Icc_subset_Ici_iff, p_pos.le, q_pos.le]
  apply hf.comp_mul_left_div continuousOn_id
  all_goals intro x hx
  · simpa [mem_Ici] using mul_nonneg (le_of_lt c_pos) (hsub hx)
  · exact ((lt_min p_pos q_pos).trans_le hx.1).ne'

lemma intervalIntegrable_div
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntervalIntegrable (fun x ↦ f x / x) volume p q := by
  have hcont : ContinuousOn (fun x ↦ f (1 * x) / x) (uIcc p q) :=
    Frullani.comp_mul_left_div hf hp hq (by simp)
  simpa using hcont.intervalIntegrable

lemma exists_integral_div_eq_mul_log {a b : ℝ} {f : ℝ → ℝ} {y : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (y_pos : 0 < y) (hf : ContinuousOn f (Ici 0)) :
    ∃ c ∈ uIcc (a * y) (b * y), ∫ x in (a * y)..(b * y), f x / x = f c * log (b / a) := by
  have hay := mul_pos a_pos y_pos
  have hby := mul_pos b_pos y_pos
  have hf' : ContinuousOn f (uIcc (a * y) (b * y)) :=
    hf.mono (by simp [uIcc, Icc_subset_Ici_iff, hay.le, hby.le])
  obtain ⟨c, hc, heq⟩ := _root_.exists_integral_div_eq_mul_log hay hby hf'
  rw [mul_div_mul_right b a (ne_of_gt y_pos)] at heq
  exact ⟨c, hc, heq⟩

/-- **Frullani integral**.
If `f : ℝ → ℝ` is continuous on `[0, ∞)` with `Tendsto f atTop (𝓝 L)`, and `0 < a`, `0 < b`, then
`∫ x in Ioi 0, (f (a * x) - f (b * x)) / x = (f 0 - L) * log (b / a)`. -/
theorem integral_Ioi
    {a b : ℝ} {f : ℝ → ℝ} {L : ℝ} (a_pos : 0 < a) (b_pos : 0 < b) (hf : ContinuousOn f (Ici 0))
    (hlim : Tendsto f atTop (𝓝 L))
    (hint : IntegrableOn (fun x ↦ (f (a * x) - f (b * x)) / x) (Ioi 0)) :
    ∫ x in Ioi 0, (f (a * x) - f (b * x)) / x = (f 0 - L) * log (b / a) := by
  let g : ℝ → ℝ := fun x ↦ (f (a * x) - f (b * x)) / x
  have hg (ε R : ℝ) (hε : 0 < ε) (hR : ε < R) : ∫ x in ε..R, g x =
      (∫ x in a * ε..b * ε, f x / x) - (∫ x in a * R..b * R, f x / x) := by
    let u x := f x / x
    wlog hab : a ≤ b generalizing a b
    · have hint_neg :
        IntegrableOn (fun x ↦ - ((f (a * x) - f (b * x)) / x)) (Ioi 0) volume := hint.neg
      have hint_neg' : IntegrableOn (fun x ↦ (f (b * x) - f (a * x)) / x) (Ioi 0) volume := by
        convert hint_neg using 1
        ext
        ring
      simp only [not_le] at hab
      specialize this b_pos a_pos hint_neg' hab.le
      have hg_neg : (fun x ↦ (f (b * x) - f (a * x)) / x) = fun x ↦ - g x := by
        funext x
        unfold g
        ring
      simp only [hg_neg, intervalIntegral.integral_neg] at this
      rw [integral_symm (b * ε) (a * ε), integral_symm (b * R) (a * R), ← neg_inj, this]
      ring
    calc
      _ = (∫ x in ε..R, f (a * x) / x) - ∫ x in ε..R, f (b * x) / x := by
        simp_rw [g, sub_div]
        have hR_pos : 0 < R := by nlinarith
        apply intervalIntegral.integral_sub
        all_goals apply ContinuousOn.intervalIntegrable
        · exact Frullani.comp_mul_left_div hf hε hR_pos a_pos
        · exact Frullani.comp_mul_left_div hf hε hR_pos b_pos
      _ = (∫ y in a * ε..a * R, u y) - ∫ y in b * ε..b * R, u y := by
        have hfa_eq : ∫ x in ε..R, f (a * x) / x = ∫ y in a * ε..a * R, u y := by
          calc
            _ = ∫ x in ε..R, a * u (a * x) := by
              unfold u
              field_simp
            _ = a * ∫ x in ε..R, u (a * x) := by apply intervalIntegral.integral_const_mul
            _ = ∫ y in a * ε..a * R, u y := by apply mul_integral_comp_mul_left
        have hfb_eq : ∫ x in ε..R, f (b * x) / x = ∫ y in b * ε..b * R, u y := by
          calc
            _ = ∫ x in ε..R, b * u (b * x) := by
              congr
              funext x
              unfold u
              field_simp
            _ = b * ∫ x in ε..R, u (b * x) := by
              apply intervalIntegral.integral_const_mul
            _ = ∫ y in b * ε..b * R, u y := by
              apply mul_integral_comp_mul_left
        rw [hfa_eq, hfb_eq]
      _ = (∫ x in a * ε..b * ε, u x) - (∫ x in a * R..b * R, u x) := by
        apply integral_interval_sub_interval_comm
        all_goals
          apply intervalIntegrable_div hf
          all_goals nlinarith
  change ∫ x in Ioi 0, g x = (f 0 - L) * log (b / a)
  have hc (y : ℝ) (y_pos : 0 < y) : ∃ c ∈ uIcc (a * y) (b * y),
      (∫ x in (a * y)..(b * y), f x / x) = f c * log (b / a) :=
    exists_integral_div_eq_mul_log a_pos b_pos y_pos hf
  let F : ℝ → ℝ := fun R ↦ ∫ x in 0..R, g x
  have h_lhs : Tendsto F atTop (𝓝 (∫ x in Ioi 0, g x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have h_rhs : Tendsto F atTop (𝓝 ((f 0 - L) * log (b / a))) := by
    unfold F
    choose! fc hy_mem hy_eq using hc
    have hg' (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
        ∫ x in ε..R, g x = (f (fc ε) - f (fc R)) * log (b / a) := by
      have hR_pos : 0 < R := by linarith
      rw [hg ε R hε hεR, hy_eq ε hε, hy_eq R hR_pos]
      field_simp
    have h_lim_L : Tendsto (fun R ↦ f (fc R)) atTop (𝓝 L) := by
      apply hlim.comp
      let m := min a b
      have hm_pos : 0 < m := by grind
      have h_ev_le : (fun y ↦ m * y) ≤ᶠ[atTop] fc := by
        rw [EventuallyLE, eventually_atTop]
        use 1
        intro y hy1
        have hy_pos : 0 < y := by linarith
        have hy := hy_mem y hy_pos
        simp only [ge_iff_le]
        rw [mem_uIcc] at hy
        rcases hy with h | h
        · have : m ≤ a := by grind
          nlinarith
        · have : m ≤ b := by grind
          nlinarith
      have h_lim_atTop : Tendsto (fun y ↦ m * y) atTop atTop := by
        simpa [tendsto_const_mul_atTop_of_pos hm_pos] using tendsto_id
      exact tendsto_atTop_mono' atTop h_ev_le h_lim_atTop
    have h_tail (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
        ∫ x in Ioi ε, g x = (f (fc ε) - L) * log (b / a) := by
      have hR' : Tendsto (fun R ↦ ∫ x in ε..R, g x) atTop (𝓝 (∫ x in Ioi ε, g x)) := by
        apply intervalIntegral_tendsto_integral_Ioi
        · apply hint.mono_set (Ioi_subset_Ioi hε.le)
        · exact tendsto_id
      have hR : Tendsto (fun R ↦ ∫ x in ε..R, g x) atTop (𝓝 ((f (fc ε) - L) * log (b / a))) := by
        have h_ev_eq : (fun R ↦ ∫ x in ε..R, g x) =ᶠ[atTop]
            (fun R ↦ (f (fc ε) - f (fc R)) * log (b / a)) := by
          apply (eventually_gt_atTop ε).mono
          intro R hεR'
          exact hg' ε R hε hεR'
        rw [tendsto_congr' h_ev_eq]
        have h_lim_const : Tendsto (fun _ : ℝ ↦ f (fc ε)) atTop (𝓝 (f (fc ε))) := tendsto_const_nhds
        have h_sub : Tendsto (fun R ↦ (f (fc ε) - f (fc R))) atTop (𝓝 ((f (fc ε)) - L)) :=
          h_lim_const.sub h_lim_L
        have h_const_log : Tendsto (fun _ : ℝ ↦ log (b / a)) atTop (𝓝 (log (b / a))) :=
          tendsto_const_nhds
        exact h_sub.mul h_const_log
      exact tendsto_nhds_unique hR' hR
    have hε : Tendsto (fun ε ↦ ∫ x in Ioi ε, g x) (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, g x)) :=
      IntegrableOn.tendsto_integral_Ioi hint
    have h_lim_f_zero : Tendsto (fun ε ↦ f (fc ε)) (𝓝[>] 0) (𝓝 (f 0)) := by
      have h_lim_zero : Tendsto (fun ε ↦ (max a b) * ε) (𝓝[>] 0) (𝓝 0) := by
        have hc : ContinuousWithinAt (fun ε : ℝ ↦ (max a b) * ε) (Ioi (0 : ℝ)) 0 :=
          (continuous_mul_left (max a b)).continuousWithinAt
        simpa using hc.tendsto
      have h_ev_fc_nonneg : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ fc ε := by
        apply eventually_of_mem self_mem_nhdsWithin
        intro ε hε
        have hmem := hy_mem ε hε
        have hε_pos : 0 < ε := by grind
        have hmin_nonneg : 0 ≤ min (a * ε) (b * ε) := by apply le_min (by nlinarith) (by nlinarith)
        apply le_trans hmin_nonneg
        rw [mem_uIcc] at hmem
        grind
      have h_ev_fc_le_max : ∀ᶠ ε in 𝓝[>] 0, fc ε ≤ (max a b) * ε := by
        apply eventually_of_mem self_mem_nhdsWithin
        intro ε hε
        have hmem := hy_mem ε hε
        rw [max_mul_of_nonneg a b hε.le]
        rw [mem_uIcc] at hmem
        grind
      have hcont_zero : ContinuousWithinAt f (Ici (0 : ℝ)) 0 := by
        apply hf.continuousWithinAt (by simp)
      have hfc_within : Tendsto fc (𝓝[>] 0) (𝓝[Ici (0 : ℝ)] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
            tendsto_const_nhds h_lim_zero h_ev_fc_nonneg h_ev_fc_le_max
        · exact h_ev_fc_nonneg
      exact hcont_zero.tendsto.comp hfc_within
    have h_main : ∫ x in Ioi 0, g x = (f 0 - L) * log (b / a) := by
      have h_ev_eq : (fun ε ↦ ∫ x in Ioi ε, g x) =ᶠ[𝓝[>] 0]
          (fun ε ↦ (f (fc ε) - L) * log (b / a)) := by
        change (∀ᶠ ε in 𝓝[>] 0, ∫ x in Ioi ε, g x = (f (fc ε) - L) * log (b / a))
        apply eventually_of_mem self_mem_nhdsWithin
        intro ε hε
        simp [h_tail ε (ε + 1) hε]
      have h_rhs_from_left : Tendsto (fun ε ↦ (f (fc ε) - L) * log (b / a))
          (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, g x)) := by rwa [← tendsto_congr' h_ev_eq]
      have h_lim_f_zero_sub_L : Tendsto (fun ε ↦ f (fc ε) - L) (𝓝[>] 0) (𝓝 (f 0 - L)) :=
        h_lim_f_zero.sub tendsto_const_nhds
      have h_rhs_goal : Tendsto (fun ε ↦ (f (fc ε) - L) * log (b / a))
          (𝓝[>] 0) (𝓝 ((f 0 - L) * log (b / a))) := h_lim_f_zero_sub_L.mul_const (log (b / a))
      exact tendsto_nhds_unique h_rhs_from_left h_rhs_goal
    rwa [h_main] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

end Frullani
