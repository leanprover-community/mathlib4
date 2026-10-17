/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Prékopa–Leindler inequality and Brunn–Minkowski theorem
-/

public section

open scoped ENNReal
open Module

namespace MeasureTheory

variable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)

include ha0 ha1 in
private theorem prekopa_leindler_real_of_iSup_eq_one {f g j : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (hf1 : ⨆ x, f x = 1) (hg1 : ⨆ x, g x = 1)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  open scoped Pointwise in
  have hsupport {e : ℝ → ℝ≥0∞} (he : ⨆ x, e x = 1) :
      Function.support (fun t ↦ volume {x | .ofReal t ≤ e x}) ⊆ Set.Iic 1 := by
    intro t
    contrapose
    suffices 1 < t → {x | .ofReal t ≤ e x} = ∅ by simp +contextual [this]
    intro ht
    ext x
    suffices e x < .ofReal t by simpa
    grw [le_iSup e, he]
    simpa using ht
  have hnonempty {t : ℝ} (ht : t ∈ Set.Ioo 0 1) {e : ℝ → ℝ≥0∞} (he : ⨆ x, e x = 1) :
      {x | .ofReal t ≤ e x}.Nonempty := by
    have h := not_imp_not.mpr <| le_iSup_iff.mp (he.symm.le) (.ofReal t)
    push Not at h
    obtain ⟨x, hx⟩ := h (by simpa using ht.2)
    exact ⟨x, hx.le⟩
  calc
    _ ≤ .ofReal (1 - a) * (∫⁻ x, f x) + .ofReal a * (∫⁻ x, g x) := by
      convert ENNReal.geom_mean_le_arith_mean2_weighted (1 - a).toNNReal a.toNNReal _ _ ?_
      · simp [ha1]
      · simp [ha0]
      · rw [ENNReal.ofNNReal_toNNReal]
      · rw [ENNReal.ofNNReal_toNNReal]
      · rw [← Real.toNNReal_add (by simp [ha1]) (by simp [ha0]), sub_add_cancel,
          Real.toNNReal_one]
    _ = (∫⁻ t in Set.Ioo 0 1, volume ((1 - a) • {x | .ofReal t ≤ f x})) +
        (∫⁻ t in Set.Ioo 0 1, volume (a • {x | .ofReal t ≤ g x})) := by
      simp_rw [Measure.addHaar_smul_of_nonneg _ ha0,
        Measure.addHaar_smul_of_nonneg _ (sub_nonneg.mpr ha1), finrank_self, pow_one]
      rw [lintegral_eq_lintegral_measure_ofReal_le _ hf.aemeasurable,
        lintegral_eq_lintegral_measure_ofReal_le _ hg.aemeasurable,
        ← setLIntegral_eq_of_support_subset (hsupport hf1), Measure.restrict_restrict (by simp),
        ← setLIntegral_eq_of_support_subset (hsupport hg1), Measure.restrict_restrict (by simp),
        ← lintegral_const_mul' _ _ (by simp), ← lintegral_const_mul' _ _ (by simp)]
      congrm $(setLIntegral_congr ?set) + $(setLIntegral_congr ?set)
      exact (Ioo_ae_eq_Ioc.trans (by simp [Set.Iic_inter_Ioi])).symm
    _ ≤ ∫⁻ t in Set.Ioo 0 1, volume {x | .ofReal t ≤ j x}  := by
      grw [le_lintegral_add]
      refine setLIntegral_mono' (by simp) fun t ht ↦ ?_
      grw [Real.volume_add_volume_le (hnonempty ht hf1).smul_set (hnonempty ht hg1).smul_set]
      refine measure_mono fun x hx ↦ ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
      obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.mp hy
      obtain ⟨z', hz', rfl⟩ := Set.mem_smul_set.mp hz
      simp only [Set.mem_ofPred_eq] at hy' hz' ⊢
      specialize h y' z'
      grw [← hy', ← hz', ← ENNReal.rpow_add_of_nonneg _ _ (by simpa using ha1) ha0,
        sub_add_cancel, ENNReal.rpow_one] at h
      exact h
    _ ≤ _ := by
      rw [lintegral_eq_lintegral_measure_ofReal_le _ hj.aemeasurable]
      exact lintegral_mono_set Set.Ioo_subset_Ioi_self

include ha0 ha1 in
private theorem prekopa_leindler_real_of_iSup_ne_top {f g j : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (hftop : ⨆ x, f x ≠ ∞) (hgtop : ⨆ x, g x ≠ ∞)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  by_cases hf0 : ⨆ x, f x = 0
  · rw [ENNReal.iSup_eq_zero] at hf0
    rcases lt_or_eq_of_le ha1 with ha1 | rfl
    · simp [hf0, ha1]
    · have : ∀ (y : ℝ), g y ≤ j y := by simpa using h
      simpa using lintegral_mono this
  by_cases hg0 : ⨆ x, g x = 0
  · rw [ENNReal.iSup_eq_zero] at hg0
    rcases lt_or_eq_of_le ha0 with ha0 | rfl
    · simp [hg0, ha0]
    · have : ∀ (y : ℝ), f y ≤ j y := by simpa using h
      simpa using lintegral_mono this
  have hj' : Measurable (j · * ((⨆ x, f x)⁻¹ ^ (1 - a) * (⨆ x, g x)⁻¹ ^ a)) := by fun_prop
  have hf1 : ⨆ x, f x * (⨆ x, f x)⁻¹ = 1 := by
    rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel hf0 hftop]
  have hg1 : ⨆ x, g x * (⨆ x, g x)⁻¹ = 1 := by
    rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel hg0 hgtop]
  have h' (x y) : (f x * (⨆ x, f x)⁻¹) ^ (1 - a) * (g y * (⨆ x, g x)⁻¹) ^ a ≤
      j ((1 - a) * x + a * y) * ((⨆ x, f x)⁻¹ ^ (1 - a) * (⨆ x, g x)⁻¹ ^ a) := by
    grw [← h x y, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    exact le_of_eq (by ring)
  have h := prekopa_leindler_real_of_iSup_eq_one ha0 ha1 (by fun_prop) (by fun_prop) hj' hf1 hg1 h'
  rw [lintegral_mul_const _ hf, lintegral_mul_const _ hg, lintegral_mul_const _ hj,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h
  rw [← ENNReal.mul_le_mul_iff_left (c := ((⨆ x, f x)⁻¹ ^ (1 - a) * (⨆ x, g x)⁻¹ ^ a))
    (by simp; grind) (by finiteness)]
  convert h using 1
  ring

include ha0 ha1 in
private theorem prekopa_leindler_real {f g j : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x :=
  calc
    _ = (∫⁻ x, ⨆ t : ℕ, min (f x) t) ^ (1 - a) * (∫⁻ x, ⨆ t : ℕ, min (g x) t) ^ a := by
      simp_rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    _ = (⨆ t : ℕ, (∫⁻ x, min (f x) t) ^ (1 - a)) * ⨆ t : ℕ, (∫⁻ x, min (g x) t) ^ a := by
      congr
      <;> rw [lintegral_iSup (by fun_prop) fun t u h x ↦ by simp [h],
        ENNReal.iSup_rpow_of_nonneg (by grind)]
    _ = ⨆ (u : ℕ) (t : ℕ), (∫⁻ x,  min (f x) t) ^ (1 - a) * (∫⁻ x, min (g x) u) ^ a := by
      simp_rw [ENNReal.mul_iSup, ENNReal.iSup_mul]
    _ ≤ _ := by
      refine iSup_le fun u ↦ iSup_le fun t ↦ ?_
      apply prekopa_leindler_real_of_iSup_ne_top ha0 ha1 (by fun_prop) (by fun_prop) hj
      · exact lt_top_iff_ne_top.mp (iSup_lt_iff.mpr ⟨t + 1, by simp⟩)
      · exact lt_top_iff_ne_top.mp (iSup_lt_iff.mpr ⟨u + 1, by simp⟩)
      · intro x y
        grw [← h x y]
        gcongr <;> simp

include ha0 ha1 in
private theorem prekopa_leindler_pi {d : ℕ} {f g j : (Fin d → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) • x + a • y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  induction d with
  | zero => simpa [lintegral_unique, volume_pi, Unique.eq_default] using h default default
  | succ d ih =>
    calc
      _ = (∫⁻ (x) (y), f (Fin.cons x y)) ^ (1 - a) * (∫⁻ (x) (y), g (Fin.cons x y)) ^ a := by
        simp_rw [volume_pi, (measurePreserving_piFinSuccAbove _ 0).symm.lintegral_map_equiv _ _]
        rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
        simp
      _ ≤ ∫⁻ (x) (y), j (Fin.cons x y) := by
        refine prekopa_leindler_real ha0 ha1 (by fun_prop) (by fun_prop) (by fun_prop) fun x y ↦ ?_
        refine ih (by fun_prop) (by fun_prop) (by fun_prop) fun u v ↦ ?_
        convert h (Fin.cons x u) (Fin.cons y v)
        ext i
        cases i using Fin.cases <;> simp
      _ = ∫⁻ x, j x := by
        simp_rw [volume_pi, (measurePreserving_piFinSuccAbove _ 0).symm.lintegral_map_equiv _ _]
        rw [lintegral_prod _ (by fun_prop)]
        simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

include ha0 ha1 in
/-- **Prékopa–Leindler inequality** for real vector space. -/
theorem lintegral_rpow_mul_lintegral_rpow_le {f g j : E → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) • x + a • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - a) * (∫⁻ x, g x ∂μ) ^ a ≤ ∫⁻ x, j x ∂μ := by
  let e : E ≃ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    (nonempty_linearEquiv_iff_lift_rank_eq.mpr (by simp)).some
  replace e := e.toContinuousLinearEquiv
  obtain ⟨c, _, hc⟩ := e.toLinearMap.exists_map_addHaar_eq_smul_addHaar μ volume e.surjective
  suffices (∫⁻ x, f (e.symm x) ∂(μ.map e)) ^ (1 - a) * (∫⁻ x, g (e.symm x) ∂(μ.map e)) ^ a ≤
      ∫⁻ x, j  (e.symm x) ∂(μ.map e) by
    rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop),
      lintegral_map (by fun_prop) (by fun_prop)] at this
    simpa
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hc
  simp_rw [hc, lintegral_smul_measure, smul_eq_mul]
  calc
    _ = c * ((∫⁻ x, f (e.symm x)) ^ (1 - a) * (∫⁻ x, g (e.symm x)) ^ a) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp [ha1]),
        ENNReal.mul_rpow_of_nonneg _ _ ha0, mul_mul_mul_comm,
        ← ENNReal.rpow_add_of_nonneg _ _ (by simp [ha1]) ha0, sub_add_cancel,
        ENNReal.rpow_one]
    _ ≤ _ := by
      gcongr
      refine prekopa_leindler_pi ha0 ha1 (by fun_prop) (by fun_prop) (by fun_prop) fun x y ↦ ?_
      simpa using h (e.symm x) (e.symm y)

include ha0 ha1 in
open Pointwise in
/-- **Brunn–Minkowski theorem** for real vector space, multiplicative version. -/
theorem measure_rpow_mul_measure_rpow_le {A B : Set E} (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ A ^ (1 - a) * μ B ^ a ≤ μ ((1 - a) • A + a • B) := by
  obtain ⟨C, hABC, hC, hμC⟩ := exists_measurable_superset μ ((1 - a) • A + a • B)
  rw [← hμC]
  rw [← lintegral_indicator_fun_one hA, ← lintegral_indicator_fun_one hB,
    ← lintegral_indicator_fun_one hC]
  apply lintegral_rpow_mul_lintegral_rpow_le ha0 ha1 μ (by fun_prop) (by fun_prop) (by fun_prop)
  intro x y
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ B
    · apply ge_of_eq
      aesop (add safe [Set.add_mem_add, Set.smul_mem_smul_set])
    · rcases lt_or_eq_of_le ha0 with ha0 | rfl
      · simp [hy, ha0]
      · have : A ⊆ C := by simpa [hBn] using hABC
        simpa using Set.indicator_le_indicator_of_subset this zero_le x
  · rcases lt_or_eq_of_le ha1 with ha1 | rfl
    · simp [hx, ha1]
    · have : B ⊆ C := by simpa [hAn] using hABC
      simpa using Set.indicator_le_indicator_of_subset this zero_le y

open Pointwise in
/-- **Brunn–Minkowski theorem** for real vector space. -/
theorem measure_rpow_add_measure_rpow_le [Nontrivial E] {A B : Set E} (hAn : A.Nonempty)
    (hBn : B.Nonempty) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ A ^ ((finrank ℝ E)⁻¹ : ℝ) + μ B ^ ((finrank ℝ E)⁻¹ : ℝ) ≤
      μ (A + B) ^ ((finrank ℝ E)⁻¹ : ℝ) := by
  have hrank0 : 0 < (finrank ℝ E : ℝ)⁻¹ := by simpa using finrank_pos
  by_cases hA0 : μ A = 0
  · grw [← Set.singleton_subset_iff.mpr hAn.some_mem]
    simp [hA0, hrank0]
  by_cases hB0 : μ B = 0
  · grw [← Set.singleton_subset_iff.mpr hBn.some_mem]
    simp [hB0, hrank0]
  by_cases hAtop : μ A = ∞
  · grw [← Set.singleton_subset_iff.mpr hBn.some_mem]
    simp [hAtop, hrank0]
  by_cases hBtop : μ B = ∞
  · grw [← Set.singleton_subset_iff.mpr hAn.some_mem]
    simp [hBtop, hrank0]
  set a := μ A ^ ((finrank ℝ E)⁻¹ : ℝ)
  set b := μ B ^ ((finrank ℝ E)⁻¹ : ℝ)
  have ha0 : a ≠ 0 := by simp [a, hA0]
  have hatop : a ≠ ∞ := by simp [a, hAtop]
  have hb0 : b ≠ 0 := by simp [b, hB0]
  have hbtop : b ≠ ∞ := by simp [b, hBtop]
  have hab : a + b ≠ 0 := by simp [ha0]
  let c := (b / (a + b)).toReal
  have hc0 : 0 < c := by
    simp [c, ENNReal.toReal_pos_iff, pos_iff_ne_zero, lt_top_iff_ne_top, ha0, hb0, hatop, hbtop]
  have hc1 : c < 1 := by
    rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal (by finiteness) (by simp),
      ENNReal.div_lt_iff (by simp [hb0]) (by simp [hbtop]), add_comm]
    simpa using ENNReal.lt_add_right hbtop ha0
  have hc1' : 0 < 1 - c := by simpa using hc1
  calc
    _ = ((a / (a + b))⁻¹ * a) ^ (1 - c) * ((b / (a + b))⁻¹ * b) ^ c := by
      rw [ENNReal.inv_div (by simp [hatop]) (by simp [ha0]),
        ENNReal.inv_div (by simp [hbtop]) (by simp [hb0]),
        ENNReal.div_mul_cancel ha0 hatop, ENNReal.div_mul_cancel hb0 hbtop,
        ← ENNReal.rpow_add_of_nonneg _ _ hc1'.le hc0.le, tsub_add_cancel_of_le hc1.le,
        ENNReal.rpow_one]
    _ = ((1 - b / (a + b))⁻¹ * a) ^ (1 - c) * ((b / (a + b))⁻¹ * b) ^ c := by
      congr
      apply ENNReal.eq_sub_of_add_eq' (by simp)
      rw [← ENNReal.add_div]
      exact ENNReal.div_self hab (by simp [hatop, hbtop])
    _ = (μ ((1 - c)⁻¹ • A) ^ (1 - c) * μ (c⁻¹ • B) ^ c) ^ ((finrank ℝ E)⁻¹ : ℝ) := by
      have hrank : 0 ≤ ((finrank ℝ E)⁻¹ : ℝ) := by simp
      rw [ENNReal.mul_rpow_of_nonneg _ _ hrank, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_comm (1 - c), mul_comm c, ENNReal.rpow_mul, ENNReal.rpow_mul]
      congr
      <;> rw [Measure.addHaar_smul, abs_pow, ENNReal.ofReal_pow (by simp),
        ENNReal.mul_rpow_of_nonneg _ _ hrank, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ (by simpa using finrank_pos.ne'), ENNReal.rpow_one, abs_inv]
      <;> congr
      · rw [abs_of_nonneg hc1'.le, ENNReal.ofReal_inv_of_pos hc1', ENNReal.ofReal_sub _ hc0.le,
          ENNReal.ofReal_one, ENNReal.ofReal_toReal (ENNReal.div_ne_top hbtop hab)]
      · rw [abs_of_nonneg hc0.le, ENNReal.ofReal_inv_of_pos hc0,
          ENNReal.ofReal_toReal (ENNReal.div_ne_top hbtop hab)]
    _ ≤ _ := by
      gcongr
      convert measure_rpow_mul_measure_rpow_le hc0.le hc1.le μ (by simpa using hAn)
        (by simpa using hBn) (hA.const_smul₀ (1 - c)⁻¹) (hB.const_smul₀ c⁻¹)
      · rw [smul_smul, mul_inv_cancel₀ hc1'.ne', one_smul]
      · rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]


end MeasureTheory
