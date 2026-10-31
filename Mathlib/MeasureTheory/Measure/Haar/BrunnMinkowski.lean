/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic

import Mathlib.MeasureTheory.Integral.Lebesgue.PrekopaLeindler
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Brunn–Minkowski theorem

This file proves the Brunn–Minkowski theorem for finite-dimensional real vector space $E$:
for nonempty measurable sets $A$ and $B$, we have
 - $μ(A)^{1/n} + μ(B)^{1/n} ≤ μ(A + B)^{1/n}$
 - $μ(A)^{1-a} μ(B)^a ≤ μ ((1 - a) • A + a • B)$ for $0 ≤ a ≤ 1$ (multiplicative version)
where $n$ is the dimension of $E$, and $μ$ is a Haar measure.
-/

public section

namespace MeasureTheory

open scoped ENNReal
open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

open Pointwise in
/-- **Brunn–Minkowski theorem** for real vector space, multiplicative version. -/
theorem measure_rpow_mul_measure_rpow_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A B : Set E}
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ A ^ (1 - a) * μ B ^ a ≤ μ ((1 - a) • A + a • B) := by
  obtain ⟨C, hABC, hC, hμC⟩ := exists_measurable_superset μ ((1 - a) • A + a • B)
  rw [← hμC, ← lintegral_indicator_fun_one hA, ← lintegral_indicator_fun_one hB,
    ← lintegral_indicator_fun_one hC]
  apply lintegral_rpow_mul_lintegral_rpow_le μ ha0 ha1 (by fun_prop) (by fun_prop) (by fun_prop)
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
/-- **Brunn–Minkowski theorem** for real vector space for `NullMeasurableSet`, multiplicative
version. -/
theorem measure_rpow_mul_measure_rpow_le₀ {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A B : Set E}
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) :
    μ A ^ (1 - a) * μ B ^ a ≤ μ ((1 - a) • A + a • B) := by
  obtain ⟨A', hA'A, hA', hμA⟩ := hA.exists_measurable_subset_ae_eq
  obtain ⟨B', hB'B, hB', hμB⟩ := hB.exists_measurable_subset_ae_eq
  calc
    _ = μ A' ^ (1 - a) * μ B' ^ a := by rw [measure_congr hμA, measure_congr hμB]
    _ ≤ μ (A' ∪ {hAn.some}) ^ (1 - a) * μ (B' ∪ {hBn.some}) ^ a := by gcongr <;> simp
    _ ≤ μ ((1 - a) • (A' ∪ {hAn.some}) + a • (B' ∪ {hBn.some})) :=
      measure_rpow_mul_measure_rpow_le μ ha0 ha1 (by simp) (by simp) (by simp [hA']) (by simp [hB'])
    _ ≤ _ := by
      gcongr
      · exact Set.union_subset hA'A <| Set.singleton_subset_iff.mpr hAn.some_mem
      · exact Set.union_subset hB'B <| Set.singleton_subset_iff.mpr hBn.some_mem

open Pointwise in
/-- **Brunn–Minkowski theorem** for real vector space. -/
theorem measure_rpow_add_measure_rpow_le [Nontrivial E] {A B : Set E} (hAn : A.Nonempty)
    (hBn : B.Nonempty) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ A ^ (finrank ℝ E : ℝ)⁻¹ + μ B ^ (finrank ℝ E : ℝ)⁻¹ ≤ μ (A + B) ^ (finrank ℝ E : ℝ)⁻¹ := by
  have hE : 0 < (finrank ℝ E : ℝ)⁻¹ := by simpa using finrank_pos
  by_cases hA0 : μ A = 0
  · grw [← Set.singleton_subset_iff.mpr hAn.some_mem]
    simp [hA0, hE]
  by_cases hB0 : μ B = 0
  · grw [← Set.singleton_subset_iff.mpr hBn.some_mem]
    simp [hB0, hE]
  by_cases hAtop : μ A = ∞
  · grw [← Set.singleton_subset_iff.mpr hBn.some_mem]
    simp [hAtop, hE]
  by_cases hBtop : μ B = ∞
  · grw [← Set.singleton_subset_iff.mpr hAn.some_mem]
    simp [hBtop, hE]
  set a := μ A ^ (finrank ℝ E : ℝ)⁻¹
  set b := μ B ^ (finrank ℝ E : ℝ)⁻¹
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
      exact ENNReal.div_self hab <| by simp [hatop, hbtop]
    _ = (μ ((1 - c)⁻¹ • A) ^ (1 - c) * μ (c⁻¹ • B) ^ c) ^ (finrank ℝ E : ℝ)⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hE.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_comm (1 - c), mul_comm c, ENNReal.rpow_mul, ENNReal.rpow_mul]
      congr
      <;> rw [Measure.addHaar_smul, abs_pow, ENNReal.ofReal_pow (by simp),
        ENNReal.mul_rpow_of_nonneg _ _ hE.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ <| by simpa using finrank_pos.ne', ENNReal.rpow_one, abs_inv]
      · rw [abs_of_nonneg hc1'.le, ENNReal.ofReal_inv_of_pos hc1', ENNReal.ofReal_sub _ hc0.le,
          ENNReal.ofReal_one, ENNReal.ofReal_toReal <| ENNReal.div_ne_top hbtop hab]
      · rw [abs_of_nonneg hc0.le, ENNReal.ofReal_inv_of_pos hc0,
          ENNReal.ofReal_toReal <| ENNReal.div_ne_top hbtop hab]
    _ ≤ _ := by
      gcongr
      convert measure_rpow_mul_measure_rpow_le μ hc0.le hc1.le hAn.smul_set hBn.smul_set
        (hA.const_smul₀ (1 - c)⁻¹) (hB.const_smul₀ c⁻¹)
      · rw [smul_smul, mul_inv_cancel₀ hc1'.ne', one_smul]
      · rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]

open Pointwise in
/-- **Brunn–Minkowski theorem** for real vector space for `NullMeasurableSet`. -/
theorem measure_rpow_add_measure_rpow_le₀ [Nontrivial E] {A B : Set E} (hAn : A.Nonempty)
    (hBn : B.Nonempty) (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) :
    μ A ^ (finrank ℝ E : ℝ)⁻¹ + μ B ^ (finrank ℝ E : ℝ)⁻¹ ≤ μ (A + B) ^ (finrank ℝ E : ℝ)⁻¹ := by
  set r := (finrank ℝ E : ℝ)⁻¹
  obtain ⟨A', hA'A, hA', hμA⟩ := hA.exists_measurable_subset_ae_eq
  obtain ⟨B', hB'B, hB', hμB⟩ := hB.exists_measurable_subset_ae_eq
  calc
    _ = μ A' ^ r + μ B' ^ r := by rw [measure_congr hμA, measure_congr hμB]
    _ ≤ μ (A' ∪ {hAn.some}) ^ r + μ (B' ∪ {hBn.some}) ^ r := by gcongr <;> simp
    _ ≤ μ ((A' ∪ {hAn.some}) + (B' ∪ {hBn.some})) ^ r :=
      measure_rpow_add_measure_rpow_le μ (by simp) (by simp) (by simp [hA']) (by simp [hB'])
    _ ≤ _ := by
      gcongr
      · exact Set.union_subset hA'A <| Set.singleton_subset_iff.mpr hAn.some_mem
      · exact Set.union_subset hB'B <| Set.singleton_subset_iff.mpr hBn.some_mem

end MeasureTheory
