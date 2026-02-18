/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Positivity.Finset

/-!
# Real-valued Lᵖ norm

This file proves theorems about `MeasureTheory.lpNorm`,
a real-valued version of `MeasureTheory.eLpNorm`.
-/

open Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

public section

namespace MeasureTheory
variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] {f g h : α → E}

lemma toReal_eLpNorm (hf : AEStronglyMeasurable f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ := by
  rw [lpNorm, if_pos hf]

lemma ofReal_lpNorm (hf : MemLp f p μ) : .ofReal (lpNorm f p μ) = eLpNorm f p μ := by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

@[simp]
lemma lpNorm_of_not_aestronglyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0 :=
  if_neg hf

@[simp]
lemma lpNorm_of_not_memLp (hf' : ¬ MemLp f p μ) : lpNorm f p μ = 0 := by simp_all [MemLp, lpNorm]

@[simp] lemma lpNorm_nonneg : 0 ≤ lpNorm f p μ := by simp [lpNorm, apply_ite]

lemma lpNorm_eq_integral_norm_rpow_toReal (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [← toReal_eLpNorm hf, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, ← ENNReal.toReal_rpow,
    ← integral_toReal]
  · simp [← ENNReal.toReal_rpow]
  · simp_rw [← ofReal_norm]
    borelize E
    fun_prop
  · exact .of_forall fun x ↦ ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)

lemma lpNorm_nnreal_eq_integral_norm_rpow {p : ℝ≥0} (hp : p ≠ 0) (hf : AEStronglyMeasurable f μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ (p : ℝ) ∂μ) ^ (p⁻¹ : ℝ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp

lemma lpNorm_one_eq_integral_norm (hf : AEStronglyMeasurable f μ) :
    lpNorm f 1 μ = ∫ x, ‖f x‖ ∂μ := by
  simp [lpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top hf]

@[simp] lemma lpNorm_exponent_zero (f : α → E) : lpNorm f 0 μ = 0 := by simp [lpNorm]
@[simp] lemma lpNorm_measure_zero (f : α → E) : lpNorm f p (0 : Measure α) = 0 := by simp [lpNorm]

lemma ae_le_lpNorm_exponent_top (hf : MemLp f ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ lpNorm f ∞ μ := by
  simpa only [← toReal_eLpNorm hf.aestronglyMeasurable, ← ENNReal.ofReal_le_iff_le_toReal hf.2.ne,
    ofReal_norm] using ae_le_eLpNormEssSup

lemma lpNorm_exponent_top_eq_essSup (hf : MemLp f ∞ μ) : lpNorm f ∞ μ = essSup (‖f ·‖) μ := by
  simp only [← toReal_eLpNorm hf.aestronglyMeasurable, eLpNorm_exponent_top, eLpNormEssSup]
  refine ENNReal.toReal_essSup (by simp) ⟨lpNorm f ∞ μ, ?_⟩
  simpa [-toReal_enorm, lpNorm] using ae_le_lpNorm_exponent_top hf

@[simp]
lemma lpNorm_zero (p : ℝ≥0∞) (μ : Measure α) : lpNorm (0 : α → E) p μ = 0 := by simp [lpNorm]

@[simp]
lemma lpNorm_fun_zero (p : ℝ≥0∞) (μ : Measure α) : lpNorm (fun _ ↦ 0 : α → E) p μ = 0 := by
  simp [lpNorm]

@[simp]
lemma lpNorm_eq_zero (hf : MemLp f p μ) (hp : p ≠ 0) : lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.toReal_eq_zero_iff, hf.eLpNorm_ne_top,
    eLpNorm_eq_zero_iff hf.1 hp]

@[simp] lemma lpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : lpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma lpNorm_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (-f) p μ = lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.neg]
  · rw [lpNorm_of_not_aestronglyMeasurable hf,
      lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by simpa using h.neg]

@[simp] lemma lpNorm_fun_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (fun x ↦ -f x) p μ = lpNorm f p μ := lpNorm_neg ..

lemma lpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f - g) p μ = lpNorm (g - f) p μ := by rw [← lpNorm_neg]; simp

@[simp] lemma lpNorm_norm (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ ‖f x‖) p μ = lpNorm f p μ := by
  rw [← toReal_eLpNorm hf, ← toReal_eLpNorm (by fun_prop)]; simp

@[simp] lemma lpNorm_abs {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    lpNorm (|f|) p μ = lpNorm f p μ := lpNorm_norm hf p

@[simp] lemma lpNorm_fun_abs {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ |f x|) p μ = lpNorm f p μ := lpNorm_abs hf _

@[simp] lemma lpNorm_const (hp : p ≠ 0) (hμ : μ ≠ 0) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

@[simp] lemma lpNorm_const' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const' c hp₀ hp, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

section NormedField
variable {𝕜 : Type*} [NormedField 𝕜]

@[simp] lemma lpNorm_one (hp : p ≠ 0) (hμ : μ ≠ 0) :
    lpNorm (1 : α → 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, lpNorm_const hp hμ, Measure.real, ENNReal.toReal_rpow]

@[simp] lemma lpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (μ : Measure α) :
    lpNorm (1 : α → 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, lpNorm_const' hp₀ hp, Measure.real, ENNReal.toReal_rpow]

lemma lpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) (μ : Measure α) :
    lpNorm (c • f) p μ = ‖c‖₊ * lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [lpNorm, eLpNorm_const_smul, hf, hf.const_smul]
  obtain rfl | hc := eq_or_ne c 0
  · simp
  rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by
    simpa [hc] using h.const_smul c⁻¹]
  simp

lemma lpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (μ : Measure α) :
    lpNorm (n • f) p μ = n • lpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using lpNorm_const_smul (n : ℝ) f μ (p := p)

variable [NormedSpace ℝ 𝕜]

lemma lpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm ((n : α → 𝕜) * f) p μ = n * lpNorm f p μ := by
  simpa only [nsmul_eq_mul] using lpNorm_nsmul n f μ

lemma lpNorm_fun_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (n * f ·) p μ = n * lpNorm f p μ := lpNorm_natCast_mul ..

lemma lpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f * (n : α → 𝕜)) p μ = lpNorm f p μ * n := by
  simpa only [mul_comm] using lpNorm_natCast_mul n f p μ

lemma lpNorm_fun_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f · * n) p μ = lpNorm f p μ * n := lpNorm_mul_natCast ..

lemma lpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞)
    (μ : Measure α) : lpNorm (f / (n : α → 𝕜)) p μ = lpNorm f p μ / n := by
  rw [eq_div_iff (by positivity), ← lpNorm_mul_natCast]; simp [Pi.mul_def, hn]

lemma lpNorm_fun_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞)
    (μ : Measure α) : lpNorm (f · / n) p μ = lpNorm f p μ / n := lpNorm_div_natCast hn ..

end NormedField

lemma lpNorm_add_le (hf : MemLp f p μ) (hp : 1 ≤ p) :
    lpNorm (f + g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  by_cases hg : MemLp g p μ
  · rw [← toReal_eLpNorm (hf.add hg).aestronglyMeasurable,
      ← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable,
      ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
    gcongr
    exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩,
      eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp]
  · rw [lpNorm_of_not_memLp fun hfg ↦ hg <| by simpa using hfg.sub hf, lpNorm_of_not_memLp hg]
    simp

lemma lpNorm_add_le' (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm (f + g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  simpa [add_comm] using lpNorm_add_le hg (g := f) hp

lemma lpNorm_sub_le (hf : MemLp f p μ) (hp : 1 ≤ p) :
    lpNorm (f - g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  simpa [sub_eq_add_neg] using lpNorm_add_le hf (g := -g) hp

lemma lpNorm_le_lpNorm_add_lpNorm_sub' (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm g p μ + lpNorm (f - g) p μ := by
  simpa using lpNorm_add_le hg (g := f - g) hp

lemma lpNorm_le_lpNorm_add_lpNorm_sub (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm g p μ + lpNorm (g - f) p μ := by
  simpa [neg_add_eq_sub] using lpNorm_add_le hg.neg (g := g - f) hp

lemma lpNorm_le_add_lpNorm_add (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm (f + g) p μ + lpNorm g p μ := by
  simpa using lpNorm_add_le' (f := f + g) hg.neg hp

lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm (f - h) p μ ≤ lpNorm (f - g) p μ + lpNorm (g - h) p μ := by
  simpa using lpNorm_add_le (hf.sub hg) (g := g - h) hp

lemma lpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ)
    (hp : 1 ≤ p) : lpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, lpNorm (f i) p μ := by
  rw [← Finset.sum_congr rfl fun i hi ↦ toReal_eLpNorm (hf i hi).aestronglyMeasurable,
    ← ENNReal.toReal_sum fun i hi ↦ (hf i hi).2.ne,
    ← toReal_eLpNorm (Finset.aestronglyMeasurable_sum _ fun i hi ↦ (hf i hi).aestronglyMeasurable)]
  grw [eLpNorm_sum_le (fun i hi ↦ (hf _ hi).aestronglyMeasurable) hp]
  simpa using fun i hi ↦ (hf i hi).2.ne

-- TODO: Golf using `eLpNorm_expect_le` once it exists
lemma lpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι}
    {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ) (hp : 1 ≤ p) :
    lpNorm (𝔼 i ∈ s, f i) p μ ≤ 𝔼 i ∈ s, lpNorm (f i) p μ  :=  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos <| by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul, ← lpNorm_nsmul, Finset.card_smul_expect]
  exact lpNorm_sum_le hf hp

lemma lpNorm_mono_real {g : α → ℝ} (hg : MemLp g p μ) (h : ∀ x, ‖f x‖ ≤ g x) :
    lpNorm f p μ ≤ lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg.aestronglyMeasurable]
    exact ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)
  · simp [hf]

set_option backward.isDefEq.respectTransparency false in
lemma lpNorm_smul_measure_of_ne_zero {f : α → E} {c : ℝ≥0} (hc : c ≠ 0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_zero' hc f p μ]
    simp [ENNReal.smul_def, NNReal.smul_def]
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by
      simpa [hc] using h.smul_measure c⁻¹]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma lpNorm_smul_measure_of_ne_top (hp : p ≠ ∞) {f : α → E} (c : ℝ≥0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_top' hp]
    simp [ENNReal.smul_def, NNReal.smul_def]
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hc := eq_or_ne c 0
  · rw [NNReal.zero_rpow (by simp [ENNReal.toReal_eq_zero_iff, *])]
    simp
  rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by
    simpa [hc] using h.smul_measure c⁻¹]
  simp

@[simp] lemma lpNorm_conj {K : Type*} [RCLike K] (f : α → K) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (conj f) p μ = lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← lpNorm_norm hf, ← lpNorm_norm]
    · simp
    · exact (continuous_star.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf ?_]
    simpa [Function.comp_def]
      using (continuous_star.measurable.comp_aemeasurable h.aemeasurable).aestronglyMeasurable

end MeasureTheory
