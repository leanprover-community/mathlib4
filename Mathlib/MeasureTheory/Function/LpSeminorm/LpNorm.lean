/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

lemma ofReal_lpNorm_eq_eLpNorm (hf : MemLp f p μ) : .ofReal (lpNorm f p μ) = eLpNorm f p μ := by
  rw [lpNorm, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

lemma lpNorm_eq_integral_norm_rpow_toReal (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ ^ p.toReal) μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [lpNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, ← ENNReal.toReal_rpow,
    ← integral_toReal hf]
  · simp [← ENNReal.toReal_rpow]
  · exact .of_forall fun x ↦ ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)

lemma lpNorm_nnreal_eq_integral_norm_rpow {p : ℝ≥0} (hp : p ≠ 0)
    (hf : AEMeasurable (fun x ↦ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal) μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ (p : ℝ) ∂μ) ^ (p⁻¹ : ℝ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp

lemma lpNorm_one_eq_integral_norm (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ) μ) :
    lpNorm f 1 μ = ∫ x, ‖f x‖ ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top (by simpa using hf)]
  simp

@[simp] lemma lpNorm_exponent_zero (f : α → E) : lpNorm f 0 μ = 0 := by simp [lpNorm]
@[simp] lemma lpNorm_measure_zero (f : α → E) : lpNorm f p (0 : Measure α) = 0 := by simp [lpNorm]

lemma ae_le_lpNorm_exponent_top (hf : MemLp f ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ lpNorm f ⊤ μ := by
  simpa only [lpNorm, ← ENNReal.ofReal_le_iff_le_toReal hf.2.ne, ofReal_norm]
    using ae_le_eLpNormEssSup

lemma lpNorm_exponent_top_eq_essSup (hf : MemLp f ∞ μ) : lpNorm f ∞ μ = essSup (‖f ·‖) μ := by
  simp only [lpNorm, eLpNorm_exponent_top, eLpNormEssSup]
  refine ENNReal.toReal_essSup (by simp) ⟨lpNorm f ∞ μ, ?_⟩
  simpa [-toReal_enorm, lpNorm] using ae_le_lpNorm_exponent_top hf

@[simp]
lemma lpNorm_zero (p : ℝ≥0∞) (μ : Measure α) : lpNorm (0 : α → E) p μ = 0 := by simp [lpNorm]

@[simp]
lemma lpNorm_fun_zero (p : ℝ≥0∞) (μ : Measure α) : lpNorm (fun _ ↦ 0 : α → E) p μ = 0 := by
  simp [lpNorm]

@[simp]
lemma lpNorm_eq_zero (hf : MemLp f p μ) (hp : p ≠ 0) : lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [lpNorm, ENNReal.toReal_eq_zero_iff, hf.eLpNorm_ne_top, eLpNorm_eq_zero_iff hf.1 hp]

@[simp] lemma lpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : lpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma lpNorm_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (-f) p μ = lpNorm f p μ := by simp [lpNorm]

@[simp] lemma lpNorm_fun_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (fun x ↦ -f x) p μ = lpNorm f p μ := lpNorm_neg ..

lemma lpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f - g) p μ = lpNorm (g - f) p μ := by simp [lpNorm, eLpNorm_sub_comm]

@[simp] lemma lpNorm_norm (f : α → E) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ ‖f x‖) p μ = lpNorm f p μ := by simp [lpNorm]

@[simp] lemma lpNorm_abs (f : α → ℝ) (p : ℝ≥0∞) : lpNorm (|f|) p μ = lpNorm f p μ :=
  lpNorm_norm f p

@[simp] lemma lpNorm_fun_abs (f : α → ℝ) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ |f x|) p μ = lpNorm f p μ := lpNorm_abs ..

@[simp] lemma lpNorm_const (hp : p ≠ 0) (hμ : μ ≠ 0) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow]

@[simp] lemma lpNorm_fun_const (hp₀ : p ≠ 0) (hp : p ≠ ∞) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const' c hp₀ hp, Measure.real, ENNReal.toReal_rpow]

section NormedField
variable {𝕜 : Type*} [NormedField 𝕜]

@[simp] lemma lpNorm_one (hp : p ≠ 0) (hμ : μ ≠ 0) :
    lpNorm (1 : α → 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, lpNorm_const hp hμ, Measure.real, ENNReal.toReal_rpow]

@[simp] lemma lpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (μ : Measure α) :
    lpNorm (1 : α → 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, lpNorm_fun_const hp₀ hp, Measure.real, ENNReal.toReal_rpow]

lemma lpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) (μ : Measure α) :
    lpNorm (c • f) p μ = ‖c‖₊ * lpNorm f p μ := by simp [lpNorm, eLpNorm_const_smul]

lemma lpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (μ : Measure α) :
    lpNorm (n • f) p μ = n • lpNorm f p μ := by simp [lpNorm, eLpNorm_nsmul]

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

lemma lpNorm_add_le (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm (f + g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  unfold lpNorm
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  gcongr
  exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩,
    eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp]

lemma lpNorm_sub_le (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm (f - g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  simpa [sub_eq_add_neg] using lpNorm_add_le hf hg.neg hp

lemma lpNorm_le_lpNorm_add_lpNorm_sub' (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm g p μ + lpNorm (f - g) p μ := by
  simpa using lpNorm_add_le hg (hf.sub hg) hp

lemma lpNorm_le_lpNorm_add_lpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm g p μ + lpNorm (g - f) p μ := by
  simpa [neg_add_eq_sub] using lpNorm_add_le hg.neg (hg.sub hf) hp

lemma lpNorm_le_add_lpNorm_add (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm (f + g) p μ + lpNorm g p μ := by
  simpa using lpNorm_add_le (hf.add hg) hg.neg hp

lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hh : MemLp h p μ) (hp : 1 ≤ p) :
    lpNorm (f - h) p μ ≤ lpNorm (f - g) p μ + lpNorm (g - h) p μ := by
  simpa using lpNorm_add_le (hf.sub hg) (hg.sub hh) hp

lemma lpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ)
    (hp : 1 ≤ p) : lpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, lpNorm (f i) p μ := by
  unfold lpNorm
  rw [← ENNReal.toReal_sum fun i hi ↦ (hf i hi).2.ne]
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
    lpNorm f p μ ≤ lpNorm g p μ :=
  ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)

lemma lpNorm_smul_measure_of_ne_zero {f : α → E} {c : ℝ≥0} (hc : c ≠ 0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  simp [lpNorm, eLpNorm_smul_measure_of_ne_zero' hc f p μ]
  simp [ENNReal.smul_def, NNReal.smul_def]

lemma lpNorm_smul_measure_of_ne_top (hp : p ≠ ∞) {f : α → E} (c : ℝ≥0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  simp [lpNorm, eLpNorm_smul_measure_of_ne_top' hp]
  simp [ENNReal.smul_def, NNReal.smul_def]

@[simp] lemma lpNorm_conj {K : Type*} [RCLike K] (f : α → K) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (conj f) p μ = lpNorm f p μ := by simp [← lpNorm_norm]

end MeasureTheory
