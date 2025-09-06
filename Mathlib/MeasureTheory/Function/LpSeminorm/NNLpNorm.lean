/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# `ℝ≥0`-valued Lᵖ norm

This file proves theorems about `MeasureTheory.nnLpNorm`,
an `ℝ≥0`-valued version of `MeasureTheory.eLpNorm`.
-/

open Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace MeasureTheory
variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] {f g h : α → E}

lemma coe_nnLpNorm_eq_eLpNorm (hf : MemLp f p μ) : nnLpNorm f p μ = eLpNorm f p μ := by
  rw [nnLpNorm, ENNReal.coe_toNNReal hf.eLpNorm_ne_top]

-- TODO: Rename `eLpNorm_eq_lintegral_rpow_enorm` to `eLpNorm_eq_lintegral_rpow_enorm_toReal`
lemma coe_nnLpNorm_eq_integral_norm_rpow_toReal (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ ^ p.toReal) μ) :
    nnLpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [nnLpNorm, eLpNorm_eq_lintegral_rpow_enorm hp₀ hp, ENNReal.coe_toNNReal_eq_toReal,
    ← ENNReal.toReal_rpow, ← integral_toReal hf]
  · simp [← ENNReal.toReal_rpow]
  · exact .of_forall fun x ↦ ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)

-- TODO: Rename `coe_eLpNorm_nnreal_eq_lintegral_norm_rpow`
lemma coe_nnLpNorm_nnreal_eq_integral_norm_rpow {p : ℝ≥0} (hp : p ≠ 0)
    (hf : AEMeasurable (fun x ↦ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal) μ) :
    nnLpNorm f p μ = (∫ x, ‖f x‖ ^ (p : ℝ) ∂μ) ^ (p⁻¹ : ℝ) := by
  rw [coe_nnLpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp

lemma coe_nnLpNorm_one_eq_integral_norm (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ) μ) :
    nnLpNorm f 1 μ = ∫ x, ‖f x‖ ∂μ := by
  rw [coe_nnLpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top (by simpa using hf)]
  simp

@[simp] lemma nnLpNorm_exponent_zero (f : α → E) : nnLpNorm f 0 μ = 0 := by simp [nnLpNorm]
@[simp] lemma nnLpNorm_measure_zero (f : α → E) : nnLpNorm f p (0 : Measure α) = 0 := by
  simp [nnLpNorm]

lemma ae_le_nnLinftyNorm (hf : MemLp f ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ nnLpNorm f ⊤ μ := by
  simp_rw [← ENNReal.coe_le_coe, coe_nnLpNorm_eq_eLpNorm hf]; exact ae_le_eLpNormEssSup

lemma nnLinftyNorm_eq_essSup (hf : MemLp f ∞ μ) : nnLpNorm f ∞ μ = essSup (‖f ·‖₊) μ := by
  refine ENNReal.coe_injective ?_
  rw [coe_nnLpNorm_eq_eLpNorm hf, ENNReal.coe_essSup, eLpNorm_exponent_top, eLpNormEssSup]
  · simp_rw [enorm_eq_nnnorm]
  · exact ⟨_, ae_le_nnLinftyNorm hf⟩

@[simp] lemma nnLpNorm_zero (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (0 : α → E) p μ = 0 := by simp [nnLpNorm]

@[simp] lemma nnLpNorm_zero' (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (fun _ ↦ 0 : α → E) p μ = 0 := by simp [nnLpNorm]

@[simp]
lemma nnLpNorm_eq_zero (hf : MemLp f p μ) (hp : p ≠ 0) : nnLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [nnLpNorm, ENNReal.toNNReal_eq_zero_iff, hf.eLpNorm_ne_top, eLpNorm_eq_zero_iff hf.1 hp]

@[simp] lemma nnLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : nnLpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma nnLpNorm_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (-f) p μ = nnLpNorm f p μ := by simp [nnLpNorm]

@[simp] lemma nnLpNorm_neg' (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (fun x ↦ -f x) p μ = nnLpNorm f p μ := nnLpNorm_neg ..

lemma nnLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (f - g) p μ = nnLpNorm (g - f) p μ := by simp [nnLpNorm, eLpNorm_sub_comm]

@[simp] lemma nnLpNorm_norm (f : α → E) (p : ℝ≥0∞) :
    nnLpNorm (fun x ↦ ‖f x‖) p μ = nnLpNorm f p μ := by simp [nnLpNorm]

@[simp] lemma nnLpNorm_abs (f : α → ℝ) (p : ℝ≥0∞) : nnLpNorm (|f|) p μ = nnLpNorm f p μ :=
  nnLpNorm_norm f p

@[simp] lemma nnLpNorm_fun_abs (f : α → ℝ) (p : ℝ≥0∞) :
    nnLpNorm (fun x ↦ |f x|) p μ = nnLpNorm f p μ := nnLpNorm_abs ..

@[simp] lemma nnLpNorm_const (hp : p ≠ 0) (hμ : μ ≠ 0) (c : E) :
    nnLpNorm (fun _x ↦ c) p μ = ‖c‖₊ * (μ Set.univ).toNNReal ^ p.toReal⁻¹ := by
  simp [nnLpNorm, eLpNorm_const c hp hμ]

@[simp] lemma nnLpNorm_const' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (c : E) :
    nnLpNorm (fun _x ↦ c) p μ = ‖c‖₊ * (μ Set.univ).toNNReal ^ p.toReal⁻¹ := by
  simp [nnLpNorm, eLpNorm_const' c hp₀ hp]

section NormedField
variable {𝕜 : Type*} [NormedField 𝕜]

@[simp] lemma nnLpNorm_one (hp : p ≠ 0) (hμ : μ ≠ 0) :
    nnLpNorm (1 : α → 𝕜) p μ = (μ Set.univ).toNNReal ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, nnLpNorm_const hp hμ]

@[simp] lemma nnLpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (μ : Measure α) :
    nnLpNorm (1 : α → 𝕜) p μ = (μ Set.univ).toNNReal ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, nnLpNorm_const' hp₀ hp]

lemma nnLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) (μ : Measure α) :
    nnLpNorm (c • f) p μ = ‖c‖₊ * nnLpNorm f p μ := by simp [nnLpNorm, eLpNorm_const_smul]

lemma nnLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (μ : Measure α) :
    nnLpNorm (n • f) p μ = n • nnLpNorm f p μ := by simp [nnLpNorm, eLpNorm_nsmul]

variable [NormedSpace ℝ 𝕜]

lemma nnLpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm ((n : α → 𝕜) * f) p μ = n * nnLpNorm f p μ := by
  simpa only [nsmul_eq_mul] using nnLpNorm_nsmul n f μ

lemma nnLpNorm_natCast_mul' (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (n * f ·) p μ = n * nnLpNorm f p μ := nnLpNorm_natCast_mul ..

lemma nnLpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (f * (n : α → 𝕜)) p μ = nnLpNorm f p μ * n := by
  simpa only [mul_comm] using nnLpNorm_natCast_mul n f p μ

lemma nnLpNorm_mul_natCast' (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (f · * n) p μ = nnLpNorm f p μ * n := nnLpNorm_mul_natCast ..

lemma nnLpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞)
    (μ : Measure α) : nnLpNorm (f / (n : α → 𝕜)) p μ = nnLpNorm f p μ / n := by
  rw [eq_div_iff (by positivity), ← nnLpNorm_mul_natCast]; simp [Pi.mul_def, hn]

lemma nnLpNorm_div_natCast' [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞)
    (μ : Measure α) : nnLpNorm (f · / n) p μ = nnLpNorm f p μ / n := nnLpNorm_div_natCast hn ..

end NormedField

lemma nnLpNorm_add_le (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    nnLpNorm (f + g) p μ ≤ nnLpNorm f p μ + nnLpNorm g p μ := by
  unfold nnLpNorm
  rw [← ENNReal.toNNReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  gcongr
  exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩,
    eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp]

lemma nnLpNorm_sub_le (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    nnLpNorm (f - g) p μ ≤ nnLpNorm f p μ + nnLpNorm g p μ := by
  simpa [sub_eq_add_neg] using nnLpNorm_add_le hf hg.neg hp

lemma nnLpNorm_le_nnLpNorm_add_nnLpNorm_sub' (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    nnLpNorm f p μ ≤ nnLpNorm g p μ + nnLpNorm (f - g) p μ := by
  simpa using nnLpNorm_add_le hg (hf.sub hg) hp

lemma nnLpNorm_le_nnLpNorm_add_nnLpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    nnLpNorm f p μ ≤ nnLpNorm g p μ + nnLpNorm (g - f) p μ := by
  simpa [neg_add_eq_sub] using nnLpNorm_add_le hg.neg (hg.sub hf) hp

lemma nnLpNorm_le_add_nnLpNorm_add (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    nnLpNorm f p μ ≤ nnLpNorm (f + g) p μ + nnLpNorm g p μ := by
  simpa using nnLpNorm_add_le (hf.add hg) hg.neg hp

lemma nnLpNorm_sub_le_nnLpNorm_sub_add_nnLpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hh : MemLp h p μ) (hp : 1 ≤ p) :
    nnLpNorm (f - h) p μ ≤ nnLpNorm (f - g) p μ + nnLpNorm (g - h) p μ := by
  simpa using nnLpNorm_add_le (hf.sub hg) (hg.sub hh) hp

lemma nnLpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ)
    (hp : 1 ≤ p) : nnLpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, nnLpNorm (f i) p μ := by
  rw [← ENNReal.coe_le_coe, coe_nnLpNorm_eq_eLpNorm (memLp_finset_sum' s hf:),
    ENNReal.coe_finset_sum]
  exact (eLpNorm_sum_le (fun i hi ↦ (hf _ hi).aestronglyMeasurable) hp).trans_eq <|
    Finset.sum_congr rfl fun i hi ↦ (coe_nnLpNorm_eq_eLpNorm (hf i hi)).symm

-- TODO: Golf using `eLpNorm_expect_le` once it exists
lemma nnLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι}
    {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ) (hp : 1 ≤ p) :
    nnLpNorm (𝔼 i ∈ s, f i) p μ ≤ 𝔼 i ∈ s, nnLpNorm (f i) p μ  :=  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos <| by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul, ← nnLpNorm_nsmul, Finset.card_smul_expect]
  exact nnLpNorm_sum_le hf hp

lemma nnLpNorm_mono_real {g : α → ℝ} (hg : MemLp g p μ) (h : ∀ x, ‖f x‖ ≤ g x) :
    nnLpNorm f p μ ≤ nnLpNorm g p μ :=
  ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)

lemma nnLpNorm_smul_measure_of_ne_zero {f : α → E} {c : ℝ≥0} (hc : c ≠ 0) :
    nnLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • nnLpNorm f p μ := by
  simp [nnLpNorm, eLpNorm_smul_measure_of_ne_zero' hc f p μ]

lemma nnLpNorm_smul_measure_of_ne_top (hp : p ≠ ∞) {f : α → E} (c : ℝ≥0) :
    nnLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • nnLpNorm f p μ := by
  simp [nnLpNorm, eLpNorm_smul_measure_of_ne_top' hp]

@[simp] lemma nnLpNorm_conj {K : Type*} [RCLike K] (f : α → K) (p : ℝ≥0∞) (μ : Measure α) :
    nnLpNorm (conj f) p μ = nnLpNorm f p μ := by simp [← nnLpNorm_norm]

end MeasureTheory
