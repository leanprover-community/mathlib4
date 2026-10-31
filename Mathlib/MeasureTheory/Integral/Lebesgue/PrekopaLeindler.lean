/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Prékopa–Leindler inequality

This file proves the Prékopa–Leindler inequality for finite-dimensional real vector space `E`:
Let $0 ≤ a ≤ 1$ and let `f g j : E → ℝ≥0∞`, suppose that these functions satisfy
$$
f(x)^{1-a} g(x)^a \le j((1-a)x+ay)
$$
for all $x$ and $y$ in `E`, then
$$
\left(\int f(x) dx\right)^{1-a} \left(\int g(x) dx\right)^a \le \int j(x) dx
$$
where integrals are with respect to a Haar measure.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section toMove
open Set Measure
variable {α : Type*} [MeasurableSpace α]

theorem lintegral_eq_lintegral_Ioc_measure_ofReal_le (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {a : ℝ} (ha : ∀ x, f x ≤ .ofReal a) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioc 0 a, μ {x | .ofReal t ≤ f x} := by
  by_cases! ha0 : a < 0
  · have : ∀ x, f x = 0 := by simpa [ENNReal.ofReal_eq_zero.mpr ha0.le] using ha
    simp [Ioc_eq_empty_of_le ha0.le, this]
  rw [lintegral_eq_lintegral_measure_ofReal_le μ hf]
  suffices Function.support (fun t ↦ μ {x | .ofReal t ≤ f x}) ⊆ Iic a by
    rw [← setLIntegral_eq_of_support_subset this, restrict_restrict (by simp), Iic_inter_Ioi]
  intro t
  contrapose
  suffices a < t → {x | .ofReal t ≤ f x} = ∅ by simp +contextual [this]
  intro ht
  ext x
  simpa using (ha x).trans_lt <| (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0).mpr ht

theorem lintegral_eq_lintegral_Ioo_measure_ofReal_le (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {a : ℝ} (ha : ∀ x, f x ≤ .ofReal a) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioo 0 a, μ {x | .ofReal t ≤ f x} := by
  rw [lintegral_eq_lintegral_Ioc_measure_ofReal_le μ hf ha]
  exact setLIntegral_congr Ioo_ae_eq_Ioc.symm

end toMove

variable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {f g j : ℝ → ℝ≥0∞} (hf : Measurable f)
  (hg : Measurable g) (hj : Measurable j)

-- Start in one dimension with two functions of the same supremum of 1.
include ha0 ha1 hf hg hj in
private theorem prekopa_leindler_real_of_iSup_eq_one (hf1 : ⨆ x, f x = 1) (hg1 : ⨆ x, g x = 1)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  open scoped Pointwise in
  have hnonempty {t : ℝ} (ht : t ∈ Set.Ioo 0 1) {e : ℝ → ℝ≥0∞} (he : ⨆ x, e x = 1) :
      {x | .ofReal t ≤ e x}.Nonempty := by
    have h := not_imp_not.mpr <| le_iSup_iff.mp he.symm.le (.ofReal t)
    push Not at h
    obtain ⟨x, hx⟩ := h <| by simpa using ht.2
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
    -- Transform all integrals using layer cake formula restricted to (0, 1)
    _ = (∫⁻ t in Set.Ioo 0 1, volume ((1 - a) • {x | .ofReal t ≤ f x})) +
        ∫⁻ t in Set.Ioo 0 1, volume (a • {x | .ofReal t ≤ g x}) := by
      simp_rw [volume.addHaar_smul_of_nonneg ha0,
        volume.addHaar_smul_of_nonneg (sub_nonneg.mpr ha1), Module.finrank_self, pow_one]
      rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
      congrm _ * ?_ + _ * ?_
      · apply lintegral_eq_lintegral_Ioo_measure_ofReal_le _ hf.aemeasurable
        simpa [hf1] using le_iSup f
      · apply lintegral_eq_lintegral_Ioo_measure_ofReal_le _ hg.aemeasurable
        simpa [hg1] using le_iSup g
    -- For each layer, apply one-dimensional Brunn–Minkowski.
    -- The supremum hypothesis provides the non-emptiness of each layer.
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

-- Next, generalize it to finitely bounded function by normalizing the bound to 1.
include ha0 ha1 hf hg hj in
private theorem prekopa_leindler_real_of_iSup_ne_top (hftop : ⨆ x, f x ≠ ∞) (hgtop : ⨆ x, g x ≠ ∞)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  by_cases hf0 : ⨆ x, f x = 0
  · rcases lt_or_eq_of_le ha1 with ha1 | rfl
    · simp [ENNReal.iSup_eq_zero.mp hf0, ha1]
    · have : ∀ x, g x ≤ j x := by simpa using h
      simpa using lintegral_mono this
  by_cases hg0 : ⨆ x, g x = 0
  · rcases lt_or_eq_of_le ha0 with ha0 | rfl
    · simp [ENNReal.iSup_eq_zero.mp hg0, ha0]
    · have : ∀ x, f x ≤ j x := by simpa using h
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
  exact (ENNReal.mul_le_mul_iff_left (by aesop) (by finiteness)).mp <| h.trans_eq' (by ring)

-- Then generalize it to potentionally unbounded function.
-- This is a public lemma as it can be convenient for one-dimensional application.
include ha0 ha1 hf hg hj in
/-- One-dimensional **Prékopa–Leindler inequality**. -/
theorem _root_.Real.lintegral_rpow_mul_lintegral_rpow_le
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x :=
  calc
    -- Approximate the functions using sequences of bounded functions
    _ = (∫⁻ x, ⨆ t : ℕ, min (f x) t) ^ (1 - a) * (∫⁻ x, ⨆ t : ℕ, min (g x) t) ^ a := by
      simp_rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    _ = (⨆ t : ℕ, (∫⁻ x, min (f x) t) ^ (1 - a)) * ⨆ t : ℕ, (∫⁻ x, min (g x) t) ^ a := by
      congr
      <;> rw [lintegral_iSup (by fun_prop) fun t u h x ↦ by simp [h],
        ENNReal.iSup_rpow_of_nonneg (by grind)]
    _ = ⨆ (s : ℕ) (t : ℕ), (∫⁻ x,  min (f x) t) ^ (1 - a) * (∫⁻ x, min (g x) s) ^ a := by
      simp_rw [ENNReal.mul_iSup, ENNReal.iSup_mul]
    _ ≤ _ := by
      refine iSup₂_le fun s t ↦ ?_
      apply prekopa_leindler_real_of_iSup_ne_top ha0 ha1 (by fun_prop) (by fun_prop) hj
      · exact lt_top_iff_ne_top.mp <| iSup_lt_iff.mpr ⟨t + 1, by simp⟩
      · exact lt_top_iff_ne_top.mp <| iSup_lt_iff.mpr ⟨s + 1, by simp⟩
      · intro x y
        grw [← h x y]
        gcongr <;> simp

-- And generalize it to higher dimension by induction.
include ha0 ha1 in
private theorem lintegral_rpow_mul_lintegral_rpow_le_pi {n : ℕ} {f g j : (Fin n → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) • x + a • y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  induction n with
  | zero => simpa [lintegral_unique, volume_pi, Unique.eq_default] using h default default
  | succ n ih =>
    calc
      -- Break integrals into 1-d and `n`-d parts.
      _ = (∫⁻ (x) (y), f (Fin.cons x y)) ^ (1 - a) * (∫⁻ (x) (y), g (Fin.cons x y)) ^ a := by
        simp_rw [volume_pi, (measurePreserving_piFinSuccAbove _ 0).symm.lintegral_map_equiv]
        simp (disch := fun_prop) [lintegral_prod]
      _ ≤ ∫⁻ (x) (y), j (Fin.cons x y) := by
        -- Apply one-dimensional Prékopa–Leindler on the outer integral.
        refine Real.lintegral_rpow_mul_lintegral_rpow_le ha0 ha1 (by fun_prop) (by fun_prop)
          (by fun_prop) fun x y ↦ ?_
        -- Then use the `n`-dimensional Prékopa–Leindler (the induction hypothesis)
        -- on the inner integral to fulfill the condition.
        refine ih (by fun_prop) (by fun_prop) (by fun_prop) fun u v ↦ ?_
        convert h (Fin.cons x u) (Fin.cons y v)
        ext i
        cases i using Fin.cases <;> simp
      _ = ∫⁻ x, j x := by
        simp_rw [volume_pi, (measurePreserving_piFinSuccAbove _ 0).symm.lintegral_map_equiv]
        simp (disch := fun_prop) [lintegral_prod]

-- Finally, transfer the result to general vector spaces.
/-- **Prékopa–Leindler inequality** for real vector space. -/
theorem lintegral_rpow_mul_lintegral_rpow_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {f g j : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hj : Measurable j) (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) • x + a • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - a) * (∫⁻ x, g x ∂μ) ^ a ≤ ∫⁻ x, j x ∂μ := by
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E := .ofFinrankEq (by simp)
  obtain ⟨c, _, hc⟩ :=
    e.symm.toLinearMap.exists_map_addHaar_eq_smul_addHaar μ volume e.symm.surjective
  suffices (c * ∫⁻ x, f (e x)) ^ (1 - a) * (c * ∫⁻ x, g (e x)) ^ a ≤ c * ∫⁻ x, j (e x) by
    simp_rw [← smul_eq_mul c, ← lintegral_smul_measure, ← hc] at this
    simpa (disch := fun_prop) [lintegral_map] using this
  calc
    _ = c * ((∫⁻ x, f (e x)) ^ (1 - a) * (∫⁻ x, g (e x)) ^ a) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp [ha1]),
        ENNReal.mul_rpow_of_nonneg _ _ ha0, mul_mul_mul_comm,
        ← ENNReal.rpow_add_of_nonneg _ _ (by simp [ha1]) ha0, sub_add_cancel, ENNReal.rpow_one]
    _ ≤ _ :=
      mul_le_mul_right (lintegral_rpow_mul_lintegral_rpow_le_pi ha0 ha1 (by fun_prop) (by fun_prop)
        (by fun_prop) fun x y ↦ by simpa using h (e x) (e y)) _

end MeasureTheory
