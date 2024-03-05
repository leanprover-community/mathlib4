/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.CdfToKernel
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.Disintegration.AuxLemmas

/-!
# Kernel CDF

We prove IsRatCondKernelCDF from conditions on integrals.

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Implementation details


## References

-/


open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

open ProbabilityTheory.kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {κ : kernel α (γ × ℝ)} {ν : kernel α γ}
  {f : α × γ → ℚ → ℝ}

structure IsKernelPDF (f : α × γ → ℚ → ℝ) (κ : kernel α (γ × ℝ)) (ν : kernel α γ) : Prop :=
  (measurable : Measurable f)
  (mono' (a : α) {q r : ℚ} (_hqr : q ≤ r) : ∀ᵐ c ∂(ν a), f (a, c) q ≤ f (a, c) r)
  (nonneg' (a : α) (q : ℚ) : ∀ᵐ c ∂(ν a), 0 ≤ f (a, c) q)
  (le_one' (a : α) (q : ℚ) : ∀ᵐ c ∂(ν a), f (a, c) q ≤ 1)
  (tendsto_integral_zero_of_antitone (a : α) (s : ℕ → ℚ) (_hs : Antitone s)
    (_hs_tendsto : Tendsto s atTop atBot) :
    Tendsto (fun m ↦ ∫ c, f (a, c) (s m) ∂(ν a)) atTop (𝓝 0))
  (tendsto_integral_one_of_monotone (a : α) (s : ℕ → ℚ) (_hs : Monotone s)
    (_hs_tendsto : Tendsto s atTop atTop) :
    Tendsto (fun m ↦ ∫ c, f (a, c) (s m) ∂(ν a)) atTop (𝓝 (ν a univ).toReal))
  (integrable (a : α) (q : ℚ) : Integrable (fun c ↦ f (a, c) q) (ν a))
  (set_integral (a : α) {A : Set γ} (_hA : MeasurableSet A) (q : ℚ) :
    ∫ c in A, f (a, c) q ∂(ν a) = (κ a (A ×ˢ Iic ↑q)).toReal)

lemma IsKernelPDF.measurable_right (hf : IsKernelPDF f κ ν) (a : α) (q : ℚ) :
    Measurable (fun t ↦ f (a, t) q) := by
  let h := hf.measurable
  rw [measurable_pi_iff] at h
  exact (h q).comp measurable_prod_mk_left

lemma IsKernelPDF.mono (hf : IsKernelPDF f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ {q r : ℚ} (_ : q ≤ r), f (a, c) q ≤ f (a, c) r := by
  simp_rw [ae_all_iff]
  intro q r hqr
  exact hf.mono' a hqr

lemma IsKernelPDF.nonneg (hf : IsKernelPDF f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ (q : ℚ), 0 ≤ f (a, c) q := by
  rw [ae_all_iff]
  exact hf.nonneg' a

lemma IsKernelPDF.le_one (hf : IsKernelPDF f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ (q : ℚ), f (a, c) q ≤ 1 := by
  rw [ae_all_iff]
  exact hf.le_one' a

lemma IsKernelPDF.tendsto_zero_of_antitone (hf : IsKernelPDF f κ ν) [IsFiniteKernel ν] (a : α)
    (s : ℕ → ℚ) (hs : Antitone s) (hs_tendsto : Tendsto s atTop atBot) :
    ∀ᵐ c ∂(ν a), Tendsto (fun m ↦ f (a, c) (s m)) atTop (𝓝 0) := by
  refine tendsto_of_integral_tendsto_of_antitone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n ↦ hf.integrable a (s n)
  · rw [integral_zero]
    exact hf.tendsto_integral_zero_of_antitone a s hs hs_tendsto
  · filter_upwards [hf.mono a] with t ht
    exact fun n m hnm ↦ ht (hs hnm)
  · filter_upwards [hf.nonneg a] with c hc using fun i ↦ hc (s i)

lemma IsKernelPDF.tendsto_one_of_monotone (hf : IsKernelPDF f κ ν) [IsFiniteKernel ν] (a : α)
    (s : ℕ → ℚ) (hs : Monotone s) (hs_tendsto : Tendsto s atTop atTop) :
    ∀ᵐ c ∂(ν a), Tendsto (fun m ↦ f (a, c) (s m)) atTop (𝓝 1) := by
  refine tendsto_of_integral_tendsto_of_monotone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n ↦ hf.integrable a (s n)
  · rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact hf.tendsto_integral_one_of_monotone a s hs hs_tendsto
  · filter_upwards [hf.mono a] with t ht
    exact fun n m hnm ↦ ht (hs hnm)
  · filter_upwards [hf.le_one a] with c hc using fun i ↦ hc (s i)

lemma tendsto_atTop_densityIic (hf : IsKernelPDF f κ ν) [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (fun q : ℚ ↦ f (a, t) q) atTop (𝓝 1) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ f (a, t) n) atTop (𝓝 1) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    let f' := fun q : ℚ ↦ f (a, t) ⌊q⌋₊
    let g := fun q : ℚ ↦ f (a, t) ⌈q⌉₊
    have hf_le : ∀ᶠ q in atTop, f' q ≤ f (a, t) q := by
      simp only [eventually_atTop, ge_iff_le]
      exact ⟨0, fun q hq ↦ h_mono (Nat.floor_le hq)⟩
    have hg_le : ∀ q : ℚ, f (a, t) q ≤ g q := by
      exact fun q ↦ h_mono (Nat.le_ceil _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ hf_le (eventually_of_forall hg_le)
    · exact ht.comp tendsto_nat_floor_atTop
    · exact ht.comp tendsto_nat_ceil_atTop
  let s : ℕ → ℚ := fun n ↦ n
  have hs : Monotone s := fun i j hij ↦ by simp [s, hij]
  have hs_tendsto : Tendsto s atTop atTop := by
    exact tendsto_nat_cast_atTop_atTop
  filter_upwards [hf.tendsto_one_of_monotone a s hs hs_tendsto] with x hx using hx

lemma tendsto_atBot_densityIic (hf : IsKernelPDF f κ ν) [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (fun q : ℚ ↦ f (a, t) q) atBot (𝓝 0) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun q : ℚ ↦ f (a, t) (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    have h_eq_neg : (fun q : ℚ ↦ f (a, t) q) = fun q : ℚ ↦ f (a, t) (- -q) := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    convert ht.comp tendsto_neg_atBot_atTop
    simp
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ f (a, t) (-n)) atTop (𝓝 0) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    let f' := fun q : ℚ ↦ f (a, t) (-⌊q⌋₊)
    let g := fun q : ℚ ↦ f (a, t) (-⌈q⌉₊)
    have hf_le : ∀ᶠ (q : ℚ) in atTop, f (a, t) (-q) ≤ f' q := by
      simp only [eventually_atTop, ge_iff_le]
      refine ⟨0, fun q hq ↦ ?_⟩
      norm_cast
      refine h_mono ?_
      simp only [Rat.ofInt_eq_cast, Int.cast_neg, Int.cast_ofNat, neg_le_neg_iff]
      exact Nat.floor_le hq
    have hg_le : ∀ q, g q ≤ f (a, t) (-q) := by
      refine fun q ↦ ?_
      simp only [g]
      norm_cast
      refine h_mono ?_
      simp only [Rat.ofInt_eq_cast, Int.cast_neg, Int.cast_ofNat, neg_le_neg_iff]
      exact Nat.le_ceil _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ (eventually_of_forall hg_le) hf_le
    · exact ht.comp tendsto_nat_ceil_atTop
    · exact ht.comp tendsto_nat_floor_atTop
  let s : ℕ → ℚ := fun n ↦ -n
  have hs : Antitone s := fun i j hij ↦ neg_le_neg (by exact mod_cast hij)
  have hs_tendsto : Tendsto s atTop atBot := by
    simp only [s, tendsto_neg_atBot_iff]
    exact tendsto_nat_cast_atTop_atTop
  convert hf.tendsto_zero_of_antitone a s hs hs_tendsto with x n

lemma bddBelow_range_densityIic (hf : IsKernelPDF f κ ν) (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, BddBelow (range fun (r : Ioi q) ↦ f (a, t) r) := by
  filter_upwards [hf.nonneg a] with c hc
  refine fun q ↦ ⟨0, ?_⟩
  rw [mem_lowerBounds]
  rintro x ⟨y, rfl⟩
  exact hc y

lemma integrable_iInf_rat_gt_densityIic (hf : IsKernelPDF f κ ν) [IsFiniteKernel ν]
    (a : α) (q : ℚ) :
    Integrable (fun t ↦ ⨅ r : Ioi q, f (a, t) r) (ν a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_iInf fun i ↦ hf.measurable_right a _
  refine (?_ : _ ≤ (ν a univ : ℝ≥0∞)).trans_lt (measure_lt_top _ _)
  refine (snorm_le_of_ae_bound (C := 1) ?_).trans ?_
  · filter_upwards [bddBelow_range_densityIic hf a, hf.nonneg a, hf.le_one a]
      with t hbdd_below h_nonneg h_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · refine ciInf_le_of_le ?_ ?_ ?_
      · exact hbdd_below _
      · exact ⟨q + 1, by simp⟩
      · exact h_le_one _
    · exact le_ciInf fun r ↦ h_nonneg _
  · simp

lemma set_integral_iInf_rat_gt_densityIic (hf : IsKernelPDF f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) (q : ℚ) {A : Set γ} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a) = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
  refine le_antisymm ?_ ?_
  · have h : ∀ r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, f (a, t) r' ∂(ν a)
        ≤ (κ a (A ×ˢ Iic (r : ℝ))).toReal := by
      intro r
      rw [← hf.set_integral a hA]
      refine set_integral_mono_ae ?_ ?_ ?_
      · exact (integrable_iInf_rat_gt_densityIic hf _ _).integrableOn
      · exact (hf.integrable _ _).integrableOn
      · filter_upwards [bddBelow_range_densityIic hf a] with t ht
        exact ciInf_le (ht _) r
    calc ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a)
      ≤ ⨅ r : Ioi q, (κ a (A ×ˢ Iic (r : ℝ))).toReal := le_ciInf h
    _ = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
        rw [← Measure.iInf_rat_gt_prod_Iic hA q]
        exact (ENNReal.toReal_iInf (fun r ↦ measure_ne_top _ _)).symm
  · rw [← hf.set_integral a hA]
    refine set_integral_mono_ae ?_ ?_ ?_
    · exact (hf.integrable _ _).integrableOn
    · exact (integrable_iInf_rat_gt_densityIic hf _ _).integrableOn
    · filter_upwards [hf.mono a] with c h_mono
      exact le_ciInf (fun r ↦ h_mono (le_of_lt r.prop))

lemma iInf_rat_gt_densityIic_eq (hf : IsKernelPDF f κ ν) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, ⨅ r : Ioi q, f (a, t) r = f (a, t) q := by
  rw [ae_all_iff]
  refine fun q ↦ ae_eq_of_forall_set_integral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · intro s _ _
    refine Integrable.integrableOn ?_
    exact integrable_iInf_rat_gt_densityIic hf _ _
  · exact fun s _ _ ↦ (hf.integrable a _).integrableOn
  · intro s hs _
    rw [hf.set_integral _ hs, set_integral_iInf_rat_gt_densityIic hf _ _ hs]

lemma isRatStieltjesPoint_densityIic_ae (hf : IsKernelPDF f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), IsRatStieltjesPoint f (a, t) := by
  filter_upwards [tendsto_atTop_densityIic hf a, tendsto_atBot_densityIic hf a,
    iInf_rat_gt_densityIic_eq hf a, hf.mono a] with t ht_top ht_bot ht_iInf h_mono
  exact ⟨fun _ _ ↦ h_mono, ht_top, ht_bot, ht_iInf⟩

lemma isRatCondKernelCDF_densityIic (hf : IsKernelPDF f κ ν) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    IsRatCondKernelCDF f κ ν where
  measurable := hf.measurable
  isRatStieltjesPoint_ae := isRatStieltjesPoint_densityIic_ae hf
  integrable := hf.integrable
  set_integral := hf.set_integral

noncomputable
def condKernelCDF (hf : IsKernelPDF f κ ν) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    α × γ → StieltjesFunction :=
  stieltjesOfMeasurableRat f (isRatCondKernelCDF_densityIic hf).measurable

lemma isCondKernelCDF_condKernelCDF (hf : IsKernelPDF f κ ν) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    IsCondKernelCDF (condKernelCDF hf) κ ν :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_densityIic hf)

end ProbabilityTheory
