/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.KernelCdf
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.Disintegration.AuxLemmas

/-!
# Kernel CDF

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
  [MeasurableSpace.CountablyGenerated γ] {κ : kernel α (γ × ℝ)} {ν : kernel α γ}

noncomputable
def kernel.densityIic (κ : kernel α (γ × ℝ)) (ν : kernel α γ) (a : α) (t : γ) (q : ℚ) : ℝ :=
  kernel.density κ ν a t (Set.Iic q)

lemma measurable_densityIic (κ : kernel α (γ × ℝ)) (ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.densityIic κ ν p.1 p.2) := by
  rw [measurable_pi_iff]
  exact fun _ ↦ measurable_density κ ν measurableSet_Iic

lemma measurable_densityIic_right (κ : kernel α (γ × ℝ)) (ν : kernel α γ) (a : α) (q : ℚ) :
    Measurable (fun t ↦ kernel.densityIic κ ν a t q) :=
  measurable_density_right _ _ measurableSet_Iic _

lemma monotone_densityIic (hκν : kernel.fst κ ≤ ν) (a : α) (t : γ) :
    Monotone (kernel.densityIic κ ν a t) := by
  intro q r hqr
  simp_rw [kernel.densityIic]
  refine density_mono_set hκν a t ?_
  refine Iic_subset_Iic.mpr ?_
  exact_mod_cast hqr

lemma densityIic_nonneg (hκν : kernel.fst κ ≤ ν) (a : α) (t : γ) (q : ℚ) :
    0 ≤ kernel.densityIic κ ν a t q :=
  density_nonneg hκν a t _

lemma densityIic_le_one (hκν : kernel.fst κ ≤ ν) (a : α) (t : γ) (q : ℚ) :
    kernel.densityIic κ ν a t q ≤ 1 :=
  density_le_one hκν a t _

lemma tendsto_atTop_densityIic (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun q ↦ kernel.densityIic κ (kernel.fst κ) a t q) atTop (𝓝 1) := by
  let ν := kernel.fst κ
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ kernel.densityIic κ ν a t n) atTop (𝓝 1) by
    filter_upwards [this] with t ht
    let f := fun q : ℚ ↦ kernel.densityIic κ ν a t ⌊q⌋₊
    let g := fun q : ℚ ↦ kernel.densityIic κ ν a t ⌈q⌉₊
    have hf_le : ∀ᶠ q in atTop, f q ≤ kernel.densityIic κ ν a t q := by
      simp only [eventually_atTop, ge_iff_le]
      exact ⟨0, fun q hq ↦ monotone_densityIic le_rfl a t (Nat.floor_le hq)⟩
    have hg_le : ∀ q, kernel.densityIic κ ν a t q ≤ g q :=
      fun q ↦ monotone_densityIic le_rfl a t (Nat.le_ceil _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ hf_le (eventually_of_forall hg_le)
    · exact ht.comp tendsto_nat_floor_atTop
    · exact ht.comp tendsto_nat_ceil_atTop
  let s : ℕ → Set ℝ := fun n ↦ Iic n
  have hs : Monotone s := fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hij)
  have hs_iUnion : ⋃ i, s i = univ := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil x, Nat.le_ceil x⟩
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ ↦ measurableSet_Iic
  filter_upwards [tendsto_density_atTop_ae_of_monotone a s hs hs_iUnion hs_meas]
    with x hx using hx

lemma tendsto_atBot_densityIic (hκν : kernel.fst κ ≤ ν) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (fun q ↦ kernel.densityIic κ ν a t q) atBot (𝓝 0) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun q ↦ kernel.densityIic κ ν a t (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    have h_eq_neg : (fun q ↦ kernel.densityIic κ ν a t q)
        = fun q ↦ kernel.densityIic κ ν a t (- -q) := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    exact ht.comp tendsto_neg_atBot_atTop
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ kernel.densityIic κ ν a t (-n)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    let f := fun q : ℚ ↦ kernel.densityIic κ ν a t (-⌊q⌋₊)
    let g := fun q : ℚ ↦ kernel.densityIic κ ν a t (-⌈q⌉₊)
    have hf_le : ∀ᶠ q in atTop, kernel.densityIic κ ν a t (-q) ≤ f q := by
      simp only [eventually_atTop, ge_iff_le]
      refine ⟨0, fun q hq ↦ monotone_densityIic hκν a t ?_⟩
      rw [neg_le_neg_iff]
      exact Nat.floor_le hq
    have hg_le : ∀ q, g q ≤ kernel.densityIic κ ν a t (-q) := by
      refine fun q ↦ monotone_densityIic hκν a t ?_
      rw [neg_le_neg_iff]
      exact Nat.le_ceil _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ (eventually_of_forall hg_le) hf_le
    · exact ht.comp tendsto_nat_ceil_atTop
    · exact ht.comp tendsto_nat_floor_atTop
  let s : ℕ → Set ℝ := fun n ↦ Iic (-n)
  have hs : Antitone s := fun i j hij ↦ Iic_subset_Iic.mpr (neg_le_neg (by exact mod_cast hij))
  have hs_iInter : ⋂ i, s i = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, neg_lt]
    exact exists_nat_gt (-x)
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ ↦ measurableSet_Iic
  convert tendsto_density_atTop_ae_of_antitone hκν a s hs hs_iInter hs_meas with x n
  simp [kernel.densityIic]

lemma set_integral_densityIic (hκν : kernel.fst κ ≤ ν) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) (q : ℚ) {A : Set γ} (hA : MeasurableSet A) :
    ∫ t in A, kernel.densityIic κ ν a t q ∂(ν a) = (κ a (A ×ˢ Iic (q : ℝ))).toReal :=
  set_integral_density hκν a measurableSet_Iic hA

lemma integrable_densityIic (hκν : kernel.fst κ ≤ ν) [IsFiniteKernel ν]
    (a : α) (q : ℚ) :
    Integrable (fun t ↦ kernel.densityIic κ ν a t q) (ν a) :=
  integrable_density hκν _ measurableSet_Iic

lemma bddBelow_range_densityIic (hκν : kernel.fst κ ≤ ν) (a : α) (t : γ) (q : ℚ) :
    BddBelow (range fun (r : Ioi q) ↦ kernel.densityIic κ ν a t r) := by
  refine ⟨0, ?_⟩
  rw [mem_lowerBounds]
  rintro x ⟨y, rfl⟩
  exact densityIic_nonneg hκν _ _ _

lemma integrable_iInf_rat_gt_densityIic (hκν : kernel.fst κ ≤ ν) [IsFiniteKernel ν]
    (a : α) (q : ℚ) :
    Integrable (fun t ↦ ⨅ r : Ioi q, kernel.densityIic κ ν a t r) (ν a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_iInf fun i ↦ measurable_densityIic_right κ ν a i
  refine (?_ : _ ≤ (ν a univ : ℝ≥0∞)).trans_lt (measure_lt_top _ _)
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun t ↦ ?_))).trans ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    · refine ciInf_le_of_le ?_ ?_ ?_
      · exact bddBelow_range_densityIic hκν a t _
      · exact ⟨q + 1, by simp⟩
      · exact densityIic_le_one hκν _ _ _
    · exact le_ciInf fun r ↦ densityIic_nonneg hκν a t r
  · simp

lemma set_integral_iInf_rat_gt_densityIic (hκν : kernel.fst κ ≤ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) (q : ℚ) {A : Set γ} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, kernel.densityIic κ ν a t r ∂(ν a)
      = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
  refine le_antisymm ?_ ?_
  · have h : ∀ r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, kernel.densityIic κ ν a t r' ∂(ν a)
        ≤ (κ a (A ×ˢ Iic (r : ℝ))).toReal := by
      intro r
      rw [← set_integral_densityIic hκν a r hA]
      refine set_integral_mono ?_ ?_ ?_
      · exact (integrable_iInf_rat_gt_densityIic hκν _ _).integrableOn
      · exact (integrable_densityIic hκν _ _).integrableOn
      · exact fun t ↦ ciInf_le (bddBelow_range_densityIic hκν _ _ _) r
    calc ∫ t in A, ⨅ r : Ioi q, kernel.densityIic κ ν a t r ∂(ν a)
      ≤ ⨅ r : Ioi q, (κ a (A ×ˢ Iic (r : ℝ))).toReal := le_ciInf h
    _ = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
        rw [← Measure.iInf_rat_gt_prod_Iic hA q]
        exact (ENNReal.toReal_iInf (fun r ↦ measure_ne_top _ _)).symm
  · rw [← set_integral_densityIic hκν a q hA]
    refine set_integral_mono ?_ ?_ ?_
    · exact (integrable_densityIic hκν _ _).integrableOn
    · exact (integrable_iInf_rat_gt_densityIic hκν _ _).integrableOn
    · exact fun t ↦ le_ciInf (fun r ↦ monotone_densityIic hκν _ _ (le_of_lt r.prop))

lemma iInf_rat_gt_densityIic_eq (hκν : kernel.fst κ ≤ ν) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, ⨅ r : Ioi q, kernel.densityIic κ ν a t r
      = kernel.densityIic κ ν a t q := by
  rw [ae_all_iff]
  refine fun q ↦ ae_eq_of_forall_set_integral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · intro s _ _
    refine Integrable.integrableOn ?_
    exact integrable_iInf_rat_gt_densityIic hκν _ _
  · exact fun s _ _ ↦ (integrable_densityIic hκν a q).integrableOn
  · intro s hs _
    rw [set_integral_densityIic hκν _ _ hs, set_integral_iInf_rat_gt_densityIic hκν _ _ hs]

lemma isRatStieltjesPoint_densityIic_ae (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a),
      IsRatStieltjesPoint (fun p q ↦ kernel.densityIic κ (kernel.fst κ) p.1 p.2 q) (a, t) := by
  filter_upwards [tendsto_atTop_densityIic κ a, tendsto_atBot_densityIic le_rfl a,
    iInf_rat_gt_densityIic_eq le_rfl a] with t ht_top ht_bot ht_iInf
  exact ⟨monotone_densityIic le_rfl a t, ht_top, ht_bot, ht_iInf⟩

lemma isRatCondKernelCDF_densityIic (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun p : α × γ ↦ kernel.densityIic κ (kernel.fst κ) p.1 p.2) κ (kernel.fst κ)
    where
  measurable := measurable_densityIic κ (kernel.fst κ)
  isRatStieltjesPoint_ae := isRatStieltjesPoint_densityIic_ae κ
  integrable := integrable_densityIic le_rfl
  set_integral := fun _ _ hs _ ↦ set_integral_densityIic le_rfl _ _ hs

noncomputable
def condKernelCDF (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] : α × γ → StieltjesFunction :=
  stieltjesOfMeasurableRat (fun p : α × γ ↦ kernel.densityIic κ (kernel.fst κ) p.1 p.2)
    (isRatCondKernelCDF_densityIic κ).measurable

lemma isCondKernelCDF_condKernelCDF (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (kernel.fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_densityIic κ)

end ProbabilityTheory
