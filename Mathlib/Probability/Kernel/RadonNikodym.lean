/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.KernelCDFReal
import Mathlib.Probability.Kernel.WithDensity

/-!
# Radon-Nikodym derivative and Lebesgue decompusition for kernels

Let `γ` be a countably generated measurable space and `κ ν : kernel α γ`. Then there exists... TODO

## Main definitions

* `ProbabilityTheory.kernel.rnDeriv`
* `ProbabilityTheory.kernel.singularPart`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

Theorem 1.28 in [O. Kallenberg, Random Measures, Theory and Applications][kallenberg2017].

## Tags

Foobars, barfoos
-/

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  [MeasurableSpace.CountablyGenerated γ] {κ ν : kernel α γ}

lemma kernel.fst_map_prod_le_of_le (hκν : κ ≤ ν) :
    kernel.fst (kernel.map κ (fun a ↦ (a, ()))
      (@measurable_prod_mk_right γ Unit _ inferInstance _)) ≤ ν := by
  rwa [kernel.fst_map_prod _ measurable_id' measurable_const, kernel.map_id']

noncomputable
def kernel.rnDerivAux (κ ν : kernel α γ) (a : α) (x : γ) : ℝ :=
  kernel.density (kernel.map κ (fun a ↦ (a, ()))
    (@measurable_prod_mk_right γ Unit _ inferInstance _)) ν a x univ

lemma rnDerivAux_nonneg (hκν : κ ≤ ν) {a : α} {x : γ} : 0 ≤ kernel.rnDerivAux κ ν a x :=
  density_nonneg (kernel.fst_map_prod_le_of_le hκν) _ _ _

lemma rnDerivAux_le_one (hκν : κ ≤ ν) {a : α} {x : γ} : kernel.rnDerivAux κ ν a x ≤ 1 :=
  density_le_one (kernel.fst_map_prod_le_of_le hκν) _ _ _

lemma measurable_rnDerivAux (κ ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.rnDerivAux κ ν p.1 p.2) :=
  measurable_density _ ν MeasurableSet.univ

lemma measurable_rnDerivAux_right (κ ν : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ kernel.rnDerivAux κ ν a x) := by
  change Measurable ((fun p : α × γ ↦ kernel.rnDerivAux κ ν p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDerivAux _ _).comp measurable_prod_mk_left

noncomputable
def kernel.rnDeriv (κ ν : kernel α γ) (a : α) (x : γ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x)
    / ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x)

lemma kernel.rnDeriv_def (κ ν : kernel α γ) :
    kernel.rnDeriv κ ν = fun a x ↦ ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x)
      / ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x) := rfl

lemma measurable_rnDeriv (κ ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.rnDeriv κ ν p.1 p.2) :=
  (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

lemma measurable_rnDeriv_right (κ ν : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ kernel.rnDeriv κ ν a x) := by
  change Measurable ((fun p : α × γ ↦ kernel.rnDeriv κ ν p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDeriv _ _).comp measurable_prod_mk_left

lemma withDensity_rnDerivAux (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity (κ + ν)
      (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)) = κ := by
  have h_le : κ ≤ κ + ν := le_add_of_nonneg_right bot_le
  ext a s hs
  rw [kernel.withDensity_apply']
  swap; exact (measurable_rnDerivAux _ _).ennreal_ofReal
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · unfold kernel.rnDerivAux
    rw [set_integral_density (kernel.fst_map_prod_le_of_le h_le) a MeasurableSet.univ hs,
      ENNReal.ofReal_toReal, kernel.map_apply' _ _ _ (hs.prod MeasurableSet.univ)]
    · congr with x
      simp
    · exact measure_ne_top _ _
  · exact (integrable_density (kernel.fst_map_prod_le_of_le h_le) a MeasurableSet.univ).restrict
  · exact ae_of_all _ (fun x ↦ density_nonneg (kernel.fst_map_prod_le_of_le h_le) _ _ _)

lemma withDensity_one_sub_rnDerivAux (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity (κ + ν)
      (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x)) = ν := by
  have h_le : κ ≤ κ + ν := le_add_of_nonneg_right bot_le
  suffices kernel.withDensity (κ + ν)
        (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x))
      + kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x))
      = κ + ν by
    ext a s
    have h : (kernel.withDensity (κ + ν)
          (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x))
        + kernel.withDensity (κ + ν)
          (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x))) a s
        = κ a s + ν a s := by
      rw [this]
      simp
    simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
      at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  have h_nonneg : ∀ a x, 0 ≤ kernel.rnDerivAux κ (κ + ν) a x :=
    fun _ _ ↦ density_nonneg (kernel.fst_map_prod_le_of_le h_le) _ _ _
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (h_nonneg _ _), ENNReal.ofReal_one]
  rw [kernel.withDensity_sub_add]
  · rw [kernel.withDensity_one']
  · exact measurable_const
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  · refine fun a ↦ ne_of_lt ?_
    calc ∫⁻ x, ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x) ∂(κ + ν) a
      ≤ ∫⁻ _, 1 ∂(κ + ν) a := by
          refine lintegral_mono (fun x ↦ ?_)
          simp [rnDerivAux_le_one (le_add_of_nonneg_right bot_le)]
    _ < ⊤ := by rw [MeasureTheory.lintegral_const, one_mul]; exact measure_lt_top _ _
  · refine fun a ↦ ae_of_all _ (fun x ↦ ?_)
    simp only [ENNReal.ofReal_le_one]
    exact density_le_one (kernel.fst_map_prod_le_of_le h_le) _ _ _

noncomputable
def kernel.singularPart (κ ν : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel ν] :
    kernel α γ :=
  kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)
    - Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x)

lemma kernel.mutuallySingular_singularPart (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    kernel.singularPart κ ν a ⟂ₘ ν a := by
  symm
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  refine ⟨{x | kernel.rnDerivAux κ (κ + ν) a x = 1},
    measurable_rnDerivAux_right _ _ a (measurableSet_singleton _), ?_, ?_⟩
  · suffices kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal
        (1 - kernel.rnDerivAux κ (κ + ν) a x)) a {x | kernel.rnDerivAux κ (κ + ν) a x = 1} = 0 by
      rwa [withDensity_one_sub_rnDerivAux κ ν] at this
    simp_rw [h_coe]
    rw [kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq, ae_restrict_iff]
    rotate_left
    · exact (measurable_const.sub
        ((measurable_rnDerivAux _ _).comp measurable_prod_mk_left)).ennreal_ofReal
        (measurableSet_singleton _)
    · exact (measurable_const.sub
        ((measurable_rnDerivAux _ _).comp measurable_prod_mk_left)).ennreal_ofReal
    · exact (measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal
    refine ae_of_all _ (fun x hx ↦ ?_)
    simp only [mem_setOf_eq] at hx
    simp [hx]
  · have h_meas' : Measurable <| Function.uncurry fun a b ↦
        ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a b)
        - ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a b) * rnDeriv κ ν a b := by
      refine (measurable_rnDerivAux _ _).ennreal_ofReal.sub
        (Measurable.mul ?_ (measurable_rnDeriv _ _))
      exact (measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal
    have h_meas : Measurable fun b ↦ ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a b)
        - ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a b) * rnDeriv κ ν a b := by
      change Measurable ((Function.uncurry fun a b ↦
        ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a b)
        - ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a b) * rnDeriv κ ν a b)
        ∘ (fun b ↦ (a, b)))
      exact h_meas'.comp measurable_prod_mk_left
    rw [kernel.singularPart, kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq,
      ae_restrict_iff]
    all_goals simp_rw [h_coe]
    rotate_left
    · exact measurableSet_preimage h_meas (measurableSet_singleton _)
    · exact h_meas
    · exact h_meas'
    refine ae_of_all _ (fun x hx ↦ ?_)
    simp only [mem_compl_iff, mem_setOf_eq] at hx
    simp_rw [rnDeriv]
    rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
      mul_inv_cancel, one_mul, tsub_self]
    · rfl
    · rw [ne_eq, sub_eq_zero]
      exact Ne.symm hx
    · simp [rnDerivAux_le_one (le_add_of_nonneg_right bot_le)]
    · simp [lt_of_le_of_ne (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) hx]

lemma kernel.rnDeriv_add_singularPart (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity ν (kernel.rnDeriv κ ν) + kernel.singularPart κ ν = κ := by
  have : kernel.withDensity ν (kernel.rnDeriv κ ν)
      = kernel.withDensity (kernel.withDensity (κ + ν)
        (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x))) (kernel.rnDeriv κ ν) := by
    rw [kernel.rnDeriv_def]
    congr
    exact (withDensity_one_sub_rnDerivAux κ ν).symm
  rw [this, kernel.singularPart, add_comm, ← kernel.withDensity_mul]
  rotate_left
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).real_toNNReal
  · exact measurable_rnDeriv _ _
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  have h_le : ∀ a x, ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x
      ≤ ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x) := by
    intro a x
    unfold kernel.rnDeriv
    by_cases h_one : kernel.rnDerivAux κ (κ + ν) a x = 1
    · simp [h_one]
    rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
      mul_inv_cancel, one_mul]
    · rw [ne_eq, sub_eq_zero]
      exact Ne.symm h_one
    · simp [rnDerivAux_le_one (le_add_of_nonneg_right bot_le)]
    · simp [lt_of_le_of_ne (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) h_one]
  rw [kernel.withDensity_sub_add, withDensity_rnDerivAux]
  all_goals simp_rw [h_coe]
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul
      (measurable_rnDeriv _ _)
  · refine fun a ↦ ne_of_lt ?_
    have : ∀ x,
        ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x ≤ 1 := by
      refine fun x ↦ (h_le a x).trans ?_
      simp only [ENNReal.ofReal_le_one, rnDerivAux_le_one (le_add_of_nonneg_right bot_le)]
    calc ∫⁻ x, ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x ∂(κ + ν) a
      ≤ ∫⁻ _, 1 ∂(κ + ν) a := lintegral_mono this
    _ < ⊤ := by rw [MeasureTheory.lintegral_const, one_mul]; exact measure_lt_top _ _
  · exact fun a ↦ ae_of_all _ (h_le a)

end ProbabilityTheory
