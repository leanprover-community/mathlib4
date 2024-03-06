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
    Measurable (fun p : α × γ ↦ kernel.densityIic κ ν p.1 p.2) :=
  measurable_pi_iff.mpr <| fun _ ↦ measurable_density κ ν measurableSet_Iic

lemma isRatCondKernelCDFAux_densityIic (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    isRatCondKernelCDFAux (Function.uncurry (kernel.densityIic κ (kernel.fst κ))) κ (kernel.fst κ)
      where
  measurable := measurable_densityIic _ _
  mono' a q r hqr :=
    ae_of_all _ fun c ↦ density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' a q := ae_of_all _ fun c ↦ density_nonneg le_rfl _ _ _
  le_one' a q := ae_of_all _ fun c ↦ density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    have hs'_anti : Antitone s' := by
      refine fun i j hij ↦ Iic_subset_Iic.mpr ?_
      exact mod_cast hs_anti hij
    have hs'_iInter : ⋂ i, s' i = ∅ := by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, s']
      rw [tendsto_atTop_atBot] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_lt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, lt_of_le_of_lt ?_ hq⟩
      exact mod_cast hi i le_rfl
    have hs'_meas : ∀ n, MeasurableSet (s' n) := fun _ ↦ measurableSet_Iic
    exact tendsto_integral_density_of_antitone (le_rfl : kernel.fst κ ≤ kernel.fst κ)
      a s' hs'_anti hs'_iInter hs'_meas
  tendsto_integral_of_monotone a s hs_mono hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    have hs'_mono : Monotone s' := fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    have hs'_iUnion : ⋃ i, s' i = univ := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
    have hs'_meas : ∀ n, MeasurableSet (s' n) := fun _ ↦ measurableSet_Iic
    have h := tendsto_integral_density_of_monotone (le_rfl : kernel.fst κ ≤ kernel.fst κ)
      a s' hs'_mono hs'_iUnion hs'_meas
    convert h
    rw [kernel.fst_apply' _ _ MeasurableSet.univ]
    rfl
  integrable a q := integrable_density le_rfl a measurableSet_Iic
  set_integral a A hA q := set_integral_density le_rfl a measurableSet_Iic hA

lemma isRatCondKernelCDF_densityIic (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun p : α × γ ↦ kernel.densityIic κ (kernel.fst κ) p.1 p.2) κ
      (kernel.fst κ) :=
  (isRatCondKernelCDFAux_densityIic κ).isRatCondKernelCDF

noncomputable
def condKernelCDF (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] : α × γ → StieltjesFunction :=
  stieltjesOfMeasurableRat (fun p : α × γ ↦ kernel.densityIic κ (kernel.fst κ) p.1 p.2)
    (isRatCondKernelCDF_densityIic κ).measurable

lemma isCondKernelCDF_condKernelCDF (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (kernel.fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_densityIic κ)

end ProbabilityTheory
