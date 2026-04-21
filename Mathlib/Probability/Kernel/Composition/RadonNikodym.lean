/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Radon-Nikodym derivative of a composition product

We compute the Radon-Nikodym derivative of a composition product `μ ⊗ₘ κ` with respect to another
composition product `ν ⊗ₘ η` in terms of the Radon-Nikodym derivatives `∂μ/∂ν` and
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.

## Main statements

* `rnDeriv_compProd`: the Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` equals the product of
  `∂μ/∂ν` and `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.
* `rnDeriv_measure_compProd_left`: the Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)`
  (with the same kernel) equals `∂μ/∂ν`.

## TODO

Under suitable assumptions to have Radon-Nikodym derivatives defined for kernels, we should give
equivalent statements with `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` replaced by `∂κ/∂η`.

-/
set_option backward.defeqAttrib.useBackward true


public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- Auxiliary lemma for `rnDeriv_measure_compProd_left`. -/
private lemma rnDeriv_measure_compProd_left_of_ac (hμν : μ ≪ ν) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ μ.rnDeriv ν p.1 := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  have h_key t₁ t₂ : MeasurableSet t₁ → MeasurableSet t₂ →
      ∫⁻ x in t₁ ×ˢ t₂, (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) x ∂ν ⊗ₘ κ =
        ∫⁻ x in t₁ ×ˢ t₂, μ.rnDeriv ν x.1 ∂ν ⊗ₘ κ := by
    intro ht₁ ht₂
    rw [Measure.setLIntegral_rnDeriv (hμν.compProd_left _),
      Measure.setLIntegral_compProd (by fun_prop) ht₁ ht₂]
    simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter]
    rw [setLIntegral_rnDeriv_mul hμν (κ.measurable_coe ht₂).aemeasurable ht₁,
      Measure.compProd_apply_prod ht₁ ht₂]
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    exact h_key t₁ t₂ ht₁ ht₂
  · intro t ht ht_eq
    rw [setLIntegral_compl ht, ht_eq, setLIntegral_compl ht]
    · congr 1
      specialize h_key .univ .univ .univ .univ
      simpa only [univ_prod_univ, Measure.restrict_univ] using h_key
    · rw [← ht_eq]
      exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
    · exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

/-- Auxiliary lemma for `rnDeriv_measure_compProd_left`. -/
lemma rnDeriv_compProd_withDensity_rnDeriv (μ ν : Measure α) (κ η : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := by
  conv_rhs => rw [Measure.haveLebesgueDecomposition_add μ ν]
  rw [Measure.compProd_add_left]
  have h := Measure.rnDeriv_add' (μ.singularPart ν ⊗ₘ κ) (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ)
    (ν ⊗ₘ η)
  have h2 : (μ.singularPart ν ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ ?_
    · exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart _) _ _
    · exact Measure.AbsolutelyContinuous.rfl
  filter_upwards [h, h2] with x hx hx2
  simp [hx, hx2]

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)` (with the same kernel) equals `∂μ/∂ν`. -/
lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (μ.rnDeriv ν) p.1 := by
  calc (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ)
  _ =ᵐ[ν ⊗ₘ κ] (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) :=
    (rnDeriv_compProd_withDensity_rnDeriv μ ν κ κ).symm
  _ =ᵐ[ν ⊗ₘ κ] (fun p ↦ (ν.withDensity (μ.rnDeriv ν)).rnDeriv ν p.1) :=
    rnDeriv_measure_compProd_left_of_ac
      (MeasureTheory.withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) κ
  _ =ᵐ[ν ⊗ₘ κ] fun p ↦ μ.rnDeriv ν p.1 :=
    Measure.ae_eq_compProd_of_ae_eq_fst _ (by fun_prop) (by fun_prop)
      (Measure.rnDeriv_withDensity ν (by fun_prop))

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` equals the product of `∂μ/∂ν` and
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`. -/
lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η]
      (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p) := by
  refine Filter.EventuallyEq.trans (Measure.rnDeriv_mul_rnDeriv h_ac).symm ?_
  filter_upwards [rnDeriv_measure_compProd_left μ ν η] with p hp
  rw [Pi.mul_apply, hp, mul_comm]

end ProbabilityTheory
