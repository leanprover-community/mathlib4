/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.SignedLebesgue
import Mathlib.MeasureTheory.Measure.WithDensityVectorMeasure

#align_import measure_theory.decomposition.radon_nikodym from "leanprover-community/mathlib"@"fc75855907eaa8ff39791039710f567f37d4556f"

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rnDeriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`MeasureTheory/Function/ConditionalExpectation`).

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq` :
  the Radon-Nikodym theorem
* `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` :
  the Radon-Nikodym theorem for signed measures

The file also contains properties of `rnDeriv` that use the Radon-Nikodym theorem, notably
* `MeasureTheory.Measure.rnDeriv_withDensity_left`: the Radon-Nikodym derivative of
  `μ.withDensity f` with respect to `ν` is `f * μ.rnDeriv ν`.
* `MeasureTheory.Measure.rnDeriv_withDensity_right`: the Radon-Nikodym derivative of
  `μ` with respect to `ν.withDensity f` is `f⁻¹ * μ.rnDeriv ν`.
* `MeasureTheory.Measure.inv_rnDeriv`: `(μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ`.
* `MeasureTheory.Measure.set_lintegral_rnDeriv`: `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s` if `μ ≪ ν`.
  There is also a version of this result for the Bochner integral.

## Tags

Radon-Nikodym theorem
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

theorem withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) :
    ν.withDensity (rnDeriv μ ν) = μ := by
  suffices μ.singularPart ν = 0 by
    conv_rhs => rw [haveLebesgueDecomposition_add μ ν, this, zero_add]
  suffices μ.singularPart ν Set.univ = 0 by simpa using this
  have h_sing := mutuallySingular_singularPart μ ν
  rw [← measure_add_measure_compl h_sing.measurableSet_nullSet]
  simp only [MutuallySingular.measure_nullSet, zero_add]
  refine le_antisymm ?_ (zero_le _)
  refine (singularPart_le μ ν ?_ ).trans_eq ?_
  exact h h_sing.measure_compl_nullSet
#align measure_theory.measure.with_density_rn_deriv_eq MeasureTheory.Measure.withDensity_rnDeriv_eq

variable {μ ν : Measure α}

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.withDensity (rnDeriv μ ν) = μ`. -/
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq
    [HaveLebesgueDecomposition μ ν] : μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ :=
  ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩
#align measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq

lemma rnDeriv_pos [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := by
  rw [← Measure.withDensity_rnDeriv_eq _ _  hμν,
    ae_withDensity_iff (Measure.measurable_rnDeriv _ _), Measure.withDensity_rnDeriv_eq _ _  hμν]
  exact ae_of_all _ (fun x hx ↦ lt_of_le_of_ne (zero_le _) hx.symm)

lemma rnDeriv_pos' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < ν.rnDeriv μ x := by
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_le ?_
  filter_upwards [Measure.rnDeriv_pos (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)),
    (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).ae_le
    (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ))] with x hx hx2
  rwa [← hx2]

section rnDeriv_withDensity_leftRight

variable {μ ν : Measure α} {f : α → ℝ≥0∞}

/-- Auxiliary lemma for `rnDeriv_withDensity_left`. -/
lemma rnDeriv_withDensity_withDensity_rnDeriv_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    ((ν.withDensity (μ.rnDeriv ν)).withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, withDensity_add_measure]
  have : SigmaFinite ((μ.singularPart ν).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (hf.singularPart ν)
      ((Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)).ae_le hf_ne_top)
  have : SigmaFinite ((ν.withDensity (μ.rnDeriv ν)).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (hf.withDensity_rnDeriv ν)
      ((Measure.absolutelyContinuous_of_le (Measure.withDensity_rnDeriv_le _ _)).ae_le hf_ne_top)
  exact (rnDeriv_add_of_mutuallySingular _ _ _ (mutuallySingular_singularPart μ ν).withDensity).symm

/-- Auxiliary lemma for `rnDeriv_withDensity_right`. -/
lemma rnDeriv_withDensity_withDensity_rnDeriv_right (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0)
    (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    (ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have hν_ac : ν ≪ ν.withDensity f := withDensity_absolutelyContinuous' hf hf_ne_zero
  refine hν_ac.ae_eq ?_
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf hf_ne_top
  refine (rnDeriv_add_of_mutuallySingular _ _ _ ?_).symm
  exact ((mutuallySingular_singularPart μ ν).symm.withDensity).symm

lemma rnDeriv_withDensity_left_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x := by
  refine (Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact hf.mul (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    rw [zero_add, withDensity_apply _ hs, withDensity_apply _ hs]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ _ _ _ hs]
    · congr with x
      rw [mul_comm]
      simp only [Pi.mul_apply]
    · refine ae_restrict_of_ae ?_
      exact Measure.rnDeriv_lt_top _ _
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable

lemma rnDeriv_withDensity_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfμ : AEMeasurable f μ) (hfν : AEMeasurable f ν)
    (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have hμ'ν : μ' ≪ ν := withDensity_absolutelyContinuous _ _
  have h := rnDeriv_withDensity_left_of_absolutelyContinuous hμ'ν hfν
  have h1 : μ'.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have h2 : (μ'.withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
    exact rnDeriv_withDensity_withDensity_rnDeriv_left μ ν hfμ hf_ne_top
  filter_upwards [h, h1, h2] with x hx hx1 hx2
  rw [← hx2, hx, hx1]

/-- Auxiliary lemma for `rnDeriv_withDensity_right`. -/
lemma rnDeriv_withDensity_right_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν)
    (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x := by
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf hf_ne_top
  refine (withDensity_absolutelyContinuous' hf hf_ne_zero).ae_eq ?_
  refine (Measure.eq_rnDeriv₀ (ν := ν.withDensity f) ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact (hf.inv.mono_ac (withDensity_absolutelyContinuous _ _)).mul
      (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [zero_add, withDensity_apply _ hs, withDensity_apply _ hs]
    rw [set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ _ _ _ hs]
    · simp only [Pi.mul_apply]
      have : (fun a ↦ f a * ((f a)⁻¹ * μ.rnDeriv ν a)) =ᵐ[ν] μ.rnDeriv ν := by
        filter_upwards [hf_ne_zero, hf_ne_top] with x hx1 hx2
        simp [← mul_assoc, ENNReal.mul_inv_cancel, hx1, hx2]
      rw [lintegral_congr_ae (ae_restrict_of_ae this)]
    · refine ae_restrict_of_ae ?_
      filter_upwards [hf_ne_top] with x hx using hx.lt_top
    · exact hf.restrict

lemma rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ'.rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) :=
    rnDeriv_withDensity_withDensity_rnDeriv_right μ ν hf hf_ne_zero hf_ne_top
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)).symm
  have : SigmaFinite μ' := SigmaFinite.withDensity_of_ne_top
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.rnDeriv_ne_top _ _)
  have hμ' := rnDeriv_withDensity_right_of_absolutelyContinuous
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hf hf_ne_zero hf_ne_top
  filter_upwards [h₁, h₂, hμ'] with x hx₁ hx₂ hx_eq
  rw [← hx₁, hx₂, hx_eq]

end rnDeriv_withDensity_leftRight

lemma rnDeriv_eq_zero_of_mutuallySingular [SigmaFinite μ] {ν' : Measure α}
    [SigmaFinite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') :
    μ.rnDeriv ν' =ᵐ[ν] 0 := by
  let t := h.nullSet
  have ht : MeasurableSet t := h.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ (by simp [t])
  change μ.rnDeriv ν' =ᵐ[ν.restrict t] 0
  have : μ.rnDeriv ν' =ᵐ[ν.restrict t] (μ.restrict t).rnDeriv ν' := by
    have h : (μ.restrict t).rnDeriv ν' =ᵐ[ν] t.indicator (μ.rnDeriv ν') :=
      hνν'.ae_le (rnDeriv_restrict μ ν' ht)
    rw [Filter.EventuallyEq, ae_restrict_iff' ht]
    filter_upwards [h] with x hx hxt
    rw [hx, Set.indicator_of_mem hxt]
  refine this.trans ?_
  simp only [t, MutuallySingular.restrict_nullSet]
  suffices (0 : Measure α).rnDeriv ν' =ᵐ[ν'] 0 by
    have h_ac' : ν.restrict t ≪ ν' := restrict_le_self.absolutelyContinuous.trans hνν'
    exact h_ac'.ae_le this
  exact rnDeriv_zero _

/-- Auxiliary lemma for `rnDeriv_add_right_of_mutuallySingular`. -/
lemma rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν']
    (hμν : μ ≪ ν) (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  let t := hνν'.nullSet
  have ht : MeasurableSet t := hνν'.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t (by simp [t]) ?_
  change μ.rnDeriv (ν + ν') =ᵐ[ν.restrict tᶜ] μ.rnDeriv ν
  rw [← withDensity_eq_iff_of_sigmaFinite (μ := ν.restrict tᶜ)
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.measurable_rnDeriv _ _).aemeasurable]
  have : (ν.restrict tᶜ).withDensity (μ.rnDeriv (ν + ν'))
      = ((ν + ν').restrict tᶜ).withDensity (μ.rnDeriv (ν + ν')) := by simp [t]
  rw [this, ← restrict_withDensity ht.compl, ← restrict_withDensity ht.compl,
      Measure.withDensity_rnDeriv_eq _ _ (hμν.add_right ν'), Measure.withDensity_rnDeriv_eq _ _ hμν]

/-- Auxiliary lemma for `rnDeriv_add_right_of_mutuallySingular`. -/
lemma rnDeriv_add_right_of_mutuallySingular' {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν']
    (hμν' : μ ⟂ₘ ν') (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν]
  have h₁ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) ν
  refine (Filter.EventuallyEq.trans (h_ac.ae_le h₁) ?_).trans h₂.symm
  have h₃ := rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hνν'
  have h₄ : (μ.singularPart ν).rnDeriv (ν + ν') =ᵐ[ν] 0 := by
    refine h_ac.ae_eq ?_
    simp only [rnDeriv_eq_zero, MutuallySingular.add_right_iff]
    exact ⟨mutuallySingular_singularPart μ ν, hμν'.singularPart ν⟩
  have h₅ : (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := rnDeriv_singularPart μ ν
  filter_upwards [h₃, h₄, h₅] with x hx₃ hx₄ hx₅
  simp only [Pi.add_apply]
  rw [hx₃, hx₄, hx₅]

lemma rnDeriv_add_right_of_mutuallySingular {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν'] (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν']
  have h₁ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) ν
  refine (Filter.EventuallyEq.trans (h_ac.ae_le h₁) ?_).trans h₂.symm
  have h₃ := rnDeriv_add_right_of_mutuallySingular' (?_ : μ.singularPart ν' ⟂ₘ ν') hνν'
  · have h₄ : (ν'.withDensity (rnDeriv μ ν')).rnDeriv (ν + ν') =ᵐ[ν] 0 := by
      refine rnDeriv_eq_zero_of_mutuallySingular ?_ h_ac
      exact hνν'.symm.withDensity
    have h₅ : (ν'.withDensity (rnDeriv μ ν')).rnDeriv ν =ᵐ[ν] 0 := by
      rw [rnDeriv_eq_zero]
      exact hνν'.symm.withDensity
    filter_upwards [h₃, h₄, h₅] with x hx₃ hx₄ hx₅
    rw [Pi.add_apply, Pi.add_apply, hx₃, hx₄, hx₅]
  exact mutuallySingular_singularPart μ ν'

lemma rnDeriv_withDensity_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)) =ᵐ[μ] μ.rnDeriv ν := by
  conv_rhs => rw [ν.haveLebesgueDecomposition_add μ, add_comm]
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_eq ?_
  exact (rnDeriv_add_right_of_mutuallySingular
    (Measure.mutuallySingular_singularPart ν μ).symm.withDensity).symm

/-- Auxiliary lemma for `inv_rnDeriv`. -/
lemma inv_rnDeriv_aux [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (rnDeriv_withDensity _ (measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.rnDeriv μ := rnDeriv_withDensity _ (measurable_rnDeriv _ _)
  rw [withDensity_rnDeriv_eq _ _ hνμ, ← withDensity_rnDeriv_eq _ _ hμν]
  conv in ((ν.withDensity (μ.rnDeriv ν)).rnDeriv ν)⁻¹ => rw [withDensity_rnDeriv_eq _ _ hμν]
  change (ν.withDensity (μ.rnDeriv ν)).withDensity (fun x ↦ (μ.rnDeriv ν x)⁻¹) = ν
  rw [withDensity_inv_same (measurable_rnDeriv _ _)
    (by filter_upwards [hνμ.ae_le (rnDeriv_pos hμν)] with x hx using hx.ne')
    (rnDeriv_ne_top _ _)]

lemma inv_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)))⁻¹
      ∧ ν.rnDeriv μ =ᵐ[μ] (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ by
    refine (this.1.trans (Filter.EventuallyEq.trans ?_ this.2.symm))
    exact Measure.inv_rnDeriv_aux (absolutelyContinuous_withDensity_rnDeriv hμν)
      (withDensity_absolutelyContinuous _ _)
  constructor
  · filter_upwards [rnDeriv_withDensity_rnDeriv hμν] with x hx
    simp only [Pi.inv_apply, inv_inj]
    exact hx.symm
  · exact (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ)).symm

lemma inv_rnDeriv' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (ν.rnDeriv μ)⁻¹ =ᵐ[μ] μ.rnDeriv ν := by
  filter_upwards [inv_rnDeriv hμν] with x hx; simp only [Pi.inv_apply, ← hx, inv_inv]

section integral

lemma set_lintegral_rnDeriv_le (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν ≤ μ s :=
  (withDensity_apply_le _ _).trans (Measure.le_iff'.1 (withDensity_rnDeriv_le μ ν) s)

lemma set_lintegral_rnDeriv' [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply _ hs, Measure.withDensity_rnDeriv_eq _ _ hμν]

lemma set_lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] [SFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply' _ s, Measure.withDensity_rnDeriv_eq _ _ hμν]

lemma lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  rw [← set_lintegral_univ, set_lintegral_rnDeriv' hμν MeasurableSet.univ]

lemma integrableOn_toReal_rnDeriv {s : Set α} (hμs : μ s ≠ ∞) :
    IntegrableOn (fun x ↦ (μ.rnDeriv ν x).toReal) s ν := by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((set_lintegral_rnDeriv_le _).trans_lt hμs.lt_top).ne

lemma setIntegral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν) s).toReal := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv_eq_withDensity' := setIntegral_toReal_rnDeriv_eq_withDensity'

lemma setIntegral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν) s).toReal := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply' _ s]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv_eq_withDensity := setIntegral_toReal_rnDeriv_eq_withDensity

lemma setIntegral_toReal_rnDeriv_le [SigmaFinite μ] {s : Set α} (hμs : μ s ≠ ∞) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν ≤ (μ s).toReal := by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t ≠ ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    ≤ ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine setIntegral_mono_set ?_ ?_ (HasSubset.Subset.eventuallyLE (subset_toMeasurable _ _))
        · exact integrableOn_toReal_rnDeriv hμt
        · exact ae_of_all _ (by simp)
  _ = (withDensity ν (rnDeriv μ ν) t).toReal := setIntegral_toReal_rnDeriv_eq_withDensity' ht_m
  _ ≤ (μ t).toReal := by
        gcongr
        · exact hμt
        · apply withDensity_rnDeriv_le
  _ = (μ s).toReal := by rw [measure_toMeasurable s]

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv_le := setIntegral_toReal_rnDeriv_le

lemma setIntegral_toReal_rnDeriv' [SigmaFinite μ] [HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (μ s).toReal := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity' hs, Measure.withDensity_rnDeriv_eq _ _ hμν]
#align measure_theory.measure.with_density_rn_deriv_to_real_eq MeasureTheory.Measure.setIntegral_toReal_rnDeriv'

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv' := setIntegral_toReal_rnDeriv'

lemma setIntegral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (μ s).toReal := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity s, Measure.withDensity_rnDeriv_eq _ _ hμν]

@[deprecated (since := "2024-04-17")]
alias set_integral_toReal_rnDeriv := setIntegral_toReal_rnDeriv

lemma integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = (μ Set.univ).toReal := by
  rw [← integral_univ, setIntegral_toReal_rnDeriv hμν Set.univ]

end integral

lemma rnDeriv_mul_rnDeriv {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hμν : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ := by
  refine (rnDeriv_withDensity_left ?_ ?_ ?_).symm.trans ?_
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · exact rnDeriv_ne_top _ _
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

lemma rnDeriv_le_one_of_le (hμν : μ ≤ ν) [SigmaFinite ν] : μ.rnDeriv ν ≤ᵐ[ν] 1 := by
  refine ae_le_of_forall_set_lintegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) measurable_const
    (fun s _ _ ↦ ?_)
  simp only [Pi.one_apply, MeasureTheory.set_lintegral_one]
  exact (Measure.set_lintegral_rnDeriv_le s).trans (hμν s)

section MeasurableEmbedding

variable {mβ : MeasurableSpace β} {f : α → β}

lemma _root_.MeasurableEmbedding.rnDeriv_map_aux (hf : MeasurableEmbedding f)
    (hμν : μ ≪ ν) [SigmaFinite μ] [SigmaFinite ν] :
    (fun x ↦ (μ.map f).rnDeriv (ν.map f) (f x)) =ᵐ[ν] μ.rnDeriv ν := by
  refine ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite ?_ ?_ (fun s _ _ ↦ ?_)
  · exact (Measure.measurable_rnDeriv _ _).comp hf.measurable
  · exact Measure.measurable_rnDeriv _ _
  rw [← hf.lintegral_map, Measure.set_lintegral_rnDeriv hμν]
  have hs_eq : s = f ⁻¹' (f '' s) := by rw [hf.injective.preimage_image]
  have : SigmaFinite (μ.map f) := hf.sigmaFinite_map
  have : SigmaFinite (ν.map f) := hf.sigmaFinite_map
  rw [hs_eq, ← hf.restrict_map, Measure.set_lintegral_rnDeriv (hf.absolutelyContinuous_map hμν),
    hf.map_apply]

lemma _root_.MeasurableEmbedding.rnDeriv_map (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (fun x ↦ (μ.map f).rnDeriv (ν.map f) (f x)) =ᵐ[ν] μ.rnDeriv ν := by
  rw [μ.haveLebesgueDecomposition_add ν, Measure.map_add _ _ hf.measurable]
  have : SigmaFinite (map f ν) := hf.sigmaFinite_map
  have : SigmaFinite (map f (μ.singularPart ν)) := hf.sigmaFinite_map
  have : SigmaFinite (map f (ν.withDensity (μ.rnDeriv ν))) := hf.sigmaFinite_map
  have h_add := Measure.rnDeriv_add' ((μ.singularPart ν).map f)
    ((ν.withDensity (μ.rnDeriv ν)).map f) (ν.map f)
  rw [Filter.EventuallyEq, hf.ae_map_iff, ← Filter.EventuallyEq] at h_add
  refine h_add.trans ((Measure.rnDeriv_add' _ _ _).trans ?_).symm
  refine Filter.EventuallyEq.add ?_ ?_
  · refine (Measure.rnDeriv_singularPart μ ν).trans ?_
    symm
    suffices (fun x ↦ ((μ.singularPart ν).map f).rnDeriv (ν.map f) x) =ᵐ[ν.map f] 0 by
      rw [Filter.EventuallyEq, hf.ae_map_iff] at this
      exact this
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ Measure.AbsolutelyContinuous.rfl
    exact hf.mutuallySingular_map (μ.mutuallySingular_singularPart ν)
  · exact (hf.rnDeriv_map_aux (withDensity_absolutelyContinuous _ _)).symm

lemma _root_.MeasurableEmbedding.map_withDensity_rnDeriv (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (ν.withDensity (μ.rnDeriv ν)).map f = (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
  ext s hs
  rw [hf.map_apply, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    set_lintegral_map hs (Measure.measurable_rnDeriv _ _) hf.measurable]
  refine set_lintegral_congr_fun (hf.measurable hs) ?_
  filter_upwards [hf.rnDeriv_map μ ν] with a ha _ using ha.symm

lemma _root_.MeasurableEmbedding.singularPart_map (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (μ.map f).singularPart (ν.map f) = (μ.singularPart ν).map f := by
  have h_add : μ.map f = (μ.singularPart ν).map f
      + (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.map_add _ _ hf.measurable, ← hf.map_withDensity_rnDeriv μ ν]
  refine (Measure.eq_singularPart (Measure.measurable_rnDeriv _ _) ?_ h_add).symm
  exact hf.mutuallySingular_map (μ.mutuallySingular_singularPart ν)

end MeasurableEmbedding

end Measure

namespace SignedMeasure

open Measure VectorMeasure

theorem withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutelyContinuous_ennreal_iff, (_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ),
    totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi, rnDeriv_def, integral_sub,
      setIntegral_toReal_rnDeriv h.1 i, setIntegral_toReal_rnDeriv h.2 i]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      erw [VectorMeasure.sub_apply]
      rw [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi]
    all_goals
      rw [← integrableOn_univ]
      refine IntegrableOn.restrict ?_ MeasurableSet.univ
      refine ⟨?_, hasFiniteIntegral_toReal_of_lintegral_ne_top ?_⟩
      · apply Measurable.aestronglyMeasurable
        -- NB. `measurability` proves this, but is quite slow
        -- TODO(#13864): reinstate faster automation, e.g. by making `fun_prop` work here
        apply (Measure.measurable_rnDeriv _ μ).ennreal_toNNReal.coe_nnreal_real
      · rw [set_lintegral_univ]
        exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ
#align measure_theory.signed_measure.with_densityᵥ_rn_deriv_eq MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α)
    [SigmaFinite μ] : s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩
#align measure_theory.signed_measure.absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq

end SignedMeasure

section IntegralRNDerivMul

open Measure

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

theorem lintegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) : ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf]
  rfl

lemma set_lintegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x in s, f x ∂μ := by
  nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  rw [set_lintegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf hs]
  simp only [Pi.mul_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integrable_rnDeriv_smul_iff [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable f μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [← integrable_withDensity_iff_integrable_smul' (E := E)
    (measurable_rnDeriv μ ν) (rnDeriv_lt_top μ ν)]

theorem withDensityᵥ_rnDeriv_smul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    ν.withDensityᵥ (fun x ↦ (rnDeriv μ ν x).toReal • f x) = μ.withDensityᵥ f := by
  rw [withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (measurable_rnDeriv μ ν).aemeasurable
    (rnDeriv_lt_top μ ν) ((integrable_rnDeriv_smul_iff hμν).mpr hf), withDensity_rnDeriv_eq μ ν hμν]

theorem integral_rnDeriv_smul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} :
    ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ := by
  by_cases hf : Integrable f μ
  · rw [← integral_univ, ← withDensityᵥ_apply ((integrable_rnDeriv_smul_iff hμν).mpr hf) .univ,
      ← integral_univ, ← withDensityᵥ_apply hf .univ, withDensityᵥ_rnDeriv_smul hμν hf]
  · rw [integral_undef hf, integral_undef]
    contrapose! hf
    exact (integrable_rnDeriv_smul_iff hμν).mp hf

end IntegralRNDerivMul

end MeasureTheory
