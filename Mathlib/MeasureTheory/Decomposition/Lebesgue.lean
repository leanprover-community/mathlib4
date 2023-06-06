/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module measure_theory.decomposition.lebesgue
! leanprover-community/mathlib commit b2ff9a3d7a15fd5b0f060b135421d6a89a999c2f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.WithDensityVectorMeasure
import Mathlib.MeasureTheory.Function.AeEqOfIntegral

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ` and a measurable
function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `measure_theory.measure.have_lebesgue_decomposition` : A pair of measures `μ` and `ν` is said
  to `have_lebesgue_decomposition` if there exist a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f`
* `measure_theory.measure.singular_part` : If a pair of measures `have_lebesgue_decomposition`,
  then `singular_part` chooses the measure from `have_lebesgue_decomposition`, otherwise it
  returns the zero measure.
* `measure_theory.measure.rn_deriv`: If a pair of measures
  `have_lebesgue_decomposition`, then `rn_deriv` chooses the measurable function from
  `have_lebesgue_decomposition`, otherwise it returns the zero function.
* `measure_theory.signed_measure.have_lebesgue_decomposition` : A signed measure `s` and a
  measure `μ` is said to `have_lebesgue_decomposition` if both the positive part and negative
  part of `s` `have_lebesgue_decomposition` with respect to `μ`.
* `measure_theory.signed_measure.singular_part` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `measure_theory.signed_measure.rn_deriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite` :
  the Lebesgue decomposition theorem.
* `measure_theory.measure.eq_singular_part` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singular_part ν`.
* `measure_theory.measure.eq_rn_deriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rn_deriv ν`.
* `measure_theory.signed_measure.singular_part_add_with_density_rn_deriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

# Tags

Lebesgue decomposition theorem
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal

open Set

variable {α β : Type _} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}

include m

namespace MeasureTheory

namespace Measure

/-- A pair of measures `μ` and `ν` is said to `have_lebesgue_decomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.with_density f`. -/
class HaveLebesgueDecomposition (μ ν : Measure α) : Prop where
  lebesgue_decomposition :
    ∃ p : Measure α × (α → ℝ≥0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2
#align measure_theory.measure.have_lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition

/-- If a pair of measures `have_lebesgue_decomposition`, then `singular_part` chooses the
measure from `have_lebesgue_decomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singular_part ν + ν.with_density (μ.rn_deriv ν)`. -/
irreducible_def singularPart (μ ν : Measure α) : Measure α :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).1 else 0
#align measure_theory.measure.singular_part MeasureTheory.Measure.singularPart

/-- If a pair of measures `have_lebesgue_decomposition`, then `rn_deriv` chooses the
measurable function from `have_lebesgue_decomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singular_part ν + ν.with_density (μ.rn_deriv ν)`.-/
irreducible_def rnDeriv (μ ν : Measure α) : α → ℝ≥0∞ :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).2 else 0
#align measure_theory.measure.rn_deriv MeasureTheory.Measure.rnDeriv

theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] :
    Measurable (μ.rnDeriv ν) ∧
      μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) := by
  rw [singular_part, rn_deriv, dif_pos h, dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition
#align measure_theory.measure.have_lebesgue_decomposition_spec MeasureTheory.Measure.haveLebesgueDecomposition_spec

theorem haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  (haveLebesgueDecomposition_spec μ ν).2.2
#align measure_theory.measure.have_lebesgue_decomposition_add MeasureTheory.Measure.haveLebesgueDecomposition_add

instance haveLebesgueDecomposition_smul (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) : (r • μ).HaveLebesgueDecomposition ν
    where lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := have_lebesgue_decomposition_spec μ ν
    refine' ⟨⟨r • μ.singular_part ν, r • μ.rn_deriv ν⟩, _, hsing.smul _, _⟩
    · change Measurable ((r : ℝ≥0∞) • _)
      -- cannot remove this line
      exact hmeas.const_smul _
    · change _ = (r : ℝ≥0∞) • _ + ν.with_density ((r : ℝ≥0∞) • _)
      rw [with_density_smul _ hmeas, ← smul_add, ← hadd]
      rfl
#align measure_theory.measure.have_lebesgue_decomposition_smul MeasureTheory.Measure.haveLebesgueDecomposition_smul

@[measurability]
theorem measurable_rnDeriv (μ ν : Measure α) : Measurable <| μ.rnDeriv ν := by
  by_cases h : have_lebesgue_decomposition μ ν
  · exact (have_lebesgue_decomposition_spec μ ν).1
  · rw [rn_deriv, dif_neg h]
    exact measurable_zero
#align measure_theory.measure.measurable_rn_deriv MeasureTheory.Measure.measurable_rnDeriv

theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν := by
  by_cases h : have_lebesgue_decomposition μ ν
  · exact (have_lebesgue_decomposition_spec μ ν).2.1
  · rw [singular_part, dif_neg h]
    exact mutually_singular.zero_left
#align measure_theory.measure.mutually_singular_singular_part MeasureTheory.Measure.mutuallySingular_singularPart

theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν ≤ μ := by
  by_cases hl : have_lebesgue_decomposition μ ν
  · cases' (have_lebesgue_decomposition_spec μ ν).2 with _ h
    conv_rhs => rw [h]
    exact measure.le_add_right le_rfl
  · rw [singular_part, dif_neg hl]
    exact measure.zero_le μ
#align measure_theory.measure.singular_part_le MeasureTheory.Measure.singularPart_le

theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) ≤ μ := by
  by_cases hl : have_lebesgue_decomposition μ ν
  · cases' (have_lebesgue_decomposition_spec μ ν).2 with _ h
    conv_rhs => rw [h]
    exact measure.le_add_left le_rfl
  · rw [rn_deriv, dif_neg hl, with_density_zero]
    exact measure.zero_le μ
#align measure_theory.measure.with_density_rn_deriv_le MeasureTheory.Measure.withDensity_rnDeriv_le

instance [IsFiniteMeasure μ] : IsFiniteMeasure (μ.singularPart ν) :=
  isFiniteMeasure_of_le μ <| singularPart_le μ ν

instance [SigmaFinite μ] : SigmaFinite (μ.singularPart ν) :=
  sigmaFinite_of_le μ <| singularPart_le μ ν

instance [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.singularPart ν) :=
  isLocallyFiniteMeasure_of_le <| singularPart_le μ ν

instance [IsFiniteMeasure μ] : IsFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isFiniteMeasure_of_le μ <| withDensity_rnDeriv_le μ ν

instance [SigmaFinite μ] : SigmaFinite (ν.withDensity <| μ.rnDeriv ν) :=
  sigmaFinite_of_le μ <| withDensity_rnDeriv_le μ ν

instance [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isLocallyFiniteMeasure_of_le <| withDensity_rnDeriv_le μ ν

theorem lintegral_rnDeriv_lt_top_of_measure_ne_top {μ : Measure α} (ν : Measure α) {s : Set α}
    (hs : μ s ≠ ∞) : (∫⁻ x in s, μ.rnDeriv ν x ∂ν) < ∞ := by
  by_cases hl : have_lebesgue_decomposition μ ν
  · haveI := hl
    obtain ⟨-, -, hadd⟩ := have_lebesgue_decomposition_spec μ ν
    suffices : (∫⁻ x in to_measurable μ s, μ.rn_deriv ν x ∂ν) < ∞
    exact lt_of_le_of_lt (lintegral_mono_set (subset_to_measurable _ _)) this
    rw [← with_density_apply _ (measurable_set_to_measurable _ _)]
    refine'
      lt_of_le_of_lt
        (le_add_left le_rfl :
          _ ≤
            μ.singular_part ν (to_measurable μ s) +
              ν.with_density (μ.rn_deriv ν) (to_measurable μ s))
        _
    rw [← measure.add_apply, ← hadd, measure_to_measurable]
    exact hs.lt_top
  · erw [measure.rn_deriv, dif_neg hl, lintegral_zero]
    exact WithTop.zero_lt_top
#align measure_theory.measure.lintegral_rn_deriv_lt_top_of_measure_ne_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top

theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    (∫⁻ x, μ.rnDeriv ν x ∂ν) < ∞ := by
  rw [← set_lintegral_univ]
  exact lintegral_rn_deriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).Ne
#align measure_theory.measure.lintegral_rn_deriv_lt_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top

/-- The Radon-Nikodym derivative of a sigma-finite measure `μ` with respect to another
measure `ν` is `ν`-almost everywhere finite. -/
theorem rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x < ∞ := by
  suffices ∀ n, ∀ᵐ x ∂ν, x ∈ spanning_sets μ n → μ.rn_deriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanning_sets_index _ _)
  intro n
  rw [← ae_restrict_iff' (measurable_spanning_sets _ _)]
  apply ae_lt_top (measurable_rn_deriv _ _)
  refine' (lintegral_rn_deriv_lt_top_of_measure_ne_top _ _).Ne
  exact (measure_spanning_sets_lt_top _ _).Ne
#align measure_theory.measure.rn_deriv_lt_top MeasureTheory.Measure.rnDeriv_lt_top

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = μ.singular_part μ`.

This theorem provides the uniqueness of the `singular_part` in the Lebesgue decomposition theorem,
while `measure_theory.measure.eq_rn_deriv` provides the uniqueness of the
`rn_deriv`. -/
theorem eq_singularPart {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : s = μ.singularPart ν := by
  haveI : have_lebesgue_decomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := have_lebesgue_decomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd 
  have hνinter : ν ((S ∩ T)ᶜ) = 0 := by
    rw [compl_inter]
    refine' nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)
    rw [hT₃, hS₃, add_zero]
    exact le_rfl
  have heq : s.restrict ((S ∩ T)ᶜ) = (μ.singular_part ν).restrict ((S ∩ T)ᶜ) := by
    ext1 A hA
    have hf : ν.with_density f (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine' with_density_absolutely_continuous ν _ _
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono (inter_subset_right _ _)
    have hrn : ν.with_density (μ.rn_deriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine' with_density_absolutely_continuous ν _ _
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono (inter_subset_right _ _)
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (s (A ∩ (S ∩ T)ᶜ)), ← hf, ← add_apply, ←
      hadd, add_apply, hrn, add_zero]
  have heq' : ∀ A : Set α, MeasurableSet A → s A = s.restrict ((S ∩ T)ᶜ) A := by
    intro A hA
    have hsinter : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_left _ _))
    rw [restrict_apply hA, ← diff_eq, ae_disjoint.measure_diff_left hsinter]
  ext1 A hA
  have hμinter : μ.singular_part ν (A ∩ (S ∩ T)) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact hT₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_right _ _))
  rw [heq' A hA, HEq, restrict_apply hA, ← diff_eq, ae_disjoint.measure_diff_left hμinter]
#align measure_theory.measure.eq_singular_part MeasureTheory.Measure.eq_singularPart

theorem singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0 := by
  refine' (eq_singular_part measurable_zero mutually_singular.zero_left _).symm
  rw [zero_add, with_density_zero]
#align measure_theory.measure.singular_part_zero MeasureTheory.Measure.singularPart_zero

theorem singularPart_smul (μ ν : Measure α) (r : ℝ≥0) :
    (r • μ).singularPart ν = r • μ.singularPart ν := by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singular_part_zero]
  by_cases hl : have_lebesgue_decomposition μ ν
  · haveI := hl
    refine'
      (eq_singular_part ((measurable_rn_deriv μ ν).const_smul (r : ℝ≥0∞))
          (mutually_singular.smul r (have_lebesgue_decomposition_spec _ _).2.1) _).symm
    rw [with_density_smul _ (measurable_rn_deriv _ _), ← smul_add, ←
      have_lebesgue_decomposition_add μ ν, ENNReal.smul_def]
  · rw [singular_part, singular_part, dif_neg hl, dif_neg, smul_zero]
    refine' fun hl' => hl _
    rw [← inv_smul_smul₀ hr μ]
    exact @measure.have_lebesgue_decomposition_smul _ _ _ _ hl' _
#align measure_theory.measure.singular_part_smul MeasureTheory.Measure.singularPart_smul

theorem singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + μ₂.singularPart ν := by
  refine'
    (eq_singular_part ((measurable_rn_deriv μ₁ ν).add (measurable_rn_deriv μ₂ ν))
        ((have_lebesgue_decomposition_spec _ _).2.1.add_left
          (have_lebesgue_decomposition_spec _ _).2.1)
        _).symm
  erw [with_density_add_left (measurable_rn_deriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singular_part ν), ← add_assoc, ← add_assoc]
  rw [← have_lebesgue_decomposition_add μ₁ ν, add_assoc, add_comm (ν.with_density (μ₂.rn_deriv ν)),
    ← have_lebesgue_decomposition_add μ₂ ν]
#align measure_theory.measure.singular_part_add MeasureTheory.Measure.singularPart_add

theorem singularPart_withDensity (ν : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).singularPart ν = 0 :=
  haveI : ν.with_density f = 0 + ν.with_density f := by rw [zero_add]
  (eq_singular_part hf mutually_singular.zero_left this).symm
#align measure_theory.measure.singular_part_with_density MeasureTheory.Measure.singularPart_withDensity

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rn_deriv ν`.

This theorem provides the uniqueness of the `rn_deriv` in the Lebesgue decomposition
theorem, while `measure_theory.measure.eq_singular_part` provides the uniqueness of the
`singular_part`. Here, the uniqueness is given in terms of the measures, while the uniqueness in
terms of the functions is given in `eq_rn_deriv`. -/
theorem eq_withDensity_rnDeriv {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  haveI : have_lebesgue_decomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := have_lebesgue_decomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd 
  have hνinter : ν ((S ∩ T)ᶜ) = 0 := by
    rw [compl_inter]
    refine' nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)
    rw [hT₃, hS₃, add_zero]
    exact le_rfl
  have heq :
    (ν.with_density f).restrict (S ∩ T) = (ν.with_density (μ.rn_deriv ν)).restrict (S ∩ T) := by
    ext1 A hA
    have hs : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_left _ _))
    have hsing : μ.singular_part ν (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hT₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_right _ _))
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (ν.with_density f (A ∩ (S ∩ T))), ← hs, ←
      add_apply, add_comm, ← hadd, add_apply, hsing, zero_add]
  have heq' :
    ∀ A : Set α, MeasurableSet A → ν.with_density f A = (ν.with_density f).restrict (S ∩ T) A := by
    intro A hA
    have hνfinter : ν.with_density f (A ∩ (S ∩ T)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact with_density_absolutely_continuous ν f hνinter ▸ measure_mono (inter_subset_right _ _)
    rw [restrict_apply hA, ← add_zero (ν.with_density f (A ∩ (S ∩ T))), ← hνfinter, ← diff_eq,
      measure_inter_add_diff _ (hS₁.inter hT₁)]
  ext1 A hA
  have hνrn : ν.with_density (μ.rn_deriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact
      with_density_absolutely_continuous ν (μ.rn_deriv ν) hνinter ▸
        measure_mono (inter_subset_right _ _)
  rw [heq' A hA, HEq, ← add_zero ((ν.with_density (μ.rn_deriv ν)).restrict (S ∩ T) A), ← hνrn,
    restrict_apply hA, ← diff_eq, measure_inter_add_diff _ (hS₁.inter hT₁)]
#align measure_theory.measure.eq_with_density_rn_deriv MeasureTheory.Measure.eq_withDensity_rnDeriv

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rn_deriv ν`.

This theorem provides the uniqueness of the `rn_deriv` in the Lebesgue decomposition
theorem, while `measure_theory.measure.eq_singular_part` provides the uniqueness of the
`singular_part`. Here, the uniqueness is given in terms of the functions, while the uniqueness in
terms of the functions is given in `eq_with_density_rn_deriv`. -/
theorem eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν := by
  refine' ae_eq_of_forall_set_lintegral_eq_of_sigma_finite hf (measurable_rn_deriv μ ν) _
  intro a ha h'a
  calc
    (∫⁻ x : α in a, f x ∂ν) = ν.with_density f a := (with_density_apply f ha).symm
    _ = ν.with_density (μ.rn_deriv ν) a := by rw [eq_with_density_rn_deriv hf hs hadd]
    _ = ∫⁻ x : α in a, μ.rn_deriv ν x ∂ν := with_density_apply _ ha
    
#align measure_theory.measure.eq_rn_deriv MeasureTheory.Measure.eq_rnDeriv

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  haveI : ν.with_density f = 0 + ν.with_density f := by rw [zero_add]
  (eq_rn_deriv hf mutually_singular.zero_left this).symm
#align measure_theory.measure.rn_deriv_with_density MeasureTheory.Measure.rnDeriv_withDensity

/-- The Radon-Nikodym derivative of the restriction of a measure to a measurable set is the
indicator function of this set. -/
theorem rnDeriv_restrict (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1 := by
  rw [← with_density_indicator_one hs]
  exact rn_deriv_with_density _ (measurable_one.indicator hs)
#align measure_theory.measure.rn_deriv_restrict MeasureTheory.Measure.rnDeriv_restrict

open VectorMeasure SignedMeasure

/-- If two finite measures `μ` and `ν` are not mutually singular, there exists some `ε > 0` and
a measurable set `E`, such that `ν(E) > 0` and `E` is positive with respect to `μ - εν`.

This lemma is useful for the Lebesgue decomposition theorem. -/
theorem exists_positive_of_not_mutuallySingular (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ¬μ ⟂ₘ ν) :
    ∃ ε : ℝ≥0,
      0 < ε ∧
        ∃ E : Set α,
          MeasurableSet E ∧ 0 < ν E ∧ 0 ≤[E] μ.toSignedMeasure - (ε • ν).toSignedMeasure := by
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have :
    ∀ n : ℕ,
      ∃ i : Set α,
        MeasurableSet i ∧
          0 ≤[i] μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ∧
            μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ≤[iᶜ] 0 :=
    by intro; exact exists_compl_positive_negative _
  choose f hf₁ hf₂ hf₃ using this
  -- set `A` to be the intersection of all the negative parts of obtained Hahn decompositions
  -- and we show that `μ A = 0`
  set A := ⋂ n, f nᶜ with hA₁
  have hAmeas : MeasurableSet A := MeasurableSet.iInter fun n => (hf₁ n).compl
  have hA₂ : ∀ n : ℕ, μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ≤[A] 0 := by
    intro n; exact restrict_le_restrict_subset _ _ (hf₁ n).compl (hf₃ n) (Inter_subset _ _)
  have hA₃ : ∀ n : ℕ, μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A := by
    intro n
    have := nonpos_of_restrict_le_zero _ (hA₂ n)
    rwa [to_signed_measure_sub_apply hAmeas, sub_nonpos, ENNReal.toReal_le_toReal] at this 
    exacts [ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)]
  have hμ : μ A = 0 := by
    lift μ A to ℝ≥0 using ne_of_lt (measure_lt_top _ _) with μA
    lift ν A to ℝ≥0 using ne_of_lt (measure_lt_top _ _) with νA
    rw [ENNReal.coe_eq_zero]
    by_cases hb : 0 < νA
    · suffices ∀ b, 0 < b → μA ≤ b by
        by_contra
        have h' := this (μA / 2) (half_pos (zero_lt_iff.2 h))
        rw [← @Classical.not_not (μA ≤ μA / 2)] at h' 
        exact h' (not_le.2 (NNReal.half_lt_self h))
      intro c hc
      have : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c * νA⁻¹; refine' exists_nat_one_div_lt _
      · refine' mul_pos hc _
        rw [_root_.inv_pos]; exact hb
      rcases this with ⟨n, hn⟩
      have hb₁ : (0 : ℝ) < νA⁻¹ := by rw [_root_.inv_pos]; exact hb
      have h' : 1 / (↑n + 1) * νA < c := by
        rw [← NNReal.coe_lt_coe, ← mul_lt_mul_right hb₁, NNReal.coe_mul, mul_assoc, ←
          NNReal.coe_inv, ← NNReal.coe_mul, _root_.mul_inv_cancel, ← NNReal.coe_mul, mul_one,
          NNReal.coe_inv]
        · exact hn
        · exact Ne.symm (ne_of_lt hb)
      refine' le_trans _ (le_of_lt h')
      rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
      exact hA₃ n
    · rw [not_lt, le_zero_iff] at hb 
      specialize hA₃ 0
      simp [hb, le_zero_iff] at hA₃ 
      assumption
  -- since `μ` and `ν` are not mutually singular, `μ A = 0` implies `ν Aᶜ > 0`
  rw [mutually_singular] at h ;
  push_neg at h 
  have := h _ hAmeas hμ
  simp_rw [hA₁, compl_Inter, compl_compl] at this 
  -- as `Aᶜ = ⋃ n, f n`, `ν Aᶜ > 0` implies there exists some `n` such that `ν (f n) > 0`
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_Union_null this
  -- thus, choosing `f n` as the set `E` suffices
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩
#align measure_theory.measure.exists_positive_of_not_mutually_singular MeasureTheory.Measure.exists_positive_of_not_mutuallySingular

namespace LebesgueDecomposition

/-- Given two measures `μ` and `ν`, `measurable_le μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`.

This is useful for the Lebesgue decomposition theorem. -/
def measurableLe (μ ν : Measure α) : Set (α → ℝ≥0∞) :=
  {f | Measurable f ∧ ∀ (A : Set α) (hA : MeasurableSet A), (∫⁻ x in A, f x ∂μ) ≤ ν A}
#align measure_theory.measure.lebesgue_decomposition.measurable_le MeasureTheory.Measure.LebesgueDecomposition.measurableLe

theorem zero_mem_measurableLe : (0 : α → ℝ≥0∞) ∈ measurableLe μ ν :=
  ⟨measurable_zero, fun A hA => by simp⟩
#align measure_theory.measure.lebesgue_decomposition.zero_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.zero_mem_measurableLe

theorem sup_mem_measurableLe {f g : α → ℝ≥0∞} (hf : f ∈ measurableLe μ ν)
    (hg : g ∈ measurableLe μ ν) : (fun a => f a ⊔ g a) ∈ measurableLe μ ν := by
  simp_rw [ENNReal.sup_eq_max]
  refine' ⟨Measurable.max hf.1 hg.1, fun A hA => _⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [set_lintegral_max hf.1 hg.1]
  refine' (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq _
  · simp only [← not_le, ← compl_set_of, ← diff_eq]
    exact measure_inter_add_diff _ (measurableSet_le hf.1 hg.1)
#align measure_theory.measure.lebesgue_decomposition.sup_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.sup_mem_measurableLe

theorem iSup_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
    (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) = f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a := by
  ext x
  simp only [Option.mem_def, ENNReal.some_eq_coe]
  constructor <;> intro h <;> rw [← h]; symm
  all_goals
    set c := ⨆ (k : ℕ) (hk : k ≤ m + 1), f k a with hc
    set d := f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a with hd
    rw [@le_antisymm_iff ℝ≥0∞, hc, hd]
    -- Specifying the type is weirdly necessary
    refine' ⟨_, _⟩
    · refine' iSup₂_le fun n hn => _
      rcases Nat.of_le_succ hn with (h | h)
      · exact le_sup_of_le_right (le_iSup₂ n h)
      · exact h ▸ le_sup_left
    · refine' sup_le _ (biSup_mono fun n hn => hn.trans m.le_succ)
      convert @le_iSup₂ _ _ (fun i => i ≤ m + 1) _ _ m.succ le_rfl
      rfl
#align measure_theory.measure.lebesgue_decomposition.supr_succ_eq_sup MeasureTheory.Measure.LebesgueDecomposition.iSup_succ_eq_sup

theorem iSup_mem_measurableLe (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLe μ ν) (n : ℕ) :
    (fun x => ⨆ (k) (hk : k ≤ n), f k x) ∈ measurableLe μ ν := by
  induction' n with m hm
  · refine' ⟨_, _⟩
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  · have :
      (fun a : α => ⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) = fun a =>
        f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a :=
      funext fun _ => supr_succ_eq_sup _ _ _
    refine' ⟨measurable_iSup fun n => Measurable.iSup_Prop _ (hf n).1, fun A hA => _⟩
    rw [this]; exact (sup_mem_measurable_le (hf m.succ) hm).2 A hA
#align measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLe

theorem iSup_mem_measurable_le' (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLe μ ν) (n : ℕ) :
    (⨆ (k) (hk : k ≤ n), f k) ∈ measurableLe μ ν := by
  convert supr_mem_measurable_le f hf n
  ext; simp
#align measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le' MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurable_le'

section SuprLemmas

--TODO: these statements should be moved elsewhere
omit m

theorem iSup_monotone {α : Type _} (f : ℕ → α → ℝ≥0∞) :
    Monotone fun n x => ⨆ (k) (hk : k ≤ n), f k x := fun n m hnm x =>
  biSup_mono fun i => ge_trans hnm
#align measure_theory.measure.lebesgue_decomposition.supr_monotone MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone

theorem iSup_monotone' {α : Type _} (f : ℕ → α → ℝ≥0∞) (x : α) :
    Monotone fun n => ⨆ (k) (hk : k ≤ n), f k x := fun n m hnm => iSup_monotone f hnm x
#align measure_theory.measure.lebesgue_decomposition.supr_monotone' MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone'

theorem iSup_le_le {α : Type _} (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
    f k ≤ fun x => ⨆ (k) (hk : k ≤ n), f k x := fun x => le_iSup₂ k hk
#align measure_theory.measure.lebesgue_decomposition.supr_le_le MeasureTheory.Measure.LebesgueDecomposition.iSup_le_le

end SuprLemmas

/-- `measurable_le_eval μ ν` is the set of `∫⁻ x, f x ∂μ` for all `f ∈ measurable_le μ ν`. -/
def measurableLeEval (μ ν : Measure α) : Set ℝ≥0∞ :=
  (fun f : α → ℝ≥0∞ => ∫⁻ x, f x ∂μ) '' measurableLe μ ν
#align measure_theory.measure.lebesgue_decomposition.measurable_le_eval MeasureTheory.Measure.LebesgueDecomposition.measurableLeEval

end LebesgueDecomposition

open LebesgueDecomposition

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (n k) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (n k) -/
/-- Any pair of finite measures `μ` and `ν`, `have_lebesgue_decomposition`. That is to say,
there exist a measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular
with respect to `ν` and `μ = ξ + ν.with_density f`.

This is not an instance since this is also shown for the more general σ-finite measures with
`measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite`. -/
theorem haveLebesgueDecomposition_of_finite_measure [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HaveLebesgueDecomposition μ ν :=
  ⟨by
    have h :=
      @exists_seq_tendsto_sSup _ _ _ _ _ (measurable_le_eval ν μ)
        ⟨0, 0, zero_mem_measurable_le, by simp⟩ (OrderTop.bddAbove _)
    choose g hmono hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (hk : k ≤ n), f k with hξ
    -- we see that `ξ` has the largest integral among all functions in `measurable_le`
    have hξ₁ : Sup (measurable_le_eval ν μ) = ∫⁻ a, ξ a ∂ν := by
      have :=
        @lintegral_tendsto_of_tendsto_of_monotone _ _ ν (fun n => ⨆ (k) (hk : k ≤ n), f k)
          (⨆ (n) (k) (hk : k ≤ n), f k) _ _ _
      · refine' tendsto_nhds_unique _ this
        refine' tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds _ _
        · intro n; rw [← hf₂ n]
          apply lintegral_mono
          simp only [iSup_apply, supr_le_le f n n le_rfl]
        · intro n
          exact le_sSup ⟨⨆ (k : ℕ) (hk : k ≤ n), f k, supr_mem_measurable_le' _ hf₁ _, rfl⟩
      · intro n
        refine' Measurable.aemeasurable _
        convert (supr_mem_measurable_le _ hf₁ n).1
        ext; simp
      · refine' Filter.eventually_of_forall fun a => _
        simp [supr_monotone' f _]
      · refine' Filter.eventually_of_forall fun a => _
        simp [tendsto_atTop_iSup (supr_monotone' f a)]
    have hξm : Measurable ξ := by
      convert measurable_iSup fun n => (supr_mem_measurable_le _ hf₁ n).1
      ext; simp [hξ]
    -- `ξ` is the `f` in the theorem statement and we set `μ₁` to be `μ - ν.with_density ξ`
    -- since we need `μ₁ + ν.with_density ξ = μ`
    set μ₁ := μ - ν.with_density ξ with hμ₁
    have hle : ν.with_density ξ ≤ μ := by
      intro B hB
      rw [hξ, with_density_apply _ hB]
      simp_rw [iSup_apply]
      rw [lintegral_supr (fun i => (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _)]
      exact iSup_le fun i => (supr_mem_measurable_le _ hf₁ i).2 B hB
    have : is_finite_measure (ν.with_density ξ) := by
      refine' is_finite_measure_with_density _
      have hle' := hle univ MeasurableSet.univ
      rw [with_density_apply _ MeasurableSet.univ, measure.restrict_univ] at hle' 
      exact ne_top_of_le_ne_top (measure_ne_top _ _) hle'
    refine' ⟨⟨μ₁, ξ⟩, hξm, _, _⟩
    · by_contra
      -- if they are not mutually singular, then from `exists_positive_of_not_mutually_singular`,
      -- there exists some `ε > 0` and a measurable set `E`, such that `μ(E) > 0` and `E` is
      -- positive with respect to `ν - εμ`
      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_not_mutually_singular μ₁ ν h
      simp_rw [hμ₁] at hE₃ 
      have hξle : ∀ A, MeasurableSet A → (∫⁻ a in A, ξ a ∂ν) ≤ μ A := by
        intro A hA; rw [hξ]
        simp_rw [iSup_apply]
        rw [lintegral_supr (fun n => (supr_mem_measurable_le _ hf₁ n).1) (supr_monotone _)]
        exact iSup_le fun n => (supr_mem_measurable_le _ hf₁ n).2 A hA
      -- since `E` is positive, we have `∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E)` for all `A`
      have hε₂ : ∀ A : Set α, MeasurableSet A → (∫⁻ a in A ∩ E, ε + ξ a ∂ν) ≤ μ (A ∩ E) := by
        intro A hA
        have := subset_le_of_restrict_le_restrict _ _ hE₁ hE₃ (inter_subset_right A E)
        rwa [zero_apply, to_signed_measure_sub_apply (hA.inter hE₁),
          measure.sub_apply (hA.inter hE₁) hle,
          ENNReal.toReal_sub_of_le _ (ne_of_lt (measure_lt_top _ _)), sub_nonneg, le_sub_iff_add_le,
          ← ENNReal.toReal_add, ENNReal.toReal_le_toReal, measure.coe_smul, Pi.smul_apply,
          with_density_apply _ (hA.inter hE₁), show ε • ν (A ∩ E) = (ε : ℝ≥0∞) * ν (A ∩ E) by rfl, ←
          set_lintegral_const, ← lintegral_add_left measurable_const] at this 
        · rw [Ne.def, ENNReal.add_eq_top, not_or]
          exact ⟨ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)⟩
        · exact ne_of_lt (measure_lt_top _ _)
        · exact ne_of_lt (measure_lt_top _ _)
        · exact ne_of_lt (measure_lt_top _ _)
        · rw [with_density_apply _ (hA.inter hE₁)]
          exact hξle (A ∩ E) (hA.inter hE₁)
        · infer_instance
      -- from this, we can show `ξ + ε * E.indicator` is a function in `measurable_le` with
      -- integral greater than `ξ`
      have hξε : (ξ + E.indicator fun _ => ε) ∈ measurable_le ν μ := by
        refine' ⟨Measurable.add hξm (Measurable.indicator measurable_const hE₁), fun A hA => _⟩
        have :
          (∫⁻ a in A, (ξ + E.indicator fun _ => ε) a ∂ν) =
            (∫⁻ a in A ∩ E, ε + ξ a ∂ν) + ∫⁻ a in A \ E, ξ a ∂ν := by
          simp only [lintegral_add_left measurable_const, lintegral_add_left hξm,
            set_lintegral_const, add_assoc, lintegral_inter_add_diff _ _ hE₁, Pi.add_apply,
            lintegral_indicator _ hE₁, restrict_apply hE₁]
          rw [inter_comm, add_comm]
        rw [this, ← measure_inter_add_diff A hE₁]
        exact add_le_add (hε₂ A hA) (hξle (A \ E) (hA.diff hE₁))
      have : (∫⁻ a, ξ a + E.indicator (fun _ => ε) a ∂ν) ≤ Sup (measurable_le_eval ν μ) :=
        le_sSup ⟨ξ + E.indicator fun _ => ε, hξε, rfl⟩
      -- but this contradicts the maximality of `∫⁻ x, ξ x ∂ν`
      refine' not_lt.2 this _
      rw [hξ₁, lintegral_add_left hξm, lintegral_indicator _ hE₁, set_lintegral_const]
      refine' ENNReal.lt_add_right _ (ENNReal.mul_pos_iff.2 ⟨ENNReal.coe_pos.2 hε₁, hE₂⟩).ne'
      have := measure_ne_top (ν.with_density ξ) univ
      rwa [with_density_apply _ MeasurableSet.univ, measure.restrict_univ] at this 
    -- since `ν.with_density ξ ≤ μ`, it is clear that `μ = μ₁ + ν.with_density ξ`
    · rw [hμ₁]; ext1 A hA
      rw [measure.coe_add, Pi.add_apply, measure.sub_apply hA hle, add_comm,
        add_tsub_cancel_of_le (hle A hA)]⟩
#align measure_theory.measure.have_lebesgue_decomposition_of_finite_measure MeasureTheory.Measure.haveLebesgueDecomposition_of_finite_measure

attribute [local instance] have_lebesgue_decomposition_of_finite_measure

instance {S : μ.FiniteSpanningSetsIn {s : Set α | MeasurableSet s}} (n : ℕ) :
    IsFiniteMeasure (μ.restrict <| S.Set n) :=
  ⟨by rw [restrict_apply MeasurableSet.univ, univ_inter]; exact S.finite _⟩

-- see Note [lower instance priority]
/-- **The Lebesgue decomposition theorem**: Any pair of σ-finite measures `μ` and `ν`
`have_lebesgue_decomposition`. That is to say, there exist a measure `ξ` and a measurable function
`f`, such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f` -/
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] : HaveLebesgueDecomposition μ ν :=
  ⟨by
    -- Since `μ` and `ν` are both σ-finite, there exists a sequence of pairwise disjoint spanning
    -- sets which are finite with respect to both `μ` and `ν`
    obtain ⟨S, T, h₁, h₂⟩ := exists_eq_disjoint_finite_spanning_sets_in μ ν
    have h₃ : Pairwise (Disjoint on T.set) := h₁ ▸ h₂
    -- We define `μn` and `νn` as sequences of measures such that `μn n = μ ∩ S n` and
    -- `νn n = ν ∩ S n` where `S` is the aforementioned finite spanning set sequence.
    -- Since `S` is spanning, it is clear that `sum μn = μ` and `sum νn = ν`
    set μn : ℕ → Measure α := fun n => μ.restrict (S.set n) with hμn
    have hμ : μ = Sum μn := by rw [hμn, ← restrict_Union h₂ S.set_mem, S.spanning, restrict_univ]
    set νn : ℕ → Measure α := fun n => ν.restrict (T.set n) with hνn
    have hν : ν = Sum νn := by rw [hνn, ← restrict_Union h₃ T.set_mem, T.spanning, restrict_univ]
    -- As `S` is finite with respect to both `μ` and `ν`, it is clear that `μn n` and `νn n` are
    -- finite measures for all `n : ℕ`. Thus, we may apply the finite Lebesgue decomposition theorem
    -- to `μn n` and `νn n`. We define `ξ` as the sum of the singular part of the Lebesgue
    -- decompositions of `μn n` and `νn n`, and `f` as the sum of the Radon-Nikodym derviatives of
    -- `μn n` and `νn n` restricted on `S n`
    set ξ := Sum fun n => singular_part (μn n) (νn n) with hξ
    set f := ∑' n, (S.set n).indicator (rn_deriv (μn n) (νn n)) with hf
    -- I claim `ξ` and `f` form a Lebesgue decomposition of `μ` and `ν`
    refine' ⟨⟨ξ, f⟩, _, _, _⟩
    ·
      exact
        Measurable.ennreal_tsum' fun n =>
          Measurable.indicator (measurable_rn_deriv (μn n) (νn n)) (S.set_mem n)
    -- We show that `ξ` is mutually singular with respect to `ν`
    · choose A hA₁ hA₂ hA₃ using fun n => mutually_singular_singular_part (μn n) (νn n)
      simp only [hξ]
      -- We use the set `B := ⋃ j, (S.set j) ∩ A j` where `A n` is the set provided as
      -- `singular_part (μn n) (νn n) ⟂ₘ νn n`
      refine' ⟨⋃ j, S.set j ∩ A j, MeasurableSet.iUnion fun n => (S.set_mem n).inter (hA₁ n), _, _⟩
      -- `ξ B = 0` since `ξ B = ∑ i j, singular_part (μn j) (νn j) (S.set i ∩ A i)`
      --                     `= ∑ i, singular_part (μn i) (νn i) (S.set i ∩ A i)`
      --                     `≤ ∑ i, singular_part (μn i) (νn i) (A i) = 0`
      -- where the second equality follows as `singular_part (μn j) (νn j) (S.set i ∩ A i)` vanishes
      -- for all `i ≠ j`
      · rw [measure_Union]
        · have :
            ∀ i,
              (Sum fun n => (μn n).singularPart (νn n)) (S.set i ∩ A i) =
                (μn i).singularPart (νn i) (S.set i ∩ A i) := by
            intro i; rw [sum_apply _ ((S.set_mem i).inter (hA₁ i)), tsum_eq_single i]
            · intro j hij
              rw [hμn, ← nonpos_iff_eq_zero]
              refine' le_trans ((singular_part_le _ _) _ ((S.set_mem i).inter (hA₁ i))) (le_of_eq _)
              rw [restrict_apply ((S.set_mem i).inter (hA₁ i)), inter_comm, ← inter_assoc]
              have : Disjoint (S.set j) (S.set i) := h₂ hij
              rw [disjoint_iff_inter_eq_empty] at this 
              rw [this, empty_inter, measure_empty]
            · infer_instance
          simp_rw [this, tsum_eq_zero_iff ENNReal.summable]
          intro n; exact measure_mono_null (inter_subset_right _ _) (hA₂ n)
        · exact h₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left
        · exact fun n => (S.set_mem n).inter (hA₁ n)
      -- We will now show `ν Bᶜ = 0`. This follows since `Bᶜ = ⋃ n, S.set n ∩ (A n)ᶜ` and thus,
      -- `ν Bᶜ = ∑ i, ν (S.set i ∩ (A i)ᶜ) = ∑ i, (νn i) (A i)ᶜ = 0`
      · have hcompl : IsCompl (⋃ n, S.set n ∩ A n) (⋃ n, S.set n ∩ A nᶜ) := by
          constructor
          · rw [disjoint_iff_inf_le]
            rintro x ⟨hx₁, hx₂⟩; rw [mem_Union] at hx₁ hx₂ 
            obtain ⟨⟨i, hi₁, hi₂⟩, ⟨j, hj₁, hj₂⟩⟩ := hx₁, hx₂
            have : i = j := by by_contra hij; exact (h₂ hij).le_bot ⟨hi₁, hj₁⟩
            exact hj₂ (this ▸ hi₂)
          · rw [codisjoint_iff_le_sup]
            intro x hx
            simp only [mem_Union, sup_eq_union, mem_inter_iff, mem_union, mem_compl_iff,
              or_iff_not_imp_left]
            intro h; push_neg at h 
            rw [top_eq_univ, ← S.spanning, mem_Union] at hx 
            obtain ⟨i, hi⟩ := hx
            exact ⟨i, hi, h i hi⟩
        rw [hcompl.compl_eq, measure_Union, tsum_eq_zero_iff ENNReal.summable]
        · intro n; rw [inter_comm, ← restrict_apply (hA₁ n).compl, ← hA₃ n, hνn, h₁]
        · exact h₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left
        · exact fun n => (S.set_mem n).inter (hA₁ n).compl
    -- Finally, it remains to show `μ = ξ + ν.with_density f`. Since `μ = sum μn`, and
    -- `ξ + ν.with_density f = ∑ n, singular_part (μn n) (νn n)`
    --                        `+ ν.with_density (rn_deriv (μn n) (νn n)) ∩ (S.set n)`,
    -- it suffices to show that the individual summands are equal. This follows by the
    -- Lebesgue decomposition properties on the individual `μn n` and `νn n`
    · simp only [hξ, hf, hμ]
      rw [with_density_tsum _, sum_add_sum]
      · refine' sum_congr fun n => _
        conv_lhs => rw [have_lebesgue_decomposition_add (μn n) (νn n)]
        suffices heq :
          (νn n).withDensity ((μn n).rnDeriv (νn n)) =
            ν.with_density ((S.set n).indicator ((μn n).rnDeriv (νn n)))
        · rw [HEq]
        rw [hν, with_density_indicator (S.set_mem n), restrict_sum _ (S.set_mem n)]
        suffices hsumeq : (Sum fun i : ℕ => (νn i).restrict (S.set n)) = νn n
        · rw [hsumeq]
        ext1 s hs
        rw [sum_apply _ hs, tsum_eq_single n, hνn, h₁, restrict_restrict (T.set_mem n), inter_self]
        · intro m hm
          rw [hνn, h₁, restrict_restrict (T.set_mem n), (h₃ hm.symm).inter_eq, restrict_empty,
            coe_zero, Pi.zero_apply]
        · infer_instance
      · exact fun n => Measurable.indicator (measurable_rn_deriv _ _) (S.set_mem n)⟩
#align measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite

end Measure

namespace SignedMeasure

open Measure

/-- A signed measure `s` is said to `have_lebesgue_decomposition` with respect to a measure `μ`
if the positive part and the negative part of `s` both `have_lebesgue_decomposition` with
respect to `μ`. -/
class HaveLebesgueDecomposition (s : SignedMeasure α) (μ : Measure α) : Prop where
  posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
  negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ
#align measure_theory.signed_measure.have_lebesgue_decomposition MeasureTheory.SignedMeasure.HaveLebesgueDecomposition

attribute [instance] have_lebesgue_decomposition.pos_part

attribute [instance] have_lebesgue_decomposition.neg_part

theorem not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) :
    ¬s.HaveLebesgueDecomposition μ ↔
      ¬s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ ∨
        ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩
#align measure_theory.signed_measure.not_have_lebesgue_decomposition_iff MeasureTheory.SignedMeasure.not_haveLebesgueDecomposition_iff

-- `infer_instance` directly does not work
-- see Note [lower instance priority]
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (s : SignedMeasure α)
    (μ : Measure α) [SigmaFinite μ] : s.HaveLebesgueDecomposition μ where
  posPart := inferInstance
  negPart := inferInstance
#align measure_theory.signed_measure.have_lebesgue_decomposition_of_sigma_finite MeasureTheory.SignedMeasure.haveLebesgueDecomposition_of_sigmaFinite

instance haveLebesgueDecomposition_neg (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] : (-s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [to_jordan_decomposition_neg, jordan_decomposition.neg_pos_part]
    infer_instance
  negPart := by
    rw [to_jordan_decomposition_neg, jordan_decomposition.neg_neg_part]
    infer_instance
#align measure_theory.signed_measure.have_lebesgue_decomposition_neg MeasureTheory.SignedMeasure.haveLebesgueDecomposition_neg

instance haveLebesgueDecomposition_smul (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ≥0) : (r • s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [to_jordan_decomposition_smul, jordan_decomposition.smul_pos_part]
    infer_instance
  negPart := by
    rw [to_jordan_decomposition_smul, jordan_decomposition.smul_neg_part]
    infer_instance
#align measure_theory.signed_measure.have_lebesgue_decomposition_smul MeasureTheory.SignedMeasure.haveLebesgueDecomposition_smul

instance haveLebesgueDecomposition_smul_real (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ) : (r • s).HaveLebesgueDecomposition μ := by
  by_cases hr : 0 ≤ r
  · lift r to ℝ≥0 using hr
    exact s.have_lebesgue_decomposition_smul μ _
  · rw [not_le] at hr 
    refine'
      { posPart := by
          rw [to_jordan_decomposition_smul_real, jordan_decomposition.real_smul_pos_part_neg _ _ hr]
          infer_instance
        negPart := by
          rw [to_jordan_decomposition_smul_real, jordan_decomposition.real_smul_neg_part_neg _ _ hr]
          infer_instance }
#align measure_theory.signed_measure.have_lebesgue_decomposition_smul_real MeasureTheory.SignedMeasure.haveLebesgueDecomposition_smul_real

/-- Given a signed measure `s` and a measure `μ`, `s.singular_part μ` is the signed measure
such that `s.singular_part μ + μ.with_densityᵥ (s.rn_deriv μ) = s` and
`s.singular_part μ` is mutually singular with respect to `μ`. -/
def singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α :=
  (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure
#align measure_theory.signed_measure.singular_part MeasureTheory.SignedMeasure.singularPart

section

theorem singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) :
    s.toJordanDecomposition.posPart.singularPart μ ⟂ₘ
      s.toJordanDecomposition.negPart.singularPart μ := by
  by_cases hl : s.have_lebesgue_decomposition μ
  · haveI := hl
    obtain ⟨i, hi, hpos, hneg⟩ := s.to_jordan_decomposition.mutually_singular
    rw [s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition_add μ] at hpos 
    rw [s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition_add μ] at hneg 
    rw [add_apply, add_eq_zero_iff] at hpos hneg 
    exact ⟨i, hi, hpos.1, hneg.1⟩
  · rw [not_have_lebesgue_decomposition_iff] at hl 
    cases' hl with hp hn
    · rw [measure.singular_part, dif_neg hp]
      exact mutually_singular.zero_left
    · rw [measure.singular_part, measure.singular_part, dif_neg hn]
      exact mutually_singular.zero_right
#align measure_theory.signed_measure.singular_part_mutually_singular MeasureTheory.SignedMeasure.singularPart_mutuallySingular

theorem singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) :
    (s.singularPart μ).totalVariation =
      s.toJordanDecomposition.posPart.singularPart μ +
        s.toJordanDecomposition.negPart.singularPart μ := by
  have :
    (s.singular_part μ).toJordanDecomposition =
      ⟨s.to_jordan_decomposition.pos_part.singular_part μ,
        s.to_jordan_decomposition.neg_part.singular_part μ, singular_part_mutually_singular s μ⟩ :=
    by
    refine' jordan_decomposition.to_signed_measure_injective _
    rw [to_signed_measure_to_jordan_decomposition]
    rfl
  · rw [total_variation, this]
#align measure_theory.signed_measure.singular_part_total_variation MeasureTheory.SignedMeasure.singularPart_totalVariation

theorem mutuallySingular_singularPart (s : SignedMeasure α) (μ : Measure α) :
    singularPart s μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  rw [mutually_singular_ennreal_iff, singular_part_total_variation]
  change _ ⟂ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ)
  rw [vector_measure.equiv_measure.right_inv μ]
  exact (mutually_singular_singular_part _ _).add_left (mutually_singular_singular_part _ _)
#align measure_theory.signed_measure.mutually_singular_singular_part MeasureTheory.SignedMeasure.mutuallySingular_singularPart

end

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`rn_deriv s μ` satisfies `μ.with_densityᵥ (s.rn_deriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`measure_theory.signed_measure.absolutely_continuous_iff_with_density_rn_deriv_eq`
and can be found in `measure_theory.decomposition.radon_nikodym`. -/
def rnDeriv (s : SignedMeasure α) (μ : Measure α) : α → ℝ := fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal
#align measure_theory.signed_measure.rn_deriv MeasureTheory.SignedMeasure.rnDeriv

variable {s t : SignedMeasure α}

@[measurability]
theorem measurable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Measurable (rnDeriv s μ) := by
  rw [rn_deriv]
  measurability
#align measure_theory.signed_measure.measurable_rn_deriv MeasureTheory.SignedMeasure.measurable_rnDeriv

theorem integrable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ := by
  refine' integrable.sub _ _ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable; measurability
      exact has_finite_integral_to_real_of_lintegral_ne_top (lintegral_rn_deriv_lt_top _ μ).Ne
#align measure_theory.signed_measure.integrable_rn_deriv MeasureTheory.SignedMeasure.integrable_rnDeriv

variable (s μ)

/-- **The Lebesgue Decomposition theorem between a signed measure and a measure**:
Given a signed measure `s` and a σ-finite measure `μ`, there exist a signed measure `t` and a
measurable and integrable function `f`, such that `t` is mutually singular with respect to `μ`
and `s = t + μ.with_densityᵥ f`. In this case `t = s.singular_part μ` and
`f = s.rn_deriv μ`. -/
theorem singularPart_add_with_density_rnDeriv_eq [s.HaveLebesgueDecomposition μ] :
    s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s := by
  conv_rhs =>
    rw [← to_signed_measure_to_jordan_decomposition s, jordan_decomposition.to_signed_measure]
  rw [singular_part, rn_deriv,
    with_densityᵥ_sub' (integrable_to_real_of_lintegral_ne_top _ _)
      (integrable_to_real_of_lintegral_ne_top _ _),
    with_densityᵥ_to_real, with_densityᵥ_to_real, sub_eq_add_neg, sub_eq_add_neg,
    add_comm (s.to_jordan_decomposition.pos_part.singular_part μ).toSignedMeasure, ← add_assoc,
    add_assoc (-(s.to_jordan_decomposition.neg_part.singular_part μ).toSignedMeasure), ←
    to_signed_measure_add, add_comm, ← add_assoc, ← neg_add, ← to_signed_measure_add, add_comm, ←
    sub_eq_add_neg]
  convert rfl
  -- `convert rfl` much faster than `congr`
  · exact s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition_add μ
  · rw [add_comm]
    exact s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition_add μ
  all_goals
    first
    | exact (lintegral_rn_deriv_lt_top _ _).Ne
    | measurability
#align measure_theory.signed_measure.singular_part_add_with_density_rn_deriv_eq MeasureTheory.SignedMeasure.singularPart_add_with_density_rnDeriv_eq

variable {s μ}

theorem jordan_decomposition_add_withDensity_mutuallySingular {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) :
    (t.toJordanDecomposition.posPart + μ.withDensity fun x : α => ENNReal.ofReal (f x)) ⟂ₘ
      t.toJordanDecomposition.negPart + μ.withDensity fun x : α => ENNReal.ofReal (-f x) := by
  rw [mutually_singular_ennreal_iff, total_variation_mutually_singular_iff] at htμ 
  change
    _ ⟂ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) ∧
      _ ⟂ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) at
    htμ 
  rw [vector_measure.equiv_measure.right_inv] at htμ 
  exact
    ((jordan_decomposition.mutually_singular _).add_right
          (htμ.1.mono_ac (refl _) (with_density_absolutely_continuous _ _))).add_left
      ((htμ.2.symm.mono_ac (with_density_absolutely_continuous _ _) (refl _)).add_right
        (with_density_of_real_mutually_singular hf))
#align measure_theory.signed_measure.jordan_decomposition_add_with_density_mutually_singular MeasureTheory.SignedMeasure.jordan_decomposition_add_withDensity_mutuallySingular

theorem toJordanDecomposition_eq_of_eq_add_withDensity {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.toJordanDecomposition =
      @JordanDecomposition.mk α _
        (t.toJordanDecomposition.posPart + μ.withDensity fun x => ENNReal.ofReal (f x))
        (t.toJordanDecomposition.negPart + μ.withDensity fun x => ENNReal.ofReal (-f x))
        (by haveI := is_finite_measure_with_density_of_real hfi.2; infer_instance)
        (by haveI := is_finite_measure_with_density_of_real hfi.neg.2; infer_instance)
        (jordan_decomposition_add_withDensity_mutuallySingular hf htμ) := by
  haveI := is_finite_measure_with_density_of_real hfi.2
  haveI := is_finite_measure_with_density_of_real hfi.neg.2
  refine' to_jordan_decomposition_eq _
  simp_rw [jordan_decomposition.to_signed_measure, hadd]
  ext (i hi)
  rw [vector_measure.sub_apply, to_signed_measure_apply_measurable hi,
      to_signed_measure_apply_measurable hi, add_apply, add_apply, ENNReal.toReal_add,
      ENNReal.toReal_add, add_sub_add_comm, ← to_signed_measure_apply_measurable hi, ←
      to_signed_measure_apply_measurable hi, ← vector_measure.sub_apply, ←
      jordan_decomposition.to_signed_measure, to_signed_measure_to_jordan_decomposition,
      vector_measure.add_apply, ← to_signed_measure_apply_measurable hi, ←
      to_signed_measure_apply_measurable hi,
      with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part hfi,
      vector_measure.sub_apply] <;>
    exact (measure_lt_top _ _).Ne
#align measure_theory.signed_measure.to_jordan_decomposition_eq_of_eq_add_with_density MeasureTheory.SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity

private theorem have_lebesgue_decomposition_mk' (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  have htμ' := htμ
  rw [mutually_singular_ennreal_iff] at htμ 
  change _ ⟂ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) at htμ 
  rw [vector_measure.equiv_measure.right_inv, total_variation_mutually_singular_iff] at htμ 
  refine'
    { posPart := by
        use ⟨t.to_jordan_decomposition.pos_part, fun x => ENNReal.ofReal (f x)⟩
        refine' ⟨hf.ennreal_of_real, htμ.1, _⟩
        rw [to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd]
      negPart := by
        use ⟨t.to_jordan_decomposition.neg_part, fun x => ENNReal.ofReal (-f x)⟩
        refine' ⟨hf.neg.ennreal_of_real, htμ.2, _⟩
        rw [to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd] }

theorem haveLebesgueDecomposition_mk (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  by_cases hfi : integrable f μ
  · exact have_lebesgue_decomposition_mk' μ hf hfi htμ hadd
  · rw [with_densityᵥ, dif_neg hfi, add_zero] at hadd 
    refine' have_lebesgue_decomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ _
    rwa [with_densityᵥ_zero, add_zero]
#align measure_theory.signed_measure.have_lebesgue_decomposition_mk MeasureTheory.SignedMeasure.haveLebesgueDecomposition_mk

private theorem eq_singular_part' (t : SignedMeasure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    t = s.singularPart μ := by
  have htμ' := htμ
  rw [mutually_singular_ennreal_iff, total_variation_mutually_singular_iff] at htμ 
  change
    _ ⟂ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) ∧
      _ ⟂ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) at
    htμ 
  rw [vector_measure.equiv_measure.right_inv] at htμ 
  · rw [singular_part, ← t.to_signed_measure_to_jordan_decomposition,
      jordan_decomposition.to_signed_measure]
    congr
    · have hfpos : Measurable fun x => ENNReal.ofReal (f x) := by measurability
      refine' eq_singular_part hfpos htμ.1 _
      rw [to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd]
    · have hfneg : Measurable fun x => ENNReal.ofReal (-f x) := by measurability
      refine' eq_singular_part hfneg htμ.2 _
      rw [to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd]

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.with_densityᵥ f`, we have
`t = singular_part s μ`, i.e. `t` is the singular part of the Lebesgue decomposition between
`s` and `μ`. -/
theorem eq_singularPart (t : SignedMeasure α) (f : α → ℝ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure)
    (hadd : s = t + μ.withDensityᵥ f) : t = s.singularPart μ := by
  by_cases hfi : integrable f μ
  · refine' eq_singular_part' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ _
    convert hadd using 2
    exact with_densityᵥ_eq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [with_densityᵥ, dif_neg hfi, add_zero] at hadd 
    refine' eq_singular_part' t measurable_zero (integrable_zero _ _ μ) htμ _
    rwa [with_densityᵥ_zero, add_zero]
#align measure_theory.signed_measure.eq_singular_part MeasureTheory.SignedMeasure.eq_singularPart

theorem singularPart_zero (μ : Measure α) : (0 : SignedMeasure α).singularPart μ = 0 := by
  refine' (eq_singular_part 0 0 vector_measure.mutually_singular.zero_left _).symm
  rw [zero_add, with_densityᵥ_zero]
#align measure_theory.signed_measure.singular_part_zero MeasureTheory.SignedMeasure.singularPart_zero

theorem singularPart_neg (s : SignedMeasure α) (μ : Measure α) :
    (-s).singularPart μ = -s.singularPart μ := by
  have h₁ :
    ((-s).toJordanDecomposition.posPart.singularPart μ).toSignedMeasure =
      (s.to_jordan_decomposition.neg_part.singular_part μ).toSignedMeasure := by
    refine' to_signed_measure_congr _
    rw [to_jordan_decomposition_neg, jordan_decomposition.neg_pos_part]
  have h₂ :
    ((-s).toJordanDecomposition.negPart.singularPart μ).toSignedMeasure =
      (s.to_jordan_decomposition.pos_part.singular_part μ).toSignedMeasure := by
    refine' to_signed_measure_congr _
    rw [to_jordan_decomposition_neg, jordan_decomposition.neg_neg_part]
  rw [singular_part, singular_part, neg_sub, h₁, h₂]
#align measure_theory.signed_measure.singular_part_neg MeasureTheory.SignedMeasure.singularPart_neg

theorem singularPart_smul_nNReal (s : SignedMeasure α) (μ : Measure α) (r : ℝ≥0) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  rw [singular_part, singular_part, smul_sub, ← to_signed_measure_smul, ← to_signed_measure_smul]
  conv_lhs =>
    congr
    congr
    rw [to_jordan_decomposition_smul, jordan_decomposition.smul_pos_part, singular_part_smul]
    skip
    congr
    rw [to_jordan_decomposition_smul, jordan_decomposition.smul_neg_part, singular_part_smul]
#align measure_theory.signed_measure.singular_part_smul_nnreal MeasureTheory.SignedMeasure.singularPart_smul_nNReal

theorem singularPart_smul (s : SignedMeasure α) (μ : Measure α) (r : ℝ) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  by_cases hr : 0 ≤ r
  · lift r to ℝ≥0 using hr
    exact singular_part_smul_nnreal s μ r
  · rw [singular_part, singular_part]
    conv_lhs =>
      congr
      congr
      rw [to_jordan_decomposition_smul_real,
        jordan_decomposition.real_smul_pos_part_neg _ _ (not_le.1 hr), singular_part_smul]
      skip
      congr
      rw [to_jordan_decomposition_smul_real,
        jordan_decomposition.real_smul_neg_part_neg _ _ (not_le.1 hr), singular_part_smul]
    rw [to_signed_measure_smul, to_signed_measure_smul, ← neg_sub, ← smul_sub]
    change -(((-r).toNNReal : ℝ) • _) = _
    rw [← neg_smul, Real.coe_toNNReal _ (le_of_lt (neg_pos.mpr (not_le.1 hr))), neg_neg]
#align measure_theory.signed_measure.singular_part_smul MeasureTheory.SignedMeasure.singularPart_smul

theorem singularPart_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s + t).singularPart μ = s.singularPart μ + t.singularPart μ := by
  refine'
    (eq_singular_part _ (s.rn_deriv μ + t.rn_deriv μ)
        ((mutually_singular_singular_part s μ).add_left (mutually_singular_singular_part t μ))
        _).symm
  erw [with_densityᵥ_add (integrable_rn_deriv s μ) (integrable_rn_deriv t μ)]
  rw [add_assoc, add_comm (t.singular_part μ), add_assoc, add_comm _ (t.singular_part μ),
    singular_part_add_with_density_rn_deriv_eq, ← add_assoc,
    singular_part_add_with_density_rn_deriv_eq]
#align measure_theory.signed_measure.singular_part_add MeasureTheory.SignedMeasure.singularPart_add

theorem singularPart_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s - t).singularPart μ = s.singularPart μ - t.singularPart μ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, singular_part_add, singular_part_neg]
#align measure_theory.signed_measure.singular_part_sub MeasureTheory.SignedMeasure.singularPart_sub

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.with_densityᵥ f`, we have
`f = rn_deriv s μ`, i.e. `f` is the Radon-Nikodym derivative of `s` and `μ`. -/
theorem eq_rnDeriv (t : SignedMeasure α) (f : α → ℝ) (hfi : Integrable f μ)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) : f =ᵐ[μ] s.rnDeriv μ :=
  by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.with_densityᵥ f' := by
    convert hadd using 2
    exact with_densityᵥ_eq.congr_ae hfi.1.ae_eq_mk.symm
  haveI := have_lebesgue_decomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine' (integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _) hfi _).symm
  rw [← add_right_inj t, ← hadd, eq_singular_part _ f htμ hadd,
    singular_part_add_with_density_rn_deriv_eq]
#align measure_theory.signed_measure.eq_rn_deriv MeasureTheory.SignedMeasure.eq_rnDeriv

theorem rnDeriv_neg (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] :
    (-s).rnDeriv μ =ᵐ[μ] -s.rnDeriv μ := by
  refine'
    integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _) (integrable_rn_deriv _ _).neg _
  rw [with_densityᵥ_neg, ← add_right_inj ((-s).singularPart μ),
    singular_part_add_with_density_rn_deriv_eq, singular_part_neg, ← neg_add,
    singular_part_add_with_density_rn_deriv_eq]
#align measure_theory.signed_measure.rn_deriv_neg MeasureTheory.SignedMeasure.rnDeriv_neg

theorem rnDeriv_smul (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : ℝ) :
    (r • s).rnDeriv μ =ᵐ[μ] r • s.rnDeriv μ := by
  refine'
    integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _)
      ((integrable_rn_deriv _ _).smul r) _
  change _ = μ.with_densityᵥ ((r : ℝ) • s.rn_deriv μ)
  rw [with_densityᵥ_smul (rn_deriv s μ) (r : ℝ), ← add_right_inj ((r • s).singularPart μ),
    singular_part_add_with_density_rn_deriv_eq, singular_part_smul]
  change _ = _ + r • _
  rw [← smul_add, singular_part_add_with_density_rn_deriv_eq]
#align measure_theory.signed_measure.rn_deriv_smul MeasureTheory.SignedMeasure.rnDeriv_smul

theorem rnDeriv_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [(s + t).HaveLebesgueDecomposition μ] :
    (s + t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ + t.rnDeriv μ := by
  refine'
    integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _)
      ((integrable_rn_deriv _ _).add (integrable_rn_deriv _ _)) _
  rw [← add_right_inj ((s + t).singularPart μ), singular_part_add_with_density_rn_deriv_eq,
    with_densityᵥ_add (integrable_rn_deriv _ _) (integrable_rn_deriv _ _), singular_part_add,
    add_assoc, add_comm (t.singular_part μ), add_assoc, add_comm _ (t.singular_part μ),
    singular_part_add_with_density_rn_deriv_eq, ← add_assoc,
    singular_part_add_with_density_rn_deriv_eq]
#align measure_theory.signed_measure.rn_deriv_add MeasureTheory.SignedMeasure.rnDeriv_add

theorem rnDeriv_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [hst : (s - t).HaveLebesgueDecomposition μ] :
    (s - t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ - t.rnDeriv μ := by
  rw [sub_eq_add_neg] at hst 
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact ae_eq_trans (rn_deriv_add _ _ _) (Filter.EventuallyEq.add (ae_eq_refl _) (rn_deriv_neg _ _))
#align measure_theory.signed_measure.rn_deriv_sub MeasureTheory.SignedMeasure.rnDeriv_sub

end SignedMeasure

namespace ComplexMeasure

/-- A complex measure is said to `have_lebesgue_decomposition` with respect to a positive measure
if both its real and imaginary part `have_lebesgue_decomposition` with respect to that measure. -/
class HaveLebesgueDecomposition (c : ComplexMeasure α) (μ : Measure α) : Prop where
  re_part : c.re.HaveLebesgueDecomposition μ
  im_part : c.im.HaveLebesgueDecomposition μ
#align measure_theory.complex_measure.have_lebesgue_decomposition MeasureTheory.ComplexMeasure.HaveLebesgueDecomposition

attribute [instance] have_lebesgue_decomposition.re_part

attribute [instance] have_lebesgue_decomposition.im_part

/-- The singular part between a complex measure `c` and a positive measure `μ` is the complex
measure satisfying `c.singular_part μ + μ.with_densityᵥ (c.rn_deriv μ) = c`. This property is given
by `measure_theory.complex_measure.singular_part_add_with_density_rn_deriv_eq`. -/
def singularPart (c : ComplexMeasure α) (μ : Measure α) : ComplexMeasure α :=
  (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)
#align measure_theory.complex_measure.singular_part MeasureTheory.ComplexMeasure.singularPart

/-- The Radon-Nikodym derivative between a complex measure and a positive measure. -/
def rnDeriv (c : ComplexMeasure α) (μ : Measure α) : α → ℂ := fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩
#align measure_theory.complex_measure.rn_deriv MeasureTheory.ComplexMeasure.rnDeriv

variable {c : ComplexMeasure α}

theorem integrable_rnDeriv (c : ComplexMeasure α) (μ : Measure α) : Integrable (c.rnDeriv μ) μ := by
  rw [← mem_ℒp_one_iff_integrable, ← mem_ℒp_re_im_iff]
  exact
    ⟨mem_ℒp_one_iff_integrable.2 (signed_measure.integrable_rn_deriv _ _),
      mem_ℒp_one_iff_integrable.2 (signed_measure.integrable_rn_deriv _ _)⟩
#align measure_theory.complex_measure.integrable_rn_deriv MeasureTheory.ComplexMeasure.integrable_rnDeriv

theorem singularPart_add_with_density_rnDeriv_eq [c.HaveLebesgueDecomposition μ] :
    c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c := by
  conv_rhs => rw [← c.to_complex_measure_to_signed_measure]
  ext (i hi) : 1
  rw [vector_measure.add_apply, signed_measure.to_complex_measure_apply]
  ext
  · rw [Complex.add_re, with_densityᵥ_apply (c.integrable_rn_deriv μ) hi, ← IsROrC.re_eq_complex_re,
      ← integral_re (c.integrable_rn_deriv μ).IntegrableOn, IsROrC.re_eq_complex_re, ←
      with_densityᵥ_apply _ hi]
    · change (c.re.singular_part μ + μ.with_densityᵥ (c.re.rn_deriv μ)) i = _
      rw [c.re.singular_part_add_with_density_rn_deriv_eq μ]
    · exact signed_measure.integrable_rn_deriv _ _
  · rw [Complex.add_im, with_densityᵥ_apply (c.integrable_rn_deriv μ) hi, ← IsROrC.im_eq_complex_im,
      ← integral_im (c.integrable_rn_deriv μ).IntegrableOn, IsROrC.im_eq_complex_im, ←
      with_densityᵥ_apply _ hi]
    · change (c.im.singular_part μ + μ.with_densityᵥ (c.im.rn_deriv μ)) i = _
      rw [c.im.singular_part_add_with_density_rn_deriv_eq μ]
    · exact signed_measure.integrable_rn_deriv _ _
#align measure_theory.complex_measure.singular_part_add_with_density_rn_deriv_eq MeasureTheory.ComplexMeasure.singularPart_add_with_density_rnDeriv_eq

end ComplexMeasure

end MeasureTheory

