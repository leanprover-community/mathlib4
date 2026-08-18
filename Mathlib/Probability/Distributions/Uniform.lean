/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform distributions and probability mass functions

This file defines two related notions of uniform distributions, which will be unified in the future.

## Uniform distributions

Defines the uniform distribution for any set with finite measure.

### Main definitions
* `IsUniform X s ℙ μ` : A random variable `X` has uniform distribution on `s` under `ℙ` if the
  push-forward measure agrees with the rescaled restricted measure `μ`.

## Uniform probability mass functions

This file defines a number of uniform `PMF` distributions from various inputs,
  uniformly drawing from the corresponding object.

### Main definitions
`PMF.uniformOfFinset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`PMF.uniformOfFintype` gives all elements equal probability,
  equal to the inverse of the size of the `Fintype`.

`PMF.ofMultiset` draws randomly from the given `Multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `Multiset`

## TODO
* Refactor the `PMF` definitions to come from a `uniformMeasure` on a `Finset`/`Fintype`/`Multiset`.
-/

@[expose] public section

open scoped Finset MeasureTheory NNReal ENNReal

-- TODO: We can't `open ProbabilityTheory` without opening the `ProbabilityTheory` scope :(
open TopologicalSpace MeasureTheory.Measure PMF

noncomputable section

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace pdf

variable {Ω : Type*}
variable {_ : MeasurableSpace Ω} {ℙ : Measure Ω}

/-- A random variable `X` has uniform distribution on `s` if its push-forward measure is
`(μ s)⁻¹ • μ.restrict s`. -/
def IsUniform (X : Ω → E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :=
  map X ℙ = ProbabilityTheory.cond μ s

namespace IsUniform

theorem aemeasurable {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : AEMeasurable X ℙ := by
  dsimp [IsUniform, ProbabilityTheory.cond] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' ℝ≥0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, Measure.smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel hns hnt]

theorem absolutelyContinuous {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) : map X ℙ ≪ μ := by
  rw [hu]; exact ProbabilityTheory.cond_absolutelyContinuous

theorem measure_preimage {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) {A : Set E} (hA : MeasurableSet A) :
    ℙ (X ⁻¹' A) = μ (s ∩ A) / μ s := by
  rwa [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu, ProbabilityTheory.cond_apply',
    ENNReal.div_eq_inv_mul]

theorem isProbabilityMeasure {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : IsProbabilityMeasure ℙ :=
  ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this, hu.measure_preimage hns hnt MeasurableSet.univ, Set.inter_univ,
      ENNReal.div_self hns hnt]⟩

theorem toMeasurable_iff {X : Ω → E} {s : Set E} :
    IsUniform X (toMeasurable μ s) ℙ μ ↔ IsUniform X s ℙ μ := by
  unfold IsUniform
  rw [ProbabilityTheory.cond_toMeasurable_eq]

protected theorem toMeasurable {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) :
    IsUniform X (toMeasurable μ s) ℙ μ :=
  toMeasurable_iff.mpr hu

theorem hasPDF {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ := by
  let t := toMeasurable μ s
  apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1)) <|
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu, withDensity_indicator (measurableSet_toMeasurable μ s), withDensity_smul _ measurable_one,
    withDensity_one, restrict_toMeasurable hnt, measure_toMeasurable, ProbabilityTheory.cond]

theorem pdf_eq_zero_of_measure_eq_zero_or_top {X : Ω → E} {s : Set E}
    (hu : IsUniform X s ℙ μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rcases hμs with H | H
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]

theorem pdf_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) := by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ μ := hasPDF hns hnt hu
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hns hnt hu
  apply (eq_of_map_eq_withDensity _ _).mp
  · rw [hu, withDensity_indicator hms, withDensity_smul _ measurable_one, withDensity_one,
      ProbabilityTheory.cond]
  · exact (measurable_one.aemeasurable.const_smul (μ s)⁻¹).indicator hms

theorem pdf_toReal_ae_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal

variable {X : Ω → ℝ} {s : Set ℝ}

theorem mul_pdf_integrable (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : ℝ => x * (pdf X ℙ volume x).toReal := by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x ↦ x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hnt.1 hnt.2 huX
  constructor
  · exact aestronglyMeasurable_id.mul
      (measurable_pdf X ℙ).aemeasurable.ennreal_toReal.aestronglyMeasurable
  refine hasFiniteIntegral_mul (pdf_eq hcs.measurableSet huX) ?_
  set ind := (volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)
  have : ∀ x, ‖x‖ₑ * s.indicator ind x = s.indicator (fun x => ‖x‖ₑ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [ind, this, lintegral_indicator hcs.measurableSet, mul_one, smul_eq_mul,
    Pi.one_apply, Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_enorm]
  exact ENNReal.mul_ne_top (setLIntegral_lt_top_of_isCompact hnt.2 hcs continuous_nnnorm).ne
    (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hnt.1)).ne

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x := by
  rw [← smul_eq_mul, ← integral_smul_measure]
  dsimp only [IsUniform, ProbabilityTheory.cond] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasurable]
    rwa [aestronglyMeasurable_iff_aemeasurable]

end IsUniform

variable {X : Ω → E}

lemma IsUniform.cond {s : Set E} :
    IsUniform (id : E → E) s (ProbabilityTheory.cond μ s) μ :=
  map_id

/-- The density of the uniform measure on a set with respect to itself. This allows us to abstract
away the choice of random variable and probability space. -/
def uniformPDF (s : Set E) (x : E) (μ : Measure E := by volume_tac) : ℝ≥0∞ :=
  s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x

/-- Check that indeed any uniform random variable has the uniformPDF. -/
lemma uniformPDF_eq_pdf {s : Set E} (hs : MeasurableSet s) (hu : pdf.IsUniform X s ℙ μ) :
    (fun x ↦ uniformPDF s x μ) =ᵐ[μ] pdf X ℙ μ :=
  (hu.pdf_eq hs).symm.trans (ae_eq_refl _)

open scoped Classical in
/-- Alternative way of writing the uniformPDF. -/
lemma uniformPDF_ite {s : Set E} {x : E} :
    uniformPDF s x μ = if x ∈ s then (μ s)⁻¹ else 0 := by
  norm_num [uniformPDF, Set.indicator]

end pdf

namespace Measure

variable {α : Type*} [MeasurableSpace α]

open scoped NNReal ENNReal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniformOfFinset (s : Finset α) : Measure α :=
  ∑ a ∈ s, (s.card⁻¹ : ℝ≥0∞) • dirac a

variable [MeasurableSingletonClass α] {s : Finset α} {a : α}

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply_singleton (a : α) :
    uniformOfFinset s {a} = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [uniformOfFinset, finsetSum_apply]
  split_ifs with ha
  · rw [Finset.sum_eq_single_of_mem a ha]
    · simp
    · simp +contextual
  · rw [Finset.sum_eq_zero]
    simp
    grind

@[deprecated (since := "2026-08-18")] alias _root_.uniformOfFinset_apply :=
  uniformOfFinset_apply_singleton

theorem uniformOfFinset_apply_singleton_of_mem (ha : a ∈ s) :
    uniformOfFinset s {a} = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]

@[deprecated (since := "2026-08-18")] alias _root_.PMF.uniformOfFinset_apply_of_mem :=
  uniformOfFinset_apply_singleton_of_mem

theorem uniformOfFinset_apply_singleton_of_notMem (ha : a ∉ s) : uniformOfFinset s {a} = 0 := by
  simp [ha]

@[deprecated (since := "2026-08-18")] alias _root_.PMF.uniformOfFinset_apply_of_notMem :=
  uniformOfFinset_apply_singleton_of_notMem

@[deprecated (since := "2026-08-18")] alias _root_.PMF.support_uniformOfFinset :=
  uniformOfFinset_apply_singleton_of_mem

@[deprecated (since := "2026-08-18")] alias _root_.PMF.mem_support_uniformOfFinset_iff :=
  uniformOfFinset_apply_singleton_of_mem

section Measure

variable (t : Set α)

open scoped Classical in
theorem uniformOfFinset_apply :
    uniformOfFinset s t = #{x ∈ s | x ∈ t} / #s :=
  calc
    uniformOfFinset s t = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ := by
      rw [uniformOfFinset, finsetSum_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      split_ifs with hx' <;> simp_all
    _ = #{x ∈ s | x ∈ t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

@[deprecated (since := "2026-08-18")] alias _root_.PMF.toOuterMeasure_uniformOfFinset_apply :=
  uniformOfFinset_apply

@[deprecated (since := "2026-08-18")] alias _root_.PMF.toMeasure_uniformOfFinset_apply :=
  uniformOfFinset_apply

end Measure

end UniformOfFinset

section UniformOfFintype

@[deprecated (since := "2026-08-18")] alias _root_.PMF.uniformOfFintype := uniformOfFinset

@[deprecated (since := "2026-08-18")] alias _root_.PMF.uniformOfFintype_apply :=
  uniformOfFinset_apply_singleton

@[deprecated (since := "2026-08-18")] alias _root_.PMF.support_uniformOfFintype :=
  uniformOfFinset_apply_singleton_of_mem

@[deprecated (since := "2026-08-18")] alias _root_.PMF.mem_support_uniformOfFintype :=
  uniformOfFinset_apply_singleton_of_mem

section Measure

@[deprecated (since := "2026-08-18")] alias _root_.PMF.toOuterMeasure_uniformOfFintype_apply :=
  uniformOfFinset_apply

@[deprecated (since := "2026-08-18")] alias _root_.PMF.toMeasure_uniformOfFintype_apply :=
  uniformOfFinset_apply

end Measure

end UniformOfFintype

section OfMultiset

open scoped Classical in
/-- Given a non-empty multiset `s` we construct the measure which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def ofMultiset (s : Multiset α) : Measure α :=
  ∑ a ∈ s.toFinset, (s.count a / s.card : ℝ≥0∞) • dirac a

variable [MeasurableSingletonClass α] {s : Multiset α}

open scoped Classical in
@[simp]
theorem ofMultiset_apply_singleton (a : α) : ofMultiset s {a} = s.count a / (Multiset.card s) := by
  by_cases ha : a ∈ s
  · rw [ofMultiset, finsetSum_apply, Finset.sum_eq_single_of_mem a (by simpa)]
    · simp
    · simp +contextual
  · rw [ofMultiset, finsetSum_apply, Finset.sum_eq_zero]
    · simp [ha]
    · simp
      grind

@[deprecated (since := "2026-08-18")] alias _root_.PMF.ofMultiset_apply :=
  ofMultiset_apply_singleton

@[deprecated (since := "2026-08-18")] alias _root_.PMF.support_ofMultiset :=
  ofMultiset_apply_singleton

@[deprecated (since := "2026-08-18")] alias _root_.PMF.mem_support_ofMultiset_iff :=
  ofMultiset_apply_singleton

theorem ofMultiset_apply_singleton_of_notMem {a : α} (ha : a ∉ s) : ofMultiset s {a} = 0 := by simpa

@[deprecated (since := "2026-08-18")] alias _root_.PMF.ofMultiset_apply_of_notMem :=
  ofMultiset_apply_singleton_of_notMem

section Measure

@[deprecated (since := "2026-08-18")] alias _root_.PMF.toOuterMeasure_ofMultiset_apply :=
  ofMultiset_apply_singleton

@[deprecated (since := "2026-08-18")] alias _root_.PMF.toMeasure_ofMultiset_apply :=
  ofMultiset_apply_singleton

end Measure

end OfMultiset

end MeasureTheory.Measure
