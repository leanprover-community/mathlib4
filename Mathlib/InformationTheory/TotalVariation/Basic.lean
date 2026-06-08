/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance between finite measures

TODO

Note that with this definition, the total variation distance between two mutually singular
probability measures is equal to `2`, which is the maximum possible value for this distance.
Some authors prefer to define the total variation distance as half of the value defined here,
so that it takes values in `[0, 1]`.

## Main definitions

* `vecTVDist μ ν`: total variation distance between two vector measures, defined as the value on
  the universal set of the variation of `μ - ν`.
* `tvDist μ ν`: total variation distance between two finite measures, defined as the value on
  the universal set of the variation of `μ - ν`, in which both measures are seen as signed measures.

## Main statements

* `vecTVDist_self`, `vecTVDist_eq_zero_iff`, `vecTVDist_comm`, `vecTVDist_triangle`: the total
  variation distance between vector measures is a distance.
* `tvDist_self`, `tvDist_eq_zero_iff`, `tvDist_comm`, `tvDist_triangle`: the total variation
  distance between finite measures is a distance.

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

section VectorMeasure

variable {M : Type*} [NormedAddCommGroup M] {μ ν : VectorMeasure 𝓧 M}

/-- Total variation distance between two vector measures. -/
noncomputable def vecTVDist {M : Type*} [NormedAddCommGroup M]
    (μ ν : VectorMeasure 𝓧 M) : ℝ≥0∞ := (μ - ν).variation Set.univ

lemma vecTVDist_eq_iSup_finPartition_enorm :
    vecTVDist μ ν = ⨆ P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧))),
      ∑ x ∈ P.parts, ‖μ x - ν x‖ₑ := by
  simp [vecTVDist, VectorMeasure.variation, preVariation, ennrealPreVariation,
    VectorMeasure.ennrealToMeasure_apply .univ, preVariationFun]

@[simp]
lemma vecTVDist_self (μ : VectorMeasure 𝓧 M) : vecTVDist μ μ = 0 := by simp [vecTVDist]

@[simp]
lemma vecTVDist_eq_zero_iff (μ ν : VectorMeasure 𝓧 M) : vecTVDist μ ν = 0 ↔ μ = ν := by
  simp [vecTVDist, sub_eq_zero]

lemma vecTVDist_comm (μ ν : VectorMeasure 𝓧 M) : vecTVDist μ ν = vecTVDist ν μ := by
  unfold vecTVDist
  rw [← neg_sub, VectorMeasure.variation_neg]

lemma vecTVDist_triangle (μ ν ξ : VectorMeasure 𝓧 M) :
    vecTVDist μ ξ ≤ vecTVDist μ ν + vecTVDist ν ξ := by
  calc vecTVDist μ ξ
  _ = ((μ - ν) + (ν - ξ)).variation Set.univ := by simp [vecTVDist]
  _ ≤ vecTVDist μ ν + vecTVDist ν ξ := VectorMeasure.variation_add_le _

lemma vecTVDist_zero_right (μ : VectorMeasure 𝓧 M) : vecTVDist μ 0 = μ.variation Set.univ := by
  simp only [vecTVDist, sub_zero]

lemma vecTVDist_zero_left (ν : VectorMeasure 𝓧 M) : vecTVDist 0 ν = ν.variation Set.univ := by
  rw [vecTVDist_comm, vecTVDist_zero_right]

lemma vecTVDist_eq_sub_zero : vecTVDist μ ν = vecTVDist (μ - ν) 0 := by simp [vecTVDist]

lemma vecTVDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    vecTVDist (μ.restrict s) (ν.restrict s) + vecTVDist (μ.restrict sᶜ) (ν.restrict sᶜ) =
      vecTVDist μ ν := by
  unfold vecTVDist
  simp_rw [← VectorMeasure.restrict_sub, VectorMeasure.variation_restrict hs,
    VectorMeasure.variation_restrict hs.compl]
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
  simp [← measure_union disjoint_compl_right hs.compl]

end VectorMeasure

section Measure

variable {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Total variation distance between two finite measures. -/
noncomputable def tvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (vecTVDist μ.toSignedMeasure ν.toSignedMeasure).toReal

@[simp] lemma tvDist_nonneg : 0 ≤ tvDist μ ν := ENNReal.toReal_nonneg

lemma vecTVDist_toSignedMeasure_lt_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure < ∞ := by
  calc vecTVDist μ.toSignedMeasure ν.toSignedMeasure
  _ ≤ vecTVDist μ.toSignedMeasure 0 + vecTVDist 0 ν.toSignedMeasure := vecTVDist_triangle _ _ _
  _ = μ Set.univ + ν Set.univ := by simp [vecTVDist_zero_right, vecTVDist_zero_left]
  _ < ∞ := by simp

@[simp]
lemma vecTVDist_toSignedMeasure_ne_top (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure ≠ ∞ :=
  (vecTVDist_toSignedMeasure_lt_top μ ν).ne

lemma vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs :
    vecTVDist μ.toSignedMeasure ν.toSignedMeasure =
      ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
        ∑ p ∈ P.parts, ‖μ.real p - ν.real p‖ₑ := by
  rw [vecTVDist_eq_iSup_finPartition_enorm]
  simp only [Measure.toSignedMeasure_apply]
  congr with P
  congr with s
  simp [s.2]

lemma tvDist_eq_iSup_finPartition_abs :
    tvDist μ ν = ⨆ (P : Finpartition (⟨.univ, .univ⟩ : Subtype (MeasurableSet (α := 𝓧)))),
      ∑ p ∈ P.parts, |μ.real p - ν.real p| := by
  rw [tvDist, vecTVDist_toSignedMeasure_eq_iSup_finPartition_abs, ENNReal.toReal_iSup (by simp)]
  congr with P
  rw [ENNReal.toReal_sum (by simp)]
  simp

@[simp]
lemma tvDist_self (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ μ = 0 := by simp [tvDist]

@[simp]
lemma tvDist_eq_zero_iff (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  tvDist μ ν = 0 ↔ μ = ν := by simp [tvDist, ENNReal.toReal_eq_zero_iff]

lemma tvDist_comm (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  rw [vecTVDist_comm]

lemma tvDist_triangle (μ ν ξ : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  unfold tvDist
  rw [← ENNReal.toReal_add (by simp) (by simp)]
  gcongr
  · simp
  exact vecTVDist_triangle _ _ _

@[simp]
lemma tvDist_zero_right (μ : Measure 𝓧) [IsFiniteMeasure μ] : tvDist μ 0 = μ.real Set.univ := by
  simp only [tvDist, vecTVDist, Measure.toSignedMeasure_zero, sub_zero,
    VectorMeasure.variation_toSignedMeasure]
  rfl

@[simp]
lemma tvDist_zero_left (ν : Measure 𝓧) [IsFiniteMeasure ν] : tvDist 0 ν = ν.real Set.univ := by
  rw [tvDist_comm, tvDist_zero_right]

lemma tvDist_of_ge (hμν : ν ≤ μ) : tvDist μ ν = μ.real Set.univ - ν.real Set.univ := by
  calc tvDist μ ν
  _ = tvDist (μ - ν) 0 := by
    simp only [tvDist_eq_iSup_finPartition_abs, measureReal_zero, Pi.zero_apply, sub_zero]
    congr with P
    congr with s
    congr 1
    simp only [Measure.real]
    rw [Measure.sub_apply s.2 hμν, ENNReal.toReal_sub_of_le (hμν s) (by simp)]
  _ = (μ - ν).real Set.univ := by simp [tvDist_zero_right]
  _ = μ.real Set.univ - ν.real Set.univ := by
    rw [Measure.real, Measure.sub_apply .univ hμν, ENNReal.toReal_sub_of_le (hμν .univ) (by simp)]
    rfl

lemma tvDist_of_le (hμν : μ ≤ ν) : tvDist μ ν = ν.real Set.univ - μ.real Set.univ := by
  rw [tvDist_comm, tvDist_of_ge hμν]

lemma tvDist_le_add : tvDist μ ν ≤ μ.real Set.univ + ν.real Set.univ := by
  calc tvDist μ ν
  _ ≤ tvDist μ 0 + tvDist 0 ν := tvDist_triangle _ _ _
  _ = μ.real Set.univ + ν.real Set.univ := by simp [tvDist_zero_right, tvDist_zero_left]

lemma tvDist_restrict_add_compl {s : Set 𝓧} (hs : MeasurableSet s) :
    tvDist (μ.restrict s) (ν.restrict s) + tvDist (μ.restrict sᶜ) (ν.restrict sᶜ) = tvDist μ ν := by
  unfold tvDist
  rw [← ENNReal.toReal_add (by simp) (by simp)]
  rw [← VectorMeasure.restrict_toSignedMeasure hs,
    ← VectorMeasure.restrict_toSignedMeasure hs.compl, ← VectorMeasure.restrict_toSignedMeasure hs,
    ← VectorMeasure.restrict_toSignedMeasure hs.compl, vecTVDist_restrict_add_compl hs]

lemma tvDist_of_mutuallySingular (hμν : μ ⟂ₘ ν) :
    tvDist μ ν = μ.real Set.univ + ν.real Set.univ := by
  rw [add_comm, ← tvDist_restrict_add_compl hμν.measurableSet_nullSet]
  simp

lemma tvDist_eq_of_isHahnDecomposition {s : Set 𝓧} (h : IsHahnDecomposition μ ν s) :
    tvDist μ ν = ν.real s - μ.real s + (μ.real sᶜ - ν.real sᶜ) := by
  rw [← tvDist_restrict_add_compl h.measurableSet, tvDist_of_le h.le_on, tvDist_of_ge h.ge_on_compl]
  simp

lemma setLIntegral_withDensity_le_one_le {μ : Measure 𝓧} (f : 𝓧 → ℝ≥0∞) (s : Set 𝓧) :
    ∫⁻ x in s ∩ {x | f x ≤ 1}, f x ∂μ ≤ μ (s ∩ {x | f x ≤ 1}) := by
  calc ∫⁻ x in s ∩ {x | f x ≤ 1}, f x ∂μ
  _ ≤ ∫⁻ x in s ∩ {x | f x ≤ 1}, 1 ∂μ := setLIntegral_mono measurable_const (by grind)
  _ = μ (s ∩ {x | f x ≤ 1}) := by simp

lemma IsHahnDecomposition_withDensity_le_one {μ : Measure 𝓧} {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) :
    IsHahnDecomposition (μ.withDensity f) μ {x | f x ≤ 1} := by
  constructor
  · exact measurableSet_le hf measurable_const
  · refine Measure.le_intro fun t ht _ ↦ ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
      withDensity_apply _ (ht.inter (measurableSet_le hf measurable_const))]
    exact setLIntegral_withDensity_le_one_le f t
  · refine Measure.le_intro fun t ht _ ↦ ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
      withDensity_apply _ (ht.inter (measurableSet_le hf measurable_const).compl)]
    calc μ (t ∩ {x | f x ≤ 1}ᶜ)
    _ = ∫⁻ x in t ∩ {x | f x ≤ 1}ᶜ, 1 ∂μ := by simp
    _ ≤ ∫⁻ x in t ∩ {x | f x ≤ 1}ᶜ, f x ∂μ := setLIntegral_mono hf (by grind)

lemma tvDist_withDensity_self_eq_integral {f : 𝓧 → ℝ≥0∞} (hf : Measurable f)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞)
    [IsFiniteMeasure (μ.withDensity f)] :
    tvDist (μ.withDensity f) μ = ∫ x, |1 - (f x).toReal| ∂μ := by
  have h_hahn : IsHahnDecomposition (μ.withDensity f) μ {x | f x ≤ 1} :=
    IsHahnDecomposition_withDensity_le_one hf
  rw [tvDist_eq_of_isHahnDecomposition h_hahn]
  unfold Measure.real
  rw [withDensity_apply _ (measurableSet_le hf measurable_const),
    withDensity_apply _ (measurableSet_le hf measurable_const).compl]
  rw [← integral_toReal (by fun_prop), ← integral_toReal (by fun_prop)]
  rotate_left
  · exact ae_restrict_of_ae <| by filter_upwards [hf_top] with x hx using hx.lt_top
  · exact ae_restrict_of_ae <| by filter_upwards [hf_top] with x hx using hx.lt_top
  have hf_int : Integrable (fun x ↦ (f x).toReal) μ := by
    rw [integrable_toReal_iff (by fun_prop) hf_top, ← setLIntegral_univ,
      ← withDensity_apply _ .univ]
    exact measure_ne_top _ _
  have h1 : μ.real {x | f x ≤ 1} - ∫ x in {x | f x ≤ 1}, (f x).toReal ∂μ =
      ∫ x in {x | f x ≤ 1}, 1 - (f x).toReal ∂μ := by
    rw [← setIntegral_one_eq_measureReal, ← integral_sub (by simp) hf_int.integrableOn]
  have h2 : ∫ x in {x | f x ≤ 1}ᶜ, (f x).toReal ∂μ - μ.real {x | f x ≤ 1}ᶜ =
      ∫ x in {x | f x ≤ 1}ᶜ, (f x).toReal - 1 ∂μ := by
    rw [← setIntegral_one_eq_measureReal, ← integral_sub hf_int.integrableOn (by simp)]
  rw [← Measure.real, ← Measure.real, h1, h2]
  calc ∫ x in {x | f x ≤ 1}, 1 - (f x).toReal ∂μ + ∫ x in {x | f x ≤ 1}ᶜ, (f x).toReal - 1 ∂μ
  _ = ∫ x in {x | f x ≤ 1}, |1 - (f x).toReal| ∂μ +
      ∫ x in {x | f x ≤ 1}ᶜ,|1 - (f x).toReal| ∂μ := by
    congr 1
    · refine setIntegral_congr_fun (measurableSet_le hf measurable_const) fun x hx ↦ ?_
      rw [abs_of_nonneg]
      simp only [Set.mem_setOf_eq, sub_nonneg] at hx ⊢
      exact ENNReal.toReal_le_of_le_ofReal (by simp) (by simp [hx])
    · refine setIntegral_congr_ae (measurableSet_le hf measurable_const).compl ?_
      filter_upwards [hf_top] with x hx_top hx
      rw [abs_of_nonpos]
      · simp
      · simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
        simp only [tsub_le_iff_right, zero_add]
        rw [← ENNReal.toReal_one]
        gcongr
  _ = ∫ x, |1 - (f x).toReal| ∂μ := by
    refine integral_add_compl (measurableSet_le hf measurable_const) ?_
    exact (Integrable.sub (by simp) hf_int).abs

lemma tvDist_eq_integral_abs_rnDeriv_of_ac (hμν : μ ≪ ν) :
    tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν := by
  have : tvDist μ ν = tvDist (ν.withDensity (μ.rnDeriv ν)) ν := by
    congr
    rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  rw [this, tvDist_withDensity_self_eq_integral (by fun_prop) (Measure.rnDeriv_ne_top μ ν)]

lemma tvDist_add_of_ac_of_mutuallySingular {μ' : Measure 𝓧} [IsFiniteMeasure μ']
    (hμν : μ ≪ ν) (hμ'ν : μ' ⟂ₘ ν) :
    tvDist (μ + μ') ν = tvDist μ ν + μ'.real Set.univ := by
  rw [← tvDist_restrict_add_compl hμ'ν.measurableSet_nullSet]
  simp only [Measure.restrict_add, hμ'ν.restrict_nullSet, add_zero, hμ'ν.restrict_nullSet',
    hμ'ν.restrict_compl_nullSet', hμ'ν.restrict_compl_nullSet, tvDist_zero_right]
  have hμ_eq_zero : μ.restrict hμ'ν.nullSetᶜ = 0 := by
    simp only [Measure.restrict_eq_zero]
    exact hμν (by simp)
  have hμ_eq : μ.restrict hμ'ν.nullSet = μ := by
    conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hμ'ν.measurableSet_nullSet]
    simp [hμ_eq_zero]
  simp [hμ_eq, hμ_eq_zero]

theorem tvDist_eq_integral_abs_rnDeriv :
    tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν + (μ.singularPart ν).real Set.univ := by
  have : tvDist μ ν = tvDist (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) ν := by
    simp_rw [Measure.rnDeriv_add_singularPart μ ν]
  rw [this, tvDist_add_of_ac_of_mutuallySingular
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) (μ.mutuallySingular_singularPart ν),
    tvDist_withDensity_self_eq_integral (by fun_prop) (μ.rnDeriv_ne_top ν)]

lemma tvDist_eq_integral_abs_sub {ξ : Measure 𝓧} (hμξ : μ ≪ ξ) (hνξ : ν ≪ ξ) :
    tvDist μ ν = ∫ x, |((μ.rnDeriv ξ) x).toReal - ((ν.rnDeriv ξ) x).toReal| ∂ξ := by
  calc tvDist μ ν
  _ = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν + (μ.singularPart ν).real Set.univ :=
    tvDist_eq_integral_abs_rnDeriv
  _ = ∫ x, |((μ.rnDeriv ξ) x).toReal - ((ν.rnDeriv ξ) x).toReal| ∂ξ := sorry

end Measure

end InformationTheory
