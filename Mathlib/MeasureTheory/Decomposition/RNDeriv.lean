/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

#align_import measure_theory.decomposition.lebesgue from "leanprover-community/mathlib"@"b2ff9a3d7a15fd5b0f060b135421d6a89a999c2f"

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ` and a measurable
function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `MeasureTheory.Measure.HaveLebesgueDecomposition` : A pair of measures `μ` and `ν` is said
  to `HaveLebesgueDecomposition` if there exist a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f`
* `MeasureTheory.Measure.singularPart` : If a pair of measures `HaveLebesgueDecomposition`,
  then `singularPart` chooses the measure from `HaveLebesgueDecomposition`, otherwise it
  returns the zero measure.
* `MeasureTheory.Measure.rnDeriv`: If a pair of measures
  `HaveLebesgueDecomposition`, then `rnDeriv` chooses the measurable function from
  `HaveLebesgueDecomposition`, otherwise it returns the zero function.

## Main results

* `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite` :
  the Lebesgue decomposition theorem.
* `MeasureTheory.Measure.eq_singularPart` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singularPart ν`.
* `MeasureTheory.Measure.eq_rnDeriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rnDeriv ν`.

## Tags

Lebesgue decomposition theorem
-/

open scoped MeasureTheory NNReal ENNReal

open Set

namespace MeasureTheory

namespace Measure

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/-- A pair of measures `μ` and `ν` is said to `HaveLebesgueDecomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.withDensity f`. -/
class HaveLebesgueDecomposition (μ ν : Measure α) : Prop where
  lebesgue_decomposition :
    ∃ p : Measure α × (α → ℝ≥0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2
#align measure_theory.measure.have_lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition
#align measure_theory.measure.have_lebesgue_decomposition.lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition

open Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `singularPart` chooses the
measure from `HaveLebesgueDecomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
@[pp_dot]
noncomputable irreducible_def singularPart (μ ν : Measure α) : Measure α :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).1 else 0
#align measure_theory.measure.singular_part MeasureTheory.Measure.singularPart

open Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `rnDeriv` chooses the
measurable function from `HaveLebesgueDecomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
@[pp_dot]
noncomputable irreducible_def rnDerivAux (μ ν : Measure α) : α → ℝ≥0∞ :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).2 else 0

@[pp_dot]
noncomputable irreducible_def continuousPart (μ ν : Measure α) : Measure α :=
  ν.withDensity (μ.rnDerivAux ν)

open Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `rnDeriv` chooses the
measurable function from `HaveLebesgueDecomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
@[pp_dot]
noncomputable irreducible_def rnDeriv (μ ν : Measure α) : α → ℝ≥0∞ :=
  fun a ↦ μ.rnDerivAux (μ + ν) a / ν.rnDerivAux (μ + ν) a
#align measure_theory.measure.rn_deriv MeasureTheory.Measure.rnDeriv

lemma rnDeriv_def' (μ ν : Measure α) :
    μ.rnDeriv ν = fun a ↦ μ.rnDerivAux (μ + ν) a / ν.rnDerivAux (μ + ν) a := by
  ext
  exact rnDeriv_def _ _ _

section ByDefinition

theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] :
    Measurable (μ.rnDerivAux ν) ∧
      μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPart ν + ν.withDensity (μ.rnDerivAux ν) := by
  rw [singularPart, rnDerivAux, dif_pos h, dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition
#align measure_theory.measure.have_lebesgue_decomposition_spec MeasureTheory.Measure.haveLebesgueDecomposition_spec

lemma rnDerivAux_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.rnDerivAux ν = 0 := by
  rw [rnDerivAux, dif_neg h]

lemma singularPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.singularPart ν = 0 := by
  rw [singularPart, dif_neg h]

lemma continuousPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.continuousPart ν = 0 := by
  rw [continuousPart, rnDerivAux, dif_neg h, withDensity_zero]

@[measurability]
theorem measurable_rnDerivAux (μ ν : Measure α) : Measurable <| μ.rnDerivAux ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDerivAux_of_not_haveLebesgueDecomposition h]
    exact measurable_zero
#align measure_theory.measure.measurable_rn_deriv MeasureTheory.Measure.measurable_rnDerivAux

lemma measurable_rnDeriv (μ ν : Measure α) : Measurable (μ.rnDeriv ν) := by
  rw [rnDeriv_def']
  exact (measurable_rnDerivAux _ _).div (measurable_rnDerivAux _ _)

theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart_of_not_haveLebesgueDecomposition h]
    exact MutuallySingular.zero_left
#align measure_theory.measure.mutually_singular_singular_part MeasureTheory.Measure.mutuallySingular_singularPart

lemma absolutelyContinuous_continuousPart (μ ν : Measure α) : μ.continuousPart ν ≪ ν := by
  rw [continuousPart]
  exact withDensity_absolutelyContinuous _ _

theorem haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDerivAux ν) :=
  (haveLebesgueDecomposition_spec μ ν).2.2
#align measure_theory.measure.have_lebesgue_decomposition_add MeasureTheory.Measure.haveLebesgueDecomposition_add

lemma singularPart_add_continuousPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.singularPart ν + μ.continuousPart ν = μ := by
  rw [continuousPart, ← haveLebesgueDecomposition_add]

lemma continuousPart_add_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.continuousPart ν + μ.singularPart ν = μ := by
  rw [add_comm, singularPart_add_continuousPart]

end ByDefinition

theorem todo {μ₁ μ₂ σ₁ σ₂ : Measure α} (hμ₁ : μ₁ ≪ ν) (hμ₂ : μ₂ ≪ ν)
    (hσ₁ : σ₁ ⟂ₘ ν) (hσ₂ : σ₂ ⟂ₘ ν) (h_eq : μ₁ + σ₁ = μ₂ + σ₂) :
    μ₁ = μ₂ ∧ σ₁ = σ₂ := by
  let s₁ := hσ₁.nullSet
  have hs₁ : MeasurableSet s₁ := hσ₁.measurableSet_nullSet
  let s₂ := hσ₂.nullSet
  have hs₂ : MeasurableSet s₂ := hσ₂.measurableSet_nullSet
  have h_sum (t : Set α) : μ₁ t + σ₁ t = μ₂ t + σ₂ t := by
    rw [← Measure.add_apply, ← Measure.add_apply, h_eq]
  have h_disj (t : Set α) : Disjoint (t ∩ (s₁ ∩ s₂)) (t ∩ (s₁ ∩ s₂)ᶜ) :=
    disjoint_compl_right.mono (inter_subset_right _ _) (inter_subset_right _ _)
  have hσ₁_zero (t : Set α) : σ₁ (t ∩ (s₁ ∩ s₂)) = 0 :=
    measure_mono_null (inter_subset_right _ _)
      (measure_mono_null (inter_subset_left _ _) hσ₁.measure_nullSet)
  have hσ₂_zero (t : Set α) : σ₂ (t ∩ (s₁ ∩ s₂)) = 0 :=
    measure_mono_null (inter_subset_right _ _)
      (measure_mono_null (inter_subset_right _ _) hσ₂.measure_nullSet)
  have hμ₁_zero (t : Set α) : μ₁ (t ∩ (s₁ᶜ ∪ s₂ᶜ)) = 0 :=
    measure_mono_null (inter_subset_right _ _)
      (measure_union_null (hμ₁ hσ₁.measure_compl_nullSet) (hμ₁ hσ₂.measure_compl_nullSet))
  have hμ₂_zero (t : Set α) : μ₂ (t ∩ (s₁ᶜ ∪ s₂ᶜ)) = 0 :=
    measure_mono_null (inter_subset_right _ _)
      (measure_union_null (hμ₂ hσ₁.measure_compl_nullSet) (hμ₂ hσ₂.measure_compl_nullSet))
  constructor
  · ext t ht
    rw [← inter_union_compl t (s₁ ∩ s₂), measure_union (h_disj t) (ht.inter (hs₁.inter hs₂).compl),
      measure_union (h_disj t) (ht.inter (hs₁.inter hs₂).compl)]
    congr 1
    · specialize h_sum (t ∩ (s₁ ∩ s₂))
      simpa [hσ₁_zero, hσ₂_zero] using h_sum
    · rw [compl_inter, hμ₁_zero, hμ₂_zero]
  · ext t ht
    rw [← inter_union_compl t (s₁ ∩ s₂), measure_union (h_disj t) (ht.inter (hs₁.inter hs₂).compl),
      measure_union (h_disj t) (ht.inter (hs₁.inter hs₂).compl)]
    congr 1
    · simp [hσ₁_zero, hσ₂_zero]
    · specialize h_sum (t ∩ (s₁ᶜ ∪ s₂ᶜ))
      rw [compl_inter]
      simpa [hμ₁_zero, hμ₂_zero] using h_sum

theorem todo1 {μ₁ μ₂ σ₁ σ₂ : Measure α} (hμ₁ : μ₁ ≪ ν) (hμ₂ : μ₂ ≪ ν)
    (hσ₁ : σ₁ ⟂ₘ ν) (hσ₂ : σ₂ ⟂ₘ ν) (h_eq : μ₁ + σ₁ = μ₂ + σ₂) :
    μ₁ = μ₂ := (todo hμ₁ hμ₂ hσ₁ hσ₂ h_eq).1

theorem todo2 {μ₁ μ₂ σ₁ σ₂ : Measure α} (hμ₁ : μ₁ ≪ ν) (hμ₂ : μ₂ ≪ ν)
    (hσ₁ : σ₁ ⟂ₘ ν) (hσ₂ : σ₂ ⟂ₘ ν) (h_eq : μ₁ + σ₁ = μ₂ + σ₂) :
    σ₁ = σ₂ := (todo hμ₁ hμ₂ hσ₁ hσ₂ h_eq).2

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = μ.singularPart μ`.

This theorem provides the uniqueness of the `singularPart` in the Lebesgue decomposition theorem,
while `MeasureTheory.Measure.eq_rnDeriv` provides the uniqueness of the
`rnDeriv`. -/
theorem eq_singularPart {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) :
    s = μ.singularPart ν := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  rw [add_comm] at hadd
  refine todo2 (withDensity_absolutelyContinuous ν f)
    (withDensity_absolutelyContinuous ν (μ.rnDerivAux ν)) hs (mutuallySingular_singularPart μ ν)
    (hadd.symm.trans ?_)
  have h := haveLebesgueDecomposition_add μ ν
  rwa [add_comm]
#align measure_theory.measure.eq_singular_part MeasureTheory.Measure.eq_singularPart

theorem eq_continuousPart [HaveLebesgueDecomposition μ ν] {μ₁ : Measure α}
    (h₁ : μ₁ ≪ ν) (hadd : μ = μ₁ + μ.singularPart ν) :
    μ₁ = μ.continuousPart ν :=
  todo1 h₁ (absolutelyContinuous_continuousPart _ _) (mutuallySingular_singularPart μ ν)
    (mutuallySingular_singularPart μ ν) ((continuousPart_add_singularPart _ _).trans hadd).symm

instance haveLebesgueDecompositionAdd (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    HaveLebesgueDecomposition (μ₁ + μ₂) ν := by
  refine ⟨⟨μ₁.singularPart ν + μ₂.singularPart ν, μ₁.rnDerivAux ν + μ₂.rnDerivAux ν⟩, ?_, ?_, ?_⟩
  · exact (measurable_rnDerivAux _ _).add (measurable_rnDerivAux _ _)
  · exact (mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)
  · conv_lhs => rw [haveLebesgueDecomposition_add μ₁ ν, haveLebesgueDecomposition_add μ₂ ν]
    simp only
    simp_rw [add_assoc]
    congr 1
    rw [← add_assoc, add_comm _ (μ₂.singularPart ν), add_assoc]
    congr 1
    rw [withDensity_add_left (measurable_rnDerivAux _ _)]

theorem singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + μ₂.singularPart ν := by
  refine (eq_singularPart ((measurable_rnDerivAux μ₁ ν).add (measurable_rnDerivAux μ₂ ν))
    ((mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)) ?_).symm
  erw [withDensity_add_left (measurable_rnDerivAux μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← add_assoc, ← add_assoc]
  rw [← haveLebesgueDecomposition_add μ₁ ν, add_assoc, add_comm (ν.withDensity (μ₂.rnDerivAux ν)),
    ← haveLebesgueDecomposition_add μ₂ ν]
#align measure_theory.measure.singular_part_add MeasureTheory.Measure.singularPart_add

lemma continuousPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).continuousPart ν = μ₁.continuousPart ν + μ₂.continuousPart ν := by
  refine (eq_continuousPart ?_ ?_).symm
  · rw [AbsolutelyContinuous.add_left_iff]
    exact ⟨absolutelyContinuous_continuousPart _ _, absolutelyContinuous_continuousPart _ _⟩
  · conv_lhs => rw [haveLebesgueDecomposition_add μ₁ ν, haveLebesgueDecomposition_add μ₂ ν]
    rw [singularPart_add]
    simp_rw [← add_assoc]
    have (a b c d : Measure α) : a + b + c + d = b + d + a + c := by abel
    rw [this]
    congr <;> rw [continuousPart]

theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ
#align measure_theory.measure.singular_part_le MeasureTheory.Measure.singularPart_le

lemma singularPart_eq_zero_of_ac (h : μ ≪ ν) : μ.singularPart ν = 0 := by
  rw [← MutuallySingular.self_iff]
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart _ _)
    AbsolutelyContinuous.rfl ((absolutelyContinuous_of_le (singularPart_le _ _)).trans h)

@[simp]
theorem singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (AbsolutelyContinuous.zero _)
#align measure_theory.measure.singular_part_zero MeasureTheory.Measure.singularPart_zero

lemma singularPart_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.singularPart ν = 0 ↔ μ ≪ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, singularPart_eq_zero_of_ac⟩
  rw [h, zero_add] at h_dec
  rw [h_dec]
  exact withDensity_absolutelyContinuous ν _

lemma withDensity_rnDerivAux_of_ac (hμν : μ ≪ ν) [HaveLebesgueDecomposition μ ν] :
    ν.withDensity (μ.rnDerivAux ν) = μ := by
  conv_rhs => rw [haveLebesgueDecomposition_add μ ν, singularPart_eq_zero_of_ac hμν, zero_add]

def rnDerivZeroSet (μ ν : Measure α) : Set α := {x | μ.rnDerivAux (μ + ν) x = 0}

lemma measurableSet_rnDerivZeroSet (μ ν : Measure α) : MeasurableSet (rnDerivZeroSet μ ν) :=
  measurable_rnDerivAux _ _ (measurableSet_singleton 0)

def rnDerivTopSet (μ ν : Measure α) : Set α := {x | μ.rnDerivAux (μ + ν) x = ∞}

lemma measurableSet_rnDerivTopSet (μ ν : Measure α) : MeasurableSet (rnDerivTopSet μ ν) :=
  measurable_rnDerivAux _ _ (measurableSet_singleton ∞)

lemma measure_eq_zero_or_top_of_subset_rnDerivTopSet [HaveLebesgueDecomposition μ (μ + ν)]
    {t : Set α} (ht : MeasurableSet t) (ht_subset : t ⊆ rnDerivTopSet μ ν) :
    μ t = 0 ∨ μ t = ∞ := by
  have hν_ac : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  rw [← withDensity_rnDerivAux_of_ac hν_ac, withDensity_apply _ ht]
  have : ∫⁻ a in t, μ.rnDerivAux (μ + ν) a ∂(μ + ν) = ∫⁻ _ in t, ∞ ∂(μ + ν) :=
    set_lintegral_congr_fun ht (ae_of_all _ (fun x hx ↦ ht_subset hx))
  rw [this]
  simp only [lintegral_const, MeasurableSet.univ, restrict_apply, univ_inter,
    mul_eq_zero, ENNReal.top_ne_zero, add_eq_zero, false_or]
  by_cases h : (μ + ν) t = 0
  · exact Or.inl h
  · exact Or.inr <| ENNReal.top_mul h

noncomputable
def rnDerivAddAux (μ ν : Measure α) : α → ℝ≥0∞ :=
  fun x ↦ if ν.rnDerivAux (μ + ν) x = ∞ then 1 else ν.rnDerivAux (μ + ν) x

lemma goal {t : Set α} (ht : MeasurableSet t) [HaveLebesgueDecomposition ν (μ + ν)] :
    ∫⁻ x in t, rnDerivAddAux μ ν x ∂(μ + ν) = ∫⁻ x in t, ν.rnDerivAux (μ + ν) x ∂(μ + ν) := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  let s := {x | ν.rnDerivAux (μ + ν) x = ∞}
  have hs : MeasurableSet s := measurable_rnDerivAux _ _ (measurableSet_singleton _)
  have h_zero_top (t : Set α) (ht : MeasurableSet t) : ν (t ∩ s) = 0 ∨ ν (t ∩ s) = ∞ := by
    rw [← withDensity_rnDerivAux_of_ac hν_ac, withDensity_apply _ (ht.inter hs)]
    have : ∫⁻ a in t ∩ s, ν.rnDerivAux (μ + ν) a ∂(μ + ν) = ∫⁻ a in t ∩ s, ∞ ∂(μ + ν) :=
      set_lintegral_congr_fun (ht.inter hs) (ae_of_all _ (fun x hx ↦ hx.2))
    rw [this]
    simp only [lintegral_const, MeasurableSet.univ, restrict_apply, univ_inter,
      mul_eq_zero, ENNReal.top_ne_zero, add_eq_zero, false_or]
    by_cases h : (μ + ν) (t ∩ s) = 0
    · exact Or.inl h
    · exact Or.inr <| ENNReal.top_mul h
  have : ∫⁻ x in t, rnDerivAddAux μ ν x ∂(μ + ν)
      = ∫⁻ x in t ∩ s, 1 ∂(μ + ν)
        + ∫⁻ x in t ∩ sᶜ, ν.rnDerivAux (μ + ν) x ∂(μ + ν) := by
    sorry
  rw [this]
  have : ∫⁻ x in t, ν.rnDerivAux (μ + ν) x ∂(μ + ν)
      = ∫⁻ x in t ∩ s, ∞ ∂(μ + ν)
        + ∫⁻ x in t ∩ sᶜ, ν.rnDerivAux (μ + ν) x ∂(μ + ν) := by
    sorry
  rw [this]
  rw [lintegral_one, lintegral_const, restrict_apply MeasurableSet.univ, univ_inter]
  sorry

lemma goal' :
    (μ + ν).withDensity (rnDerivAddAux μ ν) = (μ + ν).withDensity (ν.rnDerivAux (μ + ν)) := by
  ext t ht
  rw [withDensity_apply _ ht, withDensity_apply _ ht, goal ht]

lemma measure_singularPartSet (μ ν : Measure α) [HaveLebesgueDecomposition ν (μ + ν)] :
    ν (singularPartSet μ ν) = 0 := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h : ν = (μ + ν).withDensity (ν.rnDerivAux (μ + ν)) :=
    (withDensity_rnDerivAux_of_ac hν_ac).symm
  suffices (μ + ν).withDensity (ν.rnDerivAux (μ + ν)) (singularPartSet μ ν) = 0 by
    rwa [← h] at this
  rw [withDensity_apply _ (measurableSet_singularPartSet _ _),
    lintegral_eq_zero_iff (measurable_rnDerivAux _ _)]
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_singularPartSet _ _)]
  exact ae_of_all _ (fun _ h ↦ h)

lemma measure_inter_compl_singularPartSet' (μ ν : Measure α)
    [HaveLebesgueDecomposition μ (μ + ν)] [HaveLebesgueDecomposition ν (μ + ν)]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, μ.rnDeriv ν x ∂ν := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet _ _
  have hμ_ac : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have hμ_eq : μ = (μ + ν).withDensity (μ.rnDerivAux (μ + ν)) :=
    (withDensity_rnDerivAux_of_ac hμ_ac).symm
  have hν_eq : ν = (μ + ν).withDensity (ν.rnDerivAux (μ + ν)) :=
    (withDensity_rnDerivAux_of_ac hν_ac).symm
  have : μ (t ∩ sᶜ) = (μ + ν).withDensity (μ.rnDerivAux (μ + ν)) (t ∩ sᶜ) := by rw [← hμ_eq]
  rw [this, withDensity_apply _ (ht.inter hs.compl)]
  have : ∫⁻ x in t ∩ sᶜ, μ.rnDeriv ν x ∂ν
      = ∫⁻ x in t ∩ sᶜ, μ.rnDeriv ν x ∂(μ + ν).withDensity (ν.rnDerivAux (μ + ν)) := by congr
  rw [this, set_lintegral_withDensity_eq_set_lintegral_mul _ (measurable_rnDerivAux _ _)
    (measurable_rnDeriv _ _) (ht.inter hs.compl)]
  by_cases h_top : ∀ᵐ x ∂(μ + ν), ν.rnDerivAux (μ + ν) x < ∞
  · refine set_lintegral_congr_fun (ht.inter hs.compl) ?_
    filter_upwards [h_top] with x hx_top hx
    simp only [rnDeriv_def', Pi.mul_apply]
    rw [div_eq_mul_inv, mul_comm, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
    · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, s] at hx
      exact hx.2
    · exact hx_top.ne
  · sorry

lemma measure_inter_compl_singularPartSet (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
  rw [measure_inter_compl_singularPartSet' _ _ ht]
  symm
  calc ∫⁻ x in t, rnDeriv μ ν x ∂ν
    = ∫⁻ x in (singularPartSet μ ν) ∩ t, rnDeriv μ ν x ∂ν
      + ∫⁻ x in (singularPartSet μ ν)ᶜ ∩ t, rnDeriv μ ν x ∂ν := by
        rw [← restrict_restrict (measurableSet_singularPartSet _ _),
          ← restrict_restrict (measurableSet_singularPartSet _ _).compl,
          lintegral_add_compl _ (measurableSet_singularPartSet _ _)]
  _ = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, rnDeriv μ ν x ∂ν := by
        rw [set_lintegral_measure_zero _ _ (measure_mono_null (Set.inter_subset_left _ _) ?_),
          Set.inter_comm, zero_add]
        exact measure_singularPartSet _ _

lemma restrict_compl_singularPartSet_eq_withDensity
    (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.restrict (singularPartSet μ ν)ᶜ = ν.withDensity (μ.rnDeriv ν) := by
  ext t ht
  rw [restrict_apply ht, measure_inter_compl_singularPartSet μ ν ht, withDensity_apply _ ht]

lemma mutuallySingular_restrict_singularPartSet (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.restrict (singularPartSet μ ν) ⟂ₘ ν := by
  refine ⟨(singularPartSet μ ν)ᶜ, (measurableSet_singularPartSet _ _).compl, ?_, ?_⟩
  · rw [restrict_apply (measurableSet_singularPartSet _ _).compl, compl_inter_self, measure_empty]
  · rw [compl_compl, measure_singularPartSet μ ν]

lemma restrict_compl_singularPartSet (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.restrict (singularPartSet μ ν)ᶜ = μ.continuousPart ν := by
  rw [restrict_compl_singularPartSet_eq_withDensity]
  refine todo1 (withDensity_absolutelyContinuous ν (μ.rnDeriv ν))
    (absolutelyContinuous_continuousPart μ ν) (mutuallySingular_restrict_singularPartSet μ ν)
    (mutuallySingular_singularPart μ ν) ?_
  rw [← restrict_compl_singularPartSet_eq_withDensity, add_comm,
    restrict_add_restrict_compl (measurableSet_singularPartSet _ _),
    continuousPart_add_singularPart]

lemma restrict_singularPartSet (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.restrict (singularPartSet μ ν) = μ.singularPart ν := by
  refine eq_singularPart (measurable_rnDerivAux μ ν) ?_ ?_
  · exact mutuallySingular_restrict_singularPartSet μ ν
  · conv_lhs => rw [← restrict_add_restrict_compl (μ := μ) (measurableSet_singularPartSet μ ν),
      restrict_compl_singularPartSet, continuousPart]

lemma withDensity_rnDeriv_eq_continuousPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    ν.withDensity (μ.rnDeriv ν) = μ.continuousPart ν := by
  rw [← restrict_compl_singularPartSet, restrict_compl_singularPartSet_eq_withDensity]












lemma singularPart_add_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) = μ := (haveLebesgueDecomposition_add μ ν).symm

lemma rnDeriv_add_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν = μ := by rw [add_comm, singularPart_add_rnDeriv]

section HaveLebesgueDecomposition

instance instHaveLebesgueDecompositionZeroLeft : HaveLebesgueDecomposition 0 ν where
  lebesgue_decomposition := ⟨⟨0, 0⟩, measurable_zero, MutuallySingular.zero_left, by simp⟩

instance instHaveLebesgueDecompositionZeroRight : HaveLebesgueDecomposition μ 0 where
  lebesgue_decomposition := ⟨⟨μ, 0⟩, measurable_zero, MutuallySingular.zero_right, by simp⟩

instance instHaveLebesgueDecompositionSelf : HaveLebesgueDecomposition μ μ where
  lebesgue_decomposition := ⟨⟨0, 1⟩, measurable_const, MutuallySingular.zero_left, by simp⟩

instance haveLebesgueDecompositionSmul' (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0∞) : (r • μ).HaveLebesgueDecomposition ν where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, hmeas.const_smul _, hsing.smul _, ?_⟩
    simp only [ENNReal.smul_def]
    rw [withDensity_smul _ hmeas, ← smul_add, ← hadd]

instance haveLebesgueDecompositionSmul (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) : (r • μ).HaveLebesgueDecomposition ν := by
  rw [ENNReal.smul_def]; infer_instance
#align measure_theory.measure.have_lebesgue_decomposition_smul MeasureTheory.Measure.haveLebesgueDecompositionSmul

instance haveLebesgueDecompositionSmulRight (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) :
    μ.HaveLebesgueDecomposition (r • ν) where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, hmeas.const_smul _,
      hsing.mono_ac AbsolutelyContinuous.rfl smul_absolutelyContinuous, ?_⟩
    have : r⁻¹ • rnDeriv μ ν = ((r⁻¹ : ℝ≥0) : ℝ≥0∞) • rnDeriv μ ν := by simp [ENNReal.smul_def]
    rw [this, withDensity_smul _ hmeas, ENNReal.smul_def r, withDensity_smul_measure,
      ← smul_assoc, smul_eq_mul, ENNReal.coe_inv hr, ENNReal.inv_mul_cancel, one_smul]
    · exact hadd
    · simp [hr]
    · exact ENNReal.coe_ne_top

theorem haveLebesgueDecomposition_withDensity (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).HaveLebesgueDecomposition μ := ⟨⟨⟨0, f⟩, hf, .zero_left, (zero_add _).symm⟩⟩

instance haveLebesgueDecompositionRnDeriv (μ ν : Measure α) :
    HaveLebesgueDecomposition (ν.withDensity (μ.rnDeriv ν)) ν :=
  haveLebesgueDecomposition_withDensity ν (measurable_rnDeriv _ _)

instance instHaveLebesgueDecompositionSingularPart :
    HaveLebesgueDecomposition (μ.singularPart ν) ν :=
  ⟨⟨μ.singularPart ν, 0⟩, measurable_zero, mutuallySingular_singularPart μ ν, by simp⟩

end HaveLebesgueDecomposition

theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ
#align measure_theory.measure.with_density_rn_deriv_le MeasureTheory.Measure.withDensity_rnDeriv_le

lemma _root_.AEMeasurable.singularPart {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (μ.singularPart ν) :=
  AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

lemma _root_.AEMeasurable.withDensity_rnDeriv {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (ν.withDensity (μ.rnDeriv ν)) :=
  AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

lemma MutuallySingular.singularPart (h : μ ⟂ₘ ν) (ν' : Measure α) :
    μ.singularPart ν' ⟂ₘ ν :=
  h.mono (singularPart_le μ ν') le_rfl

lemma absolutelyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
    μ ≪ μ.withDensity (ν.rnDeriv μ) := by
  rw [haveLebesgueDecomposition_add ν μ] at hμν
  refine AbsolutelyContinuous.mk (fun s _ hνs ↦ ?_)
  obtain ⟨t, _, ht1, ht2⟩ := mutuallySingular_singularPart ν μ
  rw [← inter_union_compl s]
  refine le_antisymm ((measure_union_le (s ∩ t) (s ∩ tᶜ)).trans ?_) (zero_le _)
  simp only [nonpos_iff_eq_zero, add_eq_zero]
  constructor
  · refine hμν ?_
    simp only [add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply, add_eq_zero]
    constructor
    · exact measure_mono_null (Set.inter_subset_right _ _) ht1
    · exact measure_mono_null (Set.inter_subset_left _ _) hνs
  · exact measure_mono_null (Set.inter_subset_right _ _) ht2

@[simp]
lemma withDensity_rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    ν.withDensity (μ.rnDeriv ν) = 0 ↔ μ ⟂ₘ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero] at h_dec
    rw [h_dec]
    exact mutuallySingular_singularPart μ ν
  · rw [← MutuallySingular.self_iff]
    rw [h_dec, MutuallySingular.add_left_iff] at h
    refine MutuallySingular.mono_ac h.2 AbsolutelyContinuous.rfl ?_
    exact withDensity_absolutelyContinuous _ _

@[simp]
lemma rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν := by
  rw [← withDensity_rnDeriv_eq_zero, withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]

lemma rnDeriv_zero (ν : Measure α) : (0 : Measure α).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact MutuallySingular.zero_left

lemma MutuallySingular.rnDeriv_ae_eq_zero (hμν : μ ⟂ₘ ν) :
    μ.rnDeriv ν =ᵐ[ν] 0 := by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

@[simp]
theorem singularPart_withDensity (ν : Measure α) (f : α → ℝ≥0∞) :
    (ν.withDensity f).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (withDensity_absolutelyContinuous _ _)
#align measure_theory.measure.singular_part_with_density MeasureTheory.Measure.singularPart_withDensity

lemma rnDeriv_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact mutuallySingular_singularPart μ ν

@[simp]
lemma singularPart_self (μ : Measure α) : μ.singularPart μ = 0 :=
  singularPart_eq_zero_of_ac Measure.AbsolutelyContinuous.rfl

lemma rnDeriv_self (μ : Measure α) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ ↦ 1 := by
  have h := rnDeriv_add_singularPart μ μ
  rw [singularPart_self, add_zero] at h
  have h_one : μ = μ.withDensity 1 := by simp
  conv_rhs at h => rw [h_one]
  rwa [withDensity_eq_iff_of_sigmaFinite (measurable_rnDeriv _ _).aemeasurable] at h
  exact aemeasurable_const

lemma singularPart_eq_self [μ.HaveLebesgueDecomposition ν] : μ.singularPart ν = μ ↔ μ ⟂ₘ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, fun  h ↦ ?_⟩
  · rw [← h]
    exact mutuallySingular_singularPart _ _
  · conv_rhs => rw [h_dec]
    rw [(withDensity_rnDeriv_eq_zero _ _).mpr h, add_zero]

@[simp]
lemma singularPart_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).singularPart ν = μ.singularPart ν := by
  rw [Measure.singularPart_eq_self]
  exact Measure.mutuallySingular_singularPart _ _

instance singularPart.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.singularPart ν) :=
  isFiniteMeasure_of_le μ <| singularPart_le μ ν
#align measure_theory.measure.singular_part.measure_theory.is_finite_measure MeasureTheory.Measure.singularPart.instIsFiniteMeasure

instance singularPart.instSigmaFinite [SigmaFinite μ] : SigmaFinite (μ.singularPart ν) :=
  sigmaFinite_of_le μ <| singularPart_le μ ν
#align measure_theory.measure.singular_part.measure_theory.sigma_finite MeasureTheory.Measure.singularPart.instSigmaFinite

instance singularPart.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.singularPart ν) :=
  isLocallyFiniteMeasure_of_le <| singularPart_le μ ν
#align measure_theory.measure.singular_part.measure_theory.is_locally_finite_measure MeasureTheory.Measure.singularPart.instIsLocallyFiniteMeasure

instance withDensity.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isFiniteMeasure_of_le μ <| withDensity_rnDeriv_le μ ν
#align measure_theory.measure.with_density.measure_theory.is_finite_measure MeasureTheory.Measure.withDensity.instIsFiniteMeasure

instance withDensity.instSigmaFinite [SigmaFinite μ] :
    SigmaFinite (ν.withDensity <| μ.rnDeriv ν) :=
  sigmaFinite_of_le μ <| withDensity_rnDeriv_le μ ν
#align measure_theory.measure.with_density.measure_theory.sigma_finite MeasureTheory.Measure.withDensity.instSigmaFinite

instance withDensity.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isLocallyFiniteMeasure_of_le <| withDensity_rnDeriv_le μ ν
#align measure_theory.measure.with_density.measure_theory.is_locally_finite_measure MeasureTheory.Measure.withDensity.instIsLocallyFiniteMeasure

section RNDerivFinite

theorem lintegral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs : μ s ≠ ∞) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · suffices (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞ from
      lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    calc
      _ ≤ (singularPart μ ν) (toMeasurable μ s) + _ := le_add_self
      _ = μ s := by rw [← Measure.add_apply, ← haveLebesgueDecomposition_add, measure_toMeasurable]
      _ < ⊤ := hs.lt_top
  · simp only [Measure.rnDeriv, dif_neg hl, Pi.zero_apply, lintegral_zero, ENNReal.zero_lt_top]
#align measure_theory.measure.lintegral_rn_deriv_lt_top_of_measure_ne_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top

theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞ := by
  rw [← set_lintegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne
#align measure_theory.measure.lintegral_rn_deriv_lt_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top

lemma integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

/-- The Radon-Nikodym derivative of a sigma-finite measure `μ` with respect to another
measure `ν` is `ν`-almost everywhere finite. -/
theorem rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x < ∞ := by
  suffices ∀ n, ∀ᵐ x ∂ν, x ∈ spanningSets μ n → μ.rnDeriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
  intro n
  rw [← ae_restrict_iff' (measurable_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (lintegral_rnDeriv_lt_top_of_measure_ne_top _ ?_).ne
  exact (measure_spanningSets_lt_top _ _).ne
#align measure_theory.measure.rn_deriv_lt_top MeasureTheory.Measure.rnDeriv_lt_top

lemma rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

end RNDerivFinite

theorem singularPart_smul (μ ν : Measure α) (r : ℝ≥0) :
    (r • μ).singularPart ν = r • μ.singularPart ν := by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : ℝ≥0∞))
          (MutuallySingular.smul r (mutuallySingular_singularPart _ _)) ?_).symm
    rw [withDensity_smul _ (measurable_rnDeriv _ _), ← smul_add,
      ← haveLebesgueDecomposition_add μ ν, ENNReal.smul_def]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg, smul_zero]
    refine fun hl' ↦ hl ?_
    rw [← inv_smul_smul₀ hr μ]
    infer_instance
#align measure_theory.measure.singular_part_smul MeasureTheory.Measure.singularPart_smul

theorem singularPart_smul_right (μ ν : Measure α) (r : ℝ≥0) (hr : r ≠ 0) :
    μ.singularPart (r • ν) = μ.singularPart ν := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · exact (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl
        smul_absolutelyContinuous
    · rw [ENNReal.smul_def r, withDensity_smul_measure, ← withDensity_smul]
      swap; · exact (measurable_rnDeriv _ _).const_smul _
      convert haveLebesgueDecomposition_add μ ν
      ext x
      simp only [Pi.smul_apply]
      rw [← ENNReal.smul_def, smul_inv_smul₀ hr]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg]
    refine fun hl' ↦ hl ?_
    rw [← inv_smul_smul₀ hr ν]
    infer_instance

lemma singularPart_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).singularPart ν = (μ.singularPart ν).restrict s := by
  refine (Measure.eq_singularPart (f := s.indicator (μ.rnDeriv ν)) ?_ ?_ ?_).symm
  · exact (μ.measurable_rnDeriv ν).indicator hs
  · exact (Measure.mutuallySingular_singularPart μ ν).restrict s
  · ext t
    rw [withDensity_indicator hs, ← restrict_withDensity hs, ← Measure.restrict_add,
      ← μ.haveLebesgueDecomposition_add ν]

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the measures, while the uniqueness in
terms of the functions is given in `eq_rnDeriv`. -/
theorem eq_withDensity_rnDeriv {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃, hS₃, add_zero]
  have heq :
    (ν.withDensity f).restrict (S ∩ T) = (ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) := by
    ext1 A hA
    have hs : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_left _ _))
    have hsing : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hT₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_right _ _))
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hs, ←
      add_apply, add_comm, ← hadd, add_apply, hsing, zero_add]
  have heq' :
    ∀ A : Set α, MeasurableSet A → ν.withDensity f A = (ν.withDensity f).restrict (S ∩ T) A := by
    intro A hA
    have hνfinter : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact withDensity_absolutelyContinuous ν f hνinter ▸ measure_mono (inter_subset_right _ _)
    rw [restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hνfinter, ← diff_eq,
      measure_inter_add_diff _ (hS₁.inter hT₁)]
  ext1 A hA
  have hνrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact
      withDensity_absolutelyContinuous ν (μ.rnDeriv ν) hνinter ▸
        measure_mono (inter_subset_right _ _)
  rw [heq' A hA, heq, ← add_zero ((ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) A), ← hνrn,
    restrict_apply hA, ← diff_eq, measure_inter_add_diff _ (hS₁.inter hT₁)]
#align measure_theory.measure.eq_with_density_rn_deriv MeasureTheory.Measure.eq_withDensity_rnDeriv

theorem eq_withDensity_rnDeriv₀ {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd

theorem eq_rnDeriv₀ [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν :=
  (withDensity_eq_iff_of_sigmaFinite hf (measurable_rnDeriv _ _).aemeasurable).mp
    (eq_withDensity_rnDeriv₀ hf hs hadd)

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the functions, while the uniqueness in
terms of the functions is given in `eq_withDensity_rnDeriv`. -/
theorem eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν :=
  eq_rnDeriv₀ hf.aemeasurable hs hadd
#align measure_theory.measure.eq_rn_deriv MeasureTheory.Measure.eq_rnDeriv

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
theorem rnDeriv_withDensity₀ (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  have : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv₀ hf MutuallySingular.zero_left this).symm

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  rnDeriv_withDensity₀ ν hf.aemeasurable
#align measure_theory.measure.rn_deriv_with_density MeasureTheory.Measure.rnDeriv_withDensity

lemma rnDeriv_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv ν =ᵐ[ν] s.indicator (μ.rnDeriv ν) := by
  refine (eq_rnDeriv (s := (μ.restrict s).singularPart ν)
    ((measurable_rnDeriv _ _).indicator hs) (mutuallySingular_singularPart _ _) ?_).symm
  rw [singularPart_restrict _ _ hs, withDensity_indicator hs, ← restrict_withDensity hs,
    ← Measure.restrict_add, ← μ.haveLebesgueDecomposition_add ν]

/-- The Radon-Nikodym derivative of the restriction of a measure to a measurable set is the
indicator function of this set. -/
theorem rnDeriv_restrict_self (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1 := by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)
#align measure_theory.measure.rn_deriv_restrict MeasureTheory.Measure.rnDeriv_restrict_self

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_left (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] (r : ℝ≥0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ, singularPart_smul, ← smul_add,
      ← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top (r • ν) μ).ne

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_left_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_right (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0} (hr : r ≠ 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff]
  rotate_left
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top ν _).ne
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ), singularPart_smul_right _ _ _ hr,
      ENNReal.smul_def r, withDensity_smul_measure, ← ENNReal.smul_def, ← smul_assoc,
      smul_eq_mul, inv_mul_cancel hr, one_smul]
    exact ν.haveLebesgueDecomposition_add μ

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_right_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ 0) (hr_ne_top : r ≠ ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right ν μ ?_
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNReal.smul_def, ne_eq, smul_eq_mul]
    rw [ENNReal.coe_inv, ENNReal.coe_toNNReal hr_ne_top]
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  simp_rw [this, ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top] at h
  exact h

/-- Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add'`, which requires sigma-finite `ν₁`, `ν₂` and `μ`. -/
lemma rnDeriv_add (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    [(ν₁ + ν₂).HaveLebesgueDecomposition μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ, singularPart_add,
      withDensity_add_left (measurable_rnDeriv _ _), add_assoc,
      add_comm (ν₂.singularPart μ), add_assoc, add_comm _ (ν₂.singularPart μ),
      ← ν₂.haveLebesgueDecomposition_add μ, ← add_assoc, ← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable
  · exact (lintegral_rnDeriv_lt_top (ν₁ + ν₂) μ).ne

end Measure

end MeasureTheory
