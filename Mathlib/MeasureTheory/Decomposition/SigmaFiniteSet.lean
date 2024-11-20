/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.Exhaustion

/-!
# Method of exhaustion

If `μ, ν` are two measures with `ν` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT ν` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ`, either `ν t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `ν` is not s-finite), we define
  `μ.sigmaFiniteSetWRT ν = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `ν`, for all sets `s`
  in `(sigmaFiniteSetWRT μ ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ ν)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ ν` and `ν` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

open Classical in
/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and for all
measurable sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`. -/
def Measure.sigmaFiniteSetWRT (μ ν : Measure α) : Set α :=
  if h : ∃ s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (∀ t, t ⊆ sᶜ → ν t ≠ 0 → μ t = ∞)
  then h.choose
  else ∅

@[measurability]
lemma measurableSet_sigmaFiniteSetWRT : MeasurableSet (μ.sigmaFiniteSetWRT ν) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty

instance : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT ν)) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [Measure.restrict_empty]
    infer_instance

section IsFiniteMeasure

/-! We prove that the condition in the definition of `sigmaFiniteSetWRT` is true for finite
measures. Since every s-finite measure is absolutely continuous with respect to a finite measure,
the condition will then also be true for s-finite measures. -/

/-- A measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT' ν)` is sigma-finite and
`ν (μ.sigmaFiniteSetWRT' ν)` has maximal measure among such sets. -/
def Measure.sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : Set α :=
  ν.maximalSet (fun s ↦ SigmaFinite (μ.restrict s)) (by simp only [restrict_empty]; infer_instance)

lemma measurableSet_sigmaFiniteSetWRT' [IsFiniteMeasure ν] :
    MeasurableSet (μ.sigmaFiniteSetWRT' ν) :=
  measurableSet_maximalSet _ (by simp only [Measure.restrict_empty]; infer_instance)

lemma sigmaFinite_restrict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν)) := by
  refine prop_maximalSet ν (fun s ↦ SigmaFinite (μ.restrict s))
    (by simp only [Measure.restrict_empty]; infer_instance) ?_
  simp only
  exact fun t ht _ ↦ sigmaFinite_iUnion μ (MeasurableSet.iUnion ht)

/-- `μ.sigmaFiniteSetWRT' ν` has maximal `ν`-measure among all measurable sets `s` with sigma-finite
`μ.restrict s`. -/
lemma measure_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    ν (μ.sigmaFiniteSetWRT' ν)
      = ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  refine measure_maximalSet ν (fun s ↦ SigmaFinite (μ.restrict s))
    (by simp only [Measure.restrict_empty]; infer_instance) ?_
  simp only
  exact fun t ht _ ↦ sigmaFinite_iUnion μ (MeasurableSet.iUnion ht)

/-- Auxiliary lemma for `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'`. -/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet [IsFiniteMeasure ν]
    (hs : MeasurableSet s) (hs_subset : s ⊆ (μ.sigmaFiniteSetWRT' ν)ᶜ) (hνs : ν s ≠ 0) :
    μ s = ∞ := by
  have : ¬ SigmaFinite (μ.restrict s) := by
    refine not_prop_of_subset_compl_maximalSet ν (fun s ↦ SigmaFinite (μ.restrict s))
      (by simp only [Measure.restrict_empty]; infer_instance) ?_ hs hs_subset hνs
    simp only
    exact fun t ht _ ↦ sigmaFinite_iUnion μ (MeasurableSet.iUnion ht)
  by_contra h
  have h_lt_top : Fact (μ s < ∞) := ⟨Ne.lt_top h⟩
  exact this inferInstance

/-- For all sets `s` in `(μ.sigmaFiniteSetWRT ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`. -/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT' [IsFiniteMeasure ν]
    (hs_subset : s ⊆ (μ.sigmaFiniteSetWRT' ν)ᶜ) (hνs : ν s ≠ 0) :
    μ s = ∞ := by
  rw [measure_eq_iInf]
  simp_rw [iInf_eq_top]
  suffices ∀ t, t ⊆ (μ.sigmaFiniteSetWRT' ν)ᶜ → s ⊆ t → MeasurableSet t → μ t = ∞ by
    intro t hts ht
    suffices μ (t ∩ (μ.sigmaFiniteSetWRT' ν)ᶜ) = ∞ from
      measure_mono_top Set.inter_subset_left this
    have hs_subset_t : s ⊆ t ∩ (μ.sigmaFiniteSetWRT' ν)ᶜ := Set.subset_inter hts hs_subset
    exact this (t ∩ (μ.sigmaFiniteSetWRT' ν)ᶜ) Set.inter_subset_right hs_subset_t
      (ht.inter measurableSet_sigmaFiniteSetWRT'.compl)
  intro t ht_subset hst ht
  refine measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet ht ht_subset ?_
  exact fun hνt ↦ hνs (measure_mono_null hst hνt)

end IsFiniteMeasure

section SFinite

/-- For all sets `s` in `(μ.sigmaFiniteSetWRT ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`. -/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν]
    (hs_subset : s ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s ≠ 0) :
    μ s = ∞ := by
  have ⟨ν', hν', hνν', _⟩ := exists_isFiniteMeasure_absolutelyContinuous ν
  have h : ∃ s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
      ∧ (∀ t ⊆ sᶜ, ν t ≠ 0 → μ t = ∞) := by
    refine ⟨μ.sigmaFiniteSetWRT' ν', measurableSet_sigmaFiniteSetWRT',
      sigmaFinite_restrict_sigmaFiniteSetWRT' _ _,
      fun t ht_subset hνt ↦ measure_eq_top_of_subset_compl_sigmaFiniteSetWRT' ht_subset ?_⟩
    exact fun hν't ↦ hνt (hνν' hν't)
  rw [Measure.sigmaFiniteSetWRT, dif_pos h] at hs_subset
  exact h.choose_spec.2.2 s hs_subset hνs

lemma restrict_compl_sigmaFiniteSetWRT [SFinite ν] (hμν : μ ≪ ν) :
    μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ := by
  ext s
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]
  by_cases hνs : ν (s ∩ (μ.sigmaFiniteSetWRT ν)ᶜ) = 0
  · rw [hνs, mul_zero]
    exact hμν hνs
  · rw [ENNReal.top_mul hνs, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hνs]

end SFinite

@[simp]
lemma measure_compl_sigmaFiniteSetWRT (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν] :
    ν (μ.sigmaFiniteSetWRT ν)ᶜ = 0 := by
  have h : ν (μ.sigmaFiniteSetWRT ν)ᶜ ≠ 0 → μ (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT subset_rfl
  by_contra h0
  refine ENNReal.top_ne_zero ?_
  rw [← h h0, ← Measure.iSup_restrict_spanningSets]
  simp_rw [Measure.restrict_apply' (measurableSet_spanningSets μ _), ENNReal.iSup_eq_zero]
  intro i
  by_contra h_ne_zero
  have h_zero_top := measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
    (Set.inter_subset_left : (μ.sigmaFiniteSetWRT ν)ᶜ ∩ spanningSets μ i ⊆ _) ?_
  swap; · exact fun h ↦ h_ne_zero (hμν h)
  refine absurd h_zero_top (ne_of_lt ?_)
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ i)

section SigmaFiniteSet

/-- A measurable set such that `μ.restrict μ.sigmaFiniteSet` is sigma-finite,
  and for all measurable sets `s ⊆ μ.sigmaFiniteSetᶜ`, either `μ s = 0` or `μ s = ∞`. -/
def Measure.sigmaFiniteSet (μ : Measure α) : Set α := μ.sigmaFiniteSetWRT μ

@[measurability]
lemma measurableSet_sigmaFiniteSet : MeasurableSet μ.sigmaFiniteSet :=
  measurableSet_sigmaFiniteSetWRT

lemma measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ]
    (ht_subset : t ⊆ μ.sigmaFiniteSetᶜ) :
    μ t = 0 ∨ μ t = ∞ := by
  rw [or_iff_not_imp_left]
  exact measure_eq_top_of_subset_compl_sigmaFiniteSetWRT ht_subset

/-- The measure `μ.restrict μ.sigmaFiniteSetᶜ` takes only two values: 0 and ∞ . -/
lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s = ∞ := by
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSet.compl]
  exact measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet Set.inter_subset_right

/-- The restriction of an s-finite measure `μ` to `μ.sigmaFiniteSet` is sigma-finite. -/
instance : SigmaFinite (μ.restrict μ.sigmaFiniteSet) := by
  rw [Measure.sigmaFiniteSet]
  infer_instance

lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero (h : μ μ.sigmaFiniteSetᶜ = 0) :
    SigmaFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet (μ := μ)),
    Measure.restrict_eq_zero.mpr h, add_zero]
  infer_instance

@[simp]
lemma measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0 :=
  measure_compl_sigmaFiniteSetWRT Measure.AbsolutelyContinuous.rfl

/-- An s-finite measure `μ` is sigma-finite iff `μ μ.sigmaFiniteSetᶜ = 0`. -/
lemma measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite (μ : Measure α) :
    μ μ.sigmaFiniteSetᶜ = 0 ↔ SigmaFinite μ :=
  ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ ↦ measure_compl_sigmaFiniteSet μ⟩

end SigmaFiniteSet

end MeasureTheory
