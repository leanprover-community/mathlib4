/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Set integral

In this file we prove properties of `∫ᵛ x in s, f x ∂[B; μ]`. Recall that this notation
is defined as `∫ᵛ x, f x ∂[B; μ.restrict s]`.

The API in this file is modelled on the API for the Bochner integral.
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology ContinuousLinearMap
open scoped ENNReal NNReal Finset

variable {ι X E F G H : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  {μ ν : VectorMeasure X F} {f g : X → E} {s t : Set X}

namespace MeasureTheory.VectorMeasure

theorem IntegrableOn.mono (hs : MeasurableSet s) (hts : t ⊆ s) (h : μ.IntegrableOn f s) :
    μ.IntegrableOn f t := by
  by_cases ht : MeasurableSet t; swap
  · simp [VectorMeasure.IntegrableOn, restrict_not_measurable _ ht]
  apply Integrable.mono_measure h
  simp [variation_restrict, hs, ht, Measure.restrict_mono hts le_rfl]

theorem IntegrableOn.union (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hf : μ.IntegrableOn f s) (h'f : μ.IntegrableOn f t) :
    μ.IntegrableOn f (s ∪ t) := by
  apply Integrable.mono_measure (hf.add_measure h'f)
  grw [variation_restrict_le, Measure.restrict_union_le]
  simp [variation_restrict, hs, ht]

/- `simpNF` complains that this lemma can be proved by `simp`, because the `simp`-generated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958. -/
@[simp, nolint simpNF] theorem IntegrableOn.empty : μ.IntegrableOn f ∅ := by
  simp [VectorMeasure.IntegrableOn]

theorem IntegrableOn.biUnion_finite
    {s : Set ι} (hs : s.Finite) {t : ι → Set X} (ht : ∀ i ∈ s, MeasurableSet (t i))
    (h't : ∀ i ∈ s, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i ∈ s, t i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ h's hf =>
    simp only [mem_insert_iff, forall_eq_or_imp, iUnion_iUnion_eq_or_left] at ht h't ⊢
    exact IntegrableOn.union ht.1 (h's.measurableSet_biUnion ht.2)  h't.1 (hf ht.2 h't.2)

theorem IntegrableOn.biUnion_finset {s : Finset ι} {t : ι → Set X}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) (h't : ∀ i ∈ s, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i ∈ s, t i) :=
  IntegrableOn.biUnion_finite s.finite_toSet ht h't

theorem IntegrableOn.iUnion_finite [Finite ι] {t : ι → Set X}
    (ht : ∀ i, MeasurableSet (t i)) (h't : ∀ i, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i, t i) := by
  cases nonempty_fintype ι
  simpa using IntegrableOn.biUnion_finset (f := f) (μ := μ) (s := Finset.univ) (t := t)
    (fun i hi ↦ ht i) (fun i hi ↦ h't i)

@[simp] theorem integrableOn_univ : μ.IntegrableOn f univ ↔ μ.Integrable f := by
  simp [VectorMeasure.IntegrableOn]

theorem Integrable.integrableOn (h : μ.Integrable f) : μ.IntegrableOn f s := by
  rw [← integrableOn_univ] at h
  exact h.mono MeasurableSet.univ (subset_univ _)

theorem integrable_indicator_iff (hs : MeasurableSet s) :
    μ.Integrable (indicator s f) ↔ μ.IntegrableOn f s := by
  simp [VectorMeasure.Integrable, VectorMeasure.IntegrableOn, MeasureTheory.IntegrableOn,
    MeasureTheory.integrable_indicator_iff hs, variation_restrict hs]

theorem IntegrableOn.integrable_indicator (h : μ.IntegrableOn f s) (hs : MeasurableSet s) :
    μ.Integrable (indicator s f) :=
  (integrable_indicator_iff hs).2 h

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
  {B : E →L[ℝ] F →L[ℝ] G}

theorem setIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  simp [restrict_not_measurable _ hs]

theorem setIntegral_congr_ae (h : ∀ᵐ x ∂μ.variation, x ∈ s → f x = g x) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ] := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply integral_congr_ae
  rw [variation_restrict hs]
  exact (ae_restrict_iff' hs).2 h

theorem setIntegral_congr_fun (h : EqOn f g s) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ] :=
  setIntegral_congr_ae <| Eventually.of_forall h

theorem setIntegral_union (hst : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hft : μ.IntegrableOn f t) :
    ∫ᵛ x in s ∪ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [← integral_add_vectorMeasure hfs hft, μ.restrict_union hst hs ht]

theorem setIntegral_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hts : t ⊆ s) :
    ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] - ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union (by grind) (hs.diff ht) ht (hfs.mono hs sdiff_subset)
    (hfs.mono hs hts), sdiff_union_of_subset hts]

theorem setIntegral_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) :
    ∫ᵛ x in s ∩ t, f x ∂[B; μ] + ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← μ.restrict_inter_add_sdiff hs ht,
    integral_add_vectorMeasure (hfs.mono hs inter_subset_left) (hfs.mono hs sdiff_subset)]

theorem setIntegral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : ∀ i ∈ t, μ.IntegrableOn f (s i)) :
    ∫ᵛ x in ⋃ i ∈ t, s i, f x ∂[B; μ] = ∑ i ∈ t, ∫ᵛ x in s i, f x ∂[B; μ] := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact hs.1
    · exact Finset.measurableSet_biUnion _ hs.2
    · exact hf.1
    · apply IntegrableOn.biUnion_finset hs.2 hf.2

theorem setIntegral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : ∀ i, μ.IntegrableOn f (s i)) :
    ∫ᵛ x in ⋃ i, s i, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
  convert setIntegral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

theorem setIntegral_empty : ∫ᵛ x in ∅, f x ∂[B; μ] = 0 := by simp

theorem setIntegral_univ : ∫ᵛ x in univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by simp

theorem setIntegral_add_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) :
    ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by
  rw [← setIntegral_union disjoint_compl_right
    hs hs.compl hfi.integrableOn hfi.integrableOn, union_compl_self, setIntegral_univ]

theorem setIntegral_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) :
    ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← setIntegral_add_compl (μ := μ) hs hfi, add_sub_cancel_left]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ᵛ x in s, f x ∂[B; μ]`
defined as `∫ᵛ x, f x ∂[B; μ.restrict s]`. -/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  by_cases hfi : μ.IntegrableOn f s; swap
  · rw [integral_undef hfi, integral_undef]
    rw [integrable_indicator_iff hs]
    simpa [transpose_restrict, variation_restrict hs] using hfi
  calc
    ∫ᵛ x, indicator s f x ∂[B; μ]
    _ = ∫ᵛ x in s, indicator s f x ∂[B; μ] + ∫ᵛ x in sᶜ, indicator s f x ∂[B; μ] :=
      (setIntegral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, 0 ∂[B; μ] := by
      apply congr_arg₂ (· + ·) (integral_congr_ae ?_) (integral_congr_ae ?_)
      · rw [variation_restrict hs]
        exact indicator_ae_eq_restrict hs
      · rw [variation_restrict hs.compl]
        exact indicator_ae_eq_restrict_compl hs
    _ = ∫ᵛ x in s, f x ∂[B; μ] := by simp

theorem setIntegral_indicator (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫ᵛ x in s, t.indicator f x ∂[B; μ] = ∫ᵛ x in s ∩ t, f x ∂[B; μ] := by
  rw [integral_indicator ht, μ.restrict_restrict ht hs, Set.inter_comm]

theorem setIntegral_congr_set
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s =ᵐ[μ.variation] t) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [hst] with x hx
  replace hx : x ∈ s ↔ x ∈ t := by simpa using! hx
  simp [indicator]
  grind

theorem integral_piecewise [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : μ.IntegrableOn f s) (hg : μ.IntegrableOn g sᶜ) :
    ∫ᵛ x, s.piecewise f g x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, g x ∂[B; μ] := by
  rw [← Set.indicator_add_compl_eq_piecewise,
    integral_add (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl),
    integral_indicator hs, integral_indicator hs.compl]

theorem setIntegral_eq_zero_of_ae_eq_zero
    (ht_eq : ∀ᵐ x ∂μ.variation, x ∈ t → f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = 0 := by
  by_cases ht : MeasurableSet t; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet ht]
  by_cases hf : AEStronglyMeasurable f (μ.restrict t).variation; swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  simp only [variation_restrict ht] at hf
  have : ∫ᵛ x in t, hf.mk f x ∂[B; μ] = 0 := by
    refine integral_eq_zero_of_ae ?_
    simp only [variation_restrict ht]
    apply (ae_restrict_iff' ht).2
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  apply integral_congr_ae
  simp only [variation_restrict ht]
  exact hf.ae_eq_mk

theorem setIntegral_eq_zero_of_forall_eq_zero (ht_eq : ∀ x ∈ t, f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = 0 :=
  setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)

theorem frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] ≠ 0) :
    ∃ᶠ x in ae (μ.variation.restrict t), f x ≠ 0 := by
  have ht : MeasurableSet t := by
    contrapose! hU
    simp [setIntegral_eq_zero_of_not_measurableSet hU]
  rw [← variation_restrict ht]
  exact frequently_ae_ne_zero_of_integral_ne_zero hU

theorem exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] ≠ 0) :
    ∃ x, x ∈ t ∧ f x ≠ 0 := by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

theorem setIntegral_of_variation_apply_eq_zero (f : X → E) {s : Set X}
    (hs : μ.variation s = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  by_cases h's : MeasurableSet s; swap
  · simp [restrict_not_measurable μ h's]
  have : (μ.restrict s).variation = 0 := by
    rw [variation_restrict h's]
    apply Measure.restrict_eq_zero.2 hs
  have : μ.restrict s = 0 := variation_eq_zero.1 this
  simpa [integral_eq_setToFun, this] using! setToFun_zero_left

theorem setIntegral_dirac' {mX : MeasurableSpace X} [CompleteSpace G] {a : X} {v : F}
    (hf : StronglyMeasurable f) {s : Set X} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a ∈ s then B (f a) v else 0 := by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac' hf
  · exact integral_zero_vectorMeasure

theorem setIntegral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
    {a : X} {v : F} {s : Set X} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a ∈ s then B (f a) v else 0 := by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac
  · exact integral_zero_vectorMeasure

theorem integral_singleton' [CompleteSpace G] {a : X} (hf : StronglyMeasurable f) :
    ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a}) := by
  simp only [restrict_singleton, integral_dirac' hf]

theorem integral_singleton [MeasurableSingletonClass X] {a : X} [CompleteSpace G] :
    ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a}) := by
  simp only [restrict_singleton, integral_dirac]

end MeasureTheory.VectorMeasure
