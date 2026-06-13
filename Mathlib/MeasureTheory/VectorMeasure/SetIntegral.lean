/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

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

theorem setIntegral_diff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hts : t ⊆ s) :
    ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] - ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union (by grind) (hs.diff ht) ht (hfs.mono hs diff_subset)
    (hfs.mono hs hts), diff_union_of_subset hts]

theorem setIntegral_inter_add_diff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) :
    ∫ᵛ x in s ∩ t, f x ∂[B; μ] + ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← μ.restrict_inter_add_diff hs ht,
    integral_add_vectorMeasure (hfs.mono hs inter_subset_left) (hfs.mono hs diff_subset)]

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
  simp [integral_eq_setToFun, this]

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

theorem setIntegral_union_eq_left_of_ae (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht_eq : ∀ᵐ x ∂μ.variation.restrict t, f x = 0) :
    ∫ᵛ x in s ∪ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  classical
  rw [← integral_indicator hs, ← integral_indicator (hs.union ht)]
  apply integral_congr_ae
  rw [ae_restrict_iff' ht] at ht_eq
  filter_upwards [ht_eq] with x hx
  classical
  simp only [indicator_apply, mem_union]
  grind

theorem setIntegral_union_eq_left_of_forall (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ᵛ x in s ∪ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  apply setIntegral_union_eq_left_of_ae hs ht
  rw [ae_restrict_iff' ht]
  filter_upwards with x using ht_eq x

theorem setIntegral_eq_of_subset_of_ae_diff_eq_zero (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hts : s ⊆ t) (h't : ∀ᵐ x ∂μ.variation.restrict (t \ s), f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rwa [← union_diff_cancel hts, setIntegral_union_eq_left_of_ae hs (ht.diff hs)]

/-- If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide. -/
theorem setIntegral_eq_of_subset_of_forall_diff_eq_zero
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : s ⊆ t)
    (h't : ∀ x ∈ t \ s, f x = 0) : ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  apply setIntegral_eq_of_subset_of_ae_diff_eq_zero hs ht hts
  apply (ae_restrict_iff' (ht.diff hs)).2
  filter_upwards with x using h't x

/-- If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space. -/
theorem setIntegral_eq_integral_of_ae_compl_eq_zero (hs : MeasurableSet s)
    (h : ∀ᵐ x ∂μ.variation, x ∉ s → f x = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_diff_eq_zero hs MeasurableSet.univ (subset_univ _)
  apply (ae_restrict_iff' (MeasurableSet.univ.diff hs)).2
  filter_upwards [h] with x hx h'x using hx h'x.2

/-- If a function vanishes on `sᶜ`, then its integral on `s` coincides with its integral on the
whole space. -/
theorem setIntegral_eq_integral_of_forall_compl_eq_zero (hs : MeasurableSet s)
    (h : ∀ x, x ∉ s → f x = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] :=
  setIntegral_eq_integral_of_ae_compl_eq_zero hs (Eventually.of_forall h)

theorem setIntegral_const [CompleteSpace G] [IsFiniteMeasure (μ.variation.restrict s)]
    (c : E) : ∫ᵛ _ in s, c ∂[B; μ] = B c (μ s) := by
  by_cases hs : MeasurableSet s
  · have : IsFiniteMeasure (μ.restrict s).variation := by
      rwa [variation_restrict hs]
    rw [integral_const, restrict_apply _ hs MeasurableSet.univ, univ_inter]
  · simp [setIntegral_eq_zero_of_not_measurableSet hs, μ.not_measurable' hs]

@[simp]
theorem integral_indicator_const [CompleteSpace G]
    (e : E) ⦃s : Set X⦄ [IsFiniteMeasure (μ.variation.restrict s)]
    (s_meas : MeasurableSet s) :
    ∫ᵛ x, s.indicator (fun _ : X ↦ e) x ∂[B; μ] = B e (μ s) := by
  rw [integral_indicator s_meas, ← setIntegral_const]

theorem setIntegral_map {β : Type*} [MeasurableSpace β]
    {φ : X → β} (hφ : Measurable φ) {f : β → E} {s : Set β} (hs : MeasurableSet s)
    (hfm : AEStronglyMeasurable f ((μ.restrict (φ ⁻¹' s)).variation.map φ))
    (hfi' : μ.Integrable (f ∘ φ)) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] := by
  rw [restrict_map μ hφ hs, integral_map hφ hfm hfi'.integrableOn]

theorem _root_.MeasurableEmbedding.setIntegral_map_vectorMeasure {β : Type*} [MeasurableSpace β]
    {φ : X → β} {f : β → E} (hφ : MeasurableEmbedding φ) {s : Set β} (hs : MeasurableSet s) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] := by
  rw [restrict_map μ hφ.measurable hs, hφ.integral_map_vectorMeasure]

theorem _root_.Topology.IsClosedEmbedding.setIntegral_map_vectorMeasure
    [TopologicalSpace X] [BorelSpace X] {β : Type*}
    [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] {φ : X → β} {f : β → E} {s : Set β}
    (hs : MeasurableSet s) (hφ : IsClosedEmbedding φ) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] :=
  hφ.measurableEmbedding.setIntegral_map_vectorMeasure hs

theorem setIntegral_map_equiv {β : Type*} [MeasurableSpace β] {e : X ≃ᵐ β} {f : β → E} {s : Set β}
    (hs : MeasurableSet s) :
    ∫ᵛ y in s, f y ∂[B; μ.map e] = ∫ᵛ x in e ⁻¹' s, f (e x) ∂[B; μ] :=
  e.measurableEmbedding.setIntegral_map_vectorMeasure hs

theorem continuousLinearMap_apply_integral
    [CompleteSpace G] [CompleteSpace H]
    {C : G →L[ℝ] H} (hf : Integrable f μ.variation) :
    C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL ℝ F G H C) ∘L B); μ] := by
  apply hf.induction (P := fun f ↦ C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL ℝ F G H C) ∘L B); μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    simp [integral_indicator_const _ hs]
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply]
    simp [integral_fun_add, f_int, g_int, hf, hg]
  · apply isClosed_eq
    · apply C.continuous.comp continuous_integral
    · exact continuous_integral
  · intro f g hfg _ hf
    rw [← integral_congr_ae hfg, ← integral_congr_ae hfg, hf]

theorem integral_continuousLinearMap_comp
    {f : X → H} {C : H →L[ℝ] E} (hf : Integrable f μ.variation) :
    ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  apply hf.induction (P := fun f ↦ ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    rw [integral_indicator_const _ hs]
    have : (fun y ↦ C (s.indicator (fun x ↦ c) y)) = s.indicator (fun x ↦ C c) := by
      ext; simp only [indicator]; grind
    simp_rw [this]
    rw [integral_indicator_const _ hs]
    rfl
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply, _root_.map_add]
    rw [integral_fun_add (C.integrable_comp f_int) (C.integrable_comp g_int), hf, hg,
      integral_fun_add f_int g_int]
  · apply isClosed_eq
    · have I (f : Lp H 1 μ.variation) : ∫ᵛ x, C (f x) ∂[B; μ] = ∫ᵛ x, (C.compLp f) x ∂[B; μ] :=
        (integral_congr_ae (coeFn_compLp _ _)).symm
      simp_rw [I]
      exact continuous_integral.comp (C.compLpL 1 μ.variation).continuous
    · exact continuous_integral
  · intro f g hfg _ hf
    have : ∀ᵐ x ∂μ.variation, C (f x) = C (g x) := by
      filter_upwards [hfg] with x hx using by simp [hx]
    rw [← integral_congr_ae hfg, ← integral_congr_ae this, hf]

theorem enorm_setIntegral_le_of_enorm_le_const_ae {C : ℝ≥0∞}
    (hC : ∀ᵐ x ∂μ.variation.restrict s, ‖f x‖ₑ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ C * ‖B‖ₑ * μ.variation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  rw [← variation_restrict hs] at hC
  apply (enorm_integral_le_of_enorm_le_const hC).trans
  rw [variation_restrict hs, Measure.restrict_apply MeasurableSet.univ]
  simp

theorem enorm_setIntegral_le_of_enorm_le_const {C : ℝ≥0∞}
    (hC : ∀ x ∈ s, ‖f x‖ₑ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ C * ‖B‖ₑ * μ.variation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply enorm_setIntegral_le_of_enorm_le_const_ae
  apply (ae_restrict_iff' hs).2
  filter_upwards with x using hC x

theorem norm_setIntegral_le_of_norm_le_const_ae {C : ℝ}
    [h : IsFiniteMeasure (μ.variation.restrict s)]
    (hC : ∀ᵐ x ∂μ.variation.restrict s, ‖f x‖ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ ≤ C * ‖B‖ * μ.variation.real s := by
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    by_cases h's : μ.variation s = 0
    · simp [Measure.real, h's]
    · have : NeBot (ae (μ.variation.restrict s)) := by simpa using h's
      obtain ⟨x, hx⟩ : ∃ x, ‖f x‖ ≤ C := hC.exists
      have : 0 ≤ C := le_trans (norm_nonneg _) hx
      positivity
  rw [← variation_restrict hs] at hC h
  apply (norm_integral_le_of_norm_le_const hC).trans_eq
  simp [variation_restrict hs]

theorem norm_setIntegral_le_of_norm_le_const {C : ℝ}
    [h : IsFiniteMeasure (μ.variation.restrict s)]
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ ≤ C * ‖B‖ * μ.variation.real s := by
  rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    have : 0 ≤ C := le_trans (norm_nonneg _) (hC x hx)
    positivity
  apply norm_setIntegral_le_of_norm_le_const_ae
  filter_upwards [ae_restrict_mem hs] with x hx using hC x hx

theorem enorm_setIntegral_le_lintegral_enorm :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ ‖B‖ₑ * ∫⁻ x in s, ‖f x‖ₑ ∂μ.variation := by
  grw [enorm_integral_le_lintegral_enorm, variation_restrict_le]

theorem enorm_setIntegral_le_lintegral_enorm_transpose :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂(μ.transpose B).variation := by
  grw [enorm_integral_le_lintegral_enorm_transpose, transpose_restrict,variation_restrict_le]

private theorem hasSum_setIntegral_iUnion_nat {s : ℕ → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  have I : ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation < ∞ := calc
    ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation
    _ = ‖B‖ₑ * ∫⁻ x in (⋃ i, s i), ‖f x‖ₑ ∂μ.variation := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion hm hd]
    _ < ∞ := by
      simp only [VectorMeasure.IntegrableOn, VectorMeasure.Integrable,
        variation_restrict (MeasurableSet.iUnion hm)] at hfi
      exact ENNReal.mul_lt_top (by simp) hfi.2
  have : Summable (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) := by
    apply Summable.of_enorm (lt_of_le_of_lt _ I).ne
    gcongr
    exact enorm_setIntegral_le_lintegral_enorm
  apply (Summable.hasSum_iff_tendsto_nat this).2
  simp_rw [tendsto_iff_edist_tendsto_0, edist_eq_enorm_sub, enorm_sub_rev]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ I.ne) (by positivity) (fun N ↦ ?_)
  have : ⋃ n, s n = (⋃ n ∈ Finset.range N, s n) ∪ (⋃ n, s (n + N)) := by
    ext x
    have : (∃ i, x ∈ s (i + N)) ↔ (∃ i ≥ N, x ∈ s i) :=
      ⟨fun ⟨i, hi⟩ ↦ ⟨i + N, by grind⟩, fun ⟨i, hi, h'i⟩ ↦ ⟨i - N, by grind⟩⟩
    simp only [mem_iUnion, Finset.mem_range, mem_union, exists_prop, this, ge_iff_le]
    grind
  rw [this, setIntegral_union]; rotate_left
  · simp only [Finset.mem_range, disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j hi
    apply hd (by grind)
  · apply MeasurableSet.biUnion (Finset.countable_toSet _) (fun i hi ↦ hm i)
  · apply MeasurableSet.iUnion (fun i ↦ hm _)
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  rw [setIntegral_biUnion_finset]; rotate_left
  · exact fun i hi ↦ hm i
  · exact fun i hi j hj hij ↦ hd hij
  · exact fun i hi ↦ hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  simp only [add_sub_cancel_left]
  apply enorm_setIntegral_le_lintegral_enorm.trans_eq
  rw [lintegral_iUnion (fun i ↦ hm _), ENNReal.tsum_mul_left]
  exact fun i j hij ↦ hd (by grind)

theorem hasSum_setIntegral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  classical
  rcases finite_or_infinite ι with hι | hι
  · letI : Fintype ι := Fintype.ofFinite ι
    have : ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
      rw [setIntegral_iUnion_fintype hm hd (fun i ↦ ?_)]
      exact hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
    rw [this]
    apply hasSum_fintype
  obtain ⟨e⟩ : Nonempty (ι ≃ ℕ) := nonempty_equiv_of_countable
  rw [← e.symm.surjective.iUnion_comp, ← e.symm.hasSum_iff]
  apply hasSum_setIntegral_iUnion_nat (fun i ↦ hm _) (fun i j hij ↦ hd (by simp [hij]))
  rwa [e.symm.surjective.iUnion_comp]

theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑' n, ∫ᵛ x in s n, f x ∂[B; μ] :=
  (HasSum.tsum_eq (hasSum_setIntegral_iUnion hm hd hfi)).symm

@[simp] theorem setIntegral_toSignedMeasure {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → G} {s : Set X} (hs : MeasurableSet s) :
    ∫ᵛ x in s, f x ∂<•μ.toSignedMeasure = ∫ x in s, f x ∂μ := by
  rw [← integral_toSignedMeasure, restrict_toSignedMeasure hs]

/-- If `f` is integrable, then `∫ᵛ x in s, f x ∂[B; μ]` is absolutely continuous in `s`:
it tends to zero as `μ.variation s` tends to zero. -/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι : Type*}
    (hf : μ.Integrable f) {l : Filter ι} {s : ι → Set X}
    (hs : Tendsto (μ.variation ∘ s) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ᵛ x in s i, f x ∂[B; μ]) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  have : Tendsto (fun i ↦ ‖B‖ₑ * ∫⁻ (x : X) in s i, ‖f x‖ₑ ∂μ.variation) l (𝓝 (‖B‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero (ne_of_lt hf.2) hs) (by simp)
  rw [mul_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun i ↦ zero_le)
  intro i
  apply enorm_integral_le_lintegral_enorm.trans
  dsimp
  gcongr
  exact variation_restrict_le

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
lemma tendsto_setIntegral_of_L1 {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f ?_ ?_ ?_
  · apply hfi.mono_measure
    grw [variation_restrict_le, Measure.restrict_le_self]
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le)
      (fun i ↦ ?_)
    apply eLpNorm_mono_measure
    grw [variation_restrict_le]
    apply Measure.restrict_le_self

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
lemma tendsto_setIntegral_of_L1' {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ.variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

end MeasureTheory.VectorMeasure
