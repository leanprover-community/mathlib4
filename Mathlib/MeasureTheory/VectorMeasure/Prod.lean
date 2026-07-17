/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Semivariation

/-!
# Product of vector measures

Given two vector measures, we define their product `μ.prod ν B` as the vector measure assigning
to a measurable product `s × t` the mass `B (μ s) (ν t)`, if such a vector measure exists.
We show that it exists when either `μ` or `ν` has finite variation.

The API is modelled on the one for the product of positive measures.
-/

public section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {ι X Y E F G H I J : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup I] [NormedSpace ℝ I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  {μ : VectorMeasure X E} {ν : VectorMeasure Y F} {B : E →L[ℝ] F →L[ℝ] G}

namespace MeasureTheory.VectorMeasure

/-- Two vector measures `μ` and `ν` have a product with respect to `B` if there exists a
measure giving mass `B (μ s) (ν t)` to any measurable product set `s × t`.
This is satisfied whenever `μ` or `ν` has finite variation. -/
class HasProd (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) : Prop where
  exists_prod : ∃ ρ : VectorMeasure (X × Y) G, ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)

/-- The product of two vector measures `μ` and `ν` with respect to a continuous bilinear map `B`,
giving mass `B (μ s) (ν t)` to any measurable product set `s × t`.
If such a measure does not exist, we use the junk value `0`. -/
noncomputable def prod (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure (X × Y) G :=
  open scoped Classical in if h : HasProd μ ν B then h.exists_prod.choose else 0

lemma prod_eq_zero_of_not_hasProd (h : ¬HasProd μ ν B) :
    μ.prod ν B = 0 := by
  grind [HasProd, prod]

@[simp] lemma prod_apply [h : HasProd μ ν B] {s : Set X} {t : Set Y} :
    μ.prod ν B (s ×ˢ t) = B (μ s) (ν t) := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero, _root_.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h] using h.exists_prod.choose_spec s t h's h't

lemma HasProd.flip [HasProd μ ν B] : HasProd ν μ B.flip where
  exists_prod := by
    refine ⟨(μ.prod ν B).map Prod.swap, fun s t hs ht ↦ ?_⟩
    rw [map_apply _ (by fun_prop) (hs.prod ht)]
    simp

lemma hasProd_flip_iff : HasProd ν μ B.flip ↔ HasProd μ ν B :=
  ⟨fun h ↦ by simpa using HasProd.flip (μ := ν) (ν := μ) (B := B.flip), fun h ↦ HasProd.flip⟩

omit [NormedSpace ℝ F] in
/-- If `ν` is a vector measure, and `s ⊆ X × Y` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
a strongly measurable function. -/
theorem stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)}
    (hs : MeasurableSet s) : StronglyMeasurable fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, of_if] using stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i ↦ ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i ↦ measurable_prodMk_left (hfm i), hfd.mono fun _ _ ↦ .preimage _]
    exact StronglyMeasurable.hasSum ihf this

omit [NormedSpace ℝ E] in
theorem integrable_vectorMeasure_prodMk_left [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.Integrable fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  refine Integrable.of_bound (μ := μ.variation) ?_ ν.bound ?_
  · exact (stronglyMeasurable_vectorMeasure_prodMk_left hs).aestronglyMeasurable
  · exact Eventually.of_forall (fun x ↦ norm_apply_le_bound)

/-- The product of two vector measures when the first one has finite variation, obtained by
integrating the measure of the fibers, as in the definition of the product of positive measures.
*Do not use*: This is only used to instantiate the typeclass `HasProd`. Instead, use `μ.prod ν B`,
which uses the typeclass instance. -/
private noncomputable def prodOfIsFiniteMeasureLeft
    (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G)
    [IsFiniteMeasure μ.variation] :
    VectorMeasure (X × Y) G where
  measureOf' s := open scoped Classical in
    if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion,
      HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset ℕ) : ∑ y ∈ a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y ∈ a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum _ (fun i hi ↦ integrable_vectorMeasure_prodMk_left (f_meas i))]
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x ↦ ν.bound)
    · apply Eventually.of_forall (fun a ↦ ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi ↦ ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply norm_apply_le_bound
      · exact fun i hi j hj hij ↦ (f_disj hij).preimage _
      · exact fun i hi ↦ measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i ↦ measurable_prodMk_left (f_meas i)
      · exact fun i j hij ↦ (f_disj hij).preimage _

instance [CompleteSpace G] [IsFiniteMeasure μ.variation] : HasProd μ ν B where
  exists_prod := by
    classical
    refine ⟨prodOfIsFiniteMeasureLeft μ ν B, fun s t hs ht ↦ ?_⟩
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, hs, restrict_apply]

instance [CompleteSpace G] [h : IsFiniteMeasure ν.variation] : HasProd μ ν B :=
  hasProd_flip_iff.1 inferInstance

lemma prod_eq_of_forall_apply_prod {ρ : VectorMeasure (X × Y) G} (hρ : ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)) :
    μ.prod ν B = ρ := by
  have : HasProd μ ν B := ⟨ρ, hρ⟩
  apply ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← univ_prod_univ, hρ _ _ MeasurableSet.univ MeasurableSet.univ, prod_apply]
  · rintro - ⟨s, hs, t, ht, rfl⟩
    rw [prod_apply, hρ _ _ hs ht]

lemma prod_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] := by
  have : μ.prod ν B = prodOfIsFiniteMeasureLeft μ ν B := by
    classical
    apply prod_eq_of_forall_apply_prod (fun s t hs ht ↦ ?_)
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, restrict_apply, hs]
  rw [this]
  simp [prodOfIsFiniteMeasureLeft, hs]

lemma prod_flip_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {B : F →L[ℝ] E →L[ℝ] G} {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B.flip s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B; μ] := by
  simp [prod_apply_eq_integral hs]

lemma variation_prod_le [CompleteSpace G] [IsFiniteMeasure μ.variation] [SFinite ν.variation] :
    (μ.prod ν B).variation ≤ ‖B‖ₑ • μ.variation.prod ν.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  rw [prod_apply_eq_integral hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs]
  grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_flip,
    enorm_measure_le_variation]

instance [CompleteSpace G] [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation] :
    IsFiniteMeasure (μ.prod ν B).variation := by
  have : IsFiniteMeasure (‖B‖ₑ • μ.variation.prod ν.variation) := by
    simp only [enorm_eq_nnnorm, Measure.coe_nnreal_smul]
    infer_instance
  exact isFiniteMeasure_of_le _ variation_prod_le

end MeasureTheory.VectorMeasure
