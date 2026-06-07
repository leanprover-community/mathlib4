/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Product of vector measures
-/

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {ι X Y E F G : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure X E} {ν : VectorMeasure Y F}
  {B : E →L[ℝ] F →L[ℝ] G} {f g : X → E} {s t : Set X}

namespace MeasureTheory.VectorMeasure

omit [NormedSpace ℝ E] in
theorem vectorMeasure_if {x : Y} {t : Set Y} {s : Set X} [Decidable (x ∈ t)] :
    μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs with h <;> simp [h]

open scoped Classical in
/-- The product of two vector measures `μ` and `ν` with respect to a continuous bilinear map `B`,
giving mass `B (μ s) (ν s)` to a measurable set `s`.
If such a measure does not exist, we use the junk value `0`. -/
noncomputable def prod (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure (X × Y) G :=
  if h : ∃ ρ : VectorMeasure (X × Y) G, ∀ (s : Set X) (t : Set Y),
    MeasurableSet s →MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t) then h.choose
  else 0

/-- Two vector measures `μ` and `ν` have a product with respect to `B` if there exists a
measure giving mass `B (μ s) (ν t)` to any measurable product `s × t`.
This is satisfied whenever `μ` or `ν` has finite variation. -/
class HasProd (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) where
  out : ∃ ρ : VectorMeasure (X × Y) G, ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)

omit [NormedSpace ℝ F] in
/-- If `ν` is a vector measure, and `s ⊆ X × Y` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
a strongly measurable function. -/
theorem stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)}
    (hs : MeasurableSet s) : StronglyMeasurable fun x => ν (Prod.mk x ⁻¹' s) := by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, vectorMeasure_if] using
      stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i ↦ ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i ↦ measurable_prodMk_left (hfm i), hfd.mono fun _ _ ↦ .preimage _]
    apply StronglyMeasurable.hasSum ihf this

open scoped Classical in
/-- The naive product of two vector measures, obtained by integrating the measure of the fibers,
as in the definition of the product of positive measures. -/
noncomputable def naiveProd (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G)
    [IsFiniteMeasure (μ.transpose B.flip).variation] :
    VectorMeasure (X × Y) G where
  measureOf' s := if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ (t : Set Y), ‖ν t‖ ≤ C := sorry
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion]
    simp only [HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset ℕ) : ∑ y ∈ a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y ∈ a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum]
      intro i hi
      refine Integrable.of_bound (μ := (μ.transpose B.flip).variation) ?_ C ?_
      · exact (stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)).aestronglyMeasurable
      · exact Eventually.of_forall (fun x ↦ hC _)
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x ↦ C)
    · apply Eventually.of_forall (fun a ↦ ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi ↦ ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply hC
      · exact fun i hi j hj hij ↦ (f_disj hij).preimage _
      · exact fun i hi ↦ measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i ↦ measurable_prodMk_left (f_meas i)
      · exact fun i j hij ↦ (f_disj hij).preimage _

instance [IsFiniteMeasure (μ.transpose B.flip).variation] : HasProd μ ν B where
  out := by
    classical
    refine ⟨naiveProd μ ν B, fun s t hs ht ↦ ?_⟩
    simp only [naiveProd, hs.prod ht, ↓reduceIte]
    simp_rw [mk_preimage_prod_right_eq_if, vectorMeasure_if, integral_indicator hs]
    rw [setIntegral_const]





#exit

      simp_rw [S, mk_preimage_prod_right_eq_if, measure_if,
        lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
        restrict_apply_univ, mul_comm]
    _ = μ s * ν t := by rw [measure_toMeasurable, measure_toMeasurable]



lemma prod_apply {μ : VectorMeasure X E} {ν : VectorMeasure Y F} [h : HasProd μ ν B] {s : Set X} {t : Set Y} :
    μ.prod ν B (s ×ˢ t) = B (μ s) (ν t) := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero,
      ContinuousLinearMap.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h.out] using h.out.choose_spec s t h's h't
