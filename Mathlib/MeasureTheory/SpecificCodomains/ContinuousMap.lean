/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Specific results about `ContinuousMap`-valued integration
-/

open MeasureTheory

namespace ContinuousMap

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(α, E)`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ z : α, ‖f x z‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `α`). We are just using the properties of Banach-space-valued integration. -/
lemma hasFiniteIntegral_of_bound [CompactSpace α] (f : X → C(α, E)) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z : α, ‖f x z‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  rcases isEmpty_or_nonempty α with (h|h)
  · sorry
  · have bound_nonneg : 0 ≤ᵐ[μ] bound := by
      filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x h.some)
    refine .mono' bound_int ?_
    filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
    exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMap.mkD`. -/
lemma hasFiniteIntegral_mkD_of_bound [CompactSpace α] (f : X → α → E) (g : C(α, E))
    (f_ae_cont : ∀ᵐ x ∂μ, Continuous (f x))
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z : α, ‖f x z‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (f x) g) μ := by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont] with x bound_ge_x cont_x
  simpa only [mkD_apply_of_continuous cont_x] using bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMap.mkD`. -/
lemma hasFiniteIntegral_mkD_restrict_of_bound {s : Set α} [CompactSpace s]
    (f : X → α → E) (g : C(s, E))
    (f_ae_contOn : ∀ᵐ x ∂μ, ContinuousOn (f x) s)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ s, ‖f x z‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (s.restrict (f x)) g) μ := by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_restrict]
  · simpa

lemma aeStronglyMeasurable_mkD_of_uncurry [CompactSpace α] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(α, E))]
    (f : X → α → E) (g : C(α, E)) (f_cont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) μ :=
  continuous_mkD_of_uncurry _ _ f_cont |>.aestronglyMeasurable

open Set in
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace α] {s : Set X}
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(α, E))]
    (hs : MeasurableSet s) (f : X → α → E) (g : C(α, E))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) (μ.restrict s) :=
  continuousOn_mkD_of_uncurry _ _ f_cont |>.aestronglyMeasurable hs

open Set in
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set α} [CompactSpace t] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(t, E))]
    (f : X → α → E) (g : C(t, E)) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    AEStronglyMeasurable (fun x ↦ mkD (t.restrict (f x)) g) μ :=
  continuous_mkD_restrict_of_uncurry _ _ f_cont |>.aestronglyMeasurable

open Set in
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set α}
    [CompactSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) (f : X → α → E) (g : C(t, E))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    AEStronglyMeasurable (fun x ↦ mkD (t.restrict (f x)) g) (μ.restrict s) :=
  continuousOn_mkD_restrict_of_uncurry _ _ f_cont |>.aestronglyMeasurable hs

end ContinuousMap
