/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap

/-!
# Specific results about `ContinuousMapZero`-valued integration

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)₀`-valued function, where `Y` is a compact topological space with a distinguished `0`,
and `E` is a normed group.

The structure of this file is largely similar to that of
`Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`, which contains a more detailed
module docstring.

-/

open MeasureTheory

namespace ContinuousMapZero

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(Y, E)₀`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `Y`). We are just using the properties of Banach-space-valued integration. -/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] [Zero Y] (f : X → C(Y, E)₀) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  have bound_nonneg : 0 ≤ᵐ[μ] bound := by
    filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x 0)
  refine .mono' bound_int ?_
  filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
  exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMapZero.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMapZero.mkD`. -/
lemma hasFiniteIntegral_mkD_of_bound [CompactSpace Y] [Zero Y] (f : X → Y → E) (g : C(Y, E)₀)
    (f_ae_cont : ∀ᵐ x ∂μ, Continuous (f x))
    (f_ae_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (f x) g) μ := by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont, f_ae_zero] with x bound_ge_x cont_x zero_x
  simpa only [mkD_apply_of_continuous cont_x zero_x] using bound_ge_x

/-- A variant of `ContinuousMapZero.hasFiniteIntegral_mkD_of_bound` for a family of
functions which are continuous on a compact set. -/
lemma hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] [Zero s]
    (f : X → Y → E) (g : C(s, E)₀)
    (f_ae_contOn : ∀ᵐ x ∂μ, ContinuousOn (f x) s)
    (f_ae_zero : ∀ᵐ x ∂μ, f x (0 : s) = 0)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (s.restrict (f x)) g) μ := by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ f_ae_zero bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_restrict]
  · simpa

lemma aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [Zero Y] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (f : X → Y → E) (g : C(Y, E)₀) (f_cont : Continuous (Function.uncurry f))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] [Zero Y] {s : Set X}
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(Y, E)₀)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [Zero t]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(t, E))]
    (f : X → Y → E) (g : C(t, E)₀) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t))
    (f_zero : ∀ᵐ x ∂μ, f x (0 : t) = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (t.restrict (f x)) g) μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [Zero t] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(t, E)₀)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x (0 : t) = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (t.restrict (f x)) g) (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

end ContinuousMapZero
