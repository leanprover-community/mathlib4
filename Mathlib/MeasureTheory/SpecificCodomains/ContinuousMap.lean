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

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)`-valued function, where `Y` is a compact topological space and `E` is a normed group.

These are all elementary from a mathematical point of view, but they require a bit of care in order
to be conveniently usable. In particular, to accommodate the need of families `f : X → Y → E` which
such that `f x` is only continuous for *almost every* `x`, we give a variety of results about the
integrability of `fun x ↦ ContinuousMap.mkD (f x) g` whose assumption only mention `f` (so that
user don't have to convert between `f` and `fun x ↦ ContinuousMap.mkD (f x) g` by hand).

## Main results

* `hasFiniteIntegral_of_bound`: given `f : X → C(Y, E)`, the natural way to show
  `HasFiniteIntegral f` is to give a `bound : X → ℝ`, which itself has finite integral, and such
  that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
* `hasFiniteIntegral_mkD_of_bound` is the `mkD` analog of the above: given `f : X → Y → E` such
  that `f x` is continuous for almost every `x`, as well as a bound as above, we prove
  `HasFiniteIntegral (fun x ↦ mkD (f x) g)`. Note that, conveniently, `mkD` only appears in the
  result.
* `aeStronglyMeasurable_mkD_of_uncurry`: if now `X` is a topological space with the Borel σ-algebra,
  and `f : X → Y → E` is continuous on `X × Y`, then `fun x ↦ mkD (f x) g` is
  `AEStronglyMeasurable`. Note that this is far from optimal: this function is in fact continuous,
  and one could avoid `mkD` entirely since `f x` is always continuous in that case. Nevertheless,
  this turns out to be most convenient, as we explain below.

## Implementation Note

We claim that using "constructors with default values" such as `ContinuousMap.mkD` is the right way
to approach integration valued in a functional space `ℱ`. More precisely:

- if you happen to start from a bundled `f : X → ℱ` function, you should be able to use
  the general theory without any issues.
- if instead you start with a family of bare functions `f : X → Y → E`, to integrate it in `ℱ`, you
  should always consider the family `fun x ↦ ℱ.mkD (f x) 0`, *even if your `f` always lands in `ℱ`*.
  This allows for a unified setting with the case where `f x` belongs to `ℱ` for *almost every `x`*,
  and also avoids entering dependent-types hell.

-/

open MeasureTheory

namespace ContinuousMap

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(Y, E)`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `Y`). We are just using the properties of Banach-space-valued integration. -/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] (f : X → C(Y, E)) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  rcases isEmpty_or_nonempty Y with (h|h)
  · simp
  · have bound_nonneg : 0 ≤ᵐ[μ] bound := by
      filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x h.some)
    refine .mono' bound_int ?_
    filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
    exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMap.mkD`. -/
lemma hasFiniteIntegral_mkD_of_bound [CompactSpace Y] (f : X → Y → E) (g : C(Y, E))
    (f_ae_cont : ∀ᵐ x ∂μ, Continuous (f x))
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (f x) g) μ := by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont] with x bound_ge_x cont_x
  simpa only [mkD_apply_of_continuous cont_x] using bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_mkD_of_bound` for a family of
functions which are continuous on a compact set. -/
lemma hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s]
    (f : X → Y → E) (g : C(s, E))
    (f_ae_contOn : ∀ᵐ x ∂μ, ContinuousOn (f x) s)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (s.restrict (f x)) g) μ := by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_restrict]
  · simpa

lemma aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (f : X → Y → E) (g : C(Y, E)) (f_cont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) μ :=
  continuous_mkD_of_uncurry _ _ f_cont |>.aestronglyMeasurable

open Set in
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] {s : Set X}
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(Y, E))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) (μ.restrict s) :=
  continuousOn_mkD_of_uncurry _ _ f_cont |>.aestronglyMeasurable hs

open Set in
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(t, E))]
    (f : X → Y → E) (g : C(t, E)) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    AEStronglyMeasurable (fun x ↦ mkD (t.restrict (f x)) g) μ :=
  continuous_mkD_restrict_of_uncurry _ _ f_cont |>.aestronglyMeasurable

open Set in
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(t, E))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    AEStronglyMeasurable (fun x ↦ mkD (t.restrict (f x)) g) (μ.restrict s) :=
  continuousOn_mkD_restrict_of_uncurry _ _ f_cont |>.aestronglyMeasurable hs

end ContinuousMap
