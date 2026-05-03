/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Support

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Resolvent Transform of a Measure

Given a normed algebra `A` over a normed field `𝕜`, and `μ : Measure 𝕜`, we define the
resolvent transform of `μ` by the formula

`resolventTransform μ a = ∫ x, resolvent a x ∂μ`

This is not a standard notion in the literature, but specializes to a few standard notions,
namely the case `𝕜 = ℝ` and `A = ℂ` is the Stieltjes transform, and the case `𝕜 = A = ℂ` is the
Cauchy transform.

## Main definitions

* `resolventTransform μ a`: The resolvent transform of a measure `μ` at `a`

## Main statements

* `MeasureTheory.hasDerivAt_resolventTransform` : For any `a` not in the support of `μ`,
  the `resolventTransform` has derivative `∫ x, resolvent a x ^ 2 ∂u` at `a`.
* `MeasureTheory.analyticOn_resolventTransform` : In the case `A = ℂ`, the `resolventTransform`
  is holomorphic on the complement of `μ.support`.

## Tags

resolvent transform, Stieljes transform, Cauchy transform
-/

@[expose] public section

variable {𝕜 A : Type*}

open MeasureTheory Measure Metric Filter Complex spectrum

open scoped Topology

namespace MeasureTheory

section resolvent

variable [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]

@[fun_prop]
theorem measurable_resolvent {a : A} [OpensMeasurableSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A] [MeasurableSpace A] [BorelSpace A] :
  Measurable (resolvent (R := 𝕜) a) := by
  classical
  have h1 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a) :=
    HasDerivAt.continuousOn (fun _ hx ↦ hasDerivAt_resolvent_const_left hx)
  have h2 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a)ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    convert continuous_const (y := (0 : A)) with x
    simp
  have h3 : MeasurableSet (resolventSet 𝕜 a) := (isOpen_resolventSet a).measurableSet
  simpa using h1.measurable_piecewise h2 h3

variable [CompleteSpace 𝕜] [NormedDivisionRing A] [NormedAlgebra 𝕜 A]

theorem norm_resolvent_le_inv_infDist_support {μ : Measure 𝕜} {a : A}
    (hz : a ∉ algebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x ∈ μ.support) :
    ‖resolvent a x‖ ≤ (infDist a (algebraMap 𝕜 A '' μ.support))⁻¹ := by
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  have : infDist a (algebraMap 𝕜 A '' μ.support) ≤ ‖(algebraMap 𝕜 A) x - a‖ := by
    grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x), ← dist_eq_norm, dist_comm]
    simp [hx]
  grw [resolvent, Ring.inverse_eq_inv', norm_inv, inv_le_inv₀ (by linarith) (by positivity), this]

theorem integrable_resolvent [HereditarilyLindelofSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [CompleteSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    {μ : Measure 𝕜} [IsFiniteMeasure μ] {a : A} (hz : a ∉ algebraMap 𝕜 A '' μ.support) :
    Integrable (resolvent a) μ := by
  refine ⟨by fun_prop, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards [support_mem_ae] with x hx using norm_resolvent_le_inv_infDist_support hz hx

end resolvent

section Definition

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra 𝕜 A] [MeasurableSpace 𝕜]

/-- The resolvent transform of a measure of a measure `μ`. -/
noncomputable
def resolventTransform (μ : Measure 𝕜) (a : A) :=
  ∫ x, resolvent a x ∂μ

lemma resolventTransform_def (μ : Measure 𝕜) :
  resolventTransform μ = fun (a : A) ↦ (∫ x, resolvent a x ∂μ) := rfl

lemma resolventTransform_apply (μ : Measure 𝕜) (a : A) :
    resolventTransform μ a = ∫ x, resolvent a x ∂μ := rfl

@[simp]
lemma resolventTransform_zero_measure : resolventTransform (0 : Measure 𝕜) = (0 : A → A) := by
  ext
  simp [resolventTransform]

@[simp]
lemma resolventTransform_dirac [OpensMeasurableSpace 𝕜] [CompleteSpace A]
    (x : 𝕜) (a : A) : resolventTransform (.dirac x) a = resolvent a x := by
  simp [resolventTransform_def]

end Definition

section Deriv

variable [NontriviallyNormedField 𝕜] [HereditarilyLindelofSpace 𝕜] [CompleteSpace 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

theorem hasDerivAt_resolventTransform [RCLike A] [NormedAlgebra 𝕜 A] (μ : Measure 𝕜)
    [IsFiniteMeasure μ] (a : A) (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    HasDerivAt (resolventTransform μ) (∫ x, resolvent a x ^ 2 ∂μ) a := by
  by_cases h : μ.support.Nonempty; swap
  · have : μ = 0 := by contrapose! h; exact nonempty_support h
    simp [this, hasDerivAt_zero]
  rw [resolventTransform_def]
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ (h.image _)).mp ha
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  let s : Set A := ball a ((infDist a (algebraMap 𝕜 A '' μ.support)) / 2)
  have hs_z : s ∈ 𝓝 a := ball_mem_nhds _ (by positivity)
  have hs_μ : s ⊆ (algebraMap 𝕜 A '' μ.support)ᶜ := by
    unfold s
    grw [ball_subset_ball, ball_infDist_subset_compl]
    grind
  have resolvent_meas : ∀ᶠ w in nhds a, AEStronglyMeasurable (resolvent w) μ := by
    filter_upwards with _ using by fun_prop
  have resolvent'_bound : ∀ᵐ x ∂μ, ∀ w ∈ s,
      ‖(resolvent w x) ^ 2‖ ≤ ((infDist a (algebraMap 𝕜 A '' μ.support)) / 2)⁻¹ ^ 2 := by
    filter_upwards [support_mem_ae] with x hx w hw
    grw [resolvent, Ring.inverse_eq_inv, norm_pow, norm_inv]
    gcongr
    calc infDist a (algebraMap 𝕜 A '' μ.support) / 2
      _ ≤ infDist a (algebraMap 𝕜 A '' μ.support)
        - infDist a (algebraMap 𝕜 A '' μ.support) / 2 := by grind
      _ ≤ ‖(algebraMap 𝕜 A) x - a‖ - ‖a - w‖ := by
        gcongr
        · grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x) (by simp [hx]), dist_comm,
            dist_eq_norm]
        · apply le_of_lt
          simpa [s, ← dist_eq_norm, dist_comm w a] using hw
      _ ≤ ‖(algebraMap 𝕜 A) x - w‖ := by grw [norm_sub_le_norm_add]; grind
  have h_deriv : ∀ᵐ x ∂μ, ∀ w ∈ s, HasDerivAt (fun w ↦ resolvent w x) (resolvent w x ^ 2) w := by
    filter_upwards [support_mem_ae] with x hx w hw
    apply hasDerivAt_resolvent_const_right
    replace hw := hs_μ hw
    contrapose! hw
    rw [Set.notMem_compl_iff]
    use x, hx
    simpa [resolventSet, sub_eq_zero] using hw
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_z resolvent_meas
    (integrable_resolvent (by simp [ha])) (by fun_prop) resolvent'_bound (by fun_prop) h_deriv |>.2

theorem analyticOn_resolventTransform [NormedAlgebra 𝕜 ℂ] (μ : Measure 𝕜) [IsFiniteMeasure μ] :
    AnalyticOn ℂ (resolventTransform μ) (algebraMap 𝕜 ℂ '' μ.support)ᶜ := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply HasDerivAt.differentiableAt
    exact hasDerivAt_resolventTransform μ z hz
  apply isOpen_compl_iff.mpr
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
  exact (algebraMap_isometry 𝕜 ℂ).isClosedEmbedding

end Deriv

end MeasureTheory
