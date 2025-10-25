/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

The definition assumes that the random variables are defined on the same probability space, which
is the most common setting in applications. Convergence in distribution for random variables
on different probability spaces can be talked about using the `ProbabilityMeasure` type directly.

## Main definitions

* `TendstoInDistribution X l Z μ` : the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
-/

open Filter
open scoped Topology

namespace MeasureTheory

variable {Ω ι E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace E] {mE : MeasurableSpace E} {X Y : ι → Ω → E} {Z : Ω → E} {l : Filter ι}

section TendstoInDistribution

/-- Convergence in distribution of random variables.
This is the weak convergence of the laws of the random variables: `Tendsto` in the
`ProbabilityMeasure` type. -/
structure TendstoInDistribution [OpensMeasurableSpace E] (X : ι → Ω → E) (l : Filter ι) (Z : Ω → E)
    (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ] : Prop where
  forall_aeMeasurable : ∀ i, AEMeasurable (X i) μ
  aeMeasurable_limit : AEMeasurable Z μ := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (X n), Measure.isProbabilityMeasure_map (forall_aeMeasurable n)⟩) l
      (𝓝 ⟨μ.map Z, Measure.isProbabilityMeasure_map aeMeasurable_limit⟩)

lemma tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ) :
    TendstoInDistribution (fun _ ↦ Z) l Z μ where
  forall_aeMeasurable := fun _ ↦ by fun_prop
  tendsto := tendsto_const_nhds

lemma tendstoInDistribution_unique [HasOuterApproxClosed E] [BorelSpace E]
    (X : ι → Ω → E) {Z W : Ω → E} [l.NeBot]
    (h1 : TendstoInDistribution X l Z μ) (h2 : TendstoInDistribution X l W μ) :
    μ.map Z = μ.map W := by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

/-- **Continuous mapping theorem**: if `X n` tends to `Z` in distribution and `g` is continuous,
then `g ∘ X n` tends to `g ∘ Z` in distribution. -/
theorem TendstoInDistribution.continuous_comp {F : Type*} [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E → F} (hg : Continuous g)
    (h : TendstoInDistribution X l Z μ) :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ where
  forall_aeMeasurable := fun n ↦ hg.measurable.comp_aemeasurable (h.forall_aeMeasurable n)
  aeMeasurable_limit := hg.measurable.comp_aemeasurable h.aeMeasurable_limit
  tendsto := by
    have h_tendsto := h.tendsto
    have hX := h.forall_aeMeasurable
    have hZ := h.aeMeasurable_limit
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h_tendsto ⊢
    intro f
    specialize h_tendsto (f.compContinuous ⟨g, hg⟩)
    simp only [ProbabilityMeasure.coe_mk, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk] at h_tendsto
    simp only [ProbabilityMeasure.coe_mk]
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ,
      integral_map (by fun_prop) (by fun_prop)]
    convert h_tendsto with n
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop)]
    · simp
    · exact Measurable.aestronglyMeasurable <| by fun_prop

end TendstoInDistribution

end MeasureTheory
