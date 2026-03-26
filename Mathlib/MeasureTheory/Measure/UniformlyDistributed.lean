/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Uniformly distributed measures

In this file we define uniformly distributed measures and prove Christensen's Lemma. As an
application, we prove that the restriction of the `n - 1`-dimensional Hausdorff measure onto an
`n`-dimensional sphere coincides with the spherical measure.

## Main statements

* `uniformly_dist_unique`: Uniformly distributed outer regular measures in a pseudometric space
  are unique up to a finite constant.
* `hausdorff_eq_measure.toSphere` : The restriction of the `n - 1`-dimensional Hausdorff measure
  onto an `n`-dimensional sphere coincides with the spherical measure.

-/

open MeasureTheory Measure Metric Filter Topology
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {μ ν : Measure X}

class UniformlyDistributed (μ : Measure X) : Prop where
  uniformlydistributed :
    ∀ ⦃r : ℝ⦄, 0 < r → ∀ x y : X, μ (ball x r) = μ (ball y r) ∧ 0 < μ (ball x r) ∧ μ (ball x r) < ⊤

lemma density_exists {U : Set X} (hU : IsOpen U) :

/-- **Christensen's Lemma**: Uniformly distributed outerregular measures are unique up to
a finite constant. -/
theorem uniformly_dist_unique [OuterRegular μ] [OuterRegular ν]
    [UniformlyDistributed μ] [UniformlyDistributed ν] : ∃ c : NNReal, μ = c • ν := by
  by_cases IsEmpty X
  · simp [eq_zero_of_isEmpty]
  · simp_all only [not_isEmpty_iff]
    let x := Classical.choice ‹_›
    let g : ℝ → ENNReal := fun r ↦ μ (ball x r)
    let h : ℝ → ENNReal := fun r ↦ ν (ball x r)
    have hc : ∃ c : NNReal, Tendsto (fun r ↦ g r / h r) (𝓝[>] 0) (𝓝 c) := by sorry
    obtain ⟨c, pc⟩ := hc
    use c
    apply OuterRegular.ext_isOpen
    intro U hU
    sorry

variable {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- The spherical measure is outer regular. -/
instance measure_toSphere_outer_regular (m : Measure E) [m.IsAddHaarMeasure] :
    OuterRegular m.toSphere := by
  exact
    (WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
        m.toSphere).toOuterRegular

/-- The spherical measure is uniformly distributed. -/
instance measure_toSphere_uniformlydist (m : Measure E) (he : 0 < Module.finrank ℝ E)
    [m.IsAddHaarMeasure] : UniformlyDistributed m.toSphere := by
  constructor
  intro r hr x y
  constructor
  · rw [toSphere_apply' _ measurableSet_ball, toSphere_apply' _ measurableSet_ball]
    refine (ENNReal.mul_right_inj ?_ ?_).mpr ?_
    · sorry
    · sorry
    · sorry
  · constructor
    · rw [toSphere_apply' _ measurableSet_ball]
      refine CanonicallyOrderedAdd.mul_pos.mpr ⟨by simp [he], ?_⟩
      refine measure_pos_of_nonempty_interior m ?_
      sorry
    · exact measure_ball_lt_top

instance hausdorffMeasure_outerRegular (d : ℝ) : OuterRegular (μH[d] : Measure E) := by sorry

instance hausdorffMeasure_restirct_sphere_outerRegular : OuterRegular
    (μH[↑(Module.finrank ℝ E) - 1].comap Subtype.val : Measure (sphere (0 : E) 1)) := by
  refine OuterRegular.comap' μH[↑(Module.finrank ℝ E) - 1] ?_ ?_

instance hausdorffMeasure_restrict_sphere_uniformlydist : UniformlyDistributed
    (μH[↑(Module.finrank ℝ E) - 1].comap Subtype.val : Measure (sphere (0 : E) 1)) := by
  sorry

/-- The restriction of the `n - 1`-dimensional Hausdorff measure onto an `n`-dimensional sphere
coincides with the spherical measure. -/
theorem hausdorff_eq_measure.toSphere (m : Measure E) [m.IsAddHaarMeasure] :
    (μH[↑(Module.finrank ℝ E) - 1].comap Subtype.val : Measure (sphere (0 : E) 1)) =
    m.toSphere := by
  sorry

#min_imports
