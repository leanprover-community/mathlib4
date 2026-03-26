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

* `isUniformlyDistributed_eq_smul`: Uniformly distributed outer regular measures in a
  pseudometric space are unique up to a finite constant.
* `hausdorff_eq_measure.toSphere` : The restriction of the `n - 1`-dimensional Hausdorff measure
  onto an `n`-dimensional sphere coincides with the spherical measure.

-/

open Filter MeasureTheory Measure Metric Set

open scoped ENNReal NNReal Topology

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

namespace MeasureTheory

lemma exists_density_of_mem_open {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) (μ : Measure X) :
    Tendsto (fun r => μ (U ∩ ball x r) / μ (ball x r)) (𝓝 0) (𝓝 1) := by
  sorry

namespace Measure

class UniformlyDistributed (μ : Measure X) : Prop where
  eq_measure : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x y, μ (ball x r) = μ (ball y r)
  zero_lt : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x, 0 < μ (ball x r)
  lt_top : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x, μ (ball x r) < ⊤

private lemma isUniformlyDistributed_le_smul (μ ν : Measure X) {U : Set X} (hU : IsOpen U) (x : X) :
    μ U ≤ (liminf (fun r => (ν (ball x r))⁻¹ * μ (ball x r)) (𝓝[>] 0)) • (ν U) := by
  sorry

/-- **Christensen's Lemma**: Uniformly distributed outerregular measures are unique up to
a finite constant. -/
theorem isUniformlyDistributed_eq_smul (μ ν : Measure X) [OuterRegular μ] [OuterRegular ν]
    [UniformlyDistributed μ] [UniformlyDistributed ν] : ∃ c : ℝ≥0, μ = c • ν := by
  by_cases! hX : IsEmpty X
  · simp [eq_zero_of_isEmpty]
  · obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ∀ U, IsOpen U → μ U = (c • ν) U := by
      refine ⟨liminf (fun r => (ν (ball hX.some r))⁻¹ * μ (ball hX.some r)) (𝓝[>] 0),
        fun U hU => le_antisymm (isUniformlyDistributed_le_smul μ ν hU hX.some) ?_⟩
      calc
      _ ≤ (limsup (fun r ↦ (ν (ball hX.some r))⁻¹ * μ (ball hX.some r)) (𝓝[>] 0)) *
        ((liminf (fun r => (μ (ball hX.some r))⁻¹ * ν (ball hX.some r)) (𝓝[>] 0)) * (μ U)) := by
        simp only [smul_apply, smul_eq_mul]
        gcongr
        · exact liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
        · exact isUniformlyDistributed_le_smul ν μ hU hX.some
      _ = (liminf (fun r => (μ (ball hX.some r))⁻¹ * ν (ball hX.some r)) (𝓝[>] 0))⁻¹ *
        ((liminf (fun r => (μ (ball hX.some r))⁻¹ * ν (ball hX.some r)) (𝓝[>] 0)) * (μ U)) := by
        rw [ENNReal.inv_liminf]
        have : limsup (fun r ↦ (ν (ball hX.some r))⁻¹ * μ (ball hX.some r)) (𝓝[>] 0) =
          limsup (fun i ↦ ((μ (ball hX.some i))⁻¹ * ν (ball hX.some i))⁻¹) (𝓝[>] 0) := by
          apply limsup_congr
          have : Ioi 0 ∈ 𝓝[>] (0 : ℝ) := by
            rw [mem_nhdsGT_iff_exists_Ioo_subset]
            exact ⟨1, by grind, by grind⟩
          filter_upwards [this] with a ha
          rw [ENNReal.mul_inv, mul_comm, inv_inv]
          · exact Or.inr (UniformlyDistributed.lt_top ha hX.some).ne
          · exact Or.inr (UniformlyDistributed.zero_lt ha hX.some).ne.symm
        congr
      _ ≤ (μ U) := by
        nth_rw 2 [← one_mul (μ U)]
        rw [← mul_assoc]
        gcongr
        apply ENNReal.inv_mul_le_one
    have hci : c ≠ ∞ := by
      intro h
      have : ∞ < ∞ := calc
        _ = c • ν (ball hX.some 1) := by
          simp [h, ENNReal.top_mul (UniformlyDistributed.zero_lt _ hX.some).ne.symm]
        _ = μ (ball hX.some 1) := (hc (ball hX.some 1) isOpen_ball).symm
        _ < _ := UniformlyDistributed.lt_top (by grind) hX.some
      grind
    have : (c • ν).OuterRegular := OuterRegular.smul ν hci
    exact (ENNReal.exists_ne_top (p := fun r => μ = r • ν)).1
      ⟨c, hci, OuterRegular.ext_isOpen fun U hU => hc U hU⟩

variable {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

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

end Measure

end MeasureTheory

#min_imports
