/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Uniformly distributed measures

In this file we define uniformly distributed measures and prove Christensen's Lemma. As an
application, we prove that the restriction of the `n - 1`-dimensional Hausdorff measure onto an
`n`-dimensional sphere coincides with the spherical measure.

## Main statements

* `isUniformlyDistributed_eq_smul`: Uniformly distributed outer regular measures in a
  pseudometric space are unique up to a finite constant.

-/

@[expose] public section

open Filter MeasureTheory Measure Metric Set

open scoped ENNReal NNReal Topology

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

namespace MeasureTheory

/-- At a point `x` in an open set `U`, if `μ` is nonzero and bounded for small balls centered at
`x`, then the density of `U` at `x` is `1`. -/
lemma exists_density_of_mem_open {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (μ : Measure X) (hμz : ∀ᶠ a in 𝓝[>] 0, 0 < μ (ball x a))
    (hμt : ∀ᶠ a in 𝓝[>] 0, μ (ball x a) < ∞) :
    Tendsto (fun r => μ (U ∩ ball x r) / μ (ball x r)) (𝓝[>] 0) (𝓝 1) := by
  apply EventuallyEq.tendsto
  obtain ⟨r, hr⟩ := Metric.isOpen_iff.1 hU x hx
  filter_upwards [Ioo_mem_nhdsGT hr.1, hμz, hμt] with a ha hz ht
  rw [Set.inter_eq_right.2 ((ball_subset_ball ha.2.le).trans hr.2),
    ENNReal.div_self hz.ne.symm ht.ne]

namespace Measure

class UniformlyDistributed (μ : Measure X) : Prop where
  eq_measure : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x y, μ (ball x r) = μ (ball y r)
  zero_lt : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x, 0 < μ (ball x r)
  lt_top : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x, μ (ball x r) < ⊤

private lemma isUniformlyDistributed_le_smul (μ ν : Measure X) [OpensMeasurableSpace X]
    [UniformlyDistributed μ] [UniformlyDistributed ν] {U : Set X} (hU : IsOpen U) (x : X) :
    μ U ≤ (liminf (fun r => (ν (ball x r))⁻¹ * μ (ball x r)) (𝓝[>] 0)) • (ν U) := calc
  _ = ∫⁻ a in U, liminf (fun r => (ν (ball a r))⁻¹ * ν (U ∩ ball a r)) (𝓝[>] 0) ∂μ := by
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun hU.measurableSet fun x hx => (Tendsto.liminf_eq ?_).symm
    have hνz : ∀ᶠ a in 𝓝[>] 0, 0 < ν (ball x a) := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact UniformlyDistributed.zero_lt ha x
    have hνt : ∀ᶠ a in 𝓝[>] 0, ν (ball x a) < ∞ := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact UniformlyDistributed.lt_top ha x
    apply (exists_density_of_mem_open hU hx ν hνz hνt).congr'
    simp [ENNReal.div_eq_inv_mul]
  -- apply Fatou's lemma
  _ ≤ liminf (fun r => ∫⁻ a in U, (ν (ball a r))⁻¹ * ν (U ∩ ball a r) ∂μ) (𝓝[>] 0) := by sorry
  -- remove the dependence of `ν (ball a r)` on `a`
  _ = liminf (fun r => ∫⁻ a in U, (ν (ball x r))⁻¹ * ν (U ∩ ball a r) ∂μ) (𝓝[>] 0) := by
    apply liminf_congr
    filter_upwards [self_mem_nhdsWithin] with r hr
    have (u : X) : ν (ball u r) = ν (ball x r) := UniformlyDistributed.eq_measure hr u x
    simp_all
  _ = liminf (fun r => (ν (ball x r))⁻¹ * ∫⁻ a in U, ν (U ∩ ball a r) ∂μ) (𝓝[>] 0) := by sorry
  -- apply Fubini
  _ = liminf (fun r => (ν (ball x r))⁻¹ * ∫⁻ a in U, μ (ball a r) ∂ν) (𝓝[>] 0) := by
    congr with r
    have : ∫⁻ a in U, ν (U ∩ ball a r) ∂μ =  ∫⁻ a in U, μ (ball a r) ∂ν := by sorry
    congr
  -- remove the dependence of `μ (ball a r)` on `a`
  _ = liminf (fun r => (ν (ball x r))⁻¹ * ∫⁻ a in U, μ (ball x r) ∂ν) (𝓝[>] 0) := by
    apply liminf_congr
    filter_upwards [self_mem_nhdsWithin] with r hr
    have (u : X) : μ (ball u r) = μ (ball x r) := UniformlyDistributed.eq_measure hr u x
    simp_all
  _ = liminf (fun r => (ν (ball x r))⁻¹ * μ (ball x r) * ν U) (𝓝[>] 0) := by
    congr with r
    rw [mul_assoc]
    have :  ∫⁻ a in U, μ (ball x r) ∂ν = μ (ball x r) * ν U := by rw [setLIntegral_const]
    congr
  _ = _ := by sorry

/-- **Christensen's Lemma**: Uniformly distributed outerregular measures are unique up to
a finite constant. -/
theorem isUniformlyDistributed_eq_smul (μ ν : Measure X) [OpensMeasurableSpace X]
    [OuterRegular μ] [OuterRegular ν] [UniformlyDistributed μ] [UniformlyDistributed ν] :
    ∃ c : ℝ≥0, μ = c • ν := by
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
          filter_upwards [self_mem_nhdsWithin] with a ha
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

end Measure

end MeasureTheory

#min_imports
