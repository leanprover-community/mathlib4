/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Regular

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.ENNReal

/-!
# Uniformly distributed measures

In this file we define uniformly distributed measures and prove Christensen's Lemma.

## Main statements

* `UniformlyDistributed.eq_smul`: Uniformly distributed outer regular measures in a
  second countable pseudometric space are unique up to a finite constant. We follow the proof
  in chapter 3 of [*Geometry of sets and measures in {E}uclidean spaces*][mattila1995].

## TODO

Show that the restriction of the `n - 1`-dimensional Hausdorff measure onto an `n`-dimensional
sphere coincides with the spherical measure.

-/

@[expose] public section

open Filter MeasureTheory Measure Metric Set

open scoped ENNReal NNReal Topology

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ ν : Measure X} {U : Set X} {x : X}

namespace MeasureTheory

/-- At a point `x` in an open set `U`, if `μ` is nonzero and bounded for small balls centered at
`x`, then the density of `U` at `x` is `1`. -/
lemma exists_density_of_mem_open (hU : IsOpen U) (hx : x ∈ U)
    (μ : Measure X) (hμz : ∀ᶠ a in 𝓝[>] 0, 0 < μ (ball x a))
    (hμt : ∀ᶠ a in 𝓝[>] 0, μ (ball x a) < ∞) :
    Tendsto (fun r => μ (U ∩ ball x r) / μ (ball x r)) (𝓝[>] 0) (𝓝 1) := by
  apply EventuallyEq.tendsto
  obtain ⟨r, hr⟩ := Metric.isOpen_iff.1 hU x hx
  filter_upwards [Ioo_mem_nhdsGT hr.1, hμz, hμt] with a ha hz ht
  rw [Set.inter_eq_right.2 ((ball_subset_ball ha.2.le).trans hr.2),
    ENNReal.div_self hz.ne.symm ht.ne]

namespace Measure

/-- A measure `μ` is uniformly distributed if the measure of a ball depends only on its radius. -/
class UniformlyDistributed (μ : Measure X) : Prop where
  eq_measure : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x y, μ (ball x r) = μ (ball y r)
  zero_lt : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x, 0 < μ (ball x r)
  lt_top : ∀ ⦃r : ℝ⦄, 0 < r → ∀ x, μ (ball x r) < ⊤

namespace UniformlyDistributed

/-- If a measure is uniformly distributed, then every bounded set has finite measure. -/
theorem measure_ne_top_of_isBounded [UniformlyDistributed μ] (hb : Bornology.IsBounded U) :
    μ U ≠ ∞ := by
  by_cases! hx : Nonempty X
  · apply ne_of_lt
    obtain ⟨r, hr⟩ := hb.subset_ball_lt 0 hx.some
    apply (measure_mono hr.2).trans_lt (lt_top hr.1 hx.some)
  · simp

private lemma le_smul (μ ν : Measure X) [OpensMeasurableSpace X]
    [SecondCountableTopology X] [UniformlyDistributed μ] [UniformlyDistributed ν] (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (x : X) :
    μ U ≤ (liminf (fun r => (ν (ball x r))⁻¹ * μ (ball x r)) (𝓝[>] 0)) • (ν U) :=
  have : IsFiniteMeasure (ν.restrict U) :=
    isFiniteMeasure_restrict.2 (measure_ne_top_of_isBounded hb)
  have hum (r) : Measurable (Function.uncurry fun x => (ball x r).indicator
    fun b => (1 : ℝ≥0∞)) := by
    have : (Function.uncurry fun a => (ball a r).indicator fun b => 1) =
      {p : X × X | dist p.1 p.2 < r}.indicator fun p => (1 : ℝ≥0∞) := by
      ext; simp [Function.uncurry, indicator, dist_comm]
    -- `SecondCountableTopology` is only used for the measurability of the distance function
    exact this ▸ measurable_const.indicator <| measurableSet_lt measurable_dist measurable_const
  calc
  _ = ∫⁻ a in U, liminf (fun r => (ν (ball a r))⁻¹ * ν (U ∩ ball a r)) (𝓝[>] 0) ∂μ := by
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun hU.measurableSet fun x hx => (Tendsto.liminf_eq ?_).symm
    have hνz : ∀ᶠ a in 𝓝[>] 0, 0 < ν (ball x a) := by
      filter_upwards [self_mem_nhdsWithin] with a ha using zero_lt ha x
    have hνt : ∀ᶠ a in 𝓝[>] 0, ν (ball x a) < ∞ := by
      filter_upwards [self_mem_nhdsWithin] with a ha using lt_top ha x
    apply (exists_density_of_mem_open hU hx ν hνz hνt).congr'
    simp [ENNReal.div_eq_inv_mul]
  -- apply Fatou's lemma
  _ ≤ liminf (fun r => ∫⁻ a in U, (ν (ball a r))⁻¹ * ν (U ∩ ball a r) ∂μ) (𝓝[>] 0) := by
    refine lintegral_liminf_le' fun r => (Measurable.mul (Measurable.inv ?_) ?_).aemeasurable
    · have : (fun a => ν (ball a r)) = fun a => ν (ball x r) := by
        ext
        by_cases! hr : 0 < r
        · exact eq_measure hr _ _
        · simp [Metric.ball_eq_empty.2 hr]
      exact this ▸ measurable_const
    · have : (fun a => ν (U ∩ ball a r)) =
        fun a => ∫⁻ b in U, (ball a r).indicator (fun b => 1) b ∂ν := by
        ext; simp [setLIntegral_indicator measurableSet_ball, inter_comm]
      exact this ▸ Measurable.lintegral_prod_right (hum r)
  -- remove the dependence of `ν (ball a r)` on `a`
  _ = liminf (fun r => (ν (ball x r))⁻¹ * ∫⁻ a in U, ν (U ∩ ball a r) ∂μ) (𝓝[>] 0) := by
    apply liminf_congr
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← lintegral_const_mul']
    · grind [fun a => eq_measure (μ := ν) hr a]
    · exact ENNReal.inv_ne_top.2 (zero_lt hr x).ne.symm
  -- apply Fubini
  _ = liminf (fun r => (ν (ball x r))⁻¹ * ∫⁻ a in U, μ (U ∩ ball a r) ∂ν) (𝓝[>] 0) := by
    congr with r
    have : ∫⁻ a in U, ν (U ∩ ball a r) ∂μ =  ∫⁻ a in U, μ (U ∩ ball a r) ∂ν := calc
      _ = ∫⁻ a in U, ∫⁻ b in U, (ball a r).indicator (fun b => 1) b ∂ν ∂μ := by
        refine lintegral_congr fun a => ?_
        simp [setLIntegral_indicator measurableSet_ball, inter_comm]
      _ = ∫⁻ b in U, ∫⁻ a in U, (ball a r).indicator (fun b => 1) b ∂μ ∂ν := by
        have : IsFiniteMeasure (μ.restrict U) :=
          isFiniteMeasure_restrict.2 (measure_ne_top_of_isBounded hb)
        exact lintegral_lintegral_swap (hum r).aemeasurable
      _ = ∫⁻ b in U, ∫⁻ a in U, (ball b r).indicator (fun a => 1) a ∂μ ∂ν := by
        refine setLIntegral_congr_fun hU.measurableSet fun a ha => lintegral_congr fun c => ?_
        simp [indicator, dist_comm]
      _ = _ := by
        refine setLIntegral_congr_fun hU.measurableSet fun b hb => ?_
        rw [setLIntegral_indicator measurableSet_ball, ← setLIntegral_one, inter_comm]
    congr
  _ ≤ liminf (fun r => (ν (ball x r))⁻¹ * ∫⁻ a in U, μ (ball x r) ∂ν) (𝓝[>] 0) := by
    refine liminf_le_liminf ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    gcongr ?_ * (∫⁻ a in U, ?_ ∂ν)
    exact (measure_mono inter_subset_right).trans (eq_measure hr _ _).le
  _ = liminf (fun r => (ν (ball x r))⁻¹ * μ (ball x r) * ν U) (𝓝[>] 0) := by
    congr with r
    rw [mul_assoc, setLIntegral_const]
  _ = _ := by
    simp [ENNReal.liminf_mul_const_of_ne_top (measure_ne_top_of_isBounded hb), mul_comm (ν U)]

/-- **Christensen's Lemma**: Uniformly distributed outerregular measures are unique up to
a finite constant. -/
theorem eq_smul (μ ν : Measure X) [OpensMeasurableSpace X] [SecondCountableTopology X]
    [OuterRegular μ] [OuterRegular ν] [UniformlyDistributed μ] [UniformlyDistributed ν] :
    ∃ c : ℝ≥0, μ = c • ν := by
  by_cases! hX : IsEmpty X
  · simp [eq_zero_of_isEmpty]
  · obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ∀ U, IsOpen U → Bornology.IsBounded U → μ U = (c • ν) U := by
      refine ⟨liminf (fun r => (ν (ball hX.some r))⁻¹ * μ (ball hX.some r)) (𝓝[>] 0),
        fun U hU hb => le_antisymm (le_smul μ ν hU hb hX.some) ?_⟩
      calc
      _ ≤ (limsup (fun r ↦ (ν (ball hX.some r))⁻¹ * μ (ball hX.some r)) (𝓝[>] 0)) *
        ((liminf (fun r => (μ (ball hX.some r))⁻¹ * ν (ball hX.some r)) (𝓝[>] 0)) * (μ U)) := by
        simp only [smul_apply, smul_eq_mul]
        gcongr
        · exact liminf_le_limsup
        · exact le_smul ν μ hU hb hX.some
      _ = (liminf (fun r => (μ (ball hX.some r))⁻¹ * ν (ball hX.some r)) (𝓝[>] 0))⁻¹ *
        ((liminf (fun r => (μ (ball hX.some r))⁻¹ * ν (ball hX.some r)) (𝓝[>] 0)) * (μ U)) := by
        rw [ENNReal.inv_liminf]
        have : limsup (fun r ↦ (ν (ball hX.some r))⁻¹ * μ (ball hX.some r)) (𝓝[>] 0) =
          limsup (fun i ↦ ((μ (ball hX.some i))⁻¹ * ν (ball hX.some i))⁻¹) (𝓝[>] 0) := by
          apply limsup_congr
          filter_upwards [self_mem_nhdsWithin] with a ha
          rw [ENNReal.mul_inv, mul_comm, inv_inv]
          · exact Or.inr (lt_top ha hX.some).ne
          · exact Or.inr (zero_lt ha hX.some).ne.symm
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
          simp [h, ENNReal.top_mul (zero_lt _ hX.some).ne.symm]
        _ = μ (ball hX.some 1) := (hc (ball hX.some 1) isOpen_ball isBounded_ball).symm
        _ < _ := lt_top (by grind) hX.some
      grind
    have : (c • ν).OuterRegular := OuterRegular.smul ν hci
    exact (ENNReal.exists_ne_top (p := fun r => μ = r • ν)).1
      ⟨c, hci, OuterRegular.ext_isOpen_isBounded fun U hU hb => hc U hU hb⟩

end UniformlyDistributed

end Measure

end MeasureTheory
