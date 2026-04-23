/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Uniformly locally doubling measures

A uniformly locally doubling measure `μ` on a metric space is a measure for which there exists a
constant `C` such that for all sufficiently small radii `ε`, and for any centre, the measure of a
ball of radius `2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic facts about uniformly locally doubling measures.

## Main definitions

  * `IsUnifLocDoublingMeasure`: the definition of a uniformly locally doubling measure (as a
    typeclass).
  * `IsUnifLocDoublingMeasure.doublingConstant`: a function yielding the doubling constant `C`
    appearing in the definition of a uniformly locally doubling measure.
-/

@[expose] public section

assert_not_exists Real.instPow

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace ENNReal NNReal Topology

/-- A measure `μ` is said to be a uniformly locally doubling measure if there exists a constant `C`
such that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

Note: it is important that this definition makes a demand only for sufficiently small `ε`. For
example we want hyperbolic space to carry the instance `IsUnifLocDoublingMeasure volume` but
volumes grow exponentially in hyperbolic space. To be really explicit, consider the hyperbolic plane
of curvature -1, the area of a disc of radius `ε` is `A(ε) = 2π(cosh(ε) - 1)` so
`A(2ε)/A(ε) ~ exp(ε)`. -/
class IsUnifLocDoublingMeasure {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  (μ : Measure α) : Prop where
  exists_measure_closedBall_le_mul'' :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε)

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

theorem exists_measure_closedBall_le_mul :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε) :=
  exists_measure_closedBall_le_mul''

/-- A doubling constant for a uniformly locally doubling measure.

See also `IsUnifLocDoublingMeasure.scalingConstantOf`. -/
def doublingConstant : ℝ≥0 :=
  Classical.choose <| exists_measure_closedBall_le_mul μ

theorem eventually_measure_le_doublingConstant_mul :
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ doublingConstant μ * μ (closedBall x ε) :=
  Classical.choose_spec <| exists_measure_closedBall_le_mul μ

@[deprecated (since := "2025-12-17")]
alias exists_measure_closedBall_le_mul' := eventually_measure_le_doublingConstant_mul

theorem exists_eventually_forall_measure_closedBall_le_mul (K : ℝ) :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, ∀ t ≤ K, μ (closedBall x (t * ε)) ≤ C * μ (closedBall x ε) := by
  let C := doublingConstant μ
  suffices ∀ n,
      ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x ((2 : ℝ) ^ n * ε)) ≤ C ^ n * μ (closedBall x ε) by
    rcases pow_unbounded_of_one_lt K one_lt_two with ⟨n, hn⟩
    use C ^ n
    filter_upwards [eventually_mem_nhdsWithin, this n] with ε hε₀ hε x t ht
    rw [mem_Ioi] at hε₀
    grw [ht, hn, ENNReal.coe_pow]
    exact hε x
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
    replace ihn := eventually_nhdsGT_zero_mul_left (two_pos : 0 < (2 : ℝ)) ihn
    filter_upwards [ihn, eventually_measure_le_doublingConstant_mul μ] with ε hεn hε x
    grw [pow_succ, mul_assoc, hεn, hε, ← mul_assoc, pow_succ]

/-- A variant of `IsUnifLocDoublingMeasure.doublingConstant` which allows for scaling the
radius by values other than `2`. -/
def scalingConstantOf (K : ℝ) : ℝ≥0 :=
  max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1

@[simp]
theorem one_le_scalingConstantOf (K : ℝ) : 1 ≤ scalingConstantOf μ K :=
  le_max_of_le_right <| le_refl 1

theorem eventually_measure_mul_le_scalingConstantOf_mul (K : ℝ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ x t r, t ∈ Ioc 0 K → r ≤ R →
          μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) := by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closedBall_le_mul μ K)
  rcases mem_nhdsGT_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine ⟨R, Rpos, fun x t r ht hr => ?_⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg ht.1 rneg
    simp only [closedBall_eq_empty.2 this, measure_empty, zero_le]
  · simp only [mul_zero]
    refine le_mul_of_one_le_of_le ?_ le_rfl
    apply ENNReal.one_le_coe_iff.2 (le_max_right _ _)
  · apply (hR ⟨rpos, hr⟩ x t ht.2).trans
    gcongr
    apply le_max_left

theorem eventually_measure_le_scaling_constant_mul (K : ℝ) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x, μ (closedBall x (K * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) := by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closedBall_le_mul μ K)] with r hr x
  grw [hr x K le_rfl, scalingConstantOf, ← le_max_left]

theorem eventually_measure_le_scaling_constant_mul' (K : ℝ) (hK : 0 < K) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x,
      μ (closedBall x r) ≤ scalingConstantOf μ K⁻¹ * μ (closedBall x (K * r)) := by
  convert eventually_nhdsGT_zero_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  simp [inv_mul_cancel_left₀ hK.ne']

/-- A scale below which the doubling measure `μ` satisfies good rescaling properties when one
multiplies the radius of balls by at most `K`, as stated
in `IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul`. -/
def scalingScaleOf (K : ℝ) : ℝ :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose

theorem scalingScaleOf_pos (K : ℝ) : 0 < scalingScaleOf μ K :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1

theorem measure_mul_le_scalingConstantOf_mul {K : ℝ} {x : α} {t r : ℝ} (ht : t ∈ Ioc 0 K)
    (hr : r ≤ scalingScaleOf μ K) :
    μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr

end IsUnifLocDoublingMeasure
