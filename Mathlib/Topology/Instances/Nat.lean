/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Instances.Int
import Mathlib.Data.Nat.Lattice

/-!
# Topology on the natural numbers

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/

noncomputable section

open Filter Metric Set Topology

namespace Nat

noncomputable instance : Dist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = |(x : ℝ) - y| := rfl

theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y := rfl

@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y := rfl

theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n := fun _ _ hne =>
  Int.pairwise_one_le_dist <| mod_cast hne

theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : ℕ → ℝ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_coe_real := isUniformEmbedding_coe_real

theorem isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : ℕ → ℝ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_coe_real := isClosedEmbedding_coe_real

instance : MetricSpace ℕ := Nat.isUniformEmbedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℕ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl

theorem preimage_closedBall (x : ℕ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl

theorem closedBall_eq_Icc (x : ℕ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_lt 0 r with (hr | hr)
  · rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
    exact add_nonneg (cast_nonneg x) hr
  · rw [closedBall_eq_empty.2 hr, Icc_eq_empty_of_lt]
    calc ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := floor_mono <| by linarith
    _ < ⌈↑x - r⌉₊ := by
      rw [floor_natCast, Nat.lt_ceil]
      linarith

instance : ProperSpace ℕ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

instance : NoncompactSpace ℕ :=
  noncompactSpace_of_neBot <| by simp [Filter.atTop_neBot]

end Nat
