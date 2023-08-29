/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Instances.Int

#align_import topology.instances.nat from "leanprover-community/mathlib"@"620af85adf5cd4282f962eb060e6e562e3e0c0ba"

/-!
# Topology on the natural numbers

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/

noncomputable section

open Metric Set Filter

namespace Nat

noncomputable instance : Dist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = |(x : ℝ) - y| := rfl
#align nat.dist_eq Nat.dist_eq

theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y := rfl
#align nat.dist_coe_int Nat.dist_coe_int

@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y := rfl
#align nat.dist_cast_real Nat.dist_cast_real

theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n := fun m n hne =>
  Int.pairwise_one_le_dist <| by exact_mod_cast hne
                                 -- 🎉 no goals
#align nat.pairwise_one_le_dist Nat.pairwise_one_le_dist

theorem uniformEmbedding_coe_real : UniformEmbedding ((↑) : ℕ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.uniform_embedding_coe_real Nat.uniformEmbedding_coe_real

theorem closedEmbedding_coe_real : ClosedEmbedding ((↑) : ℕ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.closed_embedding_coe_real Nat.closedEmbedding_coe_real

instance : MetricSpace ℕ := Nat.uniformEmbedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℕ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl
#align nat.preimage_ball Nat.preimage_ball

theorem preimage_closedBall (x : ℕ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl
#align nat.preimage_closed_ball Nat.preimage_closedBall

theorem closedBall_eq_Icc (x : ℕ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_lt 0 r with (hr | hr)
  -- ⊢ closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊
  · rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
    -- ⊢ 0 ≤ ↑x + r
    exact add_nonneg (cast_nonneg x) hr
    -- 🎉 no goals
  · rw [closedBall_eq_empty.2 hr, Icc_eq_empty_of_lt]
    -- ⊢ ⌊↑x + r⌋₊ < ⌈↑x - r⌉₊
    calc ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := floor_mono <| by linarith
    _ < ⌈↑x - r⌉₊ := by
      rw [floor_coe, Nat.lt_ceil]
      linarith
#align nat.closed_ball_eq_Icc Nat.closedBall_eq_Icc

instance : ProperSpace ℕ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    -- ⊢ IsCompact (Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊)
    exact (Set.finite_Icc _ _).isCompact⟩
    -- 🎉 no goals

instance : NoncompactSpace ℕ :=
  noncompactSpace_of_neBot <| by simp [Filter.atTop_neBot]
                                 -- 🎉 no goals

end Nat

