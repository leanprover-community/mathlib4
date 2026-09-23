/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Lemmas about distances between points in intervals in `ℝ`.
-/

public section

open Bornology Filter Metric Set
open scoped NNReal Topology

namespace Real

variable {ι : Type*}

lemma dist_left_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist x y ≤ dist x z := by
  simpa only [dist_comm x] using abs_sub_left_of_mem_uIcc h

lemma dist_right_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist y z ≤ dist x z := by
  simpa only [dist_comm _ z] using abs_sub_right_of_mem_uIcc h

lemma dist_le_of_mem_uIcc {x y x' y' : ℝ} (hx : x ∈ uIcc x' y') (hy : y ∈ uIcc x' y') :
    dist x y ≤ dist x' y' :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])

lemma dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ y' - x' := by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)

lemma dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist x y ≤ 1 := by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy

variable [Fintype ι] {x y x' y' : ι → ℝ}

lemma dist_le_of_mem_pi_Icc (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') : dist x y ≤ dist x' y' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun b =>
    (Real.dist_le_of_mem_uIcc ?_ ?_).trans (dist_le_pi_dist x' y' b) <;> refine Icc_subset_uIcc ?_
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]

end Real
