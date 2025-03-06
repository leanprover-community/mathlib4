/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric distances on pi types

This file contains results on the behavior of ultrametrics in products of ultrametric spaces.

## Main results

* `Pi.instIsUltrametricDist`: a product of ultrametric spaces is ultrametric.


ultrametric, nonarchimedean
-/

instance Pi.instIsUltrametricDist {ι : Type*} {X : ι → Type*} [Fintype ι]
    [(i : ι) → PseudoMetricSpace (X i)] [(i : ι) → IsUltrametricDist (X i)] :
    IsUltrametricDist ((i : ι) → X i) := by
  constructor
  intro f g h
  simp only [le_sup_iff]
  rw [dist_pi_le_iff dist_nonneg, dist_pi_le_iff dist_nonneg, dist_pi_def, dist_pi_def]
  by_cases H : ∃ i, ∀ j, dist (f j) (g j) ≤ dist (g i) (h i)
  · obtain ⟨i, hi⟩ := H
    refine Or.inr ?_
    intro j
    refine (IsUltrametricDist.dist_triangle_max (f j) (g j) (h j)).trans
      (sup_le ((hi _).trans ?_) ?_) <;>
    · simpa using Finset.le_sup (f := fun i ↦ nndist (g i) (h i)) (Finset.mem_univ _)
  · push_neg at H
    refine Or.inl ?_
    intro i
    obtain ⟨j, hj⟩ := H i
    refine (IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)).trans
      (sup_le ?_ (hj.le.trans ?_)) <;>
    simpa using Finset.le_sup (f := fun i ↦ nndist (f i) (g i)) (Finset.mem_univ _)
