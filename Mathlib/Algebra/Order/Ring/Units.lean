/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.GroupTheory.Index

/-! # Lemmas about units of ordered rings -/

public section

lemma Units.index_posSubgroup (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    (posSubgroup R).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun a ↦ ?_⟩
  obtain h | h := lt_or_gt_of_ne a.ne_zero
  · simp [h, h.le]
  · simp [h, xor_comm, h.le]
