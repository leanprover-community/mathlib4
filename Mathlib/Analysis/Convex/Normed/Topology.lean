/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Normed.Basic
import Mathlib.Analysis.Normed.Group.Pointwise

/-!
# Topological properties of convex sets in normed spaces

We prove the following facts:

* `Convex.thickening` : The thickening of a convex set is convex;
* `Convex.cthickening` : The closed thickening of a convex set is convex;
* `isConnected_setOf_sameRay` : The set of vectors in the same ray as `x` is connected;
* `isConnected_setOf_sameRay_and_ne_zero` : The set of nonzero vectors in the same ray as the
  nonzero vector `x` is connected.
-/

variable {E : Type*}

open Metric

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E}

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

instance (priority := 100) NormedSpace.instPathConnectedSpace : PathConnectedSpace E :=
  IsTopologicalAddGroup.pathConnectedSpace

/-- The set of vectors in the same ray as `x` is connected. -/
theorem isConnected_setOf_sameRay (x : E) : IsConnected { y | SameRay ℝ x y } := by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
theorem isConnected_setOf_sameRay_and_ne_zero {x : E} (hx : x ≠ 0) :
    IsConnected { y | SameRay ℝ x y ∧ y ≠ 0 } := by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (continuous_id.smul continuous_const).continuousOn

end SeminormedAddCommGroup
