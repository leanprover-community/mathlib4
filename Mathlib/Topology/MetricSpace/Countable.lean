/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.Real.Cardinality

/-!
# Properties of countable metric spaces.

-/

open Set

universe u

variable {γ : Type u} [MetricSpace γ]
variable {s : Set γ}

namespace Metric

section TotallyDisconnected

open Function (uncurry) in
/-- Countable metric spaces are totally disconnected. -/
instance instTotallyDisconnectedSpace_of_countable
    [Countable γ] :
    TotallyDisconnectedSpace γ := by
  generalize hR : {r | ∃ x y : γ, dist x y = r} = R
  have rc : R.Countable := by
    have e : R = range (uncurry (dist (α := γ))) := by apply Set.ext; intro r; simp [← hR]
    rw [e]; exact countable_range _
  refine @TotallySeparatedSpace.totallyDisconnectedSpace _ _ ?_
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y xy
  rw [← dist_pos] at xy
  have h : ¬Ioo 0 (dist x y) ⊆ R := by
    by_contra h; have h' := (rc.mono h)
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real xy] at h'
    exact (not_le.mpr (Cardinal.cantor _)) h'
  simp only [not_subset, mem_Ioo] at h; rcases h with ⟨r, ⟨rp, rxy⟩, rr⟩
  have e : ball x r = closedBall x r := by
    apply Set.ext; intro z; simp only [mem_ball, mem_closedBall]
    simp only [mem_setOf, not_exists, ← hR] at rr; simp [Ne.le_iff_lt (rr z x)]
  refine ⟨ball x r, ⟨?_, isOpen_ball⟩, ?_⟩
  · simpa [e] using isClosed_closedBall;
  use mem_ball_self rp; simpa [dist_comm] using rxy.le

/-- Countable subsets of metric spaces are totally disconnected. -/
theorem Countable.isTotallyDisconnected (hs : Countable s) :
    IsTotallyDisconnected s := by
  rw [← totallyDisconnectedSpace_subtype_iff]
  exact @instTotallyDisconnectedSpace_of_countable _ _ (countable_coe_iff.mpr hs)

end TotallyDisconnected

end Metric
