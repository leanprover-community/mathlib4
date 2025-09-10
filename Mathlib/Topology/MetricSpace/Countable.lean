/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang
-/
import Mathlib.Analysis.Real.Cardinality

/-!
# Properties of countable metric spaces.

-/

open Function Set

variable {γ : Type*} [MetricSpace γ]

namespace Metric

section TotallyDisconnected

/-- Countable metric spaces are totally separated. -/
instance instTotallySeparatedSpace_of_countable [Countable γ] :
    TotallySeparatedSpace γ := by
  let R := {r | ∃ x y : γ, dist x y = r}
  have hR : R.Countable := by
    have hR₁ : R = range (uncurry (dist (α := γ))) := by apply Set.ext; intro r; simp [R]
    rw [hR₁]; exact countable_range _
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  rw [← dist_pos] at hxy
  have h : ¬Ioo 0 (dist x y) ⊆ R := by
    by_contra h; have h' := (hR.mono h)
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real hxy] at h'
    exact (not_le.mpr (Cardinal.cantor _)) h'
  simp only [not_subset, mem_Ioo] at h; rcases h with ⟨r, ⟨rp, rxy⟩, rr⟩
  have hball : ball x r = closedBall x r := by
    apply Set.ext; intro z; simp only [mem_ball, mem_closedBall]
    simp only [mem_setOf, not_exists, R] at rr; simp [Ne.le_iff_lt (rr z x)]
  refine ⟨ball x r, ⟨?_, isOpen_ball⟩, ?_⟩
  · simpa [hball] using isClosed_closedBall;
  use mem_ball_self rp; simpa [dist_comm] using rxy.le

/-- Countable subsets of metric spaces are totally disconnected. -/
theorem Countable.isTotallyDisconnected {s : Set γ} (hs : Countable s) :
    IsTotallyDisconnected s :=
  totallyDisconnectedSpace_subtype_iff.mp inferInstance

end TotallyDisconnected

end Metric
