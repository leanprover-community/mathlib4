/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Module.Dual

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing B] [NormedAlgebra 𝕜 B]

--variable {L : Subspace 𝕜 B} (h : 1 ∈ L)

#check NormedSpace.Dual 𝕜 B


#check Metric.closedBall 0 1

variable (B)

def StateSpace := {x : NormedSpace.Dual 𝕜 B | x ∈ Metric.closedBall 0 1 ∧ x 1 = 1 }

variable {y : NormedSpace.Dual 𝕜 B}

#check ‖y‖

lemma ss_subset_unitball : StateSpace B ⊆ (Metric.closedBall 0 1 : Set (NormedSpace.Dual 𝕜 B)) :=
  fun _ hy => Set.mem_of_mem_inter_left hy

lemma ss_norm_one {y : NormedSpace.Dual 𝕜 B} (h : y ∈ StateSpace B) : ‖y‖ = 1 := by
  apply le_antisymm_iff.mpr
  rw [StateSpace] at h
  simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq] at h
  constructor
  · exact h.1
  · 
