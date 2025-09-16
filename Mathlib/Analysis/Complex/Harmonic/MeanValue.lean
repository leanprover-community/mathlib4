/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Analytic

/-!
# The Mean Value Property of Harmonic Functions on the Complex Plane
-/

open InnerProductSpace Metric Real

variable {f : ℂ → ℝ} {c : ℂ} {R : ℝ}

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → ℝ` is harmonic in a neighborhood of a
closed disc of radius `R` and center `c`, then the circle average `circleAverage f c R` equals
`f c`.
-/
theorem HarmonicOnNhd.circleAverage_eq (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
    (isOpen_setOf_harmonicAt f) hf
  rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := harmonic_is_realOfHolomorphic h₂e
  have h₃F : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ F z :=
    fun x hx ↦ (h₁F x (by simp_all [lt_add_of_pos_of_le h₁e hx])).differentiableAt
  have h₄F : Set.EqOn (Complex.reCLM ∘ F) f (sphere c |R|) :=
    fun x hx ↦ h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
  rw [← circleAverage_congr_sphere h₄F, Complex.reCLM.circleAverage_comp_comm,
    circleAverage_of_differentiable_on h₃F]
  · apply h₂F
    simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
  · exact (continuousOn_of_forall_continuousAt
      (fun x hx ↦ (h₃F x (sphere_subset_closedBall hx)).continuousAt)).circleIntegrable'
