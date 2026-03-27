/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl

/-!
# The Mean Value Property of Harmonic Functions on the Complex Plane
-/

public section

open InnerProductSpace Metric Real

variable {f : ℂ → ℝ} {c : ℂ} {R : ℝ}

set_option backward.isDefEq.respectTransparency false in
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
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c |R|)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (Complex.reCLM ∘ F) f (sphere c |R|) :=
    fun x hx ↦ h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
  rw [← circleAverage_congr_sphere h₄F, Complex.reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage]
  · apply h₂F
    simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
  · apply (h₁F.continuousOn.mono (fun _ _ ↦ by simp_all [dist_eq_norm])).circleIntegrable'

set_option backward.isDefEq.respectTransparency false in
/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → ℝ` is harmonic on a disc of radius
`|R|` and center `c` and continuous on its closure, then the circle average `circleAverage f c R`
equals `f c`.
-/
theorem HarmonicContOnCl.circleAverage_eq {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (h₁f : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp_all
  have H : ContinuousOn (circleAverage f c) (Set.Ioc 0 |R|) := by
    refine (h₁f.2.mono ?_).circleAverage (fun z hz ↦ hz.1.le)
    intro x hx
    rw [closure_ball _ (by aesop), mem_closedBall_iff_norm]
    exact hx.2
  rw [← circleAverage_abs_radius]
  apply H.eq_of_eqOn_Ioo (by aesop)
  · intro r hr
    apply HarmonicOnNhd.circleAverage_eq
    · apply h₁f.1.mono
      rw [abs_of_pos hr.1]
      exact closedBall_subset_ball hr.2
