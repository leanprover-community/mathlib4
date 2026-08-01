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

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℂ → 𝕜} {c : ℂ} {R : ℝ}

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → 𝕜` is harmonic in a neighborhood of
a closed disc of radius `|R|` and center `c`, then the circle average `circleAverage f c R` equals
`f c`.
-/
theorem HarmonicOnNhd.circleAverage_eq (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  have h_circle : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have meanValue (L : 𝕜 →L[ℝ] ℝ) : L (circleAverage f c R) = L (f c) := by
    rw [← L.circleAverage_comp_comm h_circle]
    obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
      (isOpen_setOfPred_harmonicAt (L ∘ f)) (hf.comp_CLM L)
    rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
    obtain ⟨F, h₁F, h₂F⟩ :=
      InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
    have h₃F : DifferentiableOn ℂ F (closure (ball c |R|)) := by
      intro x hx
      apply (h₁F x _).differentiableWithinAt
      grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
    have h₄F : Set.EqOn (Complex.reCLM ∘ F) (L ∘ f) (sphere c |R|) :=
      fun x hx ↦ h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
    rw [← circleAverage_congr_sphere h₄F, Complex.reCLM.circleAverage_comp_comm,
      h₃F.diffContOnCl.circleAverage]
    · apply h₂F
      simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
    · apply (h₁F.continuousOn.mono (fun _ _ ↦ by simp_all [dist_eq_norm])).circleIntegrable'
  exact RCLike.ext (meanValue RCLike.reCLM) (meanValue RCLike.imCLM)

/--
The **Mean Value Property** of harmonic functions: If `f : ℂ → 𝕜` is harmonic on a disc of radius
`|R|` and center `c` and continuous on its closure, then the circle average `circleAverage f c R`
equals `f c`.
-/
theorem HarmonicContOnCl.circleAverage_eq (h₁f : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  have h_circle : CircleIntegrable f c R := by
    by_cases hR : R = 0
    · simp [hR]
    apply (h₁f.2.mono ?_).circleIntegrable'
    rw [closure_ball _ (abs_ne_zero.mpr hR)]
    exact sphere_subset_closedBall
  have meanValue (L : 𝕜 →L[ℝ] ℝ) : L (circleAverage f c R) = L (f c) := by
    rw [← L.circleAverage_comp_comm h_circle]
    let hL : HarmonicContOnCl (L ∘ f) (ball c |R|) :=
      ⟨h₁f.1.comp_CLM L, L.continuous.comp_continuousOn h₁f.2⟩
    by_cases hR : R = 0
    · simp_all
    have H : ContinuousOn (circleAverage (L ∘ f) c) (Set.Ioc 0 |R|) := by
      refine (hL.2.mono ?_).circleAverage (fun z hz ↦ hz.1.le)
      intro x hx
      rw [closure_ball _ (by aesop), mem_closedBall_iff_norm]
      exact hx.2
    rw [← circleAverage_abs_radius]
    apply H.eq_of_eqOn_Ioo (by aesop)
    intro r hr
    apply HarmonicOnNhd.circleAverage_eq
    exact hL.1.mono (by simpa [abs_of_pos hr.1] using closedBall_subset_ball hr.2)
  exact RCLike.ext (meanValue RCLike.reCLM) (meanValue RCLike.imCLM)
