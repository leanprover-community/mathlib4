/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Yi Yuan
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl

/-!
# The Mean Value Property of Vector-Valued Harmonic Functions

This file establishes the mean value property for harmonic functions `f : ℂ → F`, where `F` is an
arbitrary complete real normed vector space. This generalizes the mean value property for
real-valued harmonic functions.

Completeness of `F` cannot be dropped: `circleAverage` is defined in terms of the Bochner integral,
which is junk (zero) whenever the target space is incomplete.

The proof reduces to the real-valued case. Circle averages commute with continuous linear maps, and
composition with continuous linear maps preserves harmonicity. Thus, `g (circleAverage f c R)`
equals `circleAverage (g ∘ f) c R = g (f c)` for every continuous linear functional `g : F →L[ℝ] ℝ`.
Since continuous linear functionals separate the points of a normed space (Hahn-Banach, in the form
of `SeparatingDual.eq_iff_forall_dual_eq`), this suffices.
-/

public section

open InnerProductSpace Metric Real

namespace InnerProductSpace

/-!
## Compatibility of `HarmonicContOnCl` with Linear Maps
-/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/--
Compositions of continuous ℝ-linear maps with functions that are harmonic on a set and continuous
on its closure are again harmonic on the set and continuous on its closure.
-/
theorem HarmonicContOnCl.comp_CLM {f : E → F} {s : Set E} (h : HarmonicContOnCl f s)
    (l : F →L[ℝ] G) : HarmonicContOnCl (l ∘ f) s :=
  ⟨h.1.comp_CLM l, l.continuous.comp_continuousOn h.2⟩

end

/-!
## The Mean Value Property
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {f : ℂ → F} {c : ℂ} {R : ℝ}

/--
The Mean Value Property of harmonic functions: If f : ℂ → F is harmonic in a neighborhood of a
closed disc of radius R and center c, then the circle average circleAverage f c R equals
f c.
-/
theorem HarmonicOnNhd.circleAverage_eq (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt (g ∘ f)) (hf.comp_CLM g)
  rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn ℂ F (closure (ball c |R|)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (Complex.reCLM ∘ F) (⇑g ∘ f) (sphere c |R|) :=
    fun x hx ↦ h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
  rw [← circleAverage_congr_sphere h₄F, Complex.reCLM.circleAverage_comp_comm,
    h₃F.diffContOnCl.circleAverage]
  · apply h₂F
    simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
  · apply (h₁F.continuousOn.mono (fun _ _ ↦ by simp_all [dist_eq_norm])).circleIntegrable'

/--
The Mean Value Property of harmonic functions: If f : ℂ → F is harmonic on a disc of radius
|R| and center c and continuous on its closure, then the circle average circleAverage f c R
equals f c.
-/
theorem HarmonicContOnCl.circleAverage_eq (hf : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  by_cases hR : R = 0
  · simp_all
  have H : ContinuousOn (circleAverage (g ∘ f) c) (Set.Ioc 0 |R|) := by
    refine ((hf.comp_CLM g).2.mono ?_).circleAverage (fun z hz ↦ hz.1.le)
    intro x hx
    rw [closure_ball _ (by aesop), mem_closedBall_iff_norm]
    exact hx.2
  rw [← circleAverage_abs_radius]
  apply H.eq_of_eqOn_Ioo (by aesop)
  intro r hr
  apply HarmonicOnNhd.circleAverage_eq
  apply (hf.comp_CLM g).1.mono
  rw [abs_of_pos hr.1]
  exact closedBall_subset_ball hr.2

end InnerProductSpace

@[deprecated InnerProductSpace.HarmonicOnNhd.circleAverage_eq (since := "2026-08-04")]
alias HarmonicOnNhd.circleAverage_eq := InnerProductSpace.HarmonicOnNhd.circleAverage_eq

@[deprecated InnerProductSpace.HarmonicContOnCl.circleAverage_eq (since := "2026-08-04")]
alias HarmonicContOnCl.circleAverage_eq := InnerProductSpace.HarmonicContOnCl.circleAverage_eq
