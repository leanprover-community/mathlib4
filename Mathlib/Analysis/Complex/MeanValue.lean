/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Mean Value Property of Complex Differentiable Functions

This file established the classic mean value properties of complex differentiable functions,
computing the value of a function at the center of a circle as a circle average. It also provides
generalized versions that computing the value of a function at arbitrary points of a disk as circle
averages over suitable weighted functions.
-/

public section

open Complex Filter Function Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {c w : ℂ} {s : Set ℂ}

-- Helper lemma: proof of `circleAverage_of_differentiable_on_off_countable₁` in case `0 < R`.
private theorem circleAverage_of_differentiable_on_off_countable_posRadius (hR : 0 < R)
    (hs : s.Countable) (h₁f : ContinuousOn f (closedBall c R))
    (h₂f : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) (hw : w ∈ ball c R) :
    circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R = f w := by
  calc circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - w)⁻¹ • f z) := by
    simp only [circleAverage_eq_circleIntegral hR.ne', mul_inv_rev, inv_I, neg_mul, neg_smul,
      neg_inj, ne_eq, mul_eq_zero, I_ne_zero, inv_eq_zero, ofReal_eq_zero, pi_ne_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true, smul_right_inj]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    match_scalars
    have : z - c ≠ 0 := by aesop
    grind
  _ = f w := by
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw h₁f h₂f]
    match_scalars
    simp [field]

/-!
## Generalized Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute values of `f` in the
interior of a disk as circle averages of a weighted function.
-/

/--
The **Generalized Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is
continuous on a closed disc of radius `R` and center `c`, and is complex differentiable at all but
countably many points of its interior, then for every point `w` in the disk, the circle average
`circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R` equals `f w`.
-/
theorem circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z)
    (hw : w ∈ ball c |R|) (hR : R ≠ 0) :
    circleAverage (fun z ↦ ((z - c) / (z - w)) • f z) c R = f w := by
  rw [← circleAverage_abs_radius]
  exact circleAverage_of_differentiable_on_off_countable_posRadius (by simpa)
    hs h₁f h₂f hw

/--
The **Generalized Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is
complex differentiable at all points of a closed disc of radius `R` and center `c`, then for every
point `w` in the disk, the circle average `circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R`
equals `f w`.
-/
theorem circleAverage_sub_sub_inv_smul_of_differentiable_on
    (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z) (hw : w ∈ ball c |R|) (hR : R ≠ 0) :
    circleAverage (fun z ↦ ((z - c) / (z - w)) • f z) c R = f w :=
  circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable countable_empty
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    (fun z hz ↦ hf z (by simp_all [le_of_lt])) hw hR

/-!
## Classic Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute value of `f` at the
center of a circle as a circle average of the function. This specializes the generalized mean value
properties discussed in the previous section.
-/

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all but countably many
points of its interior, then the circle average `circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable hs h₁f h₂f (by aesop)
      hR]
    apply circleAverage_congr_sphere fun z hz ↦ ?_
    have : z - c ≠ 0 := by grind [ne_of_mem_sphere]
    simp_all

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is complex
differentiable at all points of a closed disc of radius `R` and center `c`, then the circle average
`circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_sub_sub_inv_smul_of_differentiable_on hf (by aesop) hR]
    apply circleAverage_congr_sphere fun z hz ↦ ?_
    have : z - c ≠ 0 := by grind [ne_of_mem_sphere]
    simp_all
