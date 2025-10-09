/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Mean Value Property of Complex Differentiable Functions
-/

open Complex Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {c : ℂ} {s : Set ℂ}

-- Helper lemma: proof of `circleAverage_of_differentiable_on_off_countable` in case `0 < R`.
private theorem circleAverage_of_differentiable_on_off_countable_posRadius (hR : 0 < R)
    (hs : s.Countable) (h₁f : ContinuousOn f (closedBall c R))
    (h₂f : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  calc circleAverage f c R
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) :=
    circleAverage_eq_circleIntegral hR.ne'
  _ = f c := by
    rw [circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable hR hs h₁f h₂f,
      ← smul_assoc]
    match_scalars
    simp [field]

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all but countably many
points of its interior, then the circle average `circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  rcases lt_trichotomy 0 R with h | rfl | h
  · rw [← abs_of_pos h]
    exact circleAverage_of_differentiable_on_off_countable_posRadius (abs_pos_of_pos h) hs h₁f h₂f
  · simp
  · rw [← circleAverage_neg_radius, ← abs_of_neg h]
    exact circleAverage_of_differentiable_on_off_countable_posRadius (abs_pos_of_neg h) hs h₁f h₂f

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is complex
differentiable at all points of a closed disc of radius `R` and center `c`, then the circle average
`circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on (hf : ∀ z ∈ closedBall c |R|, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c :=
  circleAverage_of_differentiable_on_off_countable Set.countable_empty
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    fun z hz ↦ hf z (by simp_all [le_of_lt])
