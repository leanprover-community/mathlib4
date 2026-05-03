/-
Copyright (c) 2026 Fumio Sasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fumio Sasaki
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Morera's Theorem (Triangle Version)

This file formalizes the triangle version of Morera's theorem:
a continuous complex-valued function with vanishing integrals
along all triangles is holomorphic.

The proof proceeds by showing that the vanishing triangle
integral condition implies the vanishing rectangle integral
condition (`IsConservativeOn`), and then applying the existing
Morera's theorem for rectangles.
-/

open MeasureTheory Filter Topology Set
open scoped Interval

namespace Complex

variable {f : ℂ → ℂ} {z w : ℂ}

/-- A helper lemma to convert a horizontal interval integral
into a parameterized segment integral. -/
lemma integral_re_eq_segment
    (_hf_cont : Continuous f) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) =
    ∫ t in (0 : ℝ)..1,
      (w.re - z.re : ℂ) *
        f (z + (t : ℂ) *
          ((w.re : ℂ) - (z.re : ℂ))) := by
  cases eq_or_ne (w.re - z.re) 0 with
  | inl h =>
    simp_all only [sub_eq_iff_eq_add, zero_add,
      intervalIntegral.integral_same, sub_self,
      mul_zero, add_zero,
      intervalIntegral.integral_const, sub_zero,
      one_smul, zero_mul]
  | inr h =>
    simp_all only [
      intervalIntegral.integral_const_mul]
    convert intervalIntegral.integral_comp_add_div
      _ _ _ using 3
    case convert_6 => exact w.re - z.re
    case convert_9 =>
      exact -z.re / (w.re - z.re)
    · congr 1
      norm_num [Complex.ext_iff, div_eq_mul_inv]
      ring_nf
      norm_num [Complex.normSq]
      ring_nf
      grind
    · ext; norm_num
    · ring
    · rw [← add_div, eq_div_iff]
      · ring
      · positivity
    · grobner

/-- A helper lemma to convert a vertical interval integral
into a parameterized segment integral. -/
lemma integral_im_eq_segment
    (_hf_cont : Continuous f) :
    I • (∫ y : ℝ in z.im..w.im,
        f (w.re + y * I)) =
    ∫ t in (0 : ℝ)..1,
      (w.im - z.im : ℂ) * I *
        f ((w.re : ℂ) + z.im * I +
          (t : ℂ) *
            ((w.im : ℂ) * I -
              (z.im : ℂ) * I)) := by
  by_cases h : z.im = w.im
  · simp [h]
  · suffices ∫ (y : ℝ) in z.im..w.im,
        f (↑w.re + I * ↑y) =
      (↑w.im - ↑z.im) *
        ∫ (x : ℝ) in 0..1,
          f (↑w.re + I * ↑z.im +
            ↑x * (I * ↑w.im - I * ↑z.im))
      by simp_all +decide [mul_assoc, mul_comm]
    convert intervalIntegral.integral_comp_add_div
      _ _ _ using 3
    case neg.convert_6 =>
      exact w.im - z.im
    case neg.convert_9 =>
      exact -z.im / (w.im - z.im)
    · congr 1
      norm_num [Complex.ext_iff,
        sub_ne_zero.mpr (Ne.symm h)]
      ring_nf
      norm_num [Complex.normSq,
        Complex.inv_re, Complex.inv_im]
      ring_nf
      grind
    · ext; norm_num
    · ring
    · rw [← add_div, eq_div_iff]
      · ring
      · cases lt_or_gt_of_ne h with
        | inl h => linarith
        | inr h => linarith
    · exact sub_ne_zero_of_ne <| Ne.symm h

private lemma integral_re_comp
    (_hf_cont : Continuous f)
    {c : ℂ} {a b : ℝ} (hab : a ≠ b) :
    ∫ x in a..b, f (x + c * I) =
    (b - a : ℂ) * ∫ t in (0 : ℝ)..1,
      f (a + c * I +
        t * ((b : ℂ) - (a : ℂ))) := by
  convert intervalIntegral.integral_comp_add_div
    _ _ _ using 3
  case convert_6 => exact b - a
  case convert_9 => exact -a / (b - a)
  · congr 1
    norm_num [sub_ne_zero.2 hab.symm,
      mul_div_cancel₀]
    rw [add_mul,
      div_mul_cancel₀ _
        (sub_ne_zero_of_ne <|
          mod_cast hab.symm),
      div_mul_cancel₀ _
        (sub_ne_zero_of_ne <|
          mod_cast hab.symm)]
    ring
  · ext; norm_num
  · ring
  · rw [← add_div, eq_div_iff]
    · ring
    · cases lt_or_gt_of_ne hab with
      | inl h => linarith
      | inr h => linarith
  · exact sub_ne_zero_of_ne hab.symm

private lemma integral_re_subst
    (hf_cont : Continuous f)
    {c : ℂ} {a b : ℝ} :
    ∫ x in a..b, f (x + c * I) =
    ∫ t in (0 : ℝ)..1,
      (b - a : ℂ) *
        f (a + c * I +
          t * ((b : ℂ) - (a : ℂ))) := by
  by_cases hab : a = b
  · simp [hab]
  · rw [intervalIntegral.integral_const_mul,
      integral_re_comp hf_cont hab]

/-
A rectangle integral decomposes into two triangle integrals.
-/
set_option maxHeartbeats 400000 in
-- The `linear_combination` closure requires extra heartbeats.
lemma rect_eq_sum_triangles
    (hf_cont : Continuous f) (z w : ℂ)
    (h_tri : ∀ z₁ z₂ z₃ : ℂ,
      (∫ t in (0 : ℝ)..1,
          (z₂ - z₁) *
            f (z₁ + (t : ℂ) * (z₂ - z₁))) +
        (∫ t in (0 : ℝ)..1,
          (z₃ - z₂) *
            f (z₂ + (t : ℂ) * (z₃ - z₂))) +
        (∫ t in (0 : ℝ)..1,
          (z₁ - z₃) *
            f (z₃ + (t : ℂ) * (z₁ - z₃))) =
        0) :
    (((∫ (x : ℝ) in z.re..w.re,
            f (↑x + ↑z.im * I)) -
          ∫ (x : ℝ) in z.re..w.re,
            f (↑x + ↑w.im * I)) +
        I • ∫ (y : ℝ) in z.im..w.im,
            f (↑w.re + ↑y * I)) -
      I • ∫ (y : ℝ) in z.im..w.im,
          f (↑z.re + ↑y * I) =
      0 := by
  rw [integral_re_subst, integral_re_subst]
  · have h_im :
        I • ∫ y in z.im..w.im,
          f (w.re + y * I) =
        ∫ t in (0 : ℝ)..1,
          (↑w.im - ↑z.im) * I *
            f (↑w.re + ↑z.im * I +
              ↑t * (↑w.im * I -
                ↑z.im * I)) := by
      convert integral_im_eq_segment
        hf_cont using 1
    have h_im' :
        I • ∫ y in z.im..w.im,
          f (z.re + y * I) =
        ∫ t in (0 : ℝ)..1,
          (↑w.im - ↑z.im) * I *
            f (↑z.re + ↑z.im * I +
              ↑t * (↑w.im * I -
                ↑z.im * I)) := by
      convert integral_im_eq_segment
        hf_cont using 1
      case convert_1 =>
        exact z.re + z.im * I
      case convert_2 =>
        exact z.re + w.im * I
      · norm_num
      · norm_num
    have h1 := h_tri (z.re + z.im * I)
      (w.re + z.im * I) (w.re + w.im * I)
    have h2 := h_tri (z.re + z.im * I)
      (z.re + w.im * I) (w.re + w.im * I)
    simp only [intervalIntegral.integral_const_mul,
      smul_eq_mul] at h1 h2 h_im h_im' ⊢
    rw [h_im, h_im']
    ring_nf at h1 h2 ⊢
    linear_combination h1 - h2
  · assumption
  · assumption

/-- If a continuous function has vanishing integrals along
all triangles, then its integral vanishes along all rectangles
(i.e., it is conservative). -/
lemma isConservativeOn_univ_of_triangle_integral_zero
    (hf_cont : Continuous f)
    (h_tri : ∀ z₁ z₂ z₃ : ℂ,
      (∫ t in (0 : ℝ)..1,
          (z₂ - z₁) *
            f (z₁ + (t : ℂ) * (z₂ - z₁))) +
        (∫ t in (0 : ℝ)..1,
          (z₃ - z₂) *
            f (z₂ + (t : ℂ) * (z₃ - z₂))) +
        (∫ t in (0 : ℝ)..1,
          (z₁ - z₃) *
            f (z₃ + (t : ℂ) * (z₁ - z₃))) =
        0) :
    IsConservativeOn f univ := by
  intro z w _
  rw [← add_eq_zero_iff_eq_neg,
    wedgeIntegral_add_wedgeIntegral_eq]
  exact rect_eq_sum_triangles hf_cont z w h_tri

/-- [Morera's Theorem Core]
If a continuous complex function `f` has vanishing integrals
along all triangles, then `f` is complex differentiable
(holomorphic) everywhere on ℂ. -/
lemma morera_theorem_core (hf_cont : Continuous f)
    (h_tri : ∀ z₁ z₂ z₃ : ℂ,
      (∫ t in (0 : ℝ)..1,
          (z₂ - z₁) *
            f (z₁ + (t : ℂ) * (z₂ - z₁))) +
        (∫ t in (0 : ℝ)..1,
          (z₃ - z₂) *
            f (z₂ + (t : ℂ) * (z₃ - z₂))) +
        (∫ t in (0 : ℝ)..1,
          (z₁ - z₃) *
            f (z₃ + (t : ℂ) * (z₁ - z₃))) =
        0) :
    Differentiable ℂ f := by
  rw [← differentiableOn_univ, ←
    isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      isOpen_univ]
  exact
    ⟨isConservativeOn_univ_of_triangle_integral_zero
      hf_cont h_tri, hf_cont.continuousOn⟩

end Complex
