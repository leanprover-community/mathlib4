/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Critical-Line Symmetry, Sign-Change Zero Certification, and 3-4-1 Positivity

This file formalizes:
1. The critical-line reflection symmetry for `completedRiemannZeta`.
2. Intermediate Value Theorem sign-change certification of non-trivial critical-line zeros.
3. De la Vallée Poussin's (1899) classic `3 + 4 cos θ + cos 2θ ≥ 0` trigonometric positivity.
-/

@[expose] public section

open scoped BigOperators
open Complex Filter Set

/-- Embedding of the critical line `Re(s) = 1 / 2` parametrized by `t : ℝ`. -/
noncomputable def criticalLine (t : ℝ) : ℂ := 1 / 2 + Complex.I * (t : ℂ)

/-- The real part of any point on the critical line is identically `1 / 2`. -/
theorem criticalLine_re (t : ℝ) : (criticalLine t).re = 1 / 2 := by
  simp [criticalLine]

/-- Reflection involution across the critical line: `1 - s = criticalLine (-t)`. -/
theorem one_sub_criticalLine (t : ℝ) : 1 - criticalLine t = criticalLine (-t) := by
  simp only [criticalLine, Complex.ofReal_neg]
  ring

/-- The completed Riemann zeta function is even along the critical line. -/
theorem completedRiemannZeta_criticalLine_neg (t : ℝ) :
    completedRiemannZeta (criticalLine (-t)) = completedRiemannZeta (criticalLine t) := by
  rw [← one_sub_criticalLine, completedRiemannZeta_one_sub]

/-- Unconditional Intermediate Value Theorem certification of critical-line zeros:
if a continuous real detector `Z : ℝ → ℝ` (such as the Hardy Z-function) changes sign on
`[a, b]`, then `riemannZeta` has a zero on the critical line `Re(s) = 1 / 2` in `[a, b]`. -/
theorem exists_criticalLine_zero_of_sign_change {Z : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Z (Set.Icc a b))
    (hzero : ∀ t ∈ Set.Icc a b, Z t = 0 → riemannZeta (criticalLine t) = 0)
    (hsign : Z a * Z b ≤ 0) :
    ∃ t₀ ∈ Set.Icc a b, (criticalLine t₀).re = 1 / 2 ∧ riemannZeta (criticalLine t₀) = 0 := by
  have hz : ∃ t₀ ∈ Set.Icc a b, Z t₀ = 0 := by
    rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (Z b) (Z a) := ⟨h2, h1⟩
      have := intermediate_value_Icc' hab hcont hmem
      rcases this with ⟨t₀, ht₀, heq⟩
      exact ⟨t₀, ht₀, heq⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (Z a) (Z b) := ⟨h1, h2⟩
      have := intermediate_value_Icc hab hcont hmem
      rcases this with ⟨t₀, ht₀, heq⟩
      exact ⟨t₀, ht₀, heq⟩
  rcases hz with ⟨t₀, ht₀, heq⟩
  exact ⟨t₀, ht₀, criticalLine_re t₀, hzero t₀ ht₀ heq⟩

/-- De la Vallée Poussin's (1899) trigonometric identity. -/
theorem deLaValleePoussin_trig_eq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- Unconditional pointwise non-negativity of the 3-4-1 trigonometric kernel. -/
theorem deLaValleePoussin_trig_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [deLaValleePoussin_trig_eq]
  positivity

/-- Non-negativity of positive linear combinations of 3-4-1 kernels. -/
theorem sum_deLaValleePoussin_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ω : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (t : ℝ) :
    0 ≤ ∑ i ∈ s, a i * (3 + 4 * Real.cos (t * ω i) + Real.cos (2 * (t * ω i))) := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (deLaValleePoussin_trig_nonneg _))
