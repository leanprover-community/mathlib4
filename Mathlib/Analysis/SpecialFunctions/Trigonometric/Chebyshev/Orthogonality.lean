/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section

namespace Polynomial.Chebyshev

open Real intervalIntegral

@[simp]
theorem integral_T_real (n : ℤ) :
    ∫ x in -1..1, (T ℝ n).eval x * (1 / √(1 - x ^ 2)) = ∫ θ in 0..π, cos (n * θ) := calc
  ∫ x in -1..1, (T ℝ n).eval x * (1 / √(1 - x ^ 2)) =
    ∫ x in 1..-1, (T ℝ n).eval x * -(1 / √(1 - x ^ 2)) := by
    rw [integral_symm, ← integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), (T ℝ n).eval (cos θ) := by
    rw [← integral_comp_mul_deriv''' (f' := fun x => -(1 / √ (1 - x ^ 2)))]
    · simp_rw [Function.comp_apply]
      exact integral_congr <| fun x hx => by rw [cos_arccos (by aesop) (by aesop)]
    · exact continuous_arccos.continuousOn
    · exact fun x _ => (hasDerivAt_arccos (x := x) (by grind) (by grind)).hasDerivWithinAt
    · apply Continuous.continuousOn
      continuity
    · sorry
    · sorry
  _ = ∫ θ in 0..π, cos (n * θ) := by simp

theorem integral_T_real_of_zero :
    ∫ x in -1..1, (T ℝ 0).eval x * (1 / √(1 - x ^ 2)) = π := by
  rw [integral_T_real 0]
  simp

theorem integral_T_real_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x in -1..1, (T ℝ n).eval x * (1 / √(1 - x ^ 2)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n*π, cos θ = 0 by
    rwa [integral_T_real n, integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn),
      smul_eq_zero_iff_right (by aesop), mul_zero]
  trans ∫ θ in 0..n*π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos =>
    rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]
    simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

end Polynomial.Chebyshev
