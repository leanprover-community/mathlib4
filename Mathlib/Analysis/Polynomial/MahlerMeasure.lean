/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Mahler measure of complex polynomials

In this file we define the Mahler measure of a polynomial over `ℂ[X]` and prove some basic
properties.

## Main definitions

- `Polynomial.logMahlerMeasure p`: the logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`.
- `Polynomial.MahlerMeasure p`: the (exponential) Mahler measure of a polynomial `p`, which is equal
to `e ^ (logMahlerMeasure p)` if `p` is nonzero, and `0` otherwise.

-/

namespace Polynomial

open Real

/-- The logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖` -/
noncomputable def logMahlerMeasure (p : ℂ[X]) :=
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖

theorem logMahlerMeasure_def (p : ℂ[X]) : p.logMahlerMeasure =
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖ := rfl

@[simp]
theorem logMahlerMeasure_zero : (0 : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure_def]

@[simp]
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure_def]

@[simp]
theorem logMahlerMeasure_C (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  field_simp [logMahlerMeasure_def]

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure_def]

@[simp]
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖ := by
  field_simp [logMahlerMeasure_def]

/-- The Mahler measure of a polynomial `p` defined as `e ^ (logMahlerMeasure p)` if `p` is nonzero
and `0` otherwise -/
noncomputable def MahlerMeasure (p : ℂ[X]) := if p ≠ 0 then exp (p.logMahlerMeasure) else 0

theorem MahlerMeasure_def_of_ne_zero {p : ℂ[X]} (hp : p ≠ 0): p.MahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) :=
  by simp [MahlerMeasure, hp, logMahlerMeasure_def]

theorem logMahlerMeasure_eq_log_MahlerMeasure {p : ℂ[X]} :
    p.logMahlerMeasure = log p.MahlerMeasure := by
  rw [MahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def]

@[simp]
theorem MahlerMeasure_zero : (0 : ℂ[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_one : (1 : ℂ[X]).MahlerMeasure = 1 := by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_C (z : ℂ) : (C z).MahlerMeasure = ‖z‖ := by
  simp only [MahlerMeasure, ne_eq, map_eq_zero]
  split_ifs with h <;> simp [h, exp_log]

theorem MahlerMeasure_nonneg (p : ℂ[X]) : 0 ≤ p.MahlerMeasure := by
  by_cases hp : p = 0 <;> simp [hp, MahlerMeasure_def_of_ne_zero, exp_nonneg]

@[simp]
theorem MahlerMeasure_eq_zero_iff (p : ℂ[X]) : p.MahlerMeasure = 0 ↔ p = 0 := by
  refine ⟨?_, by simp_all [MahlerMeasure_zero]⟩
  contrapose
  exact fun h ↦ by simp [MahlerMeasure_def_of_ne_zero h]

end Polynomial
