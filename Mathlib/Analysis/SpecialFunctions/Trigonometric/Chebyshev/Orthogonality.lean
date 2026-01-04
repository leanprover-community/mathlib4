/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
--public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section

namespace Polynomial.Chebyshev

open Real MeasureTheory

noncomputable abbrev chebDensT (x : ℝ) : ENNReal :=
    if x ∈ Set.Ioo (-1) 1 then ((√(1 - x ^ 2))⁻¹).toNNReal else 0

theorem integral_T_mul_T_of_ne {n m : ℤ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂volume.withDensity chebDensT = 0 := by
  sorry

example {n m : ℕ} (h : (n : WithBot ℕ) < m) : n < m := by grind
example {n m : ℕ} (h : (n : WithBot ℕ) < m) : n < m := by grind [WithBot.coe_lt_coe]
example {n m : ℕ} (h : (n : WithBot ℕ) < m) : n < m := WithBot.coe_lt_coe.mp h

example {n m : ℕ} (h : m ≤ n) : m * π / n ≤ π := by grind
example {n m : ℕ} (h : m ≤ n) : m * π / n ≤ π := by
  by_cases! n = 0
  case pos hn => rw [hn, Nat.cast_zero, div_zero]; positivity
  case neg hn => calc
      m * π / n ≤ n * π / n := by gcongr
      _ = π := by aesop

end Polynomial.Chebyshev
