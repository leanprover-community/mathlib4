/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
module

public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# The real numbers form a real closed field
-/

public instance : IsRealClosed ℝ :=
  .of_linearOrderedField Real.isSquare_iff.mpr fun {f} hf ↦ by
    wlog h : 0 ≤ f.leadingCoeff; · simpa using this (f := -f) (by simpa) (by simp; linarith)
    by_contra! contra
    have : 0 < f.eval 0 := f.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (by aesop) h
    have : f.eval 0 < 0 := by
      have aux : (-1 : ℝ) ^ f.natDegree = -1 := by aesop
      simpa [aux] using f.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (by aesop) h
    linarith
