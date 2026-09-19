/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
module

public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# The real numbers form a real closed field

In this file we prove that `ℝ` is a real closed field, providing the `IsRealClosed ℝ` instance.

The nontrivial content is that every odd-degree real polynomial has a real root, which we deduce
from the intermediate value theorem via the eventual-sign lemmas in
`Mathlib/Analysis/Polynomial/Order.lean`: if an odd-degree polynomial had no root, those lemmas
would force its value at `0` to be simultaneously positive and negative.
-/

public section

open Polynomial

namespace Real

/-- Every odd-degree real polynomial has a real root.

If `f` had no root then the hypotheses of the eventual-sign lemmas of `Polynomial` hold vacuously,
so those lemmas pin down the sign of `f` beyond all its roots at *both* ends of the real line. As
the degree is odd these two signs are opposite, yet both apply at the point `0`, a contradiction. -/
theorem exists_isRoot_of_odd_natDegree {f : ℝ[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  by_contra! h
  -- With no root, `∀ y, f.IsRoot y → _` holds vacuously for any bound; we use `0`.
  have hlt : ∀ y, f.IsRoot y → y < 0 := fun y hy => absurd hy (h y)
  have hgt : ∀ y, f.IsRoot y → (0 : ℝ) < y := fun y hy => absurd hy (h y)
  have hneg : Int.negOnePow f.natDegree = -1 := Int.negOnePow_odd _ (by exact_mod_cast hf)
  rcases le_or_gt 0 f.leadingCoeff with hlc | hlc
  · -- `f` is eventually positive at `+∞` and eventually negative at `-∞`.
    have hpos := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hlt hlc
    have hsign := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg hgt hlc
    rw [hneg] at hsign
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hsign
    linarith
  · have hpos := eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hlt hlc.le
    have hsign := negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos hgt hlc.le
    rw [hneg] at hsign
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hsign
    linarith

end Real

instance : IsRealClosed ℝ :=
  .of_linearOrderedField (fun h => Real.isSquare_iff.mpr h) Real.exists_isRoot_of_odd_natDegree
