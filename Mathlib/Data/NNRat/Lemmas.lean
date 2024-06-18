/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.Field.Rat

#align_import data.rat.nnrat from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

/-!
# Field and action structures on the nonnegative rationals

This file provides additional results about `NNRat` that cannot live in earlier files due to import
cycles.
-/

open Function
open scoped NNRat

namespace NNRat
variable {α : Type*} {p q : ℚ≥0}

/-- A `MulAction` over `ℚ` restricts to a `MulAction` over `ℚ≥0`. -/
instance [MulAction ℚ α] : MulAction ℚ≥0 α :=
  MulAction.compHom α coeHom.toMonoidHom

/-- A `DistribMulAction` over `ℚ` restricts to a `DistribMulAction` over `ℚ≥0`. -/
instance [AddCommMonoid α] [DistribMulAction ℚ α] : DistribMulAction ℚ≥0 α :=
  DistribMulAction.compHom α coeHom.toMonoidHom

@[simp, norm_cast]
lemma coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x ↦ ↑(f x)) a :=
  (coeHom : ℚ≥0 →+ ℚ).map_indicator _ _ _
#align nnrat.coe_indicator NNRat.coe_indicator

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

lemma toNNRat_inv (q : ℚ) : toNNRat q⁻¹ = (toNNRat q)⁻¹ := by
  obtain hq | hq := le_total q 0
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv, toNNRat_coe]
#align rat.to_nnrat_inv Rat.toNNRat_inv

lemma toNNRat_div (hp : 0 ≤ p) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← toNNRat_inv, ← toNNRat_mul hp]
#align rat.to_nnrat_div Rat.toNNRat_div

lemma toNNRat_div' (hq : 0 ≤ q) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, toNNRat_mul (inv_nonneg.2 hq), toNNRat_inv]
#align rat.to_nnrat_div' Rat.toNNRat_div'

end Rat

/-! ### Numerator and denominator -/

namespace NNRat

variable {p q : ℚ≥0}

@[simp]
lemma num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext : 1
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_natCast,
    Int.natAbs_of_nonneg (Rat.num_nonneg.2 q.cast_nonneg)]
  exact Rat.num_div_den q
#align nnrat.num_div_denom NNRat.num_div_den

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort*} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q := by
  rw [← num_div_den q]; apply h
#align nnrat.rec NNRat.rec

end NNRat
