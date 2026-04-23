/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Integral elements of ℂ

This file proves that `Complex.I` is integral over ℤ and ℚ.
-/

public section

open Polynomial

namespace Complex

theorem isIntegral_int_I : IsIntegral ℤ I := by
  refine ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_C, I_sq, eq_intCast, Int.cast_one, neg_add_cancel]

theorem isIntegral_rat_I : IsIntegral ℚ I :=
  isIntegral_int_I.tower_top

end Complex
