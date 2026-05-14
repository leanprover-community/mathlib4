/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.ArithMult.Init
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
# The Liouville Function

This file defines the Liouville function `λ(n)`.

## Main Definitions

* `ArithmeticFunction.liouville` is the Liouville function `λ(n)` defined to be `1` if `n` has an
  even number of prime factors (counting multiplicity) and `-1` otherwise.
-/

@[expose] public section

namespace ArithmeticFunction

/-- The Liouville function `λ(n)` defined to be `1` if `n` has an even number of prime factors
(counting multiplicity) and `-1` otherwise. -/
def liouville : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else (-1) ^ cardFactors n
  map_zero' := by simp

theorem liouville_apply {n : ℕ} (h : n ≠ 0) : liouville n = (-1) ^ cardFactors n :=
  if_neg h

theorem liouville_ne_zero {n : ℕ} (h : n ≠ 0) : liouville n ≠ 0 := by
  simp [liouville_apply h]

theorem liouville_apply_one : liouville 1 = 1 := by
  simp [liouville_apply]

theorem liouville_apply_mul (m n : ℕ) : liouville (m * n) = liouville m * liouville n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp [liouville_apply, cardFactors_mul, hm, hn, pow_add]

theorem isMultiplicative_liouville : IsMultiplicative liouville :=
  ⟨liouville_apply_one, fun {m n} _ ↦ liouville_apply_mul m n⟩

end ArithmeticFunction
