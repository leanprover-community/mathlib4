/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

example : Real.exp (-100) < 1e-43 := by dyadic_interval [prec := 145]

example : ⌊Real.exp 30⌋ = 10686474581524 := by
  rw [Int.floor_eq_iff]; constructor <;> dyadic_interval [prec := 1]

example : ⌊Real.exp (Real.exp 2)⌋ = 1618 := by
  rw [Int.floor_eq_iff]; constructor <;> dyadic_interval [prec := 15]

example : (10686474581524 : ℝ) ≤ Real.exp 30 := by dyadic_interval

example {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 := by dyadic_interval

example {x : ℝ} (hx : 1 ≤ x) : 2 ≤ Real.exp x := by dyadic_interval [prec := 4]

example (x : ℝ) : 0 ≤ Real.exp x := by dyadic_interval

end Inclusion.Tests
