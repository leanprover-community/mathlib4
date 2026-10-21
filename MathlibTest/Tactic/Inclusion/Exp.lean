/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

example : Real.exp (-1) < 0.368 := by dyadic_interval [prec := 20]

example : (10686474581524 : ℝ) < Real.exp 30 := by dyadic_interval [prec := 2]

example {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 := by dyadic_interval

example {x : ℝ} (hx : 1 ≤ x) : 2 ≤ Real.exp x := by dyadic_interval [prec := 4]

example (x : ℝ) : 0 ≤ Real.exp x := by dyadic_interval

end Inclusion.Tests
