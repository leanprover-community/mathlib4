/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Pi

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

example : 3.14159 < Real.pi := by dyadic_interval [prec := 20]

example : Real.pi < 3.1416 := by dyadic_interval [prec := 20]

-- More than 32 terms of the series of `arctan (1 / 5)`, so its sum splits in halves.
example : |Real.pi - 3.14159265358979323846264338327950288| < 1e-35 := by
  dyadic_interval [prec := 130]

example : Real.pi ^ 2 < 9.8697 := by dyadic_interval [prec := 20]

end Inclusion.Tests
