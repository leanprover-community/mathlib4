/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Cos

import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

example : |Real.cos 1 - 0.5403023058681398| < 1e-15 := by dyadic_interval [prec := 55]

example {x : ℝ} (h₁ : 1 ≤ x) (h₂ : x ≤ 2) : -0.416147 < Real.cos x ∧ Real.cos x < 0.540303 := by
  dyadic_interval [prec := 25]

-- An interval wider than `2π` gets a shortcut
example {x : ℝ} (h₁ : 0 ≤ x) (h₂ : x ≤ 8) : Real.cos x ∈ Set.Icc (-1) 1 := by dyadic_interval

example (x : ℝ) : -1 ≤ Real.cos x := by dyadic_interval

end Inclusion.Tests
