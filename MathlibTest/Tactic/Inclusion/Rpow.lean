/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rpow
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

open Real

namespace Inclusion.Tests

example : (2 : ℝ) ^ (0 : ℝ) = 1 := by dyadic_interval

example {x : ℝ} (hx : 1 ≤ x) : x ^ (0 : ℝ) = 1 := by dyadic_interval

example : (2 : ℝ) ^ (0.5 : ℝ) ∈ Set.Icc 1.4142 1.4143 := by
  dyadic_interval [prec := 20]

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : x ^ (2 : ℝ) ∈ Set.Icc 0.99 4.01 := by
  dyadic_interval [prec := 10]

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : (2 : ℝ) ^ x ∈ Set.Icc 1.9 4.1 := by
  dyadic_interval [prec := 15]

example {x y : ℝ} (hx : x ∈ Set.Icc 1.5 2) (hy : y ∈ Set.Icc 1 1.5) :
    x ^ y ∈ Set.Icc 0.9 3.2 := by
  dyadic_interval [prec := 15]

example {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ (2 : ℝ) := by dyadic_interval [prec := 4]

example {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) : 1 ≤ x ^ y := by dyadic_interval [prec := 4]

example : 1.2311444133 < (2 : ℝ) ^ (0.3 : ℝ) := by dyadic_interval [prec := 60]

example : (2 : ℝ) ^ (0.3 : ℝ) < 1.2311444134 := by dyadic_interval [prec := 60]

example : ⌊(2 : ℝ) ^ (10.3 : ℝ)⌋ = 1260 := by
  rw [Int.floor_eq_iff]
  constructor <;> dyadic_interval [prec := 20]

example : ⌈(3 : ℝ) ^ (1.7 : ℝ)⌉ = 7 := by
  rw [Int.ceil_eq_iff]
  dyadic_interval [prec := 20]

example : ⌊(1.5 : ℝ) ^ ((2 : ℝ) ^ (1.7 : ℝ))⌋ = 3 := by
  rw [Int.floor_eq_iff]
  constructor <;> dyadic_interval [prec := 20]

example : ⌊exp ((2 : ℝ) ^ (1.7 : ℝ))⌋ = 25 := by
  rw [Int.floor_eq_iff]
  constructor <;> dyadic_interval [prec := 20]

example : log ((2 : ℝ) ^ (10.3 : ℝ)) ∈ Set.Icc 7 7.2 := by
  dyadic_interval [prec := 20]

example : exp ((2 : ℝ) ^ (0.3 : ℝ)) < 3.5 := by dyadic_interval [prec := 30]

example {x y : ℝ} (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) :
    log (x ^ y) ∈ Set.Icc (-0.1) 1.4 := by dyadic_interval [prec := 15]

example {x y : ℝ} (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) :
    x ^ y * y ∈ Set.Icc 0.9 8.1 := by dyadic_interval [prec := 15]

example {x y : ℝ} (hx : x ∈ Set.Icc 2 3) (hy : y ∈ Set.Icc 1 2) :
    x ^ y - y ∈ Set.Icc (-0.1) 8.1 := by dyadic_interval [prec := 15]

example : (2 : ℝ) ^ (3.7 : ℝ) ∈ Set.Icc
    12.996038341699768361755350124404506420563279590914
    12.996038341699768361755350124404506420563279590915 := by
  dyadic_interval [prec := 190]

example : (1.5 : ℝ) ^ (-2.3 : ℝ) ∈ Set.Icc
    0.3935411081313582737322585918067438924599440197386
    0.3935411081313582737322585918067438924599440197387 := by
  dyadic_interval [prec := 190]

example : (3 : ℝ) ^ (1.7 : ℝ) ∈ Set.Icc
    6.4730078399237792986648467479408196650154421405164
    6.4730078399237792986648467479408196650154421405165 := by
  dyadic_interval [prec := 190]

end Inclusion.Tests
