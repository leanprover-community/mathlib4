/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia, Robert Y. Lewis, Mario Carneiro, Kim Morrison
-/
import Mathlib

/-!
Mathlib used to have a tactic (`polyrith`) that communicated with a remote Sage server
to do Grobner basis calculations.
This test file is adapted from the test file for `polyrith`,
but uses the `grobner` tactic instead.
(Recall `grobner` is a thin wrapper around `grind` disabling other modules.)
-/

/-! ### Standard Cases over ℤ, ℚ, and ℝ -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10) :
  3*x + 2*y = 10 := by grobner

example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 := by grobner

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 := by grobner

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 := by grobner

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
    x + 2.2*y + 2*z - 5*w = -8.5 := by
  -- `grind` does not yet understand scientific notation:
  fail_if_success grobner
  sorry

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a := by grobner

/-! ### Case with ambiguous identifiers -/

example («def evil» y : ℤ) (h1 : 3*«def evil» + 2*y = 10) :
  3*«def evil» + 2*y = 10 := by grobner

example («¥» y : ℤ) (h1 : 3*«¥» + 2*y = 10) :
  «¥» * (3*«¥» + 2*y) = 10 * «¥» := by grobner

/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) :
  a * a = a * b := by grobner

example (a b c : ℤ) (h : a = b) :
  a * c = b * c := by grobner

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 := by grobner

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 := by grobner

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by grobner

/-! ### Cases with non-hypothesis inputs/input restrictions -/

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
  b = 2 / 3 := by grobner

axiom term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (_h2 : b + c = 0) : a + b + c + d = 0 := by
  have := term c d
  grobner

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  have := hqc
  specialize h a b
  grobner

axiom bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 := by
  have := bad a
  have := bad (b^2)
  grobner

/-! ### Case over arbitrary field/ring -/

example {α} [h : CommRing α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
  c * (a*f - b*e) = 0 := by grobner

example {K : Type*} [Field K] [Invertible 2] [Invertible 3]
  {ω p q r s t : K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) := by
  have hs_nonzero : s ≠ 0 := by
    contrapose! hp_nonzero with hs_nonzero
    grobner
  have H' : 2 * q = s ^ 3 - t ^ 3 := by
    rw [← mul_left_inj' (pow_ne_zero 3 hs_nonzero)]
    grobner
  grobner

/-! ## Degenerate cases -/

example {K : Type*} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by grobner

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by grobner

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by grobner

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by grobner

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by grobner

example (z : ℤ) (h1 : z + 1 = 2) (h2 : z + 2 = 2) : (1 : ℤ) = 2 := by grobner

example {R} [CommRing R] (x : R) (h2 : (2 : R) = 0) : x + x = 0 := by grobner

example {R} [CommRing R] (_x : R) (h : (2 : R) = 4) : (0 : R) = 2 := by grobner

/-
### Examples with exponent
-/

example (x y z : ℚ) (h : x = y) (h2 : x * y = 0) : x + y*z = 0 := by grobner

example (K : Type)
    [Field K]
    [CharZero K]
    {x y z : K}
    (h₂ : y ^ 3 + x * (3 * z ^ 2) = 0)
    (h₁ : x ^ 3 + z * (3 * y ^ 2) = 0)
    (h₀ : y * (3 * x ^ 2) + z ^ 3 = 0)
    (h : x ^ 3 * y + y ^ 3 * z + z ^ 3 * x = 0) :
    x = 0 := by grobner

example (y a : ℤ) (k : ℕ) (h : a ^ k = 0) : a ^ k * y = 0 := by
  grobner
