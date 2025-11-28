/-
Copyright (c) 2025 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Dirichlet kernel

The Dirichlet kernel is a family of functions related to the Fourier Transform.

This file defines lemmas relevant to the Dirichlet kernel.

## References

* https://en.wikipedia.org/wiki/Dirichlet_kernel


## TODO

- Define the Dirichlet kernel

- Show that $S_n(f)(x) = (D_n * f)(x)$

-/

@[expose] public section

open Real

section

theorem sum_range_cos_mul_add (n : ℕ) (x a : ℝ) (hx : sin (x / 2) ≠ 0) :
    ∑ k ∈ Finset.range n, cos ((k : ℝ) * x + a)
    = sin (n * x / 2) / sin (x / 2) * cos ((n - 1 : ℝ) * x / 2 + a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, fieldEq]
    have : 2 * sin ((n + 1) * x / 2) * cos (n * x / 2 + a)
         - 2 * sin (n * x / 2) * cos ((n - 1) * x / 2 + a)
         = 2 * sin (x / 2) * cos (n * x + a) := by
      rw [two_mul_sin_mul_cos, two_mul_sin_mul_cos, two_mul_sin_mul_cos]
      ring_nf
      rw [sub_eq_add_neg, ← sin_neg]
      ring_nf
    linarith

theorem sum_range_sin_mul_add (n : ℕ) (x a : ℝ) (hx : sin (x / 2) ≠ 0) :
    ∑ k ∈ Finset.range n, sin ((k : ℝ) * x + a)
    = sin (n * x / 2) / sin (x / 2) * sin ((n - 1 : ℝ) * x / 2 + a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, fieldEq]
    have : 2 * sin (n * x / 2) * sin ((n - 1) * x / 2 + a)
         + 2 * sin (x / 2) * sin (↑n * x + a)
         = 2 * sin ((n + 1) * x / 2) * sin (n * x / 2 + a) := by
      rw [two_mul_sin_mul_sin, two_mul_sin_mul_sin, two_mul_sin_mul_sin]
      nth_rw 3 [← cos_neg]
      ring_nf
    linarith

end
