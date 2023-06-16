/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module ring_theory.polynomial.selmer
! leanprover-community/mathlib commit 3e00d81bdcbf77c8188bbd18f5524ddc3ed8cac6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Polynomial.UnitTrinomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.LinearCombination

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `Polynomial.x_pow_sub_x_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1 : ℤ[X]` are
irreducible.

- `Polynomial.x_pow_sub_x_sub_one_irreducible_rat`: The Selmer polynomials `X ^ n - X - 1 : ℚ[X]`
are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/


namespace Polynomial

open scoped Polynomial

variable {n : ℕ}
example (n : ℕ) : (n % 2 = 0) ∨ (n % 2 = 1) := by exact Nat.mod_two_eq_zero_or_one n
theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1
  · linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  -- thanks polyrith!
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3]
    simp_rw [pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases (n % 3)
    . norm_cast at *
      simp only [zero_add, pow_mul, h3, one_pow, true_or]
    . norm_cast at *
      ring_nf
      simp only [mul_comm, pow_mul, h3, one_pow, mul_one, true_or, or_true]
    . norm_cast at *
      ring_nf
      simp only [mul_comm, pow_mul, h3, one_pow, one_mul, sq_eq_one_iff, or_true]
  have z_ne_zero : z ≠ 0 := fun h => by
    -- porting note: original code was
    -- zero_ne_one ((zero_pow zero_lt_three).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
    have := h ▸ h3
    simpa
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, self_eq_add_left] at h1 )
  · exact one_ne_zero (by rwa [key, self_eq_add_right] at h1 )
  · refine' z_ne_zero (pow_eq_zero _)
    exact 2
    norm_cast at * -- porting note: did not need this in mathlib3
    rwa [key, add_self_eq_zero] at h2
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible_aux Polynomial.X_pow_sub_X_sub_one_irreducible_aux

theorem x_pow_sub_x_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1] <;> ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply @X_pow_sub_X_sub_one_irreducible_aux n z
  rw [trinomial_mirror zero_lt_one hn (by simp) (by simp)] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C] at h1 h2
  simp_rw [Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ', Nat.sub_add_cancel hn.le] at h2
  norm_cast at *
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible Polynomial.x_pow_sub_x_sub_one_irreducible

theorem x_pow_sub_x_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1] <;> ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast _).mp
      (x_pow_sub_x_sub_one_irreducible hn1)
  ·
    rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).IsPrimitive
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible_rat Polynomial.x_pow_sub_x_sub_one_irreducible_rat

end Polynomial
