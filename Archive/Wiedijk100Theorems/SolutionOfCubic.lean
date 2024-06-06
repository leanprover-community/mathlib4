/-
Copyright (c) 2022 Jeoff Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeoff Lee
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

#align_import wiedijk_100_theorems.solution_of_cubic from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
# The Solution of a Cubic

This file proves Theorem 37 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

In this file, we give the solutions to the cubic equation `a * x^3 + b * x^2 + c * x + d = 0`
over a field `K` that has characteristic neither 2 nor 3, that has a third primitive root of
unity, and in which certain other quantities admit square and cube roots.

This is based on the [Cardano's Formula](https://en.wikipedia.org/wiki/Cubic_equation#Cardano's_formula).

## Main statements

- `cubic_eq_zero_iff` : gives the roots of the cubic equation
where the discriminant `p = 3 * a * c - b^2` is nonzero.
- `cubic_eq_zero_iff_of_p_eq_zero` : gives the roots of the cubic equation
where the discriminant equals zero.

## References

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Cubic_Quartic.html) was written by Amine Chaieb.

## Tags

polynomial, cubic, root
-/


namespace Theorems100

section Field

open Polynomial

variable {K : Type*} [Field K]
variable [Invertible (2 : K)] [Invertible (3 : K)]
variable (a b c d : K)
variable {ω p q r s t : K}

theorem cube_root_of_unity_sum (hω : IsPrimitiveRoot ω 3) : 1 + ω + ω ^ 2 = 0 := by
  simpa [cyclotomic_prime, Finset.sum_range_succ] using hω.isRoot_cyclotomic (by decide)
#align theorems_100.cube_root_of_unity_sum Theorems100.cube_root_of_unity_sum

/-- The roots of a monic cubic whose quadratic term is zero and whose discriminant is nonzero. -/
theorem cubic_basic_eq_zero_iff (hω : IsPrimitiveRoot ω 3) (hp_nonzero : p ≠ 0)
    (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r) (ht : t * s = p) (x : K) :
    x ^ 3 + 3 * p * x - 2 * q = 0 ↔ x = s - t ∨ x = s * ω - t * ω ^ 2 ∨ x = s * ω ^ 2 - t * ω := by
  have h₁ : ∀ x a₁ a₂ a₃ : K, x = a₁ ∨ x = a₂ ∨ x = a₃ ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0 := by
    intros; simp only [mul_eq_zero, sub_eq_zero, or_assoc]
  rw [h₁]
  refine Eq.congr ?_ rfl
  have hs_nonzero : s ≠ 0 := by
    contrapose! hp_nonzero with hs_nonzero
    linear_combination -1 * ht + t * hs_nonzero
  rw [← mul_left_inj' (pow_ne_zero 3 hs_nonzero)]
  have H := cube_root_of_unity_sum hω
  linear_combination
    hr + (-q + r + s ^ 3) * hs3 - (3 * x * s ^ 3 + (t * s) ^ 2 + t * s * p + p ^ 2) * ht +
    (x ^ 2 * (s - t) + x * (-ω * (s ^ 2 + t ^ 2) + s * t * (3 + ω ^ 2 - ω)) -
      (-(s ^ 3 - t ^ 3) * (ω - 1) + s ^ 2 * t * ω ^ 2 - s * t ^ 2 * ω ^ 2)) * s ^ 3 * H
#align theorems_100.cubic_basic_eq_zero_iff Theorems100.cubic_basic_eq_zero_iff

/-- Roots of a monic cubic whose discriminant is nonzero. -/
theorem cubic_monic_eq_zero_iff (hω : IsPrimitiveRoot ω 3) (hp : p = (3 * c - b ^ 2) / 9)
    (hp_nonzero : p ≠ 0) (hq : q = (9 * b * c - 2 * b ^ 3 - 27 * d) / 54)
    (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r) (ht : t * s = p) (x : K) :
    x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = s - t - b / 3 ∨ x = s * ω - t * ω ^ 2 - b / 3 ∨ x = s * ω ^ 2 - t * ω - b / 3 := by
  let y := x + b / 3
  have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _
  have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
  have h9 : (9 : K) = 3 ^ 2 := by norm_num
  have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
  have h₁ : x ^ 3 + b * x ^ 2 + c * x + d = y ^ 3 + 3 * p * y - 2 * q := by
    rw [hp, hq]
    field_simp [y, h9, h54]; ring
  rw [h₁, cubic_basic_eq_zero_iff hω hp_nonzero hr hs3 ht y]
  simp_rw [eq_sub_iff_add_eq]
#align theorems_100.cubic_monic_eq_zero_iff Theorems100.cubic_monic_eq_zero_iff

/-- **The Solution of Cubic**.
  The roots of a cubic polynomial whose discriminant is nonzero. -/
theorem cubic_eq_zero_iff (ha : a ≠ 0) (hω : IsPrimitiveRoot ω 3)
    (hp : p = (3 * a * c - b ^ 2) / (9 * a ^ 2)) (hp_nonzero : p ≠ 0)
    (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3))
    (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r) (ht : t * s = p) (x : K) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = s - t - b / (3 * a) ∨
        x = s * ω - t * ω ^ 2 - b / (3 * a) ∨ x = s * ω ^ 2 - t * ω - b / (3 * a) := by
  have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
  have h9 : (9 : K) = 3 ^ 2 := by norm_num
  have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
  have h₁ : a * x ^ 3 + b * x ^ 2 + c * x + d
    = a * (x ^ 3 + b / a * x ^ 2 + c / a * x + d / a) := by field_simp; ring
  have h₂ : ∀ x, a * x = 0 ↔ x = 0 := by intro x; simp [ha]
  have hp' : p = (3 * (c / a) - (b / a) ^ 2) / 9 := by field_simp [hp, h9]; ring_nf
  have hq' : q = (9 * (b / a) * (c / a) - 2 * (b / a) ^ 3 - 27 * (d / a)) / 54 := by
    rw [hq, h54]
    simp [field_simps, ha]
    ring_nf
  rw [h₁, h₂, cubic_monic_eq_zero_iff (b / a) (c / a) (d / a) hω hp' hp_nonzero hq' hr hs3 ht x]
  have h₄ :=
    calc
      b / a / 3 = b / (a * 3) := by field_simp [ha]
      _ = b / (3 * a) := by rw [mul_comm]
  rw [h₄]
#align theorems_100.cubic_eq_zero_iff Theorems100.cubic_eq_zero_iff

/-- the solution of the cubic equation when p equals zero. -/
theorem cubic_eq_zero_iff_of_p_eq_zero (ha : a ≠ 0) (hω : IsPrimitiveRoot ω 3)
    (hpz : 3 * a * c - b ^ 2 = 0)
    (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)) (hs3 : s ^ 3 = 2 * q)
    (x : K) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = s - b / (3 * a) ∨ x = s * ω - b / (3 * a) ∨ x = s * ω ^ 2 - b / (3 * a) := by
  have h₁ : ∀ x a₁ a₂ a₃ : K, x = a₁ ∨ x = a₂ ∨ x = a₃ ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0 := by
    intros; simp only [mul_eq_zero, sub_eq_zero, or_assoc]
  have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _
  have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
  have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
  have hb2 : b ^ 2 = 3 * a * c := by rw [sub_eq_zero] at hpz; rw [hpz]
  have hb3 : b ^ 3 = 3 * a * b * c := by rw [pow_succ, hb2]; ring
  have h₂ :=
    calc
      a * x ^ 3 + b * x ^ 2 + c * x + d =
      a * (x + b / (3 * a)) ^ 3 + (c - b ^ 2 / (3 * a)) * x + (d - b ^ 3 * a / (3 * a) ^ 3) := by
        field_simp; ring
      _ = a * (x + b / (3 * a)) ^ 3 + (d - (9 * a * b * c - 2 * b ^ 3) * a / (3 * a) ^ 3) := by
        simp only [hb2, hb3]; field_simp [ha]; ring
      _ = a * ((x + b / (3 * a)) ^ 3 - s ^ 3) := by rw [hs3, hq]; field_simp [h54]; ring
  have h₃ : ∀ x, a * x = 0 ↔ x = 0 := by intro x; simp [ha]
  have h₄ : ∀ x : K, x ^ 3 - s ^ 3 = (x - s) * (x - s * ω) * (x - s * ω ^ 2) := by
    intro x
    calc
      x ^ 3 - s ^ 3 = (x - s) * (x ^ 2 + x * s + s ^ 2) := by ring
      _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + (1 + ω + ω ^ 2) * x * s + s ^ 2) := by ring
      _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + ω ^ 3 * s ^ 2) := by
        rw [hω.pow_eq_one, cube_root_of_unity_sum hω]; simp
      _ = (x - s) * (x - s * ω) * (x - s * ω ^ 2) := by ring
  rw [h₁, h₂, h₃, h₄ (x + b / (3 * a))]
  ring_nf
#align theorems_100.cubic_eq_zero_iff_of_p_eq_zero Theorems100.cubic_eq_zero_iff_of_p_eq_zero

end Field

end Theorems100
