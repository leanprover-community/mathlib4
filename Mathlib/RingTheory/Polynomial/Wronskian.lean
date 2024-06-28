/-
Copyright (c) 2024 Jineon Back and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek and Seewoo Lee
-/
import Mathlib.RingTheory.Polynomial.Content

/-!
# Wronskian of a pair of polynomial

This file defines Wronskian of a pair of polynomial, which is `W(a, b) = ab' - a'b`, and prove basic properties of it.

## Main declarations

- `wronskian_eq_sum_zero`: We have `W(a, b) = W(b, c)` when `a + b + c = 0`.
- `wronskian.degree_lt_add`: Degree of Wronskian `W(a, b)` is strictly smaller than the sum of degrees of `a` and `b`
- `wronskian.natDegree_lt_add`: `natDegree` version of the above theorem. We need to assume that the Wronskian is nonzero. (Otherwise, `a = b = 1` gives a counterexample.)
-/

noncomputable section

open scoped Polynomial Classical

open Polynomial

variable {R : Type _} [CommRing R]

/-- Wronskian: W(a, b) = ab' - a'b. -/
def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b

@[simp]
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  simp_rw [wronskian]; simp only [MulZeroClass.zero_mul, derivative_zero, sub_self]

@[simp]
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := by
  simp_rw [wronskian]; simp only [derivative_zero, MulZeroClass.mul_zero, sub_self]

theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring

theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring

theorem wronskian_add_right (a b c : R[X]) : wronskian a (b + c) = wronskian a b + wronskian a c :=
  by simp_rw [wronskian, derivative_add]; ring

theorem wronskian_self (a : R[X]) : wronskian a a = 0 := by rw [wronskian, mul_comm, sub_self]

theorem wronskian_anticomm (a b : R[X]) : wronskian a b = -wronskian b a := by
  rw [wronskian, wronskian]; ring

theorem wronskian_eq_of_sum_zero {a b c : R[X]} (h : a + b + c = 0) :
    wronskian a b = wronskian b c := by
  rw [← neg_eq_iff_add_eq_zero] at h
  rw [← h]
  rw [wronskian_neg_right]
  rw [wronskian_add_right]
  rw [wronskian_self]
  rw [add_zero]
  rw [← wronskian_anticomm]

private theorem degree_ne_bot {a : R[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ := by
  intro h; rw [Polynomial.degree_eq_bot] at h; exact ha h

theorem wronskian.degree_lt_add {a b : R[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left => .
      {
        apply lt_of_le_of_lt
        exact degree_mul_le a (derivative b)
        rw [WithBot.add_lt_add_iff_left (degree_ne_bot ha)]
        exact Polynomial.degree_derivative_lt hb
      }
      case right => .
      {
        apply lt_of_le_of_lt
        exact degree_mul_le (derivative a) b
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot hb)]
        exact Polynomial.degree_derivative_lt ha
      }

theorem wronskian.natDegree_lt_add {a b : R[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a ≠ 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b ≠ 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe, WithBot.coe_add]
  convert ← wronskian.degree_lt_add ha hb
  exact Polynomial.degree_eq_natDegree hw
  exact Polynomial.degree_eq_natDegree ha
  exact Polynomial.degree_eq_natDegree hb

-- Note: the following is false!
-- Counterexample: b = a = 1 →
-- (wronskian a b).natDegree = a.natDegree = b.natDegree = 0
/-
lemma wronskian.natDegree_lt_add {a b : R[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) :
  (wronskian a b).natDegree < a.natDegree + b.natDegree := sorry
-/
