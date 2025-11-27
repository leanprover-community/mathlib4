/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cassini and Catalan identities for the Fibonacci numbers

Cassini's identity states that for `n : ℤ`, `fib (n + 1) * fib (n - 1) - fib n ^ 2` is equal
to `(-1) ^ |n|`. And Catalan's identity states that for any integers `x` and `a`, we get
`fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ |x| * fib a ^ 2`.
-/

/-- Being a linear recurrence, the entries of the Fibonacci sequence can be related via
matrix exponentiation. -/
public lemma Nat.fib_matrix_eq : ∀ {n : ℕ},
    !![fib (n + 2), fib (n + 1); fib (n + 1), fib n] = !![1, 1; 1, 0] ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, ← fib_matrix_eq]
    simp [fib_add_two, ← add_assoc, add_rotate, add_comm (fib n)]

/-- Nat version of Cassini's identity. Auxiliary for `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
lemma Nat.fib_add_two_mul_fib_sub_fib_add_one_sq (n : ℕ) :
    (fib (n + 2) * fib n - fib (n + 1) ^ 2 : ℤ) = (-1) ^ (n + 1) :=
  calc
    _ = (!![fib (n + 2), fib (n + 1); fib (n + 1), fib n] : Matrix _ _ ℤ).det := by simp [pow_two]
    _ = (!![fib (n + 2), fib (n + 1); fib (n + 1), fib n].map (castRingHom ℤ)).det := rfl
    _ = (!![1, 1; 1, 0].map (castRingHom ℤ) ^ (n + 1)).det := by rw [fib_matrix_eq, Matrix.map_pow]
    _ = (!![1, 1; 1, 0] ^ (n + 1)).det := by congr; simp [← Matrix.ext_iff]
    _ = (-1) ^ (n + 1) := by simp

/-- Auxiliary for `Int.fib_succ_mul_fib_pred_sub_fib_sq`. The `Int` version of
`Nat.fib_add_two_mul_fib_sub_fib_add_one_sq`. -/
lemma Int.fib_add_two_mul_fib_sub_fib_add_one_sq (n : ℕ) :
    fib (n + 2) * fib n - fib (n + 1) ^ 2 = (-1) ^ (n + 1) := by
  simp [← Nat.fib_add_two_mul_fib_sub_fib_add_one_sq, ← fib_natCast]

/-- **Cassini's identity**: `fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`. -/
public lemma Int.fib_succ_mul_fib_pred_sub_fib_sq (n : ℤ) :
    fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n.natAbs := by
  if hn₀ : n = 0 then simp [hn₀] else
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by simpa using hn₀)
    simp [natAbs_add_of_nonneg, ← fib_add_two_mul_fib_sub_fib_add_one_sq, add_assoc]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by simpa using hn₀)
    simp_rw [show -((i + 1 : ℕ) : ℤ) + 1 = -i by simp, sub_eq_add_neg, ← neg_add,
      fib_neg, natAbs_neg, natAbs_natCast]
    grind [fib_add_two_mul_fib_sub_fib_add_one_sq]

/-- Nat version of Catalan's identity. Auxiliary for
`Int.fib_add_add_sq_sub_fib_mul_fib_add_two_mul` -/
lemma Nat.fib_add_add_one_sq_sub_fib_succ_mul_fib_add_two_mul_succ (x a : ℕ) :
    (fib (x + a + 1) ^ 2 - fib (x + 1) * fib (x + 2 * a + 1) : ℤ) = (-1) ^ (x + 1) * fib a ^ 2 := by
  by_cases ha : a = 0
  · simp [ha, sq]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha
  calc (fib (x + a + 2) ^ 2 - fib (x + 1) * fib (x + 2 * a + 3) : ℤ)
      = (fib (x + 1) * fib (a + 2) + fib x * fib (a + 1)) ^ 2 - fib (x + 1) *
          (fib (x + 1) * (fib ((a + 1) + 1) ^ 2 + fib (a + 1) ^ 2) + fib ((x + 1) - 1)
            * (fib (a + 1) * fib ((a + 1) + 1) + fib ((a + 1) - 1) * fib (a + 1))) := by
        congr 2
        · rw [(by ring : x + a + 2 = x + (a + 1) + 1)]
          simp only [fib_add, fib_one, mul_one, reduceAdd, fib_two, cast_add, cast_mul]
          ring
        · rw [show x + 2 * a + 3 = (x + 1) + 2 * (a + 1) by ring]
          set b := a + 1
          set c := x + 1
          have {m n : ℕ} (hn : n ≠ 0) :
              fib (m + n) = fib m * fib (n - 1) + fib (m + 1) * fib n := by
            obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
            simp [← add_assoc, fib_add]
          rw [add_comm c, this (by grind)]
          simp_rw [two_mul, fib_add, this (m := b) (n := b) (by grind)]
          simp only [cast_add, cast_mul, sq, add_comm, mul_comm]
    _ = fib (x + 1) * fib x * fib (a + 1) * (fib (a + 2) - fib a) +
      fib (a + 1) ^ 2 * (fib x ^ 2 - fib (x + 1) ^ 2) := by simp only [add_tsub_cancel_right]; ring
    _ = fib (a + 1) ^ 2 * (fib x ^ 2 + fib (x + 1) * fib x - fib (x + 1) ^ 2) := by
        simp only [fib_add_two, cast_add, add_sub_cancel_left]
        ring
    _ = _ := by
        rw [← fib_add_two_mul_fib_sub_fib_add_one_sq, sub_mul, fib_add_two, cast_add]
        ring

/-- **Catalan's identity**: `fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ |x| * fib a ^ 2`. -/
public lemma Int.fib_add_add_sq_sub_fib_mul_fib_add_two_mul (x a : ℤ) :
    fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ x.natAbs * fib a ^ 2 :=
  calc
    _ = (fib x * fib (a + 1) + fib (x - 1) * fib a) ^ 2 - fib x *
          (fib x * (fib (a + 1) ^ 2 + fib a ^ 2) + fib (x - 1) *
          (fib a * fib (a + 1) + fib (a - 1) * fib a)) := by
      congr 2
      · simp only [fib_add, fib_one, mul_one, reduceAdd, fib_two]
        ring
      · simp_rw [add_comm x, two_mul]
        simp only [fib_add, ← add_sub, sub_add_cancel, fib_one, mul_one, reduceAdd, fib_two]
        grind
    _ = fib a ^ 2 * (fib (x - 1) ^ 2 + fib x * fib (x - 1) - fib x ^ 2) := by grind [fib_add_two]
    _ = _ := by grind [fib_succ_mul_fib_pred_sub_fib_sq, fib_add_two]
