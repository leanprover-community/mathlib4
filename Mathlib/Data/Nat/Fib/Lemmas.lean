/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cassini and Catalan identities for the Fibonacci numbers

Cassini's identity states that for `n : ℕ`, `fib (n + 2) * fib n - fib (n + 1) ^ 2` is equal
to `(-1) ^ (n + 1)`. And Catalan's identity states that for any naturals `x` and `a`, we get
`fib (x + a + 2) ^ 2 - fib (x + 1) * fib (x + 2 * a + 3) = (-1) ^ (x + 1) * fib (a + 1) ^ 2`.
-/

namespace Nat

/-- Being a linear recurrence, the entries of the Fibonacci sequence can be related to
matrix exponentiation. -/
lemma fib_matrix_eq : ∀ {n : ℕ},
    !![fib (n + 2), fib (n + 1); fib (n + 1), fib n] = !![1, 1; 1, 0] ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, ← fib_matrix_eq]
    simp [fib_add_two, ← add_assoc, add_rotate, add_comm (fib n)]

/-- **Cassini's identity**: `fib (n + 2) * fib n - fib (n + 1) ^ 2 = (-1) ^ (n + 1)`. -/
lemma fib_add_two_mul_fib_sub_fib_succ_sq (n : ℕ) :
    (fib (n + 2) * fib n - fib (n + 1) ^ 2 : ℤ) = (-1) ^ (n + 1) :=
  calc
    _ = (!![fib (n + 2), fib (n + 1); fib (n + 1), fib n] : Matrix _ _ ℤ).det := by simp [pow_two]
    _ = (!![fib (n + 2), fib (n + 1); fib (n + 1), fib n].map (castRingHom ℤ)).det := rfl
    _ = (!![1, 1; 1, 0].map (castRingHom ℤ) ^ (n + 1)).det := by rw [fib_matrix_eq, Matrix.map_pow]
    _ = (!![1, 1; 1, 0] ^ (n + 1)).det := by congr; simp [← Matrix.ext_iff]
    _ = (-1) ^ (n + 1) := by simp

/-- Cassini's identity for even `n`: `fib (n + 2) * fib n = fib (n + 1) ^ 2 - 1.` -/
lemma fib_add_two_mul_fib_of_even {n : ℕ} (hn2 : Even n) :
    fib (n + 2) * fib n = fib (n + 1) ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ := hn2
  grind [fib_add_two_mul_fib_sub_fib_succ_sq, pow_mul]

/-- Cassini's identity for odd `n`: `fib (n + 1) * fib (n - 1) = fib n ^ 2 - 1.` -/
lemma fib_succ_mul_fib_pred_of_odd {n : ℕ} (hn : Odd n) :
    fib (n + 1) * fib (n - 1) = fib n ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ := hn
  grind [fib_add_two_mul_fib_sub_fib_succ_sq, pow_mul]

/-- **Catalan's identity**:
`fib (x + a + 2) ^ 2 - fib (x + 1) * fib (x + 2 * a + 3) = (-1) ^ (x + 1) * fib (a + 1) ^ 2`. -/
lemma fib_add_add_two_sq_sub_fib_add_mul_fib_add_two_mul_add_three (x a : ℕ) :
    (fib (x + a + 2) ^ 2 - fib (x + 1) * fib (x + 2 * a + 3) : ℤ)
      = (-1) ^ (x + 1) * fib (a + 1) ^ 2 :=
  calc (fib (x + a + 2) ^ 2 - fib (x + 1) * fib (x + 2 * a + 3) : ℤ)
      = (fib (x + 1) * fib (a + 2) + fib x * fib (a + 1)) ^ 2 - fib (x + 1) *
          (fib (x + 1) * (fib ((a + 1) + 1) ^ 2 + fib (a + 1) ^ 2) + fib ((x + 1) - 1)
            * (fib (a + 1) * fib ((a + 1) + 1) + fib ((a + 1) - 1) * fib (a + 1))) := by
        congr 2
        · rw [(by ring : x + a + 2 = x + (a + 1) + 1)]
          simp [fib_add]
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
        rw [← fib_add_two_mul_fib_sub_fib_succ_sq, sub_mul, fib_add_two, cast_add]
        ring

end Nat
