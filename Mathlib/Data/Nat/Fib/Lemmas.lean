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

Cassini's identity states that for nonzero `n`, `fib (n + 1) * fib (n - 1) - fib n ^ 2` is equal
to `(-1) ^ n`. And Catalan's identity states that for nonzero `x` and `a`, we get
`fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ x * fib a ^ 2`.
-/

namespace Nat

/-- For any nonzero `n`, the matrix `[fib (n + 1), fib n; fib n, fib (n - 1)]` is equal to
`[1, 1; 1, 0] ^ n`. -/
lemma fib_matrix_eq : ∀ {n : ℕ}, n ≠ 0 →
    !![fib (n + 1), fib n; fib n, fib (n - 1)] = !![1, 1; 1, 0] ^ n
  | 1, _ => by simp
  | n + 2, _ => by
    rw [pow_succ, ← fib_matrix_eq (add_one_ne_zero n)]
    simp [fib_add_two, ← add_assoc, add_rotate, add_comm (fib n)]

/-- **Cassini's identity**: for nonzero `n`, `fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n`. -/
lemma fib_succ_mul_fib_pred_sub_fib_sq {n : ℕ} (hn : n ≠ 0) :
    (fib (n + 1) * fib (n - 1) - fib n ^ 2 : ℤ) = (-1) ^ n :=
  calc _ = (!![fib (n + 1), fib n; fib n, fib (n - 1)] : Matrix _ _ ℤ).det := by simp [pow_two]
    _ = (!![fib (n + 1), fib n; fib n, fib (n - 1)].map (castRingHom ℤ)).det := rfl
    _ = (!![1, 1; 1, 0].map (castRingHom ℤ) ^ n).det := by rw [fib_matrix_eq hn, Matrix.map_pow]
    _ = (!![1, 1; 1, 0] ^ n).det := by congr; simp [← Matrix.ext_iff]
    _ = (-1) ^ n := by simp

/-- Cassini's identity for nonzero even `n`: `fib (n + 1) * fib (n - 1) = fib n ^ 2 + 1.` -/
lemma fib_succ_mul_fib_pred_of_ne_zero_even {n : ℕ} (hn : n ≠ 0) (hn2 : Even n) :
    fib (n + 1) * fib (n - 1) = fib n ^ 2 + 1 := by
  obtain ⟨a, rfl⟩ := hn2
  grind [fib_succ_mul_fib_pred_sub_fib_sq, pow_mul]

/-- Cassini's identity for odd `n`: `fib (n + 1) * fib (n - 1) = fib n ^ 2 - 1.` -/
lemma fib_succ_mul_fib_pred_of_odd {n : ℕ} (hn : Odd n) :
    fib (n + 1) * fib (n - 1) = fib n ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ := hn
  grind [fib_succ_mul_fib_pred_sub_fib_sq, pow_mul]

/-- **Catalan's identity**: for nonzero `x` and `a`,
`fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ x * fib a ^ 2`. -/
lemma fib_add_sq_sub_fib_mul_fib_add_two_mul {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) :
    (fib (x + a) ^ 2 - fib x * fib (x + 2 * a) : ℤ) = (-1) ^ x * fib a ^ 2 :=
  calc (fib (x + a) ^ 2 - fib x * fib (x + 2 * a) : ℤ)
      = (fib x * fib (a + 1) + fib (x - 1) * fib a) ^ 2 - (fib x * (fib (a + 1) ^ 2 + fib a ^ 2) +
          fib (x - 1) * (fib a * fib (a + 1) + fib (a - 1) * fib a)) * fib x := by
        rw [mul_comm]
        congr 2
        · rw [add_comm, fib_add_of_ne_zero hx]
          simp only [cast_add, cast_mul, add_comm, mul_comm]
        · rw [add_comm x, fib_add_of_ne_zero hx]
          simp_rw [two_mul, fib_add, fib_add_of_ne_zero (m := a) (n := a) ha]
          simp only [cast_add, cast_mul, sq, add_comm, mul_comm]
    _ = fib x * fib (x - 1) * fib a * (fib (a + 1) - fib (a - 1)) +
      fib a ^ 2 * (fib (x - 1) ^ 2 - fib x ^ 2) := by ring
    _ = fib a ^ 2 * (fib (x - 1) ^ 2 + fib x * fib (x - 1) - fib x ^ 2) := by
        rw [← Int.natCast_sub (fib_mono (by grind)), fib_succ_sub_fib_pred ha]
        ring
    _ = _ := by
        rw [← fib_succ_mul_fib_pred_sub_fib_sq hx, fib_add_one hx, Int.natCast_add, add_mul]
        ring

/-- Another version of **Catalan's identity**.
Also see `fib_add_sub_fib_add_two_mul_mul_fib`. -/
theorem fib_sq_sub_fib_sub_mul_fub_add {n r : ℕ} (hr : r ≠ 0) (hrn : r < n) :
    (fib n ^ 2 - fib (n - r) * fib (n + r) : ℤ) = (-1) ^ (n - r) * fib r ^ 2 := by
  have := fib_add_sq_sub_fib_mul_fib_add_two_mul (Nat.sub_ne_zero_iff_lt.mpr hrn) hr
  grind

end Nat
