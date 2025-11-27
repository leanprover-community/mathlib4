/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Data.Int.Fib.Basic

/-!
# Cassini and Catalan identities for the Fibonacci numbers

Cassini's identity states that for `n : ℤ`, `fib (n + 1) * fib (n - 1) - fib n ^ 2` is equal
to `(-1) ^ |n|`. And Catalan's identity states that for any integers `x` and `a`, we get
`fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ |x| * fib a ^ 2`.
-/

namespace Int

/-- Auxiliary for `Int.fib_succ_mul_fib_pred_sub_fib_sq` -/
lemma fib_natCast_succ_mul_fib_natCast_pred_sub_fib_natCast_sq (n : ℕ) :
    fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ _ _ => grind [fib_add_two]

/-- **Cassini's identity**: `fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`. -/
public theorem fib_succ_mul_fib_pred_sub_fib_sq (n : ℤ) :
    fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n.natAbs := by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact fib_natCast_succ_mul_fib_natCast_pred_sub_fib_natCast_sq n
  · if hn : n = 0 then simp [hn] else
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    simp_rw [show -((i + 1 : ℕ) : ℤ) + 1 = -i by simp, sub_eq_add_neg, ← neg_add, fib_neg,
      natAbs_neg, natAbs_natCast, ← fib_natCast_succ_mul_fib_natCast_pred_sub_fib_natCast_sq]
    grind

/-- **Catalan's identity**: `fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ |x| * fib a ^ 2`. -/
public theorem fib_add_sq_sub_fib_mul_fib_add_two_mul (x a : ℤ) :
    fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ x.natAbs * fib a ^ 2 :=
  calc
    _ = (fib x * fib (a + 1) + fib (x - 1) * fib a) ^ 2 -
          fib x * (fib x * (fib (a + 1) ^ 2 + fib a ^ 2) +
            fib (x - 1) * (fib a * fib (a + 1) + fib (a - 1) * fib a)) := by
      rw [add_comm x]
      simp only [two_mul, fib_add, fib_one, mul_one, reduceAdd, fib_two, ← add_sub, sub_add_cancel]
      ring
    _ = _ := by grind [fib_succ_mul_fib_pred_sub_fib_sq, fib_add_two]

end Int
