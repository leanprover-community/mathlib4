/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Prime

/-!
# Existence of a sufficiently large prime for which `a * c ^ p / (p - 1)! < 1`

This is a technical result used in the proof of the Lindemann-Weierstrass theorem.
-/

namespace FloorRing

open scoped Nat

variable {K : Type*}

theorem exists_prime_mul_pow_lt_factorial [LinearOrderedRing K] [FloorRing K] (n : ℕ) (a c : K) :
    ∃ p > n, p.Prime ∧ a * c ^ p < (p - 1)! := by
  obtain ⟨p, pn, pp, h⟩ := n.exists_prime_mul_pow_lt_factorial ⌈|a|⌉.natAbs ⌈|c|⌉.natAbs
  use p, pn, pp
  calc a * c ^ p
    _ ≤ |a * c ^ p| := le_abs_self _
    _ ≤ ⌈|a|⌉ * (⌈|c|⌉ : K) ^ p := ?_
    _ = ↑(Int.natAbs ⌈|a|⌉ * Int.natAbs ⌈|c|⌉ ^ p) := ?_
    _ < ↑(p - 1)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> try first | positivity | apply Int.le_ceil
  · simp_rw [Nat.cast_mul, Nat.cast_pow, Int.cast_natAbs,
      abs_eq_self.mpr (Int.ceil_nonneg (abs_nonneg (_ : K)))]

theorem exists_prime_mul_pow_div_factorial_lt_one [LinearOrderedField K] [FloorRing K]
    (n : ℕ) (a c : K) :
    ∃ p > n, p.Prime ∧ a * c ^ p / (p - 1)! < 1 := by
  simp_rw [div_lt_one (α := K) (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  exact exists_prime_mul_pow_lt_factorial ..

end FloorRing
