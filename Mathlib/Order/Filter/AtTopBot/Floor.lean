/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Order.Filter.AtTopBot

/-!
# `a * c ^ n / (n - d)! < ε` holds true for sufficiently large `n`.
-/

open Filter
open scoped Nat

theorem Nat.eventually_pow_lt_factorial_sub (c d : ℕ) : ∀ᶠ n in atTop, c ^ n < (n - d)! := by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d') c0)).trans_lt ?_
  convert_to (c ^ 2) ^ (c ^ 2 + d' + d + 1) < (c ^ 2 + (c ^ 2 + d' + d + 1) + 1)!
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega
  · congr 1
    omega
  refine (lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial).trans_le <|
    (factorial_le (Nat.le_succ _))
  rw [← one_mul (_ ^ _ : ℕ)]
  apply Nat.mul_lt_mul_of_le_of_lt
  · exact Nat.one_le_of_lt (Nat.factorial_pos _)
  · exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  · exact (Nat.factorial_pos _)

theorem Nat.eventually_mul_pow_lt_factorial_sub (a c d : ℕ) :
    ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  obtain ⟨n0, h⟩ := (Nat.eventually_pow_lt_factorial_sub (a * c) d).exists_forall_of_atTop
  rw [eventually_atTop]
  refine ⟨max n0 1, fun n hn => lt_of_le_of_lt ?_ (h n (le_of_max_le_left hn))⟩
  rw [mul_pow]
  refine Nat.mul_le_mul_right _ (Nat.le_self_pow ?_ _)
  omega

variable {K : Type*}

theorem FloorSemiring.eventually_mul_pow_lt_factorial_sub [LinearOrderedRing K] [FloorSemiring K]
    (a c : K) (d : ℕ) : ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub ⌈|a|⌉₊ ⌈|c|⌉₊ d] with n h
  calc a * c ^ n
    _ ≤ |a * c ^ n| := le_abs_self _
    _ ≤ ⌈|a|⌉₊ * (⌈|c|⌉₊ : K) ^ n := ?_
    _ = ↑(⌈|a|⌉₊ * ⌈|c|⌉₊ ^ n) := ?_
    _ < ↑(n - d)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> try first | positivity | apply Nat.le_ceil
  · simp_rw [Nat.cast_mul, Nat.cast_pow]

theorem FloorSemiring.eventually_mul_pow_div_factorial_lt [LinearOrderedField K] [FloorSemiring K]
    (a c : K) (d : ℕ) {ε : K} (hε : 0 < ε) : ∀ᶠ n in atTop, a * c ^ n / (n - d)! < ε := by
  filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
  rw [mul_right_comm, mul_inv_lt_iff hε] at h
  rwa [div_lt_iff (Nat.cast_pos.mpr (Nat.factorial_pos _))]

namespace Nat

@[deprecated (since := "2024-09-25")]
theorem exists_pow_lt_factorial (c : ℕ) : ∃ n0 > 1, ∀ n ≥ n0, c ^ n < (n - 1)! :=
  let ⟨n0, h⟩ := (eventually_pow_lt_factorial_sub c 1).exists_forall_of_atTop
  ⟨max n0 2, by omega, fun n hn ↦ h n (by omega)⟩

@[deprecated (since := "2024-09-25")]
theorem exists_mul_pow_lt_factorial (a : ℕ) (c : ℕ) : ∃ n0, ∀ n ≥ n0, a * c ^ n < (n - 1)! :=
  (eventually_mul_pow_lt_factorial_sub a c 1).exists_forall_of_atTop

end Nat
