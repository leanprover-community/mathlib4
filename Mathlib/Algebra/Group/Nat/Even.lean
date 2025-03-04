/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Sqrt

/-!
# `IsSquare` and `Even` for natural numbers
-/

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! #### Parity -/

variable {m n : ℕ}

lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Nat.two_mul, hm]
  mpr h := ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [← Nat.two_mul, h])⟩

instance : DecidablePred (Even : ℕ → Prop) := fun _ ↦ decidable_of_iff _ even_iff.symm

/-- `IsSquare` can be decided on `ℕ` by checking against the square root. -/
instance : DecidablePred (IsSquare : ℕ → Prop) :=
  fun m ↦ decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) <| by
    simp_rw [← Nat.exists_mul_self m, IsSquare, eq_comm]

lemma not_even_iff : ¬ Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_not_eq_zero]

@[simp] lemma two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  (even_iff_exists_two_nsmul _).symm.not.trans not_even_iff

@[simp] lemma not_even_one : ¬Even 1 := by simp [even_iff]

@[parity_simps] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  rcases mod_two_eq_zero_or_one m with h₁ | h₁ <;> rcases mod_two_eq_zero_or_one n with h₂ | h₂ <;>
    simp [even_iff, h₁, h₂, Nat.add_mod]

@[parity_simps] lemma even_add_one : Even (n + 1) ↔ ¬Even n := by simp [even_add]

lemma succ_mod_two_eq_zero_iff : (m + 1) % 2 = 0 ↔ m % 2 = 1 := by
  simp [← Nat.even_iff, ← Nat.not_even_iff, parity_simps]

lemma succ_mod_two_eq_one_iff : (m + 1) % 2 = 1 ↔ m % 2 = 0 := by
  simp [← Nat.even_iff, ← Nat.not_even_iff, parity_simps]

lemma two_not_dvd_two_mul_add_one (n : ℕ) : ¬2 ∣ 2 * n + 1 := by simp [add_mod]

lemma two_not_dvd_two_mul_sub_one : ∀ {n}, 0 < n → ¬2 ∣ 2 * n - 1
  | n + 1, _ => two_not_dvd_two_mul_add_one n

@[parity_simps] lemma even_sub (h : n ≤ m) : Even (m - n) ↔ (Even m ↔ Even n) := by
  conv_rhs => rw [← Nat.sub_add_cancel h, even_add]
  by_cases h : Even n <;> simp [h]

@[parity_simps] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  rcases mod_two_eq_zero_or_one m with h₁ | h₁ <;> rcases mod_two_eq_zero_or_one n with h₂ | h₂ <;>
    simp [even_iff, h₁, h₂, Nat.mul_mod]

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
@[parity_simps] lemma even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction n <;> simp +contextual [*, pow_succ', even_mul]

lemma even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m := even_pow.trans <| and_iff_left h

lemma even_mul_succ_self (n : ℕ) : Even (n * (n + 1)) := by rw [even_mul, even_add_one]; exact em _

lemma even_mul_pred_self : ∀ n : ℕ, Even (n * (n - 1))
  | 0 => .zero
  | (n + 1) => mul_comm (n + 1 - 1) (n + 1) ▸ even_mul_succ_self n

lemma two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := fun h ↦
  Nat.mul_div_cancel_left' ((even_iff_exists_two_nsmul _).1 h)

lemma div_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun h ↦ Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)

theorem one_lt_of_ne_zero_of_even (h0 : n ≠ 0) (hn : Even n) : 1 < n := by
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr (And.intro h0 ?_)
  intro h
  rw [h] at hn
  exact Nat.not_even_one hn

theorem add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) :
    n + 1 < m := by
  rcases hn with ⟨n, rfl⟩
  rcases hm with ⟨m, rfl⟩
  omega

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by simp [*, parity_simps]

example : ¬Even 25394535 := by decide

end Nat
