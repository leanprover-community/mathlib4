/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Sqrt

/-!
# Parity of integers
-/

open Nat

namespace Int

/-! #### Parity -/

variable {m n : ℤ}

@[simp] lemma emod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by grind

@[simp] lemma one_emod_two : (1 : Int) % 2 = 1 := rfl

-- `EuclideanDomain.mod_eq_zero` uses (2 ∣ n) as normal form
@[local simp] lemma emod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by grind

@[grind =]
lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

lemma not_even_iff : ¬Even n ↔ n % 2 = 1 := by grind

@[simp] lemma two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 := by grind

instance : DecidablePred (Even : ℤ → Prop) := fun _ ↦ decidable_of_iff _ even_iff.symm

/-- `IsSquare` can be decided on `ℤ` by checking against the square root. -/
instance : DecidablePred (IsSquare : ℤ → Prop) :=
  fun m ↦ decidable_of_iff' (sqrt m * sqrt m = m) <| by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp] lemma not_even_one : ¬Even (1 : ℤ) := by simp [even_iff]

@[parity_simps] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by grind

lemma two_not_dvd_two_mul_add_one (n : ℤ) : ¬2 ∣ 2 * n + 1 := by grind

@[parity_simps]
lemma even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by grind

@[parity_simps] lemma even_add_one : Even (n + 1) ↔ ¬Even n := by grind

@[parity_simps] lemma even_sub_one : Even (n - 1) ↔ ¬Even n := by grind

@[parity_simps, grind =] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  rcases emod_two_eq_zero_or_one m with h₁ | h₁ <;>
  rcases emod_two_eq_zero_or_one n with h₂ | h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]

@[parity_simps, grind =] lemma even_pow {n : ℕ} : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction n with grind

lemma even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m := by grind

@[simp, norm_cast, grind =]
lemma even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  rw_mod_cast [even_iff, Nat.even_iff]

lemma two_mul_ediv_two_of_even : Even n → 2 * (n / 2) = n := by grind

lemma ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n := by grind

-- Here are examples of how `parity_simps` can be used with `Int`.
example (m n : ℤ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp +decide [*, parity_simps]

example : ¬Even (25394535 : ℤ) := by decide

@[simp]
theorem isSquare_sign_iff {z : ℤ} : IsSquare z.sign ↔ 0 ≤ z := by
  induction z using Int.induction_on with
  | zero => simpa using ⟨0, by simp⟩
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by omega), ← neg_add', Int.neg_nonneg]
    norm_cast
    simp only [reduceNeg, le_zero_eq, Nat.add_eq_zero, succ_ne_self, and_false, iff_false]
    rintro ⟨a | a, ⟨⟩⟩

end Int
