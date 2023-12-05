import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Factorization.Basic

open Finset Finsupp

namespace Nat
variable {a b n : ℕ}

noncomputable def ceilingRoot (n a : ℕ) : ℕ := (a.factorization ⌈/⌉ n).prod (· ^ ·)

@[simp] lemma ceilingRoot_zero_left (a : ℕ) : ceilingRoot 0 a = 1 := by simp [ceilingRoot]
@[simp] lemma ceilingRoot_zero_right (n : ℕ) : ceilingRoot n 0 = 1 := by simp [ceilingRoot]
@[simp] lemma ceilingRoot_one_left (ha : a ≠ 0) : ceilingRoot 1 a = a := by simp [ceilingRoot, ha]
@[simp] lemma ceilingRoot_one_right (n : ℕ) : ceilingRoot n 1 = 1 := by simp [ceilingRoot]

@[simp] lemma ceilingRoot_pow_self (hn : n ≠ 0) (ha : a ≠ 0) : ceilingRoot n (a ^ n) = a := by
  simp [ceilingRoot, pos_iff_ne_zero.2 hn, ha]

@[simp] lemma ceilingRoot_ne_zero : ceilingRoot n a ≠ 0 := by
  simp (config := { contextual := true }) [ceilingRoot, not_imp_not]

@[simp] lemma factorization_ceilingRoot (n a : ℕ) :
    (ceilingRoot n a).factorization = a.factorization ⌈/⌉ n := by
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ _ := by simpa using support_ceilDiv_subset hp
  exact this.1

lemma dvd_ceilingRoot_pow (hn : n ≠ 0) (ha : a ≠ 0) : a ∣ ceilingRoot n a ^ n := by
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ ceilingRoot_ne_zero), factorization_pow,
    factorization_ceilingRoot]
  sorry

lemma dvd_pow_iff (hn : n ≠ 0) (ha : a ≠ 0) : a ∣ b ^ n ↔ ceilingRoot n a ∣ b := by
  refine ⟨?_, fun h ↦ (dvd_ceilingRoot_pow hn ha).trans $ pow_dvd_pow_of_dvd h _⟩
  sorry



end Nat
